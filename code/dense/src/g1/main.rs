// g1: dense-window covers beyond m = 62 (queue G1). Generic W-word masks (2m <= 64*W), exact integer arithmetic.
//   g1 edgetest M            event-point edge enumeration vs old rational enumeration (equal minimal families?)
//   g1 fam M [tmax]          family stage only: enumerate |T|<=tmax blocks, exact irreducible reduction, stats
//   g1 brute M               brute-force domination test of the full family (all (T,L), |T|<=4, L subset Low')  (m <= 17)
//   g1 run LO HI SECS [seed0] [tmax]   driver: for every composite 2m+1, LO<=m<=HI: family, local search, exact check
//   g1 check M file          independent exact checker of certs/m<M>.g1.sol (line format: "cap v1 v2 ...", velocities 1-based)
// Resource rules: <= 3 threads, internal RSS watchdog (3.9 GB), outputs under (development file, not part of this archive) and certs/. Resumable.
use std::collections::{HashMap,HashSet}; use std::sync::{Mutex,atomic::*}; use std::time::Instant;
const DIR:&str=".";
const RSSCAP:f64=3.9;
static MINP:AtomicI32=AtomicI32::new(-99); fn minp()->i32{ MINP.load(Ordering::Relaxed) }
// NEGT: blocks of negative profit are kept only if |T| <= NEGT (99 = no restriction)
static NEGT:AtomicU32=AtomicU32::new(99); fn negt()->u32{ NEGT.load(Ordering::Relaxed) }
fn need_l(nt:u32,minp:i32,negt:u32)->i32{ if nt<=negt { nt as i32+minp } else { nt as i32+minp.max(0) } }
fn nth()->usize{ static N:std::sync::OnceLock<usize>=std::sync::OnceLock::new(); *N.get_or_init(||std::env::var("G1_THREADS").ok().and_then(|x|x.parse().ok()).unwrap_or(3).min(3).max(1)) }
#[repr(C)] struct RU { ut:[i64;2], st:[i64;2], maxrss:i64, rest:[i64;13] }
extern "C" { fn getrusage(who:i32,u:*mut RU)->i32; }
fn rss()->f64{ let mut u=RU{ut:[0;2],st:[0;2],maxrss:0,rest:[0;13]}; unsafe{getrusage(0,&mut u);} u.maxrss as f64/1e9 }
fn watchdog(cap:f64){ std::thread::spawn(move||loop{ std::thread::sleep(std::time::Duration::from_secs(2)); let r=rss();
    if r>cap { eprintln!("WATCHDOG: peak RSS {:.2} GB > cap {:.2} GB, exiting",r,cap); std::process::exit(3);} }); }
fn atomic_write(path:&str,b:&[u8]){ let tmp=format!("{}.tmp",path); std::fs::write(&tmp,b).unwrap(); std::fs::rename(&tmp,path).unwrap(); }
fn load1()->f64{ let o=std::process::Command::new("sysctl").args(["-n","vm.loadavg"]).output(); match o { Ok(o)=>{ let s=String::from_utf8_lossy(&o.stdout).to_string(); s.split_whitespace().filter_map(|x|x.trim_matches(|c|c=='{'||c=='}').parse::<f64>().ok()).next().unwrap_or(0.0) }, Err(_)=>0.0 } }
fn wait_load(){ loop { let l=load1(); if l<12.0 {return;} println!("LOAD {:.2} >= 12, waiting 60 s",l); std::thread::sleep(std::time::Duration::from_secs(60)); } }
fn gcd(a:u64,b:u64)->u64{ if a==0{b}else{gcd(b%a,a)} }
fn factor(mut n:u64)->String{ let mut v=vec![]; let mut p=2; while p*p<=n { let mut e=0; while n%p==0 {n/=p;e+=1;} if e>0 { v.push(if e>1 {format!("{}^{}",p,e)} else {p.to_string()}); } p+=1; } if n>1 {v.push(n.to_string());} v.join("*") }
fn is_prime(n:u64)->bool{ n>=2 && factor(n)==n.to_string() }

// ---------- W-word mask, bit x-1 <-> velocity x ----------
#[derive(Clone,Copy,PartialEq,Eq,Hash,PartialOrd,Ord,Debug)]
pub struct Mk<const W:usize>(pub [u64;W]);
impl<const W:usize> Mk<W>{
    pub fn z()->Self{ Mk([0;W]) }
    pub fn b(i:u32)->Self{ let mut a=[0u64;W]; a[(i>>6) as usize]=1u64<<(i&63); Mk(a) }
    pub fn has(&self,i:u32)->bool{ self.0[(i>>6) as usize]>>(i&63)&1==1 }
    pub fn set(&mut self,i:u32){ self.0[(i>>6) as usize]|=1u64<<(i&63); }
    pub fn clr(&mut self,i:u32){ self.0[(i>>6) as usize]&=!(1u64<<(i&63)); }
    pub fn and(&self,o:&Self)->Self{ let mut a=self.0; for i in 0..W { a[i]&=o.0[i]; } Mk(a) }
    pub fn or(&self,o:&Self)->Self{ let mut a=self.0; for i in 0..W { a[i]|=o.0[i]; } Mk(a) }
    pub fn andn(&self,o:&Self)->Self{ let mut a=self.0; for i in 0..W { a[i]&=!o.0[i]; } Mk(a) }
    pub fn is0(&self)->bool{ self.0.iter().all(|&w|w==0) }
    pub fn cnt(&self)->u32{ self.0.iter().map(|w|w.count_ones()).sum() }
    pub fn tz(&self)->u32{ for i in 0..W { if self.0[i]!=0 { return (i as u32)*64+self.0[i].trailing_zeros(); } } 64*W as u32 }
    pub fn sub(&self,o:&Self)->bool{ for i in 0..W { if self.0[i]&!o.0[i]!=0 {return false;} } true }
    pub fn meets(&self,o:&Self)->bool{ for i in 0..W { if self.0[i]&o.0[i]!=0 {return true;} } false }
    pub fn bits(&self)->Vec<u32>{ let mut v=vec![]; for i in 0..W { let mut r=self.0[i]; while r!=0 { v.push((i as u32)*64+r.trailing_zeros()); r&=r-1; } } v }
    pub fn range(lo:u32,hi:u32)->Self{ let mut r=Self::z(); for i in lo..hi { r.set(i); } r }
}

// ---------- minimal bad sets ----------
pub struct Edges<const W:usize>{ m:u32, n:u32, es:Vec<Mk<W>>, wit:Vec<(u32,u32)>, nraw:usize }
fn mask_of<const W:usize>(m:u32,n:u32,p:u64,q:u64)->Mk<W>{ let t=(m+1) as u64; let mut k=Mk::<W>::z(); let mut r=0u64;
    for x in 1..=n { r+=p; if r>=q {r-=q;} let mn=if r<q-r {r} else {q-r}; if t*mn<q { k.set(x-1); } } k }
fn minimalize<const W:usize>(m:u32,raw:HashMap<Mk<W>,(u32,u32)>)->Edges<W>{
    let nraw=raw.len(); let mut v:Vec<(Mk<W>,(u32,u32))>=raw.into_iter().collect();
    v.sort_by_key(|&(s,(p,q))|(s.cnt(),q,p,s)); let mut es:Vec<Mk<W>>=vec![]; let mut wit=vec![];
    for &(s,w) in &v { if !es.iter().any(|u|u.sub(&s)) { es.push(s); wit.push(w); } }
    Edges{m,n:2*m,es,wit,nraw} }
// event points: every cell of the arrangement {t : ||x t|| < 1/(m+1)} has its right endpoint at an event point
// t = (k(m+1) +- 1)/(x(m+1)) (or t = 1/2); the mask at an endpoint is contained in the mask of the cell. So the minimal masks
// over all real t are the minimal masks over event points.
fn edges_ev<const W:usize>(m:u32)->Edges<W>{
    let n=2*m; let t=(m+1) as u64; let mut pq:HashSet<(u32,u32)>=HashSet::new(); pq.insert((1,2));
    for x in 1..=(n as u64) { let b=x*t; for k in 0..=(x/2+1) { for s in [-1i64,1] { let a=(k*t) as i64+s; if a<=0 {continue;} let a=a as u64; if 2*a>b {continue;}
        let g=gcd(a,b); pq.insert(((a/g) as u32,(b/g) as u32)); } } }
    let mut raw:HashMap<Mk<W>,(u32,u32)>=HashMap::new();
    for &(p,q) in &pq { let k=mask_of::<W>(m,n,p as u64,q as u64); if k.is0() {continue;} let e=raw.entry(k).or_insert((p,q)); if (q,p)<(e.1,e.0) { *e=(p,q); } }
    minimalize(m,raw) }
fn edges_old<const W:usize>(m:u32,nth:usize)->Edges<W>{
    let n=2*m; let t=(m+1) as u64; let qmax=2*(n as u64)*t; let mut hs=vec![];
    for tid in 0..nth { hs.push(std::thread::spawn(move||{ let mut seen:HashMap<Mk<W>,(u32,u32)>=HashMap::new(); let mut q=1+tid as u64;
        while q<=qmax { for p in 1..=q/2 { if gcd(p,q)!=1 {continue;} let k=mask_of::<W>(m,n,p,q); if !k.is0() { seen.entry(k).or_insert((p as u32,q as u32)); } } q+=nth as u64; } seen })); }
    let mut all:HashMap<Mk<W>,(u32,u32)>=HashMap::new();
    for h in hs { for (k,v) in h.join().unwrap() { let e=all.entry(k).or_insert(v); if (v.1,v.0)<(e.1,e.0) {*e=v;} } }
    minimalize(m,all) }

// ---------- validity oracle ----------
pub struct Ctx<const W:usize>{ m:u32, n:u32, es:Vec<Mk<W>>, by_min:Vec<Vec<Mk<W>>>, privl:Vec<Vec<Mk<W>>>, low:Mk<W>, high:Mk<W> }
impl<const W:usize> Ctx<W>{
    fn new(m:u32,es:Vec<Mk<W>>)->Self{ let n=2*m; let mut by_min=vec![vec![];n as usize]; for e in es.iter(){ by_min[e.tz() as usize].push(*e); }
        let low=Mk::range(0,m+1); let high=Mk::range(m+1,n); let mut privl=vec![vec![];n as usize]; for e in es.iter(){ let lo=e.and(&low); if lo.cnt()==1 { privl[lo.tz() as usize].push(e.and(&high)); } } Ctx{m,n,es,by_min,privl,low,high} }
    // valid single-low block (T1,{l}) iff some edge inside T1+{l} (necessarily with exactly the low l)
    fn v1(&self,t:&Mk<W>,l:u32)->bool{ self.privl[l as usize].iter().any(|yp| yp.sub(t)) }
    fn local(&self,s:&Mk<W>,out:&mut Vec<Mk<W>>){ out.clear(); for i in 0..W { let mut r=s.0[i]; while r!=0 { let v=i*64+r.trailing_zeros() as usize; r&=r-1; for e in &self.by_min[v] { if e.sub(s) { out.push(*e); } } } } }
    fn y_independent(&self)->bool{ self.es.iter().all(|e| !e.andn(&self.high).is0()) }
    fn valid(&self,s:&Mk<W>,buf:&mut Vec<Mk<W>>)->bool{ let l=s.and(&self.low).cnt(); if l==0 {return true;} self.local(s,buf); !hs_exists(buf,&Mk::z(),l-1) }
}
fn hs_exists<const W:usize>(es:&[Mk<W>],hit:&Mk<W>,k:u32)->bool{
    let mut best:Option<&Mk<W>>=None; let mut bc=u32::MAX;
    for e in es { if !e.meets(hit) { let c=e.cnt(); if c<bc {bc=c;best=Some(e);} } }
    let best=match best { None=>return true, Some(b)=>*b };
    if k==0 {return false;}
    let mut used=Mk::<W>::z(); let mut cnt=0u32;
    for e in es { if !e.meets(hit) && !e.meets(&used) { used=used.or(e); cnt+=1; } }
    if cnt>k {return false;}
    for i in 0..W { let mut r=best.0[i]; while r!=0 { let b=(i as u32)*64+r.trailing_zeros(); r&=r-1; if hs_exists(es,&hit.or(&Mk::b(b)),k-1) {return true;} } }
    false }

// ---------- block family ----------
struct Priv<const W:usize>{ by_y:Vec<Vec<(Mk<W>,u32)>>, free:Mk<W> }
fn build_priv<const W:usize>(ctx:&Ctx<W>)->Priv<W>{
    let mut by_y=vec![vec![];ctx.n as usize]; let mut free=Mk::<W>::z();
    for e in &ctx.es { let lo=e.and(&ctx.low); if lo.cnt()!=1 {continue;} let yp=e.and(&ctx.high); let lb=lo.tz();
        if yp.is0() { free.set(lb); } else { let mx=*yp.bits().last().unwrap(); by_y[mx as usize].push((yp,lb)); } }
    Priv{by_y,free} }
fn reducible<const W:usize>(ctx:&Ctx<W>,t:&Mk<W>,l:&Mk<W>,buf:&mut Vec<Mk<W>>)->bool{
    let tb=t.bits(); let lb=l.bits(); let nt=tb.len(); let nl=lb.len(); if nt<2||nl<2 {return false;}
    for tm in 1u32..(1u32<<nt) { if tm&1==0 || tm==(1u32<<nt)-1 {continue;}
        let mut t1=Mk::<W>::z(); let mut t2=Mk::<W>::z(); for i in 0..nt { if tm>>i&1==1 { t1.set(tb[i]); } else { t2.set(tb[i]); } }
        for lm in 1u32..(1u32<<nl)-1 { let mut l1=Mk::<W>::z(); let mut l2=Mk::<W>::z(); for i in 0..nl { if lm>>i&1==1 { l1.set(lb[i]); } else { l2.set(lb[i]); } }
            if lm.count_ones()==1 { if !ctx.v1(&t1,l1.tz()) {continue;} } else if (nl as u32-lm.count_ones())==1 { if !ctx.v1(&t2,l2.tz()) {continue;} }
            if ctx.valid(&t1.or(&l1),buf) && ctx.valid(&t2.or(&l2),buf) { return true; } } }
    false }
struct Wk<'a,const W:usize>{ minp:i32, ctx:&'a Ctx<W>, pr:&'a Priv<W>, tmax:u32, reduce:bool, out:Vec<(Mk<W>,Mk<W>)>, buf:Vec<Mk<W>>, full:u64, nodes:u64 }
impl<'a,const W:usize> Wk<'a,W>{
    fn process(&mut self,t:&Mk<W>,c:&Mk<W>){
        if c.is0() {return;}
        let need=need_l(t.cnt(),self.minp,negt()); if (c.cnt() as i32)<need {return;}  // block profit |L|-|T| >= minp needs |L| >= |T|+minp, L inside c
        let cl=c.bits(); let mut valid:Vec<Mk<W>>=vec![]; let mut set:HashSet<Mk<W>>=HashSet::new();
        self.dfs_l(t,&cl,0,&Mk::z(),&mut valid,&mut set,need);
        for l in &valid {
            if (l.cnt() as i32)<need {continue;}
            if cl.iter().any(|&b| !l.has(b) && { let mut l2=*l; l2.set(b); set.contains(&l2) }) {continue;}
            let mut ok=true; for y in t.bits() { let mut t2=*t; t2.clr(y); if self.ctx.valid(&t2.or(l),&mut self.buf) { ok=false; break; } }
            if ok { self.full+=1; if self.reduce && reducible(self.ctx,t,l,&mut self.buf) {continue;} self.out.push((*t,*l)); }
        } }
    fn dfs_l(&mut self,t:&Mk<W>,cl:&[u32],from:usize,l:&Mk<W>,valid:&mut Vec<Mk<W>>,set:&mut HashSet<Mk<W>>,need:i32){
        for i in from..cl.len(){ if (((l.cnt() as usize)+1+(cl.len()-i-1)) as i32)<need {break;} let mut l2=*l; l2.set(cl[i]);
            if self.ctx.valid(&t.or(&l2),&mut self.buf) { valid.push(l2); set.insert(l2); self.dfs_l(t,cl,i+1,&l2,valid,set,need); } } }
    fn add_y(&self,t:&Mk<W>,c:&Mk<W>,y:u32)->(Mk<W>,Mk<W>){ let mut t2=*t; t2.set(y); let mut c2=*c; for &(yp,lb) in &self.pr.by_y[y as usize] { if yp.sub(&t2) { c2.set(lb); } } (t2,c2) }
    fn dfs_t(&mut self,t:&Mk<W>,k:u32,last:u32,c:&Mk<W>){
        self.nodes+=1; self.process(t,c);
        if k>=self.tmax {return;}
        for y in last..self.ctx.n { if !self.ctx.high.has(y) {continue;} let (t2,c2)=self.add_y(t,c,y); self.dfs_t(&t2,k+1,y+1,&c2); } }
}
// work units: id < ny: T={y_id} alone; then pairs (i<j) of the Y list: root T={y_i,y_j} with the full subtree beneath it
fn units(ny:usize)->Vec<(usize,usize)>{ let mut u=vec![]; for i in 0..ny { u.push((i,usize::MAX)); } for i in 0..ny { for j in i+1..ny { u.push((i,j)); } } u }
fn run_unit<const W:usize>(w:&mut Wk<W>,ys:&[u32],u:(usize,usize)){
    let z=Mk::<W>::z(); let (t1,c1)=w.add_y(&z,&z,ys[u.0]);
    if u.1==usize::MAX { w.nodes+=1; w.process(&t1,&c1); }
    else if w.tmax>=2 { let (t2,c2)=w.add_y(&t1,&c1,ys[u.1]); w.dfs_t(&t2,2,ys[u.1]+1,&c2); } }
fn put_blocks<const W:usize>(v:&mut Vec<u8>,b:&[(Mk<W>,Mk<W>)]){ for (t,l) in b { let tb=t.bits(); let lb=l.bits(); v.push(tb.len() as u8); v.push(lb.len() as u8); for x in tb { v.extend_from_slice(&(x as u16).to_le_bytes()); } for x in lb { v.extend_from_slice(&(x as u16).to_le_bytes()); } } }
fn get_blocks<const W:usize>(b:&[u8],mut pos:usize,nblk:usize)->(Vec<(Mk<W>,Mk<W>)>,usize){ let mut out=Vec::with_capacity(nblk);
    for _ in 0..nblk { let nt=b[pos] as usize; let nl=b[pos+1] as usize; pos+=2; let mut t=Mk::<W>::z(); let mut l=Mk::<W>::z();
        for _ in 0..nt { t.set(u16::from_le_bytes([b[pos],b[pos+1]]) as u32); pos+=2; } for _ in 0..nl { l.set(u16::from_le_bytes([b[pos],b[pos+1]]) as u32); pos+=2; } out.push((t,l)); } (out,pos) }
struct FamInfo{ full:u64, irr:usize, nodes:u64, secs:f64 }
// checkpointed, resumable family enumeration (irreducible blocks only when reduce=true). Files: logs/g1/fam_m{m}_t{tmax}.{ck,done}
fn family<const W:usize>(ctx:&Ctx<W>,pr:&Priv<W>,tmax:u32,reduce:bool,persist:bool)->(Vec<(Mk<W>,Mk<W>)>,FamInfo){
    let m=ctx.m; let ys:Vec<u32>=ctx.high.bits(); let us=units(ys.len()); let nu=us.len();
    let sfx=format!("{}{}",if minp()==-99 {String::new()} else {format!("_p{}",minp())},if negt()==99 {String::new()} else {format!("_n{}",negt())}); let fdone=format!("{}/logs/g1/fam_m{}_t{}{}.done",DIR,m,tmax,sfx); let fck=format!("{}/logs/g1/fam_m{}_t{}{}.ck",DIR,m,tmax,sfx);
    // header (u64 LE): magic, nu, ndone_units, full, nodes, nblk, secs_so_far(bits); then done bitmap (nu bytes); then blocks
    let read=|path:&str|->Option<(Vec<bool>,u64,u64,usize,f64,Vec<(Mk<W>,Mk<W>)>)>{ let b=std::fs::read(path).ok()?; if b.len()<56 {return None;}
        let r=|i:usize|u64::from_le_bytes(b[i*8..i*8+8].try_into().unwrap()); if r(0)!=0x47315F46414D0000+(reduce as u64) || r(1)!=nu as u64 {return None;}
        let done:Vec<bool>=b[56..56+nu].iter().map(|&x|x==1).collect(); let (bl,_)=get_blocks::<W>(&b,56+nu,r(5) as usize); Some((done,r(3),r(4),r(2) as usize,f64::from_bits(r(6)),bl)) };
    if persist { if let Some((_,full,nodes,_,secs,bl))=read(&fdone) { println!("family: complete file found ({} blocks)",bl.len()); return (bl.clone(),FamInfo{full,irr:bl.len(),nodes,secs}); } }
    let mut done=vec![false;nu]; let mut all:Vec<(Mk<W>,Mk<W>)>=vec![]; let mut full=0u64; let mut nodes=0u64; let mut secs0=0.0f64;
    if persist { if let Some((d,f,nd,_,s,bl))=read(&fck) { done=d; full=f; nodes=nd; secs0=s; all=bl; println!("RESUME family: {} of {} units done, {} blocks, full {} (secs so far {:.0})",done.iter().filter(|&&x|x).count(),nu,all.len(),full,secs0); } }
    let todo:Vec<usize>=(0..nu).filter(|&i|!done[i]).collect(); let ntodo=todo.len(); let next=AtomicUsize::new(0); let t0=Instant::now(); let d0=nu-ntodo;
    struct St<const W:usize>{ done:Vec<bool>, all:Vec<(Mk<W>,Mk<W>)>, full:u64, nodes:u64, nd:usize, lastp:f64, lastc:f64 }
    let st=Mutex::new(St::<W>{done,all,full,nodes,nd:d0,lastp:0.0,lastc:0.0});
    let write_ck=|g:&St<W>,path:&str,secs:f64|{ let mut b=vec![]; let h=[0x47315F46414D0000u64+(reduce as u64),nu as u64,g.nd as u64,g.full,g.nodes,g.all.len() as u64,secs.to_bits()]; for x in h { b.extend_from_slice(&x.to_le_bytes()); }
        for &d in &g.done { b.push(d as u8); } put_blocks(&mut b,&g.all); atomic_write(path,&b); };
    std::thread::scope(|sc|{ for _ in 0..nth() { sc.spawn(||{ let mut w=Wk{minp:minp(),ctx,pr,tmax,reduce,out:vec![],buf:vec![],full:0,nodes:0};
        loop { let i=next.fetch_add(1,Ordering::SeqCst); if i>=ntodo {break;} let ui=todo[i]; w.out.clear(); w.full=0; w.nodes=0; run_unit(&mut w,&ys,us[ui]);
            let mut g=st.lock().unwrap(); g.all.extend(w.out.drain(..)); g.full+=w.full; g.nodes+=w.nodes; g.done[ui]=true; g.nd+=1;
            let el=t0.elapsed().as_secs_f64();
            if el-g.lastp>=30.0 { g.lastp=el; let dn=g.nd-d0; let rate=dn as f64/el; println!("family m={} units {}/{} rate {:.1}/s eta {:.0}s blocks {} full {} elapsed {:.0}s rss {:.2}GB",m,g.nd,nu,rate,(nu-g.nd) as f64/rate.max(1e-9),g.all.len(),g.full,el,rss()); }
            if persist && el-g.lastc>=120.0 { g.lastc=el; write_ck(&g,&fck,secs0+el); } } }); } });
    let mut g=st.lock().unwrap(); let secs=secs0+t0.elapsed().as_secs_f64(); let mut v=std::mem::take(&mut g.all); v.sort(); v.dedup();
    let info=FamInfo{full:g.full,irr:v.len(),nodes:g.nodes,secs};
    if persist { g.all=v.clone(); write_ck(&g,&fdone,secs); let _=std::fs::remove_file(&fck); }
    (v,info) }

// ---------- local search (hard Y-disjointness, weighted uncovered lows) ----------
struct Rn(u64); impl Rn{ fn next(&mut self)->u64{ self.0^=self.0<<13; self.0^=self.0>>7; self.0^=self.0<<17; self.0 } fn below(&mut self,n:usize)->usize{ (self.next()%(n as u64)) as usize } }
struct Fam{ npos:Vec<u32>, n:usize, nb:usize, ny:Vec<u8>, ys:Vec<[u16;6]>, loff:Vec<u32>, lp:Vec<u16>, by_low:Vec<Vec<u32>> }
impl Fam{ fn y(&self,b:usize)->&[u16]{ &self.ys[b][..self.ny[b] as usize] } fn l(&self,b:usize)->&[u16]{ &self.lp[self.loff[b] as usize..self.loff[b+1] as usize] } }
fn make_fam<const W:usize>(blocks:&[(Mk<W>,Mk<W>)],low:&Mk<W>,n:usize)->(Fam,Vec<(Mk<W>,Mk<W>)>){
    let minp:i32=minp();
    let mut v:Vec<(Mk<W>,Mk<W>)>=blocks.iter().map(|(t,l)|(*t,l.and(low))).filter(|(t,l)|!t.is0()&&!l.is0()&&(l.cnt() as i32)>=need_l(t.cnt(),minp,negt())).collect(); v.sort(); v.dedup(); v.sort_by_key(|(t,l)|std::cmp::Reverse(l.cnt() as i32-t.cnt() as i32));  // stable: profit descending, so profit>=0 blocks come first
    let mut f=Fam{npos:vec![0;n],n,nb:v.len(),ny:vec![],ys:vec![],loff:vec![0],lp:vec![],by_low:vec![vec![];n]};
    for (i,(t,l)) in v.iter().enumerate(){ let tb=t.bits(); assert!(tb.len()<=6); let mut a=[0u16;6]; for (k,&y) in tb.iter().enumerate(){ a[k]=y as u16; } f.ny.push(tb.len() as u8); f.ys.push(a);
        for x in l.bits(){ f.lp.push(x as u16); f.by_low[x as usize].push(i as u32); } f.loff.push(f.lp.len() as u32); }
    (f,v) }
#[derive(Clone,Copy)] struct Par{ noise:u64, k:usize, t0:u64, tr:u64, hiw:bool, pf:u64 }
struct LS<'a>{ par:Par, f:&'a Fam, owner:Vec<i32>, cnt:Vec<u16>, w:Vec<i64>, unc:Vec<u16>, upos:Vec<i32>, insol:Vec<bool>, tabu:Vec<u64>, tmp:Vec<i32>, touched:Vec<u16>, rng:Rn, step:u64 }
impl<'a> LS<'a>{
    fn new(f:&'a Fam,lows:&[u32],seed:u64,par:Par)->LS<'a>{ let n=f.n; let mut s=LS{par,f,owner:vec![-1;n],cnt:vec![0;n],w:vec![1;n],unc:vec![],upos:vec![-1;n],insol:vec![false;f.nb],tabu:vec![0;f.nb],tmp:vec![0;n],touched:vec![],rng:Rn(seed.wrapping_mul(0x9E3779B97F4A7C15)|1),step:0};
        for &x in lows { s.upos[x as usize]=s.unc.len() as i32; s.unc.push(x as u16); } s }
    fn cover_add(&mut self,l:usize){ if self.cnt[l]==0 { let p=self.upos[l] as usize; let last=*self.unc.last().unwrap(); self.unc.swap_remove(p); if (last as usize)!=l { self.upos[last as usize]=p as i32; } self.upos[l]=-1; } self.cnt[l]+=1; }
    fn cover_del(&mut self,l:usize){ self.cnt[l]-=1; if self.cnt[l]==0 { self.upos[l]=self.unc.len() as i32; self.unc.push(l as u16); } }
    fn add(&mut self,b:usize){ let f=self.f; for &y in f.y(b) { self.owner[y as usize]=b as i32; } for &l in f.l(b) { self.cover_add(l as usize); } self.insol[b]=true; }
    fn del(&mut self,b:usize){ let f=self.f; for &y in f.y(b) { self.owner[y as usize]=-1; } for &l in f.l(b) { self.cover_del(l as usize); } self.insol[b]=false; }
    fn delta(&mut self,b:usize,rem:&mut [i32;6],nr:&mut usize)->i64{
        let f=self.f; *nr=0; for &y in f.y(b) { let o=self.owner[y as usize]; if o>=0 && !rem[..*nr].contains(&o) { rem[*nr]=o; *nr+=1; } }
        self.touched.clear();
        for k in 0..*nr { for &l in f.l(rem[k] as usize) { if self.tmp[l as usize]==0 { self.touched.push(l); } self.tmp[l as usize]-=1; } }
        for &l in f.l(b) { if self.tmp[l as usize]==0 { self.touched.push(l); } self.tmp[l as usize]+=1; }
        let mut d=0i64; for &l in &self.touched { let l=l as usize; let t=self.tmp[l]; if t!=0 { let old=self.cnt[l] as i32; let new=old+t; if old==0&&new>0 { d-=self.w[l]; } else if old>0&&new==0 { d+=self.w[l]; } } self.tmp[l]=0; }
        d }
    fn do_step(&mut self)->bool{ let noise=self.par.noise;
        if self.unc.is_empty(){ return true; }
        self.step+=1; let f=self.f; let u=if self.par.hiw { let mut bu=self.unc[0] as usize; let mut bw=-1i64; for k in 0..self.unc.len().min(1000) { let x=self.unc[self.rng.below(self.unc.len())] as usize; let w=self.w[x]; if w>bw {bw=w;bu=x;} } bu } else { self.unc[self.rng.below(self.unc.len())] as usize }; let cands=&f.by_low[u];
        let mut best=i64::MAX; let mut bb=usize::MAX; let mut ties=0u64; let mut rem=[0i32;6]; let mut nr=0usize;
        let rnd=self.rng.next()%1000<noise;
        if rnd { for _ in 0..8 { let b=cands[self.rng.below(cands.len())] as usize; if self.tabu[b]<=self.step { bb=b; break; } } }
        if bb==usize::MAX { let kk=self.par.k; let restrict=self.par.pf>0 && self.rng.next()%1000>=self.par.pf; let ncand=if restrict && f.npos[u]>0 {f.npos[u] as usize} else {cands.len()}; let cnt=if kk>0 && ncand>kk {kk} else {ncand}; for ii in 0..cnt { let b=if cnt==ncand {cands[ii]} else {cands[self.rng.below(ncand)]} as usize; if self.tabu[b]>self.step {continue;} let d=self.delta(b,&mut rem,&mut nr);
            if d<best { best=d; bb=b; ties=1; } else if d==best { ties+=1; if self.rng.next()%ties==0 { bb=b; } } } }
        if bb==usize::MAX { return false; }
        let d=self.delta(bb,&mut rem,&mut nr);
        if d>0 { for k in 0..self.unc.len(){ let l=self.unc[k] as usize; self.w[l]+=1; } }
        if self.step%64==0 { for l in 0..f.n { if self.w[l]>1 && self.rng.next()%16==0 { self.w[l]-=1; } } }
        for k in 0..nr { let c=rem[k] as usize; self.del(c); self.tabu[c]=self.step+self.par.t0+self.rng.next()%self.par.tr; }
        self.add(bb); false }
}

// ---------- certificates: parts, exact checker ----------
fn brute_cap<const W:usize>(es:&[Mk<W>],part:&Mk<W>)->u32{
    let el=part.bits(); let k=el.len(); assert!(k<=24,"part too large for brute force");
    let loc:Vec<u32>=es.iter().filter(|e|e.sub(part)).map(|e|{ let mut w=0u32; for (i,&b) in el.iter().enumerate(){ if e.has(b) { w|=1<<i; } } w }).collect();
    let mut best=0; for s in 0u32..(1u32<<k) { let c=s.count_ones(); if c<=best {continue;} if loc.iter().all(|&e| e&!s!=0) { best=c; } } best }
fn write_sol<const W:usize>(path:&str,parts:&[(Mk<W>,u32)]){ let mut s=String::new(); for (u,c) in parts { s.push_str(&format!("{}",c)); for b in u.bits() { s.push_str(&format!(" {}",b+1)); } s.push('\n'); } atomic_write(path,s.as_bytes()); }
fn read_sol<const W:usize>(path:&str)->Result<Vec<(Mk<W>,u32)>,String>{ let txt=std::fs::read_to_string(path).map_err(|e|e.to_string())?; let mut v=vec![];
    for line in txt.lines().filter(|l|!l.trim().is_empty()) { let mut it=line.split_whitespace(); let c:u32=it.next().unwrap().parse().map_err(|_|"bad cap".to_string())?; let mut u=Mk::<W>::z();
        for x in it { let x:u32=x.parse().map_err(|_|"bad velocity".to_string())?; if x<1 || x>64*W as u32 {return Err("velocity out of range".into());} u.set(x-1); } v.push((u,c)); } Ok(v) }
fn check_parts<const W:usize>(ed:&Edges<W>,parts:&[(Mk<W>,u32)],nsamp:u64)->Result<String,String>{
    let m=ed.m as u64; let n=2*m; let full=Mk::<W>::range(0,n as u32); let mut cov=Mk::<W>::z(); let mut sum=0u32; let mut maxsz=0;
    for (u,c) in parts { if !u.sub(&full) {return Err("part outside [1,2m]".into());} cov=cov.or(u); sum+=c; maxsz=maxsz.max(u.cnt());
        let b=brute_cap(&ed.es,u); if b!=*c {return Err(format!("capacity mismatch: brute {} claimed {}",b,c));} }
    if !full.sub(&cov) {return Err("not a cover of [1,2m]".into());}
    if sum as u64>m-1 {return Err(format!("sum {} > m-1",sum));}
    // each edge used (inside some part) re-derived from its rational witness
    let mut nused=0; for (i,e) in ed.es.iter().enumerate() { if parts.iter().any(|(u,_)| e.sub(u)) { nused+=1; let (p,q)=ed.wit[i]; if mask_of::<W>(ed.m,ed.n,p as u64,q as u64)!=*e {return Err("witness mismatch".into());} } }
    // completeness sampling: the mask of a random rational time must contain a listed minimal bad set
    let mut rng=Rn(0x1234567887654321u64^m); let mut nz=0u64;
    for _ in 0..nsamp { let q=2+rng.next()%2_000_000; let p=1+rng.next()%(q-1); let mk=mask_of::<W>(ed.m,ed.n,p,q); if mk.is0() {continue;} nz+=1;
        if !ed.es.iter().any(|e|e.sub(&mk)) {return Err(format!("completeness sample failed at t={}/{}",p,q));} }
    Ok(format!("CHECK OK: {} parts, sum cap {} <= {}, max part {}, {} witness times, brute force against {} minimal bad sets; completeness samples {} nonempty of {}",parts.len(),sum,m-1,maxsz,nused,ed.es.len(),nz,nsamp)) }
fn check_file<const W:usize>(m:u32,path:&str)->Result<String,String>{ let ed=edges_ev::<W>(m); let parts=read_sol::<W>(path)?; check_parts(&ed,&parts,200_000) }

// ---------- per-m pipeline ----------
fn finish_cert<const W:usize>(m:u32,ctx:&Ctx<W>,v:&[(Mk<W>,Mk<W>)],free:&Mk<W>,low:&Mk<W>,sol:&[usize])->Result<String,String>{
    let mut parts:Vec<(Mk<W>,u32)>=vec![]; let mut usedy=Mk::<W>::z(); let mut cov=Mk::<W>::z();
    for &b in sol { let (t,l)=v[b]; if usedy.meets(&t) {return Err("T overlap".into());} usedy=usedy.or(&t); cov=cov.or(&l); parts.push((t.or(&l),t.cnt())); }
    if !low.sub(&cov) {return Err("lows not covered".into());}
    if !free.is0() { parts.push((*free,0)); }
    let mut left:Vec<u32>=ctx.high.andn(&usedy).bits(); while !left.is_empty(){ let k=left.len().min(8); let mut c=Mk::<W>::z(); for _ in 0..k { c.set(left.pop().unwrap()); } parts.push((c,c.cnt())); }
    let out=format!("{}/certs/m{}.g1.sol",DIR,m); write_sol(&out,&parts);
    let tc=Instant::now(); let r=check_file::<W>(m,&out); let t_chk=tc.elapsed().as_secs_f64();
    match r { Ok(msg)=>Ok(format!("{} check {:.1}s",msg,t_chk)), Err(e)=>{ let _=std::fs::remove_file(&out); Err(e) } } }
// GLPK fallback (binary solver; model written by Rust, solution parsed by Rust). Complete-family result: if glpsol proves optimum > 0 it is a
// floating-point statement about the whole irreducible family (HEURISTIC-grade, not exact).
fn glp<const W:usize>(m:u32,secs:u64,tmax:u32){
    wait_load(); let t0=Instant::now(); let ed=edges_ev::<W>(m); let ctx=Ctx::<W>::new(m,ed.es.clone()); let pr=build_priv(&ctx); let free=pr.free; let low=ctx.low.andn(&free);
    let (blocks,_)=family::<W>(&ctx,&pr,tmax,true,true); let (f,v)=make_fam(&blocks,&low,ctx.n as usize); drop(blocks);
    let lp=format!("{}/logs/g1/glp_m{}.lp",DIR,m); let solf=format!("{}/logs/g1/glp_m{}.out",DIR,m);
    { use std::io::Write; let mut w=std::io::BufWriter::new(std::fs::File::create(&lp).unwrap()); let lows=low.bits();
      write!(w,"Minimize\n obj:").unwrap(); for &l in &lows { write!(w," + s{}",l+1).unwrap(); } writeln!(w,"\nSubject To").unwrap();
      let mut yl:Vec<Vec<usize>>=vec![vec![];f.n]; for b in 0..f.nb { for &y in f.y(b) { yl[y as usize].push(b); } }
      for &l in &lows { write!(w," L{}:",l+1).unwrap(); for &b in &f.by_low[l as usize] { write!(w," + x{}",b).unwrap(); } writeln!(w," + s{} >= 1",l+1).unwrap(); }
      for y in ctx.high.bits() { let y=y as usize; if yl[y].is_empty() {continue;} write!(w," Y{}:",y+1).unwrap(); for &b in &yl[y] { write!(w," + x{}",b).unwrap(); } writeln!(w," <= 1").unwrap(); }
      writeln!(w,"Bounds").unwrap(); for &l in &lows { writeln!(w," 0 <= s{} <= 1",l+1).unwrap(); } writeln!(w,"Binary").unwrap(); for b in 0..f.nb { writeln!(w," x{}",b).unwrap(); } writeln!(w,"End").unwrap(); }
    println!("glp m={} LP written ({} columns), launching glpsol --tmlim {} (RSS polled, killed above 4 GB)",m,f.nb,secs);
    let mut ch=std::process::Command::new("nice").args(["-n","10","glpsol","--cpxlp",&lp,"-o",&solf,"--tmlim",&secs.to_string(),"--mipgap","0"]).stdout(std::fs::File::create(format!("{}/logs/g1/glp_m{}.log",DIR,m)).unwrap()).spawn().expect("glpsol");
    let pid=ch.id(); let mut killed=false; loop { match ch.try_wait().unwrap() { Some(_)=>break, None=>{ std::thread::sleep(std::time::Duration::from_secs(5));
        let o=std::process::Command::new("ps").args(["-o","rss=","-p",&pid.to_string()]).output().unwrap(); let kb:f64=String::from_utf8_lossy(&o.stdout).trim().parse().unwrap_or(0.0);
        if kb/1e6>4.0 { println!("glpsol RSS {:.2} GB > 4 GB, killing",kb/1e6); let _=ch.kill(); killed=true; } } } }
    let _=std::fs::remove_file(&lp);
    let txt=std::fs::read_to_string(&solf).unwrap_or_default(); let mut chosen:Vec<usize>=vec![]; let mut incol=false; let mut obj=String::new();
    for l in txt.lines(){ if l.starts_with("Objective:") { obj=l.to_string(); } if l.contains("Column name") {incol=true;continue;} if !incol {continue;} let t:Vec<&str>=l.split_whitespace().collect();
        if t.len()>=3 && t[1].starts_with('x') { let off= if t[2]=="*" {3} else {2}; if let Some(x)=t.get(off){ if x.parse::<f64>().map(|y|y>0.5).unwrap_or(false) { chosen.push(t[1][1..].parse().unwrap()); } } } }
    let st=txt.lines().find(|l|l.starts_with("Status:")).unwrap_or("Status: none").to_string();
    println!("glp m={} killed={} {} {} chosen {} time {:.0}s",m,killed,st,obj,chosen.len(),t0.elapsed().as_secs_f64());
    if obj.contains("= 0 ") || obj.ends_with("= 0") { match finish_cert::<W>(m,&ctx,&v,&free,&low,&chosen) { Ok(msg)=>{ println!("GLP RESULT m={} OK {}",m,msg); }, Err(e)=>println!("GLP RESULT m={} CHECKFAIL {}",m,e) } } else { println!("GLP RESULT m={} NO COVER FOUND ({} {}) (float solver; UNDECIDED unless status says optimal with obj>0)",m,st,obj); }
}

fn ls_run<const W:usize>(m:u32,f:&Fam,v:&[(Mk<W>,Mk<W>)],lows:&[u32],secs:f64,seed0:u64)->Option<(Vec<usize>,u64,u64)>{
    // restart schedule per thread: trial k runs min(20*2^(k/3), 300) s with a fresh seed; first success stops all threads
    let par=Par{noise:0,k:0,t0:2,tr:6,hiw:false,pf:0}; let t0=Instant::now(); let stop=AtomicBool::new(false); let result:Mutex<Option<(Vec<usize>,u64,u64)>>=Mutex::new(None); let _=v;
    let totsteps=AtomicU64::new(0);
    std::thread::scope(|sc|{ for th in 0..nth() as u64 { let (stop,result,totsteps)=(&stop,&result,&totsteps); sc.spawn(move||{
        let mut trial=0u64; let mut tl=Instant::now();
        while !stop.load(Ordering::Relaxed) && t0.elapsed().as_secs_f64()<secs {
            let seed=seed0*1_000_000+th*10_000+trial; let lim=(20.0*2f64.powi((trial/3) as i32)).min(300.0); trial+=1; let ts=Instant::now(); let mut s=LS::new(f,lows,seed,par); let mut best=s.unc.len(); let mut last=0u64;
            loop { if stop.load(Ordering::Relaxed) {break;}
                if s.do_step() { let sol:Vec<usize>=(0..f.nb).filter(|&b|s.insol[b]).collect(); *result.lock().unwrap()=Some((sol,seed,s.step)); stop.store(true,Ordering::SeqCst); break; }
                if s.unc.len()<best { best=s.unc.len(); }
                if s.step&0xFF==0 { if ts.elapsed().as_secs_f64()>lim || t0.elapsed().as_secs_f64()>secs {break;}
                    if th==0 && tl.elapsed().as_secs()>=30 { let r=(s.step-last) as f64/tl.elapsed().as_secs_f64(); last=s.step; tl=Instant::now();
                        println!("ls m={} thread0 trial {} (limit {:.0}s) steps {} rate {:.0}/s uncovered {} best {} elapsed {:.0}s/{:.0}s (stochastic, no ETA) rss {:.2}GB",m,trial-1,lim,s.step,r,s.unc.len(),best,t0.elapsed().as_secs_f64(),secs,rss()); } } }
            totsteps.fetch_add(s.step,Ordering::Relaxed); } }); } });
    let r=result.lock().unwrap().clone(); r }
fn run_m<const W:usize>(m:u32,secs:f64,seed0:u64,tmax:u32)->String{
    // stages: block family restricted to profit |L|-|T| >= 0, then >= -1, then the full irreducible family; first success stops.
    // Stage limits: secs, 2*secs, 3*secs (LS wall time). A cover is a cover whatever stage found it (exact checker).
    wait_load(); let t0=Instant::now(); let q=2*m as u64+1;
    let ed=edges_ev::<W>(m); let ctx=Ctx::<W>::new(m,ed.es.clone()); assert!(ctx.y_independent(),"Y not independent"); let t_edges=t0.elapsed().as_secs_f64();
    let pr=build_priv(&ctx); let free=pr.free; let low=ctx.low.andn(&free); let lows:Vec<u32>=low.bits();
    println!("m={} 2m+1={}={} W={} minimal bad sets {} (event masks {}), edges {:.1}s",m,q,factor(q),W,ed.es.len(),ed.nraw,t_edges);
    let mut status=String::from("UNDECIDED"); let mut chk=String::new(); let mut tot_fam=0.0; let mut tot_ls=0.0; let mut last=(0u64,0usize,0u32); let mut stagelog=vec![];
    for (si,&(mp,ng)) in [(0i32,99u32),(-1,3),(-1,99),(-99,99)].iter().enumerate() {
        MINP.store(mp,Ordering::Relaxed); NEGT.store(ng,Ordering::Relaxed); wait_load(); let tf=Instant::now();
        let (blocks,info)=family::<W>(&ctx,&pr,tmax,true,true); let t_fam=tf.elapsed().as_secs_f64(); tot_fam+=t_fam; let rfam=rss();
        let (f,v)=make_fam(&blocks,&low,ctx.n as usize); drop(blocks); last=(info.full,f.nb,mp as u32);
        println!("m={} stage minprofit {}: kept blocks (pre-reduction) {} irreducible {} (usable {}) nodes {} enumeration wall {:.0}s (cumulative {:.0}s) peakRSS {:.2}GB",m,mp,info.full,info.irr,f.nb,info.nodes,t_fam,info.secs,rfam);
        let lim=secs*(si as f64+1.0).min(3.0); let tl0=Instant::now(); let res=ls_run::<W>(m,&f,&v,&lows,lim,seed0); let mut t_ls=tl0.elapsed().as_secs_f64();
        let mut found:Option<(Vec<usize>,String)>=None; let mut satst=String::from("-");
        if let Some((sol,seed,steps))=res { found=Some((sol,format!("LS seed {} steps {}",seed,steps))); }
        else { let ts=Instant::now(); let (st,sol)=sat_try(m,&f,&lows,2.0*secs,mp); t_ls+=ts.elapsed().as_secs_f64(); satst=st; if let Some(sol)=sol { found=Some((sol,"kissat".to_string())); } }
        tot_ls+=t_ls; stagelog.push(format!("p>={}{}:{}blk,fam{:.0}s,ls+sat{:.0}s,sat={}",mp,if ng<99 {format!(",negT<={}",ng)} else {String::new()},f.nb,t_fam,t_ls,satst));
        if let Some((sol,how))=found {
            match finish_cert::<W>(m,&ctx,&v,&free,&low,&sol) {
                Ok(msg)=>{ status="OK".to_string(); chk=format!("{} (minprofit {}, {}, blocks {})",msg,mp,how,sol.len()); for &(x,y) in [(0i32,99u32),(-1,3),(-1,99),(-99,99)].iter() { let sf=format!("{}{}",if x==-99 {String::new()} else {format!("_p{}",x)},if y==99 {String::new()} else {format!("_n{}",y)}); let _=std::fs::remove_file(format!("{}/logs/g1/fam_m{}_t{}{}.done",DIR,m,tmax,sf)); } break; }
                Err(e)=>{ status="CHECKFAIL".to_string(); chk=e; break; } } } }
    MINP.store(-99,Ordering::Relaxed); NEGT.store(99,Ordering::Relaxed);
    if status=="UNDECIDED" { chk=format!("no cover; stages {}",stagelog.join(" ")); }
    else { chk=format!("{} | stages {}",chk,stagelog.join(" ")); }
    let line=format!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.0}\t{:.0}\t{:.0}\t{:.2}\t{}\t{}\t{}",m,q,factor(q),ed.es.len(),last.0,last.1,tmax,tot_fam,tot_fam,tot_ls,rss(),status,chk,last.2 as i32);
    println!("RESULT {}",line); line }

macro_rules! disp { ($m:expr,$f:ident,$($a:expr),*)=>{ match (2*($m as usize)+63)/64 { 1|2=>$f::<2>($($a),*), 3=>$f::<3>($($a),*), 4=>$f::<4>($($a),*), 5=>$f::<5>($($a),*), 6=>$f::<6>($($a),*), 7=>$f::<7>($($a),*), 8=>$f::<8>($($a),*), _=>panic!("m too large") } } }

fn edgetest<const W:usize>(m:u32){ let t0=Instant::now(); let a=edges_ev::<W>(m); let ta=t0.elapsed().as_secs_f64(); let t1=Instant::now(); let b=edges_old::<W>(m,nth()); let tb=t1.elapsed().as_secs_f64();
    let sa:HashSet<Mk<W>>=a.es.iter().cloned().collect(); let sb:HashSet<Mk<W>>=b.es.iter().cloned().collect();
    println!("EDGETEST m={} event method: {} minimal bad sets ({:.2}s); old rational method: {} ({:.1}s); identical sets: {}",m,a.es.len(),ta,b.es.len(),tb,sa==sb); if sa!=sb { std::process::exit(1); } }
fn famtest<const W:usize>(m:u32,tmax:u32){ watchdog(RSSCAP); let t0=Instant::now(); let ed=edges_ev::<W>(m); let ctx=Ctx::<W>::new(m,ed.es.clone()); assert!(ctx.y_independent()); let pr=build_priv(&ctx);
    let (b,info)=family::<W>(&ctx,&pr,tmax,true,false); println!("FAM m={} edges {} kept(full) {} irreducible {} nodes {} time {:.1}s peakRSS {:.2}GB",m,ed.es.len(),info.full,b.len(),info.nodes,t0.elapsed().as_secs_f64(),rss()); }
fn brute<const W:usize>(m:u32){ watchdog(RSSCAP); let ed=edges_ev::<W>(m); let ctx=Ctx::<W>::new(m,ed.es.clone()); let pr=build_priv(&ctx); let (fam,info)=family::<W>(&ctx,&pr,4,false,false);
    println!("full family {} blocks (kept {})",fam.len(),info.full); let low=ctx.low.andn(&pr.free); let lb=low.bits(); let yb=ctx.high.bits(); let nl=lb.len(); assert!(nl<=24);
    let mut tsets:Vec<Mk<W>>=vec![]; fn rec<const W:usize>(yb:&[u32],i:usize,cur:Mk<W>,k:usize,out:&mut Vec<Mk<W>>){ out.push(cur); if k==4 {return;} for j in i..yb.len(){ let mut c=cur; c.set(yb[j]); rec(yb,j+1,c,k+1,out); } }
    rec(&yb,0,Mk::z(),0,&mut tsets); let nt=tsets.len(); let next=AtomicUsize::new(0); let pairs=AtomicU64::new(0); let nval=AtomicU64::new(0); let undom=AtomicU64::new(0); let t0=Instant::now();
    std::thread::scope(|sc|{ for _ in 0..nth() { sc.spawn(||{ let mut buf=vec![]; loop { let i=next.fetch_add(1,Ordering::SeqCst); if i>=nt {break;} let t=tsets[i];
        let sub:Vec<&(Mk<W>,Mk<W>)>=fam.iter().filter(|(t2,_)|t2.sub(&t)).collect();
        for lm in 1u32..(1u32<<nl) { let mut l=Mk::<W>::z(); for k in 0..nl { if lm>>k&1==1 { l.set(lb[k]); } }
            pairs.fetch_add(1,Ordering::Relaxed); if ctx.valid(&t.or(&l),&mut buf) { nval.fetch_add(1,Ordering::Relaxed); if !sub.iter().any(|(_,l2)| l.sub(l2)) { undom.fetch_add(1,Ordering::Relaxed); } } }
        if i%200==0 { let el=t0.elapsed().as_secs_f64(); println!("brute T {}/{} elapsed {:.0}s eta {:.0}s",i,nt,el,el*(nt-i) as f64/(i+1) as f64); } } }); } });
    println!("BRUTE m={} (T,L) pairs tested {} valid {} undominated by full family {} time {:.0}s",m,pairs.load(Ordering::Relaxed),nval.load(Ordering::Relaxed),undom.load(Ordering::Relaxed),t0.elapsed().as_secs_f64()); }


fn lsbench<const W:usize>(m:u32,total:f64,trial:f64,par:Par){ let ed=edges_ev::<W>(m); let ctx=Ctx::<W>::new(m,ed.es.clone()); let pr=build_priv(&ctx); let low=ctx.low.andn(&pr.free); let lows=low.bits();
    let (blocks,_)=family::<W>(&ctx,&pr,4,true,true); let (f,_v)=make_fam(&blocks,&low,ctx.n as usize); let t0=Instant::now(); let seedc=AtomicU64::new(1000); let res:Mutex<Vec<(u64,f64,bool,usize)>>=Mutex::new(vec![]);
    std::thread::scope(|sc|{ for _ in 0..nth() { sc.spawn(||{ loop { if t0.elapsed().as_secs_f64()+trial*0.0>total {break;} let seed=seedc.fetch_add(1,Ordering::SeqCst); let mut s=LS::new(&f,&lows,seed,par); let ts=Instant::now(); let mut ok=false; let mut best=usize::MAX;
        let mut bu:Vec<u16>=vec![]; loop { if s.do_step() {ok=true;break;} if s.unc.len()<best { best=s.unc.len(); bu=s.unc.clone(); } if s.step&0xFF==0 && (ts.elapsed().as_secs_f64()>trial || t0.elapsed().as_secs_f64()>total) {break;} }
        if std::env::var("LSDIAG").is_ok() { let mut v:Vec<u32>=bu.iter().map(|&x|x as u32+1).collect(); v.sort(); println!("DIAG seed {} ok {} best {} uncovered velocities {:?}",seed,ok,best,v); }
        res.lock().unwrap().push((seed,ts.elapsed().as_secs_f64(),ok,best)); } }); } });
    let r=res.lock().unwrap(); let mut okt:Vec<f64>=r.iter().filter(|x|x.2).map(|x|x.1).collect(); okt.sort_by(|a,b|a.partial_cmp(b).unwrap()); let tot:f64=r.iter().map(|x|x.1).sum();
    println!("LSBENCH m={} noise={} k={} tabu={}+{} hiw={} trials {} solved {} total cpu-s {:.0} cpu-s per solve {:.1} solved times {:?}",m,par.noise,par.k,par.t0,par.tr,par.hiw,r.len(),okt.len(),tot,tot/(okt.len().max(1) as f64),okt.iter().map(|x|(x*10.0).round()/10.0).collect::<Vec<_>>()); }
// SAT route: pure SAT (every low covered; every Y in at most one block, sequential-counter AMO). Output DIMACS; solver run as a binary.
fn write_cnf(f:&Fam,lows:&[u32],out:&str)->(i64,usize){
    use std::io::Write; let mut cl:Vec<Vec<i64>>=vec![]; let mut nv=f.nb as i64;
    for &l in lows { cl.push(f.by_low[l as usize].iter().map(|&b|b as i64+1).collect()); }
    let mut yl:Vec<Vec<usize>>=vec![vec![];f.n]; for b in 0..f.nb { for &y in f.y(b) { yl[y as usize].push(b); } }
    for y in 0..f.n { let v=&yl[y]; if v.len()<2 {continue;} let k=v.len(); let base=nv; nv+=k as i64-1;
        for i in 0..k { let x=v[i] as i64+1; if i<k-1 { cl.push(vec![-x,base+i as i64+1]); } if i>0 && i<k-1 { cl.push(vec![-(base+i as i64),base+i as i64+1]); } if i>0 { cl.push(vec![-x,-(base+i as i64)]); } } }
    let mut w=std::io::BufWriter::new(std::fs::File::create(out).unwrap()); writeln!(w,"p cnf {} {}",nv,cl.len()).unwrap(); for c in &cl { for x in c { write!(w,"{} ",x).unwrap(); } writeln!(w,"0").unwrap(); }
    (nv,cl.len()) }
fn cnf<const W:usize>(m:u32,tmax:u32,seedperm:u64){
    let ed=edges_ev::<W>(m); let ctx=Ctx::<W>::new(m,ed.es.clone()); let pr=build_priv(&ctx); let low=ctx.low.andn(&pr.free); let lows=low.bits(); let _=seedperm;
    let (blocks,_)=family::<W>(&ctx,&pr,tmax,true,true); let (f,_v)=make_fam(&blocks,&low,ctx.n as usize); drop(blocks);
    let out=format!("{}/logs/g1/sat_m{}.cnf",DIR,m); let (nv,nc)=write_cnf(&f,&lows,&out);
    println!("cnf m={} vars {} clauses {} blocks {} written {}",m,nv,nc,f.nb,out); }
// SAT stage: kissat (binary) on the exact-cover CNF of the current family; returns status string and chosen block indices. UNSAT is a statement about THIS family only.
fn sat_try(m:u32,f:&Fam,lows:&[u32],secs:f64,mp:i32)->(String,Option<Vec<usize>>){
    let cnf=format!("{}/logs/g1/sat_m{}_p{}.cnf",DIR,m,mp); let outf=format!("{}/logs/g1/sat_m{}_p{}.out",DIR,m,mp); let (nv,nc)=write_cnf(f,lows,&cnf);
    println!("m={} SAT stage minprofit {}: vars {} clauses {} kissat --time={}",m,mp,nv,nc,secs.ceil());
    let mut ch=std::process::Command::new("nice").args(["-n","10","kissat",&format!("--time={}",secs.ceil() as u64),&cnf]).stdout(std::fs::File::create(&outf).unwrap()).spawn().expect("kissat");
    let pid=ch.id(); loop { match ch.try_wait().unwrap() { Some(_)=>break, None=>{ std::thread::sleep(std::time::Duration::from_secs(2));
        let o=std::process::Command::new("ps").args(["-o","rss=","-p",&pid.to_string()]).output().unwrap(); let kb:f64=String::from_utf8_lossy(&o.stdout).trim().parse().unwrap_or(0.0);
        if kb/1e6>3.5 { println!("kissat RSS {:.2} GB too large, killing",kb/1e6); let _=ch.kill(); } } } }
    let txt=std::fs::read_to_string(&outf).unwrap_or_default(); let _=std::fs::remove_file(&cnf);
    let st=txt.lines().find(|l|l.starts_with("s ")).unwrap_or("s NONE").to_string();
    if st.contains("UNSATISFIABLE") { let _=std::fs::remove_file(&outf); return ("UNSAT".into(),None); }
    if st.contains("SATISFIABLE") { let mut chosen=vec![]; for l in txt.lines() { if l.starts_with("v ") { for t in l[2..].split_whitespace() { let x:i64=t.parse().unwrap(); if x>0 && (x as usize)<=f.nb { chosen.push(x as usize-1); } } } } let _=std::fs::remove_file(&outf); return ("SAT".into(),Some(chosen)); }
    let _=std::fs::remove_file(&outf); ("UNKNOWN".into(),None) }
// parse a SAT solver model (lines "v ..."), assemble and check the certificate
fn satmodel<const W:usize>(m:u32,tmax:u32,modelfile:&str){
    let ed=edges_ev::<W>(m); let ctx=Ctx::<W>::new(m,ed.es.clone()); let pr=build_priv(&ctx); let free=pr.free; let low=ctx.low.andn(&free);
    let (blocks,_)=family::<W>(&ctx,&pr,tmax,true,true); let (f,v)=make_fam(&blocks,&low,ctx.n as usize); drop(blocks);
    let txt=std::fs::read_to_string(modelfile).unwrap(); let mut chosen=vec![]; for l in txt.lines() { if l.starts_with("v ") { for t in l[2..].split_whitespace() { let x:i64=t.parse().unwrap(); if x>0 && (x as usize)<=f.nb { chosen.push(x as usize-1); } } } }
    match finish_cert::<W>(m,&ctx,&v,&free,&low,&chosen) { Ok(msg)=>println!("SAT RESULT m={} OK {} blocks {}",m,msg,chosen.len()), Err(e)=>println!("SAT RESULT m={} CHECKFAIL {}",m,e) } }
fn lowcov<const W:usize>(m:u32){ let ed=edges_ev::<W>(m); let ctx=Ctx::<W>::new(m,ed.es.clone()); let pr=build_priv(&ctx); let low=ctx.low.andn(&pr.free);
    let (blocks,_)=family::<W>(&ctx,&pr,4,true,true); let mut cnt:std::collections::BTreeMap<u32,[u32;4]>=Default::default(); for l in low.bits() { cnt.insert(l,[0;4]); }
    for (t,l) in &blocks { let p=l.and(&low).cnt() as i32-t.cnt() as i32; let k=if p>=1 {0} else if p==0 {1} else if p==-1 {2} else {3}; for x in l.and(&low).bits() { cnt.get_mut(&x).unwrap()[k]+=1; } }
    let mut zero=vec![]; let mut zero1=vec![]; for (x,c) in &cnt { if c[0]+c[1]==0 { zero.push(x+1); } else if c[0]+c[1]<=3 { zero1.push((x+1,c[0]+c[1])); } }
    println!("LOWCOV m={} lows {} lows with no profit>=0 block: {:?} ; with 1..3: {:?}",m,cnt.len(),zero,zero1); }
fn main(){
    let a:Vec<String>=std::env::args().collect(); watchdog(RSSCAP); if let Some(x)=std::env::var("G1_MINPROFIT").ok().and_then(|x|x.parse::<i32>().ok()) { MINP.store(x,Ordering::Relaxed); } if let Some(x)=std::env::var("G1_NEGT").ok().and_then(|x|x.parse::<u32>().ok()) { NEGT.store(x,Ordering::Relaxed); }
    match a[1].as_str(){
        "edgetest"=>{ let m:u32=a[2].parse().unwrap(); disp!(m,edgetest,m) }
        "fam"=>{ let m:u32=a[2].parse().unwrap(); let tmax:u32=a.get(3).map(|s|s.parse().unwrap()).unwrap_or(4); disp!(m,famtest,m,tmax) }
        "lsbench"=>{ let m:u32=a[2].parse().unwrap(); let par=Par{noise:a[5].parse().unwrap(),k:a[6].parse().unwrap(),t0:a[7].parse().unwrap(),tr:a[8].parse().unwrap(),hiw:a.get(9).map(|x|x=="1").unwrap_or(false),pf:a.get(10).map(|x|x.parse().unwrap()).unwrap_or(0)}; disp!(m,lsbench,m,a[3].parse().unwrap(),a[4].parse().unwrap(),par) }
        "brute"=>{ let m:u32=a[2].parse().unwrap(); disp!(m,brute,m) }
        "lowcov"=>{ let m:u32=a[2].parse().unwrap(); disp!(m,lowcov,m) }
        "cnf"=>{ let m:u32=a[2].parse().unwrap(); disp!(m,cnf,m,4,0) }
        "satmodel"=>{ let m:u32=a[2].parse().unwrap(); disp!(m,satmodel,m,4,&a[3]) }
        "glp"=>{ let m:u32=a[2].parse().unwrap(); disp!(m,glp,m,a[3].parse().unwrap(),4) }
        "check"=>{ let m:u32=a[2].parse().unwrap(); let r:Result<String,String>=disp!(m,check_file,m,&a[3]); match r { Ok(s)=>println!("{}",s), Err(e)=>{ println!("CHECK FAILED: {}",e); std::process::exit(1);} } }
        "run"=>{ let lo:u32=a[2].parse().unwrap(); let hi:u32=a[3].parse().unwrap(); let secs:f64=a[4].parse().unwrap(); let seed0:u64=a.get(5).map(|s|s.parse().unwrap()).unwrap_or(1); let tmax:u32=a.get(6).map(|s|s.parse().unwrap()).unwrap_or(4);
            let resf=format!("{}/logs/g1/results.tsv",DIR); let list:Vec<u32>=(lo..=hi).filter(|&m|!is_prime(2*m as u64+1)).collect(); println!("driver: {} composite 2m+1 for m in {}..={}",list.len(),lo,hi); let tstart=Instant::now(); let mut done=0;
            for &m in &list { let solf=format!("{}/certs/m{}.g1.sol",DIR,m);
                if std::path::Path::new(&solf).exists() { println!("m={} already has certs/m{}.g1.sol, skipping (verified earlier in a results row)",m,m); done+=1; continue; }
                if std::env::var("G1_SKIP_UNDEC").is_ok() { let prev=std::fs::read_to_string(&resf).unwrap_or_default(); let hit=prev.lines().any(|l|{ let c:Vec<&str>=l.split('\t').collect(); c.len()>13 && c[0]==m.to_string() && c[11]=="UNDECIDED" && c[9].parse::<f64>().map(|x|x>=secs-1.0).unwrap_or(false) });
                    if hit { println!("m={} already UNDECIDED at >= {}s, skipped (G1_SKIP_UNDEC)",m,secs); done+=1; continue; } }
                let line=disp!(m,run_m,m,secs,seed0,tmax); use std::io::Write; let mut fh=std::fs::OpenOptions::new().create(true).append(true).open(&resf).unwrap(); writeln!(fh,"{}",line).unwrap(); done+=1;
                let el=tstart.elapsed().as_secs_f64(); println!("DRIVER done {}/{} m-values, elapsed {:.0}s, eta (rough) {:.0}s",done,list.len(),el,el/done as f64*(list.len()-done) as f64); } }
        _=>eprintln!("unknown command")
    }
}
