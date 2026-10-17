// g1: dense-window covers beyond m = 62 (queue G1). Generic W-word masks (2m <= 64*W), exact integer arithmetic.
//   g1 edgetest M            event-point edge enumeration vs old rational enumeration (equal minimal families?)
//   g1 fam M [tmax]          family stage only: enumerate |T|<=tmax blocks, exact irreducible reduction, stats
//   g1 brute M               brute-force domination test of the full family (all (T,L), |T|<=4, L subset Low')  (m <= 17)
//   g1 run LO HI SECS [seed0] [tmax]   driver: for every composite 2m+1, LO<=m<=HI: family, local search, exact check
//   g1 check M file          independent exact checker of certs/m<M>.g1.sol (line format: "cap v1 v2 ...", velocities 1-based)
// Resource rules: <= 3 threads, internal RSS watchdog (3.9 GB), outputs under logs/gap and certs/. Resumable.
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
        for y in last..self.ctx.n { if !self.ctx.high.has(y) {continue;} if k+1==self.tmax && self.pr.by_y[y as usize].is_empty() {continue;} let (t2,c2)=self.add_y(t,c,y); self.dfs_t(&t2,k+1,y+1,&c2); } }
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
// checkpointed, resumable family enumeration (irreducible blocks only when reduce=true). Files: logs/gap/fam_m{m}_t{tmax}.{ck,done}
fn family<const W:usize>(ctx:&Ctx<W>,pr:&Priv<W>,tmax:u32,reduce:bool,persist:bool)->(Vec<(Mk<W>,Mk<W>)>,FamInfo){
    let m=ctx.m; let ys:Vec<u32>=ctx.high.bits(); let us=units(ys.len()); let nu=us.len();
    let sfx=format!("{}{}",if minp()==-99 {String::new()} else {format!("_p{}",minp())},if negt()==99 {String::new()} else {format!("_n{}",negt())}); let fdone=format!("{}/logs/gap/fam_m{}_t{}{}.done",DIR,m,tmax,sfx); let fck=format!("{}/logs/gap/fam_m{}_t{}{}.ck",DIR,m,tmax,sfx);
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
struct LS<'a>{ par:Par, f:&'a Fam, owner:Vec<i32>, cnt:Vec<u16>, w:Vec<i64>, unc:Vec<u16>, upos:Vec<i32>, insol:Vec<bool>, tabu:Vec<u64>, tmp:Vec<i32>, touched:Vec<u16>, rng:Rn, step:u64, hash:u64 }
impl<'a> LS<'a>{
    fn new(f:&'a Fam,lows:&[u32],seed:u64,par:Par)->LS<'a>{ let n=f.n; let mut s=LS{par,f,owner:vec![-1;n],cnt:vec![0;n],w:vec![1;n],unc:vec![],upos:vec![-1;n],insol:vec![false;f.nb],tabu:vec![0;f.nb],tmp:vec![0;n],touched:vec![],rng:Rn(seed.wrapping_mul(0x9E3779B97F4A7C15)|1),step:0,hash:0};
        for &x in lows { s.upos[x as usize]=s.unc.len() as i32; s.unc.push(x as u16); } s }
    fn cover_add(&mut self,l:usize){ if self.cnt[l]==0 { let p=self.upos[l] as usize; let last=*self.unc.last().unwrap(); self.unc.swap_remove(p); if (last as usize)!=l { self.upos[last as usize]=p as i32; } self.upos[l]=-1; } self.cnt[l]+=1; }
    fn cover_del(&mut self,l:usize){ self.cnt[l]-=1; if self.cnt[l]==0 { self.upos[l]=self.unc.len() as i32; self.unc.push(l as u16); } }
    fn add(&mut self,b:usize){ let f=self.f; for &y in f.y(b) { self.owner[y as usize]=b as i32; } for &l in f.l(b) { self.cover_add(l as usize); } self.insol[b]=true; self.hash^=splitmix(b as u64); }
    fn del(&mut self,b:usize){ let f=self.f; for &y in f.y(b) { self.owner[y as usize]=-1; } for &l in f.l(b) { self.cover_del(l as usize); } self.insol[b]=false; self.hash^=splitmix(b as u64); }
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
    let lp=format!("{}/logs/gap/glp_m{}.lp",DIR,m); let solf=format!("{}/logs/gap/glp_m{}.out",DIR,m);
    { use std::io::Write; let mut w=std::io::BufWriter::new(std::fs::File::create(&lp).unwrap()); let lows=low.bits();
      write!(w,"Minimize\n obj:").unwrap(); for &l in &lows { write!(w," + s{}",l+1).unwrap(); } writeln!(w,"\nSubject To").unwrap();
      let mut yl:Vec<Vec<usize>>=vec![vec![];f.n]; for b in 0..f.nb { for &y in f.y(b) { yl[y as usize].push(b); } }
      for &l in &lows { write!(w," L{}:",l+1).unwrap(); for &b in &f.by_low[l as usize] { write!(w," + x{}",b).unwrap(); } writeln!(w," + s{} >= 1",l+1).unwrap(); }
      for y in ctx.high.bits() { let y=y as usize; if yl[y].is_empty() {continue;} write!(w," Y{}:",y+1).unwrap(); for &b in &yl[y] { write!(w," + x{}",b).unwrap(); } writeln!(w," <= 1").unwrap(); }
      writeln!(w,"Bounds").unwrap(); for &l in &lows { writeln!(w," 0 <= s{} <= 1",l+1).unwrap(); } writeln!(w,"Binary").unwrap(); for b in 0..f.nb { writeln!(w," x{}",b).unwrap(); } writeln!(w,"End").unwrap(); }
    println!("glp m={} LP written ({} columns), launching glpsol --tmlim {} (RSS polled, killed above 4 GB)",m,f.nb,secs);
    let mut ch=std::process::Command::new("nice").args(["-n","10","glpsol","--cpxlp",&lp,"-o",&solf,"--tmlim",&secs.to_string(),"--mipgap","0"]).stdout(std::fs::File::create(format!("{}/logs/gap/glp_m{}.log",DIR,m)).unwrap()).spawn().expect("glpsol");
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


// ---------- LNS repair: destroy a random subset of blocks of a near-solution, re-solve the residual exactly (DFS with node limit) ----------
struct LnsS<'a>{ f:&'a Fam, cands:Vec<u32>, by:Vec<Vec<u32>>, usedy:Vec<bool>, cov:Vec<u16>, chosen:Vec<u32>, nodes:u64, limit:u64 }
impl<'a> LnsS<'a>{
    fn rec(&mut self,unc:&mut Vec<u16>)->bool{
        self.nodes+=1; if self.nodes>self.limit {return false;}
        // most constrained uncovered low
        let mut best=usize::MAX; let mut bc=usize::MAX;
        for &l in unc.iter() { if self.cov[l as usize]>0 {continue;} let mut c=0usize; for &b in &self.by[l as usize] { if self.f.y(b as usize).iter().all(|&y|!self.usedy[y as usize]) { c+=1; if c>=bc {break;} } } if c<bc { bc=c; best=l as usize; if c==0 {return false;} } }
        if best==usize::MAX {return true;}
        let opts:Vec<u32>=self.by[best].iter().cloned().filter(|&b|self.f.y(b as usize).iter().all(|&y|!self.usedy[y as usize])).collect();
        for b in opts { let bu=b as usize; for &y in self.f.y(bu) { self.usedy[y as usize]=true; } for &l in self.f.l(bu) { self.cov[l as usize]+=1; } self.chosen.push(b);
            if self.rec(unc) {return true;}
            self.chosen.pop(); for &y in self.f.y(bu) { self.usedy[y as usize]=false; } for &l in self.f.l(bu) { self.cov[l as usize]-=1; } if self.nodes>self.limit {return false;} }
        false } }
fn lns_repair(f:&Fam,snap:&[usize],lows:&[u32],rng:&mut Rn,rounds:usize,limit:u64)->Option<Vec<usize>>{
    if snap.is_empty() {return None;}
    for _ in 0..rounds {
        // targeted destruction: for 1..3 random uncovered lows pick a random block covering it and destroy its Y-blockers; then a few extra random blocks
        let mut cov0=vec![0u16;f.n]; let mut owner=vec![usize::MAX;f.n]; for (i,&b) in snap.iter().enumerate() { for &l in f.l(b) { cov0[l as usize]+=1; } for &y in f.y(b) { owner[y as usize]=i; } }
        let unc0:Vec<u32>=lows.iter().cloned().filter(|&l|cov0[l as usize]==0).collect();
        let mut destroyed:std::collections::HashSet<usize>=std::collections::HashSet::new(); let nt=1+rng.below(3);
        if !unc0.is_empty() { for _ in 0..nt { let u=unc0[rng.below(unc0.len())]; let cs=&f.by_low[u as usize]; if cs.is_empty() {continue;}
            let mut bestc=cs[rng.below(cs.len())] as usize; let mut bb=usize::MAX; for _ in 0..6 { let c=cs[rng.below(cs.len())] as usize; let mut set=std::collections::HashSet::new(); for &y in f.y(c) { if owner[y as usize]!=usize::MAX { set.insert(owner[y as usize]); } } if set.len()<bb { bb=set.len(); bestc=c; } }
            for &y in f.y(bestc) { if owner[y as usize]!=usize::MAX { destroyed.insert(owner[y as usize]); } } } }
        let extra=rng.below(5); for _ in 0..extra { destroyed.insert(rng.below(snap.len())); }
        if destroyed.is_empty() { destroyed.insert(rng.below(snap.len())); }
        let d=destroyed.len();
        let mut usedy=vec![false;f.n]; let mut cov=vec![0u16;f.n]; let mut keep=vec![];
        for (i,&b) in snap.iter().enumerate() { if destroyed.contains(&i) {continue;} keep.push(b); for &y in f.y(b) { usedy[y as usize]=true; } for &l in f.l(b) { cov[l as usize]+=1; } }
        let unc:Vec<u16>=lows.iter().filter(|&&l|cov[l as usize]==0).map(|&l|l as u16).collect();
        let mut by=vec![vec![];f.n]; let mut cands=vec![];
        for b in 0..f.nb { if f.y(b).iter().all(|&y|!usedy[y as usize]) && f.l(b).iter().any(|&l|cov[l as usize]==0) { cands.push(b as u32); for &l in f.l(b) { if cov[l as usize]==0 { by[l as usize].push(b as u32); } } } }
        let mut st=LnsS{f,cands,by,usedy,cov,chosen:vec![],nodes:0,limit}; let _=&st.cands; let mut u=unc;
        let nu=u.len(); let nc=st.cands.len();
        if st.rec(&mut u) { let mut sol=keep; sol.extend(st.chosen.iter().map(|&b|b as usize)); return Some(sol); }
        if std::env::var("GAP_LNSDBG").is_ok() { println!("lns round: destroyed {} unc {} cands {} nodes {}",d,nu,nc,st.nodes); } }
    None }
fn ls_run<const W:usize>(m:u32,f:&Fam,v:&[(Mk<W>,Mk<W>)],lows:&[u32],secs:f64,seed0:u64)->Option<(Vec<usize>,u64,u64)>{
    // restart schedule per thread: trial k runs min(20*2^(k/3), 300) s with a fresh seed; first success stops all threads
    let par=Par{noise:0,k:0,t0:2,tr:6,hiw:false,pf:0}; let t0=Instant::now(); let stop=AtomicBool::new(false); let result:Mutex<Option<(Vec<usize>,u64,u64)>>=Mutex::new(None); let _=v;
    let totsteps=AtomicU64::new(0);
    std::thread::scope(|sc|{ for th in 0..nth() as u64 { let (stop,result,totsteps)=(&stop,&result,&totsteps); sc.spawn(move||{
        let mut trial=0u64; let mut tl=Instant::now();
        while !stop.load(Ordering::Relaxed) && t0.elapsed().as_secs_f64()<secs {
            let seed=seed0*1_000_000+th*10_000+trial; let lim=(20.0*2f64.powi((trial/3) as i32)).min(std::env::var("GAP_TRIALMAX").ok().and_then(|x|x.parse().ok()).unwrap_or(300.0)); trial+=1; let ts=Instant::now(); let mut s=LS::new(f,lows,seed,par); let mut best=s.unc.len(); let mut last=0u64; let mut snap:Vec<usize>=vec![]; let mut snapunc=usize::MAX; let mut lastlns=0u64;
            loop { if stop.load(Ordering::Relaxed) {break;}
                if s.do_step() { let sol:Vec<usize>=(0..f.nb).filter(|&b|s.insol[b]).collect(); *result.lock().unwrap()=Some((sol,seed,s.step)); stop.store(true,Ordering::SeqCst); break; }
                if s.unc.len()<best { best=s.unc.len(); }
                if s.unc.len()<snapunc && s.unc.len()<=6 { snapunc=s.unc.len(); snap=(0..f.nb).filter(|&b|s.insol[b]).collect(); }
                if s.unc.len()<=2 && s.step>=lastlns+2000 && std::env::var("GAP_LNSLIVE").is_ok() { lastlns=s.step; let cur:Vec<usize>=(0..f.nb).filter(|&b|s.insol[b]).collect(); let mut rg=Rn(seed.wrapping_mul(0xA24BAED4963EE407).wrapping_add(s.step)|1);
                    if let Some(sol)=lns_repair(f,&cur,lows,&mut rg,20,30000) { *result.lock().unwrap()=Some((sol,seed,s.step)); stop.store(true,Ordering::SeqCst); println!("LNS(live) repair succeeded with {} uncovered (seed {} step {})",s.unc.len(),seed,s.step); break; } }
                if s.step&0xFF==0 { if ts.elapsed().as_secs_f64()>lim || t0.elapsed().as_secs_f64()>secs {break;}
                    if th==0 && tl.elapsed().as_secs()>=30 { let r=(s.step-last) as f64/tl.elapsed().as_secs_f64(); last=s.step; tl=Instant::now();
                        println!("ls m={} thread0 trial {} (limit {:.0}s) steps {} rate {:.0}/s uncovered {} best {} elapsed {:.0}s/{:.0}s (stochastic, no ETA) rss {:.2}GB",m,trial-1,lim,s.step,r,s.unc.len(),best,t0.elapsed().as_secs_f64(),secs,rss()); } } }
            if !stop.load(Ordering::Relaxed) && !snap.is_empty() && std::env::var("GAP_LNS").is_ok() { let mut rg=Rn(seed.wrapping_mul(0xD1B54A32D192ED03)|1); let rounds:usize=std::env::var("GAP_LNS").ok().and_then(|x|x.parse().ok()).unwrap_or(200);
                if let Some(sol)=lns_repair(f,&snap,lows,&mut rg,rounds,30000) { *result.lock().unwrap()=Some((sol,seed,s.step)); stop.store(true,Ordering::SeqCst); println!("LNS repair succeeded from snapshot with {} uncovered (seed {})",snapunc,seed); } }
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
    let nst:usize=std::env::var("GAP_STAGES").ok().and_then(|x|x.parse().ok()).unwrap_or(4);
    for (si,&(mp,ng)) in [(0i32,99u32),(-1,3),(-1,99),(-99,99)].iter().enumerate().take(nst) {
        MINP.store(mp,Ordering::Relaxed); NEGT.store(ng,Ordering::Relaxed); wait_load(); let tf=Instant::now();
        let (blocks,info)=family::<W>(&ctx,&pr,tmax,true,true); let t_fam=tf.elapsed().as_secs_f64(); tot_fam+=t_fam; let rfam=rss();
        let (f,v)=make_fam(&blocks,&low,ctx.n as usize); drop(blocks); last=(info.full,f.nb,mp as u32);
        println!("m={} stage minprofit {}: kept blocks (pre-reduction) {} irreducible {} (usable {}) nodes {} enumeration wall {:.0}s (cumulative {:.0}s) peakRSS {:.2}GB",m,mp,info.full,info.irr,f.nb,info.nodes,t_fam,info.secs,rfam);
        let lim=secs*(si as f64+1.0).min(3.0); let tl0=Instant::now(); let res=ls_run::<W>(m,&f,&v,&lows,lim,seed0); let mut t_ls=tl0.elapsed().as_secs_f64();
        let mut found:Option<(Vec<usize>,String)>=None; let mut satst=String::from("-");
        if let Some((sol,seed,steps))=res { found=Some((sol,format!("LS seed {} steps {}",seed,steps))); }
        else if std::env::var("GAP_NOSAT").is_ok() { }
        else { let ts=Instant::now(); let (st,sol)=sat_try(m,&f,&lows,2.0*secs,mp); t_ls+=ts.elapsed().as_secs_f64(); satst=st; if let Some(sol)=sol { found=Some((sol,"kissat".to_string())); } }
        tot_ls+=t_ls; stagelog.push(format!("p>={}{}:{}blk,fam{:.0}s,ls+sat{:.0}s,sat={}",mp,if ng<99 {format!(",negT<={}",ng)} else {String::new()},f.nb,t_fam,t_ls,satst));
        if let Some((sol,how))=found {
            match finish_cert::<W>(m,&ctx,&v,&free,&low,&sol) {
                Ok(msg)=>{ status="OK".to_string(); chk=format!("{} (minprofit {}, {}, blocks {})",msg,mp,how,sol.len()); for &(x,y) in [(0i32,99u32),(-1,3),(-1,99),(-99,99)].iter() { let sf=format!("{}{}",if x==-99 {String::new()} else {format!("_p{}",x)},if y==99 {String::new()} else {format!("_n{}",y)}); let _=std::fs::remove_file(format!("{}/logs/gap/fam_m{}_t{}{}.done",DIR,m,tmax,sf)); } break; }
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
    let (blocks,_)=family::<W>(&ctx,&pr,std::env::var("GAP_TMAX").ok().and_then(|x|x.parse().ok()).unwrap_or(4),true,true); let (f,_v)=make_fam(&blocks,&low,ctx.n as usize); let t0=Instant::now(); let seedc=AtomicU64::new(1000); let res:Mutex<Vec<(u64,f64,bool,usize)>>=Mutex::new(vec![]);
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
    let out=format!("{}/logs/gap/sat_m{}.cnf",DIR,m); let (nv,nc)=write_cnf(&f,&lows,&out);
    println!("cnf m={} vars {} clauses {} blocks {} written {}",m,nv,nc,f.nb,out); }
// SAT stage: kissat (binary) on the exact-cover CNF of the current family; returns status string and chosen block indices. UNSAT is a statement about THIS family only.
fn sat_try(m:u32,f:&Fam,lows:&[u32],secs:f64,mp:i32)->(String,Option<Vec<usize>>){
    let cnf=format!("{}/logs/gap/sat_m{}_p{}.cnf",DIR,m,mp); let outf=format!("{}/logs/gap/sat_m{}_p{}.out",DIR,m,mp); let (nv,nc)=write_cnf(f,lows,&cnf);
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
fn lowcov<const W:usize>(m:u32,tm:u32){ let ed=edges_ev::<W>(m); let ctx=Ctx::<W>::new(m,ed.es.clone()); let pr=build_priv(&ctx); let low=ctx.low.andn(&pr.free);
    let (blocks,_)=family::<W>(&ctx,&pr,tm,true,true); let mut cnt:std::collections::BTreeMap<u32,[u32;4]>=Default::default(); for l in low.bits() { cnt.insert(l,[0;4]); }
    for (t,l) in &blocks { let p=l.and(&low).cnt() as i32-t.cnt() as i32; let k=if p>=1 {0} else if p==0 {1} else if p==-1 {2} else {3}; for x in l.and(&low).bits() { cnt.get_mut(&x).unwrap()[k]+=1; } }
    let mut zero=vec![]; let mut zero1=vec![]; for (x,c) in &cnt { if c[0]+c[1]==0 { zero.push(x+1); } else if c[0]+c[1]<=3 { zero1.push((x+1,c[0]+c[1])); } }
    println!("LOWCOV m={} lows {} lows with no profit>=0 block: {:?} ; with 1..3: {:?}",m,cnt.len(),zero,zero1); }

// ================= GAP: balanced exact partition BAL(m,K) on W-word masks (port of src/t5 + exact-cover DFS with restarts) =================
fn hsh<const W:usize>(t:&Mk<W>,l:&Mk<W>)->u128{ let mut a:u64=0x9E3779B97F4A7C15; let mut b:u64=0xC2B2AE3D27D4EB4F;
    for i in 0..W { a=(a^t.0[i]).wrapping_mul(0x100000001B3).rotate_left(23)^(a>>7); b=(b^t.0[i].rotate_left(17)).wrapping_mul(0xFF51AFD7ED558CCD).rotate_left(29); }
    for i in 0..W { a=(a^l.0[i]).wrapping_mul(0x100000001B3).rotate_left(23)^(a>>7); b=(b^l.0[i].rotate_left(31)).wrapping_mul(0xC4CEB9FE1A85EC53).rotate_left(29); }
    ((a as u128)<<64)|(b as u128) }
fn reducible_bal_h<const W:usize>(t:&Mk<W>,l:&Mk<W>,set:&HashSet<u128>)->bool{
    let tb=t.bits(); let lb=l.bits(); let k=tb.len(); if k<2 {return false;}
    for a in 1..k { for tm in 1u32..(1u32<<k)-1 { if tm.count_ones() as usize!=a || tm&1==0 {continue;}
        let mut t1=Mk::<W>::z(); let mut t2=Mk::<W>::z(); for i in 0..k { if tm>>i&1==1 { t1.set(tb[i]); } else { t2.set(tb[i]); } }
        for lm in 1u32..(1u32<<k)-1 { if lm.count_ones() as usize!=a {continue;}
            let mut l1=Mk::<W>::z(); let mut l2=Mk::<W>::z(); for i in 0..k { if lm>>i&1==1 { l1.set(lb[i]); } else { l2.set(lb[i]); } }
            if set.contains(&hsh(&t1,&l1)) && set.contains(&hsh(&t2,&l2)) { return true; } } } }
    false }
fn add_y_s<const W:usize>(pr:&Priv<W>,t:&Mk<W>,c:&Mk<W>,y:u32)->(Mk<W>,Mk<W>){ let mut t2=*t; t2.set(y); let mut c2=*c; for &(yp,lb) in &pr.by_y[y as usize] { if yp.sub(&t2) { c2.set(lb); } } (t2,c2) }
struct BW<'a,const W:usize>{ ctx:&'a Ctx<W>, pr:&'a Priv<W>, kmax:u32, only:u32, red:Option<&'a HashSet<u128>>, out:Vec<Vec<(Mk<W>,Mk<W>)>>, buf:Vec<Mk<W>>, nodes:u64 }
impl<'a,const W:usize> BW<'a,W>{
    fn dfs_l(&mut self,t:&Mk<W>,k:u32,cl:&[u32],from:usize,l:&Mk<W>,cnt:u32){
        if cnt==k { if let Some(rs)=self.red { if reducible_bal_h(t,l,rs) {return;} } self.out[k as usize].push((*t,*l)); return; }
        for i in from..cl.len(){ if cl.len()-i < (k-cnt) as usize {break;} let mut l2=*l; l2.set(cl[i]);
            if self.ctx.valid(&t.or(&l2),&mut self.buf) { self.dfs_l(t,k,cl,i+1,&l2,cnt+1); } } }
    fn dfs_t(&mut self,t:&Mk<W>,k:u32,last:u32,c:&Mk<W>){
        self.nodes+=1;
        if k>=1 && (self.only==0||self.only==k) && c.cnt()>=k { let cl=c.bits(); self.dfs_l(t,k,&cl,0,&Mk::z(),0); }
        if k>=self.kmax {return;}
        for y in last..self.ctx.n { if !self.ctx.high.has(y) {continue;} let (t2,c2)=add_y_s(self.pr,t,c,y); self.dfs_t(&t2,k+1,y+1,&c2); } }
}
fn bal_unit<const W:usize>(w:&mut BW<W>,ys:&[u32],u:(usize,usize)){
    let z=Mk::<W>::z(); let (t1,c1)=add_y_s(w.pr,&z,&z,ys[u.0]);
    if u.1==usize::MAX { w.dfs_t_single(&t1,&c1); } else if w.kmax>=2 { let (t2,c2)=add_y_s(w.pr,&t1,&c1,ys[u.1]); w.dfs_t(&t2,2,ys[u.1]+1,&c2); } }
impl<'a,const W:usize> BW<'a,W>{ fn dfs_t_single(&mut self,t:&Mk<W>,c:&Mk<W>){ self.nodes+=1; if (self.only==0||self.only==1) && c.cnt()>=1 { let cl=c.bits(); self.dfs_l(t,1,&cl,0,&Mk::z(),0); } } }
fn bal_pass<const W:usize>(ctx:&Ctx<W>,pr:&Priv<W>,kmax:u32,only:u32,red:Option<&HashSet<u128>>,tag:&str)->Vec<Vec<(Mk<W>,Mk<W>)>>{
    let ys:Vec<u32>=ctx.high.bits(); let us=units(ys.len()); let nu=us.len(); let next=AtomicUsize::new(0); let t0=Instant::now();
    let all:Mutex<(Vec<Vec<(Mk<W>,Mk<W>)>>,usize,u64,f64)>=Mutex::new((vec![vec![];kmax as usize+1],0,0,0.0));
    std::thread::scope(|sc|{ for _ in 0..nth() { sc.spawn(||{ let mut w=BW{ctx,pr,kmax,only,red,out:vec![vec![];kmax as usize+1],buf:vec![],nodes:0};
        loop { let i=next.fetch_add(1,Ordering::SeqCst); if i>=nu {break;} bal_unit(&mut w,&ys,us[i]);
            let mut g=all.lock().unwrap(); for k in 0..=kmax as usize { let mut v=std::mem::take(&mut w.out[k]); g.0[k].append(&mut v); } g.1+=1; g.2+=w.nodes; w.nodes=0;
            let el=t0.elapsed().as_secs_f64(); if el-g.3>=30.0 { g.3=el; let tot:usize=g.0.iter().map(|v|v.len()).sum(); let rate=g.1 as f64/el; println!("bal {} units {}/{} rate {:.1}/s eta {:.0}s blocks {} elapsed {:.0}s rss {:.2}GB",tag,g.1,nu,rate,(nu-g.1) as f64/rate.max(1e-9),tot,el,rss()); } } }); } });
    let g=all.into_inner().unwrap(); g.0 }
fn wr_bl<const W:usize>(path:&str,v:&[(Mk<W>,Mk<W>)]){ let mut b=Vec::with_capacity(v.len()*16*W); for (t,l) in v { for i in 0..W { b.extend_from_slice(&t.0[i].to_le_bytes()); } for i in 0..W { b.extend_from_slice(&l.0[i].to_le_bytes()); } } atomic_write(path,&b); }
fn rd_bl<const W:usize>(path:&str)->Option<Vec<(Mk<W>,Mk<W>)>>{ let b=std::fs::read(path).ok()?; let sz=16*W; if b.len()%sz!=0 {return None;} let mut v=Vec::with_capacity(b.len()/sz);
    for c in b.chunks(sz) { let mut t=Mk::<W>::z(); let mut l=Mk::<W>::z(); for i in 0..W { t.0[i]=u64::from_le_bytes(c[i*8..i*8+8].try_into().unwrap()); l.0[i]=u64::from_le_bytes(c[(W+i)*8..(W+i)*8+8].try_into().unwrap()); } v.push((t,l)); } Some(v) }
// builds irreducible balanced family files logs/gap/bal_m{m}_k{k}.bin (k=1..K) and raw files logs/gap/braw_m{m}_k{k}.bin (k<K), resumable per k
fn bal_family<const W:usize>(m:u32,kk:u32,ctx:&Ctx<W>,pr:&Priv<W>)->Vec<(Mk<W>,Mk<W>)>{
    let fp=|k:u32|format!("{}/logs/gap/bal_m{}_k{}.bin",DIR,m,k); let rp=|k:u32|format!("{}/logs/gap/braw_m{}_k{}.bin",DIR,m,k);
    let mut fam:Vec<(Mk<W>,Mk<W>)>=vec![]; let mut set:HashSet<u128>=HashSet::new(); let t0=Instant::now();
    // raw blocks of size < kk, all sizes in one pass (only=0), stored by size
    let have_raw=(1..kk).all(|k|std::path::Path::new(&rp(k)).exists());
    let raw:Vec<Vec<(Mk<W>,Mk<W>)>>= if have_raw { let mut r=vec![vec![]]; for k in 1..kk { r.push(rd_bl::<W>(&rp(k)).expect("raw read")); } println!("bal: raw files found"); r }
        else { let mut r=bal_pass::<W>(ctx,pr,kk-1,0,None,"raw"); for k in 1..kk as usize { r[k].sort(); wr_bl::<W>(&rp(k as u32),&r[k]); } r };
    for k in 1..kk as usize { println!("bal: k={} raw valid balanced {} t={:.0}s rss {:.2}GB",k,raw[k].len(),t0.elapsed().as_secs_f64(),rss()); }
    for k in 1..kk as usize {
        let irr:Vec<(Mk<W>,Mk<W>)>= if let Some(v)=rd_bl::<W>(&fp(k as u32)) { v } else { let v:Vec<(Mk<W>,Mk<W>)>=raw[k].iter().filter(|(t,l)|!reducible_bal_h(t,l,&set)).cloned().collect(); wr_bl::<W>(&fp(k as u32),&v); v };
        for (t,l) in &raw[k] { set.insert(hsh(t,l)); }
        println!("bal: k={} irreducible {} t={:.0}s",k,irr.len(),t0.elapsed().as_secs_f64()); fam.extend(irr); }
    drop(raw);
    let top:Vec<(Mk<W>,Mk<W>)>= if let Some(v)=rd_bl::<W>(&fp(kk)) { v } else { let mut r=bal_pass::<W>(ctx,pr,kk,kk,Some(&set),"top"); let mut v=std::mem::take(&mut r[kk as usize]); v.sort(); wr_bl::<W>(&fp(kk),&v); v };
    println!("bal: k={} irreducible {} t={:.0}s rss {:.2}GB",kk,top.len(),t0.elapsed().as_secs_f64(),rss()); fam.extend(top);
    println!("BALFAM m={} K={} irreducible total {} (1..{})",m,kk,fam.len(),kk); fam }
struct BS<'a,const W:usize>{ nodes:u64, limit:u64, t0:Instant, secs:f64, sol:Vec<usize>, aborted:bool, hard_abort:bool, lastp:Instant, target:Mk<W>, cm:&'a [Mk<W>], rng:Rn, shuffle:bool, lows_n:usize }
impl<'a,const W:usize> BS<'a,W>{
    fn rec(&mut self,cands:&[u32],covered:&Mk<W>,depth:u32)->bool{
        self.nodes+=1; let rem=self.target.andn(covered); if rem.is0() {return true;}
        if self.nodes&0x3FF==0 { let el=self.t0.elapsed().as_secs_f64(); if el>self.secs { self.hard_abort=true; self.aborted=true; return false; } if self.nodes>self.limit { self.aborted=true; return false; }
            if self.lastp.elapsed().as_secs()>=30 { self.lastp=Instant::now(); println!("dfs nodes {} elapsed {:.0}s/{:.0}s depth {} cands {} remaining items {} rss {:.2}GB",self.nodes,el,self.secs,depth,cands.len(),rem.cnt(),rss()); } }
        let mut cnt=[0u32;64*8]; for &c in cands { for b in self.cm[c as usize].and(&rem).bits() { cnt[b as usize]+=1; } }
        let mut best=0u32; let mut bc=u32::MAX; for it in rem.bits() { if cnt[it as usize]<bc { bc=cnt[it as usize]; best=it; if bc==0 {return false;} } }
        let mut opts:Vec<u32>=cands.iter().cloned().filter(|&c|self.cm[c as usize].has(best)).collect();
        if self.shuffle { for i in (1..opts.len()).rev() { let j=self.rng.below(i+1); opts.swap(i,j); } }
        for &o in &opts { let om=self.cm[o as usize]; let nc:Vec<u32>=cands.iter().cloned().filter(|&c|!self.cm[c as usize].meets(&om)).collect();
            self.sol.push(o as usize); if self.rec(&nc,&covered.or(&om),depth+1) {return true;} if self.aborted {return false;} self.sol.pop(); }
        false }
}
fn bal<const W:usize>(m:u32,kk:u32,secs:f64,seed0:u64){
    let t0=Instant::now(); let ed=edges_ev::<W>(m); let ctx=Ctx::<W>::new(m,ed.es.clone()); assert!(ctx.y_independent()); let pr=build_priv(&ctx); let free=pr.free; let low=ctx.low.andn(&free);
    println!("bal m={} q={} K={} edges {} Y {} Low' {}",m,2*m+1,kk,ed.es.len(),ctx.high.cnt(),low.cnt());
    let fam=bal_family::<W>(m,kk,&ctx,&pr); let target=low.or(&ctx.high); let cm:Vec<Mk<W>>=fam.iter().map(|(t,l)|t.or(l)).collect();
    // sanity: every item covered by some block
    let mut any=Mk::<W>::z(); for c in &cm { any=any.or(c); } if !target.sub(&any) { println!("BAL RESULT m={} K={} INFEASIBLE (some item in no block)",m,kk); return; }
    let cands:Vec<u32>=(0..fam.len() as u32).collect(); let mut limit:u64=2_000_000; let mut seed=seed0; let ts=Instant::now(); let mut run=0;
    loop { run+=1; let mut s=BS{nodes:0,limit,t0:ts,secs,sol:vec![],aborted:false,hard_abort:false,lastp:Instant::now(),target,cm:&cm,rng:Rn(seed.wrapping_mul(0x9E3779B97F4A7C15)|1),shuffle:run>1,lows_n:low.cnt() as usize}; let _=s.lows_n;
        let ok=s.rec(&cands,&Mk::z(),0); let el=ts.elapsed().as_secs_f64();
        if ok { println!("BAL RESULT m={} K={} FEASIBLE run {} nodes {} time {:.1}s",m,kk,run,s.nodes,el);
            let sol=s.sol.clone(); let v:Vec<(Mk<W>,Mk<W>)>=fam.clone();
            match finish_cert::<W>(m,&ctx,&v,&free,&low,&sol) { Ok(msg)=>println!("BAL CERT OK m={} blocks {} {}",m,sol.len(),msg), Err(e)=>println!("BAL CERT FAIL m={} {}",m,e) } return; }
        if s.hard_abort { println!("BAL RESULT m={} K={} UNDECIDED (time limit {}s) runs {} last-run nodes {} family {}",m,kk,secs,run,s.nodes,fam.len()); return; }
        if !s.aborted { println!("BAL RESULT m={} K={} INFEASIBLE within the complete irreducible balanced family (exhaustive run {}, nodes {}, {:.0}s)",m,kk,run,s.nodes,el); return; }
        println!("dfs restart {} (limit {} nodes reached) elapsed {:.0}s",run,limit,el); seed+=1; if run%3==0 { limit*=2; } }
}

// exact-cover CNF of the balanced family (every item in exactly one block), solved by kissat as a binary. UNSAT/SAT statements are about THIS family (solver verdict, no proof object checked).
fn balsat<const W:usize>(m:u32,kk:u32,secs:u64,tag:&str){
    let ed=edges_ev::<W>(m); let ctx=Ctx::<W>::new(m,ed.es.clone()); assert!(ctx.y_independent()); let pr=build_priv(&ctx); let free=pr.free; let low=ctx.low.andn(&free);
    let fam=bal_family::<W>(m,kk,&ctx,&pr); let target=low.or(&ctx.high);
    let mut cl:Vec<Vec<i64>>=vec![]; let mut nv=fam.len() as i64;
    for it in target.bits() { let v:Vec<usize>=(0..fam.len()).filter(|&i|fam[i].0.has(it)||fam[i].1.has(it)).collect(); cl.push(v.iter().map(|&i|i as i64+1).collect());
        let k=v.len(); if k<2 {continue;} let base=nv; nv+=k as i64-1;
        for i in 0..k { let x=v[i] as i64+1; if i<k-1 { cl.push(vec![-x,base+i as i64+1]); } if i>0 && i<k-1 { cl.push(vec![-(base+i as i64),base+i as i64+1]); } if i>0 { cl.push(vec![-x,-(base+i as i64)]); } } }
    let cnf=format!("{}/logs/gap/balsat_m{}_k{}{}.cnf",DIR,m,kk,tag); let outf=format!("{}/logs/gap/balsat_m{}_k{}{}.out",DIR,m,kk,tag);
    { use std::io::Write; let mut w=std::io::BufWriter::new(std::fs::File::create(&cnf).unwrap()); writeln!(w,"p cnf {} {}",nv,cl.len()).unwrap(); for c in &cl { for x in c { write!(w,"{} ",x).unwrap(); } writeln!(w,"0").unwrap(); } }
    println!("balsat m={} K={} family {} vars {} clauses {} kissat --time={}",m,kk,fam.len(),nv,cl.len(),secs);
    let mut ch=std::process::Command::new("nice").args(["-n","10","kissat",&format!("--time={}",secs),&cnf]).stdout(std::fs::File::create(&outf).unwrap()).spawn().expect("kissat");
    let pid=ch.id(); loop { match ch.try_wait().unwrap() { Some(_)=>break, None=>{ std::thread::sleep(std::time::Duration::from_secs(5));
        let o=std::process::Command::new("ps").args(["-o","rss=","-p",&pid.to_string()]).output().unwrap(); let kb:f64=String::from_utf8_lossy(&o.stdout).trim().parse().unwrap_or(0.0);
        if kb/1e6>3.5 { println!("kissat RSS {:.2} GB too large, killing",kb/1e6); let _=ch.kill(); } } } }
    let txt=std::fs::read_to_string(&outf).unwrap_or_default(); let st=txt.lines().find(|l|l.starts_with("s ")).unwrap_or("s NONE").to_string();
    if st.contains("UNSATISFIABLE") { println!("BALSAT RESULT m={} K={} UNSATISFIABLE (kissat verdict, family of {} irreducible balanced blocks; no proof object checked)",m,kk,fam.len()); }
    else if st.contains("SATISFIABLE") { let mut chosen=vec![]; for l in txt.lines() { if l.starts_with("v ") { for t in l[2..].split_whitespace() { let x:i64=t.parse().unwrap(); if x>0 && (x as usize)<=fam.len() { chosen.push(x as usize-1); } } } }
        let mut uy=Mk::<W>::z(); let mut ul=Mk::<W>::z(); for &b in &chosen { assert!(!uy.meets(&fam[b].0) && !ul.meets(&fam[b].1),"overlap"); uy=uy.or(&fam[b].0); ul=ul.or(&fam[b].1); } assert!(uy==ctx.high && ul==low,"not exact partition");
        println!("BALSAT RESULT m={} K={} SATISFIABLE blocks {}",m,kk,chosen.len());
        match finish_cert::<W>(m,&ctx,&fam,&free,&low,&chosen) { Ok(msg)=>println!("BAL CERT OK m={} blocks {} {}",m,chosen.len(),msg), Err(e)=>println!("BAL CERT FAIL m={} {}",m,e) } }
    else { println!("BALSAT RESULT m={} K={} UNKNOWN ({}) after {}s",m,kk,st,secs); }
}

fn main_old(){
    let a:Vec<String>=std::env::args().collect(); watchdog(RSSCAP); if let Some(x)=std::env::var("G1_MINPROFIT").ok().and_then(|x|x.parse::<i32>().ok()) { MINP.store(x,Ordering::Relaxed); } if let Some(x)=std::env::var("G1_NEGT").ok().and_then(|x|x.parse::<u32>().ok()) { NEGT.store(x,Ordering::Relaxed); }
    match a[1].as_str(){
        "edgetest"=>{ let m:u32=a[2].parse().unwrap(); disp!(m,edgetest,m) }
        "fam"=>{ let m:u32=a[2].parse().unwrap(); let tmax:u32=a.get(3).map(|s|s.parse().unwrap()).unwrap_or(4); disp!(m,famtest,m,tmax) }
        "lsbench"=>{ let m:u32=a[2].parse().unwrap(); let par=Par{noise:a[5].parse().unwrap(),k:a[6].parse().unwrap(),t0:a[7].parse().unwrap(),tr:a[8].parse().unwrap(),hiw:a.get(9).map(|x|x=="1").unwrap_or(false),pf:a.get(10).map(|x|x.parse().unwrap()).unwrap_or(0)}; disp!(m,lsbench,m,a[3].parse().unwrap(),a[4].parse().unwrap(),par) }
        "brute"=>{ let m:u32=a[2].parse().unwrap(); disp!(m,brute,m) }
        "lowcov"=>{ let m:u32=a[2].parse().unwrap(); disp!(m,lowcov,m,a.get(3).map(|s|s.parse().unwrap()).unwrap_or(4)) }
        "cnf"=>{ let m:u32=a[2].parse().unwrap(); disp!(m,cnf,m,4,0) }
        "satmodel"=>{ let m:u32=a[2].parse().unwrap(); disp!(m,satmodel,m,4,&a[3]) }
        "glp"=>{ let m:u32=a[2].parse().unwrap(); disp!(m,glp,m,a[3].parse().unwrap(),a.get(4).map(|s|s.parse().unwrap()).unwrap_or(4)) }
        "bal"=>{ let m:u32=a[2].parse().unwrap(); disp!(m,bal,m,a[3].parse().unwrap(),a[4].parse().unwrap(),a.get(5).map(|x|x.parse().unwrap()).unwrap_or(1)) }
        "balsat"=>{ let m:u32=a[2].parse().unwrap(); disp!(m,balsat,m,a[3].parse().unwrap(),a[4].parse().unwrap(),"") }
        "check"=>{ let m:u32=a[2].parse().unwrap(); let r:Result<String,String>=disp!(m,check_file,m,&a[3]); match r { Ok(s)=>println!("{}",s), Err(e)=>{ println!("CHECK FAILED: {}",e); std::process::exit(1);} } }
        "run"=>{ let lo:u32=a[2].parse().unwrap(); let hi:u32=a[3].parse().unwrap(); let secs:f64=a[4].parse().unwrap(); let seed0:u64=a.get(5).map(|s|s.parse().unwrap()).unwrap_or(1); let tmax:u32=a.get(6).map(|s|s.parse().unwrap()).unwrap_or(4);
            let resf=format!("{}/logs/gap/results.tsv",DIR); let list:Vec<u32>=(lo..=hi).filter(|&m|!is_prime(2*m as u64+1)).collect(); println!("driver: {} composite 2m+1 for m in {}..={}",list.len(),lo,hi); let tstart=Instant::now(); let mut done=0;
            for &m in &list { let solf=format!("{}/certs/m{}.g1.sol",DIR,m);
                if std::path::Path::new(&solf).exists() { println!("m={} already has certs/m{}.g1.sol, skipping (verified earlier in a results row)",m,m); done+=1; continue; }
                if std::env::var("G1_SKIP_UNDEC").is_ok() { let prev=std::fs::read_to_string(&resf).unwrap_or_default(); let hit=prev.lines().any(|l|{ let c:Vec<&str>=l.split('\t').collect(); c.len()>13 && c[0]==m.to_string() && c[11]=="UNDECIDED" && c[9].parse::<f64>().map(|x|x>=secs-1.0).unwrap_or(false) });
                    if hit { println!("m={} already UNDECIDED at >= {}s, skipped (G1_SKIP_UNDEC)",m,secs); done+=1; continue; } }
                let line=disp!(m,run_m,m,secs,seed0,tmax); use std::io::Write; let mut fh=std::fs::OpenOptions::new().create(true).append(true).open(&resf).unwrap(); writeln!(fh,"{}",line).unwrap(); done+=1;
                let el=tstart.elapsed().as_secs_f64(); println!("DRIVER done {}/{} m-values, elapsed {:.0}s, eta (rough) {:.0}s",done,list.len(),el,el/done as f64*(list.len()-done) as f64); } }
        _=>eprintln!("unknown command")
    }
}

// =====================================================================================================================
// M94 DRIVE (2026-10-03): bounded multi-phase search for a cover-capacity certificate at one m (written for m = 94, W = 3).
//   m94 drive            phases 1..4 as in the task; resumable (logs/m94/drive_state.txt, logs/m94/pool.bin); stops at the first certificate
//   m94 selftest         DFS/finish check on m = 64 (|T|<=4 family), output under logs/m94 only
// Load rule: a monitor thread reads the 1-minute load every 10 s; at >= 12 all workers sleep (PAUSE) until it falls below 12.
// =====================================================================================================================
type MK=Mk<3>;
fn splitmix(x:u64)->u64{ let mut z=x.wrapping_add(0x9E3779B97F4A7C15); z=(z^(z>>30)).wrapping_mul(0xBF58476D1CE4E5B9); z=(z^(z>>27)).wrapping_mul(0x94D049BB133111EB); z^(z>>31) }
static PAUSE:AtomicBool=AtomicBool::new(false);
static PAUSED:AtomicU64=AtomicU64::new(0);
static MON:AtomicBool=AtomicBool::new(false);
static STARTEP:AtomicU64=AtomicU64::new(0);
const WALL:f64=10800.0;
fn now_ep()->u64{ std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs() }
fn wall_left()->f64{ WALL-(now_ep()-STARTEP.load(Ordering::Relaxed)) as f64 }
fn start_monitor(){ if MON.swap(true,Ordering::SeqCst){return;} std::thread::spawn(||{ let mut was=false; loop{ let l=load1(); let p=l>=12.0;
    if p!=was { println!("LOAD {:.2}: {}",l,if p {"PAUSE (workers sleep)"} else {"RESUME"}); was=p; } PAUSE.store(p,Ordering::Relaxed);
    std::thread::sleep(std::time::Duration::from_secs(10)); if p { PAUSED.fetch_add(10,Ordering::Relaxed); } } }); }
fn pause_point(){ while PAUSE.load(Ordering::Relaxed) { std::thread::sleep(std::time::Duration::from_secs(2)); } }
#[derive(Clone,Copy)] struct Clock{ t0:Instant, p0:u64 }
impl Clock{ fn new()->Self{ Clock{t0:Instant::now(),p0:PAUSED.load(Ordering::Relaxed)} } fn act(&self)->f64{ self.t0.elapsed().as_secs_f64()-(PAUSED.load(Ordering::Relaxed)-self.p0) as f64 } }
fn lg(msg:&str){ println!("{}",msg); }

struct Env{ m:u32, ctx:Ctx<3>, free:MK, low:MK, lows:Vec<u32>, lowmask:u128, v:Vec<(MK,MK)>, f:Fam, f4:Fam, map4:Vec<u32>, ytot:u32, eyl:Vec<(MK,MK)> }
fn setup(m:u32,big:u32)->Env{
    MINP.store(0,Ordering::Relaxed); NEGT.store(99,Ordering::Relaxed);
    let ed=edges_ev::<3>(m); let ctx=Ctx::<3>::new(m,ed.es.clone()); assert!(ctx.y_independent());
    let pr=build_priv(&ctx); let free=pr.free; let low=ctx.low.andn(&free); let lows=low.bits();
    let (mut all,_)=family::<3>(&ctx,&pr,4,true,true);
    if big>4 { let (b5,_)=family::<3>(&ctx,&pr,big,true,true); all.extend(b5); }
    let (f,v)=make_fam(&all,&low,ctx.n as usize); drop(all);
    let b4:Vec<(MK,MK)>=v.iter().filter(|(t,_)|t.cnt()<=4).cloned().collect();
    let (f4,v4)=make_fam(&b4,&low,ctx.n as usize);
    let idx:HashMap<(MK,MK),u32>=v.iter().enumerate().map(|(i,b)|(*b,i as u32)).collect();
    let map4:Vec<u32>=v4.iter().map(|b|idx[b]).collect();
    let mut lowmask=0u128; for &x in &lows { lowmask|=1u128<<x; }
    let eyl:Vec<(MK,MK)>=ctx.es.iter().map(|e|(e.and(&ctx.high),e.and(&ctx.low))).collect();
    let ytot=ctx.high.cnt();
    println!("setup m={} edges {} family(p>=0, |T|<={}) {} blocks, |T|<=4 sub-family {} blocks, lows {} (free {}), Y {}",m,ctx.es.len(),big,f.nb,f4.nb,lows.len(),free.cnt(),ytot);
    Env{m,ctx,free,low,lows,lowmask,v,f,f4,map4,ytot,eyl} }
#[derive(Clone)] struct RB{ t:MK, l:MK, y:u128, lm:u128, ny:u8, nl:u8 }
fn mk_rb(m:u32,t:&MK,l:&MK)->RB{ let mut y=0u128; for b in t.bits(){ y|=1u128<<(b-(m+1)); } let mut lm=0u128; for b in l.bits(){ lm|=1u128<<b; } RB{t:*t,l:*l,y,lm,ny:t.cnt() as u8,nl:l.cnt() as u8} }
fn sort_rb(v:&mut Vec<RB>){ v.sort_by(|a,b|(std::cmp::Reverse(a.nl),a.ny,a.t,a.l).cmp(&(std::cmp::Reverse(b.nl),b.ny,b.t,b.l))); }

// ---------- final certificate ----------
fn finish_to(env:&Env,blocks:&[(MK,MK)],out:&str)->Result<String,String>{
    let mut parts:Vec<(MK,u32)>=vec![]; let mut usedy=MK::z(); let mut cov=MK::z();
    for (t,l) in blocks { if usedy.meets(t) {return Err("T overlap".into());} usedy=usedy.or(t); cov=cov.or(l); parts.push((t.or(l),t.cnt())); }
    if !env.low.sub(&cov) {return Err("lows not covered".into());}
    if !env.free.is0() { parts.push((env.free,0)); }
    let mut left:Vec<u32>=env.ctx.high.andn(&usedy).bits(); while !left.is_empty(){ let k=left.len().min(8); let mut c=MK::z(); for _ in 0..k { c.set(left.pop().unwrap()); } parts.push((c,c.cnt())); }
    write_sol(out,&parts);
    match check_file::<3>(env.m,out) { Ok(msg)=>Ok(msg), Err(e)=>{ let _=std::fs::remove_file(out); Err(e) } } }
fn cert_path(m:u32)->String{ format!("{}/certs/m{}.g1.sol",DIR,m) }
fn declare_success(env:&Env,blocks:&[(MK,MK)],how:&str)->bool{
    let out=cert_path(env.m); match finish_to(env,blocks,&out) { Ok(msg)=>{ println!("SUCCESS m={} via {}: {} -> {}",env.m,how,msg,out); true }, Err(e)=>{ println!("FINISH FAILED ({}): {}",how,e); false } } }

// ---------- pool of near-solutions (indices into env.v) ----------
struct Pool{ states:Vec<(u8,Vec<u32>)>, seen:HashSet<u64>, seedctr:u64, n3:usize, nle2:usize, ufreq:Vec<u32>, famhash:u64, nb:u64, p1secs:f64 }
const CAP3:usize=12000; const CAPLE2:usize=8000;
fn zob(idx:&[u32])->u64{ idx.iter().fold(0u64,|a,&b|a^splitmix(b as u64)) }
fn pool_new(env:&Env)->Pool{ Pool{states:vec![],seen:HashSet::new(),seedctr:0,n3:0,nle2:0,ufreq:vec![0;192],famhash:famhash(env),nb:env.v.len() as u64,p1secs:0.0} }
fn famhash(env:&Env)->u64{ let mut h=0u64; for (t,l) in &env.v { h=splitmix(h^t.0[0]^splitmix(t.0[1]^splitmix(t.0[2]^splitmix(l.0[0]^splitmix(l.0[1])^l.0[2])))); } h }
fn pool_path()->String{ format!("{}/logs/m94/pool.bin",DIR) }
fn pool_save(p:&Pool){ let mut b:Vec<u8>=vec![]; for x in [0x4D39345F504F4F4Cu64,p.famhash,p.nb,p.states.len() as u64,p.seedctr,p.p1secs.to_bits()] { b.extend_from_slice(&x.to_le_bytes()); }
    for &u in &p.ufreq { b.extend_from_slice(&u.to_le_bytes()); }
    for (u,idx) in &p.states { b.push(*u); b.extend_from_slice(&(idx.len() as u16).to_le_bytes()); for &i in idx { b.extend_from_slice(&i.to_le_bytes()); } }
    atomic_write(&pool_path(),&b); }
fn pool_load(env:&Env)->Pool{ let mut p=pool_new(env); let b=match std::fs::read(pool_path()){ Ok(b)=>b, Err(_)=>return p }; if b.len()<48+192*4 {return p;}
    let r=|i:usize|u64::from_le_bytes(b[i*8..i*8+8].try_into().unwrap()); if r(0)!=0x4D39345F504F4F4C || r(1)!=p.famhash || r(2)!=p.nb { println!("pool.bin does not match this family, ignored"); return p; }
    let ns=r(3) as usize; p.seedctr=r(4); p.p1secs=f64::from_bits(r(5)); let mut pos=48; for i in 0..192 { p.ufreq[i]=u32::from_le_bytes(b[pos..pos+4].try_into().unwrap()); pos+=4; }
    for _ in 0..ns { let u=b[pos]; let n=u16::from_le_bytes([b[pos+1],b[pos+2]]) as usize; pos+=3; let mut idx=Vec::with_capacity(n); for _ in 0..n { idx.push(u32::from_le_bytes(b[pos..pos+4].try_into().unwrap())); pos+=4; }
        p.seen.insert(zob(&idx)); if u==3 {p.n3+=1;} else {p.nle2+=1;} p.states.push((u,idx)); }
    println!("pool loaded: {} states ({} with 3 uncovered, {} with <=2), seed counter {}, p1 seconds so far {:.0}",p.states.len(),p.n3,p.nle2,p.seedctr,p.p1secs); p }
fn pool_add(p:&mut Pool,unc:u8,idx:Vec<u32>,uncl:&[u16])->bool{ let h=zob(&idx); if p.seen.contains(&h) {return false;}
    if unc==3 { if p.n3>=CAP3 {return false;} p.n3+=1; } else { if p.nle2>=CAPLE2 {return false;} p.nle2+=1; }
    p.seen.insert(h); for &l in uncl { p.ufreq[l as usize]+=1; } p.states.push((unc,idx)); true }
fn pool_stats(p:&Pool,env:&Env)->String{ let mut c=[0usize;4]; let mut bl:HashSet<u32>=HashSet::new(); for (u,idx) in &p.states { c[*u as usize]+=1; for &b in idx { bl.insert(b); } }
    let mut uf:Vec<(u32,usize)>=(0..192).filter(|&i|p.ufreq[i]>0).map(|i|(p.ufreq[i],i+1)).collect(); uf.sort(); uf.reverse(); let top:Vec<String>=uf.iter().take(12).map(|(c,v)|format!("{}:{}",v,c)).collect();
    format!("pool: {} distinct near-solutions (3 unc: {}, 2 unc: {}, 1 unc: {}), {} distinct blocks of {}, uncovered-low frequencies (velocity:count, top 12) {}, distinct lows ever uncovered {}",p.states.len(),c[3],c[2],c[1],bl.len(),env.v.len(),top.join(" "),uf.len()) }

// ---------- phase 1 / growth: LS harvest ----------
fn harvest(env:&Env,pool:&Mutex<Pool>,budget:f64,mode:u8,tag:&str)->Option<Vec<usize>>{
    let par=Par{noise:0,k:0,t0:2,tr:6,hiw:false,pf:0}; let clk=Clock::new(); let stop=AtomicBool::new(false); let found:Mutex<Option<Vec<usize>>>=Mutex::new(None);
    let ntr=AtomicU64::new(0); let globest=AtomicU32::new(99); let trial_lim:f64=if mode==0 {60.0} else {30.0};
    let seeds:Vec<Vec<u32>>=if mode==1 { let p=pool.lock().unwrap(); let mn=p.states.iter().map(|s|s.0).min().unwrap_or(3); let lim=mn.max(2); let mut v:Vec<Vec<u32>>=p.states.iter().filter(|s|s.0<=lim).map(|s|s.1.clone()).collect(); let n=v.len(); if n>3000 { v=v.split_off(n-3000); } v } else { vec![] };
    if mode==1 { println!("{}: growth, {} seed states for kicks",tag,seeds.len()); }
    let lastsave=Mutex::new(Instant::now());
    std::thread::scope(|sc|{ for th in 0..nth() as u64 { let (stop,found,ntr,globest,seeds,lastsave)=(&stop,&found,&ntr,&globest,&seeds,&lastsave); let clk=clk; sc.spawn(move||{
        let mut tl=Instant::now();
        while !stop.load(Ordering::Relaxed) && clk.act()<budget && wall_left()>0.0 {
            pause_point();
            let ctr={ let mut p=pool.lock().unwrap(); p.seedctr+=1; p.seedctr }; let seed=900_000+ctr*7+th;
            let use4=mode==0 && ctr%2==1; let fam=if use4 {&env.f4} else {&env.f};
            let mut s=LS::new(fam,&env.lows,seed,par); let mut rg=Rn(seed.wrapping_mul(0x9E3779B97F4A7C15)|1);
            if mode==1 && !seeds.is_empty() { let st=&seeds[rg.below(seeds.len())]; let k=5+rg.below(11); let mut keep:Vec<u32>=st.clone(); for _ in 0..k { if keep.is_empty() {break;} let i=rg.below(keep.len()); keep.swap_remove(i); } for &b in &keep { s.add(b as usize); } }
            let ts=Instant::now(); let mut lastrec=0u64; let mut nrec=0usize; let mut best=99usize;
            loop {
                if stop.load(Ordering::Relaxed) {break;}
                if s.do_step() { let sol:Vec<usize>=(0..fam.nb).filter(|&b|s.insol[b]).map(|b|if use4 {env.map4[b] as usize} else {b}).collect(); *found.lock().unwrap()=Some(sol); stop.store(true,Ordering::SeqCst); break; }
                let u=s.unc.len(); if u<best {best=u;} 
                if u<=3 && s.step>=lastrec+50 && nrec<400 { lastrec=s.step; let idx:Vec<u32>={ let mut v:Vec<u32>=(0..fam.nb).filter(|&b|s.insol[b]).map(|b|if use4 {env.map4[b]} else {b as u32}).collect(); v.sort(); v };
                    let h=zob(&idx); let skip={ pool.lock().unwrap().seen.contains(&h) }; if !skip { let mut p=pool.lock().unwrap(); if pool_add(&mut p,u as u8,idx,&s.unc.iter().map(|&x|x).collect::<Vec<u16>>()) { nrec+=1; } } }
                if s.step&0xFF==0 { pause_point(); if ts.elapsed().as_secs_f64()>trial_lim || clk.act()>budget || wall_left()<=0.0 {break;}
                    if th==0 && tl.elapsed().as_secs()>=30 { tl=Instant::now(); let (np,n3,nl2)={ let p=pool.lock().unwrap(); (p.states.len(),p.n3,p.nle2) }; let a=clk.act();
                        println!("{} ls trials {} pool {} (3unc {} le2 {}) thread0 unc {} best {} elapsed {:.0}s/{:.0}s ETA {:.0}s (budget-bound; success is stochastic) rss {:.2}GB",tag,ntr.load(Ordering::Relaxed),np,n3,nl2,s.unc.len(),globest.load(Ordering::Relaxed),a,budget,(budget-a).max(0.0),rss());
                        let mut ls=lastsave.lock().unwrap(); if ls.elapsed().as_secs()>=120 { *ls=Instant::now(); let mut p=pool.lock().unwrap(); p.p1secs+= if mode==0 {120.0} else {0.0}; pool_save(&p); } } } }
            let mut g=globest.load(Ordering::Relaxed); while (best as u32)<g { match globest.compare_exchange(g,best as u32,Ordering::SeqCst,Ordering::SeqCst){ Ok(_)=>break, Err(x)=>g=x } }
            ntr.fetch_add(1,Ordering::Relaxed); } }); } });
    { let p=pool.lock().unwrap(); pool_save(&p); }
    let r=found.lock().unwrap().clone(); r }

// ---------- neighbourhood generation ----------
fn t_minimal(env:&Env,t:&MK,l:&MK,buf:&mut Vec<MK>)->bool{ for y in t.bits(){ let mut t2=*t; t2.clr(y); if env.ctx.valid(&t2.or(l),buf) {return false;} } true }
fn max_subsets(env:&Env,t:&MK,l:&MK,minsize:usize,buf:&mut Vec<MK>)->Vec<MK>{
    let lb=l.bits(); let k=lb.len(); let mut out:Vec<MK>=vec![]; if k==0 {return out;}
    let mut masks:Vec<u32>=(1u32..(1u32<<k)).filter(|x|x.count_ones() as usize>=minsize.max(1)).collect(); masks.sort_by_key(|x|std::cmp::Reverse(x.count_ones()));
    for mk in masks { let mut sub=MK::z(); for i in 0..k { if mk>>i&1==1 { sub.set(lb[i]); } } if out.iter().any(|o|sub.sub(o)) {continue;} if env.ctx.valid(&t.or(&sub),buf) { out.push(sub); } }
    out }
fn pushb(env:&Env,t2:MK,l2:MK,minp:i32,out:&mut HashSet<(MK,MK)>,buf:&mut Vec<MK>){ if !l2.is0() && !t2.is0() && (l2.cnt() as i32-t2.cnt() as i32)>=minp && t_minimal(env,&t2,&l2,buf) { out.insert((t2,l2)); } }
// flags: 1 = drop one T element (L shrinks to maximal valid subsets), 2 = swap one T element, 4 = add one free Y element (frees) and one low
fn neigh(env:&Env,t:&MK,l:&MK,minp:i32,flags:u32,frees:&[u32],out:&mut HashSet<(MK,MK)>,buf:&mut Vec<MK>){
    let nt=t.cnt() as i32; let ybits:Vec<u32>=env.ctx.high.bits();
    if flags&1!=0 { for y in t.bits(){ let mut t2=*t; t2.clr(y); if t2.is0() {continue;} let need=((t2.cnt() as i32)+minp).max(1) as usize; for sub in max_subsets(env,&t2,l,need,buf) { pushb(env,t2,sub,minp,out,buf); } } }
    if flags&2!=0 { for y in t.bits(){ for &y2 in &ybits { if t.has(y2) {continue;} let mut t2=*t; t2.clr(y); t2.set(y2); let need=(nt+minp).max(1) as usize; for sub in max_subsets(env,&t2,l,need,buf) { pushb(env,t2,sub,minp,out,buf); } } } }
    if flags&4!=0 { for &y in frees { if t.has(y) {continue;} let mut t2=*t; t2.set(y); for &x in &env.lows { if l.has(x) {continue;} let mut l2=*l; l2.set(x); if env.ctx.valid(&t2.or(&l2),buf) { pushb(env,t2,l2,minp,out,buf); } } } } }
fn build_r(env:&Env,pool:&Pool,cap:usize,minp:i32,tlim:f64,tag:&str)->Vec<(MK,MK)>{
    let clk=Clock::new(); let mut idxs:Vec<usize>=(0..pool.states.len()).collect(); idxs.sort_by_key(|&i|(pool.states[i].0,std::cmp::Reverse(i)));
    let mut pooled:HashSet<u32>=HashSet::new(); let mut order:Vec<u32>=vec![]; let mut chosen:Vec<usize>=vec![];
    for &i in &idxs { if pooled.len()>=cap {break;} for &b in &pool.states[i].1 { if pooled.insert(b) { order.push(b); } } chosen.push(i); }
    let mut out:HashSet<(MK,MK)>=HashSet::new(); for (i,b) in env.v.iter().enumerate() { if b.0.cnt()<=4 || pooled.contains(&(i as u32)) { out.insert(*b); } }
    let base=out.len(); println!("{}: R base {} blocks ({} pooled from {} states, |T|<=4 family included)",tag,base,pooled.len(),chosen.len());
    let mut buf=vec![]; let mut done=0usize;
    for (k,&b) in order.iter().enumerate() { if clk.act()>tlim*0.6 {break;} pause_point(); let (t,l)=env.v[b as usize]; neigh(env,&t,&l,minp,3,&[],&mut out,&mut buf); done=k+1;
        if k%2000==0 { println!("{}: drop/swap neighbours {}/{} blocks, R {} ({:.0}s)",tag,k,order.len(),out.len(),clk.act()); } }
    let n1=out.len(); println!("{}: drop/swap done for {}/{} pooled blocks, R {}",tag,done,order.len(),n1);
    let ym:Vec<u32>=env.ctx.high.bits(); let mut pairs:HashSet<(u32,u32)>=HashSet::new(); let mut pl:Vec<(u32,u32)>=vec![];
    for &i in chosen.iter().take(4000) { let mut used=MK::z(); for &b in &pool.states[i].1 { used=used.or(&env.v[b as usize].0); } let fr:Vec<u32>=ym.iter().cloned().filter(|&y|!used.has(y)).collect();
        for &b in &pool.states[i].1 { for &y in &fr { if pairs.insert((b,y)) { pl.push((b,y)); } } } }
    let mut nd=0usize; for &(b,y) in &pl { if clk.act()>tlim {break;} pause_point(); let (t,l)=env.v[b as usize]; neigh(env,&t,&l,minp,4,&[y],&mut out,&mut buf); nd+=1; }
    println!("{}: add-free-Y neighbours from {}/{} (block,y) pairs, R {} (+{}), total build {:.0}s",tag,nd,pl.len(),out.len(),out.len()-n1,clk.act());
    out.into_iter().collect() }

// ---------- exact DFS packing ----------
type Lists=Vec<(u8,Vec<u32>)>;
const SC:u64=27720;
struct Dfs<'a>{ bl:&'a [RB], lowmask:u128, ytot:u32, memo:Vec<u64>, mcount:usize, mcap:usize, nodes:u64, limit:u64, clk:Clock, tlim:f64, chosen:Vec<u32>, maxneg:u32, aborted:bool, hits:u64, prunes:u64, maxdepth:usize, bestunc:u32, lastp:f64, tag:String, verbose:bool, found:Vec<u32> }
fn hkey(used:u128,cov:u128,negs:u32)->u64{ splitmix(used as u64^splitmix((used>>64) as u64^splitmix(cov as u64^splitmix((cov>>64) as u64^negs as u64))))|1 }
impl<'a> Dfs<'a>{
    fn memo_has(&self,k:u64)->bool{ let mask=self.memo.len()-1; let mut i=(k as usize)&mask; loop { let e=self.memo[i]; if e==0 {return false;} if e==k {return true;} i=(i+1)&mask; } }
    fn memo_put(&mut self,k:u64){ if self.mcount>=self.mcap {return;} let mask=self.memo.len()-1; let mut i=(k as usize)&mask; loop { let e=self.memo[i]; if e==0 { self.memo[i]=k; self.mcount+=1; return; } if e==k {return;} i=(i+1)&mask; } }
    fn root(&self,used0:u128,cov0:u128,negs0:u32)->Option<Lists>{
        let unc=self.lowmask&!cov0; let mut lists:Lists=vec![]; let mut pos=vec![usize::MAX;128]; let mut r=unc; while r!=0 { let u=r.trailing_zeros(); r&=r-1; pos[u as usize]=lists.len(); lists.push((u as u8,vec![])); }
        for (i,b) in self.bl.iter().enumerate() { if b.y&used0!=0 {continue;} if negs0>=self.maxneg && b.nl<b.ny {continue;} let mut r=b.lm&unc; while r!=0 { let u=r.trailing_zeros(); r&=r-1; lists[pos[u as usize]].1.push(i as u32); } }
        let freey=self.ytot-used0.count_ones(); let mut sum=0u64;
        for (_,l) in &lists { if l.is_empty() {return None;} let mut c=u64::MAX; for &b in l { let cb=&self.bl[b as usize]; let k=(cb.lm&unc).count_ones() as u64; let v=cb.ny as u64*SC/k; if v<c {c=v;} } sum+=c; }
        if sum>freey as u64*SC {return None;} Some(lists) }
    fn child(&self,parent:&Lists,b:u32,used:u128,cov:u128,negs:u32)->Option<Lists>{
        let bb=&self.bl[b as usize]; let unc=self.lowmask&!cov; let freey=self.ytot-used.count_ones(); let mut sum=0u64; let mut out:Lists=Vec::with_capacity(parent.len());
        for (u,lst) in parent { if (cov>>*u)&1==1 {continue;} let mut nl:Vec<u32>=Vec::with_capacity(lst.len()); let mut cmin=u64::MAX;
            for &c in lst { let cb=&self.bl[c as usize]; if cb.y&bb.y!=0 {continue;} if negs>=self.maxneg && cb.nl<cb.ny {continue;}
                let k=(cb.lm&unc).count_ones() as u64; let v=cb.ny as u64*SC/k; if v<cmin {cmin=v;} nl.push(c); }
            if nl.is_empty() {return None;} sum+=cmin; if sum>freey as u64*SC {return None;} out.push((*u,nl)); }
        Some(out) }
    fn rec(&mut self,used:u128,cov:u128,negs:u32,lists:&Lists)->u8{
        self.nodes+=1; if lists.is_empty() { self.found=self.chosen.clone(); return 1; }
        if self.nodes>self.limit { self.aborted=true; return 2; }
        if self.nodes&0x1FFF==0 { pause_point(); let a=self.clk.act(); if a>self.tlim || wall_left()<=0.0 { self.aborted=true; return 2; }
            if self.verbose && a-self.lastp>=30.0 { self.lastp=a; println!("{} dfs nodes {} rate {:.0}/s depth {} maxdepth {} fewest-uncovered-lows {} memo {} hits {} prunes {} elapsed {:.0}s/{:.0}s ETA <= {:.0}s (time cap; no completion estimate) rss {:.2}GB",self.tag,self.nodes,self.nodes as f64/a.max(1e-9),self.chosen.len(),self.maxdepth,self.bestunc,self.mcount,self.hits,self.prunes,a,self.tlim,(self.tlim-a).max(0.0),rss()); } }
        let un=lists.len() as u32; if un<self.bestunc { self.bestunc=un; } if self.chosen.len()>self.maxdepth { self.maxdepth=self.chosen.len(); }
        let key=hkey(used,cov,negs); if self.memo_has(key) { self.hits+=1; return 0; }
        let mut bi=0; let mut bl=usize::MAX; for (i,(_,l)) in lists.iter().enumerate() { if l.len()<bl { bl=l.len(); bi=i; } }
        let lst=&lists[bi].1;
        for &b in lst { let bb=&self.bl[b as usize]; let used2=used|bb.y; let cov2=cov|bb.lm; let negs2=negs+(bb.nl<bb.ny) as u32;
            match self.child(lists,b,used2,cov2,negs2) { None=>{ self.prunes+=1; }, Some(ch)=>{ self.chosen.push(b); let r=self.rec(used2,cov2,negs2,&ch); if r!=0 {return r;} self.chosen.pop(); } } }
        self.memo_put(key); 0 } }
// verdict: 0 = no packing in bl (COMPLETE search of bl), 1 = found, 2 = aborted (node/time cap)
fn dfs_solve(bl:&[RB],lowmask:u128,ytot:u32,used0:u128,cov0:u128,maxneg:u32,limit:u64,tlim:f64,mlog:u32,tag:&str,verbose:bool)->(u8,Vec<u32>,u64,u64,u32){
    let mut d=Dfs{bl,lowmask,ytot,memo:vec![0u64;1usize<<mlog],mcount:0,mcap:(1usize<<mlog)/10*7,nodes:0,limit,clk:Clock::new(),tlim,chosen:vec![],maxneg,aborted:false,hits:0,prunes:0,maxdepth:0,bestunc:999,lastp:0.0,tag:tag.to_string(),verbose,found:vec![]};
    let root=match d.root(used0,cov0,0) { None=>return (0,vec![],0,0,0), Some(r)=>r };
    let r=d.rec(used0,cov0,0,&root); let v=if r==1 {1} else if d.aborted {2} else {0};
    (v,d.found.clone(),d.nodes,d.hits,d.bestunc) }
fn to_blocks(rb:&[RB],sol:&[u32])->Vec<(MK,MK)>{ sol.iter().map(|&i|(rb[i as usize].t,rb[i as usize].l)).collect() }
fn rb_of(env:&Env,v:&[(MK,MK)])->Vec<RB>{ let mut x:Vec<RB>=v.iter().map(|(t,l)|mk_rb(env.m,t,l)).collect(); sort_rb(&mut x); x }

// ---------- phase 3: larger blocks through one uncovered low ----------
fn gen_cands(env:&Env,l:u32,maxt:u32,cap:usize,tlim:f64)->Vec<(MK,MK)>{
    let clk=Clock::new(); let mut yps:Vec<MK>=env.eyl.iter().map(|e|e.0).filter(|y|{ let c=y.cnt(); c>=1&&c<=maxt }).collect(); yps.sort(); yps.dedup();
    let mut by_y:Vec<Vec<usize>>=vec![vec![];env.ctx.n as usize]; for (i,y) in yps.iter().enumerate() { for b in y.bits() { by_y[b as usize].push(i); } }
    let mut all:HashSet<MK>=HashSet::new(); let mut frontier:Vec<MK>=vec![];
    for e in &env.eyl { if e.1.has(l) { let c=e.0.cnt(); if c>=1&&c<=maxt && all.insert(e.0) { frontier.push(e.0); } } }
    let mut buf=vec![]; let mut out:Vec<(MK,MK)>=vec![]; let mut ev=0usize; let mut stopped=false;
    let mut eval=|t:&MK,out:&mut Vec<(MK,MK)>,buf:&mut Vec<MK>|{ let mut lu=MK::z(); for e in &env.eyl { if e.0.sub(t) { lu=lu.or(&e.1); } } let lu=lu.and(&env.low); if !lu.has(l) || (lu.cnt() as usize)<(t.cnt() as usize) {return;}
        let lb=lu.bits(); let mut best=MK::z(); for ord in 0..2 { let mut cur=MK::z(); cur.set(l); if !env.ctx.valid(&t.or(&cur),buf) {return;} let it:Vec<u32>=if ord==0 {lb.clone()} else {lb.iter().rev().cloned().collect()};
            for x in it { if x==l {continue;} let mut c2=cur; c2.set(x); if env.ctx.valid(&t.or(&c2),buf) { cur=c2; } } if cur.cnt()>best.cnt() {best=cur;} }
        if best.cnt()>=t.cnt() && t_minimal(env,t,&best,buf) { out.push((*t,best)); } };
    let starts=frontier.clone(); for t in &starts { eval(t,&mut out,&mut buf); ev+=1; }
    while !frontier.is_empty() && !stopped { let mut next:Vec<MK>=vec![];
        for t in &frontier { if clk.act()>tlim || all.len()>=cap { stopped=true; break; }
            for y in t.bits() { for &i in &by_y[y as usize] { let yp=&yps[i]; if yp.sub(t) {continue;} let u=t.or(yp); if u.cnt()>maxt {continue;} if all.insert(u) { next.push(u); eval(&u,&mut out,&mut buf); ev+=1; } } } }
        frontier=next; }
    println!("gen_cands low {}: {} T-sets generated ({}), {} valid candidate blocks (|L|>=|T|, T minimal), stopped_by_cap {} ({:.0}s)",l+1,all.len(),ev,out.len(),stopped,clk.act()); out }
fn state_masks(rbs:&[RB])->(u128,u128){ let mut y=0u128; let mut c=0u128; for b in rbs { y|=b.y; c|=b.lm; } (y,c) }
fn p3(env:&Env,pool:&Pool,rb_all:&[RB],budget:f64)->Option<Vec<(MK,MK)>>{
    let clk=Clock::new(); let mut sts:Vec<(u8,usize)>=pool.states.iter().enumerate().filter(|(_,s)|s.0<=2).map(|(i,s)|(s.0,i)).collect(); sts.sort(); sts.truncate(100);
    println!("p3: {} best states (<=2 uncovered) used",sts.len()); if sts.is_empty() { return None; }
    let st_rb:Vec<Vec<RB>>=sts.iter().map(|&(_,i)|pool.states[i].1.iter().map(|&b|mk_rb(env.m,&env.v[b as usize].0,&env.v[b as usize].1)).collect()).collect();
    let mut lf:HashMap<u32,usize>=HashMap::new(); for rbs in &st_rb { let (_,c)=state_masks(rbs); let mut r=env.lowmask&!c; while r!=0 { let u=r.trailing_zeros(); r&=r-1; *lf.entry(u).or_insert(0)+=1; } }
    let mut tl:Vec<(usize,u32)>=lf.iter().map(|(&u,&c)|(c,u)).collect(); tl.sort(); tl.reverse(); println!("p3: target lows (velocity:states) {:?}",tl.iter().map(|(c,u)|(u+1,*c)).collect::<Vec<_>>());
    let ntl=tl.len(); let mut attempts=0u64; let mut subnodes=0u64; let mut rg=Rn(0xC0FFEE123456789);
    for (ti,&(_,l)) in tl.iter().enumerate() { if clk.act()>=budget || wall_left()<=0.0 {break;}
        let share=(budget-clk.act())/((ntl-ti) as f64); let cands=gen_cands(env,l,6,5_000_000,share*0.35);
        if cands.is_empty() {continue;} let crb:Vec<RB>=cands.iter().map(|(t,lk)|mk_rb(env.m,t,lk)).collect();
        // per state, candidate options with fewest blockers
        let mut opts:Vec<Vec<(u8,u32)>>=vec![]; let mut sidx:Vec<usize>=vec![];
        for (si,rbs) in st_rb.iter().enumerate() { let (_,c)=state_masks(rbs); if (c>>l)&1==1 {continue;} let mut v:Vec<(u8,u32)>=vec![];
            for (ci,cb) in crb.iter().enumerate() { let mut nb=0u8; for b in rbs { if b.y&cb.y!=0 {nb+=1;} } if nb<=5 { v.push((nb,ci as u32)); } }
            for i in (1..v.len()).rev() { let j=rg.below(i+1); v.swap(i,j); } v.sort_by_key(|x|x.0); v.truncate(20000); opts.push(v); sidx.push(si); }
        println!("p3: low {}: {} states with it uncovered, options per state {:?} (blockers<=5)",l+1,sidx.len(),opts.iter().map(|o|o.len()).take(8).collect::<Vec<_>>());
        let tend=clk.act()+share*0.65; let mut pass=0usize; let mut progress=true;
        while progress && clk.act()<tend { progress=false;
            for (k,&si) in sidx.iter().enumerate() { if clk.act()>=tend || wall_left()<=0.0 {break;} pause_point(); let o=&opts[k]; let lo=pass*200; if lo>=o.len() {continue;} progress=true; let hi=(lo+200).min(o.len());
                let rbs=&st_rb[si];
                for &(_,ci) in &o[lo..hi] { let cb=&crb[ci as usize]; attempts+=1;
                    let kept:Vec<&RB>=rbs.iter().filter(|b|b.y&cb.y==0).collect(); let mut used=cb.y; let mut cov=cb.lm; for b in &kept { used|=b.y; cov|=b.lm; }
                    let unc=env.lowmask&!cov; let freey=env.ytot-used.count_ones(); if freey>26 {continue;}
                    let sub:Vec<RB>=rb_all.iter().filter(|b|b.y&used==0 && b.lm&unc!=0).cloned().collect();
                    let (vd,sol,nd,_,_)=dfs_solve(&sub,env.lowmask,env.ytot,used,cov,0,200_000,5.0,12,"p3sub",false); subnodes+=nd;
                    if vd==1 { let mut blocks:Vec<(MK,MK)>=kept.iter().map(|b|(b.t,b.l)).collect(); blocks.push((cb.t,cb.l)); blocks.extend(to_blocks(&sub,&sol)); println!("p3: sub-solve succeeded (low {}, state {}, attempts {})",l+1,si,attempts); return Some(blocks); }
                    if attempts%2000==0 { let a=clk.act(); println!("p3 low {} pass {} attempts {} sub-nodes {} elapsed {:.0}s/{:.0}s ETA <= {:.0}s (budget-bound)",l+1,pass,attempts,subnodes,a,budget,(budget-a).max(0.0)); } } }
            pass+=1; } }
    println!("p3: finished without a cover: {} attempts, {} sub-DFS nodes, {:.0}s",attempts,subnodes,clk.act()); None }

// ---------- state file ----------
fn st_path()->String{ format!("{}/logs/m94/drive_state.txt",DIR) }
fn st_load()->HashMap<String,f64>{ let mut h=HashMap::new(); for l in std::fs::read_to_string(st_path()).unwrap_or_default().lines(){ let mut it=l.split_whitespace(); if let (Some(k),Some(v))=(it.next(),it.next()) { if let Ok(x)=v.parse::<f64>() { h.insert(k.to_string(),x); } } } h }
fn st_save(h:&HashMap<String,f64>){ let mut ks:Vec<&String>=h.keys().collect(); ks.sort(); let mut s=String::new(); for k in ks { s.push_str(&format!("{} {}\n",k,h[k])); } atomic_write(&st_path(),s.as_bytes()); }
fn append_line(path:&str,line:&str){ use std::io::Write; let mut f=std::fs::OpenOptions::new().create(true).append(true).open(path).unwrap(); writeln!(f,"{}",line).unwrap(); }

fn drive(m:u32){
    start_monitor(); wait_load(); std::thread::sleep(std::time::Duration::from_secs(1));
    let mut st=st_load(); if !st.contains_key("start_ep") { st.insert("start_ep".into(),now_ep() as f64); st_save(&st); } STARTEP.store(st["start_ep"] as u64,Ordering::Relaxed);
    println!("drive m={} wall left {:.0}s of {:.0}s; state {:?}",m,wall_left(),WALL,st);
    if std::path::Path::new(&cert_path(m)).exists() { println!("certificate already exists, nothing to do"); return; }
    let env=setup(m,5); let pool=Mutex::new(pool_load(&env)); let resf=format!("{}/logs/m94/rounds.tsv",DIR);
    // ---- phase 1
    if st.get("p1_done").copied().unwrap_or(0.0)<1.0 { let used=pool.lock().unwrap().p1secs; let budget=(2400.0-used).max(60.0).min(wall_left());
        println!("PHASE 1: pool harvest, budget {:.0}s active (already {:.0}s), LS on |T|<=5 p>=0 (full) and |T|<=4 families alternating, trial 60 s, record <=3 uncovered",budget,used);
        if let Some(sol)=harvest(&env,&pool,budget,0,"p1") { let bl:Vec<(MK,MK)>=sol.iter().map(|&b|env.v[b]).collect(); if declare_success(&env,&bl,"phase 1 LS") {return;} }
        { let p=pool.lock().unwrap(); println!("PHASE 1 done: {}",pool_stats(&p,&env)); }
        st.insert("p1_done".into(),1.0); st_save(&st); }
    // ---- phase 2 rounds
    let r0=st.get("rounds_done").copied().unwrap_or(0.0) as usize;
    for r in r0..6 { if wall_left()<1200.0 {println!("wall budget nearly spent, skipping to report"); break;}
        let tag=format!("p2r{}",r+1); let cap=5000*(r+1); let t0=Clock::new();
        println!("PHASE 2 round {}: restricted exact solve; pooled-block cap {}",r+1,cap);
        let rv={ let p=pool.lock().unwrap(); build_r(&env,&p,cap,0,240.0,&tag) }; let rb=rb_of(&env,&rv); let nr=rb.len();
        let tl=480.0f64.min(wall_left()-600.0).max(60.0); let (vd,sol,nodes,hits,bu)=dfs_solve(&rb,env.lowmask,env.ytot,0,0,0,500_000_000,tl,26,&tag,true);
        let verdict=match vd { 1=>"FOUND", 0=>"INFEASIBLE-ON-R (complete search of R; 64-bit memo keys)", _=>"ABORTED (cap), no verdict" };
        let line=format!("round {}\t|R| {}\tverdict {}\tnodes {}\tmemo_hits {}\tfewest_uncovered_lows_in_dfs {}\tsecs {:.0}",r+1,nr,verdict,nodes,hits,bu,t0.act()); println!("{}",line); append_line(&resf,&line);
        if vd==1 { let bl=to_blocks(&rb,&sol); if declare_success(&env,&bl,&format!("phase 2 round {} DFS",r+1)) {return;} }
        let gb=240.0f64.min((wall_left()-1500.0).max(0.0)); if gb>30.0 { println!("PHASE 2 round {}: growing pool, kicks of 5-15 blocks, {:.0}s",r+1,gb);
            if let Some(sol)=harvest(&env,&pool,gb,1,&format!("{}g",tag)) { let bl:Vec<(MK,MK)>=sol.iter().map(|&b|env.v[b]).collect(); if declare_success(&env,&bl,"phase 2 growth LS") {return;} } }
        { let p=pool.lock().unwrap(); println!("after round {}: {}",r+1,pool_stats(&p,&env)); }
        st.insert("rounds_done".into(),(r+1) as f64); st_save(&st); }
    // ---- phase 3
    if st.get("p3_done").copied().unwrap_or(0.0)<1.0 && wall_left()>600.0 { let rba:Vec<RB>=rb_of(&env,&env.v); let budget=1800.0f64.min(wall_left()-900.0).max(300.0);
        println!("PHASE 3: targeted larger blocks (|T|<=6) through uncovered lows, budget {:.0}s",budget);
        let res={ let p=pool.lock().unwrap(); p3(&env,&p,&rba,budget) };
        if let Some(bl)=res { if declare_success(&env,&bl,"phase 3 targeted") {return;} }
        st.insert("p3_done".into(),1.0); st_save(&st); }
    // ---- phase 4
    if st.get("p4_done").copied().unwrap_or(0.0)<1.0 && wall_left()>400.0 { println!("PHASE 4: allow profit -1 blocks (at most 1, then 2) in the restricted exact solve");
        let rv={ let p=pool.lock().unwrap(); build_r(&env,&p,30000,-1,300.0,"p4") }; let rb=rb_of(&env,&rv); println!("p4: |R| = {} (including profit -1 blocks)",rb.iter().filter(|b|b.nl<b.ny).count()+rb.iter().filter(|b|b.nl>=b.ny).count());
        for mn in [1u32,2] { let tl=(wall_left()-300.0).min(780.0); if tl<60.0 {break;} let t0=Clock::new(); let (vd,sol,nodes,hits,bu)=dfs_solve(&rb,env.lowmask,env.ytot,0,0,mn,500_000_000,tl,26,&format!("p4n{}",mn),true);
            let verdict=match vd { 1=>"FOUND", 0=>"INFEASIBLE-ON-R4", _=>"ABORTED (cap), no verdict" };
            let line=format!("phase4 maxneg {}\t|R| {}\tverdict {}\tnodes {}\tmemo_hits {}\tfewest_uncovered_lows_in_dfs {}\tsecs {:.0}",mn,rb.len(),verdict,nodes,hits,bu,t0.act()); println!("{}",line); append_line(&resf,&line);
            if vd==1 { let bl=to_blocks(&rb,&sol); if declare_success(&env,&bl,&format!("phase 4 maxneg {}",mn)) {return;} } }
        st.insert("p4_done".into(),1.0); st_save(&st); }
    { let p=pool.lock().unwrap(); let s=pool_stats(&p,&env); println!("FINAL: UNDECIDED (no cover found; no impossibility claimed). {}",s); append_line(&format!("{}/logs/m94/final.txt",DIR),&format!("UNDECIDED {}",s)); }
}
fn selftest(){ start_monitor(); STARTEP.store(now_ep(),Ordering::Relaxed); wait_load(); let m=64u32; let env=setup(m,4); let rb=rb_of(&env,&env.v); println!("selftest m={} |R|={}",m,rb.len());
    let (vd,sol,nodes,hits,bu)=dfs_solve(&rb,env.lowmask,env.ytot,0,0,0,200_000_000,300.0,24,"selftest",true); println!("selftest verdict {} nodes {} hits {} fewest-unc {}",vd,nodes,hits,bu);
    if vd==1 { let bl=to_blocks(&rb,&sol); let out=format!("{}/logs/m94/selftest_m{}.sol",DIR,m); println!("selftest finish: {:?}",finish_to(&env,&bl,&out)); } }
fn main(){ let a:Vec<String>=std::env::args().collect(); match a.get(1).map(|s|s.as_str()) { Some("drive")=>{ watchdog(5.5); drive(94) }, Some("selftest")=>{ watchdog(5.5); selftest() }, Some("selftest2")=>{ watchdog(5.5); selftest2() }, _=>main_old() } }
fn selftest2(){ start_monitor(); STARTEP.store(now_ep(),Ordering::Relaxed); wait_load(); let m=64u32; let env=setup(m,4);
    let parts=read_sol::<3>(&format!("{}/certs/m{}.g1.sol",DIR,m)).unwrap(); let mut cb:Vec<(MK,MK)>=vec![];
    for (u,c) in &parts { let t=u.and(&env.ctx.high); let l=u.and(&env.ctx.low); if *c>0 && !l.is0() { cb.push((t,l)); } }
    println!("selftest2: {} certificate blocks (T,L) read from certs/m64.g1.sol",cb.len());
    let mut r1:Vec<RB>=cb.iter().map(|(t,l)|mk_rb(m,t,l)).collect(); sort_rb(&mut r1);
    let (v1,s1,n1,_,_)=dfs_solve(&r1,env.lowmask,env.ytot,0,0,99,10_000_000,60.0,16,"st2a",false); println!("A cert blocks only: verdict {} (expect 1) nodes {} chosen {}",v1,n1,s1.len());
    if v1==1 { let bl=to_blocks(&r1,&s1); let out=format!("{}/logs/m94/selftest_m{}.sol",DIR,m); println!("finish_to check: {:?}",finish_to(&env,&bl,&out)); }
    let mut bad=0; let mut tot=0; for i in 0..r1.len() { let mut r2=r1.clone(); r2.remove(i); let (v,_,_,_,_)=dfs_solve(&r2,env.lowmask,env.ytot,0,0,99,10_000_000,60.0,16,"st2b",false); tot+=1; if v==1 {bad+=1;} }
    println!("B remove one cert block: {} of {} still found (these must have covers by other cert blocks; expect small)",bad,tot);
    let mut rg=Rn(77); let mut r3=r1.clone(); let mut all=rb_of(&env,&env.v); for i in (1..all.len()).rev() { let j=rg.below(i+1); all.swap(i,j); } r3.extend(all.into_iter().take(1500)); sort_rb(&mut r3);
    let (v3,_,n3,h3,_)=dfs_solve(&r3,env.lowmask,env.ytot,0,0,99,50_000_000,120.0,22,"st2c",false); println!("C cert + 1500 random blocks: verdict {} (expect 1) nodes {} memo hits {}",v3,n3,h3);
    // negative: R = random blocks only with one low's blocks deleted
    let low0=env.lows[5]; let r4:Vec<RB>=r1.iter().filter(|b|(b.lm>>low0)&1==0).cloned().collect(); let (v4,_,_,_,_)=dfs_solve(&r4,env.lowmask,env.ytot,0,0,0,10_000_000,60.0,16,"st2d",false); println!("D no block covers low {}: verdict {} (expect 0)",low0+1,v4); }
