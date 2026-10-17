// Enumerate the Pareto family of minimal valid blocks (T subset Y, L subset Low), |T|<=tmax.
// Family F(tmax): all (T,L) such that tau(T u L)=|L|, L maximal valid for T, T minimal for L.
// Completeness: every valid block (T0,L0) with a T subset T0, |T|<=tmax,... see XC_REPORT.md.
use crate::valid::Ctx; use crate::common::*;
use std::collections::HashSet; use std::sync::atomic::{AtomicUsize,Ordering}; use std::sync::Mutex; use std::time::Instant;
pub struct Priv { pub by_y:Vec<Vec<(u128,u32)>>, pub free_lows:u128 }
pub fn build_priv(ctx:&Ctx)->Priv{
    let mut by_y=vec![vec![];ctx.n as usize]; let mut free=0u128;
    for &e in &ctx.es { let lo=e&ctx.low; if lo.count_ones()!=1 {continue;} let yp=e&ctx.high; let lb=lo.trailing_zeros();
        if yp==0 { free|=lo; } else { let mut r=yp; while r!=0 { let b=r.trailing_zeros() as usize; r&=r-1; by_y[b].push((yp,lb)); } } }
    Priv{by_y,free_lows:free}
}
struct Wk<'a>{ ctx:&'a Ctx, pr:&'a Priv, tmax:u32, out:Vec<(u128,u128)>, buf:Vec<u128>, nodes:u64, maxvalid:usize, nlsets:u64 }
impl<'a> Wk<'a>{
    fn process(&mut self,t:u128,c:u128){
        if c==0 {return;}
        let cl=bits(c); let mut valid:Vec<u128>=vec![]; let mut set:HashSet<u128>=HashSet::new();
        self.dfs_l(t,&cl,0,0,&mut valid,&mut set);
        self.nlsets+=valid.len() as u64; if valid.len()>self.maxvalid {self.maxvalid=valid.len();}
        for &l in &valid {
            if cl.iter().any(|&b| l>>b&1==0 && set.contains(&(l|1u128<<b))) {continue;}
            // T minimal for L
            let mut ok=true; for y in bits(t) { if self.ctx.valid((t&!(1u128<<y))|l,&mut self.buf) { ok=false; break; } }
            if ok { self.out.push((t,l)); }
        }
    }
    fn dfs_l(&mut self,t:u128,cl:&[u32],from:usize,l:u128,valid:&mut Vec<u128>,set:&mut HashSet<u128>){
        for i in from..cl.len(){ let l2=l|1u128<<cl[i];
            if self.ctx.valid(t|l2,&mut self.buf) { valid.push(l2); set.insert(l2); self.dfs_l(t,cl,i+1,l2,valid,set); } }
    }
    fn dfs_t(&mut self,t:u128,k:u32,last:usize,c:u128){
        self.nodes+=1; self.process(t,c);
        if k>=self.tmax {return;}
        let ny=self.ctx.n as usize;
        for y in last..ny { if self.ctx.high>>y&1==0 {continue;}
            let t2=t|1u128<<y; let mut c2=c;
            for &(yp,lb) in &self.pr.by_y[y] { if yp&!t2==0 { c2|=1u128<<lb; } }
            self.dfs_t(t2,k+1,y+1,c2);
        }
    }
}
// one chunk = blocks whose T has smallest element y0 (or T=empty for chunk id 0)
pub fn run_chunk(ctx:&Ctx,pr:&Priv,tmax:u32,chunk:usize)->(Vec<(u128,u128)>,u64,u64,usize){
    let mut w=Wk{ctx,pr,tmax,out:vec![],buf:vec![],nodes:0,maxvalid:0,nlsets:0};
    let hy:Vec<usize>=(0..ctx.n as usize).filter(|&y|ctx.high>>y&1==1).collect();
    if chunk==0 { /* T=empty: only free lows, stripped */ }
    else { let y=hy[chunk-1]; let t=1u128<<y; let mut c=0u128;
        for &(yp,lb) in &pr.by_y[y] { if yp&!t==0 { c|=1u128<<lb; } }
        if tmax>=1 { w.dfs_t(t,1,y+1,c); } }
    (w.out,w.nodes,w.nlsets,w.maxvalid)
}
pub fn blkfile(m:u32,tmax:u32)->String{ format!("{}/logs/xc/blocks_m{}_t{}.bin",DIR,m,tmax) }
pub fn read_blocks(path:&str)->Vec<(u128,u128)>{ let b=std::fs::read(path).unwrap_or_default(); b.chunks_exact(32).map(|c|(u128::from_le_bytes(c[..16].try_into().unwrap()),u128::from_le_bytes(c[16..].try_into().unwrap()))).collect() }
// enumerate all chunks with checkpoint/resume; returns blocks (T,L)
pub fn enumerate_blocks(ctx:&Ctx,tmax:u32,nth:usize,persist:bool)->Vec<(u128,u128)>{
    let m=ctx.m; let pr=build_priv(ctx); let nch=1+ (ctx.high.count_ones() as usize);
    let ck=format!("{}/logs/xc/blkck_m{}_t{}.txt",DIR,m,tmax); let bf=blkfile(m,tmax);
    // resume: ck lists done chunks; bf holds blocks of done chunks only (written together, atomically ordered: bf first, then ck)
    let mut done:HashSet<usize>=HashSet::new();
    if persist { if let Ok(s)=std::fs::read_to_string(&ck){ for t in s.split_whitespace(){ done.insert(t.parse().unwrap()); } } }
    let mut all:Vec<(u128,u128)>= if done.is_empty() {vec![]} else {read_blocks(&bf)};
    if !done.is_empty(){ println!("resume: {} chunks done, {} blocks",done.len(),all.len()); }
    let todo:Vec<usize>=(0..nch).filter(|c|!done.contains(c)).collect();
    let next=AtomicUsize::new(0); let st=Mutex::new((all.clone(),done.clone(),0u64,0u64,0usize)); let t0=Instant::now(); let ntodo=todo.len();
    let t0_done=done.len();
    std::thread::scope(|sc|{ for _ in 0..nth { sc.spawn(||loop{
        let i=next.fetch_add(1,Ordering::SeqCst); if i>=ntodo {break;} let ch=todo[i];
        let (b,nodes,nl,mv)=run_chunk(ctx,&pr,tmax,ch);
        let mut g=st.lock().unwrap(); g.0.extend(b); g.1.insert(ch); g.2+=nodes; g.3+=nl; if mv>g.4 {g.4=mv;}
        if persist { let mut bytes=Vec::with_capacity(g.0.len()*32); for &(t,l) in &g.0 { bytes.extend_from_slice(&t.to_le_bytes()); bytes.extend_from_slice(&l.to_le_bytes()); }
        atomic_write(&bf,&bytes); let s:Vec<String>=g.1.iter().map(|x|x.to_string()).collect(); atomic_write(&ck,s.join(" ").as_bytes()); }
        let d=g.1.len()-t0_done; let el=t0.elapsed().as_secs_f64();
        println!("chunk {} done {}/{} blocks {} nodes {} Lsets {} maxvalid {} t={:.0}s rss {:.2}GB",ch,g.1.len(),nch,g.0.len(),g.2,g.3,g.4,el,rss());
        let _=d; }); } });
    let g=st.lock().unwrap(); all=g.0.clone(); all.sort(); all
}

// family loader used by search/sat/stats: file cache if present, else in-memory enumeration (no disk use)
pub fn get_blocks(ctx:&Ctx,tmax:u32)->Vec<(u128,u128)>{
    if std::env::var("XC_IRRED").is_ok() { let f=read_blocks(&format!("{}/logs/xc/irred_m{}_t{}.bin",DIR,ctx.m,tmax)); assert!(!f.is_empty(),"run xc reduce first"); return f; }
    let f=read_blocks(&blkfile(ctx.m,tmax)); if !f.is_empty() {return f;}
    let mut b=enumerate_blocks(ctx,tmax,6,false); b.dedup(); b }

// Exact reduction: drop a block (T,L) if T = T1 u T2 (disjoint, nonempty), L = L1 u L2 (disjoint, nonempty) with both
// (T1,L1), (T2,L2) valid. Any cover using it can use the two parts instead (parts are dominated by family blocks with
// smaller T; induction on sum |T|^2), so the reduced family has a cover iff the full family does.
pub fn reducible(ctx:&Ctx,t:u128,l:u128,buf:&mut Vec<u128>)->bool{
    let tb=bits(t); let lb=bits(l); let nt=tb.len(); let nl=lb.len(); if nt<2||nl<2 {return false;}
    for tm in 1u32..(1u32<<nt) { if tm&1==0 || tm==(1u32<<nt)-1 {continue;}  // T1 contains first element, T2 nonempty
        let mut t1=0u128; let mut t2=0u128; for i in 0..nt { if tm>>i&1==1 { t1|=1u128<<tb[i]; } else { t2|=1u128<<tb[i]; } }
        for lm in 1u32..(1u32<<nl)-1 { let mut l1=0u128; let mut l2=0u128; for i in 0..nl { if lm>>i&1==1 { l1|=1u128<<lb[i]; } else { l2|=1u128<<lb[i]; } }
            if ctx.valid(t1|l1,buf) && ctx.valid(t2|l2,buf) { return true; } } }
    false }
pub fn reduce(ctx:&Ctx,blocks:&[(u128,u128)],nth:usize)->Vec<(u128,u128)>{
    let n=blocks.len(); let next=AtomicUsize::new(0); let t0=Instant::now(); let keep=Mutex::new(vec![false;n]); let doneb=AtomicUsize::new(0);
    std::thread::scope(|sc|{ for _ in 0..nth { sc.spawn(||{ let mut buf=vec![]; let mut loc:Vec<usize>=vec![];
        loop { let s=next.fetch_add(4096,Ordering::SeqCst); if s>=n {break;} let e=(s+4096).min(n);
            for i in s..e { let (t,l)=blocks[i]; if !reducible(ctx,t,l,&mut buf) { loc.push(i); } }
            let d=doneb.fetch_add(e-s,Ordering::SeqCst)+(e-s);
            if (s/4096)%32==0 { let el=t0.elapsed().as_secs_f64(); println!("reduce {}/{} rate {:.0}/s eta {:.0}s",d,n,d as f64/el.max(1e-9),(n-d) as f64/(d as f64/el.max(1e-9))); } }
        let mut k=keep.lock().unwrap(); for i in loc { k[i]=true; } }); } });
    let k=keep.lock().unwrap(); (0..n).filter(|&i|k[i]).map(|i|blocks[i]).collect() }
