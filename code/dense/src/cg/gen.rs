// Randomized block generator (pricing heuristic). Every returned column is exactly validated.
use crate::valid::Ctx;
pub struct Rng(pub u64);
impl Rng {
    pub fn next(&mut self)->u64{ let mut x=self.0; x^=x<<13; x^=x>>7; x^=x<<17; self.0=x; x.wrapping_mul(0x2545F4914F6CDD1D) }
    pub fn f(&mut self)->f64{ (self.next()>>11) as f64/((1u64<<53) as f64) }
    pub fn below(&mut self,n:usize)->usize{ (self.next()%(n as u64)) as usize }
}
fn bits(s:u128)->Vec<u32>{ let mut v=vec![]; let mut r=s; while r!=0 { v.push(r.trailing_zeros()); r&=r-1; } v }
fn gain(score:&[f64],new:u128)->f64{ let mut g=0.0; let mut r=new; while r!=0 { g+=score[r.trailing_zeros() as usize]; r&=r-1; } g }
fn shuffle(v:&mut Vec<u32>,rng:&mut Rng){ for i in (1..v.len()).rev(){ let j=rng.below(i+1); v.swap(i,j);} }
// reduce T (greedy random order), grow L (greedy random order), reduce T again
pub fn finalize(ctx:&Ctx,mut s:u128,rng:&mut Rng,buf:&mut Vec<u128>,out:&mut Vec<u128>){
    let red=|s:&mut u128,rng:&mut Rng,buf:&mut Vec<u128>|{ let mut hv=bits(*s&ctx.high); shuffle(&mut hv,rng);
        for y in hv { let t=*s&!(1u128<<y); if ctx.valid(t,buf) { *s=t; } } };
    red(&mut s,rng,buf); out.push(s);
    let mut lv=bits(ctx.low&!s); shuffle(&mut lv,rng);
    for l in lv { let t=s|(1u128<<l); if ctx.valid(t,buf) { s=t; } }
    red(&mut s,rng,buf); out.push(s);
}
pub fn gen_block(ctx:&Ctx,score:&[f64],smax:u32,rng:&mut Rng,buf:&mut Vec<u128>,out:&mut Vec<u128>,startw:&[f64]){
    // start vertex: low, weighted by startw
    let tot:f64=startw.iter().sum(); let mut x=rng.f()*tot; let mut v0=0usize;
    for (i,&w) in startw.iter().enumerate(){ x-=w; if x<=0.0 { v0=i; break; } v0=i; }
    if ctx.adj[v0].is_empty(){return;}
    let mut s=0u128;
    { let mut best=-1e18; for _ in 0..3 { let e=ctx.es[ctx.adj[v0][rng.below(ctx.adj[v0].len())] as usize];
        let g=gain(score,e)+rng.f()*0.2; if g>best {best=g; s=e;} } }
    if s.count_ones()>smax {return;}
    for _step in 0..40 {
        if ctx.valid(s,buf) { finalize(ctx,s,rng,buf,out); finalize(ctx,s,rng,buf,out); if rng.f()<0.6 {return;} }
        let vs=bits(s); let mut best=-1e18; let mut be=0u128;
        for _ in 0..6 { let v=vs[rng.below(vs.len())] as usize; let a=&ctx.adj[v]; if a.is_empty(){continue;}
            let e=ctx.es[a[rng.below(a.len())] as usize]; let nw=e&!s; if nw==0 {continue;}
            if (s|e).count_ones()>smax {continue;}
            let g=gain(score,nw)+rng.f()*0.4; if g>best {best=g;be=e;} }
        if be==0 {return;}
        s|=be;
    }
}
