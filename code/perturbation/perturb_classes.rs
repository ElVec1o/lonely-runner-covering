// Three-way classification of M for the component bound.
//  A: M contains a unit mod n                      -> proved: ell >= 1/(n(n-1))
//  B: no unit, but some b in M with 2b > n         -> missing-speed time a/b available
//  C: no unit, every b in M has 2b <= n            -> no route yet
// Reports min over M of ell*n(n-1) in each class. Exact rationals throughout.
use std::env;
#[derive(Clone,Copy)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }
/// Sweep note: a zero-length gap is an isolated point of the region, not an absence of one.
/// It is recorded, so that "no component" and "no positive-length component" stay distinct.
fn maxcomp(n:i128,m:&[i128])->Q{
  let mut iv:Vec<(Q,Q)>=Vec::new();
  for j in 1..n { if m.contains(&j){continue;} for i in 0..=j { iv.push((q(i*n-1,j*n),q(i*n+1,j*n))); } }
  iv.sort_by(|a,b| cmp(a.0,b.0));
  let mut best=Q{n:0,d:1}; let mut cur=q(0,1);
  for &(l,r) in iv.iter(){
    if cmp(l,cur)!=std::cmp::Ordering::Less { let gp=sub(l,cur); if cmp(gp,best)==std::cmp::Ordering::Greater {best=gp;} }
    if cmp(r,cur)==std::cmp::Ordering::Greater {cur=r;} }
  let one=q(1,1);
  if cmp(one,cur)!=std::cmp::Ordering::Less { let gp=sub(one,cur); if cmp(gp,best)==std::cmp::Ordering::Greater {best=gp;} }
  best
}
fn main(){
  let a:Vec<String>=env::args().collect();
  let nlo:i128=a[1].parse().unwrap(); let nhi:i128=a[2].parse().unwrap(); let k:usize=a[3].parse().unwrap();
  for n in nlo..=nhi {
    let cand:Vec<i128>=(1..n).collect(); if cand.len()<k {continue;}
    let mut mins:[Option<(Q,Vec<i128>)>;3]=[None,None,None];
    let mut cnt=[0u64;3];
    let mut idx:Vec<usize>=(0..k).collect();
    loop{
      let m:Vec<i128>=idx.iter().map(|&i| cand[i]).collect();
      let cls = if m.iter().any(|&j| g(j,n)==1) {0}
                else if m.iter().any(|&b| 2*b>n) {1} else {2};
      let e=maxcomp(n,&m); cnt[cls]+=1;
      match &mins[cls]{ None=>mins[cls]=Some((e,m.clone())),
        Some((w,_))=>if cmp(e,*w)==std::cmp::Ordering::Less {mins[cls]=Some((e,m.clone()))} }
      let mut p=k; loop{ if p==0 {break;} p-=1; if idx[p]!=p+cand.len()-k {break;} if p==0 {break;} }
      if idx[p]==p+cand.len()-k {break;}
      idx[p]+=1; for z in (p+1)..k { idx[z]=idx[z-1]+1; }
    }
    let f=|o:&Option<(Q,Vec<i128>)>,c:u64| match o {
      Some((w,mm))=>format!("{:.4} M={:?} [{}]",(w.n as f64/w.d as f64)*(n*(n-1)) as f64,mm,c),
      None=>format!("-- [{}]",c) };
    println!("n={:<4} A:{}   B:{}   C:{}", n, f(&mins[0],cnt[0]), f(&mins[1],cnt[1]), f(&mins[2],cnt[2]));
  }
}
