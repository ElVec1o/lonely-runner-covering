// P8, correct setting: a genuine k=2 perturbation.  M = {b1,b2}, R = {v1,v2}.
// After the adversary picks v1 to shatter, does U' = U(n,M) \ B_{v1} keep a component?
// By monotonicity U(n,{b1,b2}) contains U(n,{b1}), so this is strictly more favourable than the
// |M|=1 test run earlier.  Exact rationals.
use std::env;
#[derive(Clone,Copy)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }
/// (longest component length, number of isolated points).  A gap of length zero is an isolated
/// point of the region: two bad intervals abutting exactly.  Dropping those makes "empty" and
/// "no positive-length component" indistinguishable, which matters for the residual region.
fn maxcomp_set(n:i128, speeds:&[i128])->Q{
  let mut iv:Vec<(Q,Q)>=Vec::new();
  for &j in speeds { for i in 0..=j { iv.push((q(i*n-1,j*n), q(i*n+1,j*n))); } }
  iv.sort_by(|x,y| cmp(x.0,y.0));
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
  let nlo:i128=a[1].parse().unwrap(); let nhi:i128=a[2].parse().unwrap(); let cap:i128=a[3].parse().unwrap();
  let mut degen=0u64; let mut degex:Vec<(i128,i128,i128,i128)>=Vec::new();
  for n in nlo..=nhi {
    let mut worst=f64::MAX; let mut wat=(0i128,0i128,0i128);
    for b1 in 1..n { for b2 in (b1+1)..n {
      let present:Vec<i128>=(1..n).filter(|&x| x!=b1 && x!=b2).collect();
      for v1 in n..=(cap*n) {
        let mut sp=present.clone(); sp.push(v1);
        let e=maxcomp_set(n,&sp);
        let val=(e.n as f64/e.d as f64)*(n*(n-1)) as f64;
        if e.n==0 { degen+=1; if degex.len()<10 { degex.push((n,b1,b2,v1)); } }
        if val<worst { worst=val; wat=(b1,b2,v1); }
      }
    }}
    println!("n={:<4} min over (M,v1) of maxcomp(U')*n(n-1) = {:.6}  at M={{{},{}}} v1={}",
             n, worst, wat.0, wat.1, wat.2);
  }
  println!("--- DEGENERATE (U' has no positive-length component) = {}", degen);
  for d in degex.iter() { println!("      n={} M={{{},{}}} v1={}", d.0,d.1,d.2,d.3); }
}
