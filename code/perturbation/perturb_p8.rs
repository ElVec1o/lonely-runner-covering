// P8 RECURSION TEST.  U' = U(n,M) \ B_{v1}.  For the recursion to bound the next replacement we
// need U' to still have a component of positive length.  Adversary picks v1 to shatter U.
// Reports min over v1 in [n, cap*n] of maxcomp(U') * n(n-1), and how often it degenerates to 0.
use std::env;
#[derive(Clone,Copy)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }
/// max component of { t : ||s t|| >= 1/n for all s in speeds }
/// Sweep note: a zero-length gap is an isolated point of the region, not an absence of one.
/// It is recorded, so that "no component" and "no positive-length component" stay distinct.
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
  let nlo:i128=a[1].parse().unwrap(); let nhi:i128=a[2].parse().unwrap();
  let cap:i128=a[3].parse().unwrap();
  let mut zero_cases:Vec<(i128,i128,i128)>=Vec::new();
  let mut globalmin=f64::MAX; let mut gat=(0i128,0i128,0i128);
  for n in nlo..=nhi {
    let mut worst_over_b=f64::MAX; let mut wb=(0i128,0i128);
    for b in 1..n {
      let present:Vec<i128>=(1..n).filter(|&x| x!=b).collect();
      let mut worst=f64::MAX; let mut wv=0;
      for v1 in n..=(cap*n) {
        let mut sp=present.clone(); sp.push(v1);
        let e=maxcomp_set(n,&sp);
        let val=(e.n as f64/e.d as f64)*(n*(n-1)) as f64;
        if e.n==0 { zero_cases.push((n,b,v1)); }
        if val<worst { worst=val; wv=v1; }
      }
      if worst<worst_over_b { worst_over_b=worst; wb=(b,wv); }
    }
    if worst_over_b<globalmin { globalmin=worst_over_b; gat=(n,wb.0,wb.1); }
    println!("n={:<4} min over (b,v1) of maxcomp(U')*n(n-1) = {:.6}  at b={} v1={}",
             n, worst_over_b, wb.0, wb.1);
  }
  println!("--- global min = {:.6} at (n,b,v1)={:?}", globalmin, gat);
  println!("--- DEGENERATE (U' has zero-length components) count = {}", zero_cases.len());
  for z in zero_cases.iter().take(12) { println!("      n={} b={} v1={}", z.0,z.1,z.2); }
}
