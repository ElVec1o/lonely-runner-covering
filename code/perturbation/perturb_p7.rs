// FALSIFICATION TEST FOR P7.  Claim:  ell(n,{b}) * n(n-1) * P(b)  >= c > 0,
// where P(b) = smallest prime NOT dividing b  (P(b) < 2 log b + 2 by Chebyshev).
// Equivalently ell >= c / (n^2 log n).  Exhaustive over 1 <= b < n, exact rationals.
// Also reports the two named regimes so the mechanism can be checked separately.
use std::env;
#[derive(Clone,Copy)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }
/// Sweep note: a zero-length gap is an isolated point of the region, not an absence of one.
/// It is recorded, so that "no component" and "no positive-length component" stay distinct.
fn maxcomp(n:i128,b:i128)->Q{
  let mut iv:Vec<(Q,Q)>=Vec::with_capacity((n*n/2) as usize);
  for j in 1..n { if j==b {continue;} for i in 0..=j { iv.push((q(i*n-1,j*n),q(i*n+1,j*n))); } }
  iv.sort_by(|x,y| cmp(x.0,y.0));
  let mut best=Q{n:0,d:1}; let mut cur=q(0,1);
  for &(l,r) in iv.iter(){
    if cmp(l,cur)!=std::cmp::Ordering::Less { let gp=sub(l,cur); if cmp(gp,best)==std::cmp::Ordering::Greater {best=gp;} }
    if cmp(r,cur)==std::cmp::Ordering::Greater {cur=r;} }
  let one=q(1,1);
  if cmp(one,cur)!=std::cmp::Ordering::Less { let gp=sub(one,cur); if cmp(gp,best)==std::cmp::Ordering::Greater {best=gp;} }
  best
}
fn smallest_prime_not_dividing(b:i128)->i128{
  let mut p=2i128;
  loop{ let mut isp=true; let mut d=2; while d*d<=p { if p%d==0 {isp=false;break;} d+=1; }
        if isp && b % p != 0 { return p; } p+=1; }
}
/// closed form for the b <= n/2 regime
fn closed_c(n:i128,b:i128)->Option<Q>{
  if 2*b>n {return None;}
  let mut j0=n-b; while g(j0,b)!=1 { j0+=1; }
  if 2*(n-b)-j0 <= 0 {return None;}
  Some(q(2*(n-b)-j0, 2*n*b*j0))
}
fn main(){
  let a:Vec<String>=env::args().collect();
  let nlo:i128=a[1].parse().unwrap(); let nhi:i128=a[2].parse().unwrap();
  let mut worst=f64::MAX; let mut wat=(0i128,0i128);
  let mut worst_noP=f64::MAX; let mut wat2=(0i128,0i128);
  let mut cf_tested=0u64; let mut cf_exact=0u64; let mut cf_lower=0u64; let mut cf_bad=0u64;
  for n in nlo..=nhi {
    for b in 1..n {
      let e=maxcomp(n,b);
      let ev=e.n as f64/e.d as f64;
      let base=ev*(n*(n-1)) as f64;
      let p=smallest_prime_not_dividing(b) as f64;
      let val=base*p;
      if val<worst { worst=val; wat=(n,b); }
      if base<worst_noP { worst_noP=base; wat2=(n,b); }
      if let Some(c)=closed_c(n,b){
        cf_tested+=1;
        let ord=cmp(c,e);
        if ord==std::cmp::Ordering::Equal { cf_exact+=1; }
        else if ord==std::cmp::Ordering::Less { cf_lower+=1; }   // closed form is a valid lower bound
        else { cf_bad+=1;
          if cf_bad<=6 { println!("  CF-OVERSHOOT n={} b={} closed={}/{} true={}/{}",n,b,c.n,c.d,e.n,e.d); } }
      }
    }
  }
  println!("n range {}..{}", nlo, nhi);
  println!("min ell*n(n-1)*P(b) = {:.5}  at (n,b)={:?}", worst, wat);
  println!("min ell*n(n-1)      = {:.5}  at (n,b)={:?}", worst_noP, wat2);
  println!("closed form (b<=n/2): tested={} exact={} valid-lower={} OVERSHOOT={}",
           cf_tested, cf_exact, cf_lower, cf_bad);
}
