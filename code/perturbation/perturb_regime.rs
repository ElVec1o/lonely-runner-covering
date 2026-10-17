// Task 2: probe Conjecture 7.1 IN THE REGIME THAT CAN REFUTE IT.
// Two hard upper bounds on the residual's longest component:
//    ceiling  = (n-2)/(n v1)          (Prop 7.1)
//    ell(n,M)                          (residual is a subset of U)
// At v1 ~ n the ceiling is ~1/n while ell ~ 1/n^2, so ratio-to-ceiling must decay like 1/n.
// The properly formed question is the ratio to min(ell, ceiling).
#[derive(Clone,Copy)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }
fn longest(n:i128, m:&[i128], v1:i128)->f64{
  let mut sp:Vec<i128>=(1..n).filter(|x| !m.contains(x)).collect();
  if v1>0 { sp.push(v1); }
  let mut iv:Vec<(Q,Q)>=Vec::with_capacity((n*n/2+v1+4) as usize);
  for &j in &sp { for i in 0..=j { iv.push((q(i*n-1,j*n), q(i*n+1,j*n))); } }
  iv.sort_by(|x,y| cmp(x.0,y.0));
  let mut best=Q{n:0,d:1}; let mut cur=q(0,1);
  for &(l,r) in iv.iter(){
    if cmp(l,cur)!=std::cmp::Ordering::Less { let gp=sub(l,cur);
      if cmp(gp,best)==std::cmp::Ordering::Greater {best=gp;} }
    if cmp(r,cur)==std::cmp::Ordering::Greater {cur=r;} }
  let one=q(1,1);
  if cmp(one,cur)!=std::cmp::Ordering::Less { let gp=sub(one,cur);
    if cmp(gp,best)==std::cmp::Ordering::Greater {best=gp;} }
  best.n as f64/best.d as f64
}
fn main(){
  println!("(A) ratio to the CEILING at v1 = n  -- does it decay like 1/n?");
  println!("{:>4} {:>12} {:>12} {:>10}","n","min ratio","1/n","ratio*n");
  for n in [8i128,12,16,20,24,28,32,36,40] {
    let mut w=f64::MAX;
    for b1 in 1..n { for b2 in (b1+1)..n {
      let m=[b1,b2];
      let l=longest(n,&m,n);
      let c=(n-2) as f64/((n*n) as f64);
      if l/c<w { w=l/c; }
    }}
    println!("{:>4} {:>12.5} {:>12.5} {:>10.4}",n,w,1.0/n as f64,w*n as f64);
  }
  println!();
  println!("(B) ratio to min(ell, ceiling), v1 swept from n to 4000");
  let mut worst=f64::MAX; let mut wat=(0i128,0i128,0i128,0i128); let mut zero=0u64;
  for n in 8..=20i128 {
    for b1 in 1..n { for b2 in (b1+1)..n {
      let m=[b1,b2];
      let ell=longest(n,&m,0);
      let mut v1=n;
      while v1<=4000 {
        let l=longest(n,&m,v1);
        if l==0.0 { zero+=1; }
        let ceil=(n-2) as f64/((n*v1) as f64);
        let base=if ell<ceil {ell} else {ceil};
        let r=l/base;
        if r<worst { worst=r; wat=(n,b1,b2,v1); }
        v1 += if v1<3*n {1} else if v1<400 {13} else {197};
      }
    }}
  }
  println!("  min ratio = {:.5} at (n,b1,b2,v1) = {:?}",worst,wat);
  println!("  cases with no positive-length component: {}",zero);
}
