// REPAIRED CONJECTURE: is  longest component of U(n,M)\B_{v1}  >=  c * (n-2)/(n v1)  ?
// That is the right shape: (n-2)/(n v1) is the hard ceiling, so the question is whether a constant
// fraction of it survives. If yes, the recursion bounds v2 in terms of v1, which is what is needed.
#[derive(Clone,Copy)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }
fn longest(n:i128, m:&[i128], v1:i128)->Q{
  let mut sp:Vec<i128>=(1..n).filter(|x| !m.contains(x)).collect(); sp.push(v1);
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
  best
}
fn main(){
  let mut worst=f64::MAX; let mut wat=(0i128,0i128,0i128,0i128);
  let mut zero=0u64;
  for n in 8..=20i128 {
    for b1 in 1..n { for b2 in (b1+1)..n {
      let m=[b1,b2];
      let mut v1=n;
      while v1<=600 {
        let l=longest(n,&m,v1);
        let lv=l.n as f64/l.d as f64;
        let ceil=(n-2) as f64/((n*v1) as f64);
        if l.n==0 { zero+=1; }
        let r=lv/ceil;
        if r<worst { worst=r; wat=(n,b1,b2,v1); }
        v1 += if v1<60 {1} else if v1<200 {7} else {29};
      }
    }}
  }
  println!("k=2, n=8..20, all M, v1 from n to 600");
  println!("  min over (M,v1) of  longest / [(n-2)/(n v1)]  = {:.5}", worst);
  println!("  attained at (n,b1,b2,v1) = {:?}", wat);
  println!("  cases with NO positive-length component: {}", zero);
}
