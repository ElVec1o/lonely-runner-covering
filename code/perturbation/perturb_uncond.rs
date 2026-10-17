// UNCONDITIONAL CRITERION.  Covering needs  sum_{v in R} 1/v >= ell(n,M)(n-2k)/2,
// while v >= n for all v in R forces sum 1/v <= k/n.  So if
//        ell(n,M)  >  2k / (n (n-2k))
// no R whatsoever can cover U(n,M): V is lonely for EVERY choice of R, unconditionally.
// Question: what fraction of the class does that settle?
#[derive(Clone,Copy)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }
fn ell(n:i128, m:&[i128])->Q{
  let mut iv:Vec<(Q,Q)>=Vec::new();
  for j in 1..n { if m.contains(&j) {continue;} for i in 0..=j { iv.push((q(i*n-1,j*n),q(i*n+1,j*n))); } }
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
  for k in 1..=3usize {
    println!("k = {}", k);
    println!("{:>5} {:>10} {:>10} {:>9}   worst-case example settled?","n","subsets","settled","percent");
    for n in [10i128,14,18,22,26,30,34,38] {
      if (n as usize) <= 2*k { continue; }
      let mut tot=0u64; let mut good=0u64;
      // enumerate all k-subsets of [1,n)
      let cand:Vec<i128>=(1..n).collect();
      let mut idx:Vec<usize>=(0..k).collect();
      loop{
        let m:Vec<i128>=idx.iter().map(|&i| cand[i]).collect();
        let e=ell(n,&m); tot+=1;
        // ell > 2k/(n(n-2k))  <=>  e.n * n*(n-2k) > 2k * e.d
        if e.n * (n*(n - 2*k as i128)) > (2*k as i128) * e.d { good+=1; }
        let mut p=k; loop{ if p==0 {break;} p-=1; if idx[p]!=p+cand.len()-k {break;} if p==0 {break;} }
        if idx[p]==p+cand.len()-k {break;}
        idx[p]+=1; for z in (p+1)..k { idx[z]=idx[z-1]+1; }
      }
      println!("{:>5} {:>10} {:>10} {:>8.1}%",n,tot,good,100.0*good as f64/tot as f64);
    }
    println!();
  }
}
