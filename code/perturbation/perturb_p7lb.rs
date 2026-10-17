// VERIFY THE UNIFIED LOWER BOUND used in the P7 proof.
//   s  = n - b,   j0 = min{ j >= s : gcd(j,b) = 1 }   (exists in [s, s+b-1])
//   LB(n,b) = max over:
//     (A) 1/(n(n-1))                      if gcd(b,n) = 1
//     (M) s/(n b j0) - [2b<n]/(2 b n)     the missing-speed route at a/b
// Claim: LB(n,b) <= ell(n,{b}) for ALL 1 <= b < n.  Any violation is fatal to the proof.
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
  let mut iv:Vec<(Q,Q)>=Vec::with_capacity((n*n/2+n) as usize);
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
fn spnd(b:i128)->i128{ let mut p=2i128;
  loop{ let mut isp=true; let mut d=2; while d*d<=p { if p%d==0 {isp=false;break;} d+=1; }
        if isp && b%p!=0 {return p;} p+=1; } }
fn main(){
  let a:Vec<String>=env::args().collect();
  let nlo:i128=a[1].parse().unwrap(); let nhi:i128=a[2].parse().unwrap();
  let mut viol=0u64; let mut tot=0u64;
  let mut worstratio=f64::MAX; let mut wr=(0i128,0i128);
  let mut worstP=f64::MAX; let mut wp=(0i128,0i128);
  let mut j0_gap_max=0i128; let mut j0g=(0i128,0i128);
  for n in nlo..=nhi { for b in 1..n {
    tot+=1;
    let s=n-b;
    let mut j0=s.max(1); while g(j0,b)!=1 { j0+=1; }
    if j0 > s.max(1)+b-1 { println!("  J0-WINDOW-FAIL n={} b={} j0={}",n,b,j0); }
    if j0-s.max(1) > j0_gap_max { j0_gap_max=j0-s.max(1); j0g=(n,b); }
    // route M
    let mut lb = if 2*b<n { sub(q(s, n*b*j0), q(1, 2*b*n)) } else { q(s, n*b*j0) };
    if lb.n < 0 { lb = q(0,1); }
    // route A
    if g(b,n)==1 { let la=q(1,n*(n-1)); if cmp(la,lb)==std::cmp::Ordering::Greater { lb=la; } }
    let tr=maxcomp(n,b);
    if cmp(lb,tr)==std::cmp::Ordering::Greater { viol+=1;
      if viol<=8 { println!("  VIOLATION n={} b={} LB={}/{} true={}/{}",n,b,lb.n,lb.d,tr.n,tr.d); } }
    let lbf=lb.n as f64/lb.d as f64;
    let r=lbf*(n*(n-1)) as f64;
    if r<worstratio { worstratio=r; wr=(n,b); }
    let rp=r*spnd(b) as f64;
    if rp<worstP { worstP=rp; wp=(n,b); }
  }}
  println!("n range {}..{}   pairs tested = {}", nlo, nhi, tot);
  println!("LB <= true ell  VIOLATIONS = {}", viol);
  println!("min LB*n(n-1)        = {:.5} at (n,b)={:?}", worstratio, wr);
  println!("min LB*n(n-1)*P(b)   = {:.5} at (n,b)={:?}", worstP, wp);
  println!("max coprime gap j0-s = {} at (n,b)={:?}  (Jacobsthal-type)", j0_gap_max, j0g);
}
