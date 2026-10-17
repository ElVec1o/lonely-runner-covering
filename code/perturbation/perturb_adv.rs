// ADVERSARIAL REVIEW of the P7 proof, attacking each load-bearing step separately.
//  A. Is the m>=2 residue class ever binding?  Paper claims never; that step is MISSING from the text.
//  B. How big is the coprime gap j0 - s ?  The paper's b<=n/2 branch uses j0 <= s+b-1, which is
//     far too weak when b ~ n/2 (it yields only ~1/n^3). Measure the true gap.
//  C. Is  2s - j0 >= alpha*s  for a fixed alpha > 0 ?  This is what the b<=n/2 branch really needs.
use std::env;
fn g(a:i64,b:i64)->i64{ if b==0 {a.abs()} else {g(b,a%b)} }
fn main(){
  let a:Vec<String>=env::args().collect();
  let nhi:i64=a[1].parse().unwrap();  // ranges start at n=3 (D9 fix)
  let mut maxgap=0i64; let mut mg=(0i64,0i64);
  let mut min_alpha=f64::MAX; let mut ma=(0i64,0i64);
  let mut bind_violations=0i64;
  let mut worst_m2=f64::MAX; let mut wm2=(0i64,0i64,0i64);
  for n in 3..=nhi { for b in 1..n {
    let s=n-b;
    let mut j0=s; while g(j0,b)!=1 { j0+=1; }
    if j0-s>maxgap { maxgap=j0-s; mg=(n,b); }
    if 2*b<=n {
      let alpha=(2*s-j0) as f64/s as f64;
      if alpha<min_alpha { min_alpha=alpha; ma=(n,b); }
      if 2*s-j0<=0 { bind_violations+=1; }
    }
    // A: is any m>=2 speed binding?  compare (m*n-b)/(n b j) against (n-b)/(n b j0) for m=2
    //    i.e. is (2n-b)/j >= (n-b)/j0 for every present j <= n-1 ?
    for j in 1..n { if j==b {continue;}
      let lhs=(2*n-b) as f64/j as f64; let rhs=(n-b) as f64/j0 as f64;
      let ratio=lhs/rhs;
      if ratio<worst_m2 { worst_m2=ratio; wm2=(n,b,j); }
    }
  }}
  println!("B. max coprime gap j0 - s = {} at (n,b)={:?}", maxgap, mg);
  println!("C. min alpha = (2s-j0)/s over b<=n/2 : {:.5} at (n,b)={:?}", min_alpha, ma);
  println!("C. cases with 2s-j0 <= 0 (would break the b<=n/2 branch): {}", bind_violations);
  println!("A. min over all (n,b,j) of [(2n-b)/j] / [(n-b)/j0] = {:.5} at {:?}", worst_m2, wm2);
  println!("   (A > 1 everywhere means the m>=2 classes are never binding, as the proof assumes)");
}
