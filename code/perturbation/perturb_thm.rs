// CANDIDATE THEOREM (unconditional, no conjecture, no bound on R):
//   If M contains b with 2b <= n-1 and 8kb <= n, and n > 6k-2, then
//   ell(n,M) > 2k/(n(n-2k)), hence NO set R of k speeds >= n can cover U(n,M),
//   hence V = ([n-1]\M) u R is lonely for EVERY such R.
//
// Chain: Prop 3.1 gives ell >= (2s-j0)/(2 n b j0) with s=n-b, j0 <= n-1, so
//        ell >= (n-2b+1)/(2 n b (n-1)); the criterion needs
//        (n-2b+1)(n-2k) > 4kb(n-1).
// Verify BOTH the algebraic implication and the true ell, exhaustively.
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
  // (1) algebraic step: 2b<=n-1, 8kb<=n, n>6k-2  ==>  (n-2b+1)(n-2k) > 4kb(n-1)
  let mut bad1=0u64; let mut t1=0u64; let mut t1_b2=0u64;
  for n in 3..=4000i128 { for k in 1..=60i128 {
    if 2*k>=n || n<=6*k-2 {continue;}
    for b in 1..n { if 2*b>n-1 || 8*k*b>n {continue;}
      t1+=1; if b>=2 { t1_b2+=1; }
      if !((n-2*b+1)*(n-2*k) > 4*k*b*(n-1)) { bad1+=1;
        if bad1<=5 {println!("  ALG FAIL n={} k={} b={}",n,k,b);} }
    }}}
  println!("(1) algebraic implication: {} triples, {} failures", t1, bad1);
  println!("(1b) of these, triples with b>=2: {}", t1_b2);
  // (2) the true ell really exceeds the threshold, exhaustively over M containing such a b
  let mut bad2=0u64; let mut t2=0u64; let mut worst=f64::MAX; let mut wat=(0i128,0i128,0i128);
  for n in 6..=60i128 { for k in 1..=3i128 {
    if 2*k>=n || n<=6*k-2 {continue;}
    for b in 1..n { if 2*b>n-1 || 8*k*b>n {continue;}
      // M = {b} u (k-1 arbitrary others); monotonicity means ell only grows, so test M={b} alone
      let e=ell(n,&[b]); t2+=1;
      let lhs = e.n*(n*(n-2*k)); let rhs = 2*k*e.d;
      if !(lhs>rhs) { bad2+=1; if bad2<=5 {println!("  ELL FAIL n={} k={} b={}",n,k,b);} }
      let r = (e.n as f64/e.d as f64)/(2.0*k as f64/((n*(n-2*k)) as f64));
      if r<worst {worst=r; wat=(n,k,b);}
    }}}
  println!("(2) true ell exceeds threshold: {} cases, {} failures; min margin ratio {:.4} at (n,k,b)={:?}",
           t2, bad2, worst, wat);
  // (3) how much of the class does the theorem cover?
  println!("(3) fraction of k-subsets containing some admissible b:");
  for k in 1..=3usize { for n in [40i128,80,160,320] {
    if (n as usize)<=6*k {continue;}
    let mut adm=0i128; for b in 1..n { if 2*b<=n-1 && 8*(k as i128)*b<=n {adm+=1;} }
    // fraction of k-subsets meeting the admissible set
    let tot = (0..k).fold(1.0f64,|a,i| a*((n-1-i as i128) as f64)/((i+1) as f64));
    let miss = if (n-1-adm) as usize >= k {(0..k).fold(1.0f64,|a,i| a*((n-1-adm-i as i128) as f64)/((i+1) as f64))} else {0.0};
    println!("   k={} n={:<5} admissible b: 1..{:<4}  covered {:.1}% of subsets", k, n, adm, 100.0*(1.0-miss/tot));
  }}
}
