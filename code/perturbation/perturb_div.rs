// Conjecture 7.2: is the obstruction exactly DIVISIBILITY?
// Split (n,M,v1) by  D = { q in M u {n} : q does not divide v1 }  and compare min ratios.
// Prediction: |D| >= 1 gives a good constant; the bad cases concentrate at |D| = 0, which forces
// lcm(M u {n}) | v1.
#[derive(Clone,Copy)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }
fn longest(n:i128, m:&[i128], vs:&[i128])->f64{
  let mut sp:Vec<i128>=(1..n).filter(|x| !m.contains(x)).collect();
  for &v in vs { sp.push(v); }
  let mut iv:Vec<(Q,Q)>=Vec::new();
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
  // per-class minima
  let mut mins=[f64::MAX;4]; let mut ats=[(0i128,0i128,0i128,0i128);4]; let mut cnt=[0u64;4];
  for n in 8..=30i128 { for b1 in 1..n { for b2 in (b1+1)..n {
    let m=[b1,b2]; let e=longest(n,&m,&[]);
    let mut v1=n; while v1<=6*n {
      let l=longest(n,&m,&[v1]);
      let c=(n-2) as f64/((n*v1) as f64);
      let base=if e<c {e} else {c}; let r=l/base;
      let d = [b1,b2,n].iter().filter(|&&qq| v1 % qq != 0).count();
      cnt[d]+=1;
      if r<mins[d] { mins[d]=r; ats[d]=(n,b1,b2,v1); }
      v1+=1; }
  }}}
  println!("min ratio split by |D| = #{{q in M u {{n}} : q does NOT divide v1}}");
  for d in 0..4 { if cnt[d]>0 {
    println!("  |D|={}  instances={:<9} min ratio={:.6}  at (n,b1,b2,v1)={:?}",d,cnt[d],mins[d],ats[d]); } }
  println!();
  // the |D|=0 cases: what are they?
  println!("|D|=0 cases (lcm(M u {{n}}) divides v1), n<=20:");
  let mut shown=0;
  for n in 8..=20i128 { for b1 in 1..n { for b2 in (b1+1)..n {
    let m=[b1,b2]; let e=longest(n,&m,&[]);
    let mut v1=n; while v1<=6*n {
      if v1%b1==0 && v1%b2==0 && v1%n==0 {
        let l=longest(n,&m,&[v1]);
        let c=(n-2) as f64/((n*v1) as f64);
        let base=if e<c {e} else {c};
        if shown<8 { println!("   n={} M={{{},{}}} v1={} ratio={:.4}",n,b1,b2,v1,l/base); shown+=1; }
      }
      v1+=1; }
  }}}
}
