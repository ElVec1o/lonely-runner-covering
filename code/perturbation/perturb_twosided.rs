// Two-sided bound in the regime 2b >= n: no present multiple of b, so the component extends both
// ways from a/b.  ell >= (s/(n b))(1/j0 + 1/(n-1)).  Does it (i) never exceed the true ell, and
// (ii) make condition (c) non-vacuous, and by how much?
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
fn j0f(n:i128,b:i128)->i128{ let s=n-b; let mut j=if s<1 {1} else {s}; while g(j,b)!=1 { j+=1; } j }
fn main(){
  // (i) soundness of the two-sided bound
  let mut viol=0u64; let mut t=0u64;
  for n in 3..=200i128 { for b in 1..n { if 2*b < n || b<2 {continue;}
    let s=n-b; let jj=j0f(n,b); t+=1;
    let lb=q(s*((n-1)+jj), n*b*jj*(n-1));   // (s/(nb))(1/j0 + 1/(n-1))
    if cmp(lb, ell(n,&[b]))==std::cmp::Ordering::Greater { viol+=1;
      if viol<=5 { println!("  VIOLATION n={} b={}",n,b); } }
  }}
  println!("two-sided bound vs true ell, all 2b>=n, b>=2, n<=200: {} pairs, {} violations", t, viol);
  // (ii) new condition (c'):  s(n-2k)(j0 + n-1) > 2 k b j0 (n-1)
  let mut fires=0u64;
  for n in 3..=400i128 { for k in 1..(n+1)/2 { if 2*k>=n {continue;}
    for b in 2..n { if 2*b < n {continue;}
      let s=n-b; let jj=j0f(n,b);
      if s*(n-2*k)*(jj+n-1) > 2*k*b*jj*(n-1) { fires+=1; }
  }}}
  println!("condition (c') fires {} times (old (c): 0)", fires);
  // (iii) reach with (a) + (b) + (c')
  println!("\n{:>3} {:>3} {:>9} {:>9} {:>9}","k","n","C1 true","C2 old","C2' new");
  for k in 1..=3i128 { for n in [22i128,26,30,34,38,42] {
    if 2*k>=n {continue;}
    let cand:Vec<i128>=(1..n).collect(); let kk=k as usize;
    let mut idx:Vec<usize>=(0..kk).collect();
    let (mut tt,mut a1,mut a2,mut a3)=(0u64,0u64,0u64,0u64);
    loop{
      let m:Vec<i128>=idx.iter().map(|&i| cand[i]).collect();
      tt+=1; let e=ell(n,&m);
      let p1 = e.n*(n*(n-2*k)) > 2*k*e.d;
      let cert=|b:i128,newc:bool|->bool{
        if b==1 { return n>6*k; }
        let s=n-b; let jj=j0f(n,b);
        if 2*b<=n-1 { (2*s-jj)*(n-2*k) > 4*k*b*jj }
        else if newc { s*(n-2*k)*(jj+n-1) > 2*k*b*jj*(n-1) }
        else { s*(n-2*k) > 2*k*b*jj }
      };
      if p1 {a1+=1;}
      if m.iter().any(|&b| cert(b,false)) {a2+=1;}
      if m.iter().any(|&b| cert(b,true)) {a3+=1;}
      let mut p=kk; loop{ if p==0 {break;} p-=1; if idx[p]!=p+cand.len()-kk {break;} if p==0 {break;} }
      if idx[p]==p+cand.len()-kk {break;}
      idx[p]+=1; for z in (p+1)..kk { idx[z]=idx[z-1]+1; }
    }
    println!("{:>3} {:>3} {:>8.2}% {:>8.2}% {:>8.2}%",k,n,
      100.0*a1 as f64/tt as f64, 100.0*a2 as f64/tt as f64, 100.0*a3 as f64/tt as f64);
  }}
}
