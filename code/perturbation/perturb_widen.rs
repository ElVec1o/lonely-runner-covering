// Widening the unconditional corollary.  Three nested conditions, all EXHAUSTIVE over all k-subsets:
//   (C1) the criterion itself, using the TRUE ell           -> the ceiling of this method
//   (C2) the j0-explicit condition from Prop 4.1            -> proposed new corollary
//   (C3) the current closed form 8kb <= n, n > 6k-2         -> what the paper has now
// C3 => C2 => C1 should hold.  Report the reach of each.
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
fn j0(n:i128,b:i128)->i128{ let s=n-b; let mut j=if s<1 {1} else {s}; while g(j,b)!=1 { j+=1; } j }
/// does b certify M via the j0-explicit condition?
fn c2(n:i128,k:i128,b:i128)->bool{
  if b==1 { return n>6*k; }                       // the b=1 case, ell >= 1/(2n)
  let s=n-b; let jj=j0(n,b);
  if 2*b<=n-1 { (2*s-jj)*(n-2*k) > 4*k*b*jj }     // ell >= (2s-j0)/(2 n b j0)
  else        { s*(n-2*k) > 2*k*b*jj }            // ell >= s/(n b j0)
}
fn c3(n:i128,k:i128,b:i128)->bool{ (b==1 && n>6*k) || (b>=2 && 8*k*b<=n && n>6*k-2) }
fn main(){
  println!("{:>3} {:>3} {:>9} {:>9} {:>9}   (exhaustive over all k-subsets)","k","n","C1 true","C2 j0","C3 now");
  let mut viol=0u64;
  for k in 1..=3i128 { for n in [22i128,26,30,34,38,42] {
    if 2*k>=n {continue;}
    let cand:Vec<i128>=(1..n).collect(); let kk=k as usize;
    let mut idx:Vec<usize>=(0..kk).collect();
    let (mut t,mut a1,mut a2,mut a3)=(0u64,0u64,0u64,0u64);
    loop{
      let m:Vec<i128>=idx.iter().map(|&i| cand[i]).collect();
      t+=1;
      let e=ell(n,&m);
      let p1 = e.n*(n*(n-2*k)) > 2*k*e.d;
      let p2 = m.iter().any(|&b| c2(n,k,b));
      let p3 = m.iter().any(|&b| c3(n,k,b));
      if p1 {a1+=1;} if p2 {a2+=1;} if p3 {a3+=1;}
      if (p3 && !p2) || (p2 && !p1) { viol+=1; }
      let mut p=kk; loop{ if p==0 {break;} p-=1; if idx[p]!=p+cand.len()-kk {break;} if p==0 {break;} }
      if idx[p]==p+cand.len()-kk {break;}
      idx[p]+=1; for z in (p+1)..kk { idx[z]=idx[z-1]+1; }
    }
    println!("{:>3} {:>3} {:>8.2}% {:>8.2}% {:>8.2}%", k, n,
             100.0*a1 as f64/t as f64, 100.0*a2 as f64/t as f64, 100.0*a3 as f64/t as f64);
  }}
  println!("\nimplication failures (C3=>C2 and C2=>C1): {}", viol);
}
