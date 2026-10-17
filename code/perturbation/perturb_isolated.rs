// The residual region U(n,M) \ B_{v1} INCLUDING isolated points.
// Regenerates the k=1 counterexample to the unrestricted form of the residual conjecture:
// for n = 2 mod 6, M = {n-2}, v1 = 2(n-2) the residual is a nonempty finite set of points.
// usage: perturb_isolated n v1 b1 [b2 ...]
use std::env;
#[derive(Clone,Copy,PartialEq)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }
fn main(){
  let av:Vec<String>=env::args().collect();
  let n:i128=av[1].parse().unwrap();
  let v1:i128=av[2].parse().unwrap();
  let m:Vec<i128>=av[3..].iter().map(|s| s.parse().unwrap()).collect();
  let mut sp:Vec<i128>=(1..n).filter(|x| !m.contains(x)).collect();
  if v1>0 { sp.push(v1); }
  let mut iv:Vec<(Q,Q)>=Vec::new();
  for &j in &sp { for i in 0..=j { iv.push((q(i*n-1,j*n), q(i*n+1,j*n))); } }
  iv.sort_by(|x,y| cmp(x.0,y.0));
  let mut pts:Vec<Q>=Vec::new(); let mut ivs:Vec<(Q,Q)>=Vec::new();
  let mut cur=q(0,1);
  for &(l,r) in iv.iter(){
    if cmp(l,cur)!=std::cmp::Ordering::Less {
      let gp=sub(l,cur);
      if gp.n==0 { pts.push(cur); } else { ivs.push((cur,l)); } }
    if cmp(r,cur)==std::cmp::Ordering::Greater {cur=r;} }
  let one=q(1,1);
  if cmp(one,cur)!=std::cmp::Ordering::Less {
    let gp=sub(one,cur);
    if gp.n==0 { pts.push(cur); } else { ivs.push((cur,one)); } }
  println!("n={} M={:?} v1={}", n, m, v1);
  println!("  positive-length components : {}", ivs.len());
  for (a,b) in ivs.iter().take(6) { println!("      [{}/{}, {}/{}]", a.n,a.d,b.n,b.d); }
  print!("  isolated points ({})        : ", pts.len());
  for p in pts.iter().take(12) { print!("{}/{} ", p.n,p.d); }
  println!();
  println!("  VERDICT: {}", if ivs.is_empty() && pts.is_empty() { "EMPTY" }
                            else if ivs.is_empty() { "NONEMPTY, no positive-length component" }
                            else { "has a positive-length component" });
}
