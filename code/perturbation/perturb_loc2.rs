// Where does the surviving component sit after the adversary removes B_{v1}?
// usage: loc2 n b1 b2 v1
use std::env;
#[derive(Clone,Copy,PartialEq)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }
fn fl(a:Q)->i128{ a.n.div_euclid(a.d) }
fn simplest(lo:Q,hi:Q)->Q{
  let c=if lo.n.rem_euclid(lo.d)==0 {lo.n/lo.d} else {fl(lo)+1};
  if cmp(q(c,1),hi)!=std::cmp::Ordering::Greater { return q(c,1); }
  let a=fl(lo);
  let r=simplest(q(hi.d,hi.n-a*hi.d), q(lo.d,lo.n-a*lo.d));
  q(a*r.n+r.d, r.n)
}
fn main(){
  let av:Vec<String>=env::args().collect();
  let n:i128=av[1].parse().unwrap();
  let b1:i128=av[2].parse().unwrap(); let b2:i128=av[3].parse().unwrap();
  let v1:i128=av[4].parse().unwrap();
  let mut sp:Vec<i128>=(1..n).filter(|&x| x!=b1 && x!=b2).collect(); sp.push(v1);
  let mut iv:Vec<(Q,Q)>=Vec::new();
  for &j in &sp { for i in 0..=j { iv.push((q(i*n-1,j*n), q(i*n+1,j*n))); } }
  iv.sort_by(|x,y| cmp(x.0,y.0));
  let mut comps:Vec<(Q,Q,Q)>=Vec::new(); let mut cur=q(0,1);
  for &(l,r) in iv.iter(){
    if cmp(l,cur)!=std::cmp::Ordering::Less { comps.push((sub(l,cur),cur,l)); }
    if cmp(r,cur)==std::cmp::Ordering::Greater {cur=r;} }
  let one=q(1,1);
  if cmp(one,cur)!=std::cmp::Ordering::Less { comps.push((sub(one,cur),cur,one)); }
  comps.sort_by(|a,b| cmp(b.0,a.0));
  println!("n={} M={{{},{}}} v1={}", n,b1,b2,v1);
  for (i,&(ln,lo,hi)) in comps.iter().take(3).enumerate(){
    let s=simplest(lo,hi);
    // which base point family? denominator n, b1, b2, or other
    let fam = if s.d==n {"a/n"} else if s.d==b1 {"a/b1"} else if s.d==b2 {"a/b2"}
              else if n % s.d==0 {"divisor of n"}
              else if b1 % s.d==0 || b2 % s.d==0 {"divisor of b"} else {"other"};
    println!("  #{} len*n(n-1)={:.4}  simplest inside = {}/{}   family: {}",
             i+1,(ln.n as f64/ln.d as f64)*(n*(n-1)) as f64, s.n,s.d,fam);
  }
}
