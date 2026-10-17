// Locate the largest components of U(n,M) and identify the simplest rational inside each.
use std::env;
#[derive(Clone, Copy, PartialEq)] struct Q { n: i128, d: i128 }
fn g(a: i128, b: i128) -> i128 { if b==0 {a.abs()} else {g(b, a%b)} }
fn q(n: i128, d: i128) -> Q { let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
    let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a: Q, b: Q) -> std::cmp::Ordering { (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a: Q, b: Q) -> Q { q(a.n*b.d - b.n*a.d, a.d*b.d) }
fn fl(a: Q) -> i128 { a.n.div_euclid(a.d) }
/// smallest-denominator rational in [lo,hi]
fn simplest(lo: Q, hi: Q) -> Q {
    let c = if lo.n.rem_euclid(lo.d)==0 { lo.n/lo.d } else { fl(lo)+1 };
    if cmp(q(c,1), hi) != std::cmp::Ordering::Greater { return q(c,1); }
    let a = fl(lo);
    let lo2 = q(hi.d, hi.n - a*hi.d);
    let hi2 = q(lo.d, lo.n - a*lo.d);
    let r = simplest(lo2, hi2);
    q(a*r.n + r.d, r.n)
}
fn main(){
    let av: Vec<String>=env::args().collect();
    let n: i128 = av[1].parse().unwrap();
    let m: Vec<i128> = av[2..].iter().map(|s| s.parse().unwrap()).collect();
    let mut iv: Vec<(Q,Q)> = Vec::new();
    for j in 1..n { if m.contains(&j) { continue; }
        for i in 0..=j { iv.push((q(i*n-1,j*n), q(i*n+1,j*n))); } }
    iv.sort_by(|a,b| cmp(a.0,b.0));
    let mut comps: Vec<(Q,Q,Q)> = Vec::new(); // (len, lo, hi)
    let mut cur = q(0,1);
    for &(l,r) in iv.iter() {
        if cmp(l,cur)!=std::cmp::Ordering::Less { comps.push((sub(l,cur), cur, l)); }
        if cmp(r,cur)==std::cmp::Ordering::Greater { cur=r; } }
    let one=q(1,1);
    if cmp(one,cur)!=std::cmp::Ordering::Less { comps.push((sub(one,cur),cur,one)); }
    comps.sort_by(|a,b| cmp(b.0,a.0));
    println!("n={} M={:?}   1/(n(n-1)) = 1/{}", n, m, n*(n-1));
    for (i,&(ln,lo,hi)) in comps.iter().take(4).enumerate() {
        let s = simplest(lo,hi);
        println!("  #{} len={}/{}  x n(n-1) = {:.4}   [{}/{}, {}/{}]   simplest inside = {}/{}",
                 i+1, ln.n, ln.d, (ln.n as f64/ln.d as f64)*(n*(n-1)) as f64,
                 lo.n,lo.d,hi.n,hi.d, s.n,s.d);
    }
}
