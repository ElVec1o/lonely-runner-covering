// Falsification test for the Component Lemma:
//   if M contains some j with gcd(j,n)=1, then U(n,M) has a component of length >= 1/(n(n-1)).
// Exhaustive over all M of size k. Reports any violation, plus the min over each class.
use std::env;
#[derive(Clone, Copy)] struct Q { n: i128, d: i128 }
fn g(a: i128, b: i128) -> i128 { if b == 0 { a.abs() } else { g(b, a % b) } }
fn q(n: i128, d: i128) -> Q { let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
    let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a: Q, b: Q) -> std::cmp::Ordering { (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a: Q, b: Q) -> Q { q(a.n*b.d - b.n*a.d, a.d*b.d) }
/// Sweep note: a zero-length gap is an isolated point of the region, not an absence of one.
/// It is recorded, so that "no component" and "no positive-length component" stay distinct.
fn maxcomp(n: i128, m: &[i128]) -> Q {
    let mut iv: Vec<(Q,Q)> = Vec::new();
    for j in 1..n { if m.contains(&j) { continue; }
        for i in 0..=j { iv.push((q(i*n-1, j*n), q(i*n+1, j*n))); } }
    iv.sort_by(|a,b| cmp(a.0,b.0));
    let mut best = Q{n:0,d:1}; let mut cur = q(0,1);
    for &(l,r) in iv.iter() {
        if cmp(l,cur)!=std::cmp::Ordering::Less { let gp=sub(l,cur);
            if cmp(gp,best)==std::cmp::Ordering::Greater { best=gp; } }
        if cmp(r,cur)==std::cmp::Ordering::Greater { cur=r; } }
    let one=q(1,1);
    if cmp(one,cur)!=std::cmp::Ordering::Less { let gp=sub(one,cur);
        if cmp(gp,best)==std::cmp::Ordering::Greater { best=gp; } }
    best
}
fn main(){
    let a: Vec<String>=env::args().collect();
    let nlo: i128=a[1].parse().unwrap(); let nhi: i128=a[2].parse().unwrap();
    let k: usize=a[3].parse().unwrap();
    let mut viol=0u64; let mut totu=0u64;
    for n in nlo..=nhi {
        let cand: Vec<i128>=(1..n).collect();
        if cand.len()<k { continue; }
        let mut minu: Option<(Q,Vec<i128>)>=None;   // M containing a unit
        let mut minn: Option<(Q,Vec<i128>)>=None;   // M with no unit
        let mut idx: Vec<usize>=(0..k).collect();
        loop {
            let m: Vec<i128>=idx.iter().map(|&i| cand[i]).collect();
            let hasunit = m.iter().any(|&j| g(j,n)==1);
            let e = maxcomp(n,&m);
            if hasunit {
                totu+=1;
                // check e >= 1/(n(n-1)) : e.n * n*(n-1) >= e.d
                if e.n * (n*(n-1)) < e.d { viol+=1;
                    println!("VIOLATION n={} M={:?} ell={}/{}", n, m, e.n, e.d); }
                match &minu { None=>minu=Some((e,m.clone())),
                    Some((w,_))=>if cmp(e,*w)==std::cmp::Ordering::Less {minu=Some((e,m.clone()))} }
            } else {
                match &minn { None=>minn=Some((e,m.clone())),
                    Some((w,_))=>if cmp(e,*w)==std::cmp::Ordering::Less {minn=Some((e,m.clone()))} }
            }
            let mut p=k; loop { if p==0 {break;} p-=1;
                if idx[p]!=p+cand.len()-k {break;} if p==0 {break;} }
            if idx[p]==p+cand.len()-k {break;}
            idx[p]+=1; for z in (p+1)..k { idx[z]=idx[z-1]+1; }
        }
        let su=match &minu { Some((w,m))=>format!("{}/{} (x n(n-1) = {:.4}) M={:?}", w.n,w.d,
            (w.n as f64/w.d as f64)*(n*(n-1)) as f64, m), None=>"none".into() };
        let sn=match &minn { Some((w,m))=>format!("{:.4} M={:?}",
            (w.n as f64/w.d as f64)*(n*(n-1)) as f64, m), None=>"none".into() };
        println!("n={:<4} k={} unitM_min={}   |  nonunitM_min={}", n,k,su,sn);
    }
    println!("=== unit-class instances checked: {}  VIOLATIONS: {} ===", totu, viol);
}
