// Section 5 (|A| = 4) falsification.
// Exact: 4 level-0 units d mod N=7^(m+1): exists j in 1..5, k in 0..6 with q((1+7^m k) j d_i) notin {0,6}.
// Model (chain): q_1=a, q_{j+1}=q_j+a+eps_j. F1/F2/F3 arc claims and Z7 finishing lemmas.
fn q(x: u64, m: u32) -> u64 { let n = 7u64.pow(m+1); (x % n) / 7u64.pow(m) }
fn good_exact(d: &[u64], m: u32) -> bool {
    let n = 7u64.pow(m+1); let p = 7u64.pow(m);
    for j in 1..=5u64 { for k in 0..7u64 { let lam = ((1 + p*k) * j) % n;
        if d.iter().all(|&x| { let v = q(lam*x % n, m); v != 0 && v != 6 }) { return true; } } }
    false
}
fn qs(a: u64, eps: u32) -> [u64;6] { let mut v=[0u64;6]; v[1]=a%7; for j in 1..5 { v[j+1]=(v[j]+a+((eps>>(j-1))&1) as u64)%7; } v }
// arc: all values v_i - t in {0..len-1} for some t
fn arc(vals: &[u64], len: u64) -> bool { (0..7).any(|t| vals.iter().all(|&v| (v+7-t)%7 < len)) }
fn main() {
    // exact m = 1 exhaustive (multisets), m = 2 exhaustive (multisets)
    for m in 1..=2u32 {
        let n = 7u64.pow(m+1); let units: Vec<u64> = (1..n).filter(|x| x%7!=0).collect(); let u=units.len();
        let (mut tot, mut bad) = (0u64, 0u64);
        for a in 0..u { for b in a..u { for c in b..u { for e in c..u {
            tot+=1; if !good_exact(&[units[a],units[b],units[c],units[e]], m) { bad+=1; if bad<4 {println!("m={} BAD {:?}",m,[units[a],units[b],units[c],units[e]]);} }
        }}}}
        println!("exact m={}: {} multisets, {} failures", m, tot, bad);
    }
    // F1: 4 elements one class: exists j<=5 arc(q_j,5)
    let mut f=[0u64;3]; let mut tot=[0u64;3];
    for a in 0..7u64.pow(4) { for e in 0..(1u64<<16) {
        let el: Vec<[u64;6]> = (0..4).map(|i| qs((a/7u64.pow(i))%7, ((e>>(4*i))&15) as u32)).collect();
        tot[0]+=1; if !(1..=5).any(|j| arc(&el.iter().map(|x|x[j]).collect::<Vec<_>>(),5)) { f[0]+=1; }
    }}
    for a in 0..343u64 { for e in 0..(1u64<<12) {
        let el: Vec<[u64;6]> = (0..3).map(|i| qs((a/7u64.pow(i))%7, ((e>>(4*i))&15) as u32)).collect();
        tot[1]+=1; if !(1..=5).any(|j| arc(&el.iter().map(|x|x[j]).collect::<Vec<_>>(),4)) { f[1]+=1; }
    }}
    for a in 0..49u64 { for e in 0..(1u64<<8) {
        let el: Vec<[u64;6]> = (0..2).map(|i| qs((a/7u64.pow(i))%7, ((e>>(4*i))&15) as u32)).collect();
        tot[2]+=1; if !(1..=5).any(|j| arc(&el.iter().map(|x|x[j]).collect::<Vec<_>>(),2)) { f[2]+=1; }
    }}
    println!("F1 (4,len5): {} / {} fail; F2 (3,len4): {} / {} fail; F3 (2,len2): {} / {} fail", f[0],tot[0],f[1],tot[1],f[2],tot[2]);
    // NC: F1 with j<=2 only, F3 with len 1
    let mut nc=0; for a in 0..49u64 { for e in 0..(1u64<<8) {
        let el: Vec<[u64;6]> = (0..2).map(|i| qs((a/7u64.pow(i))%7, ((e>>(4*i))&15) as u32)).collect();
        if !(1..=5).any(|j| arc(&el.iter().map(|x|x[j]).collect::<Vec<_>>(),1)) { nc+=1; } }}
    println!("NC F3 len1: {} fail", nc);
    // Z2: t, w, rho in {2,4}: kappa in {1-t,2-t}: w+kappa*rho notin {0,6}
    let g=|v:u64| v!=0 && v!=6;
    let mut z=0; for t in 0..7u64 { for w in 0..7u64 { for rho in [2u64,4] {
        if ![1u64,2].iter().any(|&o| { let kap=(o+7-t)%7; g((w+kap*rho)%7) }) { z+=1; } }}}
    println!("Z2 fails {}", z);
    let mut z=0; for t in 0..7u64 { for w1 in 0..7u64 { for w2 in 0..7u64 { for r1 in [2u64,4] { for r2 in [2u64,4] {
        if ![1u64,2,3,4].iter().any(|&o| { let kap=(o+7-t)%7; g((w1+kap*r1)%7) && g((w2+kap*r2)%7) }) { z+=1; } }}}}}
    println!("Z3 fails {}", z);
    let mut z=0; for t in 0..7u64 { for w1 in 0..7u64 { for w2 in 0..7u64 { for r1 in [2u64,4] { for r2 in [2u64,4] {
        if ![1u64,2,3].iter().any(|&o| { let kap=(o+7-t)%7; g((w1+kap*r1)%7) && g((w2+kap*r2)%7) }) { z+=1; } }}}}}
    println!("NC Z3 with 3 kappas: {} fail", z);
}
