// Exact integer check of the dense-window statement and of the proof steps of Theorem D.
// Usage: dense_check controls | window M H | steps M
// ML is computed only on the controls; elsewhere the certificate is a witness time c/s with
// min_i min(r_i, s-r_i) * (m+1) >= s, r_i = v_i*c mod s (exact integers).
use std::env;

fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }

// exact ML of a set: max over candidate times c/s, s = v_i+v_j, of min_i dist(v_i c/s, Z); fraction (num,den)
fn ml(v: &[u64]) -> (u64, u64) {
    let mut best = (0u64, 1u64);
    for i in 0..v.len() { for j in i..v.len() {
        let s = v[i] + v[j];
        for c in 1..s {
            let mut mn = s; // numerator of the gap, denominator s
            for &x in v { let r = (x * c) % s; let d = r.min(s - r); if d < mn { mn = d; } }
            // compare mn/s with best
            if mn * best.1 > best.0 * s { let g = gcd(mn, s); best = (mn / g, s / g); }
        }
    }}
    best
}

fn masks(m: u32, h: u32) -> Vec<u32> {
    let mut all: Vec<u32> = Vec::new();
    for s in 2..=(2 * h) as u64 { for c in 1..s {
        let mut mk = 0u32;
        for x in 1..=h as u64 {
            let r = (x * c) % s; let d = r.min(s - r);
            if d * (m as u64 + 1) < s { mk |= 1 << (x - 1); }
        }
        all.push(mk);
    }}
    all.sort_by_key(|k| (k.count_ones(), *k)); all.dedup();
    // keep inclusion-minimal masks (a superset mask is never needed)
    let mut keep: Vec<u32> = Vec::new();
    for &k in &all { if !keep.iter().any(|&p| p & k == p) { keep.push(k); } }
    keep
}

fn main() {
    let a: Vec<String> = env::args().collect();
    match a[1].as_str() {
        "controls" => {
            for v in [vec![1u64,2,3,4,5], vec![1,3,4,7], vec![1,2,3], vec![1,2], vec![1,3,4,7,10], vec![1,2,3,4,5,6]] {
                let (n, d) = ml(&v); println!("ML{:?} = {}/{}  (floor 1/{})", v, n, d, v.len() + 1);
            }
            // negative control for the window search: height-H masks must produce a failing set for a
            // too-large floor, e.g. m=4,H=8 with the floor 1/4 instead of 1/5 (ML(1,3,4,7)=1/5 < 1/4)
            let mk = masks(3, 8); // m=3 means floor 1/4
            let v: u32 = (1<<0)|(1<<2)|(1<<3)|(1<<6);
            println!("control: {{1,3,4,7}} has a witness for floor 1/4? {}", mk.iter().any(|&k| k & v == 0));
        }
        "window" => {
            let m: u32 = a[2].parse().unwrap(); let h: u32 = a[3].parse().unwrap();
            let mk = masks(m, h);
            let (mut tot, mut fail) = (0u64, 0u64); let mut first: Vec<u32> = vec![];
            let mut exact_m = 0u64;
            for v in 1u32..(1u32 << h) {
                let pc = v.count_ones(); if pc > m { continue; }
                tot += 1; if pc == m { exact_m += 1; }
                if !mk.iter().any(|&k| k & v == 0) { fail += 1; if first.len() < 5 { first.push(v); } }
            }
            println!("m={} H={} masks={} sets(size<=m)={} sets(size=m)={} failures={}", m, h, mk.len(), tot, exact_m, fail);
            for v in first { let s: Vec<u32> = (1..=h).filter(|x| v >> (x-1) & 1 == 1).collect(); println!("  no witness: {:?}", s); }
        }
        "steps" => {
            let m: u32 = a[2].parse().unwrap(); let h = 2 * m; let n = 2 * m as u64 + 1;
            let prime = (2..n).all(|d| n % d != 0);
            let (mut c1, mut c2, mut c3) = (0u64, 0u64, 0u64);
            let (mut c3pair, mut c3nopair, mut modn_fail) = (0u64, 0u64, 0u64);
            let mut ex: Option<Vec<u64>> = None;
            for v in 1u32..(1u32 << h) {
                if v.count_ones() > m { continue; }
                let set: Vec<u64> = (1..=h as u64).filter(|x| v >> (x - 1) & 1 == 1).collect();
                let ok = |s: u64, c: u64| set.iter().all(|&x| { let r = (x*c)%s; r.min(s-r) * (m as u64 + 1) >= s });
                if v & 1 == 0 { c1 += 1; assert!(ok(2*m as u64 + 2, 1), "case1 witness fails"); continue; }
                if let Some(q) = (2..=m as u64 + 1).find(|q| set.iter().all(|x| x % q != 0)) {
                    c2 += 1; assert!(ok(q, 1), "case2 witness fails"); continue; }
                c3 += 1;
                let has = |x: u64| set.contains(&x);
                assert!(has(m as u64 + 1), "m+1 not forced");
                assert!(has(m as u64) || has(2*m as u64), "m or 2m not forced");
                if has(m as u64) || has(2*m as u64) { c3pair += 1; } else { c3nopair += 1; }
                // modulus-N witness: some c in [1,N-1] with ok(N,c)
                if !(1..n).any(|c| ok(n, c)) { modn_fail += 1; if ex.as_ref().map_or(true, |e| set.len() < e.len()) { ex = Some(set.clone()); } }
            }
            println!("m={} N={} prime={} case1={} case2={} case3={} (pair present {}, absent {}) case3 families with NO witness c/N: {}",
                m, n, prime, c1, c2, c3, c3pair, c3nopair, modn_fail);
            if let Some(e) = ex { println!("  smallest case-3 family without a witness at modulus N: {:?}", e); }
        }
        _ => {}
    }
}
