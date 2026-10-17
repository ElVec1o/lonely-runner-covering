// Rigid residual of Case B, fixed-k perturbation of the extremal set {1,..,n-1}.
//
// V = ({1..n-1} \ M) u R,  M subset (n/2,n) with |M|=k,  R subset [n,inf) with |R|=k.
// |V| = n-1 speeds => n runners => floor 1/n.
// Pool P = M u {n}.  A replacement v blocks pool element b iff b | v.
// Residual = every element of P is blocked.  Since |P|=k+1 > k=|R|, some v blocks >= 2.
//
// This enumerates the TIGHT residual: exactly one replacement blocks a pair, the others one each.
// For each such V it searches for an exact witness time t = a/q certifying ML(V) >= 1/n:
//     for all v in V:  n * min(va mod q, q - (va mod q)) >= q.
// Integer arithmetic only. A witness is a proof; absence within QMAX is reported as OPEN.

use std::env;

fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn lcm(a: u64, b: u64) -> u64 { a / gcd(a, b) * b }

/// Smallest q <= qmax admitting a witness a/q for the floor 1/n. Returns (q,a) or None.
fn witness(speeds: &[u64], n: u64, qmax: u64) -> Option<(u64, u64)> {
    for q in 2..=qmax {
        // reduce speeds mod q once
        let red: Vec<u64> = speeds.iter().map(|v| v % q).collect();
        if red.iter().any(|&r| r == 0) { continue; } // that speed is blocked at every a/q
        for a in 1..q {
            if gcd(a, q) != 1 { continue; }
            let mut ok = true;
            for &r in &red {
                let x = (r * a) % q;
                let d = if x < q - x { x } else { q - x };
                if n * d < q { ok = false; break; }
            }
            if ok { return Some((q, a)); }
        }
    }
    None
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let nlo: u64 = args[1].parse().unwrap();
    let nhi: u64 = args[2].parse().unwrap();
    let k: usize = args[3].parse().unwrap();
    let bmul: u64 = args[4].parse().unwrap(); // replacement bound B = bmul * n
    let qmax: u64 = args[5].parse().unwrap();

    let mut total: u64 = 0;
    let mut open: u64 = 0;
    let mut qhist: std::collections::BTreeMap<u64, u64> = std::collections::BTreeMap::new();

    for n in nlo..=nhi {
        let b_bound = bmul * n;
        // candidate missing speeds: (n/2, n)
        let cand: Vec<u64> = (1..n).filter(|&b| 2 * b > n).collect();
        if (cand.len() as usize) < k { continue; }
        // all k-subsets M
        let mut idx: Vec<usize> = (0..k).collect();
        loop {
            let m: Vec<u64> = idx.iter().map(|&i| cand[i]).collect();
            let mut pool = m.clone();
            pool.push(n);
            // choose the double-blocked pair {pool[i], pool[j]}
            for i in 0..pool.len() {
                for j in (i + 1)..pool.len() {
                    let l = lcm(pool[i], pool[j]);
                    if l > b_bound { continue; }
                    let singles: Vec<u64> = (0..pool.len())
                        .filter(|&x| x != i && x != j).map(|x| pool[x]).collect();
                    // cofactors for the double blocker
                    let mut c0 = 1u64;
                    while c0 * l <= b_bound {
                        let v0 = c0 * l;
                        if v0 < n { c0 += 1; continue; }
                        // cartesian product of cofactors for singletons
                        let ranges: Vec<Vec<u64>> = singles.iter().map(|&b| {
                            (1..=(b_bound / b)).map(|c| c * b).filter(|&v| v >= n).collect()
                        }).collect();
                        let mut counters = vec![0usize; ranges.len()];
                        if ranges.iter().any(|r| r.is_empty()) { c0 += 1; continue; }
                        loop {
                            let mut r: Vec<u64> = vec![v0];
                            for (t, rg) in ranges.iter().enumerate() { r.push(rg[counters[t]]); }
                            r.sort(); r.dedup();
                            if r.len() == k {
                                // build V
                                let mut v: Vec<u64> =
                                    (1..n).filter(|x| !m.contains(x)).collect();
                                v.extend(r.iter());
                                total += 1;
                                match witness(&v, n, qmax) {
                                    Some((qw, _aw)) => { *qhist.entry(qw).or_insert(0) += 1; }
                                    None => {
                                        open += 1;
                                        if open <= 20 {
                                            let rr: Vec<u64> = {
                                                let mut z: Vec<u64> = vec![v0];
                                                for (t, rg) in ranges.iter().enumerate() { z.push(rg[counters[t]]); }
                                                z.sort(); z.dedup(); z
                                            };
                                            println!("OPEN n={} M={:?} R={:?}", n, m, rr);
                                        }
                                    }
                                }
                            }
                            // advance counters
                            let mut t = 0;
                            loop {
                                if t == counters.len() { break; }
                                counters[t] += 1;
                                if counters[t] < ranges[t].len() { break; }
                                counters[t] = 0; t += 1;
                            }
                            if t == counters.len() { break; }
                        }
                        c0 += 1;
                    }
                }
            }
            // next k-subset
            let mut p = k;
            loop {
                if p == 0 { break; }
                p -= 1;
                if idx[p] != p + cand.len() - k { break; }
                if p == 0 { break; }
            }
            if idx[p] == p + cand.len() - k { break; }
            idx[p] += 1;
            for z in (p + 1)..k { idx[z] = idx[z - 1] + 1; }
        }
    }
    println!("--- total={} open={} ---", total, open);
    let mut acc = 0u64;
    for (q, c) in qhist.iter() {
        acc += c;
        if *c > 0 && (*q <= 12 || acc * 100 / total.max(1) > 99) {
            println!("q={} count={} cum={:.4}", q, c, acc as f64 / total as f64);
        }
    }
}
