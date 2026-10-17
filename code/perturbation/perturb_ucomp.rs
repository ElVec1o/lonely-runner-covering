// U(n,M): the region left uncovered by the baseline [n-1] after deleting M, |M|=k.
// Exact rational arithmetic. Computes the LARGEST component length ell(n,M) and compares to
// the uniform covering threshold  T(n,k) = 2k / (n(n-2k)).
// ell > T  ==>  ([n-1]\M) u R is lonely for EVERY R of size k with all speeds >= n.
//
// Reports min over M of ell, and the exact ratio ell / T for the worst M.

use std::env;

#[derive(Clone, Copy, Debug)]
struct Q { n: i128, d: i128 } // d > 0, reduced

fn g(a: i128, b: i128) -> i128 { if b == 0 { a.abs() } else { g(b, a % b) } }
fn q(n: i128, d: i128) -> Q { let s = if d < 0 { -1 } else { 1 }; let (n,d)=(n*s,d*s);
    let k = g(n.abs(), d); if k == 0 { Q{n:0,d:1} } else { Q{n:n/k, d:d/k} } }
fn cmp(a: Q, b: Q) -> std::cmp::Ordering { (a.n * b.d).cmp(&(b.n * a.d)) }
fn sub(a: Q, b: Q) -> Q { q(a.n * b.d - b.n * a.d, a.d * b.d) }

/// Largest component of U(n, M) as an exact rational, plus its left endpoint.
fn max_component(n: i128, m: &[i128]) -> (Q, Q, i64, f64) {
    // bad open intervals ((i*n - 1)/(j*n), (i*n + 1)/(j*n)) for present j, i = 0..j
    let mut iv: Vec<(Q, Q)> = Vec::new();
    for j in 1..n {
        if m.contains(&j) { continue; }
        for i in 0..=j {
            iv.push((q(i * n - 1, j * n), q(i * n + 1, j * n)));
        }
    }
    iv.sort_by(|a, b| cmp(a.0, b.0));
    // sweep over [0,1]; U is the complement. Track max gap.
    let mut best = Q { n: 0, d: 1 };
    let mut bestl = Q { n: 0, d: 1 };
    let mut ncomp: i64 = 0;
    let mut tot: f64 = 0.0;
    let mut cur_r = q(0, 1); // right edge of the covered prefix; start at 0
    for &(l, r) in iv.iter() {
        if cmp(l, cur_r) == std::cmp::Ordering::Greater {
            let gap = sub(l, cur_r);
            ncomp += 1; tot += gap.n as f64 / gap.d as f64;
            if cmp(gap, best) == std::cmp::Ordering::Greater { best = gap; bestl = cur_r; }
        }
        if cmp(r, cur_r) == std::cmp::Ordering::Greater { cur_r = r; }
    }
    let one = q(1, 1);
    if cmp(one, cur_r) == std::cmp::Ordering::Greater {
        let gap = sub(one, cur_r);
        ncomp += 1; tot += gap.n as f64 / gap.d as f64;
        if cmp(gap, best) == std::cmp::Ordering::Greater { best = gap; bestl = cur_r; }
    }
    (best, bestl, ncomp, tot)
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let nlo: i128 = a[1].parse().unwrap();
    let nhi: i128 = a[2].parse().unwrap();
    let k: usize = a[3].parse().unwrap();

    for n in nlo..=nhi {
        if n as i128 - 2 * k as i128 <= 0 { continue; }
        // threshold T = 2k / (n(n-2k)); compare ell > T  <=>  ell.n * n*(n-2k) > 2k * ell.d
        let tn = 2 * k as i128;
        let td = n * (n - 2 * k as i128);
        let mut worst: Option<(Q, Vec<i128>)> = None;
        let mut fails = 0u64;
        let mut total = 0u64;
        // all k-subsets of [1, n-1]
        let mut idx: Vec<usize> = (0..k).collect();
        let cand: Vec<i128> = (1..n).collect();
        loop {
            let m: Vec<i128> = idx.iter().map(|&i| cand[i]).collect();
            let (ell, _, _np, _l) = max_component(n, &m);
            total += 1;
            // ell > T ?
            if ell.n * td <= tn * ell.d { fails += 1; }
            match &worst {
                None => worst = Some((ell, m.clone())),
                Some((w, _)) => if cmp(ell, *w) == std::cmp::Ordering::Less {
                    worst = Some((ell, m.clone()))
                },
            }
            let mut p = k;
            loop { if p == 0 { break; } p -= 1;
                   if idx[p] != p + cand.len() - k { break; }
                   if p == 0 { break; } }
            if idx[p] == p + cand.len() - k { break; }
            idx[p] += 1;
            for z in (p + 1)..k { idx[z] = idx[z - 1] + 1; }
        }
        let (w, wm) = worst.unwrap();
        let (_e, _b, npc, ltot) = max_component(n, &wm);
        let ellf = w.n as f64 / w.d as f64;
        let vbound = 2.0 * k as f64 / (ellf * (n - 2 * k as i128) as f64);
        let ratio = (w.n as f64 / w.d as f64) / (tn as f64 / td as f64);
        println!("n={} k={} worstM={:?} ell={}/{} ell*n^2={:.4} ncomp={} L={:.6} L*n={:.4} minRbound={:.1} bnd/n={:.2} ellT={:.3} fails={}/{}",
                 n, k, wm, w.n, w.d, ellf*(n*n) as f64, npc, ltot, ltot*n as f64, vbound, vbound/n as f64, ratio, fails, total);
    }
}
