// k3m13dec.rs -- DECIDE the lonely runner conjecture at k=3, m=13: every 13-element velocity set
// inside [1, 39].  This is height 3m rather than the dense window's 2m, at m = 13 velocities
// (14 runners), one past the literature frontier of m <= 12.
//
// k3m13.rs only SIEVES: it applies Tao's Lemma 5.1 and reports how many sets survive.  It reported
// 1,434,202 survivors out of C(39,13) = 8,122,425,444, so it decides nothing on its own.  This tool
// decides, and does so WITHOUT relying on the Lemma 5.1 implementation being correct.
//
// The criterion is exact and self-contained.  A velocity set V is lonely exactly when some time t
// has every velocity far from the integers:
//
//     V is lonely   <=>   there is a time t with  B(t) disjoint from V,
//
// where B(t) = { x in [1,39] : ||x t|| < 1/(m+1) } is the bad set of t.  So V is a counterexample
// exactly when V meets EVERY bad set, that is when V is a hitting set for the bad-set family.
//
// The family is finite and is enumerated exactly.  B(t) changes only at the breakpoints
// t = (j(m+1) +- 1)/(x(m+1)) for x <= 39, and is constant between consecutive breakpoints, so
// evaluating at every breakpoint AND at a mediant strictly between each consecutive pair sees every
// distinct bad set.  Mediants are REDUCED before use; an earlier tool in this project reported 1504
// spurious failures because unreduced mediants name a different rational.
//
// Soundness direction that matters: the enumeration may only ever UNDER-collect bad sets, never
// over-collect, because each set is computed from an explicit rational by the definition.  Missing a
// bad set can only make a lonely set look like a counterexample, so a report of ZERO counterexamples
// is safe, while a nonzero report needs each witness re-checked by hand.
//
// Cost: 8.12e9 sets, each tested against the bad-set family with early exit on the first disjoint
// bad set.  Bad sets are ordered cheapest-first (the t = 1/q times, whose bad sets are the multiples
// of q, reject the overwhelming majority immediately).  Bitmasks are u64 and the window is [1,39],
// so the shift never reaches 64; the u64 overflow that voided this project's m >= 32 bad-pair data
// cannot occur here, and the assertion below enforces that.
//
// Progress, ETA and periodic checkpoints to disk (atomic temp-then-rename), resumable with --resume.
//
//   rustc -O -o k3m13dec k3m13dec.rs && ./k3m13dec

use std::collections::HashSet;
use std::io::Write;

// parameterized so that controls exercise the SAME code path as the real run
static mut PM: usize = 13; static mut PV: usize = 39; static mut PT: u64 = 14;
#[inline] fn m_() -> usize { unsafe { PM } }
#[inline] fn v_() -> usize { unsafe { PV } }
#[inline] fn t_() -> u64 { unsafe { PT } }

fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }

/// bad set of the time num/den, as a bitmask over [1,V]
fn bad_mask(num: u64, den: u64) -> u64 {
    let mut m = 0u64;
    for x in 1..=v_() as u64 {
        let r = (x as u128 * num as u128 % den as u128) as u64;
        let d = r.min(den - r);
        if (d as u128) * (t_() as u128) < den as u128 { m |= 1u64 << x; }
    }
    m
}

/// every distinct bad set, from the breakpoints and the reduced mediants between them
fn bad_family() -> Vec<u64> {
    let mut pts: Vec<(u64, u64)> = vec![(0, 1), (1, 1)];
    for x in 1..=v_() as u64 {
        let den = x * t_();
        for j in 0..=x {
            for s in [-1i64, 1] {
                let ni = j as i64 * t_() as i64 + s;
                if ni < 0 || ni as u64 > den { continue; }
                let g = gcd(ni as u64, den).max(1);
                pts.push((ni as u64 / g, den / g));
            }
        }
    }
    pts.sort_by(|a, b| (a.0 as u128 * b.1 as u128).cmp(&(b.0 as u128 * a.1 as u128)));
    pts.dedup();
    let mut cand: Vec<(u64, u64)> = pts.clone();
    for w in pts.windows(2) {
        let (nu, de) = (w[0].0 + w[1].0, w[0].1 + w[1].1);
        let g = gcd(nu, de).max(1);
        cand.push((nu / g, de / g)); // REDUCED
    }
    let mut seen = HashSet::new();
    let mut fam: Vec<u64> = Vec::new();
    for (nu, de) in cand {
        if de == 0 { continue; }
        let b = bad_mask(nu % de, de);
        // An EMPTY bad set must be kept: it is a time at which nothing in the window is bad, so
        // it certifies every velocity set as lonely at once.  Discarding it was a bug that made the
        // tight set {1..m} look like a counterexample at threshold 1/(m+1); control 2 caught it.
        if seen.insert(b) { fam.push(b); }
    }
    // cheapest-first: the t = 1/q bad sets reject most sets immediately, so try small ones first
    fam.sort_by_key(|b| b.count_ones());
    fam
}

fn main() {
    let resume = std::env::args().any(|a| a == "--resume");
    let av: Vec<String> = std::env::args().collect();
    unsafe {
        if av.len() > 3 { PM = av[1].parse().unwrap(); PV = av[2].parse().unwrap(); PT = av[3].parse().unwrap(); }
    }
    assert!(v_() < 64, "window {} needs a wider mask than u64", v_());
    eprintln!("PARAMS m={} window=[1,{}] threshold=1/{}", m_(), v_(), t_());

    let fam = bad_family();
    eprintln!("distinct bad sets over [1,{}] at threshold 1/{}: {}", v_(), t_(), fam.len());
    let total: u64 = {
        let (mut n, mut r) = (1u128, 1u128);
        for i in 0..m_() { n *= (v_() - i) as u128; r *= (i + 1) as u128; }
        (n / r) as u64
    };
    eprintln!("sets to test: {}", total);

    let mut idx = vec![0usize; m_()];
    for i in 0..m_() { idx[i] = i + 1; }
    let mut tested: u64 = 0;
    let mut counter: Vec<Vec<usize>> = Vec::new();
    if resume {
        if let Ok(s) = std::fs::read_to_string("/tmp/k3m13dec.ckpt") {
            let v: Vec<usize> = s.trim().split(',').filter_map(|x| x.parse().ok()).collect();
            if v.len() == m_() + 1 { tested = v[0] as u64; for i in 0..m_() { idx[i] = v[i + 1]; } }
            eprintln!("resumed at tested={}", tested);
        }
    }
    let t0 = std::time::Instant::now();
    let mut last_ck = 0u64;

    loop {
        tested += 1;
        let mut mask = 0u64;
        for i in 0..m_() { mask |= 1u64 << idx[i]; }
        // lonely iff some bad set is disjoint from the velocity set
        let mut lonely = false;
        for &b in fam.iter() { if mask & b == 0 { lonely = true; break; } }
        if !lonely { counter.push(idx.clone()); }

        if tested % 200_000_000 == 0 {
            let el = t0.elapsed().as_secs_f64();
            let rate = (tested - last_ck.max(0)) as f64 / el.max(1e-9);
            let eta = if rate > 0.0 { (total - tested) as f64 / rate } else { 0.0 };
            eprintln!("[{:.0}s] tested {}/{} ({:.1}%) counterexamples {} | {:.0}M/s ETA {:.0}s",
                      el, tested, total, 100.0 * tested as f64 / total as f64,
                      counter.len(), rate / 1e6, eta);
            // atomic checkpoint: temp then rename
            let mut s = format!("{}", tested);
            for i in 0..m_() { s.push_str(&format!(",{}", idx[i])); }
            if std::fs::write("/tmp/k3m13dec.ckpt.tmp", &s).is_ok() {
                let _ = std::fs::rename("/tmp/k3m13dec.ckpt.tmp", "/tmp/k3m13dec.ckpt");
            }
        }

        // next combination in lexicographic order
        let mut i = m_();
        loop {
            if i == 0 {
                println!("DECIDED: tested {} | counterexamples {}", tested, counter.len());
                if counter.is_empty() {
                    println!("RESULT: every {}-element velocity set in [1,{}] is lonely (threshold 1/{}).", m_(), v_(), t_());
                } else {
                    println!("RESULT: {} candidate counterexamples, EACH NEEDS HAND CHECK:", counter.len());
                    for c in counter.iter().take(50) { println!("  C {:?}", c); }
                }
                let _ = std::io::stdout().flush();
                return;
            }
            i -= 1;
            if idx[i] < v_() - (m_() - 1 - i) {
                idx[i] += 1;
                for j in i + 1..m_() { idx[j] = idx[j - 1] + 1; }
                break;
            }
        }
    }
}
