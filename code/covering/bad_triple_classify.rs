// trip3class -- exact classification of bad sets of size 2 and 3 inside [1,2m], tested against
// the exhaustive breakpoint sweep (exhaustive over all real times, exact integer arithmetic).
//
// Threshold T = m+1: x is bad at p/q iff min(r, q-r)*T < q, r = xp mod q.
//
// PREDICTED exact bad sets (derived from the rank-2 lattice argument):
//   size 1: {1}, {m+1}
//   size 2: CMP {a, q-a}, q in {2m+1, 2m+2}, gcd(a,q)=1, both in window
//           DBL {a, 2a}, a <= m, and ( 3a > 2m  or  xs(a,m) <= 3(m+1-a) )
//               where xs(a,m) = min{ x in [2m-a+1, 2m] : gcd(x,a) = 1 }
//   size 3: SUM {a,b,a+b}, a<b, b != 2a, a+b <= 2m, gcd(a,b)=1, and one of
//             S1: 2a+b > 2m, a+b > m+1
//             S2: 2a+b <= 2m, b >= m+1, a+2b <= 3m+3
//             S3: 2a+b <= 2m, b <= m, a+2b > 2m, 2a+3b <= 4m+4, a+b > m+1
//           DBL {a,2a,c}, c <= 2m, c not in {a,2a,3a}, gcd(a,c)=1, a+c > 2m, 2a+c > 2m+2,
//               and ( 3a > 2m  or  2a+c <= 3m+3 )
//           CHN {a,2a,3a}, 3a <= 2m, and ( 4a > 2m  or  xs(a,m) <= 4(m+1-a) )
// MINIMAL = exact and containing no predicted exact set of smaller size.
//
// Usage: trip3class mlo mhi [threads]
// Output: per-m counts, discrepancy lines (PRED-NOT-ENUM / ENUM-NOT-PRED), final summary.

use std::collections::{BTreeSet, HashSet};
use std::env;
use std::sync::{Arc, Mutex};
use std::thread;

fn gcd(a: u64, b: u64) -> u64 { if a == 0 { b } else { gcd(b % a, a) } }

fn badset_full(num: u64, den: u64, n: u64, t: u64) -> Vec<u64> {
    let p = num % den; let mut r = 0u64; let mut v = Vec::new();
    for x in 1..=n {
        r += p; if r >= den { r -= den; }
        let mn = if r < den - r { r } else { den - r };
        if t * mn < den { v.push(x); }
    }
    v
}

/// all exact bad sets of size <= 3 inside [1,2m], exhaustive over real times
fn enumerate(m: u64) -> BTreeSet<Vec<u64>> {
    let n = 2 * m; let t = m + 1;
    let mut pts: Vec<(u64, u64)> = vec![(0, 1), (1, 1)];
    for x in 1..=n {
        let den = x * t;
        for j in 0..=x { for s in [0i64, 1] {
            let numi = j as i64 * t as i64 + if s == 0 { -1 } else { 1 };
            if numi < 0 || numi as u64 > den { continue; }
            let num = numi as u64; let g = gcd(num, den).max(1);
            pts.push((num / g, den / g));
        }}
    }
    pts.sort_by(|a, b| (a.0 as u128 * b.1 as u128).cmp(&(b.0 as u128 * a.1 as u128)));
    pts.dedup();
    let mut cand: Vec<(u64,u64)> = pts.clone();
    for w in pts.windows(2) { cand.push((w[0].0 + w[1].0, w[0].1 + w[1].1)); }
    let mut out: BTreeSet<Vec<u64>> = BTreeSet::new();
    for (nu, de) in cand {
        let b = badset_full(nu, de, n, t);
        if b.is_empty() || b.len() > 3 { continue; }
        out.insert(b);
    }
    out
}

fn xs(a: u64, m: u64) -> u64 {
    let lo = 2 * m + 1 - a;
    for x in lo..=2 * m { if gcd(x, a) == 1 { return x; } }
    unreachable!()
}

/// predicted exact bad sets, with a family tag
fn predict(m: u64) -> Vec<(Vec<u64>, &'static str)> {
    let n = 2 * m; let t = m + 1;
    let mut v: Vec<(Vec<u64>, &'static str)> = Vec::new();
    v.push((vec![1], "ONE")); v.push((vec![t], "TOP"));
    // pairs
    for a in 1..=m {
        if 3 * a > n || xs(a, m) <= 3 * (t - a) { v.push((vec![a, 2 * a], "DBLP")); }
    }
    for q in [n + 1, n + 2] {
        for a in 1..=n { let b = q - a; if a < b && b <= n && gcd(a, q) == 1 { v.push((vec![a, b], "CMP")); } }
    }
    // triples
    for a in 1..=n { for b in (a + 1)..=n {
        let c = a + b;
        if c > n || b == 2 * a || gcd(a, b) != 1 { continue; }
        let s1 = 2 * a + b > n && c > t;
        let s2 = 2 * a + b <= n && b >= t && a + 2 * b <= 3 * t;
        let s3 = 2 * a + b <= n && b <= m && a + 2 * b > n && 2 * a + 3 * b <= 4 * t && c > t;
        if s1 { v.push((vec![a, b, c], "S1")); }
        else if s2 { v.push((vec![a, b, c], "S2")); }
        else if s3 { v.push((vec![a, b, c], "S3")); }
    }}
    for a in 1..=m { for c in 1..=n {
        if c == a || c == 2 * a || c == 3 * a || gcd(a, c) != 1 { continue; }
        if a + c > n && 2 * a + c > n + 2 && (3 * a > n || 2 * a + c <= 3 * t) {
            let mut s = vec![a, 2 * a, c]; s.sort(); v.push((s, "DBL3"));
        }
    }}
    for a in 1..=n {
        if 3 * a <= n && (4 * a > n || xs(a, m) <= 4 * (t - a)) { v.push((vec![a, 2 * a, 3 * a], "CHN")); }
    }
    v
}

/// paper's nine families (clsweep's classify, hypotheses included)
fn paper9(s: &[u64], m: u64) -> bool {
    let n = 2 * m;
    match s.len() {
        1 => s[0] == 1 || s[0] == m + 1,
        2 => {
            let (a, b) = (s[0], s[1]);
            if b == 2 * a && 3 * a > 2 * m && a <= m { return true; }
            for &q in &[2 * m + 1, 2 * m + 2] { if a + b == q && gcd(a, q) == 1 { return true; } }
            if b == 2 * a && 2 * a <= n {
                let lo = std::cmp::max(2 * m + 2, 2 * m + 2 * a) + 1;
                for q in lo..=(3 * m + 3) { if gcd(a, q) == 1 { return true; } }
            }
            false
        }
        3 => {
            let (a, b, c) = (s[0], s[1], s[2]);
            if c == a + b && gcd(a, b) == 1 {
                if c > m + 1 && 2 * a + b > 2 * m { return true; }
                if b >= m + 1 && a + 2 * b <= 3 * m + 3 { return true; }
            }
            for (x, y, t) in [(a, b, c), (a, c, b), (b, c, a)] {
                if y == 2 * x && x + t > 2 * m && 2 * x + t > 2 * m + 2 && 2 * x + t <= 3 * m + 3
                    && gcd(x, t) == 1 { return true; }
            }
            false
        }
        _ => false,
    }
}

fn minimal_of(sets: &BTreeSet<Vec<u64>>) -> BTreeSet<Vec<u64>> {
    let mut out = BTreeSet::new();
    for s in sets {
        let ss: HashSet<u64> = s.iter().cloned().collect();
        let contained = sets.iter().any(|u| u.len() < s.len() && u.iter().all(|x| ss.contains(x)));
        if !contained { out.insert(s.clone()); }
    }
    out
}

struct Res { m: u64, lines: Vec<String>, n_exact: usize, n_min3: usize, n_out9: usize, bad: usize,
             tags: Vec<(String, usize)> }

fn run(m: u64) -> Res {
    let enum_sets = enumerate(m);
    let pred = predict(m);
    let pred_sets: BTreeSet<Vec<u64>> = pred.iter().map(|(s, _)| s.clone()).collect();
    let mut lines = Vec::new(); let mut bad = 0;
    for s in &enum_sets { if !pred_sets.contains(s) { bad += 1; if lines.len() < 40 { lines.push(format!("m={} ENUM-NOT-PRED {:?}", m, s)); } } }
    for s in &pred_sets { if !enum_sets.contains(s) { bad += 1; if lines.len() < 40 { lines.push(format!("m={} PRED-NOT-ENUM {:?}", m, s)); } } }
    // minimal triples and tags
    let mins = minimal_of(&enum_sets);
    let mut tagcount: std::collections::BTreeMap<String, usize> = Default::default();
    let mut n_out9 = 0; let mut n_min3 = 0;
    for s in &mins {
        if s.len() != 3 { continue; }
        n_min3 += 1;
        let tag = pred.iter().find(|(p, _)| p == s).map(|(_, t)| *t).unwrap_or("NONE");
        let out9 = !paper9(s, m);
        if out9 { n_out9 += 1; }
        *tagcount.entry(format!("{}{}", tag, if out9 { "/out9" } else { "" })).or_insert(0) += 1;
    }
    Res { m, lines, n_exact: enum_sets.len(), n_min3, n_out9, bad,
          tags: tagcount.into_iter().collect() }
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let (mlo, mhi): (u64, u64) = (a[1].parse().unwrap(), a[2].parse().unwrap());
    let nth: usize = if a.len() > 3 { a[3].parse().unwrap() } else { 1 };
    let next = Arc::new(Mutex::new(mlo));
    let results: Arc<Mutex<Vec<Res>>> = Arc::new(Mutex::new(Vec::new()));
    let mut hs = Vec::new();
    for _ in 0..nth {
        let next = next.clone(); let results = results.clone();
        hs.push(thread::spawn(move || loop {
            let m = { let mut g = next.lock().unwrap(); let m = *g; *g += 1; m };
            if m > mhi { break; }
            let r = run(m);
            let mut g = results.lock().unwrap();
            eprintln!("done m={} exact<=3={} minimal3={} out9={} discrepancies={}", m, r.n_exact, r.n_min3, r.n_out9, r.bad);
            g.push(r);
        }));
    }
    for h in hs { h.join().unwrap(); }
    let mut rs = results.lock().unwrap(); rs.sort_by_key(|r| r.m);
    let mut totbad = 0; let mut totmin3 = 0; let mut totout9 = 0;
    let mut agg: std::collections::BTreeMap<String, usize> = Default::default();
    for r in rs.iter() {
        totbad += r.bad; totmin3 += r.n_min3; totout9 += r.n_out9;
        for (k, v) in &r.tags { *agg.entry(k.clone()).or_insert(0) += v; }
        println!("m={:>4} exact<=3={:>6} minimal_triples={:>6} outside_paper9={:>5} discrepancies={} tags={:?}",
                 r.m, r.n_exact, r.n_min3, r.n_out9, r.bad, r.tags);
        for l in &r.lines { println!("  {}", l); }
    }
    println!("\nRANGE m={}..{}: minimal triples={} outside paper's nine={} DISCREPANCIES={}", mlo, mhi, totmin3, totout9, totbad);
    println!("aggregate tags: {:?}", agg);
    println!("{}", if totbad == 0 { "RESULT: predicted list == enumerated list (exact bad sets of size <=3) on the whole range" } else { "RESULT: *** DISCREPANCIES ***" });
}
