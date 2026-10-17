// clsweep -- exhaustiveness of the size-<=3 classification, checked far past the paper's range.
//
// Theorem 4.1 asserts that every bad set of size 1, 2 or 3 inside [1,2m] belongs to one of nine
// explicitly parameterized families, and labels that COMPUTED over 7 <= m <= 24.  That is the
// weakest computed claim in the paper and the one the family-only decision of the window rests on,
// so it is worth checking much further.
//
// This tool enumerates EVERY bad set of size at most three by the O(m^3) breakpoint sweep, which is
// exhaustive over all real times, and tests each against the nine families:
//
//   {1}                             {m+1}
//   MUL  {d, 2d}    2m/3 < d <= m
//   CMP  {a, q-a}   q = 2m+1 or q = 2m+2, gcd(a,q) = 1
//   DBL  {a, 2a}    some q in (max(2m+2, 2m+2a), 3m+3] with gcd(a,q) = 1
//   SUM  {a, b, a+b}   a+b > m+1 and 2a+b > 2m,  gcd(a,b) = 1
//   SUM' {a, b, a+b}   b >= m+1, a+2b <= 3m+3,   gcd(a,b) = 1
//   DBL3 {a, 2a, t}    a+t > 2m, 2m+2 < 2a+t <= 3m+3, gcd(a,t) = 1
//
// Any bad set of size <= 3 matching none of these is printed in full: it would be a new species and
// a counterexample to Theorem 4.1 as stated.
//
// Usage:  clsweep mlo mhi
// Build:  rustc -O -o clsweep clsweep.rs

use std::collections::HashSet;
use std::env;

fn gcd(a: u64, b: u64) -> u64 { if a == 0 { b } else { gcd(b % a, a) } }

/// full bad set of num/den inside [1,n]
fn badset_full(num: u64, den: u64, n: u64, t: u64) -> Vec<u64> {
    let p = num % den; let mut r = 0u64; let mut v = Vec::new();
    for x in 1..=n {
        r += p; if r >= den { r -= den; }
        let mn = if r < den - r { r } else { den - r };
        if t * mn < den { v.push(x); }
    }
    v
}

/// every minimal bad set together with a witnessing time, via the breakpoint sweep
fn bad_sets(m: u64) -> Vec<(Vec<u64>, u64, u64)> {
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
    let mut seen: HashSet<Vec<u64>> = HashSet::new();
    let mut out: Vec<(Vec<u64>, u64, u64)> = Vec::new();
    for (nu, de) in cand {
        if de == 0 { continue; }
        let b = badset_full(nu, de, n, t);
        if b.is_empty() || b.len() > 6 { continue; }
        if seen.insert(b.clone()) { out.push((b, nu % de, de)); }
    }
    out.sort_by_key(|(b, _, _)| b.len());
    // keep only minimal ones
    let mut min: Vec<(Vec<u64>, u64, u64)> = Vec::new();
    for (b, p, q) in out {
        let bs: HashSet<u64> = b.iter().cloned().collect();
        if !min.iter().any(|(u, _, _)| u.iter().all(|x| bs.contains(x))) { min.push((b, p, q)); }
    }
    min
}


/// does `s` belong to one of the nine families?
fn classify(s: &[u64], m: u64) -> Option<&'static str> {
    let n = 2 * m;
    if s.len() == 1 {
        if s[0] == 1 { return Some("SING1"); }
        if s[0] == m + 1 { return Some("SINGM"); }
        return None;
    }
    if s.len() == 2 {
        let (a, b) = (s[0], s[1]);
        if b == 2 * a && 3 * a > 2 * m && a <= m { return Some("MUL"); }
        for &q in &[2 * m + 1, 2 * m + 2] {
            if a + b == q && gcd(a, q) == 1 { return Some("CMP"); }
        }
        if b == 2 * a && 2 * a <= n {
            let lo = std::cmp::max(2 * m + 2, 2 * m + 2 * a) + 1;
            for q in lo..=(3 * m + 3) { if gcd(a, q) == 1 { return Some("DBL"); } }
        }
        return None;
    }
    if s.len() == 3 {
        let (a, b, c) = (s[0], s[1], s[2]);
        if c == a + b && gcd(a, b) == 1 {
            if c > m + 1 && 2 * a + b > 2 * m { return Some("SUM"); }
            if b >= m + 1 && a + 2 * b <= 3 * m + 3 { return Some("SUMP"); }
        }
        // DBL3 {a, 2a, t}: the doubling pair may be any two of the three
        for (x, y, t) in [(a, b, c), (a, c, b), (b, c, a)] {
            if y == 2 * x && x + t > 2 * m && 2 * x + t > 2 * m + 2 && 2 * x + t <= 3 * m + 3
                && gcd(x, t) == 1 { return Some("DBL3"); }
        }
        return None;
    }
    Some("BIG")
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let (mlo, mhi): (u64, u64) = (a[1].parse().unwrap(), a[2].parse().unwrap());
    let mut worst: Vec<String> = Vec::new();
    let mut tot = 0u64;
    let mut npair = 0u64;
    let mut nsing = 0u64;
    for m in mlo..=mhi {
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
        pts.sort_by(|x, y| (x.0 as u128 * y.1 as u128).cmp(&(y.0 as u128 * x.1 as u128)));
        pts.dedup();
        let mut cand: Vec<(u64,u64)> = pts.clone();
        for w in pts.windows(2) { cand.push((w[0].0 + w[1].0, w[0].1 + w[1].1)); }
        let mut seen: HashSet<Vec<u64>> = HashSet::new();
        let mut small: Vec<Vec<u64>> = Vec::new();
        for (nu, de) in cand {
            if de == 0 { continue; }
            let b = badset_full(nu, de, n, t);
            if b.is_empty() || b.len() > 3 { continue; }
            if seen.insert(b.clone()) { small.push(b); }
        }
        // only MINIMAL ones need a family: a size-3 set containing a bad pair is not minimal
        let mut minimal: Vec<Vec<u64>> = Vec::new();
        let mut by_size = small.clone();
        by_size.sort_by_key(|s| s.len());
        for s in by_size {
            let ss: HashSet<u64> = s.iter().cloned().collect();
            if !minimal.iter().any(|u| u.iter().all(|x| ss.contains(x))) { minimal.push(s); }
        }
        let mut bad = 0;
        for s in &minimal {
            tot += 1;
            if classify(s, m).is_none() {
                bad += 1;
                if s.len() == 2 { npair += 1; }
                if s.len() == 1 { nsing += 1; }
                if worst.len() < 12 { worst.push(format!("m={} UNCLASSIFIED size {} {:?}", m, s.len(), s)); }
            }
        }
        if bad > 0 || m % 25 == 0 || m == mhi {
            println!("m={:>4} minimal size<=3 bad sets={:>5} unclassified={}", m, minimal.len(), bad);
        }
    }
    println!("\nunclassified by size: singletons={} pairs={} (rest are triples)", nsing, npair);
    println!("{} minimal bad sets of size <= 3 checked over m={}..{}", tot, mlo, mhi);
    if worst.is_empty() {
        println!("RESULT: every one belongs to one of the nine families. Theorem 4.1 holds on this range.");
    } else {
        println!("RESULT: *** UNCLASSIFIED SETS FOUND -- Theorem 4.1 is FALSE as stated ***");
        for w in &worst { println!("  {}", w); }
    }
}
