// famdec -- decide the dense window using ONLY the nine VERIFIED bad-set families.
//
// hitdec.rs enumerates bad sets by scanning every reduced p/q with q <= 2N(m+1).  That is
// exhaustive but costs O(m^4) time and, more importantly, the resulting family is an unformalized
// object: the Lean development knows the nine families of Section 6, not "whatever the scan found".
//
// This tool instead GENERATES the bad sets from the nine families alone:
//     singletons  {1}, {m+1}
//     MUL         {d, 2d}          2m/3 < d <= m
//     CMP(2m+1)   {a, 2m+1-a}      gcd(a, 2m+1) = 1
//     CMP(2m+2)   {a, 2m+2-a}      gcd(a, 2m+2) = 1
//     DBL         {a, 2a}          some q in (max(2m+2, 2m+2a), 3m+3] with gcd(a,q) = 1
//     SUM         {a, b, a+b}      m+1 < a+b <= 2m,  2a+b > 2m,        gcd(a,b) = 1
//     SUM'        {a, b, a+b}      b >= m+1, a+b <= 2m, a+2b <= 3m+3,  gcd(a,b) = 1
//     DBL3        {a, 2a, t}       a+t > 2m, 2m+2 < 2a+t <= 3m+3,      gcd(a,t) = 1
//
// Every one of these is a Lean theorem (Delta2Triples.lean), so a verdict here rests on verified
// mathematics plus one combinatorial search, not on an unaudited enumeration.
//
// Soundness of the direction we care about: tau is monotone in the family of sets to be hit, so
// "no hitting set of size m for THIS subfamily" implies "no hitting set of size m at all", which is
// exactly the window statement.  A verdict in the other direction proves nothing about the window;
// it proves only that the nine families are insufficient at that m, which is itself the useful
// diagnostic.  The two outcomes are printed differently and never conflated.
//
// Cost is O(m^2) generation instead of O(m^4) scanning, so the range is bounded by the search and
// by the bitmask width (512 bits here, i.e. m <= 256), not by the enumeration.
//
// Usage:  famdec mlo mhi [logfile]
// Build:  rustc -O -o famdec famdec.rs

use std::collections::HashSet;
use std::env;
use std::fs::{rename, File};
use std::io::Write;
use std::time::Instant;

const W: usize = 8; // 512 bits
type Bs = [u64; W];

fn bs_zero() -> Bs { [0; W] }
fn bs_set(b: &mut Bs, i: usize) { b[i >> 6] |= 1u64 << (i & 63); }
fn bs_get(b: &Bs, i: usize) -> bool { b[i >> 6] >> (i & 63) & 1 == 1 }
fn bs_disjoint(a: &Bs, b: &Bs) -> bool { (0..W).all(|i| a[i] & b[i] == 0) }
fn bs_or_into(a: &mut Bs, b: &Bs) { for i in 0..W { a[i] |= b[i]; } }
fn bs_count(a: &Bs) -> u32 { a.iter().map(|w| w.count_ones()).sum() }
/// is `s` contained in `u`?
fn bs_subset(s: &Bs, u: &Bs) -> bool { (0..W).all(|i| s[i] & !u[i] == 0) }

fn gcd(a: u64, b: u64) -> u64 { if a == 0 { b } else { gcd(b % a, a) } }

struct Dec {
    sets: Vec<Bs>,
    best: u32,
    nodes: u64,
    witness: Bs,
    found: bool,
}

impl Dec {
    fn rec(&mut self, hit: Bs, used: u32) {
        self.nodes += 1;
        if used >= self.best { return; }
        // smallest unhit set, and a disjoint-set lower bound, in one pass
        let mut target: Option<usize> = None;
        let mut tsize = u32::MAX;
        let mut covered = bs_zero();
        let mut disj = 0u32;
        for (i, s) in self.sets.iter().enumerate() {
            if bs_disjoint(s, &hit) {
                let c = bs_count(s);
                if c < tsize { tsize = c; target = Some(i); }
                if bs_disjoint(s, &covered) { bs_or_into(&mut covered, s); disj += 1; }
            }
        }
        let Some(ti) = target else {
            self.best = used;
            self.witness = hit;
            self.found = true;
            return;
        };
        if used + disj >= self.best { return; }
        let t = self.sets[ti];
        for i in 0..W * 64 {
            if bs_get(&t, i) {
                let mut h = hit;
                bs_set(&mut h, i);
                self.rec(h, used + 1);
                if self.found { return; }
            }
        }
    }
}

/// the nine verified families, as minimal sets inside [1,2m]
fn family_sets(m: u64) -> Vec<Bs> {
    let n = 2 * m;
    let mut raw: Vec<Vec<u64>> = Vec::new();
    let push = |raw: &mut Vec<Vec<u64>>, mut v: Vec<u64>| {
        v.sort();
        v.dedup();
        if v.iter().all(|&x| x >= 1 && x <= n) { raw.push(v); }
    };

    // singletons
    push(&mut raw, vec![1]);
    push(&mut raw, vec![m + 1]);

    // MUL: 2m/3 < d <= m
    for d in 1..=m {
        if 3 * d > 2 * m { push(&mut raw, vec![d, 2 * d]); }
    }

    // CMP at q = 2m+1 and q = 2m+2
    for &q in &[2 * m + 1, 2 * m + 2] {
        for a in 2..=m {
            if gcd(a, q) == 1 && q - a <= n { push(&mut raw, vec![a, q - a]); }
        }
    }

    // DBL: {a, 2a} witnessed by some q in (max(2m+2, 2m+2a), 3m+3] coprime to a
    for a in 1..=m {
        let lo = std::cmp::max(2 * m + 2, 2 * m + 2 * a) + 1;
        for q in lo..=(3 * m + 3) {
            if gcd(a, q) == 1 { push(&mut raw, vec![a, 2 * a]); break; }
        }
    }

    // SUM and SUM': {a, b, a+b}
    for a in 1..n {
        for b in (a + 1)..=n {
            let s = a + b;
            if s > n { break; }
            if gcd(a, b) != 1 { continue; }
            let f1 = s > m + 1 && 2 * a + b > 2 * m;
            let f2 = b >= m + 1 && a + 2 * b <= 3 * m + 3;
            if f1 || f2 { push(&mut raw, vec![a, b, s]); }
        }
    }

    // DBL3: {a, 2a, t}
    for a in 1..=m {
        for t in 1..=n {
            if a + t > 2 * m && 2 * a + t > 2 * m + 2 && 2 * a + t <= 3 * m + 3
                && gcd(a, t) == 1 { push(&mut raw, vec![a, 2 * a, t]); }
        }
    }

    // dedupe, then keep only the minimal ones
    let mut seen: HashSet<Vec<u64>> = HashSet::new();
    let mut uniq: Vec<Vec<u64>> = Vec::new();
    for v in raw { if seen.insert(v.clone()) { uniq.push(v); } }
    uniq.sort_by_key(|v| v.len());
    let masks: Vec<Bs> = uniq.iter().map(|v| {
        let mut b = bs_zero();
        for &x in v { bs_set(&mut b, (x - 1) as usize); }
        b
    }).collect();
    let mut out: Vec<Bs> = Vec::new();
    for s in masks { if !out.iter().any(|u| bs_subset(u, &s)) { out.push(s); } }
    out
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mlo: u64 = args[1].parse().unwrap();
    let mhi: u64 = args[2].parse().unwrap();
    let logf = if args.len() > 3 { args[3].clone() } else { String::from("famdec.log") };

    let t0 = Instant::now();
    let mut lines: Vec<String> = Vec::new();
    let mut holds = 0u64;
    let mut insufficient: Vec<u64> = Vec::new();

    for m in mlo..=mhi {
        assert!(2 * m <= (W * 64) as u64, "window {} exceeds the {}-bit mask", 2 * m, W * 64);
        let tg = Instant::now();
        let sets = family_sets(m);
        let tg = tg.elapsed().as_secs_f64();
        let nsets = sets.len();

        let ts = Instant::now();
        let mut d = Dec { sets, best: (m + 1) as u32, nodes: 0, witness: bs_zero(), found: false };
        d.rec(bs_zero(), 0);
        let ts = ts.elapsed().as_secs_f64();

        let verdict = if d.found {
            insufficient.push(m);
            let v: Vec<u64> = (1..=2 * m).filter(|&x| bs_get(&d.witness, (x - 1) as usize)).collect();
            format!("FAMILIES INSUFFICIENT (hitting set of size {} exists for the subfamily: {:?}) \
                     -- says nothing about the window", bs_count(&d.witness), v)
        } else {
            holds += 1;
            String::from("WINDOW HOLDS (no hitting set of size m for the verified families)")
        };
        let done = m - mlo + 1;
        let total = mhi - mlo + 1;
        let el = t0.elapsed().as_secs_f64();
        let eta = el / done as f64 * (total - done) as f64;
        let line = format!("m={:>4} sets={:>7} gen={:>7.2}s solve={:>8.2}s nodes={:>12} | {}",
                           m, nsets, tg, ts, d.nodes, verdict);
        println!("{}   [{}/{} elapsed {:.0}s eta {:.0}s]", line, done, total, el, eta);
        lines.push(line);

        // atomic checkpoint after every m
        let tmp = format!("{}.tmp", logf);
        let mut f = File::create(&tmp).unwrap();
        for l in &lines { writeln!(f, "{}", l).unwrap(); }
        writeln!(f, "-- {} of {} decided; window holds at {}; families insufficient at {:?}",
                 lines.len(), total, holds, insufficient).unwrap();
        drop(f);
        rename(&tmp, &logf).unwrap();
    }

    println!("\nrange {}..{}: window HOLDS at {} values; families INSUFFICIENT at {:?}",
             mlo, mhi, holds, insufficient);
}
