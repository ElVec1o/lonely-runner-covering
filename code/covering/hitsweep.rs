// hitsweep -- EXACT complete enumeration of the bad sets by a breakpoint sweep, in O(m^3),
// replacing the O(m^5) scan of hitdec.rs; then the same window decision on top of it.
//
// The scan in hitdec.rs tests every reduced p/q with q <= 2N(m+1), which is O(m^4) pairs each
// costing O(m).  That enumeration, not the search, is what caps every tool in this project at
// m <= 63.  It is avoidable.
//
// Membership of a fixed x in the bad set changes only where ||x alpha|| = 1/(m+1), that is at
//
//     alpha = (j(m+1) +- 1) / (x(m+1)),        0 <= j < x,
//
// so over x in [1,2m] there are only O(m^2) breakpoints in [0,1), not O(m^4).  Between two
// consecutive breakpoints the bad set is constant, so evaluating it at one interior point per
// interval sees every bad set that occurs on an interval.
//
// The breakpoints themselves must ALSO be evaluated, and this is not an optional refinement.  At a
// breakpoint alpha0 some x has ||x alpha0|| = 1/(m+1) exactly, which is not < 1/(m+1), so that x is
// good there while it is bad on both sides.  Hence B(alpha0) is a PROPER subset of both neighbours,
// and a smaller bad set is a STRONGER constraint on a hitting set.  Dropping the breakpoints would
// lose genuine bad sets and could only turn a true "window holds" into a false one.
//
// All arithmetic is exact integer arithmetic on rationals (Rule 7): breakpoints are stored as
// reduced fractions and ordered by cross multiplication, and an interior point of an interval is
// taken as the mediant of its endpoints, which lies strictly between them.  No floating point
// appears anywhere.
//
// Correctness is checked against hitdec.rs: for every m in the overlap the two must produce the
// SAME family of minimal bad sets, not merely the same verdict.
//
// Usage:  hitsweep mlo mhi [logfile]
// Build:  rustc -O -o hitsweep hitsweep.rs

use std::collections::HashSet;
use std::env;
use std::fs::{rename, File};
use std::io::Write;
use std::time::Instant;

const W: usize = 8; // 512-bit window mask, i.e. m <= 256
type Bs = [u64; W];

fn bs_zero() -> Bs { [0; W] }
fn bs_set(b: &mut Bs, i: usize) { b[i >> 6] |= 1u64 << (i & 63); }
fn bs_get(b: &Bs, i: usize) -> bool { b[i >> 6] >> (i & 63) & 1 == 1 }
fn bs_disjoint(a: &Bs, b: &Bs) -> bool { (0..W).all(|i| a[i] & b[i] == 0) }
fn bs_or_into(a: &mut Bs, b: &Bs) { for i in 0..W { a[i] |= b[i]; } }
fn bs_count(a: &Bs) -> u32 { a.iter().map(|w| w.count_ones()).sum() }
fn bs_is_zero(a: &Bs) -> bool { a.iter().all(|&w| w == 0) }
fn bs_subset(s: &Bs, u: &Bs) -> bool { (0..W).all(|i| s[i] & !u[i] == 0) }

fn gcd(a: u64, b: u64) -> u64 { if a == 0 { b } else { gcd(b % a, a) } }

/// bad set of the rational num/den inside [1,n] with threshold 1/t, exact integer arithmetic
fn badset_of(num: u64, den: u64, n: u64, t: u64) -> Bs {
    let mut b = bs_zero();
    let p = num % den;
    let mut r = 0u64;
    for x in 1..=n {
        r += p;
        if r >= den { r -= den; }
        let mn = if r < den - r { r } else { den - r };
        if t * mn < den { bs_set(&mut b, (x - 1) as usize); }
    }
    b
}

/// every distinct bad set inside [1,2m], reduced to the minimal ones
fn minimal_bad_sets(m: u64) -> Vec<Bs> {
    let n = 2 * m;
    let t = m + 1;

    // breakpoints (j*t +- 1)/(x*t) in [0,1], as reduced fractions, plus the two endpoints
    let mut pts: Vec<(u64, u64)> = vec![(0, 1), (1, 1)];
    for x in 1..=n {
        let den = x * t;
        for j in 0..=x {
            for s in [0i64, 1] {
                let numi = j as i64 * t as i64 + if s == 0 { -1 } else { 1 };
                if numi < 0 || numi as u64 > den { continue; }
                let num = numi as u64;
                let g = gcd(num, den).max(1);
                pts.push((num / g, den / g));
            }
        }
    }
    pts.sort_by(|a, b| (a.0 as u128 * b.1 as u128).cmp(&(b.0 as u128 * a.1 as u128)));
    pts.dedup();

    let mut seen: HashSet<Bs> = HashSet::new();
    let mut raw: Vec<Bs> = Vec::new();
    let mut record = |b: Bs, seen: &mut HashSet<Bs>, raw: &mut Vec<Bs>| {
        if !bs_is_zero(&b) && seen.insert(b) { raw.push(b); }
    };

    // the breakpoints themselves, where a bad set can be strictly smaller than on both sides
    for &(nu, de) in &pts {
        record(badset_of(nu, de, n, t), &mut seen, &mut raw);
    }
    // one interior point per interval: the mediant lies strictly between the endpoints
    for w in pts.windows(2) {
        let (a, b) = (w[0], w[1]);
        record(badset_of(a.0 + b.0, a.1 + b.1, n, t), &mut seen, &mut raw);
    }

    raw.sort_by_key(|s| bs_count(s));
    let mut out: Vec<Bs> = Vec::new();
    for s in raw {
        if !out.iter().any(|u| bs_subset(u, &s)) { out.push(s); }
    }
    out
}

struct Dec { sets: Vec<Bs>, best: u32, nodes: u64, witness: Bs, found: bool }

impl Dec {
    fn rec(&mut self, hit: Bs, used: u32) {
        self.nodes += 1;
        if used >= self.best { return; }
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
            self.best = used; self.witness = hit; self.found = true; return;
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

fn main() {
    let args: Vec<String> = env::args().collect();
    let mlo: u64 = args[1].parse().unwrap();
    let mhi: u64 = args[2].parse().unwrap();
    let logf = if args.len() > 3 { args[3].clone() } else { String::from("hitsweep.log") };

    let t0 = Instant::now();
    let mut lines: Vec<String> = Vec::new();
    let mut holds = 0u64;
    let mut failed: Vec<u64> = Vec::new();

    for m in mlo..=mhi {
        assert!(2 * m <= (W * 64) as u64, "window {} exceeds the {}-bit mask", 2 * m, W * 64);
        let te = Instant::now();
        let sets = minimal_bad_sets(m);
        let te = te.elapsed().as_secs_f64();
        let ns = sets.len();

        let ts = Instant::now();
        let mut d = Dec { sets, best: (m + 1) as u32, nodes: 0, witness: bs_zero(), found: false };
        d.rec(bs_zero(), 0);
        let ts = ts.elapsed().as_secs_f64();

        let verdict = if d.found {
            failed.push(m);
            let v: Vec<u64> = (1..=2 * m).filter(|&x| bs_get(&d.witness, (x - 1) as usize)).collect();
            format!("*** WINDOW FAILS *** hitting set of size {}: {:?}", bs_count(&d.witness), v)
        } else {
            holds += 1;
            String::from("WINDOW HOLDS (tau = m+1)")
        };
        let done = m - mlo + 1;
        let total = mhi - mlo + 1;
        let el = t0.elapsed().as_secs_f64();
        let eta = el / done as f64 * (total - done) as f64;
        let line = format!("m={:>4} minsets={:>7} enum={:>8.2}s solve={:>9.2}s nodes={:>13} | {}",
                           m, ns, te, ts, d.nodes, verdict);
        println!("{}   [{}/{} elapsed {:.0}s eta {:.0}s]", line, done, total, el, eta);
        lines.push(line);

        let tmp = format!("{}.tmp", logf);
        let mut f = File::create(&tmp).unwrap();
        for l in &lines { writeln!(f, "{}", l).unwrap(); }
        writeln!(f, "-- {} of {} decided; holds at {}; FAILS at {:?}", lines.len(), total, holds, failed).unwrap();
        drop(f);
        rename(&tmp, &logf).unwrap();
    }
    println!("\nrange {}..{}: window HOLDS at {}; FAILS at {:?}", mlo, mhi, holds, failed);
}
