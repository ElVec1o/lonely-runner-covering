// hitnum -- EXACT minimum hitting number tau([1,B*m]) of the bad-set hypergraph.
//
// Equivalence used:  a family of m velocities inside [1,B*m] is a counterexample
// exactly when it HITS every bad set (every time is defeated), and a smaller hitting set pads up
// to m elements.  Hence
//        LRC at height B for m runners   <=>   tau([1,B*m]) > m .
// So tau is not a bound on the problem, it IS the problem, and tau - m is the margin.
//
// The covering framework proves tau > m only through a decomposition: for any partition,
// sum_i tau(U_i) <= tau([1,B*m]), and the cover-capacity certificate is exactly the assertion
// sum_i tau(U_i) > m.  So tau - (best sum over partitions) is the framework's loss.  Knowing tau
// exactly tells us how much headroom there is; nobody had measured it.
//
// Bad sets are enumerated EXHAUSTIVELY over all reals: membership of x flips only at
// a = (j*t +- 1)/(x*t), all of denominator <= N*t, and between consecutive breakpoints the mediant
// has denominator <= 2*N*t, so every reduced p/q with q <= 2*N*t meets every breakpoint and every
// gap.  Only MINIMAL bad sets matter for hitting, so supersets are discarded.
//
// Usage:  hitnum m B
// Build:  rustc -O -o hitnum hitnum.rs

use std::collections::HashSet;
use std::env;

fn gcd(a: u64, b: u64) -> u64 {
    if a == 0 { b } else { gcd(b % a, a) }
}

struct Hs {
    sets: Vec<u64>,
    best: u32,
    nodes: u64,
}

impl Hs {
    fn rec(&mut self, hit: u64, used: u32) {
        self.nodes += 1;
        if used >= self.best {
            return;
        }
        // the smallest still-unhit set; branch over its elements (complete and minimal)
        let mut target: Option<u64> = None;
        let mut tsize = u32::MAX;
        for &s in &self.sets {
            if s & hit == 0 {
                let c = s.count_ones();
                if c < tsize {
                    tsize = c;
                    target = Some(s);
                    if c == 1 {
                        break;
                    }
                }
            }
        }
        let Some(t) = target else {
            self.best = used; // everything hit
            return;
        };
        let mut rest = t;
        while rest != 0 {
            let bit = rest & rest.wrapping_neg();
            rest ^= bit;
            self.rec(hit | bit, used + 1);
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let m: u64 = args[1].parse().unwrap();
    let bb: u64 = args[2].parse().unwrap();
    let n = bb * m;
    let t = m + 1;
    assert!(n <= 63, "window {} exceeds the u64 bitmask", n);
    let qmax = 2 * n * t; // exhaustive over all reals

    let mut seen: HashSet<u64> = HashSet::new();
    let mut raw: Vec<u64> = Vec::new();
    for q in 1..=qmax {
        for p in 0..q {
            if gcd(p, q) != 1 {
                continue;
            }
            let mut mask: u64 = 0;
            let mut r = 0u64;
            for x in 1..=n {
                r += p;
                if r >= q {
                    r -= q;
                }
                let mn = if r < q - r { r } else { q - r };
                if t * mn < q {
                    mask |= 1u64 << (x - 1);
                }
            }
            if mask != 0 && seen.insert(mask) {
                raw.push(mask);
            }
        }
    }
    // keep only minimal sets: a superset of another bad set is redundant for hitting
    raw.sort_by_key(|s| s.count_ones());
    let mut sets: Vec<u64> = Vec::new();
    for &s in &raw {
        if !sets.iter().any(|&u| u & s == u) {
            sets.push(s);
        }
    }

    let mut hs = Hs { sets, best: (n + 1) as u32, nodes: 0 };
    hs.rec(0, 0);
    println!(
        "m={} B={} window=[1,{}] qmax={} | distinct bad sets={} minimal={} | tau={} | m={} | margin tau-m={} | LRC at this height: {} | nodes={}",
        m, bb, n, qmax, raw.len(), hs.sets.len(), hs.best, m,
        (hs.best as i64) - (m as i64),
        if (hs.best as u64) > m { "HOLDS" } else { "FAILS" },
        hs.nodes
    );
}
