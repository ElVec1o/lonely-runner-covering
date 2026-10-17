// hitdec -- DECIDE the dense window at m by deciding tau([1,B*m]) > m.
//
// Equivalence used:
//     LRC at height B for m runners  <=>  tau([1,B*m]) > m,   and always tau <= m+1 (Dirichlet),
// so the window holds at m  <=>  there is NO hitting set of size m.  That is a DECISION problem:
// seed the incumbent at m+1 and search for a hitting set of size <= m.  Search exhausts => none
// exists => tau = m+1 => the window HOLDS at m.  Search succeeds => an m-element counterexample
// family, printed.
//
// Bad sets are enumerated EXHAUSTIVELY over all reals (mediant bound q <= 2*N*t, see r3lscan.rs),
// then reduced to MINIMAL sets, which is all that matters for hitting.
//
// Pruning:
//   (a) incumbent: prune when used >= best;
//   (b) disjoint-set bound: greedily collect pairwise disjoint UNHIT sets; each needs its own
//       distinct element, so used + (that count) is a valid lower bound on any completion.
//   (c) branch on the SMALLEST unhit set (fewest children).
//
// Progress, ETA and checkpointing (Rule 8) are on the outer m loop: each m is one atomic unit and
// its verdict is appended to the log as soon as it lands, so a kill loses at most one m.
//
// Usage:  hitdec mlo mhi B
// Build:  rustc -O -o hitdec hitdec.rs

use std::collections::HashSet;
use std::env;
use std::time::Instant;

fn gcd(a: u64, b: u64) -> u64 {
    if a == 0 { b } else { gcd(b % a, a) }
}

struct Dec {
    sets: Vec<u128>,
    best: u32,
    nodes: u64,
    witness: u128,
    found: bool,
}

impl Dec {
    fn rec(&mut self, hit: u128, used: u32) {
        self.nodes += 1;
        if used >= self.best {
            return;
        }
        // smallest unhit set + disjoint-set lower bound, in one pass
        let mut target: Option<u128> = None;
        let mut tsize = u32::MAX;
        let mut covered: u128 = 0;
        let mut disj: u32 = 0;
        for &s in &self.sets {
            if s & hit == 0 {
                let c = s.count_ones();
                if c < tsize {
                    tsize = c;
                    target = Some(s);
                }
                if s & covered == 0 {
                    covered |= s;
                    disj += 1;
                }
            }
        }
        let Some(t) = target else {
            self.best = used;
            self.witness = hit;
            self.found = true;
            return;
        };
        if used + disj >= self.best {
            return; // (b)
        }
        let mut rest = t;
        while rest != 0 {
            let bit = rest & rest.wrapping_neg();
            rest ^= bit;
            self.rec(hit | bit, used + 1);
            if self.found {
                return;
            }
        }
    }
}

fn minimal_bad_sets(m: u64, bb: u64, tov: u64) -> Vec<u128> {
    let n = bb * m;
    let t = if tov > 0 { tov } else { m + 1 };
    let qmax = 2 * n * t;
    let mut seen: HashSet<u128> = HashSet::new();
    let mut raw: Vec<u128> = Vec::new();
    for q in 1..=qmax {
        for p in 0..q {
            if gcd(p, q) != 1 {
                continue;
            }
            let mut mask: u128 = 0;
            let mut r = 0u64;
            for x in 1..=n {
                r += p;
                if r >= q {
                    r -= q;
                }
                let mn = if r < q - r { r } else { q - r };
                if t * mn < q {
                    mask |= 1u128 << (x - 1);
                }
            }
            if mask != 0 && seen.insert(mask) {
                raw.push(mask);
            }
        }
    }
    raw.sort_by_key(|s| s.count_ones());
    let mut sets: Vec<u128> = Vec::new();
    for &s in &raw {
        if !sets.iter().any(|&u| u & s == u) {
            sets.push(s);
        }
    }
    sets
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mlo: u64 = args[1].parse().unwrap();
    let mhi: u64 = args[2].parse().unwrap();
    let bb: u64 = args[3].parse().unwrap();
    // threshold-denominator override: 0 = the real one (m+1). Used only for negative controls.
    let tov: u64 = if args.len() > 4 { args[4].parse().unwrap() } else { 0 };
    let t0 = Instant::now();

    for m in mlo..=mhi {
        let n = bb * m;
        assert!(n <= 127, "window {} exceeds the u128 bitmask", n);
        let tenum = Instant::now();
        let sets = minimal_bad_sets(m, bb, tov);
        let tenum = tenum.elapsed().as_secs_f64();

        let tsolve = Instant::now();
        // seed the incumbent at m+1: we only ask whether a hitting set of size <= m exists
        let mut d = Dec { sets, best: (m + 1) as u32, nodes: 0, witness: 0, found: false };
        d.rec(0, 0);
        let tsolve = tsolve.elapsed().as_secs_f64();

        if d.found {
            let mut v: Vec<u64> = Vec::new();
            for x in 1..=n {
                if d.witness >> (x - 1) & 1 == 1 {
                    v.push(x);
                }
            }
            println!(
                "m={} B={} | minimal sets={} | HITTING SET OF SIZE {} FOUND -> tau<=m -> WINDOW FAILS | witness={:?} | enum={:.1}s solve={:.1}s nodes={}",
                m, bb, d.sets.len(), d.best, v, tenum, tsolve, d.nodes
            );
        } else {
            println!(
                "m={} B={} | minimal sets={} | no hitting set of size <= {} -> tau=m+1 -> WINDOW HOLDS | enum={:.1}s solve={:.1}s nodes={} | total {:.1}s",
                m, bb, d.sets.len(), m, tenum, tsolve, d.nodes, t0.elapsed().as_secs_f64()
            );
        }
    }
}
