// indcount -- Stage 1 of the A10 program: count the independent sets of size exactly m in the
// bad-pair graph G on [1,2m] \ {1, m+1}, and report alpha(G) exactly.
//
// S1.1 gives alpha(G) >= m-1+def/2, so independent m-sets exist whenever def >= 2, i.e. for every
// composite 2m+1.  I(m) is exactly how much work the bad TRIPLES must do: every independent m-set
// must contain a bad triple, or A10 fails at that m.  Comparing I(m) against T(m), the number of
// minimal bad triples, decides whether the covering framework can close A10 at all:
//
//   I(m) >> T(m) and each triple killing few sets  =>  the framework provably cannot cover them
//                                                      => NO-GO for the covering approach.
//
// Also reports how many of the independent m-sets contain NO bad set at all.  That count must be
// ZERO whenever A10 holds at m (it is a direct counterexample otherwise), so it doubles as a
// negative control on the whole pipeline.
//
// Counting: branch on the highest-degree available vertex, v in or out; prune with
// popcount(avail) - greedy_matching(avail) < k, a valid upper bound on the independent set size.
//
// Usage:  indcount mlo mhi
// Build:  rustc -O -o indcount indcount.rs

use std::collections::HashSet;
use std::env;

fn gcd(a: u64, b: u64) -> u64 {
    if a == 0 { b } else { gcd(b % a, a) }
}

fn is_prime(x: u64) -> bool {
    if x < 2 { return false; }
    let mut d = 2;
    while d * d <= x { if x % d == 0 { return false; } d += 1; }
    true
}

struct Ctx {
    nbr: Vec<u64>,       // closed neighbourhood N[v] as a bitmask, by compact id
    adj: Vec<u64>,       // open neighbourhood
    nodes: u64,
}

/// greedy maximal matching inside `avail`; |IS| <= popcount(avail) - (matching size)
fn ub(avail: u64, adj: &[u64]) -> u32 {
    let mut rest = avail;
    let mut matched = 0u32;
    while rest != 0 {
        let v = rest.trailing_zeros() as usize;
        rest &= rest - 1;
        let cand = adj[v] & rest;
        if cand != 0 {
            let w = cand.trailing_zeros();
            rest &= !(1u64 << w);
            matched += 1;
        }
    }
    avail.count_ones() - matched
}

fn count(avail: u64, k: u32, c: &mut Ctx) -> u64 {
    if k == 0 { return 1; }
    if avail.count_ones() < k { return 0; }
    c.nodes += 1;
    if ub(avail, &c.adj) < k { return 0; }
    // branch on the highest-degree available vertex
    let mut best = usize::MAX;
    let mut bestd = -1i32;
    let mut rest = avail;
    while rest != 0 {
        let v = rest.trailing_zeros() as usize;
        rest &= rest - 1;
        let d = (c.adj[v] & avail).count_ones() as i32;
        if d > bestd { bestd = d; best = v; }
    }
    if bestd <= 0 {
        // no edges left: all remaining vertices are isolated, choose k of them
        let n = avail.count_ones() as u64;
        let kk = k as u64;
        let mut r: u64 = 1;
        for i in 0..kk { r = r * (n - i) / (i + 1); }
        return r;
    }
    let v = best;
    let excl = count(avail & !(1u64 << v), k, c);
    let incl = count(avail & !c.nbr[v], k - 1, c);
    excl + incl
}

/// largest k with a nonempty count, computed by descending search
fn alpha(avail: u64, c: &mut Ctx) -> u32 {
    let mut k = ub(avail, &c.adj);
    loop {
        if k == 0 { return 0; }
        if count(avail, k, c) > 0 { return k; }
        k -= 1;
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mlo: u64 = args[1].parse().unwrap();
    let mhi: u64 = args[2].parse().unwrap();

    for m in mlo..=mhi {
        let q0 = 2 * m + 1;
        let n = 2 * m;
        let t = m + 1;
        assert!(n <= 62, "window too wide for u64");
        let qmax = 2 * n * t;

        // all minimal bad sets, split by size
        let mut seen: HashSet<u64> = HashSet::new();
        let mut raw: Vec<u64> = Vec::new();
        for q in 1..=qmax {
            for p in 0..q {
                if gcd(p, q) != 1 { continue; }
                let mut mask: u64 = 0;
                let mut r = 0u64;
                for x in 1..=n {
                    r += p;
                    if r >= q { r -= q; }
                    let mn = if r < q - r { r } else { q - r };
                    if t * mn < q { mask |= 1u64 << (x - 1); }
                }
                if mask != 0 && seen.insert(mask) { raw.push(mask); }
            }
        }
        raw.sort_by_key(|s| s.count_ones());
        let mut sets: Vec<u64> = Vec::new();
        for &s in &raw {
            if !sets.iter().any(|&u| u & s == u) { sets.push(s); }
        }
        let pairs: Vec<u64> = sets.iter().cloned().filter(|s| s.count_ones() == 2).collect();
        let triples: Vec<u64> = sets.iter().cloned().filter(|s| s.count_ones() == 3).collect();

        // ground set and compact ids
        let ground: Vec<u64> = (1..=n).filter(|&x| x != 1 && x != m + 1).collect();
        let nv = ground.len();
        let pos = |v: u64| ground.iter().position(|&x| x == v);
        let mut adj: Vec<u64> = vec![0; nv];
        let mut edges = 0;
        for &s in &pairs {
            let vs: Vec<u64> = (1..=n).filter(|&x| s >> (x - 1) & 1 == 1).collect();
            if let (Some(a), Some(b)) = (pos(vs[0]), pos(vs[1])) {
                adj[a] |= 1u64 << b;
                adj[b] |= 1u64 << a;
                edges += 1;
            }
        }
        let nbr: Vec<u64> = (0..nv).map(|v| adj[v] | (1u64 << v)).collect();
        let full: u64 = if nv == 64 { !0u64 } else { (1u64 << nv) - 1 };
        let mut c = Ctx { nbr, adj, nodes: 0 };

        let al = alpha(full, &mut c);
        let im = count(full, m as u32, &mut c);
        println!(
            "m={:>2} q0={:>3} {} | V={} E={} | alpha={} (m={}) | I(m)={:<14} | T(m)={} | nodes={}",
            m, q0, if is_prime(q0) { "prime  " } else { "compos." },
            nv, edges, al, m, im, triples.len(), c.nodes
        );
    }
}
