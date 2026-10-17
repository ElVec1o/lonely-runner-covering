// alphaex -- exact independence number of the bad-pair graph G on [1,2m] \ {1, m+1}.
//
// Checks Proposition 7.1 (alpha >= m-1+def/2-b) against reality: with b = 0 measured, the claim is
// alpha(G) = m-1+def/2 exactly.  This is an independent code path from indcount.rs, which counts
// the independent m-sets; here only the maximum is computed, so the range reaches further.
//
// Exact maximum independent set by branch and bound with the two standard safe reductions:
//   deg 0 -> take it;   deg 1 -> take it and delete its neighbour (never worse).
// The bad-pair graph is nearly a forest, so the reductions cascade and the recursion stays shallow.
//
// Usage:  alphaex mlo mhi [all]
// Build:  rustc -O -o alphaex alphaex.rs

use std::collections::HashSet;
use std::env;

fn gcd(a: u64, b: u64) -> u64 { if a == 0 { b } else { gcd(b % a, a) } }

fn is_prime(x: u64) -> bool {
    if x < 2 { return false; }
    let mut d = 2;
    while d * d <= x { if x % d == 0 { return false; } d += 1; }
    true
}

/// maximum independent set inside `avail`
fn mis(mut avail: u128, nbr: &[u128], adj: &[u128], nodes: &mut u64) -> u32 {
    let mut taken = 0u32;
    *nodes += 1;
    loop {
        let mut act = None;
        let mut rest = avail;
        while rest != 0 {
            let v = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            if (adj[v] & avail).count_ones() <= 1 { act = Some(v); break; }
        }
        match act {
            Some(v) => { taken += 1; avail &= !nbr[v]; }
            None => break,
        }
    }
    if avail == 0 { return taken; }
    // branch on a vertex of maximum degree
    let mut best = usize::MAX;
    let mut bd = 0u32;
    let mut rest = avail;
    while rest != 0 {
        let v = rest.trailing_zeros() as usize;
        rest &= rest - 1;
        let d = (adj[v] & avail).count_ones();
        if d > bd { bd = d; best = v; }
    }
    let v = best;
    let a = 1 + mis(avail & !nbr[v], nbr, adj, nodes);
    let b = mis(avail & !(1u128 << v), nbr, adj, nodes);
    taken + if a > b { a } else { b }
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let (mlo, mhi): (u64, u64) = (a[1].parse().unwrap(), a[2].parse().unwrap());
    let all = a.len() > 3 && a[3] == "all";
    println!("  m   q0  type    |  V   E | alpha | m-1 | alpha-(m-1) | nodes");
    for m in mlo..=mhi {
        let q0 = 2 * m + 1;
        let prime = is_prime(q0);
        if prime && !all { continue; }
        let n = 2 * m;
        let t = m + 1;
        let qmax = 2 * n * t;
        let ground: Vec<u64> = (1..=n).filter(|&x| x != 1 && x != m + 1).collect();
        let nv = ground.len();
        assert!(nv <= 128, "ground set too wide for u128");
        let idx = |v: u64| ground.iter().position(|&x| x == v);

        let mut seen: HashSet<u128> = HashSet::new();
        let mut ed: Vec<(usize, usize)> = Vec::new();
        for q in 1..=qmax {
            for p in 0..q {
                if gcd(p, q) != 1 { continue; }
                let mut vs: Vec<u64> = Vec::new();
                let mut r = 0u64;
                let mut over = false;
                for x in 1..=n {
                    r += p;
                    if r >= q { r -= q; }
                    let mn = if r < q - r { r } else { q - r };
                    if t * mn < q { vs.push(x); if vs.len() > 2 { over = true; break; } }
                }
                if !over && vs.len() == 2 {
                    let k = (1u128 << (vs[0] - 1)) | (1u128 << (vs[1] - 1));
                    if seen.insert(k) {
                        if let (Some(x), Some(y)) = (idx(vs[0]), idx(vs[1])) { ed.push((x, y)); }
                    }
                }
            }
        }
        let mut adj: Vec<u128> = vec![0; nv];
        for &(x, y) in &ed { adj[x] |= 1u128 << y; adj[y] |= 1u128 << x; }
        let nbr: Vec<u128> = (0..nv).map(|v| adj[v] | 1u128 << v).collect();
        let full: u128 = if nv == 128 { !0u128 } else { (1u128 << nv) - 1 };
        let mut nodes = 0u64;
        let al = mis(full, &nbr, &adj, &mut nodes);
        println!("{:3} {:4}  {}  | {:3} {:3} | {:5} | {:3} | {:11} | {}",
            m, q0, if prime { "prime  " } else { "compos." },
            nv, ed.len(), al, m - 1, al as i64 - (m as i64 - 1), nodes);
    }
}
