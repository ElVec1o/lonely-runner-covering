// tmpl63 -- DECIDE the (6,3) template: does [1,2m] \ {1, m+1} partition into blocks of size 6
// with tau = 3?
//
// Result 41: every non-overlapping VERIFIED certificate (m=10, m=16) is exactly
//     {1} and {m+1} as free singletons (surplus +1 each)  +  (m-1)/3 blocks of size 6, tau 3,
// which needs 6*(m-1)/3 = 2m-2 = |ground|, i.e. 3 | m-1.  If that partition exists for every such
// m, A10 follows on the arithmetic progression m = 1 mod 3.  This tool decides it per m.
//
// Result 49: the previous tool (certgen) generated candidate blocks as unions of at most TWO bad
// sets and so could never produce these blocks -- the real ones need a union of THREE.  Here the
// 6-subsets are enumerated DIRECTLY and filtered by tau, so no such bias exists.
//
// tau(U) is computed exactly: tau >= 3 iff no single element and no pair of elements of U hits
// every bad set inside U; tau <= 3 iff some triple does.  These blocks have tau > nu (the m=10
// blocks have nu = 2, tau = 3), i.e. they are genuine integrality-gap cuts, which is why a
// matching-based search cannot find them.
//
// Usage:  tmpl63 m
// Build:  rustc -O -o tmpl63 tmpl63.rs

use std::collections::HashSet;
use std::env;

fn gcd(a: u64, b: u64) -> u64 {
    if a == 0 { b } else { gcd(b % a, a) }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let m: u64 = args[1].parse().unwrap();
    if (m - 1) % 3 != 0 {
        println!("m={}: 3 does not divide m-1, template not applicable", m);
        return;
    }
    let n = 2 * m;
    let t = m + 1;
    assert!(n <= 62, "window {} exceeds the u64 bitmask", n);
    let qmax = 2 * n * t;

    // exhaustive minimal bad sets
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
    // only bad sets of size <= 6 can sit inside a 6-block
    let small: Vec<u64> = sets.iter().cloned().filter(|s| s.count_ones() <= 6).collect();

    let ground: Vec<u64> = (1..=n).filter(|&x| x != 1 && x != m + 1).collect();
    let gmask: u64 = ground.iter().fold(0u64, |a, &v| a | 1u64 << (v - 1));
    let ng = ground.len();

    // enumerate 6-subsets of ground, keep those with tau exactly 3
    let mut blocks: Vec<u64> = Vec::new();
    let idx: Vec<u64> = ground.iter().map(|&v| 1u64 << (v - 1)).collect();
    for a in 0..ng {
    for b in a + 1..ng {
    for c in b + 1..ng {
    for d in c + 1..ng {
    for e in d + 1..ng {
    for f in e + 1..ng {
        let u = idx[a] | idx[b] | idx[c] | idx[d] | idx[e] | idx[f];
        let inside: Vec<u64> = small.iter().cloned().filter(|&s| s & u == s).collect();
        if inside.len() < 2 { continue; }
        let els = [idx[a], idx[b], idx[c], idx[d], idx[e], idx[f]];
        // tau >= 3 : no single and no pair hits everything
        let mut hit_small = false;
        'outer: for i in 0..6 {
            if inside.iter().all(|&s| s & els[i] != 0) { hit_small = true; break 'outer; }
            for j in i + 1..6 {
                let h = els[i] | els[j];
                if inside.iter().all(|&s| s & h != 0) { hit_small = true; break 'outer; }
            }
        }
        if hit_small { continue; }
        // tau <= 3 : some triple hits everything
        let mut ok3 = false;
        'o3: for i in 0..6 { for j in i + 1..6 { for l in j + 1..6 {
            let h = els[i] | els[j] | els[l];
            if inside.iter().all(|&s| s & h != 0) { ok3 = true; break 'o3; }
        }}}
        if ok3 { blocks.push(u); }
    }}}}}}

    // exact cover of `gmask` by the blocks: branch on the lowest uncovered element
    fn cover(rest: u64, by_low: &Vec<Vec<u64>>, out: &mut Vec<u64>, nodes: &mut u64,
             cap: u64, hit: &mut bool) -> bool {
        if rest == 0 { return true; }
        *nodes += 1;
        if *nodes > cap { *hit = true; return false; }
        let low = rest.trailing_zeros() as usize;
        for &blk in &by_low[low] {
            if blk & rest == blk {
                out.push(blk);
                if cover(rest & !blk, by_low, out, nodes, cap, hit) { return true; }
                if *hit { return false; }
                out.pop();
            }
        }
        false
    }
    let mut by_low: Vec<Vec<u64>> = vec![Vec::new(); 64];
    for &blk in &blocks { by_low[blk.trailing_zeros() as usize].push(blk); }
    let mut out: Vec<u64> = Vec::new();
    let mut nodes = 0u64;
    let cap: u64 = if args.len() > 2 { args[2].parse().unwrap() } else { 200_000_000 };
    let mut hit = false;
    let found = cover(gmask, &by_low, &mut out, &mut nodes, cap, &mut hit);

    println!(
        "m={:>2} q0={:>3} | ground={} need {} blocks | (6,3)-blocks found={} | nodes={} | TEMPLATE: {}",
        m, 2 * m + 1, ng, (m - 1) / 3, blocks.len(), nodes,
        if found { "EXISTS" } else if hit { "UNDECIDED (node limit -- NOT a negative)" }
        else { "DOES NOT EXIST (search exhausted)" }
    );
    if found {
        for blk in &out {
            let v: Vec<u64> = (1..=n).filter(|&x| blk >> (x - 1) & 1 == 1).collect();
            println!("     block {:?}", v);
        }
    }
}
