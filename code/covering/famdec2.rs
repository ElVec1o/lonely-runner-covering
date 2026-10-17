// famdec2 -- decide the dense window from the nine VERIFIED families, searching the complement.
//
// famdec.rs runs a generic hitting-set branch and bound.  That is the wrong search space here: by
// Proposition 7.1 the pair-only lower bound tops out at m+1-def/2, so the bound can never prune on
// its own and the tree is forced to enumerate, badly.
//
// Here we search the COMPLEMENT instead.  A hitting set H of size m exists iff its complement S,
// also of size m, contains no bad set.  The two singletons {1} and {m+1} force 1, m+1 in H, so
// S sits inside the ground set [1,2m] \ {1, m+1} of size 2m-2, and:
//
//   * S contains no bad PAIR   <=>  S is independent in the bad-pair graph G;
//   * S contains no bad TRIPLE <=>  no triple has all three members in S.
//
// So: search for an independent m-set of G avoiding every triple.  Choosing v deletes N[v] at once
// (pair constraint) and, for every triple through v whose other two members are one chosen and one
// still available, deletes that one (triple constraint).  Pruning is the standard independent-set
// bound |S| <= popcount(avail) - (greedy matching inside avail).
//
// Verdicts, never conflated:
//   WINDOW HOLDS           search exhausted; sound for the window by monotonicity of tau.
//   FAMILIES INSUFFICIENT  an m-set free of all nine families exists; says NOTHING about the
//                          window, only that the classified vocabulary does not decide this m.
//
// Usage:  famdec2 mlo mhi [logfile]
// Build:  rustc -O -o famdec2 famdec2.rs

use std::collections::HashSet;
use std::env;
use std::fs::{rename, File};
use std::io::Write;
use std::time::Instant;

const W: usize = 4; // 256 bits of ground set, i.e. m <= 129
type Bs = [u64; W];

fn bs_zero() -> Bs { [0; W] }
fn bs_set(b: &mut Bs, i: usize) { b[i >> 6] |= 1u64 << (i & 63); }
fn bs_get(b: &Bs, i: usize) -> bool { b[i >> 6] >> (i & 63) & 1 == 1 }
fn bs_clear(b: &mut Bs, i: usize) { b[i >> 6] &= !(1u64 << (i & 63)); }
fn bs_andnot(a: &Bs, b: &Bs) -> Bs { let mut r = bs_zero(); for i in 0..W { r[i] = a[i] & !b[i]; } r }
fn bs_and(a: &Bs, b: &Bs) -> Bs { let mut r = bs_zero(); for i in 0..W { r[i] = a[i] & b[i]; } r }
fn bs_count(a: &Bs) -> u32 { a.iter().map(|w| w.count_ones()).sum() }
fn bs_empty(a: &Bs) -> bool { a.iter().all(|&w| w == 0) }
fn bs_lowest(a: &Bs) -> usize {
    for i in 0..W { if a[i] != 0 { return (i << 6) + a[i].trailing_zeros() as usize; } }
    usize::MAX
}

fn gcd(a: u64, b: u64) -> u64 { if a == 0 { b } else { gcd(b % a, a) } }

struct Ctx {
    nv: usize,
    adj: Vec<Bs>,            // open neighbourhood in the bad-pair graph
    nbr: Vec<Bs>,            // closed neighbourhood
    tri: Vec<Vec<(usize, usize)>>, // tri[v] = the other two members of each triple through v
    m: u32,
    nodes: u64,
    found: bool,
    witness: Vec<usize>,
}

/// |independent set inside avail| <= popcount(avail) - (greedy maximal matching inside avail)
fn ub(avail: &Bs, adj: &[Bs]) -> u32 {
    let mut rest = *avail;
    let mut matched = 0u32;
    while !bs_empty(&rest) {
        let v = bs_lowest(&rest);
        bs_clear(&mut rest, v);
        let cand = bs_and(&adj[v], &rest);
        if !bs_empty(&cand) { bs_clear(&mut rest, bs_lowest(&cand)); matched += 1; }
    }
    bs_count(avail) - matched
}

fn search(avail: Bs, chosen: &mut Vec<usize>, chosen_mask: Bs, c: &mut Ctx) {
    if c.found { return; }
    if chosen.len() as u32 == c.m { c.found = true; c.witness = chosen.clone(); return; }
    c.nodes += 1;
    let need = c.m - chosen.len() as u32;
    if bs_count(&avail) < need { return; }
    if ub(&avail, &c.adj) < need { return; }

    // branch on a vertex of maximum degree inside avail
    let mut best = usize::MAX;
    let mut bd = -1i64;
    let mut rest = avail;
    while !bs_empty(&rest) {
        let v = bs_lowest(&rest);
        bs_clear(&mut rest, v);
        let d = bs_count(&bs_and(&c.adj[v], &avail)) as i64;
        if d > bd { bd = d; best = v; }
    }
    let v = best;

    // include v: delete N[v], then close the triples through v that now have two chosen members
    let mut a_in = bs_andnot(&avail, &c.nbr[v]);
    let mut cm = chosen_mask;
    bs_set(&mut cm, v);
    for &(x, y) in &c.tri[v] {
        if bs_get(&cm, x) && bs_get(&a_in, y) { bs_clear(&mut a_in, y); }
        if bs_get(&cm, y) && bs_get(&a_in, x) { bs_clear(&mut a_in, x); }
    }
    chosen.push(v);
    search(a_in, chosen, cm, c);
    chosen.pop();
    if c.found { return; }

    // exclude v
    let mut a_out = avail;
    bs_clear(&mut a_out, v);
    search(a_out, chosen, chosen_mask, c);
}

/// the nine verified families as vertex lists inside [1,2m]
fn family_sets(m: u64) -> Vec<Vec<u64>> {
    let n = 2 * m;
    let mut raw: Vec<Vec<u64>> = Vec::new();
    let mut push = |v: Vec<u64>| {
        let mut v = v;
        v.sort();
        v.dedup();
        if v.iter().all(|&x| x >= 1 && x <= n) { raw.push(v); }
    };
    push(vec![1]);
    push(vec![m + 1]);
    for d in 1..=m { if 3 * d > 2 * m { push(vec![d, 2 * d]); } }
    for &q in &[2 * m + 1, 2 * m + 2] {
        for a in 2..=m { if gcd(a, q) == 1 && q - a <= n { push(vec![a, q - a]); } }
    }
    for a in 1..=m {
        let lo = std::cmp::max(2 * m + 2, 2 * m + 2 * a) + 1;
        for q in lo..=(3 * m + 3) { if gcd(a, q) == 1 { push(vec![a, 2 * a]); break; } }
    }
    for a in 1..n {
        for b in (a + 1)..=n {
            let s = a + b;
            if s > n { break; }
            if gcd(a, b) != 1 { continue; }
            let f1 = s > m + 1 && 2 * a + b > 2 * m;
            let f2 = b >= m + 1 && a + 2 * b <= 3 * m + 3;
            if f1 || f2 { push(vec![a, b, s]); }
        }
    }
    for a in 1..=m {
        for t in 1..=n {
            if a + t > 2 * m && 2 * a + t > 2 * m + 2 && 2 * a + t <= 3 * m + 3 && gcd(a, t) == 1 {
                push(vec![a, 2 * a, t]);
            }
        }
    }
    let mut seen: HashSet<Vec<u64>> = HashSet::new();
    let mut uniq: Vec<Vec<u64>> = Vec::new();
    for v in raw { if seen.insert(v.clone()) { uniq.push(v); } }
    uniq.sort_by_key(|v| v.len());
    // keep only minimal sets
    let mut out: Vec<Vec<u64>> = Vec::new();
    for s in uniq {
        let ss: HashSet<u64> = s.iter().cloned().collect();
        if !out.iter().any(|u| u.iter().all(|x| ss.contains(x))) { out.push(s); }
    }
    out
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mlo: u64 = args[1].parse().unwrap();
    let mhi: u64 = args[2].parse().unwrap();
    let logf = if args.len() > 3 { args[3].clone() } else { String::from("famdec2.log") };

    let t0 = Instant::now();
    let mut lines: Vec<String> = Vec::new();
    let mut holds = 0u64;
    let mut insufficient: Vec<u64> = Vec::new();

    for m in mlo..=mhi {
        let sets = family_sets(m);
        // the two singletons must be exactly {1} and {m+1}
        let singles: Vec<u64> = sets.iter().filter(|s| s.len() == 1).map(|s| s[0]).collect();
        assert_eq!(singles.len(), 2, "expected exactly the two singleton families at m={}", m);
        let ground: Vec<u64> = (1..=2 * m).filter(|x| !singles.contains(x)).collect();
        let nv = ground.len();
        assert!(nv <= W * 64, "ground set {} exceeds the {}-bit mask", nv, W * 64);
        let id = |v: u64| ground.iter().position(|&x| x == v);

        let mut adj = vec![bs_zero(); nv];
        let mut tri: Vec<Vec<(usize, usize)>> = vec![Vec::new(); nv];
        let mut np = 0;
        let mut nt = 0;
        for s in &sets {
            if s.len() == 2 {
                if let (Some(a), Some(b)) = (id(s[0]), id(s[1])) {
                    bs_set(&mut adj[a], b); bs_set(&mut adj[b], a); np += 1;
                }
            } else if s.len() == 3 {
                if let (Some(a), Some(b), Some(cc)) = (id(s[0]), id(s[1]), id(s[2])) {
                    tri[a].push((b, cc)); tri[b].push((a, cc)); tri[cc].push((a, b)); nt += 1;
                }
            }
        }
        let nbr: Vec<Bs> = (0..nv).map(|v| { let mut b = adj[v]; bs_set(&mut b, v); b }).collect();
        let mut full = bs_zero();
        for i in 0..nv { bs_set(&mut full, i); }

        let ts = Instant::now();
        let mut c = Ctx { nv, adj, nbr, tri, m: m as u32, nodes: 0, found: false, witness: vec![] };
        let mut chosen: Vec<usize> = Vec::new();
        search(full, &mut chosen, bs_zero(), &mut c);
        let ts = ts.elapsed().as_secs_f64();
        let _ = c.nv;

        let verdict = if c.found {
            insufficient.push(m);
            let mut v: Vec<u64> = c.witness.iter().map(|&i| ground[i]).collect();
            v.sort();
            format!("FAMILIES INSUFFICIENT (bad-set-free m-set {:?}) -- says nothing about the window", v)
        } else {
            holds += 1;
            String::from("WINDOW HOLDS (no bad-set-free m-set for the verified families)")
        };
        let done = m - mlo + 1;
        let total = mhi - mlo + 1;
        let el = t0.elapsed().as_secs_f64();
        let eta = el / done as f64 * (total - done) as f64;
        let line = format!("m={:>4} pairs={:>6} triples={:>7} solve={:>9.2}s nodes={:>13} | {}",
                           m, np, nt, ts, c.nodes, verdict);
        println!("{}   [{}/{} elapsed {:.0}s eta {:.0}s]", line, done, total, el, eta);
        lines.push(line);

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
