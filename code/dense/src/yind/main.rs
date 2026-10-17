// yind: independent check of "Statement 6" (paper/dense-window/main.tex, Proposition st:Y, first sentence):
// Y = {m+2,...,2m} contains no minimal bad set.  Standard library only, exact integer arithmetic, no code
// shared with src/cg or src/g1.
//
// Definitions.  For a real time t, B(t) = { x in [1,2m] : dist(x t, Z) < 1/(m+1) }  (bad set, bit x-1 of a u128).
// Every bad set of the family {B(t)} is attained either at a breakpoint t = ((m+1) n +- 1)/((m+1) x)
// (where some x switches status) or at the midpoint of two consecutive breakpoints in [0,1].  These
// candidates are enumerated exactly as fractions (num, den) with u64 arithmetic; B(t) is evaluated by
//   x in B(p/q)  <=>  (m+1) * min(x p mod q, q - x p mod q) < q.
// A minimal bad set is an inclusion-minimal member of the family.  Y contains a minimal bad set iff some B(t) is
// contained in Y (every B(t) contains a minimal one).  Statement: for every m the answer is "no".
// Requires 2m <= 128; run for m <= 63.
//
// Usage:  yind M1 M2        one line per m in [M1,M2]:  m, distinct, minimal, Y-independent, singleton minimal sets
//         yind control M    negative control: with Y' = {m+1,...,2m} (contains the singleton {m+1}) the answer must be "no"
use std::cmp::Ordering;
type Fr = (u64, u64); // (num, den)
fn cmp(a: Fr, b: Fr) -> Ordering { (a.0 * b.1).cmp(&(b.0 * a.1)) }
fn bad_mask(m: u64, f: Fr) -> u128 {
    let (p, q) = f; let mut s = 0u128;
    for x in 1..=2 * m { let r = (x * p) % q; if (m + 1) * r.min(q - r) < q { s |= 1u128 << (x - 1); } }
    s
}
fn family(m: u64) -> Vec<u128> {
    let mut pts: Vec<Fr> = vec![(0, 1), (1, 1)];
    for x in 1..=2 * m { for n in 0..=x { let c = (m + 1) * n;
        if c >= 1 { pts.push((c - 1, (m + 1) * x)); } pts.push((c + 1, (m + 1) * x)); } }
    pts.retain(|f| f.0 <= f.1); // inside [0,1]
    pts.sort_by(|a, b| cmp(*a, *b)); pts.dedup_by(|a, b| cmp(*a, *b) == Ordering::Equal);
    let mut sets: Vec<u128> = pts.iter().map(|&f| bad_mask(m, f)).collect();
    for w in pts.windows(2) { let mid = (w[0].0 * w[1].1 + w[1].0 * w[0].1, 2 * w[0].1 * w[1].1); sets.push(bad_mask(m, mid)); }
    sets.sort(); sets.dedup(); sets
}
fn minimal(sets: &[u128]) -> Vec<u128> {
    let mut by_size: Vec<u128> = sets.to_vec(); by_size.sort_by_key(|s| (s.count_ones(), *s));
    let mut mins: Vec<u128> = vec![];
    for &s in &by_size { if !mins.iter().any(|&t| t & !s == 0) { mins.push(s); } }
    mins
}
fn mask_range(a: u64, b: u64) -> u128 { let mut s = 0u128; for x in a..=b { s |= 1u128 << (x - 1); } s }
fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() >= 3 && a[1] == "control" {
        let m: u64 = a[2].parse().unwrap(); let sets = family(m); let mins = minimal(&sets);
        let yprime = mask_range(m + 1, 2 * m); let hit = sets.iter().filter(|&&s| s & !yprime == 0).count();
        let single = mins.iter().filter(|s| s.count_ones() == 1).count();
        println!("control m={} Y'={{m+1..2m}}: bad sets inside Y' = {}; singleton minimal sets = {}; expected: >= 1 (answer 'not independent')", m, hit, single);
        std::process::exit(if hit >= 1 { 0 } else { 1 });
    }
    let (m1, m2): (u64, u64) = (a[1].parse().unwrap(), a[2].parse().unwrap());
    println!("m\tdistinct_bad_sets\tminimal\tbad_sets_inside_Y\tY_independent\tsingleton_minimal");
    for m in m1..=m2 { let sets = family(m); let mins = minimal(&sets); let y = mask_range(m + 2, 2 * m);
        let inside = sets.iter().filter(|&&s| s & !y == 0).count();
        println!("{}\t{}\t{}\t{}\t{}\t{}", m, sets.len(), mins.len(), inside, inside == 0, mins.iter().filter(|s| s.count_ones() == 1).count()); }
}
