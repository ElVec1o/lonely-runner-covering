// mlcheck: exact maximum loneliness ML(v) = max_t min_i ||v_i t||, independent of code/reduction/mdr.
// Standard library only, exact i128 integer arithmetic.
//
// Method.  gap_v(t) = min_i ||v_i t|| is piecewise linear; a local maximum occurs where a decreasing piece
// of one tent function meets an increasing piece of another (or at the peak of one tent), that is at
//     t = k / (v_i + v_j),   k = 0,...,v_i+v_j,   i <= j,
// with EVERY integer k, not only k coprime to v_i+v_j.  (A reduced fraction k/(v_i+v_j) may have a
// smaller denominator that is not itself a sum of two speeds.)  Units: gap values are fractions of 1 (circle length 1).
//
// Usage:  mlcheck V1 V2 ...        each V is a comma-separated list; prints ML as a reduced fraction and the
//                                  maximisers t in [0,1/2] as reduced fractions.
//         mlcheck selftest         known values: [1,2,3,4] -> 1/5; [1..m] -> 1/(m+1) for m=2..12;
//                                  [3,4,7,11] -> 2/9 (maximiser 1/9, denominator 9 is not a sum of two speeds; the
//                                  coprime-only candidate set gives 3/14); Goddyn-Wong tight sets (1,3,4,7) -> 1/5,
//                                  (1,3,4,5,9) -> 1/6.  Each is also compared with a rational grid scan of all t = p/q, q <= 400.
type I = i128;
fn gcd(a: I, b: I) -> I { let (mut a, mut b) = (a.abs(), b.abs()); while b != 0 { let t = a % b; a = b; b = t; } a }
fn gap_num(v: &[I], k: I, s: I) -> I { v.iter().map(|&x| { let r = ((x * k) % s + s) % s; r.min(s - r) }).min().unwrap() }
fn lt(a: (I, I), b: (I, I)) -> bool { a.0 * b.1 < b.0 * a.1 }
fn ml(v: &[I]) -> ((I, I), Vec<(I, I)>) {
    let m = v.len(); let mut best = (0 as I, 1 as I); let mut arg: Vec<(I, I)> = vec![];
    let mut seen = std::collections::HashSet::new();
    for i in 0..m { for j in i..m { let s = v[i] + v[j]; if !seen.insert(s) { continue; }
        for k in 0..=s { let cand = (gap_num(v, k, s), s);
            if lt(best, cand) { best = cand; arg.clear(); arg.push((k, s)); } else if !lt(cand, best) { arg.push((k, s)); } } } }
    let g = gcd(best.0, best.1); let best = (best.0 / g, best.1 / g);
    let mut red: Vec<(I, I)> = arg.iter().map(|&(k, s)| { let g = gcd(k, s); (k / g, s / g) }).filter(|&(k, s)| 2 * k <= s).collect();
    red.sort_by(|a, b| (a.0 * b.1).cmp(&(b.0 * a.1))); red.dedup(); (best, red)
}
fn grid(v: &[I], qmax: I) -> (I, I) { let mut best = (0 as I, 1 as I);
    for q in 1..=qmax { for p in 0..=q { let c = (gap_num(v, p, q), q); if lt(best, c) { best = c; } } }
    let g = gcd(best.0, best.1); (best.0 / g, best.1 / g) }
fn parse(s: &str) -> Vec<I> { s.split(',').map(|x| x.trim().parse().unwrap()).collect() }
fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() >= 2 && a[1] == "selftest" {
        let mut bad = 0;
        let mut cases: Vec<(Vec<I>, (I, I))> = vec![(vec![1, 2, 3, 4], (1, 5)), (vec![3, 4, 7, 11], (2, 9)), (vec![1, 3, 4, 7], (1, 5)), (vec![1, 3, 4, 5, 9], (1, 6))];
        for m in 2..=12 { cases.push(((1..=m as I).collect(), (1, m as I + 1))); }
        for (v, want) in cases { let (got, _) = ml(&v); let gr = grid(&v, 400);
            let ok = got == want && gr == want; if !ok { bad += 1; }
            println!("{:?}: ML {}/{} (expected {}/{}), grid q<=400: {}/{} {}", v, got.0, got.1, want.0, want.1, gr.0, gr.1, if ok { "ok" } else { "FAIL" }); }
        println!("selftest failures: {}", bad); if bad > 0 { std::process::exit(1); }
        return;
    }
    for s in &a[1..] { let v = parse(s); let (b, arg) = ml(&v);
        println!("v={:?} ML={}/{} maximisers t in [0,1/2]: {}", v, b.0, b.1, arg.iter().map(|x| format!("{}/{}", x.0, x.1)).collect::<Vec<_>>().join(" ")); }
}
