// identchk.rs - tests the ConsecutiveIdentity, the sole open input to the pair classification.
//
// For every bad pair {a,b} in [1,2m] and every time p/q realizing it with the residues on opposite
// sides of zero, write u = a*p mod q (the small one, above) and v = q - (b*p mod q) (the small one,
// below).  The claim is
//
//     a*v + b*u = q.
//
// Also tested, because Delta2PairIdentity.lean DERIVES them from badness rather than assuming them
// (so a failure here would mean the Lean derivation is answering a different question):
//
//     a <= m,   q <= 2*u*t,   q <= (u+v)*t,   and the conclusion   a+b <= 2t.
//
// Two known-FALSE controls run on the same instances and must both fire, otherwise a HOLDS verdict
// means nothing.  "a*v + b*u = 2q" would NOT do as a control: it is implied false by the identity
// itself, so it could never fire and would certify nothing.  The controls used instead are
// q <= 2*v*t, the symmetric partner of a derived fact, false by measurement; and a+b <= 2t-1, false
// whenever the pair is complementary at 2m+2.  Times are found by the breakpoint sweep; mediants are REDUCED
// before use, since an earlier tester that skipped that reported 1504 spurious failures.
//
//   rustc -O -o identchk identchk.rs && ./identchk 4 90

use std::collections::HashSet;

fn gcd(a: u64, b: u64) -> u64 { if a == 0 { b } else { gcd(b % a, a) } }

fn badset(num: u64, den: u64, n: u64, t: u64) -> Vec<u64> {
    let mut v = Vec::new();
    for x in 1..=n {
        let r = (x as u128 * num as u128 % den as u128) as u64;
        let d = r.min(den - r);
        if (d as u128) * (t as u128) < den as u128 { v.push(x); }
    }
    v
}

/// breakpoints of the bad-set function, plus reduced mediants
fn times(m: u64) -> Vec<(u64, u64)> {
    let t = m + 1;
    let mut pts: Vec<(u64, u64)> = vec![(0, 1), (1, 1)];
    for x in 1..=2 * m {
        let den = x * t;
        for j in 0..=x {
            for s in [-1i64, 1] {
                let ni = j as i64 * t as i64 + s;
                if ni < 0 || ni as u64 > den { continue; }
                let (nu, de) = (ni as u64, den);
                let g = gcd(nu, de).max(1);
                pts.push((nu / g, de / g));
            }
        }
    }
    pts.sort_by(|a, b| (a.0 as u128 * b.1 as u128).cmp(&(b.0 as u128 * a.1 as u128)));
    pts.dedup();
    let mut out: Vec<(u64, u64)> = pts.clone();
    for w in pts.windows(2) {
        let (nu, de) = (w[0].0 + w[1].0, w[0].1 + w[1].1);
        let g = gcd(nu, de).max(1);
        out.push((nu / g, de / g));
    }
    let mut seen = HashSet::new();
    out.retain(|&x| x.1 != 0 && seen.insert(x));
    out
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let mlo: u64 = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(4);
    let mhi: u64 = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(90);

    let (mut inst, mut same, mut dbl) = (0u64, 0u64, 0u64);
    let (mut f_id, mut f_am, mut f_2u, mut f_uv, mut f_cc) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let (mut f_ctl, mut f_ct2) = (0u64, 0u64);
    let mut ex: Vec<String> = Vec::new();
    let mut cvals: HashSet<u64> = HashSet::new();

    for m in mlo..=mhi {
        let (n, t) = (2 * m, m + 1);
        for (p, q) in times(m) {
            let bs = badset(p, q, n, t);
            if bs.len() != 2 { continue; }
            let (x, y) = (bs[0], bs[1]);
            if y == 2 * x { dbl += 1; continue; }
            let (ra, rb) = ((x * p) % q, (y * p) % q);
            // u is the distance above for a, v the distance below for b
            if !(2 * ra <= q && 2 * rb > q) { same += 1; continue; }
            let (u, v) = (ra, q - rb);
            inst += 1;
            let lhs = x as u128 * v as u128 + y as u128 * u as u128;
            if lhs != q as u128 {
                f_id += 1;
                if lhs % q as u128 == 0 { cvals.insert((lhs / q as u128) as u64); }
                if ex.len() < 5 { ex.push(format!("ID m={} a={} b={} p/q={}/{} u={} v={} lhs={}", m, x, y, p, q, u, v, lhs)); }
            } else { cvals.insert(1); }
            if x > m { f_am += 1; }
            if (q as u128) > 2 * u as u128 * t as u128 { f_2u += 1; }
            if (q as u128) > (u + v) as u128 * t as u128 { f_uv += 1; }
            if x + y > 2 * t { f_cc += 1; }
            // CONTROLS, both known FALSE, both must fire or the tester reads nothing:
            //   C1  q <= 2*v*t   the symmetric partner of the derived fact, false by measurement
            //   C2  a+b <= 2t-1  false whenever the pair is complementary at 2m+2
            if (q as u128) > 2 * v as u128 * t as u128 { f_ctl += 1; }
            if x + y > 2 * t - 1 { f_ct2 += 1; }
        }
    }

    println!("ConsecutiveIdentity, m = {}..{}\n", mlo, mhi);
    println!("  non-doubling pairs with opposite residues : {:>8}", inst);
    println!("  doubling pairs skipped                    : {:>8}", dbl);
    println!("  same-side residues skipped                : {:>8}", same);
    println!();
    println!("  IDENTITY  a*v + b*u = q          failures : {:>8}  {}", f_id, if f_id == 0 { "HOLDS" } else { "FALSE" });
    println!("  coefficients q observed                   : {:?}", { let mut c: Vec<u64> = cvals.into_iter().collect(); c.sort(); c });
    println!();
    println!("  derived  a <= m                  failures : {:>8}", f_am);
    println!("  derived  q <= 2*u*t              failures : {:>8}", f_2u);
    println!("  derived  q <= (u+v)*t            failures : {:>8}", f_uv);
    println!("  conclusion  a+b <= 2t            failures : {:>8}", f_cc);
    for e in &ex { println!("        {}", e); }
    println!();
    println!("  CONTROL C1  q <= 2*v*t   (known FALSE)  fired : {:>8}", f_ctl);
    println!("  CONTROL C2  a+b <= 2t-1  (known FALSE)  fired : {:>8}", f_ct2);
    if f_ctl == 0 || f_ct2 == 0 {
        println!("\n*** A CONTROL DID NOT FIRE. The tester is not detecting known-false statements,");
        println!("*** so every HOLDS above is unvalidated and means nothing. ***");
    } else {
        println!("\n  Both controls fired, so a HOLDS verdict above is meaningful.");
    }
}
