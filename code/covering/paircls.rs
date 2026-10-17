// paircls -- arithmetic classification of ALL minimal bad PAIRS inside [1,2m].
//
// The triples were classified (tripchar.rs -> SUM/DBL, formalized in Delta2Triples.lean) but the
// pairs never were: `badset_unit_pair` covers only the complementary-unit family {a, q0-a} at the
// modulus q0 = 2m+1.  Result 43 showed that leaves the bad-pair graph a non-explicit object, which
// blocks any arithmetic law for the Gallai-Edmonds D.  This tool closes that gap.
//
// A pair is MINIMAL iff its full bad set inside [1,2m] is exactly {a,b} (no bad singleton inside).
// Classification by the SIGNED residue pattern (x*p mod q, folded to (-q/2, q/2]) plus arithmetic:
//   MUL  residues (0,0)      : both multiples of q; the bad set is the multiples of q in the window
//   CMP  residues (r,-r)     : complementary, a + b = q  (Bohman-Peng; badset_unit_pair when r=1)
//   DBL  residues (r,2r)     : b = 2a rides at double residue
//   OTH  anything else
// Reports counts, and for CMP whether q = 2m+1 (the badset_unit_pair case) or q > 2m+1.
//
// Usage:  paircls mlo mhi [show]
// Build:  rustc -O -o paircls paircls.rs

use std::collections::HashMap;
use std::env;

fn gcd(a: u64, b: u64) -> u64 {
    if a == 0 { b } else { gcd(b % a, a) }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mlo: u64 = args[1].parse().unwrap();
    let mhi: u64 = args[2].parse().unwrap();
    let show: bool = args.len() > 3;

    for m in mlo..=mhi {
        let n = 2 * m;
        assert!(n <= 64, "paircls stores a pair as a u64 bitmask: valid for m <= 32 only (for m >= 33 the shifts wrap and the output is void)");
        let t = m + 1;
        let qmax = 2 * n * t;
        // smallest generating (q,p) for each pair mask; also collect singleton masks
        let mut best: HashMap<u64, (u64, u64)> = HashMap::new();
        let mut singles: Vec<u64> = Vec::new();
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
                    if t * mn < q {
                        vs.push(x);
                        if vs.len() > 2 { over = true; break; }
                    }
                }
                if over { continue; }
                if vs.len() == 1 && !singles.contains(&vs[0]) { singles.push(vs[0]); }
                if vs.len() == 2 {
                    let key = (1u64 << (vs[0] - 1)) | (1u64 << (vs[1] - 1));
                    best.entry(key).or_insert((q, p));
                }
            }
        }
        let (mut mul, mut cmp_lo, mut cmp_hi, mut dbl, mut oth) = (0u32, 0u32, 0u32, 0u32, 0u32);
        let mut othlist: Vec<String> = Vec::new();
        let mut list: Vec<(u64, u64, u64, u64)> = Vec::new(); // a,b,q,p
        for (&key, &(q, p)) in &best {
            let vs: Vec<u64> = (1..=n).filter(|&x| key >> (x - 1) & 1 == 1).collect();
            let (a, b) = (vs[0], vs[1]);
            // minimal: contains no bad singleton
            if singles.contains(&a) || singles.contains(&b) { continue; }
            list.push((a, b, q, p));
        }
        list.sort();
        for &(a, b, q, p) in &list {
            let sg = |x: u64| -> i64 {
                let r = x * p % q;
                if r <= q / 2 { r as i64 } else { r as i64 - q as i64 }
            };
            let (ra, rb) = (sg(a), sg(b));
            let tagname;
            if ra == 0 && rb == 0 {
                mul += 1; tagname = "MUL";
            } else if ra == -rb {
                if q == 2 * m + 1 { cmp_lo += 1; } else { cmp_hi += 1; }
                tagname = "CMP";
            } else if rb == 2 * ra || ra == 2 * rb {
                dbl += 1; tagname = "DBL";
            } else {
                oth += 1; tagname = "OTH";
                othlist.push(format!("{{{},{}}} q={} p={} res=({},{})", a, b, q, p, ra, rb));
            }
            if show {
                println!("     {{{},{}}}  {}  q={} p={} res=({},{})", a, b, tagname, q, p, ra, rb);
            }
        }
        println!(
            "m={:>2} q0={:>3} | minimal pairs={:>3} | MUL={} CMP(q=q0)={} CMP(q>q0)={} DBL={} OTH={}",
            m, 2 * m + 1, list.len(), mul, cmp_lo, cmp_hi, dbl, oth
        );
        for s in othlist.iter().take(6) { println!("       OTH: {}", s); }
    }
}
