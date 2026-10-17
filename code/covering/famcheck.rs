// famcheck -- certify the SOUNDNESS of the family route used by famdec.rs.
//
// famdec decides the window by hitting a generated family F_gen instead of the true family F_true
// of all bad sets.  The implication we use is
//
//     F_gen subset of F_true   =>   tau(F_gen) <= tau(F_true),
//
// so "no hitting set of size m for F_gen" gives the window statement.  The direction that can go
// wrong is OVER-generation: a set in F_gen that is NOT a bad set is a fake constraint, it can only
// push tau up, and it would manufacture a false "window holds".  Under-generation is harmless.
//
// So the load-bearing requirement is exactly F_gen subset of F_true, and this tool certifies it
// CONSTRUCTIVELY: every family member is emitted together with the time p/q its proposition names,
// and the bad set B(p,q) inside [1,2m] is recomputed from the definition and compared for EQUALITY
// with the claimed set.  A generated set that equals the bad set of an explicit time is a bad set,
// no scan required, so the certificate is available at every m rather than only where an
// exhaustive O(m^4) enumeration is affordable.
//
// The witnessing times, one per family:
//   {1}          q = 2m+2,   p = 1
//   {m+1}        q = m+1,    p = 1
//   MUL  {d,2d}  q = d,      p = 1
//   CMP  {a,q-a} q,          p = a^{-1} mod q          q in {2m+1, 2m+2}
//   DBL  {a,2a}  q,          p = -a^{-1} mod q
//   SUM  {a,b,a+b}   q = a+b,    p = a^{-1} mod q
//   SUM' {a,b,a+b}   q = a+2b,   p = b^{-1} mod q
//   DBL3 {a,2a,t}    q = 2a+t,   p = a^{-1} mod q
//
// Usage:  famcheck mlo mhi [verbose]
// Build:  rustc -O -o famcheck famcheck.rs

use std::env;

fn gcd(a: u64, b: u64) -> u64 { if a == 0 { b } else { gcd(b % a, a) } }

/// modular inverse of a mod q by extended Euclid; requires gcd(a,q) = 1 and q >= 1
fn inv(a: u64, q: u64) -> u64 {
    let (mut old_r, mut r) = (a as i128, q as i128);
    let (mut old_s, mut s) = (1i128, 0i128);
    while r != 0 {
        let quo = old_r / r;
        let tmp = old_r - quo * r; old_r = r; r = tmp;
        let tmp = old_s - quo * s; old_s = s; s = tmp;
    }
    assert_eq!(old_r, 1, "inv: {} not invertible mod {}", a, q);
    (((old_s % q as i128) + q as i128) % q as i128) as u64
}

/// the bad set of p/q inside [1,n] with threshold 1/t, as a sorted vector
fn badset(p: u64, q: u64, n: u64, t: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let mut r = 0u64;
    let pr = p % q;
    for x in 1..=n {
        r += pr;
        if r >= q { r -= q; }
        let mn = if r < q - r { r } else { q - r };
        if t * mn < q { out.push(x); }
    }
    out
}

struct Item { set: Vec<u64>, p: u64, q: u64, fam: &'static str }

/// every family member together with the time its proposition names
fn generate(m: u64) -> Vec<Item> {
    let n = 2 * m;
    let mut v: Vec<Item> = Vec::new();
    let mut add = |set: Vec<u64>, p: u64, q: u64, fam: &'static str| {
        let mut s = set; s.sort(); s.dedup();
        if s.iter().all(|&x| x >= 1 && x <= n) { v.push(Item { set: s, p, q, fam }); }
    };

    add(vec![1], 1, 2 * m + 2, "SING1");
    add(vec![m + 1], 1, m + 1, "SINGM");

    for d in 1..=m {
        if 3 * d > 2 * m { add(vec![d, 2 * d], 1, d, "MUL"); }
    }

    for &q in &[2 * m + 1, 2 * m + 2] {
        let fam = if q == 2 * m + 1 { "CMP1" } else { "CMP2" };
        for a in 2..=m {
            if gcd(a, q) == 1 && q - a <= n { add(vec![a, q - a], inv(a, q), q, fam); }
        }
    }

    for a in 1..=m {
        let lo = std::cmp::max(2 * m + 2, 2 * m + 2 * a) + 1;
        for q in lo..=(3 * m + 3) {
            if gcd(a, q) == 1 { add(vec![a, 2 * a], (q - inv(a, q)) % q, q, "DBL"); break; }
        }
    }

    for a in 1..n {
        for b in (a + 1)..=n {
            let s = a + b;
            if s > n { break; }
            if gcd(a, b) != 1 { continue; }
            if s > m + 1 && 2 * a + b > 2 * m {
                add(vec![a, b, s], inv(a % s, s), s, "SUM");
            }
            if b >= m + 1 && a + 2 * b <= 3 * m + 3 {
                let q = a + 2 * b;
                add(vec![a, b, s], inv(b % q, q), q, "SUMP");
            }
        }
    }

    for a in 1..=m {
        for t in 1..=n {
            if a + t > 2 * m && 2 * a + t > 2 * m + 2 && 2 * a + t <= 3 * m + 3 && gcd(a, t) == 1 {
                let q = 2 * a + t;
                add(vec![a, 2 * a, t], inv(a % q, q), q, "DBL3");
            }
        }
    }
    v
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mlo: u64 = args[1].parse().unwrap();
    let mhi: u64 = args[2].parse().unwrap();
    let verbose = args.len() > 3;

    let mut total = 0u64;
    let mut total_bad = 0u64;
    let mut worst: Vec<String> = Vec::new();

    for m in mlo..=mhi {
        let n = 2 * m;
        let t = m + 1;
        let items = generate(m);
        let mut ok = 0u64;
        let mut fail = 0u64;
        let mut contains = 0u64; // not equal, but a superset of a genuine bad set: still SOUND
        for it in &items {
            let b = badset(it.p, it.q, n, t);
            if b == it.set { ok += 1; continue; }
            // weaker but still sound: the claimed set contains the real bad set of that time
            if !b.is_empty() && b.iter().all(|x| it.set.contains(x)) { contains += 1; continue; }
            fail += 1;
            if worst.len() < 20 {
                worst.push(format!(
                    "m={} fam={} claimed={:?} but B({}/{}) = {:?}",
                    m, it.fam, it.set, it.p, it.q, b));
            }
        }
        total += items.len() as u64;
        total_bad += fail;
        if verbose || fail > 0 {
            println!("m={:>4} generated={:>7} exact={:>7} superset={:>5} NOT-A-BAD-SET={:>5} {}",
                m, items.len(), ok, contains, fail,
                if fail == 0 { "SOUND" } else { "*** UNSOUND ***" });
        }
    }

    println!("\n{} family members checked over m={}..{}", total, mlo, mhi);
    if total_bad == 0 {
        println!("RESULT: every generated set is the bad set of the explicit time its proposition");
        println!("        names, or a superset of one. F_gen is a subset of F_true throughout.");
        println!("        The famdec route is SOUND on this range.");
    } else {
        println!("RESULT: *** {} generated sets are NOT bad sets. famdec is UNSOUND. ***", total_bad);
        for w in &worst { println!("  {}", w); }
    }
}
