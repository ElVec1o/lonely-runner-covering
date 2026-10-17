// fb: exact checker for the fractional blocking certificates of Table "tab:frac" in
// paper/dense-window/main.tex.  Standard library only, exact u64 integer arithmetic.
//
// Usage:  fb check LEANFILE      parse the certificates dense_floor_m4,m7,m12,m13 out of
//                                lean/LRSpectrumFull/Delta2FracBlocking.lean and verify them
//         fb selftest LEANFILE   negative controls (certificates perturbed; all must be rejected)
//
// Definitions (units in brackets).  Certificate for m = k+1 velocities: times p_j/q_j [dimensionless],
// weights y_j [natural numbers, scaled by D].  x in [1,2m] is "good" at p/q iff
//   q <= (k+2) * min(x p mod q, q - x p mod q)        (equivalent to  dist(x p/q, Z) >= 1/(m+1)).
// load(x) = sum of y_j over times at which x is NOT good.  The certificate is valid iff
// q_j > 0 for all j, load(x) <= D for every x in [1,2m], and (k+1) D < sum_j y_j.
// Total weight reported as a fraction  sum_j y_j / D.
use std::fs;

struct Cert { name: String, k: u64, p: Vec<u64>, q: Vec<u64>, y: Vec<u64>, d: u64 }

fn good_at(k: u64, x: u64, p: u64, q: u64) -> bool {
    let r = (x * p) % q; q <= (k + 2) * r.min(q - r)
}
fn vec_after(s: &str, open: &str) -> Option<(Vec<u64>, usize)> {
    let a = s.find(open)? + open.len(); let b = a + s[a..].find(']')?;
    let v = s[a..b].split(',').map(|t| t.trim().parse().unwrap()).collect(); Some((v, b + 1))
}
fn parse(path: &str) -> Vec<Cert> {
    let txt = fs::read_to_string(path).expect("read lean file"); let mut out = vec![]; let mut pos = 0;
    while let Some(i) = txt[pos..].find("theorem dense_floor_m") {
        let s = pos + i; let e = txt[s + 1..].find("theorem ").map(|j| s + 1 + j).unwrap_or(txt.len());
        let blk = &txt[s..e]; pos = e.min(txt.len()); if e == txt.len() { pos = txt.len(); }
        let name: String = blk["theorem ".len()..].chars().take_while(|c| !c.is_whitespace()).collect();
        let kpos = blk.find("(k := ").expect("k") + 6; let k: u64 = blk[kpos..].chars().take_while(|c| c.is_ascii_digit()).collect::<String>().parse().unwrap();
        let rest = &blk[blk.find("floor_of_frac_blocking").unwrap()..];
        let (p, a) = vec_after(rest, "![").unwrap(); let (q, b) = vec_after(&rest[a..], "![").unwrap();
        let (y, c) = vec_after(&rest[a + b..], "![").unwrap();
        let tail = &rest[a + b + c..]; let dp = tail.find("(by decide)").unwrap() + 11;
        let d: u64 = tail[dp..].trim_start().chars().take_while(|c| c.is_ascii_digit()).collect::<String>().parse().unwrap();
        out.push(Cert { name, k, p, q, y, d });
        if pos >= txt.len() { break; }
    }
    out
}
// returns (valid, maxload, sumy)
fn verify(c: &Cert, k: u64) -> (bool, u64, u64) {
    let n = c.p.len(); assert!(c.q.len() == n && c.y.len() == n);
    if c.q.iter().any(|&q| q == 0) { return (false, 0, 0); }
    let m = k + 1; let mut maxload = 0;
    for x in 1..=2 * m { let l: u64 = (0..n).filter(|&j| !good_at(k, x, c.p[j], c.q[j])).map(|j| c.y[j]).sum(); maxload = maxload.max(l); }
    let sum: u64 = c.y.iter().sum();
    (maxload <= c.d && m * c.d < sum, maxload, sum)
}
fn main() {
    let a: Vec<String> = std::env::args().collect(); if a.len() < 3 { eprintln!("usage: fb check|selftest FILE"); std::process::exit(2); }
    let certs = parse(&a[2]);
    match a[1].as_str() {
        "check" => {
            println!("name\tm\t2m+1\ttimes\tD\tmaxload\tsum_y\ttotal_weight(sum_y/D)\tm\tverdict");
            let mut allok = true;
            for c in &certs { let (ok, ml, s) = verify(c, c.k); allok &= ok;
                println!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}/{}\t{}\t{}", c.name, c.k + 1, 2 * (c.k + 1) + 1, c.p.len(), c.d, ml, s, s, c.d, c.k + 1, if ok { "ACCEPT" } else { "REJECT" }); }
            println!("certificates found: {}; all accepted: {}", certs.len(), allok);
            if !allok || certs.len() != 4 { std::process::exit(1); }
        }
        "selftest" => {
            let mut bad = 0;
            for c in &certs {
                // control 1: drop the heaviest time (weight set to 0); sum falls, expect REJECT if sum - y_max <= m D
                // control 2: reduce D by one; expect REJECT (a load equals D somewhere or the sum test fails)
                // control 3: use the certificate at the wrong size k+1 (m+1 velocities); expect REJECT
                // control 4: scale all weights by 0 (empty certificate); expect REJECT
                let mut c1 = Cert { name: c.name.clone(), k: c.k, p: c.p.clone(), q: c.q.clone(), y: c.y.clone(), d: c.d };
                let jm = (0..c1.y.len()).max_by_key(|&j| c1.y[j]).unwrap(); let before = c1.y.iter().sum::<u64>(); c1.y[jm] = 0;
                let exp1 = !((c.k + 1) * c.d < before - c.y[jm]); // expected reject iff remaining sum <= mD
                let (ok1, _, _) = verify(&c1, c1.k);
                let mut c2 = Cert { name: c.name.clone(), k: c.k, p: c.p.clone(), q: c.q.clone(), y: c.y.clone(), d: c.d.saturating_sub(1) };
                let (ok2, ml2, _) = verify(&mut c2, c.k); let exp2_reject = ml2 > c2.d || !((c.k + 1) * c2.d < c2.y.iter().sum::<u64>());
                let (ok3, _, _) = verify(c, c.k + 1);
                let c4 = Cert { name: c.name.clone(), k: c.k, p: c.p.clone(), q: c.q.clone(), y: vec![0; c.y.len()], d: c.d };
                let (ok4, _, _) = verify(&c4, c.k);
                println!("{}: ctrl1 drop heaviest -> {} (expected {}), ctrl2 D-1 -> {}, ctrl3 wrong size -> {}, ctrl4 zero weights -> {}", c.name,
                    if ok1 { "ACCEPT" } else { "REJECT" }, if exp1 { "REJECT" } else { "ACCEPT" }, if ok2 { "ACCEPT" } else { "REJECT" }, if ok3 { "ACCEPT" } else { "REJECT" }, if ok4 { "ACCEPT" } else { "REJECT" });
                if ok1 == exp1 { bad += 1; } if ok2 && exp2_reject { bad += 1; } if ok3 || ok4 { bad += 1; }
                if ok2 { bad += 1; } // D-1 must not be accepted for these four certificates (see report)
            }
            println!("selftest failures: {}", bad); if bad > 0 { std::process::exit(1); }
        }
        _ => { eprintln!("unknown"); std::process::exit(2); }
    }
}
