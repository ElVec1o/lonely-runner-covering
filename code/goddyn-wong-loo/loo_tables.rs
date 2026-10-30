// loo_tables.rs: exact leave-one-out values for the vectors V = ([n-1] \ {r}) U {mu r}.
// ML is computed by ml() of mlcore.rs (exact, every numerator k of k/(v_i+v_j)).
// Usage: loo_tables selftest
//        loo_tables example            n=8, r=6, mu=2: ML(V) and every deletion
//        loo_tables thmA               even r = 4..32, 2 <= mu <= r-1: loo = mu/(mu r+1), unique minimiser r+1
//        loo_tables triples NMAX       all (n,r,mu) with mu >= 2 satisfying criterion (1), n <= NMAX: all deletions
//        loo_tables vec n r mu         one vector, all deletions
include!("mlcore.rs");
use std::env;
fn red(a: U, b: U) -> (U, U) { let g = gcd(a, b).max(1); (a / g, b / g) }
fn vecv(n: u64, r: u64, mu: u64) -> Vec<u64> { let mut v: Vec<u64> = (1..n).filter(|&x| x != r).collect(); v.push(mu * r); v }
fn ml_of(v: &[u64]) -> (U, U) { ml(v).0 }
fn loo(v: &[u64]) -> Vec<(U, U)> {
    (0..v.len()).map(|i| { let mut w = v.to_vec(); w.remove(i); ml_of(&w) }).collect()
}
fn eqf(a: (U, U), b: (U, U)) -> bool { a.0 * b.1 == b.0 * a.1 }
fn lt(a: (U, U), b: (U, U)) -> bool { a.0 * b.1 < b.0 * a.1 }
fn fs(a: (U, U)) -> String { format!("{}/{}", a.0, a.1) }
fn crit1(n: u64, r: u64, mu: u64) -> bool { let s = n - r; (s..mu * s).all(|b| gcd(r as U, b as U) > 1) }
fn main() {
    let a: Vec<String> = env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("selftest") => {
            let c: Vec<(Vec<u64>, (U, U))> = vec![
                ((1..=5).collect(), (1, 6)), (vec![7, 19], (1, 2)), (vec![3, 4, 7, 11], (2, 9)),
                (vec![1, 3, 4, 7], (1, 5)), (vec![1, 5, 6, 11, 16, 17], (5, 33)),
                (vec![1, 4, 6, 7, 10, 11, 12, 13, 16, 17, 19, 23], (1, 9))];
            let mut ok = true;
            for (v, e) in &c { let g = ml_of(v); let good = eqf(g, *e); ok &= good; println!("{:?} ML={} expected {} {}", v, fs(g), fs(*e), if good { "ok" } else { "MISMATCH" }); }
            println!("{}", if ok { "SELFTEST PASS" } else { "SELFTEST FAIL" });
            if !ok { std::process::exit(1); }
        }
        Some("example") | Some("vec") => {
            let (n, r, mu): (u64, u64, u64) = if a[1] == "example" { (8, 6, 2) } else { (a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap()) };
            let v = vecv(n, r, mu);
            println!("n={} r={} mu={} V={:?} criterion(1)={}", n, r, mu, v, crit1(n, r, mu));
            println!("ML(V)={}", fs(ml_of(&v)));
            let l = loo(&v);
            for (i, x) in v.iter().enumerate() { println!("delete {:>3}: ML={}", x, fs(l[i])); }
            let mn = *l.iter().fold(&l[0], |m, x| if lt(*x, *m) { x } else { m });
            println!("loo={} attained at {:?}", fs(mn), v.iter().enumerate().filter(|(i, _)| eqf(l[*i], mn)).map(|(_, x)| *x).collect::<Vec<_>>());
        }
        Some("thmA") => {
            let (mut tot, mut bad) = (0, 0);
            for r in (4..=32u64).step_by(2) { for mu in 2..r {
                let mut v: Vec<u64> = (1..r).collect(); v.push(r + 1); v.push(mu * r);
                let l = loo(&v); let c = red(mu as U, (mu * r + 1) as U); tot += 1;
                let mn = *l.iter().fold(&l[0], |m, x| if lt(*x, *m) { x } else { m });
                let arg: Vec<u64> = v.iter().enumerate().filter(|(i, _)| eqf(l[*i], mn)).map(|(_, x)| *x).collect();
                if !(eqf(mn, c) && arg == vec![r + 1]) { bad += 1; println!("MISMATCH r={} mu={} loo={} argmin={:?}", r, mu, fs(mn), arg); }
            }}
            println!("even r in 4..32, all 2<=mu<=r-1: {} vectors; mismatches {}", tot, bad);
        }
        Some("triples") => {
            let nmax: u64 = a[2].parse().unwrap(); let mut bad = 0;
            for n in 4..=nmax { for r in 2..n - 1 { let s = n - r;
                let mut mu = 2u64;
                while crit1(n, r, mu) {
                    let v = vecv(n, r, mu); let m = n - 1; let g = gcd(r as U, (n - 1) as U);
                    let full = ml_of(&v); let l = loo(&v);
                    let mn = *l.iter().fold(&l[0], |x, y| if lt(*y, *x) { y } else { x });
                    let arg: Vec<u64> = v.iter().enumerate().filter(|(i, _)| eqf(l[*i], mn)).map(|(_, x)| *x).collect();
                    let inv_m = (1 as U, m as U);
                    let (pred, parg): (Option<(U, U)>, Option<Vec<u64>>) = if s == 2 { (Some(red(mu as U, (mu * (m - 1) + 1) as U)), Some(vec![n - 1])) } else if g > 1 { (Some(inv_m), Some(vec![n - 1])) } else { (None, None) };
                    let mut ok = eqf(mn, inv_m) == (g > 1) && !lt(mn, inv_m);
                    if let (Some(p), Some(pa)) = (pred, &parg) { ok = ok && eqf(mn, p) && &arg == pa; }
                    if g > 1 { ok = ok && l.iter().filter(|x| eqf(**x, inv_m)).count() == 1; }
                    if !ok { bad += 1; }
                    println!("{} {} {} s={} gcd={} ML(V)={} loo={} argmin={:?} pred={} {}", n, r, mu, s, g, fs(full), fs(mn), arg,
                        match pred { Some(p) => fs(p), None => "None".to_string() }, if ok { "OK" } else { "FAIL" });
                    mu += 1;
                }
            }}
            println!("FAILS {}", bad);
        }
        _ => { eprintln!("usage: loo_tables selftest | example | thmA | triples NMAX | vec n r mu"); std::process::exit(2); }
    }
}
