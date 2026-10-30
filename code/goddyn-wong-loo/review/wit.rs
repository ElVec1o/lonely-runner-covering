fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn main() {
    // prime window check
    let lim: usize = 20_000_000;
    let mut comp = vec![false; lim + 1]; let mut pi = vec![0u32; lim + 1];
    comp[0] = true; comp[1] = true;
    let mut i = 2; while i * i <= lim { if !comp[i] { let mut j = i * i; while j <= lim { comp[j] = true; j += i; } } i += 1; }
    let mut c = 0; for k in 0..=lim { if !comp[k] { c += 1; } pi[k] = c; }
    let (mut mn, mut mnn, mut lastfail) = (u32::MAX, 0, 0);
    for n in 33..=10_000_000usize { let cnt = pi[2 * n - 5] - pi[(3 * n) / 2]; if cnt < mn { mn = cnt; mnn = n; } if cnt < 3 { lastfail = n; } }
    println!("window (floor(1.5n),2n-5], n in [33,1e7]: min count {} at n={}, last n with <3: {}", mn, mnn, lastfail);
    for n in 28..=34usize { println!(" n={} count={}", n, pi[2 * n - 5] - pi[(3 * n) / 2]); }
    // witness checks
    let (mut tot, mut bad) = (0u64, 0u64);
    for n in 33u64..=260 { for s in 4..n { let r = n - s; if r < 2 { continue; }
        for mu in 2u64..=20 { if mu * s > r + 1 { continue; } if gcd(r, n - 1) != 1 { continue; }
            let mut v: Vec<u64> = (1..n).filter(|&x| x != r).collect(); v.push(mu * r);
            let q = n - 2;
            // R4 with u = n-2
            for &j in &v { if 2 * j > n && j <= n - 2 && (mu * r) % j == 0 {
                let u = n - 2; let dd: u128 = j as u128 * 2 * (mu as u128).pow(2) * u as u128 * r as u128;
                let num: u128 = 2 * (mu as u128).pow(2) * u as u128 * r as u128 + j as u128 * (2 * mu as u128 + 1);
                for &x in &v { if x == j { continue; } tot += 1;
                    let rem = (x as u128 * num) % dd; let d = rem.min(dd - rem);
                    if d * (q as u128) <= dd { bad += 1; println!("R4 FAIL n={} r={} mu={} j={} x={}", n, r, mu, j, x); } } } }
            // deletion of n-1
            let qq = 2 * r + s - 1;
            if gcd(r, qq) == 1 && 2 * mu < qq {
                let mut a = 0; for c in 1..qq { if (c * r) % qq == 1 { a = c; } }
                for &x in &v { if x == n - 1 { continue; } tot += 1; let rem = (x as u128 * a as u128) % qq as u128; let d = rem.min(qq as u128 - rem);
                    if d < 2 { bad += 1; println!("D FAIL n={} r={} mu={} x={}", n, r, mu, x); } }
            }
        } } }
    println!("witness checks total {} bad {}", tot, bad);
}
