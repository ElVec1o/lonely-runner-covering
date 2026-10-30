#[path = "../mlcore.rs"]
#[allow(dead_code)]
mod mls;
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let lo: u64 = a[1].parse().unwrap(); let hi: u64 = a[2].parse().unwrap();
    let mumax: u64 = a[3].parse().unwrap();
    let mut ncls = 0; let mut bad = 0;
    for n in lo..=hi { for s in 4..n { let r = n - s;
        if r < 2 { continue; }
        for mu in 2..=mumax {
            // GW criterion
            if mu * s > r + 1 { continue; }
            if !(s..mu * s).all(|b| gcd(r, b) > 1) { continue; }
            let cls = gcd(r, n - 1) == 1;
            let mut v: Vec<u64> = (1..n).filter(|&x| x != r).collect(); v.push(mu * r);
            let (m0, _) = mls::ml(&v);
            let mut best = (u128::MAX, 1u128, 0u64); // value as fraction
            let mut second = (u128::MAX, 1u128, 0u64);
            let mut tied = 0;
            let mut arg = 0u64;
            for i in 0..v.len() {
                let mut w = v.clone(); let d = w.remove(i);
                let (x, _) = mls::ml(&w);
                // compare x < best
                if best.0 == u128::MAX || x.0 * best.1 < best.0 * x.1 { second = best; best = (x.0, x.1, d); arg = d; tied = 0; }
                else if x.0 * best.1 == best.0 * x.1 { tied += 1; }
                else if second.0 == u128::MAX || x.0 * second.1 < second.0 * x.1 { second = (x.0, x.1, d); }
            }
            let tight = m0.0 == 1 && m0.1 == n as u128;
            let (exp_n, exp_d, exp_arg) = if cls { (1u128, (n - 2) as u128, (n - 2)) } else { (1u128, (n - 1) as u128, (n - 1)) };
            let ok = tight && best.0 * exp_d == exp_n * best.1 && arg == exp_arg && tied == 0;
            if cls { ncls += 1; }
            if !ok { bad += 1; }
            println!("{} n={} r={} s={} mu={} MLV={}/{} loo={}/{} argmin={} tied={} second={}/{}@{} ratio2={:.6}",
                if cls {"CLASSC"} else {"CONTROL"}, n, r, s, mu, m0.0, m0.1, best.0, best.1, arg, tied, second.0, second.1, second.2,
                (second.0 as f64 / second.1 as f64) / (best.0 as f64 / best.1 as f64));
            if !ok { println!("FAIL {} n={} r={} mu={}", if cls {"CLASSC"} else {"CONTROL"}, n, r, mu); }
        }
    }}
    println!("DONE classC={} bad={}", ncls, bad);
}
