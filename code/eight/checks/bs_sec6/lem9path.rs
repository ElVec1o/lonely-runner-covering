// simulate the PAPER'S PROOF PATH of Lemma 9 (i), (ii) (not just existence), exact integers.
// x = b1 - b3, y = b2 - b3 (residues mod N). q, nu, r on residues; nu(0) treated as "none".
fn nu(x: u64) -> u32 { if x == 0 { return 99; } let mut x = x; let mut v = 0; while x % 7 == 0 { x /= 7; v += 1; } v }
fn rr(x: u64) -> u64 { if x == 0 { return 0; } let mut x = x; while x % 7 == 0 { x /= 7; } x % 7 }
fn ellm(s: u32) -> u32 { if s == 0 { return 0; } let mut best = 8; for st in 0..7 { for l in 1..=7u32 { let mut iv = 0u32; for t in 0..l { iv |= 1 << ((st + t) % 7); } if s & !iv == 0 && l < best { best = l; } } } best }
fn main() {
    for m in [2u32, 3] {
        let n = 7u64.pow(m + 1); let pm = 7u64.pow(m);
        let q = |x: u64| (x % n) / pm;
        let sub = |a: u64, b: u64| (a % n + n - b % n) % n;
        let lam = |h: u32, k: u64| (1 + 7u64.pow(m - h) * k) % n;
        let ellb = |l: u64, b: &[u64; 3]| { let mut s = 0u32; for &v in b { s |= 1 << q(l * v % n); } ellm(s) };
        // steer: level-h element z, find k with q(lam(h,k) z) = t
        let steer = |h: u32, z: u64, t: u64| -> Option<u64> { (0..7).map(|k| lam(h, k)).find(|&l| q(l * z % n) == t) };
        let (mut c2, mut f2ell, mut f2y, mut f2yx, mut f2et, mut c3, mut f3ell, mut f3y, mut c1, mut f1) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
        let mut ex: Vec<String> = vec![];
        let step = if m == 2 { 1 } else { 3 };
        let units: Vec<u64> = (1..n).filter(|v| v % 7 == 1).collect(); // class 1 (others by scaling)
        for (i3, &b3) in units.iter().enumerate() { if i3 % step != 0 { continue; } for &b1 in &units { if b1 == b3 { continue; } for &b2 in &units { if b2 == b3 || b2 == b1 { continue; }
            let b = [b1, b2, b3];
            let x = sub(b1, b3); let y = sub(b2, b3);
            let (vx, vy) = (nu(x), nu(y));
            if vx != vy {
                // (i): WLOG higher level first
                let (hi, lo) = if vx > vy { (x, y) } else { (y, x) };
                let vh = nu(hi); let vl = nu(lo);
                c1 += 1;
                let l1 = if vh < m { steer(vh, hi, 0).unwrap() } else { (1..7u64).find(|&l| q(l * hi % n) == 1).unwrap() };
                let l2 = steer(vl, l1 * lo % n, 0).unwrap();
                let l = l2 * l1 % n;
                if ellb(l, &b) > 2 { f1 += 1; }
                continue;
            }
            let h = vx; if h >= m { continue; }
            let (rx, ry) = (rr(x), rr(y));
            if ry == 2 * rx % 7 {
                c2 += 1;
                let e = sub(2 * x, y); let ve = nu(e);
                let l1 = if e == 0 { 1 } else if ve < m { steer(ve, e, 0).unwrap() } else { (1..7u64).find(|&l| q(l * e % n) == 1).unwrap() };
                let (lx, ly) = (l1 * x % n, l1 * y % n);
                let et = (2 * q(lx) + 14 - q(ly)) % 7;
                if !(et == 0 || et == 1 || et == 6) { f2et += 1; }
                let t = if et == 6 { 6 } else { 0 };
                let l2 = steer(h, lx, t).unwrap();
                let l = l2 * l1 % n;
                if ellb(l, &b) > 2 { f2ell += 1; if ex.len() < 5 { ex.push(format!("m={} b={:?} x={} y={} e={} l1={} l={} q(lb)={:?} et={}", m, b, x, y, e, l1, l, b.iter().map(|&v| q(l * v % n)).collect::<Vec<_>>(), et)); } }
                let qy = q(l * y % n); if !(qy == 0 || qy == 5 || qy == 6) { f2y += 1; }
                let qyx = q(l * sub(y, x) % n); if !(qyx == 0 || qyx == 6) { f2yx += 1; }
            } else if ry == 3 * rx % 7 {
                c3 += 1;
                let s = (3 * q(y) + 5 * q(x)) % 7;
                let t = match s { 0 | 2 => 0, 1 | 4 | 6 => 6, _ => 5 };
                let l = steer(h, y, t).unwrap();
                if ellb(l, &b) > 3 { f3ell += 1; }
                let qy = q(l * y % n); let qx = q(l * x % n);
                if !(qy == 0 || qy == 5 || qy == 6) || !(qx == 0 || qx == 1 || qx == 5 || qx == 6) || !((qy + 7 - qx) % 7 == 0 || (qy + 7 - qx) % 7 == 1 || (qy + 7 - qx) % 7 == 6) { f3y += 1; }
            }
        } } }
        println!("m={} (i) path: {} cases, ell>2: {}", m, c1, f1);
        println!("m={} (ii) j=2 path: {} cases, et not in {{0,1,6}}: {}, ell>2: {}, q(ly) not in {{0,5,6}}: {}, q(l(y-x)) not in {{0,6}}: {}", m, c2, f2et, f2ell, f2y, f2yx);
        println!("m={} (ii) j=3 path: {} cases, ell>3: {}, table claims fail: {}", m, c3, f3ell, f3y);
        for s in &ex { println!("  {}", s); }
    }
}
