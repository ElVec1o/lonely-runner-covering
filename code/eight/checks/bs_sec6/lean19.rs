// falsify the EXACT Lean statements for BarajasSerraSec6_5 / Sec6_6 / Sec6_3.
// Mirrors Lean: nu 0 = 0, rp x = (x / 7^nu x) % 7, qq x = ((x % N) / 7^m) % 7, E x y = dsub N x y.
use std::env;
fn nu(x: u64) -> u32 { if x == 0 { return 0; } let mut x = x; let mut v = 0; while x % 7 == 0 { x /= 7; v += 1; } v }
fn rp(x: u64) -> u64 { (x / 7u64.pow(nu(x))) % 7 }
#[derive(Clone, Copy)]
struct P { n: u64, m: u32, pm: u64 }
impl P {
    fn q(&self, x: u64) -> u64 { ((x % self.n) / self.pm) % 7 }
    fn e(&self, x: u64, y: u64) -> u64 { (x % self.n + (self.n - y % self.n)) % self.n }
    fn et(&self, x: u64, y: u64) -> u64 {
        if rp(y) == 2 * rp(x) % 7 { (2 * self.q(x) + 14 - self.q(y)) % 7 } else if rp(x) == 2 * rp(y) % 7 { (2 * self.q(y) + 14 - self.q(x)) % 7 } else { (self.q(x) + 7 - self.q(y)) % 7 }
    }
    fn lam(&self, i: u32, k: u64) -> u64 { 1 + 7u64.pow(self.m - i) * k }
    fn avoid(&self, l: u64, ds: &[u64]) -> bool { ds.iter().all(|&d| { let v = self.q(l * d % self.n); v != 0 && v != 6 }) }
}
fn ok7(v: i64) -> bool { let v = v.rem_euclid(7); v != 0 && v != 6 }
fn main() {
    let args: Vec<String> = env::args().collect();
    let which = args.get(1).map(|s| s.as_str()).unwrap_or("all");
    // ---------- pure Z7 claims ----------
    if which == "all" || which == "z7" {
        // window pair finish, mu = 1,2,3
        for (mu, oset) in [(1i64, vec![5i64, 6, 0, 1, 2]), (2, vec![5, 6, 0, 1, 2]), (3, vec![6, 0, 1])] {
            let mut fail = 0; let mut nc = 0;
            for a in 0..7i64 { for g1 in 0..=mu { for g2 in 0..=mu { for p in 0..7i64 { for o in 0..7i64 {
                let good = (0..7i64).any(|k| ok7(a + k) && ok7(a + g1 + k) && ok7(a + g2 + k) && ok7(p + 4 * k) && ok7(p + o + 4 * k));
                if oset.contains(&o) { if !good { fail += 1; } } else if !good { nc += 1; }
            } } } } }
            println!("z65w mu={} fail={} | NC(o outside set) fails={}", mu, fail, nc);
        }
        // top offsets {0,1,2} and {0,1,5}, A4 offset o
        for off in [[0i64, 1, 2], [0, 1, 5], [0, 2, 4]] {
            let mut bad = vec![];
            for o in 0..7i64 { let mut allok = true; for a in 0..7i64 { for p in 0..7i64 {
                if !(0..7i64).any(|k| off.iter().all(|&x| ok7(a + x + k)) && ok7(p + 4 * k) && ok7(p + o + 4 * k)) { allok = false; } } }
                if !allok { bad.push(o); } }
            println!("top A1 offsets {:?}: A4 offsets o failing for some (a,p): {:?}", off, bad);
        }
        // (b): A1 {0,1,2}, A4 {p, p+4}; bad values of e = 2p - a
        for (off, o) in [([0i64, 1, 2], 4i64), ([0, 2, 4], 1)] {
            let mut bad = std::collections::BTreeSet::new();
            for a in 0..7i64 { for p in 0..7i64 {
                if !(0..7i64).any(|k| off.iter().all(|&x| ok7(a + x + k)) && ok7(p + 4 * k) && ok7(p + o + 4 * k)) { bad.insert((2 * p - a).rem_euclid(7)); } } }
            // consistency: is the failure a function of e only?
            let mut incons = 0;
            for a in 0..7i64 { for p in 0..7i64 { let e = (2 * p - a).rem_euclid(7);
                let g = (0..7i64).any(|k| off.iter().all(|&x| ok7(a + x + k)) && ok7(p + 4 * k) && ok7(p + o + 4 * k));
                if g == bad.contains(&e) { incons += 1; } } }
            println!("(b) A1 {:?}, A4 offset {}: bad e = {:?}, inconsistent (a,p) = {}", off, o, bad, incons);
        }
    }
    for m in [2u32, 3] {
        let pm = 7u64.pow(m); let n = pm * 7; let p = P { n, m, pm };
        let units: Vec<u64> = (1..n).filter(|v| v % 7 != 0).collect();
        // range lemma: v < N -> q(v) in {0,1,5,6} or q(2v) in {5,6,0,1} or q(3v) in {6,0}
        if which == "all" || which == "range" {
            let mut fail = 0; let mut nc = 0;
            for v in 0..n { let a = [0, 1, 5, 6].contains(&p.q(v)); let b = [5, 6, 0, 1].contains(&p.q(2 * v)); let c = [6, 0].contains(&p.q(3 * v));
                if !(a || b || c) { fail += 1; } if !(a || b) { nc += 1; } }
            println!("m={} range lemma fail={} | NC(no mu=3) fail={}", m, fail, nc);
        }
        // window pair trick: Wb b1 b2 c (E(bi,c) <= M), d4,d5 class 4 -> some mu in {1,2,3} and Lambda0 finish
        if which == "all" || which == "trick" {
            let c1: Vec<u64> = (0..n).filter(|v| v % 7 == 1).collect();
            let c4: Vec<u64> = (0..n).filter(|v| v % 7 == 4).collect();
            let step = if m == 2 { 1 } else { 7 };
            let (mut cnt, mut fail, mut nc) = (0u64, 0u64, 0u64);
            for &c in c1.iter().step_by(step) { for i in 0..=1u64 { for j in 0..=1u64 {
                // window elements: c + 7 * t with 7t <= M; sample the two extremes and middles
                for dl1 in (0..=pm).step_by(7) { for dl2 in (0..=pm).step_by(7) { if m == 3 && (dl1 % 49 != 0 || dl2 % 98 != 0) { continue; }
                let b1 = (c + dl1 * i) % n; let b2 = (c + dl2 * j) % n; let _ = (b1, b2);
                for &d4 in c4.iter().step_by(step) { for &d5 in &c4 {
                    let ds = [c, b1, b2, d4, d5]; cnt += 1;
                    let ok = [1u64, 2, 3].iter().any(|&mu| (0..7).any(|k| p.avoid(p.lam(0, k) * mu % n, &ds)));
                    if !ok { fail += 1; }
                    let ok1 = [1u64].iter().any(|&mu| (0..7).any(|k| p.avoid(p.lam(0, k) * mu % n, &ds)));
                    if !ok1 { nc += 1; }
                } } } } } } }
            println!("m={} window pair trick: {} configs fail={} | NC(mu = 1 only) fail={}", m, cnt, fail, nc);
        }
        // 6.5 (ii.2) h<m, nu(e45)=h: claim q(lam e45) in {5,6,0,1} after step(f) then T3 multiplier
        if which == "all" || which == "l9" {
            let t3 = |s: u64| -> u64 { if s == 0 || s == 2 { 0 } else if s == 3 || s == 5 { 5 } else { 6 } };
            let (mut cnt, mut fail, mut fl3) = (0u64, 0u64, 0u64);
            for h in 1..m { let ph = 7u64.pow(h);
                for x0 in 1..7u64 { for qa in 0..(n / ph / 7) { // x = ph*(x0 + 7 qa) level h
                    let x = ph * (x0 + 7 * qa) % n; let y0 = 3 * x0 % 7;
                    for qb in 0..(n / ph / 7) { let y = ph * (y0 + 7 * qb) % n;
                        for sgn in 0..1 { let _ = sgn;
                        for qc in 0..(n / ph / 7) { let e45 = ph * (y0 + 7 * qc) % n; // R(e45) = R(y)
                            if m == 3 && (qa + qb + qc) % 5 != 0 { continue; }
                            cnt += 1;
                            let f = p.e(e45, y);
                            // lam1: f=0 -> 1; nu(f)<m -> Lam_{nu f} with q=0; nu(f)=m -> LamTop l with l*w=1
                            let lam1: u64 = if f == 0 { 1 } else if nu(f) < m { let j = nu(f); (0..7).map(|k| p.lam(j, k)).find(|&l| p.q(l * f % n) == 0).unwrap() } else { let w = f / pm; (1..7).find(|l| l * w % 7 == 1).unwrap() };
                            let (x1, y1, e1) = (lam1 * x % n, lam1 * y % n, lam1 * e45 % n);
                            let s = (3 * p.q(y1) + 5 * p.q(x1)) % 7;
                            let lam2 = (0..7).map(|k| p.lam(h, k)).find(|&l| p.q(l * y1 % n) == t3(s)).unwrap();
                            let qe = p.q(lam2 * e1 % n);
                            if ![5, 6, 0, 1].contains(&qe) { fail += 1; }
                            // also the 9(ii) j=3 difference claims
                            let (qx, qy) = (p.q(lam2 * x1 % n), p.q(lam2 * y1 % n));
                            let d = (qy + 7 - qx) % 7;
                            if !([0, 5, 6].contains(&qy) && (qx <= 1 || qx >= 5) && (d <= 1 || d == 6)) { fl3 += 1; }
                        } } } } } }
            println!("m={} 6.5(ii.2) nu(e45)=h: {} configs, q(lam e45) notin {{5,6,0,1}}: {}, lemma9-three diff claims fail: {}", m, cnt, fail, fl3);
        }
        if m == 2 && (which == "all" || which == "sub") {
            let c1: Vec<u64> = (0..n).filter(|v| v % 7 == 1).collect();
            let c2: Vec<u64> = (0..n).filter(|v| v % 7 == 2).collect();
            let c4: Vec<u64> = (0..n).filter(|v| v % 7 == 4).collect();
            let lam0: Vec<u64> = (0..7).map(|k| p.lam(0, k)).collect();
            let k = c1.len();
            // 6.5: A1 three of class 1, A4 two of class 4
            let (mut cnt, mut fail, mut nc) = (0u64, 0u64, 0u64);
            for a in 0..k { for b in a..k { for cc in b..k { for x in 0..k { for y in x..k {
                let ds = [c1[a], c1[b], c1[cc], c4[x], c4[y]]; cnt += 1;
                if !units.iter().any(|&l| p.avoid(l, &ds)) { fail += 1; }
                if !lam0.iter().any(|&l| p.avoid(l, &ds)) { nc += 1; }
            } } } } }
            println!("m={} 6.5: {} fail={} | NC(Lambda0 only) fail={}", m, cnt, fail, nc);
            // 6.6: A1 two of class 1, A2 two of class 2, A4 one of class 4
            let (mut cnt, mut fail, mut nc) = (0u64, 0u64, 0u64);
            for a in 0..k { for b in a..k { for x in 0..k { for y in x..k { for z in 0..k {
                let ds = [c1[a], c1[b], c2[x], c2[y], c4[z]]; cnt += 1;
                if !units.iter().any(|&l| p.avoid(l, &ds)) { fail += 1; }
                if !lam0.iter().any(|&l| p.avoid(l, &ds)) { nc += 1; }
            } } } } }
            println!("m={} 6.6: {} fail={} | NC(Lambda0 only) fail={}", m, cnt, fail, nc);
            // 6.3: A1 three of class 1, one of class 2, one of class 4
            let (mut cnt, mut fail, mut nc) = (0u64, 0u64, 0u64);
            for a in 0..k { for b in a..k { for cc in b..k { for x in 0..k { for z in 0..k {
                let ds = [c1[a], c1[b], c1[cc], c2[x], c4[z]]; cnt += 1;
                if !units.iter().any(|&l| p.avoid(l, &ds)) { fail += 1; }
                if !lam0.iter().any(|&l| p.avoid(l, &ds)) { nc += 1; }
            } } } } }
            println!("m={} 6.3: {} fail={} | NC(Lambda0 only) fail={}", m, cnt, fail, nc);
        }
    }
}
