// falsify the EXACT Lean statements of BarajasSerraSec6 (Lemma 4 corrected, Lemma 7).
// Mirrors Lean: nu = padicValNat 7 (nu 0 = 0), rp x = (x / 7^nu x) % 7 (rp 0 = 0),
// qarc x = ((x % N) / 7^m) % 7, dsub N x y = (x%N + (N - y%N)) % N, branches of ediff/etilde in Lean order.
// Inputs x, y range over [0, 2N) (non-reduced and zero inputs included).
fn nu(x: u64) -> u32 { if x == 0 { return 0; } let mut x = x; let mut v = 0; while x % 7 == 0 { x /= 7; v += 1; } v }
fn rp(x: u64) -> u64 { (x / 7u64.pow(nu(x))) % 7 }
struct P { n: u64, m: u32, pm: u64 }
impl P {
    fn q(&self, x: u64) -> u64 { ((x % self.n) / self.pm) % 7 }
    fn dsub(&self, x: u64, y: u64) -> u64 { (x % self.n + (self.n - y % self.n)) % self.n }
    fn ediff(&self, x: u64, y: u64) -> u64 {
        if rp(y) == 2 * rp(x) % 7 { self.dsub(2 * x, y) } else if rp(x) == 2 * rp(y) % 7 { self.dsub(2 * y, x) } else { self.dsub(x, y) }
    }
    fn et(&self, x: u64, y: u64) -> u64 {
        if rp(y) == 2 * rp(x) % 7 { (2 * self.q(x) + 14 - self.q(y)) % 7 } else if rp(x) == 2 * rp(y) % 7 { (2 * self.q(y) + 14 - self.q(x)) % 7 } else { (self.q(x) + 7 - self.q(y)) % 7 }
    }
    fn lam(&self, i: u32, k: u64) -> u64 { 1 + 7u64.pow(self.m - i) * k }
}
fn ellm(s: u32) -> u32 { if s == 0 { return 0; } let mut best = 8; for st in 0..7 { for l in 1..=7u32 { let mut iv = 0u32; for t in 0..l { iv |= 1 << ((st + t) % 7); } if s & !iv == 0 && l < best { best = l; } } } best }
fn main() {
    for m in [2u32, 3] {
        let n = 7u64.pow(m + 1);
        let p = P { n, m, pm: 7u64.pow(m) };
        // Lemma 4 (ii): for all x != 0, y: et - q(ediff) in {6,0,1}; if rp x = rp y: in {0,1}
        let (mut c2, mut f2, mut f2eq) = (0u64, 0u64, 0u64);
        let lim = if m == 2 { 2 * n } else { n + 50 };
        for x in 1..lim { for y in 0..lim {
            c2 += 1;
            let d = (p.et(x, y) + 7 - p.q(p.ediff(x, y))) % 7;
            if !(d == 0 || d == 1 || d == 6) { f2 += 1; }
            if rp(x) == rp(y) && !(d == 0 || d == 1) { f2eq += 1; }
        } }
        println!("m={} L4(ii): {} pairs, fail={} fail(eq r, {{0,1}})={}", m, c2, f2, f2eq);
        // Lemma 4 (i): x,y != 0, nu x = nu y = j < m, related, i <= j, k < 7
        let (mut c1, mut f1) = (0u64, 0u64);
        for x in 1..lim { for y in 1..lim {
            let j = nu(x); if nu(y) != j || j >= m { continue; }
            let (rx, ry) = (rp(x), rp(y));
            if !(ry == rx || ry == 2 * rx % 7 || rx == 2 * ry % 7) { continue; }
            let e0 = p.et(x, y);
            for i in 0..=j { for k in 0..7 { c1 += 1; let l = p.lam(i, k); if p.et(l * x, l * y) != e0 { f1 += 1; } } }
        } }
        println!("m={} L4(i): {} (pair,lam) cases, fail={}", m, c1, f1);
        // Lemma 7: d,d' not div by 7, rp d' = 2 rp d % 7, e = ediff d d'
        let (mut c7i, mut f7i, mut c7ii, mut f7ii, mut f7iinl) = (0u64, 0u64, 0u64, 0u64, 0u64);
        let lim7 = if m == 2 { 2 * n } else { n };
        for d in 1..lim7 { if d % 7 == 0 { continue; } for dp in 1..lim7 { if dp % 7 == 0 || rp(dp) != 2 * rp(d) % 7 { continue; }
            let e = p.ediff(d, dp); let v = nu(e);
            // achievable sets
            if e != 0 && v < m {
                let mut ach = 0u32; // over h < m, k < 7
                for h in 0..m { for k in 0..7 { let l = p.lam(h, k); ach |= 1 << p.et(l * d, l * dp); } }
                for x in 0..128u32 { if ellm(x) <= 4 { c7i += 1; if ach & !x == 0 { f7i += 1; } } }
            }
            if v == m {
                let r = rp(e);
                let mut ach = 0u32; for k in 0..7 { let l = p.lam(1, k); ach |= 1 << p.et(l * d, l * dp); }
                for x in 0..128u32 {
                    let inx = x >> r & 1 == 1; let inx1 = x >> ((r + 6) % 7) & 1 == 1;
                    if !(inx && inx1) { c7ii += 1; if ach & !x == 0 { f7ii += 1; } }
                }
                // proof mechanism: q(lam 7d)=0 -> et = r ; =6 -> et = r-1
                for k in 0..7 { let l = p.lam(1, k); let q7 = p.q(l * 7 * d); let et = p.et(l * d, l * dp);
                    if (q7 == 0 && et != r) || (q7 == 6 && et != (r + 6) % 7) { f7iinl += 1; } }
            }
        } }
        println!("m={} L7(i): {} (pair,X) cases fail={}; L7(ii): {} cases fail={} mech-fail={}", m, c7i, f7i, c7ii, f7ii, f7iinl);
    }
}
