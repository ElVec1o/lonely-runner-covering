// falsify the EXACT Lean statements for BarajasSerraSec6L10 / Sec6_1 / Sec6_2 / Sec6_4.
// Mirrors Lean: nu 0 = 0, rp x = (x / 7^nu x) % 7, qq x = ((x % N) / 7^m) % 7, E x y = dsub N x y.
use std::env;
fn nu(x: u64) -> u32 { if x == 0 { return 0; } let mut x = x; let mut v = 0; while x % 7 == 0 { x /= 7; v += 1; } v }
fn rp(x: u64) -> u64 { (x / 7u64.pow(nu(x))) % 7 }
#[derive(Clone, Copy)]
struct P { n: u64, m: u32, pm: u64 }
impl P {
    fn q(&self, x: u64) -> u64 { ((x % self.n) / self.pm) % 7 }
    fn e(&self, x: u64, y: u64) -> u64 { (x % self.n + (self.n - y % self.n)) % self.n }
    fn ediff(&self, x: u64, y: u64) -> u64 {
        if rp(y) == 2 * rp(x) % 7 { self.e(2 * x, y) } else if rp(x) == 2 * rp(y) % 7 { self.e(2 * y, x) } else { self.e(x, y) }
    }
    fn et(&self, x: u64, y: u64) -> u64 {
        if rp(y) == 2 * rp(x) % 7 { (2 * self.q(x) + 14 - self.q(y)) % 7 } else if rp(x) == 2 * rp(y) % 7 { (2 * self.q(y) + 14 - self.q(x)) % 7 } else { (self.q(x) + 7 - self.q(y)) % 7 }
    }
    fn lam(&self, i: u32, k: u64) -> u64 { 1 + 7u64.pow(self.m - i) * k }
    // window: exists c among b with E(b_i, c) <= M for all i
    fn win(&self, b: &[u64]) -> bool { b.iter().any(|&c| b.iter().all(|&x| self.e(x, c) <= self.pm)) }
    fn avoid(&self, l: u64, ds: &[u64]) -> bool { ds.iter().all(|&d| { let v = self.q(l * d); v != 0 && v != 6 }) }
}
fn win5(vals: &[u64]) -> bool { (0..7).any(|t| vals.iter().all(|&v| (v + 7 - t) % 7 < 5)) }
const PERM4: [[usize; 4]; 24] = [[0,1,2,3],[0,1,3,2],[0,2,1,3],[0,2,3,1],[0,3,1,2],[0,3,2,1],[1,0,2,3],[1,0,3,2],[1,2,0,3],[1,2,3,0],[1,3,0,2],[1,3,2,0],[2,0,1,3],[2,0,3,1],[2,1,0,3],[2,1,3,0],[2,3,0,1],[2,3,1,0],[3,0,1,2],[3,0,2,1],[3,1,0,2],[3,1,2,0],[3,2,0,1],[3,2,1,0]];
const PERM3: [[usize; 3]; 6] = [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]];
fn r7(x: u64) -> u64 { x % 7 }
// Lemma 10 predicate for a labeling (d1,d2,d3,d4); only_ii1 = negative control
fn l10(p: &P, d: [u64; 4], only_ii1: bool) -> bool {
    let all_zero = (0..4).all(|i| (0..4).all(|j| i == j || p.e(d[i], d[j]) == 0));
    if all_zero { return true; }
    for pm in PERM4.iter() {
        let (d1, d2, d3, d4) = (d[pm[0]], d[pm[1]], d[pm[2]], d[pm[3]]);
        if nu(p.e(d2, d1)) != nu(p.e(d3, d1)) { return true; }
        let h = nu(p.e(d2, d1));
        let alllev = (0..4).all(|i| (0..4).all(|j| i == j || (p.e(d[i], d[j]) != 0 && nu(p.e(d[i], d[j])) == h)));
        if alllev {
            let (a, b, c) = (rp(p.e(d2, d1)), rp(p.e(d3, d1)), rp(p.e(d4, d1)));
            if b == r7(2 * a) && (c == r7(3 * a) || (!only_ii1 && c == r7(4 * a))) { return true; }
        }
    }
    false
}
fn l11(p: &P, d: [u64; 3], t: u64, plus_only: bool) -> bool {
    if p.e(d[0], d[2]) == 0 && p.e(d[1], d[2]) == 0 { return true; }
    for pm in PERM3.iter() {
        let (d1, d2, d3) = (d[pm[0]], d[pm[1]], d[pm[2]]);
        if nu(p.e(d1, d3)) != nu(p.e(d2, d3)) { return true; }
        let h = nu(p.e(d1, d3));
        let alllev = (0..3).all(|i| (0..3).all(|j| i == j || (p.e(d[i], d[j]) != 0 && nu(p.e(d[i], d[j])) == h)));
        if alllev {
            let (a, b) = (rp(p.e(d1, d3)), rp(p.e(d2, d3)));
            if a == r7(2 * b) { return true; }
            if a == r7(3 * b) && (b == t || (!plus_only && b == r7(7 - t))) { return true; }
        }
    }
    false
}
fn main() {
    let args: Vec<String> = env::args().collect();
    let which = if args.len() > 1 { args[1].clone() } else { "all".to_string() };
    for m in [2u32, 3] {
        let n = 7u64.pow(m + 1);
        let p = P { n, m, pm: 7u64.pow(m) };
        let units: Vec<u64> = (1..n).filter(|v| v % 7 != 0).collect();
        let step = if m == 2 { 1 } else { 60 };
        // class-s values in [0, 2N) (non-reduced included for m=2)
        let cls = |s: u64| -> Vec<u64> { let lim = if m == 2 { 2 * n } else { n }; (0..lim).filter(|v| v % 7 == s).collect() };
        if which == "all" || which == "l10" {
            for s in [1u64, 3] {
                let c = cls(s); let k = c.len();
                let (mut cnt, mut fail, mut failnc) = (0u64, 0u64, 0u64);
                for a in (0..k).step_by(step) { for b in a..k { for cc in b..k { for dd in cc..k {
                    let d = [c[a], c[b], c[cc], c[dd]]; cnt += 1;
                    if !l10(&p, d, false) { fail += 1; if fail < 3 { println!("  L10 FAIL {:?}", d); } }
                    if !l10(&p, d, true) { failnc += 1; }
                } } } }
                println!("m={} s={} Lemma10: {} multisets fail={} | NC(only ii.1) fail={}", m, s, cnt, fail, failnc);
            }
        }
        if which == "all" || which == "l11" {
            let c = cls(1); let k = c.len();
            let (mut cnt, mut fail, mut failnc) = (0u64, 0u64, 0u64);
            for a in (0..k).step_by(step) { for b in a..k { for cc in b..k { for t in 1..7u64 {
                let d = [c[a], c[b], c[cc]]; cnt += 1;
                if !l11(&p, d, t, false) { fail += 1; if fail < 3 { println!("  L11 FAIL {:?} t={}", d, t); } }
                if !l11(&p, d, t, true) { failnc += 1; }
            } } } }
            println!("m={} Lemma11: {} (multiset,t) fail={} | NC(+t only) fail={}", m, cnt, fail, failnc);
        }
        if which == "all" || which == "win" {
            // win9_i: nu(E b1 b3) != nu(E b2 b3) -> exists unit mu with window; win9_ii: nonzero level h<m, r(y)=2r(x)
            let c: Vec<u64> = (0..n).filter(|v| v % 7 == 1).collect();
            let (mut c1, mut f1, mut c2, mut f2, mut nc1) = (0u64, 0u64, 0u64, 0u64, 0u64);
            for &b3 in c.iter().step_by(step) { for &b1 in &c { for &b2 in &c {
                let x = p.e(b1, b3); let y = p.e(b2, b3);
                let ok = |pp: &P| units.iter().any(|&u| pp.win(&[u * b1, u * b2, u * b3]));
                if nu(x) != nu(y) { c1 += 1; if !ok(&p) { f1 += 1; }
                    // NC: window width M-1
                    let pn = P { n, m, pm: p.pm }; let okn = units.iter().any(|&u| { let bb = [u * b1, u * b2, u * b3]; bb.iter().any(|&cc| bb.iter().all(|&xx| pn.e(xx, cc) <= pn.pm - 1)) });
                    if !okn { nc1 += 1; } }
                else if x != 0 && y != 0 && nu(x) < m && rp(y) == 2 * rp(x) % 7 { c2 += 1; if !ok(&p) { f2 += 1; } }
            } } }
            println!("m={} win9_i: {} fail={} (NC width M-1 fail={}); win9_ii: {} fail={}", m, c1, f1, nc1, c2, f2);
        }
        if which == "all" || which == "trick" {
            // trick3: 5 same-class elements, W(b1,b2,b3) -> exists mu' in {1,3}, window5 of q(mu' *)
            let c: Vec<u64> = (0..n).filter(|v| v % 7 == 1).collect();
            let (mut cnt, mut fail, mut nc) = (0u64, 0u64, 0u64);
            for &b3 in c.iter().step_by(step) { for &b1 in &c { for &b2 in &c {
                if !p.win(&[b1, b2, b3]) { continue; }
                for &d4 in c.iter().step_by(step) { for &d5 in &c {
                    cnt += 1;
                    let v1: Vec<u64> = [b1, b2, b3, d4, d5].iter().map(|&x| p.q(x)).collect();
                    let v3: Vec<u64> = [b1, b2, b3, d4, d5].iter().map(|&x| p.q(3 * x)).collect();
                    if !win5(&v1) { nc += 1; if !win5(&v3) { fail += 1; } }
                } }
            } } }
            println!("m={} trick3: {} configs fail={} | NC(mu'=1 only) fail={}", m, cnt, fail, nc);
        }
        if which == "all" || which == "l7x" {
            // Lemma 7(ii)-ext: ediff(d,d') = 7^m z incl. z = 0 (mod N)
            let (mut cnt, mut fail, mut nc) = (0u64, 0u64, 0u64);
            let lim = if m == 2 { 2 * n } else { n };
            for d in 1..lim { if d % 7 == 0 { continue; } for dp in 1..lim { if dp % 7 == 0 || rp(dp) != 2 * rp(d) % 7 { continue; }
                let e = p.ediff(d, dp); if e % p.pm != 0 { continue; } let z = e / p.pm;
                let mut ach = 0u32; for k in 0..7 { let l = p.lam(1, k); ach |= 1 << p.et(l * d, l * dp); }
                for x in 0..128u32 { let inz = x >> z & 1 == 1; let inz1 = x >> ((z + 6) % 7) & 1 == 1;
                    if !(inz && inz1) { cnt += 1; if ach & !x == 0 { fail += 1; } } else if ach & !x == 0 { nc += 1; } }
            } }
            println!("m={} L7(ii)-ext (z incl 0): {} (pair,X) fail={} | NC(X∩(X+1) nonempty) unreachable={}", m, cnt, fail, nc);
        }
        if (which == "all" || which == "sub") && m == 2 {
            // full subsection conclusions: exists unit lam mod N with all speeds avoiding q in {0,6}
            let c1: Vec<u64> = (0..n).filter(|v| v % 7 == 1).collect();
            let c2: Vec<u64> = (0..n).filter(|v| v % 7 == 2).collect();
            let c4: Vec<u64> = (0..n).filter(|v| v % 7 == 4).collect();
            let lam0: Vec<u64> = (0..7).map(|k| p.lam(0, k)).collect();
            let k = c1.len();
            let sstep = if m == 2 { 1 } else { 40 };
            // 6.1
            let (mut cnt, mut fail, mut nc) = (0u64, 0u64, 0u64);
            for a in (0..k).step_by(sstep) { for b in a..k { for cc in b..k { for dd in cc..k { for ee in dd..k {
                let ds = [c1[a], c1[b], c1[cc], c1[dd], c1[ee]]; cnt += 1;
                if !units.iter().any(|&l| p.avoid(l, &ds)) { fail += 1; }
                if !lam0.iter().any(|&l| p.avoid(l, &ds)) { nc += 1; }
            } } } } }
            println!("m={} 6.1: {} fail={} | NC(Lambda0 only) fail={}", m, cnt, fail, nc);
            // 6.2
            let (mut cnt, mut fail, mut nc) = (0u64, 0u64, 0u64);
            for a in (0..k).step_by(sstep) { for b in a..k { for cc in b..k { for dd in cc..k { for &d5 in c2.iter().chain(c4.iter()) {
                let ds = [c1[a], c1[b], c1[cc], c1[dd], d5]; cnt += 1;
                if !units.iter().any(|&l| p.avoid(l, &ds)) { fail += 1; }
                if !lam0.iter().any(|&l| p.avoid(l, &ds)) { nc += 1; }
            } } } } }
            println!("m={} 6.2: {} fail={} | NC(Lambda0 only) fail={}", m, cnt, fail, nc);
            // 6.4
            let (mut cnt, mut fail, mut nc) = (0u64, 0u64, 0u64);
            let k2 = c2.len();
            for a in (0..k).step_by(sstep) { for b in a..k { for cc in b..k { for x in 0..k2 { for y in x..k2 {
                let ds = [c1[a], c1[b], c1[cc], c2[x], c2[y]]; cnt += 1;
                if !units.iter().any(|&l| p.avoid(l, &ds)) { fail += 1; }
                if !lam0.iter().any(|&l| p.avoid(l, &ds)) { nc += 1; }
            } } } } }
            println!("m={} 6.4: {} fail={} | NC(Lambda0 only) fail={}", m, cnt, fail, nc);
        }
    }
}
