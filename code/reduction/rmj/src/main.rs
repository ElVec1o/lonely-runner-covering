// rmj: exact ML of the families F(m,j) and related exact forms. Exact integer arithmetic only.
use rayon::prelude::*;

fn gcd(a: i64, b: i64) -> i64 { let (mut x, mut y) = (a.abs(), b.abs()); while y != 0 { let t = x % y; x = y; y = t; } x }
fn gcd_all(v: &[i64]) -> i64 { v.iter().fold(0, |a, &b| gcd(a, b)) }
fn lcm(a: i64, b: i64) -> i64 { a / gcd(a, b) * b }

/// min_i ||v_i a / q|| as the integer numerator r over q (r = min(res, q-res))
fn gap_num(v: &[i64], a: i64, q: i64) -> i64 {
    let mut mn = i64::MAX;
    for &x in v { let r = ((x as i128 * a as i128).rem_euclid(q as i128)) as i64; let r = r.min(q - r); if r < mn { mn = r; if mn == 0 { break; } } }
    mn
}

/// Exact ML: (num, den) reduced, plus all maximisers a/q in [0,1/2] (reduced).
/// ML is attained at some a/(v_i+v_j) (i<j) or a/(2 v_i); we scan all of them.
fn ml(v: &[i64]) -> (i64, i64, Vec<(i64, i64)>) {
    let mut dens: Vec<i64> = vec![];
    for i in 0..v.len() { dens.push(2 * v[i]); for j in i + 1..v.len() { dens.push(v[i] + v[j]); } }
    dens.sort(); dens.dedup();
    let best = dens.par_iter().map(|&q| {
        let (mut bn, mut bd) = (0i64, 1i64);
        for a in 1..=q / 2 { let r = gap_num(v, a, q); if (r as i128) * (bd as i128) > (bn as i128) * (q as i128) { bn = r; bd = q; } }
        (bn, bd)
    }).reduce(|| (0, 1), |x, y| if (x.0 as i128) * (y.1 as i128) >= (y.0 as i128) * (x.1 as i128) { x } else { y });
    let g = gcd(best.0, best.1); let (bn, bd) = (best.0 / g, best.1 / g);
    let mut maxs: Vec<(i64, i64)> = dens.par_iter().flat_map_iter(|&q| {
        let mut out = vec![];
        for a in 1..=q / 2 { let r = gap_num(v, a, q); if (r as i128) * (bd as i128) == (bn as i128) * (q as i128) { let g = gcd(a, q); out.push((a / g, q / g)); } }
        out
    }).collect();
    maxs.sort(); maxs.dedup();
    (bn, bd, maxs)
}

/// least q with a p such that (m+1) min(r, q-r) >= q for every speed (witness of ML >= 1/(m+1))
fn least_wit(v: &[i64], qmax: i64) -> Option<(i64, i64)> {
    let k2 = v.len() as i64 + 1;
    for q in 1..=qmax { for p in 1..=q / 2 { if v.iter().all(|&x| { let r = ((x as i128 * p as i128).rem_euclid(q as i128)) as i64; k2 * r.min(q - r) >= q }) { return Some((p, q)); } } }
    None
}
fn q0(v: &[i64]) -> i64 { (2..).find(|&j| v.iter().all(|&x| x % j != 0)).unwrap() }
fn l1o_prim(v: &[i64]) -> bool { (0..v.len()).all(|l| { let w: Vec<i64> = v.iter().enumerate().filter(|(i, _)| *i != l).map(|(_, &x)| x).collect(); gcd_all(&w) == 1 }) }
/// true iff some nonzero c in {-1,0,1}^m has c.v = 0 (i.e. NOT StrongFree)
fn has_pm1_relation(v: &[i64]) -> bool {
    let s: i64 = v.iter().sum(); let off = s as usize; let n = 2 * off + 1;
    let mut any = vec![false; n]; let mut ne = vec![false; n]; any[off] = true;
    for &x in v { let x = x as usize; let (a0, n0) = (any.clone(), ne.clone());
        for p in 0..n { if a0[p] { if p + x < n { any[p + x] = true; ne[p + x] = true; } if p >= x { any[p - x] = true; ne[p - x] = true; } }
                        if n0[p] { if p + x < n { ne[p + x] = true; } if p >= x { ne[p - x] = true; } } }
        if ne[off] { return true; } }
    ne[off]
}
fn in_class(v: &[i64]) -> bool { gcd_all(v) == 1 && q0(v) >= v.len() as i64 + 2 && l1o_prim(v) && has_pm1_relation(v) }
fn parse(s: &str) -> Vec<i64> { s.split(|c: char| c == ',' || c.is_whitespace() || c == '[' || c == ']').filter(|x| !x.is_empty()).map(|x| x.parse().unwrap()).collect() }

fn eval(v: &[i64]) {
    let m = v.len() as i64; let (n, d, mx) = ml(v); let lw = least_wit(v, 20000);
    let g = gcd(n * (m + 1), d);
    println!("v={:?} m={} gcd={} ML={}/{} (m+1)ML={}/{} maximisers={:?} leastwit={:?} q0={} DC={} L1O={} pm1rel={} inclass={}",
        v, m, gcd_all(v), n, d, n * (m + 1) / g, d / g, &mx[..mx.len().min(8)], lw, q0(v), q0(v) >= m + 2, l1o_prim(v), has_pm1_relation(v), in_class(v));
}


/// Window certificate at a/q, direction +: t = a/q + eps, eps in (0, epsp], epsp = min over non-multiples of q of
/// (m q - (m+1) r_i)/((m+1) q v_i), r_i = v_i a mod q. Multiples Z of q sit at v_i eps. Returns Some(eps as (P,Qd))
/// if some eps in (0, epsp] has ||z eps|| >= 1/(m+1) for all z in Z (exact), None otherwise. q in [2, m+1].
fn window_cert(v: &[i64], a: i64, q: i64) -> Option<(i128, i128)> {
    let m = v.len() as i128; let k2 = m + 1; let (q1, a1) = (q as i128, a as i128);
    let mut en: i128 = i128::MAX; let mut ed: i128 = 1; let mut z: Vec<i128> = vec![];
    for &x in v { let x = x as i128; let r = (x * a1).rem_euclid(q1);
        if r == 0 { z.push(x); continue; }
        let num = m * q1 - k2 * r; let den = k2 * q1 * x; if num <= 0 { return None; }
        if en == i128::MAX || num * ed < en * den { en = num; ed = den; } }
    if z.is_empty() { return Some((0, 1)); } // a/q itself is a witness
    // candidates eps = (k(m+1)+1)/((m+1) z0), k >= 0, eps <= en/ed
    for &z0 in &z { let dz = k2 * z0; let mut k: i128 = 0;
        loop { let p = k * k2 + 1; if p * ed > en * dz { break; }
            if z.iter().all(|&zz| { let r = (zz * p).rem_euclid(dz); k2 * r.min(dz - r) >= dz }) { return Some((p, dz)); }
            k += 1; if k > 2_000_000 { break; } } }
    None
}
/// scan all q in [2, m+1], a in [1, q-1] coprime: first certificate found (q, a, |Z|)
fn wc_scan(v: &[i64]) -> Option<(i64, i64, usize)> {
    let m = v.len() as i64;
    for q in 2..=m + 1 { for a in 1..q { if gcd(a, q) != 1 { continue; }
        if let Some((pp, dd)) = window_cert(v, a, q) {
            // verify t = a/q + pp/dd exactly: t = (a*dd + pp*q)/(q*dd)
            let (tn, td) = (a as i128 * dd + pp * q as i128, q as i128 * dd); let k2 = v.len() as i128 + 1;
            assert!(v.iter().all(|&x| { let r = (x as i128 * tn).rem_euclid(td); k2 * r.min(td - r) >= td }), "certificate failed {:?} {} {}", v, a, q); let nz = v.iter().filter(|&&x| x % q == 0).count(); return Some((q, a, nz)); } } }
    None
}
fn missed_unit(v: &[i64]) -> bool { let m1 = v.len() as i64 + 1; (1..m1).any(|c| gcd(c, m1) == 1 && v.iter().all(|&x| x.rem_euclid(m1) != c)) }

fn fmj(m: i64, j: i64, c: i64) -> Vec<i64> { let mut v: Vec<i64> = (1..=m).filter(|&x| x != j).collect(); v.push(lcm(j, m + 1) * c); v.sort(); v }

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args[0].as_str() {
        "eval" => for a in &args[1..] { eval(&parse(a)); },
        // F(m,j,c) = ([1,m] \ {j}) U {c*lcm(j,m+1)}: exact (m+1)ML for all j, c<=C
        "fam" => {
            let (m0, m1, cc): (i64, i64, i64) = (args[1].parse().unwrap(), args[2].parse().unwrap(), args[3].parse().unwrap());
            for m in m0..=m1 { for j in 1..=m { for c in 1..=cc {
                let v = fmj(m, j, c); let (n, d, mx) = ml(&v); let g = gcd(n * (m + 1), d);
                let t_all_m1 = mx.iter().all(|&(_, q)| (m + 1) % q == 0);
                println!("F m={} j={} c={} w={} (m+1)ML={}/{} ML={}/{} inclass={} nmax={} firstmax={:?} allmax_den|m+1={}", m, j, c, v.iter().max().unwrap(), n * (m + 1) / g, d / g, n, d, in_class(&v), mx.len(), mx.first(), t_all_m1);
            } } }
        }
        // (T) structured falsification: one-entry modifications [1,m]_{j->w}, (m+1) | w, w <= W, w not in [1,m]
        "t1" => {
            let (m0, m1, wmax): (i64, i64, i64) = (args[1].parse().unwrap(), args[2].parse().unwrap(), args[3].parse().unwrap());
            for m in m0..=m1 {
                let jobs: Vec<(i64, i64)> = (1..=m).flat_map(|j| ((m + 1)..=wmax).step_by((m + 1) as usize).map(move |w| (j, w))).collect();
                let res: Vec<(i64, i64, i64, i64)> = jobs.par_iter().map(|&(j, w)| { let mut v: Vec<i64> = (1..=m).filter(|&x| x != j).collect(); v.push(w);
                    let (n, d, _) = ml(&v); (j, w, n, d) }).collect();
                let (mut tight, mut below) = (0, 0);
                for &(j, w, n, d) in &res { let lhs = n as i128 * (m + 1) as i128; let rhs = d as i128;
                    if lhs == rhs { tight += 1; println!("  TIGHT m={} j={} w={}", m, j, w); }
                    if lhs < rhs { below += 1; println!("  BELOW m={} j={} w={} ML={}/{}", m, j, w, n, d); }
                    let _ = (j, w); }
                // minr tracked as ((m+1)n, d): smallest ratio > 1
                let mut best = (i64::MAX, 1i64, 0, 0); for &(j, w, n, d) in &res { let a = n * (m + 1); if (a as i128) > d as i128 && (a as i128) * (best.1 as i128) < (best.0 as i128) * (d as i128) { best = (a, d, j, w); } }
                let g = gcd(best.0, best.1);
                println!("t1 m={} cases={} tight={} below={} min(m+1)ML>1 = {}/{} at j={} w={}", m, res.len(), tight, below, best.0 / g, best.1 / g, best.2, best.3);
            }
        }
        "wc" => { use std::io::BufRead; let (mut n, mut fired, mut f1, mut fm1, mut mu) = (0, 0, 0, 0, 0);
            for l in std::io::stdin().lock().lines() { let l = l.unwrap(); let l = l.trim(); if l.is_empty() || l.starts_with('#') { continue; }
                let v = parse(l.split('|').next().unwrap()); n += 1; let r = wc_scan(&v); let m = v.len() as i64; let mu1 = missed_unit(&v); if mu1 { mu += 1; }
                match r { Some((q, a, nz)) => { fired += 1; if nz == 1 { f1 += 1; } if q == m + 1 { fm1 += 1; } if args.len() > 1 { println!("WC {:?} q={} a={} |Z|={} missedunit={}", v, q, a, nz, mu1); } },
                          None => { println!("NOWC {:?} missedunit(m+1)={} inclass={}", v, mu1, in_class(&v)); } } }
            println!("wc: families={} window-cert fired={} (|Z|=1: {}, at q=m+1: {}) ; missed unit mod m+1: {}", n, fired, f1, fm1, mu); }
        // Theorem F check: (m+1)/2 < j <= m, gcd(j,m+1)=1, v = [1,m]\{j} u {j(m+1)}, D = mj+m+1.
        // witness t = (sD+1)/(jD), s = -(m+1-j)^{-1} mod j; check gap(t) >= (m+1)/D exactly; optional exact ML == (m+1)/D.
        "thmF" => { let (m0, m1, mlmax): (i64, i64, i64) = (args[1].parse().unwrap(), args[2].parse().unwrap(), args[3].parse().unwrap());
            let (mut n, mut wok, mut mlok, mut mlchk) = (0, 0, 0, 0);
            for m in m0..=m1 { for j in 1..=m { if 2 * j <= m + 1 || gcd(j, m + 1) != 1 { continue; } n += 1;
                let d = m * j + m + 1; let s = (0..j.max(1)).find(|&s| (s * (m + 1 - j) + 1) % j == 0).unwrap();
                let mut v: Vec<i64> = (1..=m).filter(|&x| x != j).collect(); v.push(j * (m + 1));
                let (tn, td) = ((s * d + 1) as i128, (j * d) as i128);
                let ok = v.iter().all(|&x| { let r = (x as i128 * tn).rem_euclid(td); r.min(td - r) * (d as i128) >= (m as i128 + 1) * td });
                if ok { wok += 1 } else { println!("WITNESS FAIL m={} j={}", m, j); }
                if m <= mlmax { mlchk += 1; let (a, b, _) = ml(&v); if (a as i128) * (d as i128) == (b as i128) * (m as i128 + 1) { mlok += 1 } else { println!("ML MISMATCH m={} j={} ML={}/{} formula={}/{}", m, j, a, b, m + 1, d); } } } }
            println!("thmF m={}..{}: cases={} witness ok={} ; exact ML checked (m<={})={} equal to (m+1)/(mj+m+1): {}", m0, m1, n, wok, mlmax, mlchk, mlok); }
        _ => panic!("mode"),
    }
}
