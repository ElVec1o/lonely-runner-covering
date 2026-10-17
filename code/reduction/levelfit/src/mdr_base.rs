// mdr: independent checker. Exact integer arithmetic (i128).
// Conventions: v = m speeds, target delta = 1/(m+1).
use std::collections::HashMap;
use std::io::Write;

type I = i128;
// target denominator: delta = 1/dd ; default m+1, override with env MDR_DSHIFT (dd = m+1-shift) for negative controls
fn dd(v: &[I]) -> I { let sh: I = std::env::var("MDR_DSHIFT").ok().map(|x| x.parse().unwrap()).unwrap_or(0); v.len() as I + 1 - sh }

fn gcd(a: I, b: I) -> I { let (mut a, mut b) = (a.abs(), b.abs()); while b != 0 { let t = a % b; a = b; b = t; } a }
fn gcdv(v: &[I]) -> I { v.iter().fold(0, |g, &x| gcd(g, x)) }

fn parse(s: &str) -> Vec<I> {
    let s = s.trim().trim_start_matches('[');
    let s = s.split(']').next().unwrap();
    s.split(|c| c == ',' || c == ' ').filter(|x| !x.is_empty()).map(|x| x.parse().unwrap()).collect()
}

// distance numerator: ||x p/q|| = dn/q
fn dn(x: I, p: I, q: I) -> I { let r = (x % q * (p % q)) % q; let r = ((r % q) + q) % q; r.min(q - r) }

// gap at p/q as fraction (num, q)
fn gap_at(v: &[I], p: I, q: I) -> I { v.iter().map(|&x| dn(x, p, q)).min().unwrap() }

fn lt(a: (I, I), b: (I, I)) -> bool { a.0 * b.1 < b.0 * a.1 }

// exact ML over candidates c/(v_i+v_j), i<=j
fn ml(v: &[I]) -> ((I, I), Vec<(I, I)>) {
    let mut best = (0 as I, 1 as I);
    let mut arg: Vec<(I, I)> = vec![];
    let m = v.len();
    let mut seen = std::collections::HashSet::new();
    for i in 0..m { for j in i..m {
        let s = v[i] + v[j];
        if !seen.insert(s) { continue; }
        // every numerator c in 1..s (not only c coprime to s): a reduced fraction c/s may have a denominator
        // that is not itself a sum of two speeds (archive fix; the original skipped gcd(c,s) != 1)
        for c in 1..s {
            let g = gap_at(v, c, s);
            let cand = (g, s);
            let g0 = gcd(c, s);
            if lt(best, cand) { best = cand; arg.clear(); arg.push((c / g0, s / g0)); }
            else if !lt(cand, best) { arg.push((c / g0, s / g0)); }
        }
    }}
    let g = gcd(best.0, best.1); if g > 0 { best = (best.0 / g, best.1 / g); }
    arg.sort_by(|a, b| (a.0 * b.1).cmp(&(b.0 * a.1))); arg.dedup();
    (best, arg)
}

// ML with phases: phases given as num/den per speed (common den D). gap(t)=min ||v_i t - ph_i/D||
// candidates: t with v_i t - ph_i/D = +-(v_j t - ph_j/D) mod 1 => t = (k*D + ph_i +- ph_j)/(D (v_i +- v_j))
fn ml_shift(v: &[I], ph: &[I], d: I) -> ((I, I), (I, I)) {
    let m = v.len();
    let mut best = (0 as I, 1 as I); let mut arg = (0, 1);
    for i in 0..m { for j in i..m { for sg in [1 as I, -1] {
        let s = v[i] + sg * v[j]; if s == 0 { continue; }
        let s = s.abs();
        let den = d * s; // t = c/den
        for c in 0..den {
            // gap = min_i ||v_i c/den - ph_i/D|| = min dist( v_i c - ph_i*s , den)/den
            let mut g = I::MAX;
            for k in 0..m { let r = ((v[k] * c - ph[k] * s) % den + den) % den; g = g.min(r.min(den - r)); }
            if lt(best, (g, den)) { best = (g, den); arg = (c, den); }
        }
    }}}
    let g = gcd(best.0, best.1); let g2 = gcd(arg.0, arg.1);
    ((best.0 / g, best.1 / g), (arg.0 / g2, arg.1 / g2))
}

fn is_dc(v: &[I]) -> bool { let m = v.len() as I; (2..=m + 1).all(|j| v.iter().any(|&x| x % j == 0)) }
fn l1o(v: &[I]) -> bool { (0..v.len()).all(|l| { let w: Vec<I> = v.iter().enumerate().filter(|(i, _)| *i != l).map(|(_, &x)| x).collect(); gcdv(&w) == 1 }) }
// nonzero c in {-1,0,1}^m with c.v = 0 ; meet in the middle
fn half_sums(v: &[I]) -> HashMap<I, u64> {
    let mut h: HashMap<I, u64> = HashMap::new(); h.insert(0, 1);
    for &x in v { let mut n: HashMap<I, u64> = HashMap::new();
        for (&s, &c) in &h { for d in [-x, 0, x] { *n.entry(s + d).or_insert(0) += c; } }
        h = n; }
    h
}
fn not_sf(v: &[I]) -> bool {
    let k = v.len() / 2; let a = half_sums(&v[..k]); let b = half_sums(&v[k..]);
    for (&s, &c) in &a { if let Some(&d) = b.get(&-s) { let tot = c * d; if s == 0 { if tot > 1 { return true; } } else if tot > 0 { return true; } } }
    false
}
fn least_witness(v: &[I], cap: I) -> Option<(I, I)> {
    let m1 = v.len() as I + 1;
    for q in 2..=cap { for p in 1..=q / 2 { if gcd(p, q) != 1 { continue; }
        if v.iter().all(|&x| m1 * dn(x, p, q) >= q) { return Some((p, q)); } } }
    None
}
fn q0(v: &[I]) -> I { let mut j = 2; loop { if !v.iter().any(|&x| x % j == 0) { return j; } j += 1; } }

// ---------------- window / perturbation certificate ----------------
// Rationals as (num, den) with den > 0.
#[derive(Clone, Copy, Debug)]
struct R { n: I, d: I }
impl R { fn new(n: I, d: I) -> R { let g = gcd(n, d).max(1); let s = if d < 0 { -1 } else { 1 }; R { n: s * n / g, d: s * d / g } }
    fn lt(&self, o: &R) -> bool { self.n * o.d < o.n * self.d }
    fn le(&self, o: &R) -> bool { self.n * o.d <= o.n * self.d } }

// Certificate at level q, unit a, side sgn (+1 right, -1 left): t = a/q + sgn*eps, eps >= 0.
// Non-multiples n: centred residue e of (sgn*n*a) mod q, e in (-q/2, q/2]. distance ||e/q + n eps||.
// Sound good sub-interval for n (eps>=0):
//   e>0: [max(0,(delta-e/q)/n), (1-delta-e/q)/n]
//   e<0, |e|/q>=delta: [0, (|e|/q-delta)/n]
//   e<0, |e|/q<delta: [(|e|/q+delta)/n, (1-delta+|e|/q)/n]
// Returns (lo, hi) of the intersection (may be empty).
fn n_interval(v: &[I], q: I, a: I, sgn: I) -> Option<(R, R, Vec<I>)> {
    let m1 = dd(v);
    let mut lo = R::new(0, 1); let mut hi = R::new(1, 1); let mut z = vec![];
    for &x in v {
        if x % q == 0 { z.push(x); continue; }
        let mut r = ((sgn * x % q) * a % q + q) % q; // residue in [0,q)
        if 2 * r > q { r -= q; } // centred e = r
        let e = r;
        // work with common denominator q*m1*x
        let den = q * m1 * x;
        let (l, h) = if e > 0 {
            let l = if e * m1 >= q { R::new(0, 1) } else { R::new(q - e * m1, den) };
            (l, R::new(q * (m1 - 1) - e * m1, den))
        } else {
            let ae = -e;
            if ae * m1 >= q { (R::new(0, 1), R::new(ae * m1 - q, den)) }
            else { (R::new(ae * m1 + q, den), R::new(q * (m1 - 1) + ae * m1, den)) }
        };
        if lo.lt(&l) { lo = l; } if h.lt(&hi) { hi = h; }
    }
    if hi.lt(&lo) { return None; }
    Some((lo, hi, z))
}
// does some eps in [lo,hi] give ||z eps|| >= delta for all z in Z ? exact scan (candidates: endpoints, c/(zi+zj)).
// returns Some(true/false), None if too many candidates.
fn z_exact(z: &[I], lo: R, hi: R, m1: I, cap: I) -> Option<bool> {
    let ok = |p: I, qd: I| z.iter().all(|&x| { let r = ((x % qd) * (p % qd) % qd + qd) % qd; m1 * r.min(qd - r) >= qd });
    if ok(lo.n, lo.d) || ok(hi.n, hi.d) { return Some(true); }
    let mut budget = cap;
    for i in 0..z.len() { for j in i..z.len() {
        let s = z[i] + z[j];
        let c0 = (lo.n * s + lo.d - 1).div_euclid(lo.d); // ceil(lo*s)
        let c1 = (hi.n * s).div_euclid(hi.d);
        if c1 - c0 + 1 > budget { return None; }
        budget -= (c1 - c0 + 1).max(0);
        let mut c = c0; while c <= c1 { if ok(c, s) { return Some(true); } c += 1; }
    }}
    Some(false)
}

// (B) tail certificate: core = s smallest speeds (IH: ML(core) >= 1/(s+1)), tail T = rest.
// window length l = 2*(1/(s+1) - delta)/cmax ; fires if sum_T (2 delta l + 2 delta / t) < l.
fn tail_cert(v: &[I]) -> Option<usize> {
    let mut s = v.to_vec(); s.sort(); let m = s.len(); let m1 = dd(v);
    for c in 1..m { let cmax = s[c - 1];
        // l = 2*(m1 - (c+1)) / ((c+1) m1 cmax) ; need c+1 < m1
        if (c as I) + 1 >= m1 { continue; }
        let ln = 2 * (m1 - (c as I + 1)); let ld = (c as I + 1) * m1 * cmax;
        // sum_T 2 delta l + 2 delta/t  <  l   <=> multiply by m1*ld : sum_T (2 ln + 2 ld / t) < m1 ln  -> use rationals via f64-free: compare sum_T 2 ld/t < m1 ln - 2 ln |T|
        let tcount = (m - c) as I; let rhs = m1 * ln - 2 * ln * tcount; if rhs <= 0 { continue; }
        // sum 2 ld / t < rhs  : exact with common denominator product may overflow; use bound check with i128 fractions accumulated as (num,den) reduced
        let (mut sn, mut sd) = (0 as I, 1 as I);
        let mut okk = true;
        for &t in &s[c..] { let (an, ad) = (2 * ld, t); let nn = sn * ad + an * sd; let nd = sd * ad; let g = gcd(nn, nd).max(1); sn = nn / g; sd = nd / g; if sd > (1i128 << 90) { okk = false; break; } }
        if okk && sn < rhs * sd { return Some(c); }
    }
    None
}
#[derive(Debug, Clone, Copy, PartialEq)]
enum Kind { Point, WI, WX, WE }
// least q in [2,qmax] where a certificate fires. mode: 0 = WX (exact Z), 1 = WI only (point or IH window)
fn cert(v: &[I], qmax: I, want_wi_only: bool) -> Option<(I, I, I, Kind)> { cert_m(v, qmax, if want_wi_only {1} else {0}) }
fn cert_m(v: &[I], qmax: I, mode: u8) -> Option<(I, I, I, Kind)> { let want_wi_only = mode == 1;
    let m1 = dd(v);
    let qmin: I = std::env::var("MDR_QMIN").ok().map(|x| { let t: I = x.parse().unwrap(); if t == -1 { v.len() as I + 2 } else { t } }).unwrap_or(2);
    for q in qmin..=qmax { for a in 1..q { if gcd(a, q) != 1 { continue; }
        for sgn in [1 as I, -1] {
            if let Some((lo, hi, z)) = n_interval(v, q, a, sgn) {
                if z.is_empty() { return Some((q, a, sgn, Kind::Point)); } // interval nonempty: every point of it is lonely (lo>0 case fixed 2026-09-24)
                let g = gcdv(&z);
                // IH window: length >= 1/g  <=> (hi-lo) >= 1/g
                let len = R::new(hi.n * lo.d - lo.n * hi.d, hi.d * lo.d);
                if mode == 2 { // first-order escape: eps in [max(lo,1/(m1 zmin)), min(hi,(m1-1)/(m1 zmax))]
                    let zmin = *z.iter().min().unwrap(); let zmax = *z.iter().max().unwrap();
                    let l2 = R::new(1, m1 * zmin); let u2 = R::new(m1 - 1, m1 * zmax);
                    let ll = if lo.lt(&l2) { l2 } else { lo }; let uu = if hi.lt(&u2) { hi } else { u2 };
                    if ll.le(&uu) { return Some((q, a, sgn, Kind::WE)); }
                    continue;
                }
                if R::new(1, g).le(&len) && z.len() < v.len() { return Some((q, a, sgn, Kind::WI)); }
                if !want_wi_only { if let Some(true) = z_exact(&z, lo, hi, m1, 2_000_000) { return Some((q, a, sgn, Kind::WX)); } }
            }
        }
    }}
    None
}
// Window level: least q in (m+1, 2m+2] with a/q lonely (no speed divisible by q, +-units not covered)
fn tao_window(v: &[I]) -> Option<I> {
    let m = v.len() as I; let m1 = m + 1;
    for q in (m + 2)..=(2 * m + 2) { if v.iter().any(|&x| x % q == 0) { continue; }
        for p in 1..q { if gcd(p, q) != 1 { continue; } if v.iter().all(|&x| m1 * dn(x, p, q) >= q) { return Some(q); } } }
    None
}
// Lemma P as stated: q=m+1, exactly one speed w divisible by q, w > all others, some unit u mod q is residue of no speed
fn lemma_p(v: &[I]) -> bool {
    let q = v.len() as I + 1;
    let mult: Vec<I> = v.iter().cloned().filter(|x| x % q == 0).collect();
    if mult.len() != 1 { return false; }
    let w = mult[0]; if v.iter().any(|&x| x != w && x >= w) { return false; }
    (1..q).any(|u| gcd(u, q) == 1 && !v.iter().any(|&x| x % q == u))
}
fn fast(v: &[I]) -> bool { let mut s = v.to_vec(); s.sort(); let m = s.len() as I; let t = s[s.len() - 1]; s[..s.len() - 1].iter().all(|&x| m * x <= t) }

fn read_fams(path: &str) -> Vec<Vec<I>> {
    std::fs::read_to_string(path).unwrap().lines().filter_map(|l| {
        let l = l.trim(); if l.is_empty() || l.starts_with('#') { return None; }
        let f = l.split('|').next().unwrap(); if !f.chars().all(|c| c.is_ascii_digit() || c == ',' || c == ' ' || c == '[' || c == ']') { return None; }
        let v = parse(f); if v.len() < 2 { None } else { Some(v) } }).collect()
}

fn describe(v: &[I]) {
    let m = v.len() as I;
    let (b, arg) = ml(v);
    println!("v={:?} m={} gcd={} ML={}/{} (m+1)ML={}/{} maximisers={:?} least={:?} q0={} DC={} L1O={} nonSF={} fast={} lemmaP={} taoWin={:?}",
        v, m, gcdv(v), b.0, b.1, (m + 1) * b.0 / gcd((m + 1) * b.0, b.1), b.1 / gcd((m + 1) * b.0, b.1),
        &arg[..arg.len().min(6)], least_witness(v, 5000), q0(v), is_dc(v), l1o(v), not_sf(v), fast(v), lemma_p(v), tao_window(v));
}

// enumerate m-subsets of [1,H], gcd 1, DC, L1O, nonSF; count, and count ML < 1/m (decided by scanning all a/q, q<=2H)
fn enumerate(m: usize, h: I) {
    let mut idx: Vec<I> = (1..=m as I).collect();
    let (mut all, mut cls, mut below, mut belowm1) = (0u64, 0u64, 0u64, 0u64);
    let mut cls_gt = 0u64; // members with max > 2m? keep also max v > h-2
    loop {
        all += 1;
        let v = &idx;
        if gcdv(v) == 1 && is_dc(v) && l1o(v) && not_sf(v) {
            cls += 1; if v[m - 1] > h - 2 { cls_gt += 1; }
            // ML >= 1/m ? scan q <= 2h
            let mi = m as I; let mut hit = false; let mut hit1 = false;
            'o: for q in 2..=2 * h { for p in 1..=q / 2 { if gcd(p, q) != 1 { continue; }
                let g = gap_at(v, p, q); if mi * g >= q { hit = true; break 'o; } if (mi + 1) * g >= q { hit1 = true; } } }
            if !hit { below += 1; if !hit1 { belowm1 += 1; println!("BELOW_FLOOR {:?}", v); } else { println!("below1/m {:?}", v); } }
        }
        // next combination
        let mut i = m; loop { if i == 0 { println!("enum m={} H={} all={} class_superset={} (max v >= H-1: {}) ML<1/m: {} ML<1/(m+1): {}", m, h, all, cls, cls_gt, below, belowm1); return; }
            i -= 1; if idx[i] < h - (m - 1 - i) as I { idx[i] += 1; for j in i + 1..m { idx[j] = idx[j - 1] + 1; } break; } }
    }
}

// ------------- hunt: maximise least certificate level, filters every step -------------
struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn below(&mut self, n: u64) -> u64 { self.next() % n } }
fn in_class(v: &[I]) -> bool { let mut s = v.to_vec(); s.sort(); s.dedup(); s.len() == v.len() && s[0] > 0 && gcdv(v) == 1 && is_dc(v) && l1o(v) && not_sf(v) }
fn score(v: &[I], qmax: I) -> I { if fast(v) || tail_cert(v).is_some() { return 0; } match cert_m(v, qmax, 2) { Some((q, _, _, _)) => q, None => qmax + 1 } }
fn hunt(m: usize, h: I, secs: u64, seed: u64, qmax: I, out: &str) {
    let mut rng = Rng(seed * 2654435761 + 12345);
    let t0 = std::time::Instant::now();
    let mut f = std::fs::OpenOptions::new().create(true).append(true).open(out).unwrap();
    let mut best_ever = 0; let mut evals = 0u64; let mut restarts = 0;
    while t0.elapsed().as_secs() < secs {
        restarts += 1;
        // start: random DC-ish family: 1..m with a few random replacements
        let mut v: Vec<I> = (1..=m as I).collect();
        let mut tries = 0;
        while !in_class(&v) && tries < 10000 { let i = rng.below(m as u64) as usize; v[i] = 1 + rng.below(h as u64) as I; tries += 1; }
        if !in_class(&v) { continue; }
        let mut cur = score(&v, qmax); evals += 1;
        let mut stall = 0;
        while stall < 3000 && t0.elapsed().as_secs() < secs {
            let mut w = v.clone();
            let k = 1 + rng.below(2) as usize;
            for _ in 0..k { let i = rng.below(m as u64) as usize;
                w[i] = match rng.below(4) { 0 => 1 + rng.below(h as u64) as I,
                    1 => { let d = 2 + rng.below(2 * m as u64) as I; (d * (1 + rng.below((h / d) as u64) as I)).max(1) },
                    2 => (w[i] + rng.below(7) as I - 3).max(1).min(h),
                    _ => { let j = rng.below(m as u64) as usize; let c = 2 + rng.below(6) as I; (w[j] * c).min(h) } }; }
            if !in_class(&w) { stall += 1; continue; }
            let s = score(&w, qmax); evals += 1;
            if s >= cur { if s > cur { stall = 0; } else { stall += 1; } v = w; cur = s; } else { stall += 1; }
            if cur > 2 * m as I + 2 && cur > best_ever - 3 {
                let mut sv = v.clone(); sv.sort();
                writeln!(f, "{} | m={} certq={}", sv.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","), m, if cur > qmax { "none".to_string() } else { cur.to_string() }).unwrap();
            }
            if cur > best_ever { best_ever = cur; eprintln!("[{}s] m={} best certq={} evals={} restarts={} v={:?}", t0.elapsed().as_secs(), m, cur, evals, restarts, { let mut s = v.clone(); s.sort(); s }); }
        }
    }
    eprintln!("DONE m={} H={} secs={} evals={} restarts={} best={}", m, h, secs, evals, restarts, best_ever);
    writeln!(f, "# DONE m={} H={} evals={} restarts={} best={}", m, h, evals, restarts, best_ever).unwrap();
}


// U_1 (D=1) exact i128 coefficients, f64 sum, crude error bound. returns (U, err)
fn u1(v: &[I]) -> (f64, f64) {
    let a: [i128; 3] = [-1, 2, -1];
    let s: I = v.iter().sum(); if s > 400_000 { return (f64::NAN, f64::NAN); } let off = s; let len = (2 * off + 1) as usize;
    let mut f = vec![0i128; len]; f[off as usize] = 1; let mut reach: I = 0;
    for &x in v { let mut nf = vec![0i128; len];
        for idx in (off - reach)..=(off + reach) { let c = f[idx as usize]; if c == 0 { continue; }
            for k in 0..3 { let ni = (idx + (k as I - 1) * x) as usize; nf[ni] += c * a[k]; } }
        f = nf; reach += x; }
    let m = v.len(); let kk = (m + 1) as I; let pi = std::f64::consts::PI;
    let c0 = f[off as usize] as f64; if c0 <= 0.0 { return (f64::INFINITY, 0.0); }
    let mut tot = m as f64 * c0 * 2.0 / kk as f64; let mut abs = tot.abs(); let mut n = m;
    for &x in v { let mut r: I = 1; while r * x <= off { let c = f[(off + r * x) as usize];
        if c != 0 && r % kk != 0 { let t = 2.0 * (c as f64) * (2.0 * pi * ((r % kk) as f64) / kk as f64).sin() / (pi * r as f64); tot += t; abs += (2.0 * c as f64 / (pi * r as f64)).abs(); n += 1; }
        r += 1; } }
    let u = 1.1102230246251565e-16;
    (tot / c0, ((n as f64 + 32.0) * u * abs) / c0 + 4.0 * u * (tot / c0).abs())
}

// graded score: 1000*least WE level - number of (a,sigma) firing at that level (more gradient for the hunt)
fn score_g(v: &[I], qmax: I) -> I {
    if fast(v) || tail_cert(v).is_some() { return 0; }
    if std::env::var("MDR_WX").is_ok() { return 1000 * match cert_m(v, qmax, 0) { Some((q, _, _, _)) => q, None => qmax + 1 }; }
    let q = match cert_m(v, qmax, 2) { Some((q, _, _, _)) => q, None => return 1000 * (qmax + 1) };
    let mut cnt = 0; let m1 = dd(v);
    for a in 1..q { if gcd(a, q) != 1 { continue; } for sgn in [1 as I, -1] {
        if let Some((lo, hi, z)) = n_interval(v, q, a, sgn) {
            if z.is_empty() { cnt += 1; continue; }
            let zmin = *z.iter().min().unwrap(); let zmax = *z.iter().max().unwrap();
            let l2 = R::new(1, m1 * zmin); let u2 = R::new(m1 - 1, m1 * zmax);
            let ll = if lo.lt(&l2) { l2 } else { lo }; let uu = if hi.lt(&u2) { hi } else { u2 };
            if ll.le(&uu) { cnt += 1; } } } }
    1000 * q - cnt
}
fn hunt2(m: usize, h: I, secs: u64, seed: u64, qmax: I, seeds: &str, out: &str) {
    let starts: Vec<Vec<I>> = read_fams(seeds).into_iter().filter(|v| v.len() == m).collect();
    let mut rng = Rng(seed * 2654435761 + 977);
    let t0 = std::time::Instant::now();
    let mut f = std::fs::OpenOptions::new().create(true).append(true).open(out).unwrap();
    let (mut best_ever, mut evals, mut restarts, mut written) = (0 as I, 0u64, 0u64, 0u64);
    let ok = |w: &Vec<I>| -> bool { in_class(w) && { let (u, e) = u1(w); u - e >= 1.0 } };
    while t0.elapsed().as_secs() < secs {
        restarts += 1;
        let mut v = starts[rng.below(starts.len() as u64) as usize].clone();
        if !ok(&v) { continue; }
        let mut cur = score_g(&v, qmax); evals += 1; let mut stall = 0;
        while stall < 1500 && t0.elapsed().as_secs() < secs {
            let mut w = v.clone();
            let k = 1 + rng.below(2) as usize;
            for _ in 0..k { let i = rng.below(m as u64) as usize;
                w[i] = match rng.below(5) { 0 => 1 + rng.below(h as u64) as I,
                    1 => { let d = 2 + rng.below(2 * m as u64) as I; (d * (1 + rng.below((h / d) as u64) as I)).max(1) },
                    2 => (w[i] + rng.below(7) as I - 3).max(1).min(h),
                    3 => { let j = rng.below(m as u64) as usize; let c = 2 + rng.below(6) as I; (w[j] * c).min(h) },
                    _ => { let j = rng.below(m as u64) as usize; let l = rng.below(m as u64) as usize; (w[j] + w[l]).min(h) } }; }
            if !ok(&w) { stall += 1; continue; }
            let sc = score_g(&w, qmax); evals += 1;
            if sc >= cur { if sc > cur { stall = 0; } else { stall += 1; } v = w; cur = sc; } else { stall += 1; }
            if cur > best_ever { best_ever = cur; let mut sv = v.clone(); sv.sort();
                eprintln!("[{}s] m={} best WEq={} evals={} restarts={} v={:?}", t0.elapsed().as_secs(), m, cur, evals, restarts, sv); }
        }
        if cur > 1000 * (2 * m as I + 1) && written < 2000 { let mut sv = v.clone(); sv.sort(); written += 1;
            writeln!(f, "{} | m={} WEq={}", sv.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","), m, if cur > qmax { "none".to_string() } else { cur.to_string() }).unwrap(); }
    }
    eprintln!("DONE m={} H={} secs={} evals={} restarts={} best={} written={}", m, h, secs, evals, restarts, best_ever, written);
    writeln!(f, "# DONE m={} H={} evals={} restarts={} best={} written={}", m, h, evals, restarts, best_ever, written).unwrap();
}


fn seedgen(m: usize, count: usize, seed: u64, hmax: I) {
    let mut rng = Rng(seed * 7919 + 3); let mut got = 0; let mut tries = 0u64;
    while got < count && tries < 5_000_000 { tries += 1;
        let mut v: Vec<I> = (1..=m as I).collect();
        let k = 1 + rng.below(3) as usize;
        for _ in 0..k { let i = rng.below(m as u64) as usize; v[i] = m as I + 1 + rng.below((hmax - m as I) as u64) as I; }
        if in_class(&v) { let (u, e) = u1(&v); if u - e >= 1.0 { let mut s = v.clone(); s.sort(); println!("{}", s.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")); got += 1; } } }
}
// T2 hunt: minimise (2m+1)/2 * ML over gcd-1 families with (m+1) | some speed, heights <= h
fn ml_val(v: &[I]) -> (I, I) { ml(v).0 }
fn hunt3(m: usize, h: I, secs: u64, seed: u64) {
    let mut rng = Rng(seed * 104729 + 11); let t0 = std::time::Instant::now();
    let m1 = m as I + 1; let mut best: Option<((I, I), Vec<I>)> = None; let mut evals = 0u64;
    let okd = |w: &Vec<I>| -> bool { let mut s = w.clone(); s.sort(); s.dedup(); s.len() == w.len() && s[0] > 0 && gcdv(w) == 1 && w.iter().any(|x| x % m1 == 0) };
    while t0.elapsed().as_secs() < secs {
        let mut v: Vec<I> = (1..=m as I).collect(); let i = rng.below(m as u64) as usize; v[i] = m1 * (1 + rng.below(3) as I);
        if !okd(&v) { continue; }
        let mut cur = ml_val(&v); let mut stall = 0;
        while stall < 300 && t0.elapsed().as_secs() < secs {
            let mut w = v.clone();
            for _ in 0..(1 + rng.below(2)) { let i = rng.below(m as u64) as usize;
                w[i] = match rng.below(4) { 0 => 1 + rng.below(h as u64) as I, 1 => m1 * (1 + rng.below((h / m1) as u64) as I),
                    2 => (w[i] + rng.below(5) as I - 2).max(1).min(h), _ => { let j = rng.below(m as u64) as usize; let l = rng.below(m as u64) as usize; (w[j] + w[l]).min(h) } }; }
            if !okd(&w) { stall += 1; continue; }
            let s = ml_val(&w); evals += 1;
            if !lt(cur, s) { if lt(s, cur) { stall = 0; } else { stall += 1; } v = w; cur = s; } else { stall += 1; }
            let better = match &best { None => true, Some((b, _)) => lt(cur, *b) };
            if better { let mut sv = v.clone(); sv.sort(); best = Some((cur, sv.clone()));
                eprintln!("[{}s] m={} best ML={}/{} ratio_to_2/(2m+1)={:.5} v={:?}", t0.elapsed().as_secs(), m, cur.0, cur.1, (cur.0 as f64 / cur.1 as f64) * (2.0 * m as f64 + 1.0) / 2.0, sv); }
        }
    }
    eprintln!("DONE m={} H={} evals={}", m, h, evals);
}


// independent check of WX: max of full gap over the window t in a/q + sgn*[lo,hi] via all candidates c/(v_i+v_j)
fn wx_full(v: &[I], qmax: I) -> Option<(I, I, I)> {
    let m1 = dd(v);
    let good = |p: I, qd: I| v.iter().all(|&x| { let r = ((x % qd) * (p % qd) % qd + qd) % qd; m1 * r.min(qd - r) >= qd });
    let qmin: I = std::env::var("MDR_QMIN").ok().map(|x| { let t: I = x.parse().unwrap(); if t == -1 { v.len() as I + 2 } else { t } }).unwrap_or(2);
    for q in qmin..=qmax { for a in 1..q { if gcd(a, q) != 1 { continue; } for sgn in [1 as I, -1] {
        if let Some((lo, hi, _z)) = n_interval(v, q, a, sgn) {
            // t range: a/q + sgn*[lo,hi]  -> [tl, th]
            let (e1, e2) = if sgn == 1 { (lo, hi) } else { (R::new(-hi.n, hi.d), R::new(-lo.n, lo.d)) };
            let tl = R::new(a * e1.d + e1.n * q, q * e1.d); let th = R::new(a * e2.d + e2.n * q, q * e2.d);
            if good(tl.n, tl.d) || good(th.n, th.d) { return Some((q, a, sgn)); }
            let mut seen = std::collections::HashSet::new();
            for i in 0..v.len() { for j in i..v.len() { let s = v[i] + v[j]; if !seen.insert(s) { continue; }
                let c0 = (tl.n * s + tl.d - 1).div_euclid(tl.d); let c1 = (th.n * s).div_euclid(th.d);
                let mut c = c0; while c <= c1 { if good(c, s) { return Some((q, a, sgn)); } c += 1; } } }
        } } } }
    None
}


fn enum_w(m: usize, h: I, tmin: I) {
    std::env::set_var("MDR_QMIN", "-1");
    let mut idx: Vec<I> = (1..=m as I).collect();
    let (mut all, mut cls, mut failwe, mut failwx, mut printed) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let q2 = 2 * m as I + 1; let t0 = std::time::Instant::now();
    loop {
        all += 1;
        let v = &idx;
        if v[m - 1] >= tmin && gcdv(v) == 1 && is_dc(v) && (std::env::var("MDR_DCONLY").is_ok() || (l1o(v) && not_sf(v))) {
            cls += 1;
            if cert_m(v, q2, 2).is_none() { failwe += 1;
                let wx = cert_m(v, q2, 0).is_some(); if !wx { failwx += 1; }
                if printed < 200 { printed += 1; let (u, _) = u1(v); println!("FAILWE {:?} WX_window={} U1={:.6} WXany={:?}", v, wx, u, { std::env::set_var("MDR_QMIN", "2"); let r = cert_m(v, 80, 0); std::env::set_var("MDR_QMIN", "-1"); r }); } }
        }
        let mut i = m; loop { if i == 0 { println!("enumW m={} H={} maxv>={} all={} class_superset={} fail_WE_window={} fail_WX_window={} secs={}", m, h, tmin, all, cls, failwe, failwx, t0.elapsed().as_secs()); return; }
            i -= 1; if idx[i] < h - (m - 1 - i) as I { idx[i] += 1; for j in i + 1..m { idx[j] = idx[j - 1] + 1; } break; } }
        if all % 50_000_000 == 0 { eprintln!("progress all={} cls={} failWE={} t={}s", all, cls, failwe, t0.elapsed().as_secs()); }
    }
}

fn mdr_main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args[0].as_str() {
        "ml" => for a in &args[1..] { describe(&parse(a)); },
        "shift" => { // shift v ph D
            let v = parse(&args[1]); let ph = parse(&args[2]); let d: I = args[3].parse().unwrap();
            let (b, t) = ml_shift(&v, &ph, d); println!("shift v={:?} ph={:?}/{} sup gap={}/{} at t={}/{}", v, ph, d, b.0, b.1, t.0, t.1); }
        "cert" => { // cert qmax file : per family least cert level (WX), least WI level, tao window, least witness
            let qmax: I = args[1].parse().unwrap();
            for v in read_fams(&args[2]) { let m = v.len() as I;
                let c = cert(&v, qmax, false); let ci = cert(&v, qmax, true); let ce = cert_m(&v, qmax, 2);
                println!("{} | m={} cls={} TC={:?} WX={:?} WI={:?} WE={:?} tao={:?} least={:?} lemmaP={} fast={}", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","), m, in_class(&v), tail_cert(&v), c, ci, ce, tao_window(&v), least_witness(&v, 3 * m * m), lemma_p(&v), fast(&v)); } }
        "certv" => { let qmax: I = args[1].parse().unwrap(); for a in &args[2..] { let v = parse(a); println!("{:?} WX={:?} WI={:?}", v, cert(&v, qmax, false), cert(&v, qmax, true)); } }
        "lemmap" => { let fams = read_fams(&args[1]); let n = fams.len(); let c = fams.iter().filter(|v| lemma_p(v)).count();
            let u = fams.iter().filter(|v| { let q = v.len() as I + 1; let mult: Vec<&I> = v.iter().filter(|x| *x % q == 0).collect(); mult.len() == 1 && v.iter().all(|x| x <= mult[0]) }).count();
            let one = fams.iter().filter(|v| { let q = v.len() as I + 1; v.iter().filter(|x| *x % q == 0).count() == 1 }).count();
            println!("lemmaP {}: certified {}/{} ; unique multiple is largest {}/{} ; exactly one multiple {}/{}", args[1], c, n, u, n, one, n); }
        "tao" => { let fams = read_fams(&args[1]); let n = fams.len(); let mut ok = 0; let mut exc = vec![];
            for v in &fams { match tao_window(v) { Some(_) => ok += 1, None => exc.push((v.clone(), least_witness(v, 400))) } }
            println!("tao {}: window-lonely {}/{}", args[1], ok, n); for e in exc { println!("  exception {:?} least={:?}", e.0, e.1); } }
        "enum" => enumerate(args[1].parse().unwrap(), args[2].parse().unwrap()),
        "u1" => for a in &args[1..] { let v = parse(a); println!("{:?} U1={:?}", v, u1(&v)); },
        "hunt2" => hunt2(args[1].parse().unwrap(), args[2].parse().unwrap(), args[3].parse().unwrap(), args[4].parse().unwrap(), args[5].parse().unwrap(), &args[6], &args[7]),
        "seedgen" => seedgen(args[1].parse().unwrap(), args[2].parse().unwrap(), args[3].parse().unwrap(), args[4].parse().unwrap()),
        "hunt3" => hunt3(args[1].parse().unwrap(), args[2].parse().unwrap(), args[3].parse().unwrap(), args[4].parse().unwrap()),
        "wxfull" => { let qmax: I = args[1].parse().unwrap(); for a in &args[2..] { let v = parse(a); println!("{:?} WXfull={:?} WX={:?} WE={:?}", v, wx_full(&v, qmax), cert_m(&v, qmax, 0), cert_m(&v, qmax, 2)); } },
        "dbg" => { let v = parse(&args[1]); let q: I = args[2].parse().unwrap(); let a: I = args[3].parse().unwrap(); let sg: I = args[4].parse().unwrap(); let r = n_interval(&v, q, a, sg); println!("{:?}", r); if let Some((lo, hi, z)) = r { println!("z_exact={:?}", z_exact(&z, lo, hi, dd(&v), 2_000_000)); } },
        "enumw" => enum_w(args[1].parse().unwrap(), args[2].parse().unwrap(), args.get(3).map_or(0, |x| x.parse().unwrap())),
        "hunt" => hunt(args[1].parse().unwrap(), args[2].parse().unwrap(), args[3].parse().unwrap(), args[4].parse().unwrap(), args[5].parse().unwrap(), &args[6]),
        _ => panic!("mode"),
    }
}
