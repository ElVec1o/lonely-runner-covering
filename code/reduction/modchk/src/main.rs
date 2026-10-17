// modchk: independent checker (shares no code with the other programs).
//
// Quantities (Lean `rieszSharpFiresQ`, `BridgeDisjunctionQPrim`):
//   web = nonzero c in {-1,0,1}^m, sum c_i v_i = 0 ; m = k+1 speeds, k+2 = m+1 runners.
//   M  = 1 + sum_web (-1/2)^|supp c| ; W1 = sum_web |supp c| (-1/2)^|supp c|.
//   Riesz fires <=> 0 < M and 99225*((k+1)M - 2W1 + M) <= 10000 (k+2)^2 M.
//   witness (p,q): q <= (k+2) * min(r, q-r), r = v_i p mod q, for all i.
// Two independent routes to (M, W1):
//   (a) meet-in-the-middle enumeration of the web with support histogram N_s (m <= 26);
//   (b) Laurent-polynomial DP of prod (1 - cos 2 pi v_j t) with a carried "one factor replaced"
//       channel: A = CT prod a(z^{v_j}), S = CT sum_i prod_{j!=i} a(z^{v_j}) b(z^{v_i}).
//       With a = 2 - z - 1/z, b = 2 + z + 1/z: A = 2^m M, S = 2^m sum_i (2 M_i - M).
// ML exact: max over candidates n/(v_i+v_j), i <= j, of min_l ||v_l n/(v_i+v_j)|| (exact fractions).
use num_bigint::BigInt;
use num_traits::{CheckedAdd, CheckedMul, ToPrimitive, Zero};
use rayon::prelude::*;
use std::collections::HashMap;

fn gcd(a: i64, b: i64) -> i64 { let (mut x, mut y) = (a.abs(), b.abs()); while y != 0 { let t = x % y; x = y; y = t; } x }
fn gcd_all(v: &[i64]) -> i64 { v.iter().fold(0, |a, &b| gcd(a, b)) }

// ---------------- (b) DP route -----------------
fn dp_pair<T>(v: &[i64], a: &[i64], b: &[i64]) -> Option<(T, T)>
where T: Clone + Zero + CheckedAdd + CheckedMul + From<i64> {
    let d = (a.len() as i64 - 1) / 2;
    let s: i64 = v.iter().sum();
    let off = d * s; let len = (2 * off + 1) as usize;
    let mut f = vec![T::zero(); len]; let mut g = vec![T::zero(); len];
    f[off as usize] = T::from(1i64);
    let mut reach = 0i64;
    let ac: Vec<T> = a.iter().map(|&x| T::from(x)).collect();
    let bc: Vec<T> = b.iter().map(|&x| T::from(x)).collect();
    for &x in v {
        let nreach = reach + d * x;
        let mut nf = vec![T::zero(); len]; let mut ng = vec![T::zero(); len];
        for idx in (off - reach)..=(off + reach) {
            let iu = idx as usize;
            let fz = f[iu].is_zero(); let gz = g[iu].is_zero();
            if fz && gz { continue; }
            for k in 0..a.len() {
                let ni = (idx + (k as i64 - d) * x) as usize;
                if a[k] != 0 {
                    if !fz { nf[ni] = nf[ni].checked_add(&f[iu].checked_mul(&ac[k])?)?; }
                    if !gz { ng[ni] = ng[ni].checked_add(&g[iu].checked_mul(&ac[k])?)?; }
                }
                if b[k] != 0 && !fz { ng[ni] = ng[ni].checked_add(&f[iu].checked_mul(&bc[k])?)?; }
            }
        }
        f = nf; g = ng; reach = nreach;
    }
    Some((f[off as usize].clone(), g[off as usize].clone()))
}
fn dp_pair_big(v: &[i64], a: &[i64], b: &[i64]) -> (BigInt, BigInt) {
    if let Some((x, y)) = dp_pair::<i128>(v, a, b) { return (BigInt::from(x), BigInt::from(y)); }
    dp_pair::<BigInt>(v, a, b).unwrap()
}
// full coefficient array of prod (2 - z^v - z^-v)  (= 2^m prod(1-cos)), i128
fn dp_full(v: &[i64]) -> (Vec<i128>, i64) {
    let s: i64 = v.iter().sum(); let len = (2 * s + 1) as usize;
    let mut f = vec![0i128; len]; f[s as usize] = 1;
    for &x in v { let mut nf = vec![0i128; len];
        for idx in 0..len { let c = f[idx]; if c == 0 { continue; } let i = idx as i64;
            nf[idx] += 2 * c; if i + x < len as i64 { nf[(i + x) as usize] -= c; } if i - x >= 0 { nf[(i - x) as usize] -= c; } }
        f = nf; }
    (f, s)
}

// ---------------- (a) MITM web histogram -----------------
fn half_hist(v: &[i64]) -> HashMap<i64, Vec<u64>> {
    let h = v.len(); let mut mp: HashMap<i64, Vec<u64>> = HashMap::new();
    let tot = 3usize.pow(h as u32);
    for code in 0..tot { let mut c = code; let mut s = 0i64; let mut sup = 0usize;
        for i in 0..h { let dgt = c % 3; c /= 3; if dgt == 1 { s += v[i]; sup += 1; } else if dgt == 2 { s -= v[i]; sup += 1; } }
        let e = mp.entry(s).or_insert_with(|| vec![0u64; h + 1]); e[sup] += 1; }
    mp
}
fn web_hist(v: &[i64]) -> Vec<u64> {
    let m = v.len(); let h = m / 2;
    let l = half_hist(&v[..h]); let r = half_hist(&v[h..]);
    let mut n = vec![0u64; m + 1];
    for (s, hl) in l.iter() { if let Some(hr) = r.get(&(-s)) {
        for (a, &x) in hl.iter().enumerate() { if x == 0 { continue; } for (b, &y) in hr.iter().enumerate() { n[a + b] += x * y; } } } }
    n[0] -= 1; // zero vector
    n
}

// ---------------- Riesz -----------------
// returns (fires, A=2^m M, S=2^m*sum(2M_i-M)) via DP
fn riesz_dp(v: &[i64]) -> (bool, BigInt, BigInt) {
    let (a, s) = dp_pair_big(v, &[-1, 2, -1], &[1, 2, 1]);
    let m = v.len() as i64; let k2 = BigInt::from(m + 1);
    let fires = a > BigInt::zero() && BigInt::from(99225) * (&s + &a) <= BigInt::from(10000) * &k2 * &k2 * &a;
    (fires, a, s)
}
fn riesz_dp_i128(v: &[i64]) -> Option<bool> {
    let (a, s) = dp_pair::<i128>(v, &[-1, 2, -1], &[1, 2, 1])?;
    let k2 = (v.len() as i128) + 1;
    Some(a > 0 && 99225 * (s + a) <= 10000 * k2 * k2 * a)
}
// degree-2 (cot^2 Markov, R_2 definition, recomputed by the carried-channel DP)
fn riesz_deg2_cot(v: &[i64]) -> (bool, f64) {
    let (a, s) = dp_pair_big(v, &[1, -4, 6, -4, 1], &[-1, 0, 2, 0, -1]);
    let n = BigInt::from(v.len() as i64 + 1);
    let fires = a > BigInt::zero() && BigInt::from(99225) * (&s + &a) <= BigInt::from(10000) * &n * &n * &a;
    let ratio = (s.to_f64().unwrap() + a.to_f64().unwrap()) / a.to_f64().unwrap() / ((v.len() + 1) as f64).powi(2) * 9.9225;
    (fires, ratio)
}
// beck's e-test: ratio = tan^{2e}(pi/K) * S/A with P=(1-cos)^e, G=(1+cos)^e ; fires iff ratio<1 (f64 ratio of exact ints)
fn beck_e(v: &[i64], e: usize) -> f64 {
    let (a, g) = match e { 1 => (vec![-1i64, 2, -1], vec![1i64, 2, 1]), 2 => (vec![1i64, -4, 6, -4, 1], vec![1i64, 4, 6, 4, 1]), _ => panic!() };
    let (aa, ss) = dp_pair_big(v, &a, &g);
    let kk = (v.len() + 1) as f64; let lam = (std::f64::consts::PI / kk).tan().powi(2 * e as i32);
    if aa <= BigInt::zero() { return f64::INFINITY; }
    lam * ss.to_f64().unwrap() / aa.to_f64().unwrap()
}
// U_1 = sum_i int_{B_i} P / int P, B_i = {||v_i t|| < 1/(m+1)}  (f64 kernel, exact coefficients)
fn u1(v: &[i64]) -> f64 {
    let (f, s) = dp_full(v); let dl = 1.0 / (v.len() as f64 + 1.0); let pi = std::f64::consts::PI;
    let p0 = f[s as usize] as f64; let mut tot = 0.0;
    for &x in v { let mut r = -(s / x); while r * x <= s { let h = r * x; let c = f[(h + s) as usize] as f64;
            let kr = if r == 0 { 2.0 * dl } else { (2.0 * pi * r as f64 * dl).sin() / (pi * r as f64) }; tot += c * kr; r += 1; } }
    tot / p0
}

// ---------------- witnesses -----------------
fn witness_at(v: &[i64], q: i64) -> Option<i64> {
    let k2 = v.len() as i64 + 1; let vr: Vec<i64> = v.iter().map(|&x| x.rem_euclid(q)).collect();
    'p: for p in 1..q { for &x in &vr { let r = (x * p) % q; if k2 * r.min(q - r) < q { continue 'p; } } return Some(p); }
    None
}
fn wit_count(v: &[i64], qmax: i64) -> usize { (1..=qmax).filter(|&q| witness_at(v, q).is_some()).count() }
fn least_wit(v: &[i64], qmax: i64) -> Option<(i64, i64)> { for q in 1..=qmax { if let Some(p) = witness_at(v, q) { return Some((p, q)); } } None }
fn cap(v: &[i64]) -> i64 { let s: i64 = v.iter().sum(); 8 * (63 - ((s + 2) as u64).leading_zeros() as i64) }

// ---------------- ML exact -----------------
fn ml_exact(v: &[i64]) -> (i64, i64) { let r = ml_exact_t(v); (r.0, r.1) }
fn ml_exact_t(v: &[i64]) -> (i64, i64, i64, i64) { // (num, den) of max_t min_i ||v_i t||, and maximiser t = tn/td
    let m = v.len(); let mut bn = 0i64; let mut bd = 1i64; let mut tn = 0i64; let mut td = 1i64;
    for i in 0..m { for j in i..m { let d = v[i] + v[j];
        for n in 0..d { let mut wn = d; // min numerator over l, value = wn/d (distance *d)
            for &x in v { let r = ((x % d) * n) % d; let t = r.min(d - r); if t < wn { wn = t; } if (wn as i128) * (bd as i128) <= (bn as i128) * (d as i128) { break; } }
            if (wn as i128) * (bd as i128) > (bn as i128) * (d as i128) { bn = wn; bd = d; tn = n; td = d; } } } }
    let g = gcd(bn, bd); let gt = gcd(tn, td); (bn / g, bd / g, tn / gt, td / gt)
}

fn l1o_imprimitive(v: &[i64]) -> Option<(usize, i64)> {
    for l in 0..v.len() { let g = v.iter().enumerate().filter(|(i, _)| *i != l).fold(0, |a, (_, &b)| gcd(a, b)); if g != 1 { return Some((l, g)); } }
    None
}
fn missing_divisor(v: &[i64]) -> Option<i64> { let k2 = v.len() as i64 + 1; (2..=k2).find(|&j| v.iter().all(|&x| x % j != 0)) }
fn frac(n: &BigInt, m: usize) -> String { // n / 2^m reduced
    let mut n = n.clone(); let mut e = m as i64; let two = BigInt::from(2);
    while e > 0 && (&n % &two).is_zero() && !n.is_zero() { n /= &two; e -= 1; }
    if n.is_zero() { return "0".into(); } format!("{}/{}", n, BigInt::from(1) << e)
}

fn parse(s: &str) -> Vec<i64> { s.split(|c: char| c == ',' || c.is_whitespace() || c == '[' || c == ']').filter(|x| !x.is_empty()).map(|x| x.parse().unwrap()).collect() }

fn eval(v: &[i64], full: bool) {
    let m = v.len(); let sv: i64 = v.iter().sum();
    println!("== v={:?}", v);
    println!("  m={} runners={} sum={} gcd={}", m, m + 1, sv, gcd_all(v));
    let (fires, a, s) = riesz_dp(v);
    let mut webinfo = String::new();
    if m <= 26 {
        let n = web_hist(v); let web: u64 = n.iter().sum();
        let mut mq = BigInt::from(1) << m; let mut wq = BigInt::zero();
        for (sz, &c) in n.iter().enumerate() { if c == 0 { continue; } let t = BigInt::from(c) * (BigInt::from(1) << (m - sz)); let t = if sz % 2 == 1 { -t } else { t };
            mq += &t; wq += BigInt::from(sz as i64) * &t; }
        let k1 = BigInt::from(m as i64); let k2 = BigInt::from(m as i64 + 1);
        let fires_web = mq > BigInt::zero() && BigInt::from(99225) * (&k1 * &mq - BigInt::from(2) * &wq + &mq) <= BigInt::from(10000) * &k2 * &k2 * &mq;
        let agree_m = mq == a; let agree_s = (&k1 * &mq - BigInt::from(2) * &wq) == s;
        webinfo = format!("  |web|={} N_s={:?} M={} W1={} Riesz(web)={} | DP agree M:{} S:{} Riesz(DP)={}", web, n, frac(&mq, m), frac(&wq, m), fires_web, agree_m, agree_s, fires);
        assert!(agree_m && agree_s && fires_web == fires, "ROUTE DISAGREEMENT");
    }
    if !webinfo.is_empty() { println!("{}", webinfo); } else { println!("  M={} Riesz(DP)={}", frac(&a, m), fires); }
    let c = cap(v);
    let lw = least_wit(v, 5000);
    println!("  cap={} wit<=cap={} wit<=112={} wit<=500={} least witness (p,q)={:?} score={}", c, wit_count(v, c), wit_count(v, 112), wit_count(v, 500), lw, 1000 * (fires as usize) + wit_count(v, c));
    let (mn, md, tn, td) = ml_exact_t(v);
    println!("  ML={}/{} (m+1)ML={:.4} maximiser t={}/{} is witness={}", mn, md, (m + 1) as f64 * mn as f64 / md as f64, tn, td, witness_at_pq(v, tn, td));
    println!("  L1O-imprimitive={:?} missing divisor j<=m+1={:?} odd count={}", l1o_imprimitive(v), missing_divisor(v), v.iter().filter(|&&x| x % 2 == 1).count());
    if full {
        let (f2, r2) = riesz_deg2_cot(v);
        println!("  R2(cot^2, groth def) fires={} (E_F[1+sum h]*9.9225/K^2={:.4}) | beck e1 ratio={:.4} e2 ratio={:.4} | U_1={:.4}", f2, r2, beck_e(v, 1), beck_e(v, 2), if m <= 30 { u1(v) } else { f64::NAN });
    }
}

// complete enumeration of m-subsets of [1,h]
fn enumerate(m: usize, h: i64) {
    let mut firsts: Vec<(i64, i64, i64)> = vec![]; for a in 1..=h { for b in (a + 1)..=h { for c in (b + 1)..=h { firsts.push((a, b, c)); } } }
    #[derive(Default, Clone)]
    struct St { n: u64, prim: u64, nsf: u64, fire: u64, min_fire: (i64, i64), tight: Vec<Vec<i64>>, below1: u64, hil_viol: u64, fire_lt143: u64, min_fail_nsf_prim: (i64, i64), n_primnsf: u64, primnsf_fail: u64 }
    let res: Vec<St> = firsts.par_iter().with_max_len(1).map(|&(a, b, c)| {
        let mut st = St { min_fire: (1, 1), min_fail_nsf_prim: (1, 1), ..Default::default() };
        let mut cur = vec![a, b, c];
        fn rec(cur: &mut Vec<i64>, m: usize, h: i64, st: &mut St) {
            if cur.len() == m { let v = cur.clone(); st.n += 1;
                let fires = riesz_dp_i128(&v).unwrap(); let (mn, md) = ml_exact(&v); let k2 = (m + 1) as i64;
                let prim = gcd_all(&v) == 1; if prim { st.prim += 1; }
                let nsf = web_hist(&v).iter().sum::<u64>() > 0; if nsf { st.nsf += 1; }
                if prim && nsf { st.n_primnsf += 1; if !fires { st.primnsf_fail += 1; if mn * st.min_fail_nsf_prim.1 < st.min_fail_nsf_prim.0 * md { st.min_fail_nsf_prim = (mn, md); } } }
                // (m+1)ML compared with 1 : mn*k2 vs md
                if mn * k2 < md { st.below1 += 1; }
                if mn * k2 == md { st.tight.push(v.clone()); }
                if fires { st.fire += 1; if mn * k2 <= md { st.hil_viol += 1; }
                    if mn * st.min_fire.1 < st.min_fire.0 * md { st.min_fire = (mn, md); }
                    if (mn * k2 * 100) < 143 * md { st.fire_lt143 += 1; } }
                return; }
            let start = *cur.last().unwrap() + 1; let need = m - cur.len();
            for x in start..=(h - need as i64 + 1) { cur.push(x); rec(cur, m, h, st); cur.pop(); }
        }
        rec(&mut cur, m, h, &mut st); st }).collect();
    let mut t = St { min_fire: (1, 1), min_fail_nsf_prim: (1, 1), ..Default::default() };
    for s in res { t.n += s.n; t.prim += s.prim; t.nsf += s.nsf; t.fire += s.fire; t.below1 += s.below1; t.hil_viol += s.hil_viol; t.fire_lt143 += s.fire_lt143; t.tight.extend(s.tight);
        t.n_primnsf += s.n_primnsf; t.primnsf_fail += s.primnsf_fail;
        if s.min_fire.0 * t.min_fire.1 < t.min_fire.0 * s.min_fire.1 { t.min_fire = s.min_fire; }
        if s.min_fail_nsf_prim.0 * t.min_fail_nsf_prim.1 < t.min_fail_nsf_prim.0 * s.min_fail_nsf_prim.1 { t.min_fail_nsf_prim = s.min_fail_nsf_prim; } }
    let k2 = (m + 1) as f64;
    println!("enum m={} H={} families={} primitive={} nonSF={} prim&nonSF={} (Riesz-failing among them {}) Riesz-fires={}", m, h, t.n, t.prim, t.nsf, t.n_primnsf, t.primnsf_fail, t.fire);
    println!("  (m+1)ML<1 (LRC violation) = {} ; tight ((m+1)ML=1) = {} : {:?}", t.below1, t.tight.len(), t.tight);
    println!("  min (m+1)ML over Riesz-firing = {}/{} *{} = {:.4} ; firing with (m+1)ML<1.43: {} ; U1 violations (fires but ML<=1/(m+1)): {}", t.min_fire.0, t.min_fire.1, m + 1, k2 * t.min_fire.0 as f64 / t.min_fire.1 as f64, t.fire_lt143, t.hil_viol);
}


fn riesz2_i128(v: &[i64]) -> Option<bool> {
    let (a, s) = dp_pair::<i128>(v, &[1, -4, 6, -4, 1], &[-1, 0, 2, 0, -1])?;
    let n = v.len() as i128 + 1; Some(a > 0 && 99225 * (s + a) <= 10000 * n * n * a)
}
fn gl5(v: &[i64], qmax: i64) -> Option<i64> { // Leave-one-out gcd lemma applicability (assumes LR for |S| speeds)
    let m = v.len() as i64;
    for q in 2..=qmax { let s: Vec<bool> = v.iter().map(|&x| x % q == 0).collect(); let ns = s.iter().filter(|&&b| b).count();
        if ns == 0 || ns == v.len() { continue; }
        let mut tot = 0i64; for (i, &x) in v.iter().enumerate() { if s[i] { continue; } let g = gcd(x, q); let qi = q / g; tot += g * ((2 * qi + m) / (m + 1)); if tot >= q { break; } }
        if tot < q { return Some(q); } }
    None
}
// residual census: families surviving R1, Lemma-4 (divisor-complete), Lemma-5 (L1O-primitive), R2, GL5
fn resid(m: usize, h: i64, show: usize, tmin: i64) {
    let mut firsts: Vec<(i64, i64, i64)> = vec![]; for a in 1..=h { for b in (a + 1)..=h { for c in (b + 1)..=h { firsts.push((a, b, c)); } } }
    let res: Vec<(Vec<u64>, Vec<(i64, i64, Vec<i64>, i64)>)> = firsts.par_iter().with_max_len(1).map(|&(a, b, c)| {
        let mut cnt = vec![0u64; 8]; let mut surv = vec![];
        fn rec(cur: &mut Vec<i64>, m: usize, h: i64, tmin: i64, cnt: &mut Vec<u64>, surv: &mut Vec<(i64, i64, Vec<i64>, i64)>) {
            if cur.len() == m { let v = cur.clone(); if v[m - 1] <= tmin { return; } cnt[0] += 1;
                if gcd_all(&v) != 1 || web_hist(&v).iter().sum::<u64>() == 0 { return; } cnt[1] += 1;
                if riesz_dp_i128(&v).unwrap() { return; } cnt[2] += 1;
                if missing_divisor(&v).is_some() { return; } cnt[3] += 1;
                if l1o_imprimitive(&v).is_some() { return; } cnt[4] += 1;
                if riesz2_i128(&v).unwrap() { return; } cnt[5] += 1;
                if gl5(&v, 2000).is_some() { return; } cnt[6] += 1;
                let (mn, md) = ml_exact(&v); let lq = least_wit(&v, 5000).map_or(-1, |x| x.1);
                surv.push((mn, md, v, lq)); return; }
            let start = *cur.last().unwrap() + 1; let need = m - cur.len();
            for x in start..=(h - need as i64 + 1) { cur.push(x); rec(cur, m, h, tmin, cnt, surv); cur.pop(); }
        }
        let mut cur = vec![a, b, c]; rec(&mut cur, m, h, tmin, &mut cnt, &mut surv); (cnt, surv) }).collect();
    let mut cnt = vec![0u64; 8]; let mut surv = vec![];
    for (c, s) in res { for i in 0..8 { cnt[i] += c[i]; } surv.extend(s); }
    let k2 = (m + 1) as i64;
    surv.sort_by(|x, y| ((x.0 * y.1) as i128).cmp(&((y.0 * x.1) as i128)));
    println!("resid (max v > {}) m={} H={} all={} prim&nonSF={} R1-fail={} +divisor-complete={} +L1O-primitive={} +R2-fail={} +GL5-uncovered={}", tmin, m, h, cnt[0], cnt[1], cnt[2], cnt[3], cnt[4], cnt[5], cnt[6]);
    if !surv.is_empty() {
        let mx = surv.last().unwrap(); let mn = &surv[0];
        println!("  residual (m+1)ML range: min {}/{}*{} = {:.4}  max {}/{}*{} = {:.4}", mn.0, mn.1, k2, (k2 * mn.0) as f64 / mn.1 as f64, mx.0, mx.1, k2, (k2 * mx.0) as f64 / mx.1 as f64);
        let mut hist = std::collections::BTreeMap::new(); for s in &surv { let b = ((k2 * s.0) as f64 / s.1 as f64 * 10.0).floor() as i64; *hist.entry(b).or_insert(0u64) += 1; }
        println!("  histogram of floor(10*(m+1)ML): {:?}", hist);
        let maxlq = surv.iter().map(|s| s.3).max().unwrap(); println!("  max least-witness q over residual = {}", maxlq);
        let run = |v: &Vec<i64>| { let mut r = 0; while r < v.len() && v[r] == r as i64 + 1 { r += 1; } r };
        let minrun = surv.iter().map(|s| run(&s.2)).min().unwrap(); println!("  min initial run {{1..r}} over residual: r = {}", minrun);
        for s in surv.iter().rev().take(show) { println!("  top: (m+1)ML={:.4} v={:?} least q={}", (k2 * s.0) as f64 / s.1 as f64, s.2, s.3); }
        for s in surv.iter().take(3) { println!("  bottom: (m+1)ML={:.4} v={:?} least q={}", (k2 * s.0) as f64 / s.1 as f64, s.2, s.3); }
        // U_1 stratum
        let us: Vec<f64> = surv.par_iter().map(|s| u1(&s.2)).collect();
        let nlt = us.iter().filter(|&&u| u < 1.0).count();
        let mut max_ge = 0.0f64; let mut min_lt = f64::INFINITY; let mut ex_ge = vec![];
        for (s, &u) in surv.iter().zip(us.iter()) { let r = (k2 * s.0) as f64 / s.1 as f64; if u >= 1.0 { if r > max_ge { max_ge = r; ex_ge = s.2.clone(); } } else if r < min_lt { min_lt = r; } }
        println!("  U_1<1 (product-weight test, f64) on {} of {} residual; U_1>=1 stratum: {} families, max (m+1)ML there = {:.4} e.g. {:?}; min (m+1)ML with U_1<1 = {:.4}", nlt, surv.len(), surv.len() - nlt, max_ge, ex_ge, min_lt);
    }
}


fn row(v: &[i64]) {
    let m = v.len(); let r1 = riesz_dp(v).0; let (r2, r2r) = riesz_deg2_cot(v); let (mn, md) = ml_exact(v);
    let l1o = l1o_imprimitive(v).is_some(); let md4 = missing_divisor(v).is_some(); let g5 = gl5(v, 5000).is_some();
    let ind2 = gcd_all(v) == 1 && !l1o && !md4;
    let lw = least_wit(v, 5000).map_or(-1, |x| x.1);
    println!("ROW m={} R1={} R2={} r2ratio={:.3} L1Oimp={} missDiv={} GL5={} IND2class={} residual(ind2&!R1&!R2&!GL5)={} (m+1)ML={:.4} leastq={} v={:?}", m, r1, r2, r2r, l1o, md4, g5, ind2, ind2 && !r1 && !r2 && !g5, (m as f64 + 1.0) * mn as f64 / md as f64, lw, v);
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args[0].as_str() {
        "eval" => for a in &args[1..] { eval(&parse(a), false); },
        "rows" => { use std::io::BufRead; for l in std::io::stdin().lock().lines() { let l = l.unwrap(); let l = l.trim(); if l.is_empty() || l.starts_with('#') { continue; } row(&parse(l)); } },
        "full" => for a in &args[1..] { eval(&parse(a), true); },
        "enum" => enumerate(args[1].parse().unwrap(), args[2].parse().unwrap()),
        "resid" => resid(args[1].parse().unwrap(), args[2].parse().unwrap(), args.get(3).map_or(8, |x| x.parse().unwrap()), args.get(4).map_or(0, |x| x.parse().unwrap())),
        "gl5" => for a in &args[2..] { let v = parse(a); println!("gl5 {:?} q<={} -> {:?}", v, args[1], gl5(&v, args[1].parse().unwrap())); },
        "iota" => { // 1..m : least witness, whether witness q<=m exists, Riesz (DP, BigInt)
            let m: i64 = args[1].parse().unwrap(); let v: Vec<i64> = (1..=m).collect();
            let (f, a, _) = riesz_dp(&v);
            let any_le_m = (1..=m).any(|q| witness_at(&v, q).is_some());
            println!("iota m={} Riesz={} M*2^m>0:{} witness q<=m: {} least witness {:?} cap={}", m, f, a > BigInt::zero(), any_le_m, least_wit(&v, 3 * m), cap(&v));
            let qs: Vec<i64> = (1..=6 * (m + 1)).filter(|&q| witness_at(&v, q).is_some()).collect();
            let bad: Vec<i64> = qs.iter().cloned().filter(|q| q % (m + 1) != 0).collect();
            println!("  witness q <= 6(m+1): {:?} ; non-multiples of m+1: {:?}", qs, bad);
        }
        "least" => for a in &args[1..] { let v = parse(a); println!("least {:?} -> {:?}", v, least_wit(&v, 20000)); },
        "ramS6" => { // {1} U L*{1..m-1}, L = lcm(1..Q)
            let m: i64 = args[1].parse().unwrap(); let qq: i64 = args[2].parse().unwrap();
            let mut l = 1i64; for i in 1..=qq { l = l / gcd(l, i) * i; }
            let mut v = vec![1i64]; for i in 1..m { v.push(l * i); }
            let (f, _, _) = riesz_dp(&v); let lw = least_wit(&v, 2000);
            println!("ramS6 m={} Q={} L={} gcd={} Riesz={} least witness={:?} (no witness q<=Q: {})", m, qq, l, gcd_all(&v), f, lw, lw.map_or(true, |(_, q)| q > qq));
        }
        "erdS6" => { // {1..m-1} U {N}, N = n0..n1 : least witness and whether <= m+1 or the stated case-3 form
            let m: i64 = args[1].parse().unwrap(); let n0: i64 = args[2].parse().unwrap(); let n1: i64 = args[3].parse().unwrap();
            let mut fails = 0; let mut worst = 0;
            for nn in n0..=n1 { if nn < m { continue; } let mut v: Vec<i64> = (1..m).collect(); v.push(nn);
                // explicit witnesses from the report
                let ok = if nn % m != 0 { witness_at_pq(&v, 1, m) } else if nn % (m + 1) != 0 { witness_at_pq(&v, 1, m + 1) } else { witness_at_pq(&v, 2 * nn + m + 1, 2 * nn * (m + 1)) };
                if !ok { fails += 1; println!("  stated witness FAILS at N={}", nn); }
                if let Some((_, q)) = least_wit(&v, 5000) { if q > worst { worst = q; } } }
            println!("erdS6 m={} N={}..{}: stated-witness failures={} ; max least-witness q={}", m, n0, n1, fails, worst);
        }
        _ => panic!("mode"),
    }
}
fn witness_at_pq(v: &[i64], p: i64, q: i64) -> bool {
    let k2 = v.len() as i64 + 1;
    v.iter().all(|&x| { let r = ((x as i128 * p as i128).rem_euclid(q as i128)) as i64; k2 * r.min(q - r) >= q })
}
