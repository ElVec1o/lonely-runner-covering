// levelfit: least certificate level per family, fitted against invariants.
// Reuses the exact checker of ../mdr (mdr_base.rs = copy of mdr/src/main.rs,
// only its `main` renamed to `mdr_main`). New code below: invariants, fit table, adversarial hunt.
#![allow(dead_code, unused_variables, unused_mut)]
include!("mdr_base.rs");

// ---- U_D test (same coefficients and error bound as modchk) ----
const CA1: [i64; 3] = [-1, 2, -1];
const CA2: [i64; 5] = [1, -4, 6, -4, 1];
fn coeffs_c(v: &[I], d: usize) -> Option<(Vec<i128>, i64)> {
    let a: &[i64] = if d == 1 { &CA1 } else { &CA2 };
    let dd_ = d as i64; let s: i64 = v.iter().map(|&x| x as i64).sum(); if s > 150_000 { return None; }
    let off = dd_ * s; let len = (2 * off + 1) as usize;
    let mut f = vec![0i128; len]; f[off as usize] = 1; let mut reach = 0i64;
    for &x in v { let x = x as i64; let mut nf = vec![0i128; len];
        for idx in (off - reach)..=(off + reach) { let c = f[idx as usize]; if c == 0 { continue; }
            for (k, &ak) in a.iter().enumerate() { if ak == 0 { continue; } let ni = (idx + (k as i64 - dd_) * x) as usize;
                nf[ni] = nf[ni].checked_add(c.checked_mul(ak as i128)?)?; } }
        f = nf; reach += dd_ * x; }
    Some((f, off))
}
fn u_d(v: &[I], d: usize) -> Option<(f64, f64)> {
    let (f, off) = coeffs_c(v, d)?; let m = v.len(); let kk = (m + 1) as i64; let pi = std::f64::consts::PI;
    let sint: Vec<f64> = (0..kk).map(|j| (2.0 * pi * j as f64 / kk as f64).sin()).collect();
    let c0 = f[off as usize] as f64;
    let mut tot = m as f64 * c0 * 2.0 / kk as f64; let mut abs = tot.abs(); let mut n = m;
    for &x in v { let x = x as i64; let mut r = 1i64; while r * x <= off { let c = f[(off + r * x) as usize];
            if c != 0 && r % kk != 0 { let t = 2.0 * (c as f64) * sint[(r % kk) as usize] / (pi * r as f64); tot += t; abs += (2.0 * c as f64 / (pi * r as f64)).abs(); n += 1; }
            r += 1; } }
    let u = 1.1102230246251565e-16;
    let err = ((n as f64 + 16.0) * u * abs + 16.0 * u * abs) / c0 + 4.0 * u * (tot / c0).abs();
    Some((tot / c0, err))
}
// residual (no U_D certificate) for D = 1, 2; ambiguous counts as residual. None = too big to evaluate.
fn resid_u(v: &[I]) -> Option<(bool, f64, f64)> {
    let (u1, e1) = u_d(v, 1)?; let (u2, e2) = u_d(v, 2)?;
    Some((u1 + e1 >= 1.0 && u2 + e2 >= 1.0, u1, u2))
}

// ---- +-1 relations: min support, count (capped), index of their span in v^perp ----
fn ext_gcd(a: I, b: I) -> (I, I, I) { if b == 0 { (a.abs(), a.signum(), 0) } else { let (g, x, y) = ext_gcd(b, a.rem_euclid(b)); (g, y, x - (a.div_euclid(b)) * y) } }
struct Hnf { m: usize, piv: Vec<Option<Vec<I>>> }
impl Hnf {
    fn new(m: usize) -> Hnf { Hnf { m, piv: vec![None; m] } }
    // returns true if the lattice changed
    fn insert(&mut self, x0: &[I]) -> bool {
        let mut x = x0.to_vec(); let mut changed = false;
        for c in 0..self.m {
            if x[c] == 0 { continue; }
            match self.piv[c].take() {
                None => { if x[c] < 0 { for e in x.iter_mut() { *e = -*e; } } self.piv[c] = Some(x); return true; }
                Some(p) => {
                    if x[c] % p[c] == 0 { let k = x[c] / p[c]; for i in 0..self.m { x[i] -= k * p[i]; } self.piv[c] = Some(p); continue; }
                    let (g, s, t) = ext_gcd(p[c], x[c]);
                    let np: Vec<I> = (0..self.m).map(|i| s * p[i] + t * x[i]).collect();
                    let (pa, xa) = (p[c] / g, x[c] / g);
                    let nx: Vec<I> = (0..self.m).map(|i| xa * p[i] - pa * x[i]).collect();
                    let mut np = np; if np[c] < 0 { for e in np.iter_mut() { *e = -*e; } }
                    self.piv[c] = Some(np); x = nx; changed = true;
                }
            }
        }
        if changed { self.reduce(); }
        changed
    }
    fn reduce(&mut self) {
        for c in (0..self.m).rev() { if self.piv[c].is_none() { continue; }
            let pc = self.piv[c].clone().unwrap();
            for r in 0..c { if let Some(row) = self.piv[r].as_mut() { let k = row[c].div_euclid(pc[c]); if k != 0 { for i in 0..self.m { row[i] -= k * pc[i]; } } } } }
    }
    fn rank(&self) -> usize { self.piv.iter().filter(|p| p.is_some()).count() }
    // index in v^perp (v primitive): prod pivots / v_k, k = the column without a pivot
    fn index(&self, v: &[I]) -> Option<I> {
        if self.rank() + 1 != self.m { return None; }
        let k = (0..self.m).find(|&c| self.piv[c].is_none()).unwrap();
        let mut p: I = 1; for c in 0..self.m { if let Some(r) = &self.piv[c] { p = p.checked_mul(r[c])?; } }
        if p % v[k] != 0 { return Some(-1); } // should not happen
        Some(p / v[k])
    }
}
struct RelInfo { minsupp: usize, nrel: u64, capped: bool, rank: usize, index: Option<I> }
fn relations(v: &[I], cap: u64) -> RelInfo {
    let m = v.len(); let h = m / 2;
    if m > 22 { return RelInfo { minsupp: 0, nrel: 0, capped: true, rank: 0, index: None }; }
    let enumh = |w: &[I]| -> Vec<(I, u32)> { let tot = 3u32.pow(w.len() as u32); (0..tot).map(|code| { let mut c = code; let mut s = 0; for i in 0..w.len() { let dg = c % 3; c /= 3; if dg == 1 { s += w[i]; } else if dg == 2 { s -= w[i]; } } (s, code) }).collect() };
    let l = enumh(&v[..h]); let r = enumh(&v[h..]);
    let mut rmap: HashMap<I, Vec<u32>> = HashMap::new(); for &(s, c) in &r { rmap.entry(s).or_default().push(c); }
    let dec = |code: u32, n: usize, out: &mut [I]| { let mut c = code; for i in 0..n { let dg = c % 3; c /= 3; out[i] = if dg == 1 { 1 } else if dg == 2 { -1 } else { 0 }; } };
    let mut hn = Hnf::new(m); let mut minsupp = usize::MAX; let mut nrel = 0u64; let mut capped = false;
    let mut vec_ = vec![0 as I; m]; let mut done_index = false;
    'o: for &(s, cl) in &l { if let Some(lst) = rmap.get(&(-s)) { for &cr in lst {
        if cl == 0 && cr == 0 { continue; }
        nrel += 1;
        dec(cl, h, &mut vec_[..h]); dec(cr, m - h, &mut vec_[h..]);
        let sp = vec_.iter().filter(|&&x| x != 0).count(); if sp < minsupp { minsupp = sp; }
        if !done_index { hn.insert(&vec_); if hn.index(v) == Some(1) { done_index = true; } }
        if nrel >= cap { capped = true; break 'o; }
    } } }
    RelInfo { minsupp, nrel: nrel / 2, capped, rank: hn.rank(), index: hn.index(v) }
}

fn lcm(a: I, b: I) -> I { if a == 0 || b == 0 { return 0; } a / gcd(a, b) * b }
fn is_prime(p: I) -> bool { p >= 2 && (2..).take_while(|d| d * d <= p).all(|d| p % d != 0) }
fn p0(v: &[I]) -> I { let mut p = 2; loop { if is_prime(p) && !v.iter().any(|&x| x % p == 0) { return p; } p += 1; } }

// least witness with an ML guard: None only if ML < 1/(m+1)
fn qstar(v: &[I]) -> Option<(I, I)> {
    if let Some(w) = least_witness(v, 600) { return Some(w); }
    let (b, arg) = ml(v); let m1 = v.len() as I + 1;
    if b.0 * m1 < b.1 { return None; }
    // witness exists; least one is <= min denominator among maximisers
    let cap = arg.iter().map(|x| x.1).min().unwrap();
    least_witness(v, cap)
}

fn fit_line(src: &str, v: &[I], qcap: I) -> String {
    let m = v.len() as I; let m1 = m + 1;
    let mut s = v.to_vec(); s.sort();
    let (b, _) = ml(&s);
    let qs = qstar(&s);
    let qesc = cert_m(&s, qcap, 2); let qx = cert_m(&s, qcap, 0);
    let q0v = q0(&s); let p0v = p0(&s);
    let mx = s[s.len() - 1]; let mx2 = s[s.len() - 2];
    let lb = s.iter().filter(|&&x| x <= m1).fold(1 as I, |a, &x| lcm(a, x));
    let nm = s.iter().filter(|&&x| x % m1 == 0).count();
    let (mut pg, mut gmax) = (0, 1 as I); for i in 0..s.len() { for j in i + 1..s.len() { let g = gcd(s[i], s[j]); if g > 1 { pg += 1; } gmax = gmax.max(g); } }
    let ri = relations(&s, 3_000_000);
    let ru = resid_u(&s);
    let sum: I = s.iter().sum();
    format!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}/{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}/{}\t{}\t{}\t{}\t{}\t{}\t{}{}\t{}\t{}",
        src, m, s.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","),
        gcdv(&s) == 1 && is_dc(&s) && l1o(&s) && not_sf(&s),
        match ru { Some((r, _, _)) => r.to_string(), None => "na".into() },
        match ru { Some((_, u1, _)) => format!("{:.6}", u1), None => "na".into() },
        match ru { Some((_, _, u2)) => format!("{:.6}", u2), None => "na".into() },
        b.0, b.1,
        match qs { Some((p, q)) => format!("{}/{}", p, q), None => "none".into() },
        match qesc { Some((q, a, sg, k)) => format!("{}:{}:{}:{:?}", q, a, sg, k), None => format!(">{}", qcap) },
        match qx { Some((q, a, sg, k)) => format!("{}:{}:{}:{:?}", q, a, sg, k), None => format!(">{}", qcap) },
        q0v, p0v, mx, mx, mx2, lb, nm, pg, gmax, ri.minsupp, ri.nrel, if ri.capped { "+" } else { "" },
        match ri.index { Some(i) => i.to_string(), None => format!("rank{}", ri.rank) }, sum)
}
const HDR: &str = "src\tm\tv\tclassDC_L1O_nSF\tresidU\tU1\tU2\tML\tqstar\tQesc(q:a:sgn:kind)\tQexact\tq0\tp0\tmaxv\tmax/second\tlcm_le_m1\tn_mult_m1\tpairs_gcd_gt1\tmax_pair_gcd\tminsupp\tnrel\tindex\tsum";

// ---------------- adversarial hunt: maximise qstar / f(v) ----------------
// obj "q0": f = q0 ; obj "p0m": f = p0 * (m+1) / 2 ... selectable below
fn fval(obj: &str, v: &[I]) -> I { let m1 = v.len() as I + 1; match obj { "q0" => q0(v), "p0" => p0(v), "m1" => m1, "2p0" => 2 * p0(v), "3m1" => 3 * m1, "q02m" => q0(v) + 2 * m1, "3q0" => 3 * q0(v), _ => panic!("obj") } }
fn score_h(obj: &str, v: &[I]) -> Option<(I, I)> { if obj == "escq0" { let q0v = q0(v); let c = 3 * q0v; return Some((match cert_m(v, c, 2) { Some((q, _, _, _)) => q, None => c + 1 }, q0v)); } let (_, q) = qstar(v)?; Some((q, fval(obj, v))) }
fn ratio_lt(a: (I, I), b: (I, I)) -> bool { a.0 * b.1 < b.0 * a.1 }
fn hunt_ck(m: usize, h: I, secs: u64, seed: u64, seeds: &str, prefix: &str, obj: &str) {
    let ckp = format!("{}.ck", prefix); let outp = format!("{}.out", prefix);
    let mut rng = Rng(seed * 2654435761 + 4243);
    let (mut evals, mut prev_el, mut restarts) = (0u64, 0u64, 0u64);
    let mut best: Option<((I, I), Vec<I>)> = None;
    if let Ok(s) = std::fs::read_to_string(&ckp) { for l in s.lines() { let p: Vec<&str> = l.split_whitespace().collect();
        match p[0] { "evals" => evals = p[1].parse().unwrap(), "elapsed" => prev_el = p[1].parse().unwrap(), "rng" => rng.0 = p[1].parse().unwrap(),
            "restarts" => restarts = p[1].parse().unwrap(),
            "best" => { best = Some(((p[1].parse().unwrap(), p[2].parse().unwrap()), parse(p[3]))); }, _ => {} } }
        eprintln!("RESUME from {} evals={} elapsed={}", ckp, evals, prev_el); }
    let starts: Vec<Vec<I>> = read_fams(seeds).into_iter().filter(|v| v.len() == m).collect();
    assert!(!starts.is_empty());
    let t0 = std::time::Instant::now(); let el = |t0: &std::time::Instant| prev_el + t0.elapsed().as_secs();
    let mut f = std::fs::OpenOptions::new().create(true).append(true).open(&outp).unwrap();
    let ok = |w: &Vec<I>| -> bool { in_class(w) && !fast(w) && matches!(resid_u(w), Some((true, _, _))) };
    let mut last_ck = 0u64; let mut rejects = 0u64;
    let save = |evals: u64, e: u64, rng: u64, restarts: u64, best: &Option<((I, I), Vec<I>)>| {
        let mut s = format!("evals {}\nelapsed {}\nrng {}\nrestarts {}\n", evals, e, rng, restarts);
        if let Some((r, v)) = best { s += &format!("best {} {} {}\n", r.0, r.1, v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")); }
        let tmp = format!("{}.tmp", ckp); std::fs::write(&tmp, s).unwrap(); std::fs::rename(&tmp, &ckp).unwrap(); };
    while el(&t0) < secs {
        restarts += 1;
        let mut v = if restarts % 3 == 0 && best.is_some() { best.as_ref().unwrap().1.clone() } else { starts[rng.below(starts.len() as u64) as usize].clone() };
        if !ok(&v) { continue; }
        let mut cur = match score_h(obj, &v) { Some(s) => s, None => { writeln!(f, "NOWITNESS {:?}", v).unwrap(); continue; } }; evals += 1;
        let mut stall = 0;
        while stall < 800 && el(&t0) < secs {
            let mut w = v.clone();
            let k = 1 + rng.below(2) as usize;
            for _ in 0..k { let i = rng.below(m as u64) as usize;
                w[i] = match rng.below(5) { 0 => 1 + rng.below(h as u64) as I,
                    1 => { let d = 2 + rng.below(2 * m as u64) as I; (d * (1 + rng.below((h / d) as u64) as I)).max(1) },
                    2 => (w[i] + rng.below(7) as I - 3).max(1).min(h),
                    3 => { let j = rng.below(m as u64) as usize; let c = 2 + rng.below(6) as I; (w[j] * c).min(h) },
                    _ => { let j = rng.below(m as u64) as usize; let l = rng.below(m as u64) as usize; (w[j] + w[l]).min(h) } }; }
            if !ok(&w) { stall += 1; rejects += 1; continue; }
            let sc = match score_h(obj, &w) { Some(s) => s, None => { let mut sv = w.clone(); sv.sort(); writeln!(f, "NOWITNESS {:?}", sv).unwrap(); stall += 1; continue; } };
            evals += 1;
            if !ratio_lt(sc, cur) { if ratio_lt(cur, sc) { stall = 0; } else { stall += 1; } v = w; cur = sc; } else { stall += 1; }
            let better = match &best { None => true, Some((b, _)) => ratio_lt(*b, cur) };
            if better { let mut sv = v.clone(); sv.sort(); best = Some((cur, sv.clone()));
                writeln!(f, "{} | m={} qstar={} f={} ratio={:.4} t={}s", sv.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","), m, cur.0, cur.1, cur.0 as f64 / cur.1 as f64, el(&t0)).unwrap(); }
            let e = el(&t0);
            if e >= last_ck + 30 { last_ck = e; save(evals, e, rng.0, restarts, &best);
                let b = best.as_ref().unwrap();
                eprintln!("[{}s/{}s ETA {}s] m={} obj={} evals={} rejects={} restarts={} rate={:.0}/s best={}/{}={:.4} v={:?}", e, secs, secs.saturating_sub(e), m, obj, evals, rejects, restarts,
                    evals as f64 / (t0.elapsed().as_secs_f64() + 1e-9), b.0 .0, b.0 .1, b.0 .0 as f64 / b.0 .1 as f64, b.1); }
        }
    }
    let e = el(&t0); save(evals, e, rng.0, restarts, &best);
    let b = best.unwrap();
    eprintln!("DONE m={} H={} obj={} secs={} evals={} rejects={} restarts={} best={}/{} v={:?}", m, h, obj, e, evals, rejects, restarts, b.0 .0, b.0 .1, b.1);
    writeln!(f, "# DONE m={} H={} obj={} evals={} restarts={} best={}/{} v={}", m, h, obj, evals, restarts, b.0 .0, b.0 .1, b.1.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")).unwrap();
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args[0].as_str() {
        "fit" => { // fit qcap src1=file1 src2=file2 ...
            let qcap: I = args[1].parse().unwrap(); println!("{}", HDR);
            for a in &args[2..] { let (src, path) = a.split_once('=').unwrap();
                for v in read_fams(path) { println!("{}", fit_line(src, &v, qcap)); let _ = std::io::stdout().flush(); } } }
        "fitv" => { let qcap: I = args[1].parse().unwrap(); println!("{}", HDR); for a in &args[2..] { println!("{}", fit_line("cli", &parse(a), qcap)); } }
        "rel" => for a in &args[1..] { let v = parse(a); let r = relations(&v, 3_000_000); println!("{:?} minsupp={} nrel={} capped={} rank={} index={:?}", v, r.minsupp, r.nrel, r.capped, r.rank, r.index); },
        "hunt" => hunt_ck(args[1].parse().unwrap(), args[2].parse().unwrap(), args[3].parse().unwrap(), args[4].parse().unwrap(), &args[5], &args[6], &args[7]),
        _ => mdr_main(),
    }
}
