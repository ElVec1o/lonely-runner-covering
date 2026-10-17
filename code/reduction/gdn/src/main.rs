// gdn: exhaustive tight-family enumeration. Exact integer arithmetic only.
// Conventions: v = m positive integer speeds, target 1/(m+1). gap(t) = min_i ||v_i t||.
// ML is attained at some t = a/(v_i+v_j), i <= j (local maxima of a piecewise-linear
// function with nonzero slopes; i = j covers the distance-1/2 peaks).
use std::io::{BufRead, Write};
use std::time::Instant;

fn gcd(a: i64, b: i64) -> i64 { let (mut x, mut y) = (a.abs(), b.abs()); while y != 0 { let t = x % y; x = y; y = t; } x }
fn gcd_all(v: &[i64]) -> i64 { v.iter().fold(0, |a, &b| gcd(a, b)) }

fn cand_dens(v: &[i64]) -> Vec<i64> {
    let mut ds = Vec::new();
    for i in 0..v.len() { for j in i..v.len() { ds.push(v[i] + v[j]); } }
    ds.sort(); ds.dedup(); ds
}

/// numerator g of gap(a/d) = g/d
#[inline]
fn gapnum(v: &[i64], a: i64, d: i64) -> i64 {
    let mut g = d;
    for &x in v { let r = ((x % d) * a) % d; let t = r.min(d - r); if t < g { g = t; } }
    g
}

/// exact ML = bn/bd and ALL maximisers t in [0,1/2] (reduced)
fn ml_all(v: &[i64]) -> (i64, i64, Vec<(i64, i64)>) {
    let (mut bn, mut bd) = (0i64, 1i64);
    let mut ts: Vec<(i64, i64)> = Vec::new();
    for d in cand_dens(v) {
        for a in 0..=d / 2 {
            let mut g = d;
            for &x in v {
                let r = ((x % d) * a) % d; let t = r.min(d - r); if t < g { g = t; }
                if (g as i128) * (bd as i128) < (bn as i128) * (d as i128) { break; }
            }
            let lhs = (g as i128) * (bd as i128); let rhs = (bn as i128) * (d as i128);
            if lhs > rhs { bn = g; bd = d; ts.clear(); let h = gcd(a, d); ts.push((a / h, d / h)); }
            else if lhs == rhs && g > 0 { let h = gcd(a, d); ts.push((a / h, d / h)); }
        }
    }
    let h = gcd(bn, bd); ts.sort(); ts.dedup();
    (bn / h, bd / h, ts)
}

/// does some t have gap(t) > num/den (strict=true) or >= num/den (strict=false)?
fn exists_gap(v: &[i64], num: i64, den: i64, strict: bool) -> bool {
    for d in cand_dens(v) {
        for a in 1..=d / 2 {
            let mut ok = true;
            for &x in v {
                let r = ((x % d) * a) % d; let t = r.min(d - r);
                let l = (t as i128) * (den as i128); let rr = (num as i128) * (d as i128);
                if (strict && l <= rr) || (!strict && l < rr) { ok = false; break; }
            }
            if ok { return true; }
        }
    }
    false
}

fn dc(v: &[i64], jmax: i64) -> bool { (2..=jmax).all(|j| v.iter().any(|&x| x % j == 0)) }
fn l1o_prim(v: &[i64]) -> bool {
    (0..v.len()).all(|l| { let mut g = 0; for (i, &x) in v.iter().enumerate() { if i != l { g = gcd(g, x); } } g == 1 })
}
/// true iff some nonzero c in {-1,0,1}^m has c.v = 0, i.e. two distinct subsets share a sum
fn not_strong_free(v: &[i64]) -> bool {
    let s: i64 = v.iter().sum();
    let mut cnt = vec![0u8; (s + 1) as usize]; cnt[0] = 1;
    for &x in v {
        for t in (x..=s).rev() {
            let c = cnt[t as usize] as u16 + cnt[(t - x) as usize] as u16;
            cnt[t as usize] = c.min(2) as u8;
        }
    }
    cnt.iter().any(|&c| c >= 2)
}

fn spec_label(m: i64, n: i64, d: i64) -> String {
    // ML = n/d; Kravitz spectrum: ML = s/(m s + 1) or ML >= 1/m
    if n * m >= d { return "GE1/m".into(); }
    if n * (m + 1) < d { return "LRC-FAIL".into(); }
    if d == m * n + 1 { return format!("SPEC s={}", n); }
    "NONSPEC".into()
}

fn describe(v: &[i64]) {
    let m = v.len() as i64;
    let (n, d, ts) = ml_all(v);
    let tstr: Vec<String> = ts.iter().take(12).map(|(a, b)| format!("{}/{}", a, b)).collect();
    let alln1 = ts.iter().all(|&(_, b)| (m + 1) % b == 0);
    println!("{:?} | m={} gcd={} | ML={}/{} (m+1)ML={}/{} | {} | #max={} all_den|m+1={} | t={} | DC={} L1O={} notSF={} m+1|some={}",
        v, m, gcd_all(v), n, d, n * (m + 1) / gcd(n * (m + 1), d), d / gcd(n * (m + 1), d), spec_label(m, n, d),
        ts.len(), alln1, tstr.join(","), dc(v, m + 1), l1o_prim(v), not_strong_free(v), v.iter().any(|&x| x % (m + 1) == 0));
}

fn parse(s: &str) -> Vec<i64> {
    s.split(|c: char| c == ',' || c.is_whitespace() || c == '[' || c == ']').filter(|x| !x.is_empty()).map(|x| x.parse().unwrap()).collect()
}

// ---------- tight search ----------
// all gcd-1 v1<..<vm<=H with DC(j<=m) [necessary for tightness], optional (m+1)|some v_i,
// and ML <= 1/(m+1). Prints every hit with maximisers.
fn tight(m: usize, h: i64, req: bool) {
    let t0 = Instant::now(); let mut leaves: u64 = 0; let mut dcpass: u64 = 0; let mut hits: u64 = 0;
    let mut cur: Vec<i64> = Vec::with_capacity(m);
    fn rec(cur: &mut Vec<i64>, m: usize, h: i64, req: bool, leaves: &mut u64, dcpass: &mut u64, hits: &mut u64) {
        if cur.len() == m {
            *leaves += 1;
            let mm = m as i64;
            if req && !cur.iter().any(|&x| x % (mm + 1) == 0) { return; }
            if !dc(cur, mm) { return; }
            if gcd_all(cur) != 1 { return; }
            *dcpass += 1;
            if exists_gap(cur, 1, mm + 1, true) { return; }
            *hits += 1; describe(cur); std::io::stdout().flush().ok();
            return;
        }
        let start = if cur.is_empty() { 1 } else { cur[cur.len() - 1] + 1 };
        let rem = (m - cur.len()) as i64;
        for x in start..=(h - rem + 1) { cur.push(x); rec(cur, m, h, req, leaves, dcpass, hits); cur.pop(); }
    }
    // top level: iterate v1 for progress
    let rem = m as i64;
    for x in 1..=(h - rem + 1) {
        cur.push(x); rec(&mut cur, m, h, req, &mut leaves, &mut dcpass, &mut hits); cur.pop();
        eprintln!("[tight m={} H={} req={}] v1={} done, leaves={} dc_gcd_pass={} hits={} elapsed={:.1}s", m, h, req, x, leaves, dcpass, hits, t0.elapsed().as_secs_f64());
        if x == 1 && m >= 2 { /* v1=1 branch is the largest */ }
    }
    println!("# DONE tight m={} H={} req={} leaves={} dc_gcd_pass={} hits={} secs={:.1}", m, h, req, leaves, dcpass, hits, t0.elapsed().as_secs_f64());
}

// ---------- class census ----------
fn class(m: usize, h: i64, hmin: i64) {
    let t0 = Instant::now();
    let mut st = [0u64; 6]; // leaves, members, GE1/m, SPEC, NONSPEC, LRCFAIL
    let mut cur: Vec<i64> = Vec::with_capacity(m);
    fn rec(cur: &mut Vec<i64>, m: usize, h: i64, hmin: i64, st: &mut [u64; 6]) {
        if cur.len() == m {
            st[0] += 1; let mm = m as i64;
            if cur[m - 1] <= hmin { return; }
            if !dc(cur, mm + 1) || gcd_all(cur) != 1 || !l1o_prim(cur) || !not_strong_free(cur) { return; }
            st[1] += 1;
            if exists_gap(cur, 1, mm, false) { st[2] += 1; return; }
            let (n, d, _) = ml_all(cur);
            let lab = spec_label(mm, n, d);
            if lab.starts_with("SPEC") { st[3] += 1; } else if lab == "NONSPEC" { st[4] += 1; } else if lab == "LRC-FAIL" { st[5] += 1; } else { st[2] += 1; }
            describe(cur); std::io::stdout().flush().ok();
            return;
        }
        let start = if cur.is_empty() { 1 } else { cur[cur.len() - 1] + 1 };
        let rem = (m - cur.len()) as i64;
        for x in start..=(h - rem + 1) { cur.push(x); rec(cur, m, h, hmin, st); cur.pop(); }
    }
    for x in 1..=(h - m as i64 + 1) {
        cur.push(x); rec(&mut cur, m, h, hmin, &mut st); cur.pop();
        eprintln!("[class m={} H={} hmin={}] v1={} done st={:?} elapsed={:.1}s", m, h, hmin, x, st, t0.elapsed().as_secs_f64());
    }
    println!("# DONE class m={} H={} hmin={} leaves={} members={} GE1/m={} SPEC={} NONSPEC={} LRCFAIL={} secs={:.1}", m, h, hmin, st[0], st[1], st[2], st[3], st[4], st[5], t0.elapsed().as_secs_f64());
}

// ---------- Goddyn-Wong families ----------
fn gw_cond(r: i64, m: i64, s: i64) -> bool { (s..=(m * s - 1)).all(|b| gcd(r, b) > 1) }
fn check_family(tag: &str, v: &[i64], n: i64) {
    let (a, b, ts) = ml_all(v);
    let tight = a * n == b;
    let alln = ts.iter().all(|&(_, d)| n % d == 0);
    let ndiv = v.iter().any(|&x| x % n == 0);
    println!("{} n={} m={} max={} ML={}/{} tight={} #max={} all_den|n={} n|some={}{}", tag, n, v.len(), v.iter().max().unwrap(), a, b, tight, ts.len(), alln, ndiv,
        if !alln { format!(" maximisers={:?}", ts) } else { String::new() });
}
fn gw(nmax: i64) {
    let t0 = Instant::now();
    for n in 3..=nmax {
        let mut mult = vec![1i64; n as usize];
        for r in 1..n {
            let s = n - r; let mut m = 2; let mut best = 1;
            while gw_cond(r, m, s) { best = m; m += 1; if m > 64 { break; } }
            if best >= 2 {
                mult[r as usize] = best;
                for mm in 2..=best {
                    let mut v: Vec<i64> = (1..n).map(|x| if x == r { mm * r } else { x }).collect(); v.sort();
                    check_family(&format!("GW1 r={} m={}", r, mm), &v, n);
                }
            }
        }
        let acc: Vec<i64> = (1..n).filter(|&r| mult[r as usize] >= 2).collect();
        if acc.len() >= 2 {
            let mut v: Vec<i64> = (1..n).map(|x| mult[x as usize] * x).collect(); v.sort();
            check_family(&format!("GWmulti acc={:?}", acc), &v, n);
        }
        std::io::stdout().flush().ok();
        if n % 25 == 0 { eprintln!("[gw] n={} elapsed={:.1}s", n, t0.elapsed().as_secs_f64()); }
    }
    println!("# DONE gw nmax={} secs={:.1}", nmax, t0.elapsed().as_secs_f64());
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() { eprintln!("usage: gdn ml <v>... | file <path> | tight m H req01 | class m H hmin"); return; }
    match args[0].as_str() {
        "ml" => for a in &args[1..] { describe(&parse(a)); },
        "file" => { let f = std::fs::File::open(&args[1]).unwrap();
            for line in std::io::BufReader::new(f).lines() { let l = line.unwrap(); if l.starts_with('#') || l.trim().is_empty() { continue; } describe(&parse(&l)); } }
        "tight" => tight(args[1].parse().unwrap(), args[2].parse().unwrap(), args[3] == "1"),
        "gw" => gw(args[1].parse().unwrap()),
        "class" => class(args[1].parse().unwrap(), args[2].parse().unwrap(), args[3].parse().unwrap()),
        _ => eprintln!("unknown mode"),
    }
}
