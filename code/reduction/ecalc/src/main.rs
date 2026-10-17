// ecalc: exact max-loneliness tools (independent enumeration, m <= 8).
// ML(v) = max_t min_i ||v_i t||, attained at t = a/(v_i+v_j), i <= j (tent-crossing lemma).
// All arithmetic is exact integer: gap(a/s) = min_k min(r_k, s - r_k)/s, r_k = a v_k mod s.
use std::io::Write;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn sums(v: &[u64]) -> Vec<u64> {
    let mut s = Vec::new();
    for i in 0..v.len() {
        for j in i..v.len() {
            s.push(v[i] + v[j]);
        }
    }
    s.sort();
    s.dedup();
    s
}

/// Exact ML: returns (g, s, a) with ML = g/s at t = a/s (first maximiser in (s asc, a asc) order).
pub fn ml(v: &[u64]) -> (u64, u64, u64) {
    let mut best = (0u64, 1u64, 0u64);
    let mut r = vec![0u64; v.len()];
    for s in sums(v) {
        let st: Vec<u64> = v.iter().map(|&x| x % s).collect();
        for x in r.iter_mut() {
            *x = 0;
        }
        for a in 1..=s / 2 {
            let mut g = u64::MAX;
            for k in 0..v.len() {
                let mut y = r[k] + st[k];
                if y >= s {
                    y -= s;
                }
                r[k] = y;
                let d = if y < s - y { y } else { s - y };
                if d < g {
                    g = d;
                }
            }
            if g * best.1 > best.0 * s {
                best = (g, s, a);
            }
        }
    }
    best
}

/// Does ML(v) > p/q ? (early exit)
pub fn ml_exceeds(v: &[u64], p: u64, q: u64) -> bool {
    let mut r = vec![0u64; v.len()];
    for s in sums(v) {
        let st: Vec<u64> = v.iter().map(|&x| x % s).collect();
        for x in r.iter_mut() {
            *x = 0;
        }
        // need g/s > p/q, i.e. g*q > p*s ; g <= s/2
        let need = p * s; // g*q > need
        for a in 1..=s / 2 {
            let mut ok = true;
            for k in 0..v.len() {
                let mut y = r[k] + st[k];
                if y >= s {
                    y -= s;
                }
                r[k] = y;
                if ok {
                    let d = if y < s - y { y } else { s - y };
                    if d * q <= need {
                        ok = false;
                    }
                }
            }
            if ok {
                return true;
            }
        }
    }
    false
}

fn is_dc(v: &[u64]) -> bool {
    let m = v.len() as u64;
    (2..=m + 1).all(|j| v.iter().any(|&x| x % j == 0))
}
fn missing_div(v: &[u64]) -> Option<u64> {
    let m = v.len() as u64;
    (2..=m + 1).find(|&j| !v.iter().any(|&x| x % j == 0))
}
fn is_l1o(v: &[u64]) -> bool {
    (0..v.len()).all(|l| {
        let mut g = 0;
        for (i, &x) in v.iter().enumerate() {
            if i != l {
                g = gcd(g, x);
            }
        }
        g == 1
    })
}
/// StrongFree: no nonzero c in {-1,0,1}^m with c.v = 0  <=> all 2^m subset sums distinct.
fn is_strongfree(v: &[u64]) -> bool {
    let m = v.len();
    let mut s: Vec<u64> = Vec::with_capacity(1 << m);
    s.push(0);
    for &x in v {
        let n = s.len();
        for i in 0..n {
            s.push(s[i] + x);
        }
    }
    s.sort_unstable();
    s.windows(2).all(|w| w[0] != w[1])
}

fn parse(s: &str) -> Vec<u64> {
    let mut v: Vec<u64> = s.split(',').filter(|x| !x.trim().is_empty()).map(|x| x.trim().parse().unwrap()).collect();
    v.sort();
    v
}

fn describe(v: &[u64]) -> String {
    let m = v.len() as u64;
    let (g, s, a) = ml(v);
    let d = gcd(g, s);
    let (gn, gd) = (g / d, s / d);
    let dt = gcd(a, s);
    let div = v.iter().any(|&x| x % (m + 1) == 0);
    format!(
        "v={:?} m={} ML={}/{} (m+1)ML={}/{}={:.6} t={}/{} D(m+1|v)={} DC={} L1O={} SF={} missing={:?}",
        v,
        m,
        gn,
        gd,
        (m + 1) * gn / gcd((m + 1) * gn, gd),
        gd / gcd((m + 1) * gn, gd),
        ((m + 1) * gn) as f64 / gd as f64,
        a / dt,
        s / dt,
        div,
        is_dc(v),
        is_l1o(v),
        is_strongfree(v),
        missing_div(v)
    )
}

// Enumerate all sorted m-subsets of [1,H] with gcd 1, report those with ML <= p/q.
// Jobs: (v0, v1) pairs. Checkpoint: append-only done file with per-job results.
fn enumerate(m: usize, h: u64, p: u64, q: u64, out: &str) {
    let mut jobs = Vec::new();
    for a in 1..=h {
        for b in a + 1..=h {
            if (h - b) as usize >= m - 2 {
                jobs.push((a, b));
            }
        }
    }
    let donefile = format!("{}.done", out);
    let mut done = std::collections::HashSet::new();
    if let Ok(txt) = std::fs::read_to_string(&donefile) {
        for l in txt.lines() {
            if let Some(x) = l.strip_prefix("JOB ") {
                done.insert(x.trim().parse::<usize>().unwrap());
            }
        }
    }
    let jobs = Arc::new(jobs);
    let next = Arc::new(AtomicUsize::new(0));
    let fout = Arc::new(Mutex::new(
        std::fs::OpenOptions::new().create(true).append(true).open(&donefile).unwrap(),
    ));
    let total = jobs.len();
    let fin = Arc::new(AtomicUsize::new(done.len()));
    let counted = Arc::new(AtomicUsize::new(0));
    let done = Arc::new(done);
    let t0 = std::time::Instant::now();
    let mut hs = Vec::new();
    for _ in 0..8 {
        let (jobs, next, fout, fin, done, counted) =
            (jobs.clone(), next.clone(), fout.clone(), fin.clone(), done.clone(), counted.clone());
        hs.push(std::thread::spawn(move || loop {
            let j = next.fetch_add(1, Ordering::SeqCst);
            if j >= jobs.len() {
                break;
            }
            if done.contains(&j) {
                continue;
            }
            let (a, b) = jobs[j];
            let mut hits: Vec<Vec<u64>> = Vec::new();
            let mut cnt = 0usize;
            let mut v = vec![a, b];
            fn rec(
                v: &mut Vec<u64>, m: usize, h: u64, g: u64, p: u64, q: u64,
                hits: &mut Vec<Vec<u64>>, cnt: &mut usize,
            ) {
                if v.len() == m {
                    if g != 1 {
                        return;
                    }
                    *cnt += 1;
                    if !ml_exceeds(v, p, q) {
                        hits.push(v.clone());
                    }
                    return;
                }
                let last = *v.last().unwrap();
                let rem = (m - v.len()) as u64;
                for x in last + 1..=h - rem + 1 {
                    v.push(x);
                    rec(v, m, h, gcd(g, x), p, q, hits, cnt);
                    v.pop();
                }
            }
            rec(&mut v, m, h, gcd(a, b), p, q, &mut hits, &mut cnt);
            counted.fetch_add(cnt, Ordering::SeqCst);
            let mut s = String::new();
            for v in &hits {
                s.push_str(&format!("HIT {:?}\n", v));
            }
            s.push_str(&format!("CNT {} {}\nJOB {}\n", j, cnt, j));
            {
                let mut f = fout.lock().unwrap();
                f.write_all(s.as_bytes()).unwrap();
                f.flush().unwrap();
            }
            let f = fin.fetch_add(1, Ordering::SeqCst) + 1;
            if f % 200 == 0 {
                let el = t0.elapsed().as_secs_f64();
                eprintln!("progress {}/{} elapsed {:.0}s", f, total, el);
            }
        }));
    }
    for h in hs {
        h.join().unwrap();
    }
    eprintln!("finished {} jobs in {:.1}s", total, t0.elapsed().as_secs_f64());
}


fn rng(state: &mut u64) -> u64 { *state ^= *state << 13; *state ^= *state >> 7; *state ^= *state << 17; *state }
fn ml_frac(v: &[u64]) -> (u64,u64) { let (g,s,_) = ml(v); (g,s) }
fn less(a:(u64,u64), b:(u64,u64)) -> bool { a.0*b.1 < b.0*a.1 }
// simulated annealing on D-families (m+1 | some speed), gcd 1, restricted to C' if cls
fn anneal(m: usize, hmax: u64, secs: f64, seed: u64, cls: bool) -> (Vec<u64>,(u64,u64)) {
    let mm = m as u64; let mut st = seed.wrapping_mul(0x9E3779B97F4A7C15) | 1;
    let ok = |v: &[u64]| -> bool {
        let g = v.iter().fold(0, |a,&x| gcd(a,x)); if g != 1 { return false; }
        if !v.iter().any(|&x| x % (mm+1) == 0) { return false; }
        if cls && !(is_dc(v) && is_l1o(v) && !is_strongfree(v)) { return false; }
        let mut w = v.to_vec(); w.dedup(); w.len() == v.len()
    };
    // random start (no E_m bias): random m-subset of [1, 3m] plus random multiple of m+1, until ok
    let mut v: Vec<u64>;
    loop {
        let mut w: Vec<u64> = Vec::new();
        while w.len() < m - 1 { let x = 1 + rng(&mut st) % (3*mm); if !w.contains(&x) { w.push(x); } }
        let z = (mm+1) * (1 + rng(&mut st) % (hmax/(mm+1)));
        if w.contains(&z) { continue; }
        w.push(z); w.sort();
        if ok(&w) { v = w; break; }
    }
    let mut cur = ml_frac(&v); let mut best = (v.clone(), cur);
    let t0 = std::time::Instant::now(); let mut it = 0u64;
    while t0.elapsed().as_secs_f64() < secs {
        it += 1;
        let temp = 0.02 * (1.0 - t0.elapsed().as_secs_f64()/secs) + 1e-4;
        let mut w = v.clone();
        let i = (rng(&mut st) % mm) as usize;
        let r = rng(&mut st) % 4;
        w[i] = if r == 0 { 1 + rng(&mut st) % hmax } else if r == 1 { (mm+1) * (1 + rng(&mut st) % (hmax/(mm+1))) }
               else { let d = (rng(&mut st) % 7) as i64 - 3; ((w[i] as i64 + d).max(1) as u64).min(hmax) };
        w.sort();
        if !ok(&w) { continue; }
        let c = ml_frac(&w);
        let delta = (c.0 as f64/c.1 as f64 - cur.0 as f64/cur.1 as f64) * (mm+1) as f64;
        let u = (rng(&mut st) % 1_000_000) as f64 / 1e6;
        if delta <= 0.0 || u < (-delta/temp).exp() { v = w; cur = c; if less(cur, best.1) { best = (v.clone(), cur); } }
    }
    eprintln!("seed {} iters {} best {:?} {}/{}", seed, it, best.0, best.1.0, best.1.1);
    best
}


/// Perturbation certificate at a/q + eps, q = m+1 (Lemma P). Returns Some((a, sigma)) if found.
/// Conditions (all exact): no speed with centred residue e_i = -sigma (hurt at first order);
/// L = min over non-Z speeds of 1/(q v_i) (|e_i|>=2) or (q-2)/(q v_i) (e_i = sigma), q>=4;
/// exists eps in (0, L) with ||z eps|| > 1/q for all z in Z (checked at midpoints of breakpoints).
fn pcert(v: &[u64]) -> Option<(u64, i64)> {
    let q = v.len() as u64 + 1; if q < 4 { return None; }
    let z: Vec<u64> = v.iter().cloned().filter(|&x| x % q == 0).collect();
    for a in 1..q { if gcd(a, q) != 1 { continue; }
      for &sg in &[1i64, -1i64] {
        let mut bad = false; // L as fraction ln/ld (minimise)
        let (mut ln, mut ld) = (1u128, 0u128); // +inf
        for &x in v { if x % q == 0 { continue; }
            let r = (a * x % q) as i64; let e = if 2*r > q as i64 { r - q as i64 } else { r };
            if e == -sg { bad = true; break; }
            let (n, d) = if e == sg { ((q - 2) as u128, (q * x) as u128) } else { (1u128, (q * x) as u128) };
            if ld == 0 || n * ld < ln * d { ln = n; ld = d; }
        }
        if bad { continue; }
        if z.is_empty() { return Some((a, sg)); }
        if ld == 0 { return Some((a, sg)); }
        // breakpoints of ||z eps|| = 1/q in (0, L): eps = (k q +- 1)/(q z). Collect as fractions, sort, test midpoints.
        let mut pts: Vec<(u128,u128)> = vec![(0,1), (ln, ld)];
        for &w in &z { let mut k = 0u128; loop {
            let mut any = false;
            for &c in &[k*(q as u128)+1, (k+1)*(q as u128)-1] { let (n,d) = (c, (q*w) as u128);
                if n * ld < ln * d { pts.push((n,d)); any = true; } }
            if !any { break; } k += 1; if k > 100000 { break; } } }
        pts.sort_by(|x, y| (x.0 * y.1).cmp(&(y.0 * x.1)));
        for win in pts.windows(2) { let (n1,d1) = win[0]; let (n2,d2) = win[1];
            if n1 * d2 >= n2 * d1 { continue; }
            let (mn, md) = (n1*d2 + n2*d1, 2*d1*d2); // midpoint
            // check ||w * mn/md|| > 1/q  <=> q*min(r, md-r) > md, r = w*mn mod md
            if z.iter().all(|&w| { let r = (w as u128 * mn) % md; let dd = if r < md - r { r } else { md - r }; (q as u128) * dd > md }) {
                return Some((a, sg)); }
        }
      } }
    None
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args[1].as_str() {
        "eval" => println!("{}", describe(&parse(&args[2]))),
        "enum" => {
            let m: usize = args[2].parse().unwrap();
            let h: u64 = args[3].parse().unwrap();
            // threshold p/q default: E_m value (m+1)/(m^2+m+1)
            let mm = m as u64;
            let (p, q) = if args.len() > 5 {
                (args[5].parse().unwrap(), args[6].parse().unwrap())
            } else {
                (mm + 1, mm * mm + mm + 1)
            };
            enumerate(m, h, p, q, &args[4]);
        }
        "summ" => {
            // read done file, print described hits and total count
            let txt = std::fs::read_to_string(&args[2]).unwrap();
            let mut tot = 0usize;
            let mut jobs = 0usize;
            for l in txt.lines() {
                if let Some(x) = l.strip_prefix("HIT ") {
                    let v = parse(x.trim_matches(|c| c == '[' || c == ']'));
                    println!("{}", describe(&v));
                } else if let Some(x) = l.strip_prefix("CNT ") {
                    tot += x.split_whitespace().nth(1).unwrap().parse::<usize>().unwrap();
                    jobs += 1;
                }
            }
            println!("TOTAL gcd-1 families scanned: {} in {} jobs", tot, jobs);
        }
        "batch" => {
            // one family per line on stdin
            let stdin = std::io::stdin();
            let mut s = String::new();
            while stdin.read_line(&mut s).unwrap() > 0 {
                let t = s.trim().trim_matches(|c| c == '[' || c == ']').to_string();
                if !t.is_empty() {
                    println!("{}", describe(&parse(&t)));
                }
                s.clear();
            }
        }
        "anneal" => {
            let m: usize = args[2].parse().unwrap(); let h: u64 = args[3].parse().unwrap();
            let secs: f64 = args[4].parse().unwrap(); let seeds: u64 = args[5].parse().unwrap();
            let cls = args.get(6).map_or(false, |x| x == "cls");
            let hs: Vec<_> = (0..seeds).map(|sd| std::thread::spawn(move || anneal(m, h, secs, sd+1, cls))).collect();
            for hnd in hs { let (v, _) = hnd.join().unwrap(); println!("{}", describe(&v)); }
        }
        "pcert" => {
            let stdin = std::io::stdin(); let mut line = String::new();
            let (mut n, mut ok, mut single, mut singlemax) = (0, 0, 0, 0);
            while stdin.read_line(&mut line).unwrap() > 0 {
                let t = line.trim().trim_matches(|c| c == '[' || c == ']').to_string(); line.clear();
                if t.is_empty() || t.starts_with('#') { continue; }
                let v = parse(&t); let q = v.len() as u64 + 1; n += 1;
                let zc = v.iter().filter(|&&x| x % q == 0).count();
                if zc == 1 { single += 1; if v.last().unwrap() % q == 0 { singlemax += 1; } }
                let c = pcert(&v); if c.is_some() { ok += 1; }
                if args.len() > 2 { println!("{:?} |Z|={} cert={:?}", v, zc, c); }
            }
            println!("families {} certified {} single-multiple {} single-multiple-is-max {}", n, ok, single, singlemax);
        }
        _ => panic!("usage"),
    }
}
