// T2 hunt: simulated annealing minimising (2m+1)*ML(v) over v with gcd 1, some (m+1)|v_i, max v <= H.
// Exact ML: max over t = c/(v_i+v_j) of min_i ||v_i t|| (integer arithmetic). Early exit against a cap.
// Usage: t2hunt run m H secs threads seed outprefix     (resumes from outprefix.ckpt if present)
//        t2hunt ml v1,v2,...                           (exact ML, full enumeration, no pruning)
use std::collections::BTreeSet;
use std::sync::{Arc, Mutex};
use std::time::Instant;

fn gcd(mut a: u64, mut b: u64) -> u64 { while b != 0 { let t = a % b; a = b; b = t; } a }
fn gcdv(v: &[u64]) -> u64 { v.iter().fold(0, |g, &x| gcd(g, x)) }

#[inline] fn gap(v: &[u64], c: u64, s: u64, stop_num: u64, stop_den: u64) -> u64 {
    // min_i dist(v_i c mod s); stops early (returns value <= stop) once min*stop_den <= stop_num*s
    let mut g = u64::MAX;
    for &x in v { let r = (x % s) * c % s; let d = r.min(s - r); if d < g { g = d; if (g as u128) * (stop_den as u128) <= (stop_num as u128) * (s as u128) { return g; } } }
    g
}

// returns Some((g,s)) = exact ML (reduced) if ML < cap (float, on the scale ML), else None
fn ml_capped(v: &[u64], cap: f64, qsmall: u64) -> Option<(u64, u64)> {
    let (mut bg, mut bs) = (0u64, 1u64);
    let check = |g: u64, s: u64| (g as f64) >= cap * (s as f64) * (1.0 - 1e-12);
    for q in 2..=qsmall { for c in 1..=q / 2 { if gcd(c, q) != 1 { continue; }
        let g = gap(v, c, q, bg, bs); if (g as u128) * (bs as u128) > (bg as u128) * (q as u128) { bg = g; bs = q; if check(g, q) { return None; } } } }
    let mut sums = BTreeSet::new();
    for i in 0..v.len() { for j in i..v.len() { sums.insert(v[i] + v[j]); } }
    for &s in &sums { for c in 1..=s / 2 {
        let g = gap(v, c, s, bg, bs);
        if (g as u128) * (bs as u128) > (bg as u128) * (s as u128) { bg = g; bs = s; if check(g, s) { return None; } } } }
    let d = gcd(bg, bs); Some((bg / d, bs / d))
}

// unpruned exact ML, separate code path (all c in 0..s, i<=j), for re-verification
fn ml_full(v: &[u64]) -> (u64, u64) {
    let (mut bg, mut bs) = (0u64, 1u64);
    for i in 0..v.len() { for j in i..v.len() { let s = v[i] + v[j];
        for c in 0..s { let mut g = u64::MAX; for &x in v { let r = (x * c) % s; g = g.min(r.min(s - r)); }
            if (g as u128) * (bs as u128) > (bg as u128) * (s as u128) { bg = g; bs = s; } } } }
    let d = gcd(bg, bs); (bg / d, bs / d)
}

struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn below(&mut self, n: u64) -> u64 { self.next() % n } fn f(&mut self) -> f64 { (self.next() >> 11) as f64 / (1u64 << 53) as f64 } }

fn valid(v: &[u64], m: usize, h: u64) -> bool {
    let mut s = v.to_vec(); s.sort(); s.dedup();
    s.len() == m && s[0] >= 1 && s[m - 1] <= h && gcdv(&s) == 1 && s.iter().any(|&x| x % (m as u64 + 1) == 0)
}

fn seed(m: usize, h: u64, r: &mut Rng, kind: u64) -> Vec<u64> {
    let m1 = m as u64 + 1; let mu = m as u64;
    loop {
        let mut v: Vec<u64> = match kind % 5 {
            0 => { let mut v: Vec<u64> = (1..mu).collect(); v.push(mu * m1); v } // E_m
            1 => { let j = 1 + r.below(mu); let mut v: Vec<u64> = (1..=mu).filter(|&x| x != j).collect(); v.push(j * m1); v } // F(m,j)
            2 => { let mut v: Vec<u64> = (1..=mu).collect(); let k = r.below(mu) as usize; v[k] = m1; // 1..m modified
                   for _ in 0..r.below(4) { let k = r.below(mu) as usize; v[k] = 1 + r.below((3 * mu).min(h)); } v }
            3 => { let mut v = vec![m1 * (1 + r.below((h / m1).max(1)))]; while v.len() < m { v.push(1 + r.below((3 * mu).min(h))); } v } // dense core + multiple
            _ => { let mut v = vec![m1 * (1 + r.below((h / m1).max(1)))]; while v.len() < m { v.push(1 + r.below(h)); } v } // random
        };
        v.retain(|&x| x >= 1 && x <= h); v.sort(); v.dedup();
        while v.len() < m { let x = 1 + r.below(h); if !v.contains(&x) { v.push(x); } }
        v.sort();
        if valid(&v, m, h) { return v; }
        if kind % 5 < 2 { // deterministic seed invalid at this h; fall to random
            return seed(m, h, r, 4); }
    }
}

fn mutate(v: &[u64], m: usize, h: u64, r: &mut Rng) -> Vec<u64> {
    let m1 = m as u64 + 1;
    loop {
        let mut w = v.to_vec();
        let nm = 1 + (r.below(4) == 0) as usize;
        for _ in 0..nm {
            let k = r.below(m as u64) as usize;
            w[k] = match r.below(6) {
                0 => 1 + r.below(h),
                1 | 2 => { let d = 1 + r.below(6); if r.below(2) == 0 { w[k] + d } else { w[k].saturating_sub(d) } }
                3 => 1 + r.below((3 * m as u64).min(h)),
                4 => m1 * (1 + r.below((h / m1).max(1))),
                _ => { let a = w[r.below(m as u64) as usize]; a * (2 + r.below(8)) }
            };
        }
        w.sort();
        if valid(&w, m, h) { return w; }
    }
}

struct Shared { evals: u64, best: f64, bestml: (u64, u64), bestv: Vec<u64>, eq: BTreeSet<Vec<u64>>, viol: Vec<(Vec<u64>, (u64, u64))>, cur: Vec<Vec<u64>>, restarts: u64 }

fn fmt(v: &[u64]) -> String { v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",") }
fn parsev(s: &str) -> Vec<u64> { s.trim().trim_matches(|c| c == '[' || c == ']').split(|c| c == ',' || c == ' ').filter(|x| !x.is_empty()).map(|x| x.parse().unwrap()).collect() }

fn write_ckpt(path: &str, sh: &Shared, elapsed: f64) {
    let mut s = format!("elapsed {}\nevals {}\nrestarts {}\nbest {} {} {}\n", elapsed, sh.evals, sh.restarts, sh.bestml.0, sh.bestml.1, fmt(&sh.bestv));
    for c in &sh.cur { s += &format!("cur {}\n", fmt(c)); }
    for e in &sh.eq { s += &format!("eq {}\n", fmt(e)); }
    for (v, (g, q)) in &sh.viol { s += &format!("viol {} {} {}\n", g, q, fmt(v)); }
    let tmp = format!("{}.tmp", path); std::fs::write(&tmp, s).unwrap(); std::fs::rename(&tmp, path).unwrap();
}

fn run(m: usize, h: u64, secs: f64, threads: usize, seed0: u64, out: &str) {
    let ck = format!("{}.ckpt", out); let logp = format!("{}.log", out);
    let two = (2 * m + 1) as f64;
    let mut sh = Shared { evals: 0, best: f64::MAX, bestml: (0, 1), bestv: vec![], eq: BTreeSet::new(), viol: vec![], cur: vec![vec![]; threads], restarts: 0 };
    let mut done0 = 0.0;
    if let Ok(txt) = std::fs::read_to_string(&ck) {
        let mut ci = 0;
        for l in txt.lines() { let p: Vec<&str> = l.splitn(2, ' ').collect(); if p.len() < 2 { continue; }
            match p[0] { "elapsed" => done0 = p[1].parse().unwrap(), "evals" => sh.evals = p[1].parse().unwrap(), "restarts" => sh.restarts = p[1].parse().unwrap(),
                "best" => { let q: Vec<&str> = p[1].split(' ').collect(); if q.len() == 3 { sh.bestml = (q[0].parse().unwrap(), q[1].parse().unwrap()); sh.bestv = parsev(q[2]); sh.best = two * sh.bestml.0 as f64 / sh.bestml.1 as f64; } }
                "cur" => { if ci < threads { sh.cur[ci] = parsev(p[1]); ci += 1; } }
                "eq" => { sh.eq.insert(parsev(p[1])); }
                "viol" => { let q: Vec<&str> = p[1].split(' ').collect(); sh.viol.push((parsev(q[2]), (q[0].parse().unwrap(), q[1].parse().unwrap()))); }
                _ => {} } }
        eprintln!("resumed from {} at {:.0}s", ck, done0);
    }
    if done0 >= secs { eprintln!("already complete"); return; }
    let sh = Arc::new(Mutex::new(sh));
    let start = Instant::now();
    let qsmall = 4 * m as u64 + 4;
    let mut hs = vec![];
    for t in 0..threads {
        let sh = sh.clone(); let logp = logp.clone(); let ck = ck.clone();
        hs.push(std::thread::spawn(move || {
            let mut r = Rng(seed0.wrapping_mul(0x9E3779B97F4A7C15) ^ (t as u64 + 1) * 0x2545F4914F6CDD1D ^ (done0 as u64) << 20);
            for _ in 0..10 { r.next(); }
            let mut kind = t as u64;
            let start_cur = sh.lock().unwrap().cur[t].clone();
            let mut cur = if valid(&start_cur, m, h) { start_cur } else { seed(m, h, &mut r, kind) };
            let mut curml = ml_capped(&cur, 1.0, qsmall).unwrap();
            let mut curs = two * curml.0 as f64 / curml.1 as f64;
            let mut lastck = Instant::now(); let mut local_evals = 0u64; let mut stall = 0u64;
            let mut temp = 0.02;
            loop {
                let el = done0 + start.elapsed().as_secs_f64();
                if el >= secs { break; }
                let w = mutate(&cur, m, h, &mut r);
                let u = r.f().max(1e-300);
                let thr = curs - temp * u.ln(); // accept iff new score < thr
                let res = ml_capped(&w, thr / two, qsmall);
                local_evals += 1;
                if let Some(mlw) = res {
                    let sw = two * mlw.0 as f64 / mlw.1 as f64;
                    if sw < curs - 1e-12 { stall = 0; } else { stall += 1; }
                    cur = w; curml = mlw; curs = sw;
                    let exact_le1 = (2 * m as u64 + 1) * curml.0 <= curml.1; // exact: (2m+1) g <= s
                    if exact_le1 || curs < sh.lock().unwrap().best {
                        let mut g = sh.lock().unwrap();
                        if curs < g.best { g.best = curs; g.bestml = curml; g.bestv = cur.clone(); }
                        if (2 * m as u64 + 1) * curml.0 == curml.1 && g.eq.len() < 2000 { g.eq.insert(cur.clone()); }
                        if (2 * m as u64 + 1) * curml.0 < curml.1 && g.viol.len() < 200 { g.viol.push((cur.clone(), curml)); }
                    }
                } else { stall += 1; }
                temp = 0.002 + 0.03 * (1.0 - ((stall as f64) / 3000.0).min(1.0));
                if stall > 6000 { kind += threads as u64; cur = seed(m, h, &mut r, kind); curml = ml_capped(&cur, 1.0, qsmall).unwrap(); curs = two * curml.0 as f64 / curml.1 as f64; stall = 0; sh.lock().unwrap().restarts += 1; }
                if lastck.elapsed().as_secs_f64() >= 60.0 || (t == 0 && local_evals % 256 == 0 && lastck.elapsed().as_secs_f64() >= 60.0) {
                    let mut g = sh.lock().unwrap(); g.evals += local_evals; local_evals = 0; g.cur[t] = cur.clone();
                    if t == 0 {
                        let el = done0 + start.elapsed().as_secs_f64();
                        write_ckpt(&ck, &g, el);
                        let line = format!("[{:.0}s/{:.0}s ETA {:.0}s] m={} H={} evals={} rate={:.0}/s restarts={} best (2m+1)ML={:.6} ML={}/{} eq={} viol={} v=[{}]\n",
                            el, secs, secs - el, m, h, g.evals, g.evals as f64 / el.max(1.0), g.restarts, g.best, g.bestml.0, g.bestml.1, g.eq.len(), g.viol.len(), fmt(&g.bestv));
                        use std::io::Write; let mut f = std::fs::OpenOptions::new().create(true).append(true).open(&logp).unwrap(); f.write_all(line.as_bytes()).unwrap();
                    }
                    lastck = Instant::now();
                }
            }
            let mut g = sh.lock().unwrap(); g.evals += local_evals; g.cur[t] = cur;
            let _ = ck;
        }));
    }
    for hnd in hs { hnd.join().unwrap(); }
    let g = sh.lock().unwrap();
    write_ckpt(&ck, &g, secs);
    let line = format!("DONE m={} H={} evals={} restarts={} best (2m+1)ML={:.6} ML={}/{} eq={} viol={} v=[{}]\n", m, h, g.evals, g.restarts, g.best, g.bestml.0, g.bestml.1, g.eq.len(), g.viol.len(), fmt(&g.bestv));
    use std::io::Write; let mut f = std::fs::OpenOptions::new().create(true).append(true).open(&logp).unwrap(); f.write_all(line.as_bytes()).unwrap();
}

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    match a[0].as_str() {
        "ml" => for s in &a[1..] { let v = parsev(s); let f = ml_full(&v); let c = ml_capped(&v, 1.0, 4 * v.len() as u64 + 4).unwrap();
            println!("v=[{}] m={} gcd={} full={}/{} capped={}/{} (2m+1)ML={}/{}", fmt(&v), v.len(), gcdv(&v), f.0, f.1, c.0, c.1, (2 * v.len() as u64 + 1) * f.0, f.1); },
        "run" => run(a[1].parse().unwrap(), a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), a[5].parse().unwrap(), &a[6]),
        _ => eprintln!("usage"),
    }
}
