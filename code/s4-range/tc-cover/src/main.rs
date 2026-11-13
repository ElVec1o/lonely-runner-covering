// tc_cert: time-cover certificates for S4 v (four runners), exact integer checker mirroring the Lean `tcOK`.
// Certificate: (v0,v1,v2,v3), q, times n_1..n_N (time n/q).  Box of time n: w_c = (10 v_c n + 8 q) mod 10q.
// A piece index p in [0,10q) lies in the closed arc of box n for coordinate c iff (p + w_c) mod 10q <= 6q.
// Runner 0 has phase 0 (p = 0): box usable iff w_0 <= 6q.  Cover check = for all (p1,p2,p3) exists box usable with all three.
use std::env;
use std::fs;
use std::io::Write;

type V4 = [u64; 4];

fn wv(q: u64, v: u64, n: u64) -> u64 { (10 * v * n + 8 * q) % (10 * q) }

fn boxes(v: &V4, q: u64, times: &[u64]) -> Vec<[u64; 3]> {
    let mut out = vec![];
    for &n in times {
        let w0 = wv(q, v[0], n);
        if w0 <= 6 * q { out.push([wv(q, v[1], n), wv(q, v[2], n), wv(q, v[3], n)]); }
    }
    out
}

fn tabm(m2: u64, l2: u64, ws: &[u64]) -> Vec<u128> {
    (0..m2).map(|p| {
        let mut m = 0u128;
        for (k, &w) in ws.iter().enumerate() { if (p + w) % m2 <= l2 { m |= 1u128 << k; } }
        m
    }).collect()
}

fn dedup(l: &[u128]) -> Vec<u128> {
    let mut out: Vec<u128> = vec![];
    for &x in l { if out.last() != Some(&x) { out.push(x); } }
    out
}

#[derive(Default, Clone, Copy, Debug)]
pub struct Ops { tab: u64, dd: u64, l2: u64, l3: u64, total: u64 }

/// mirror of Lean `coverB`: returns (covered, ops).  perm chooses which of the 3 coordinates is level 1,2,3.
fn cover_perm(bs: &[[u64; 3]], q: u64, perm: [usize; 3]) -> (bool, Ops) {
    let m2 = 10 * q; let l2 = 6 * q;
    let mut ops = Ops::default();
    if bs.len() > 127 { return (false, ops); }
    let col = |c: usize| -> Vec<u64> { bs.iter().map(|b| b[c]).collect() };
    let t1 = tabm(m2, l2, &col(perm[0])); let t2 = tabm(m2, l2, &col(perm[1])); let t3 = tabm(m2, l2, &col(perm[2]));
    ops.tab = 3 * m2 * bs.len() as u64;
    let d1 = dedup(&t1); let d2 = dedup(&t2); let d3 = dedup(&t3);
    ops.dd = 3 * m2;
    for &x1 in &d1 {
        let masked: Vec<u128> = d2.iter().map(|&y| x1 & y).collect();
        ops.l2 += d2.len() as u64;
        let dm = dedup(&masked);
        for &s in &dm {
            ops.l3 += d3.len() as u64;
            for &x3 in &d3 { if s & x3 == 0 { ops.total = ops.tab + ops.dd + ops.l2 + ops.l3; return (false, ops); } }
        }
    }
    ops.total = ops.tab + ops.dd + ops.l2 + ops.l3;
    (true, ops)
}
fn cover(bs: &[[u64; 3]], q: u64) -> (bool, Ops) { cover_perm(bs, q, [0, 1, 2]) }
fn tc_ok(v: &V4, q: u64, times: &[u64]) -> (bool, Ops) {
    if q == 0 || v[0] == 0 { return (false, Ops::default()); }
    cover(&boxes(v, q, times), q)
}

// ---------- independent verifier: brute force over all (p1,p2,p3), masks over boxes ----------
fn brute(v: &V4, q: u64, times: &[u64]) -> bool {
    let bs = boxes(v, q, times);
    if bs.len() > 127 { return false; }
    let m2 = 10 * q; let l2 = 6 * q;
    let t: Vec<Vec<u128>> = (0..3).map(|c| tabm(m2, l2, &bs.iter().map(|b| b[c]).collect::<Vec<_>>())).collect();
    for p1 in 0..m2 as usize { for p2 in 0..m2 as usize {
        let s = t[0][p1] & t[1][p2];
        if s == 0 { return false; }
        for p3 in 0..m2 as usize { if s & t[2][p3] == 0 { return false; } }
    } }
    true
}

// ---------- open-arc variant (control): pieces strictly inside the arc (excluding both endpoints) ----------
fn brute_open(v: &V4, q: u64, times: &[u64]) -> bool {
    let m2 = 10 * q; let l2 = 6 * q;
    let mut bs: Vec<[u64; 3]> = vec![];
    for &n in times { let w0 = wv(q, v[0], n); if w0 >= 1 && w0 + 1 <= l2 { bs.push([wv(q, v[1], n), wv(q, v[2], n), wv(q, v[3], n)]); } }
    let inop = |p: u64, w: u64| { let d = (p + w) % m2; d >= 1 && d + 1 <= l2 };
    let t: Vec<Vec<u128>> = (0..3).map(|c| (0..m2).map(|p| { let mut m = 0u128; for (k, b) in bs.iter().enumerate() { if inop(p, b[c]) { m |= 1u128 << k; } } m }).collect()).collect();
    for p1 in 0..m2 as usize { for p2 in 0..m2 as usize { let s = t[0][p1] & t[1][p2]; if s == 0 { return false; } for p3 in 0..m2 as usize { if s & t[2][p3] == 0 { return false; } } } }
    true
}

// ---------- rational arithmetic for the definition-level test ----------
fn gcd(a: i128, b: i128) -> i128 { if b == 0 { a.abs() } else { gcd(b, a % b) } }
#[derive(Clone, Copy, Debug)]
struct Fr { n: i128, d: i128 }
fn fr(n: i128, d: i128) -> Fr { let g = gcd(n, d).max(1); let (mut n, mut d) = (n / g, d / g); if d < 0 { n = -n; d = -d; } Fr { n, d } }
impl Fr {
    fn add(self, o: Fr) -> Fr { fr(self.n * o.d + o.n * self.d, self.d * o.d) }
    fn mul(self, o: Fr) -> Fr { fr(self.n * o.n, self.d * o.d) }
    fn floor(self) -> i128 { self.n.div_euclid(self.d) }
    fn ceil(self) -> i128 { -((-self.n).div_euclid(self.d)) }
}
struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { let mut x = self.0; x ^= x << 13; x ^= x >> 7; x ^= x << 17; self.0 = x; x } fn below(&mut self, n: u64) -> u64 { self.next() % n } }

/// ||x|| >= 1/5 for rational x
fn good(x: Fr) -> bool { let r = x.n.rem_euclid(x.d); 5 * r >= x.d && 5 * r <= 4 * x.d }

/// end-to-end test of the soundness proof at a rational phase: returns Some(true) if the construction yields a good time
fn e2e(v: &V4, q: u64, times: &[u64], phi: &[Fr; 4]) -> bool {
    let tau = fr(-phi[0].n, phi[0].d).mul(fr(1, v[0] as i128));
    let ph: Vec<Fr> = (0..4).map(|i| phi[i].add(tau.mul(fr(v[i] as i128, 1)))).collect();
    let m2 = 10 * q as i128;
    let mut p = [0i128; 4];
    for i in 0..4 { let x = ph[i].mul(fr(5 * q as i128, 1)); p[i] = (x.floor() + x.ceil()).rem_euclid(m2); }
    for &n in times {
        let mut ok = true;
        for i in 0..4 { let w = wv(q, v[i], n) as i128; if (p[i] + w) % m2 > 6 * q as i128 { ok = false; break; } }
        if ok {
            let t = fr(n as i128, q as i128).add(tau);
            return (0..4).all(|i| good(fr(v[i] as i128, 1).mul(t).add(phi[i])));
        }
    }
    false
}

fn parse_vec(line: &str) -> Option<V4> {
    let w: Vec<u64> = line.split_whitespace().take(4).filter_map(|x| x.parse().ok()).collect();
    if w.len() == 4 { Some([w[0], w[1], w[2], w[3]]) } else { None }
}

fn admissible(v: &V4, q: u64) -> Vec<u64> { (0..q).filter(|&n| wv(q, v[0], n) <= 6 * q).collect() }

fn eliminate(v: &V4, q: u64, full: &[u64], rng: &mut Rng, rounds: usize) -> Vec<u64> {
    let mut best = full.to_vec();
    for round in 0..rounds {
        let mut cur = full.to_vec();
        let mut order: Vec<usize> = (0..cur.len()).collect();
        if round > 0 { for i in (1..order.len()).rev() { let j = rng.below(i as u64 + 1) as usize; order.swap(i, j); } }
        let mut alive = vec![true; cur.len()];
        for &i in &order {
            alive[i] = false;
            let sub: Vec<u64> = cur.iter().enumerate().filter(|(k, _)| alive[*k]).map(|(_, &x)| x).collect();
            if sub.is_empty() || !tc_ok(v, q, &sub).0 { alive[i] = true; }
        }
        cur = cur.iter().enumerate().filter(|(k, _)| alive[*k]).map(|(_, &x)| x).collect();
        if cur.len() < best.len() { best = cur; }
    }
    best
}

/// search: smallest q in [qmin,qmax] where the full admissible set covers, then try `extra` further q's; pick least ops
fn find(v: &V4, qmin: u64, qmax: u64, extra: u64, rng: &mut Rng) -> Option<(u64, Vec<u64>, Ops)> {
    let mut best: Option<(u64, Vec<u64>, Ops)> = None;
    let mut first: Option<u64> = None;
    for q in qmin..=qmax {
        if let Some(f) = first { if q > f + extra { break; } }
        let adm = admissible(v, q);
        if adm.len() < 3 || adm.len() > 127 { continue; }
        if !tc_ok(v, q, &adm).0 { continue; }
        if first.is_none() { first = Some(q); }
        let el = eliminate(v, q, &adm, rng, 6);
        let (ok, ops) = tc_ok(v, q, &el);
        if !ok { continue; }
        if best.as_ref().map_or(true, |b| ops.total < b.2.total) { best = Some((q, el, ops)); }
    }
    best
}

fn cert_line(v: &V4, q: u64, t: &[u64], ops: &Ops) -> String {
    format!("{} {} {} {} q={} N={} ops={} times={}", v[0], v[1], v[2], v[3], q, t.len(), ops.total, t.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","))
}
fn parse_cert(line: &str) -> Option<(V4, u64, Vec<u64>)> {
    let v = parse_vec(line)?;
    let mut q = 0u64; let mut times = vec![];
    for tok in line.split_whitespace().skip(4) {
        if let Some(r) = tok.strip_prefix("q=") { q = r.parse().ok()?; }
        if let Some(r) = tok.strip_prefix("times=") { times = r.split(',').filter(|s| !s.is_empty()).map(|s| s.parse().unwrap()).collect(); }
    }
    if q == 0 { return None; }
    Some((v, q, times))
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("");
    match mode {
        // gen LISTFILE OUTFILE QMIN QMAX EXTRA SEED [START END]
        "gen" => {
            let txt = fs::read_to_string(&args[2]).unwrap();
            let (qmin, qmax, extra, seed): (u64, u64, u64, u64) = (args[4].parse().unwrap(), args[5].parse().unwrap(), args[6].parse().unwrap(), args[7].parse().unwrap());
            let mut rng = Rng(seed | 1);
            let mut out = fs::File::create(&args[3]).unwrap();
            let (mut found, mut none) = (0, 0);
            for line in txt.lines() {
                let v = match parse_vec(line) { Some(v) => v, None => continue };
                match find(&v, qmin, qmax, extra, &mut rng) {
                    Some((q, t, ops)) => { writeln!(out, "{}", cert_line(&v, q, &t, &ops)).unwrap(); found += 1; }
                    None => { writeln!(out, "{} {} {} {} NONE", v[0], v[1], v[2], v[3]).unwrap(); none += 1; }
                }
                out.flush().unwrap();
            }
            println!("GEN found {} none {}", found, none);
        }
        // verify CERTFILE [PHASES]
        "verify" => {
            let txt = fs::read_to_string(&args[2]).unwrap();
            let nph: usize = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(2000);
            let mut rng = Rng(0x9e3779b97f4a7c15);
            let (mut n, mut bad) = (0, 0);
            let (mut maxops, mut sumops, mut maxq, mut maxn) = (0u64, 0u64, 0u64, 0usize);
            for line in txt.lines() {
                let (v, q, t) = match parse_cert(line) { Some(x) => x, None => { if !line.trim().is_empty() { println!("VERIFY SKIP {}", line); bad += 1; } continue; } };
                n += 1;
                let (ok, ops) = tc_ok(&v, q, &t);
                let br = brute(&v, q, &t);
                let mut e2e_fail = 0;
                for _ in 0..nph {
                    let d = 1 + rng.below(997) as i128;
                    let phi = [fr(rng.below(d as u64) as i128, d), fr(rng.below(d as u64) as i128, d), fr(rng.below(d as u64) as i128, d), fr(rng.below(d as u64) as i128, d)];
                    if !e2e(&v, q, &t, &phi) { e2e_fail += 1; }
                }
                // each time necessary?  (informational)
                let mut nec = 0;
                for r in 0..t.len() { let sub: Vec<u64> = t.iter().enumerate().filter(|(k, _)| *k != r).map(|(_, &x)| x).collect(); if !tc_ok(&v, q, &sub).0 { nec += 1; } }
                let status = if ok && br && e2e_fail == 0 { "OK" } else { bad += 1; "FAIL" };
                println!("VERIFY {:?} q={} N={} mirror={} brute={} e2e_fail={}/{} necessary={}/{} ops={} {}", v, q, t.len(), ok, br, e2e_fail, nph, nec, t.len(), ops.total, status);
                maxops = maxops.max(ops.total); sumops += ops.total; maxq = maxq.max(q); maxn = maxn.max(t.len());
            }
            println!("VERIFY SUMMARY certs {} bad {} maxops {} sumops {} maxq {} maxN {}", n, bad, maxops, sumops, maxq, maxn);
        }
        // ops VECTOR... q times : print ops for all 6 coordinate orders
        "perm" => {
            let txt = fs::read_to_string(&args[2]).unwrap();
            for line in txt.lines() {
                let (v, q, t) = match parse_cert(line) { Some(x) => x, None => continue };
                let bs = boxes(&v, q, &t);
                let mut r = vec![];
                for perm in [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] { let (ok, o) = cover_perm(&bs, q, perm); r.push(format!("{:?}:{}:{}", perm, ok, o.total)); }
                println!("PERM {:?} q={} N={} {}", v, q, t.len(), r.join(" "));
            }
        }
        "controls" => controls(),
        _ => println!("modes: gen verify perm controls"),
    }
}

fn controls() {
    let mut rng = Rng(12345);
    // C1: tight vectors, covers found by the generator
    let tight: [V4; 3] = [[1, 2, 3, 4], [1, 3, 4, 6], [1, 3, 4, 7]];
    for v in tight.iter() {
        let qs: &[u64] = if *v == [1, 3, 4, 6] { &[20] } else { &[60] };
        for &q in qs {
            let adm = admissible(v, q);
            let (ok_full, o) = tc_ok(v, q, &adm);
            println!("CTL1 {:?} q={} full admissible set ({} times) covers: {} ops {}", v, q, adm.len(), ok_full, o.total);
            if !ok_full { continue; }
            let el = eliminate(v, q, &adm, &mut rng, 8);
            let (ok, o) = tc_ok(v, q, &el);
            let br = brute(v, q, &el);
            println!("CTL1 {:?} q={} reduced N={} mirror={} brute={} ops {} times={:?}", v, q, el.len(), ok, br, o.total, el);
            let mut nec = vec![];
            for r in 0..el.len() { let sub: Vec<u64> = el.iter().enumerate().filter(|(k, _)| *k != r).map(|(_, &x)| x).collect(); let m = tc_ok(v, q, &sub).0; let b = brute(v, q, &sub); if m != b { println!("CTL1 DISAGREE mirror {} brute {}", m, b); } if !m { nec.push(el[r]); } }
            println!("CTL1 {:?} necessary times (removal uncovers) {}/{}: {:?}", v, nec.len(), el.len(), nec);
            // closed vs open
            println!("CTL3 {:?} q={} reduced cover as OPEN arcs: covers = {} (must be false); the full admissible set as open arcs: {}", v, q, brute_open(v, q, &el), brute_open(v, q, &adm));
        }
    }
    // C2: (1,1,1,5) is false: no list of times at any q can cover
    let f: V4 = [1, 1, 1, 5];
    for &q in &[5u64, 10, 15, 20, 24, 30, 40, 45, 60] {
        let all: Vec<u64> = (0..q).collect();
        let (ok, _) = tc_ok(&f, q, &all);
        let adm = admissible(&f, q);
        println!("CTL2 (1,1,1,5) q={} all {} numerators 0..q (non-admissible are dropped by the checker): accepted = {} (must be false); brute on admissible: {}", q, q, ok, brute(&f, q, &adm));
    }
    // C2b: a list of 60 random numerators (with repetition) at q=30
    let mut acc = 0;
    for _ in 0..200 { let t: Vec<u64> = (0..60).map(|_| rng.below(30)).collect(); if tc_ok(&f, 30, &t).0 { acc += 1; } }
    println!("CTL2b (1,1,1,5) q=30: 200 random lists of 60 numerators, accepted {} (must be 0)", acc);
    // C5: the open checker is not vacuously false: vectors with slack have OPEN covers
    for v in [[2u64, 3, 5, 7], [3, 4, 7, 11], [1, 2, 5, 11], [3, 4, 6, 7]].iter() {
        let mut found = None;
        for q in 5..=40u64 { let adm = admissible(v, q); if adm.len() < 3 || adm.len() > 127 { continue; } if brute_open(v, q, &adm) { found = Some((q, adm.len())); break; } }
        println!("CTL5 {:?}: least q <= 40 whose full admissible set covers with OPEN arcs: {:?}; closed checker at the same q: {}", v, found, found.map_or(false, |(q, _)| tc_ok(v, q, &admissible(v, q)).0));
    }
    // C4: end-to-end test has teeth: wrong cover (half the times removed) must produce failures
    let v: V4 = [1, 3, 4, 6]; let q = 20; let adm = admissible(&v, q);
    let half: Vec<u64> = adm.iter().cloned().step_by(2).collect();
    let mut fails = 0; let tot = 4000;
    for _ in 0..tot {
        let d = 1 + rng.below(397) as i128;
        let phi = [fr(rng.below(d as u64) as i128, d), fr(rng.below(d as u64) as i128, d), fr(rng.below(d as u64) as i128, d), fr(rng.below(d as u64) as i128, d)];
        if !e2e(&v, q, &half, &phi) { fails += 1; }
    }
    println!("CTL4 e2e with a non-covering list (every second admissible time of (1,3,4,6), q=20): construction fails at {}/{} random phases (must be > 0); mirror says covers = {}", fails, tot, tc_ok(&v, q, &half).0);
}
