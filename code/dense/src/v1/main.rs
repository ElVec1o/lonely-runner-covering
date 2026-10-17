// v1: independent verifier of cover-capacity certificates (written from the statement of
// LRSpectrumFull.floor_of_cover_capacity; no code shared with src/g1, src/xc2, src/cg).
//
// Statement checked, for k+1 = m, window [1, 2m]:
//   parts U_1..U_t subset [1,2m] with capacities c_i such that
//     (a) [1,2m] is contained in the union of the U_i,
//     (b) sum c_i < m   (i.e. <= m-1),
//     (c) for every i and every T subset U_i with |T| > c_i there is a time p/q whose failing set
//         bad(p/q) = { x in [1,2m] : not goodAt m-1 x p q } is contained in T,
//         where goodAt k x p q := q <= (k+2) * min(x p mod q, q - x p mod q)   (k+2 = m+1).
// Condition (c) is checked against the COMPLETE family of failing sets, obtained as follows.
// bad(t) is the set of x with dist(x t, Z) < 1/(m+1) (open condition). At a time t0 where some x has
// dist = 1/(m+1) exactly, that x is good at t0 and bad on one side, so bad(t0) is a subset of the bad
// set of the adjacent open interval. Hence every bad set contains the bad set of some breakpoint
// t0 = (a(m+1) +- 1)/(x(m+1)), 0<=a<=x<=2m, or of t0 = 0. The family F = { bad(t0) } is therefore
// the minimal-elements-complete family, and (c) over F is equivalent to (c) over all times.
// Condition (c) for U with capacity c is equivalent to: no subset of U of size c+1 is F-independent,
// i.e. alpha_F(U) <= c (independence is hereditary, so one size suffices).
// Arithmetic: u64/u128 integers and Vec<u64> bitsets, no floating point.
//
// Commands (all output to stdout; run under nice, single thread):
//   v1 check M FILE [mask|list]   verdict for one certificate (format by file name if omitted)
//   v1 selftest M                 completeness self-test of the family F against random times
//   v1 controls M FILE            negative controls on an accepted certificate
//   v1 all RESULTS_TSV            scan certs/ for m*.sol, skip rows already in RESULTS_TSV (resume), append rows
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::time::Instant;

const DIR: &str = ".";

type Bs = Vec<u64>;

fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }

/// Lean `goodAt k x p q` with k+2 = m+1, evaluated literally.
fn good_at(m: u64, x: u64, p: u64, q: u64) -> bool {
    let r = (x as u128 * p as u128 % q as u128) as u64;
    let mn = r.min(q - r);
    q as u128 <= (m as u128 + 1) * mn as u128
}

fn bad_set(m: u64, p: u64, q: u64, w: usize) -> Bs {
    let mut b = vec![0u64; w];
    for x in 1..=2 * m {
        if !good_at(m, x, p, q) {
            let i = (x - 1) as usize;
            b[i / 64] |= 1u64 << (i % 64);
        }
    }
    b
}

fn words(m: u64) -> usize { ((2 * m + 63) / 64) as usize }

fn subset(a: &[u64], b: &[u64]) -> bool { a.iter().zip(b).all(|(x, y)| x & !y == 0) }
fn popcnt(a: &[u64]) -> u32 { a.iter().map(|x| x.count_ones()).sum() }

struct Fam { m: u64, w: usize, edges: Vec<Bs>, ntimes: usize, empty: bool }

fn build_family(m: u64) -> Fam {
    let w = words(m);
    let mut times: HashSet<(u64, u64)> = HashSet::new();
    times.insert((0, 1));
    for x in 1..=2 * m {
        let d = x * (m + 1);
        for a in 0..=x {
            for s in [-1i64, 1] {
                let n = (a * (m + 1)) as i64 + s;
                if n < 0 || n as u64 > d { continue; }
                let n = n as u64;
                let g = gcd(n, d);
                times.insert((n / g, d / g));
            }
        }
    }
    let mut seen: HashSet<Bs> = HashSet::new();
    let mut empty = false;
    for &(p, q) in &times {
        let b = bad_set(m, p, q, w);
        if popcnt(&b) == 0 { empty = true; }
        seen.insert(b);
    }
    let mut edges: Vec<Bs> = seen.into_iter().collect();
    edges.sort();
    Fam { m, w, edges, ntimes: times.len(), empty }
}

fn mk(elems: &[u32], w: usize) -> Bs {
    let mut b = vec![0u64; w];
    for &x in elems { let i = (x - 1) as usize; b[i / 64] |= 1u64 << (i % 64); }
    b
}
fn elems_of(b: &[u64]) -> Vec<u32> {
    let mut v = vec![];
    for (wi, &x) in b.iter().enumerate() { for j in 0..64 { if x >> j & 1 == 1 { v.push((wi * 64 + j + 1) as u32); } } }
    v
}

/// alpha_F(U): maximum size of a subset of U containing no edge of F. Exact, by branching on elements.
fn alpha(edges_in_u: &[&Bs], ue: &[u32], w: usize) -> u32 {
    fn rec(i: usize, ue: &[u32], cur: &mut Bs, size: u32, best: &mut u32, e: &[&Bs], w: usize) {
        if size + (ue.len() - i) as u32 <= *best { return; }
        if i == ue.len() { *best = size; return; }
        let x = ue[i] as usize - 1;
        let (wi, bi) = (x / 64, 1u64 << (x % 64));
        cur[wi] |= bi;
        let ok = !e.iter().any(|ed| ed[wi] & bi != 0 && subset(ed, cur));
        if ok { rec(i + 1, ue, cur, size + 1, best, e, w); }
        cur[wi] &= !bi;
        rec(i + 1, ue, cur, size, best, e, w);
    }
    let mut best = 0;
    let mut cur = vec![0u64; w];
    rec(0, ue, &mut cur, 0, &mut best, edges_in_u, w);
    best
}

#[derive(Clone)]
struct Part { elems: Vec<u32>, cap: u32 }

fn parse_cert(path: &str, list: bool) -> Result<Vec<Part>, String> {
    let txt = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let mut parts = vec![];
    for (ln, line) in txt.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() { continue; }
        let tok: Vec<&str> = line.split_whitespace().collect();
        if list {
            let cap: u32 = tok[0].parse().map_err(|_| format!("line {}: bad cap", ln + 1))?;
            let mut el = vec![];
            for t in &tok[1..] { el.push(t.parse::<u32>().map_err(|_| format!("line {}: bad element", ln + 1))?); }
            parts.push(Part { elems: el, cap });
        } else {
            if tok.len() != 2 { return Err(format!("line {}: expected 'mask cap'", ln + 1)); }
            let mask: u128 = tok[0].parse().map_err(|_| format!("line {}: bad mask", ln + 1))?;
            let cap: u32 = tok[1].parse().map_err(|_| format!("line {}: bad cap", ln + 1))?;
            let mut el = vec![];
            for i in 0..128u32 { if mask >> i & 1 == 1 { el.push(i + 1); } }
            parts.push(Part { elems: el, cap });
        }
    }
    Ok(parts)
}

struct Verdict { ok: bool, msg: String, witnesses: usize }

/// Full check of (a), (b), (c). Also returns the number of distinct breakpoint bad sets used as witnesses
/// (greedy: first edge in sorted order inside each (c+1)-subset).
fn check(f: &Fam, parts: &[Part], skip_edge: Option<&HashSet<Bs>>) -> Verdict {
    let m = f.m;
    let w = f.w;
    let mut fail = vec![];
    // (0) shape
    for (i, p) in parts.iter().enumerate() {
        let mut s = p.elems.clone(); s.sort(); s.dedup();
        if s.len() != p.elems.len() { fail.push(format!("part {} has repeated elements", i)); }
        if p.elems.iter().any(|&x| x < 1 || x as u64 > 2 * m) { fail.push(format!("part {} has element outside [1,{}]", i, 2 * m)); }
    }
    if !fail.is_empty() { return Verdict { ok: false, msg: fail.join("; "), witnesses: 0 }; }
    // (a) cover
    let mut cov = vec![0u64; w];
    for p in parts { for &x in &p.elems { let i = (x - 1) as usize; cov[i / 64] |= 1 << (i % 64); } }
    let miss: Vec<u32> = (1..=2 * m as u32).filter(|&x| { let i = (x - 1) as usize; cov[i / 64] >> (i % 64) & 1 == 0 }).collect();
    if !miss.is_empty() { fail.push(format!("cover fails, uncovered {:?}", &miss[..miss.len().min(8)])); }
    // (b) sum
    let sum: u64 = parts.iter().map(|p| p.cap as u64).sum();
    if sum > m - 1 { fail.push(format!("sum cap {} > m-1 = {}", sum, m - 1)); }
    // (c) capacities
    let mut maxpart = 0;
    let mut slack = 0u32;
    let mut used: HashSet<Bs> = HashSet::new();
    for (i, p) in parts.iter().enumerate() {
        maxpart = maxpart.max(p.elems.len());
        let u = mk(&p.elems, w);
        let ein: Vec<&Bs> = f.edges.iter().filter(|e| subset(e, &u) && skip_edge.map_or(true, |s| !s.contains(*e))).collect();
        let a = alpha(&ein, &p.elems, w);
        if a > p.cap { fail.push(format!("part {} {:?}: alpha {} > cap {}", i, p.elems, a, p.cap)); }
        else { slack += p.cap - a; }
        // witnesses: for every (cap+1)-subset, first edge inside
        if a <= p.cap && (p.cap as usize) < p.elems.len() {
            let n = p.elems.len(); let r = p.cap as usize + 1;
            let mut idx: Vec<usize> = (0..r).collect();
            loop {
                let t = mk(&idx.iter().map(|&j| p.elems[j]).collect::<Vec<_>>(), w);
                if let Some(e) = ein.iter().find(|e| subset(e, &t)) { used.insert((*e).clone()); }
                // next combination
                let mut k = r;
                while k > 0 && idx[k - 1] == n - r + k - 1 { k -= 1; }
                if k == 0 { break; }
                idx[k - 1] += 1;
                for j in k..r { idx[j] = idx[j - 1] + 1; }
            }
        }
    }
    let ok = fail.is_empty();
    let msg = if ok {
        format!("ACCEPT: {} parts, sum cap {} <= {}, max part {}, cap slack over exact alpha {}, {} distinct witness bad-sets, family {} sets from {} breakpoint times",
            parts.len(), sum, m - 1, maxpart, slack, used.len(), f.edges.len(), f.ntimes)
    } else { format!("REJECT: {}", fail.join("; ")) };
    Verdict { ok, msg, witnesses: used.len() }
}

fn lcg(s: &mut u64) -> u64 { *s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); *s >> 11 }

fn selftest(f: &Fam, n: usize, seed: u64) -> Result<String, String> {
    // every bad set of an actual time must contain some member of F (the family is complete).
    let mut s = seed;
    let mut checked = 0usize;
    for _ in 0..n {
        let q = 1 + lcg(&mut s) % 6000;
        let p = lcg(&mut s) % (q + 1);
        let b = bad_set(f.m, p, q, f.w);
        if !f.edges.iter().any(|e| subset(e, &b)) { return Err(format!("time {}/{}: bad set contains no family member", p, q)); }
        checked += 1;
    }
    // times at exact breakpoint neighbours with large denominators
    for _ in 0..n / 10 {
        let x = 1 + lcg(&mut s) % (2 * f.m);
        let a = lcg(&mut s) % (x + 1);
        let d = x * (f.m + 1) * 1000;
        let base = a * (f.m + 1) * 1000;
        for dl in [-3i64, -1, 0, 1, 3] {
            let n = base as i64 + dl;
            if n < 0 || n as u64 > d { continue; }
            let b = bad_set(f.m, n as u64, d, f.w);
            if !f.edges.iter().any(|e| subset(e, &b)) { return Err(format!("near-breakpoint time {}/{} fails", n, d)); }
            checked += 1;
        }
    }
    Ok(format!("completeness selftest: {} times, every bad set contains a family member (seed {})", checked, seed))
}

fn controls(f: &Fam, parts: &[Part]) -> String {
    let m = f.m; let w = f.w;
    let mut out = String::new();
    let base = check(f, parts, None);
    out += &format!("baseline: {}\n", if base.ok { "ACCEPT" } else { "REJECT" });
    if !base.ok { return out + "baseline rejected, controls not meaningful\n"; }
    // C1: shrink one capacity by 1 (parts with cap>=1). Expect REJECT exactly when alpha == cap.
    let (mut shr_rej, mut shr_n, mut shr_acc_slack) = (0, 0, 0);
    for i in 0..parts.len() {
        if parts[i].cap == 0 { continue; }
        let mut q = parts.to_vec(); q[i].cap -= 1;
        let v = check(f, &q, None); shr_n += 1;
        if !v.ok { shr_rej += 1; } else { shr_acc_slack += 1; }
    }
    out += &format!("C1 shrink one cap by 1: {} of {} rejected ({} accepted: these parts had cap slack over exact alpha)\n", shr_rej, shr_n, shr_acc_slack);
    // C2: raise sum above m-1 by increasing a cap by (m-1-sum+1)
    let sum: u64 = parts.iter().map(|p| p.cap as u64).sum();
    let mut q = parts.to_vec(); q[0].cap += (m - sum) as u32;
    let v = check(f, &q, None);
    out += &format!("C2 sum cap pushed to {} > m-1: {}\n", sum + (m - sum), if v.ok { "ACCEPTED (BAD)" } else { "rejected" });
    // C3: drop each part's element from cover (remove x from all parts) for a sample of x: expect reject
    let mut c3 = (0, 0);
    for x in 1..=(2 * m as u32) {
        let mut q = parts.to_vec();
        for p in q.iter_mut() { p.elems.retain(|&e| e != x); }
        let v = check(f, &q, None); c3.1 += 1; if !v.ok { c3.0 += 1; }
    }
    out += &format!("C3 delete an element from the cover entirely: {} of {} rejected\n", c3.0, c3.1);
    // C4: corrupt a part by adding one outside element (cap unchanged). Count rejections; accepted ones must have alpha<=cap anyway.
    let (mut rej, mut tot) = (0, 0);
    for i in 0..parts.len() {
        for x in 1..=(2 * m as u32) {
            if parts[i].elems.contains(&x) { continue; }
            let mut q = parts.to_vec(); q[i].elems.push(x);
            let v = check(f, &q, None); tot += 1; if !v.ok { rej += 1; }
        }
    }
    out += &format!("C4 add one outside element to one part, cap unchanged: {} of {} rejected (accepted ones keep alpha<=cap)\n", rej, tot);
    // C5: merge two parts keeping caps additive-minus-one (cap = c1+c2-1 when both >=1): expect reject often
    // C6: drop witness times. Collect the greedy witness sets, remove each individually, then all.
    let mut used: Vec<Bs> = vec![];
    {
        let mut all: HashSet<Bs> = HashSet::new();
        for p in parts {
            let u = mk(&p.elems, w);
            let ein: Vec<&Bs> = f.edges.iter().filter(|e| subset(e, &u)).collect();
            let n = p.elems.len(); let r = p.cap as usize + 1;
            if r > n { continue; }
            let mut idx: Vec<usize> = (0..r).collect();
            loop {
                let t = mk(&idx.iter().map(|&j| p.elems[j]).collect::<Vec<_>>(), w);
                if let Some(e) = ein.iter().find(|e| subset(e, &t)) { all.insert((*e).clone()); }
                let mut k = r; while k > 0 && idx[k - 1] == n - r + k - 1 { k -= 1; }
                if k == 0 { break; }
                idx[k - 1] += 1; for j in k..r { idx[j] = idx[j - 1] + 1; }
            }
        }
        used.extend(all);
    }
    let (mut essential, mut redundant) = (0, 0);
    for e in &used {
        let mut s = HashSet::new(); s.insert(e.clone());
        if check(f, parts, Some(&s)).ok { redundant += 1; } else { essential += 1; }
    }
    let allset: HashSet<Bs> = used.iter().cloned().collect();
    let vall = check(f, parts, Some(&allset));
    out += &format!("C6 drop a witness bad-set ({} used): removing one alone rejects for {} (essential), {} replaced by other family members; removing ALL used: {}\n",
        used.len(), essential, redundant, if vall.ok { "ACCEPTED (BAD)" } else { "rejected" });
    // C7: whole family emptied of sets inside the largest part: trivial reject
    out
}

fn mfromname(path: &str) -> Option<u64> {
    let b = path.rsplit('/').next()?;
    let b = b.strip_prefix('m')?;
    let d: String = b.chars().take_while(|c| c.is_ascii_digit()).collect();
    d.parse().ok()
}

fn is_list(path: &str) -> bool { path.contains(".g1.") }

fn fam_cache<'a>(c: &'a mut HashMap<u64, Fam>, m: u64) -> &'a Fam {
    c.entry(m).or_insert_with(|| build_family(m))
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 2 { eprintln!("usage: see source header"); std::process::exit(2); }
    match a[1].as_str() {
        "check" => {
            let m: u64 = a[2].parse().unwrap();
            let list = a.get(4).map(|s| s == "list").unwrap_or(is_list(&a[3]));
            let t = Instant::now();
            let f = build_family(m);
            if f.empty { println!("WARNING: family contains an EMPTY bad set (degenerate)"); }
            let parts = parse_cert(&a[3], list).unwrap_or_else(|e| { println!("m={} PARSE ERROR {}", m, e); std::process::exit(1) });
            let v = check(&f, &parts, None);
            println!("m={} {} [{:.1}s]", m, v.msg, t.elapsed().as_secs_f64());
            std::process::exit(if v.ok { 0 } else { 1 });
        }
        "selftest" => {
            let m: u64 = a[2].parse().unwrap();
            let f = build_family(m);
            match selftest(&f, 200_000, 12345) { Ok(s) => println!("m={} {}", m, s), Err(e) => { println!("m={} SELFTEST FAIL {}", m, e); std::process::exit(1) } }
        }
        "controls" => {
            let m: u64 = a[2].parse().unwrap();
            let list = is_list(&a[3]);
            let f = build_family(m);
            let parts = parse_cert(&a[3], list).unwrap();
            print!("m={} file={}\n{}", m, a[3], controls(&f, &parts));
        }
        "all" => {
            let results = &a[2];
            let done: HashSet<String> = std::fs::read_to_string(results).unwrap_or_default().lines()
                .filter_map(|l| l.split('\t').next().map(|s| s.to_string())).collect();
            let mut files: Vec<String> = std::fs::read_dir(format!("{}/certs", DIR)).unwrap()
                .filter_map(|e| e.ok()).map(|e| e.file_name().to_string_lossy().to_string())
                .filter(|n| n.starts_with('m') && n.ends_with(".sol")).collect();
            files.sort_by_key(|n| (mfromname(n).unwrap_or(0), n.clone()));
            let todo: Vec<&String> = files.iter().filter(|n| {
                let sz = std::fs::metadata(format!("{}/certs/{}", DIR, n)).map(|m| m.len()).unwrap_or(0);
                !done.contains(&format!("{}:{}", n, sz))
            }).collect();
            println!("v1 all: {} files total, {} to do", files.len(), todo.len());
            let mut cache: HashMap<u64, Fam> = HashMap::new();
            let t0 = Instant::now();
            for (i, n) in todo.iter().enumerate() {
                let path = format!("{}/certs/{}", DIR, n);
                let sz = std::fs::metadata(&path).map(|m| m.len()).unwrap_or(0);
                let Some(m) = mfromname(n) else { continue };
                let t = Instant::now();
                let fam_t = Instant::now();
                let have = cache.contains_key(&m);
                let f = fam_cache(&mut cache, m);
                let fam_s = if have { 0.0 } else { fam_t.elapsed().as_secs_f64() };
                let row = match parse_cert(&path, is_list(n)) {
                    Err(e) => format!("PARSE_ERROR\t{}", e),
                    Ok(parts) => { let v = check(f, &parts, None); format!("{}\t{}", if v.ok { "ACCEPT" } else { "REJECT" }, v.msg) }
                };
                let line = format!("{}:{}\t{}\t{}\t{:.1}\t{}", n, sz, m, row, fam_s + t.elapsed().as_secs_f64() - fam_s, f.edges.len());
                println!("{}", line);
                let mut fh = std::fs::OpenOptions::new().create(true).append(true).open(results).unwrap();
                writeln!(fh, "{}", line).unwrap();
                let el = t0.elapsed().as_secs_f64();
                let eta = el / (i + 1) as f64 * (todo.len() - i - 1) as f64;
                println!("progress {}/{} elapsed {:.0}s ETA {:.0}s", i + 1, todo.len(), el, eta);
            }
        }
        _ => { eprintln!("unknown command"); std::process::exit(2); }
    }
}
