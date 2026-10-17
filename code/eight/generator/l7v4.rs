// l7v4.rs -- emit v4 certificates (lean-mathlib/LRSpectrumFull/EightCheckV4.lean) for the k=7 Lemma-7
// tree in the l7x2 "best" configuration: SYM=e root (1 in V, ratio-min multiple of 8 e, children in
// increasing e), BOUND=mwu (uniform / top-r / weighted, integer weights <= YMAX=31, MWUIT=300, at r<=3),
// REST leaves (RESTMWUR=3), ORD=desc, BR=minc, ratio-min filter at children of r>=5 nodes (FILTR=4).
// Tree semantics are copied from l7x2.rs; node count is cross-checked against logs/x/all_best.txt.
// Usage: l7v4 p root  out.lean [ctrl]        whole tree as one checkRoot theorem (+ controls)
//        l7v4 p tasks out.lean ntasks [ctrl] ntasks subtrees rooted at r=4 states, even stride
//        l7v4 p count                        node / record statistics only
use std::fmt::Write as _;
const NW: usize = 11;
type BS = [u64; NW];
fn pc(a: &BS) -> u32 { a.iter().map(|x| x.count_ones()).sum() }
fn and(a: &BS, b: &BS) -> BS { let mut r = [0; NW]; for i in 0..NW { r[i] = a[i] & b[i]; } r }
fn andn(a: &BS, b: &BS) -> BS { let mut r = [0; NW]; for i in 0..NW { r[i] = a[i] & !b[i]; } r }
fn pc_and(a: &BS, b: &BS) -> u32 { let mut s = 0; for i in 0..NW { s += (a[i] & b[i]).count_ones(); } s }
fn set(a: &mut BS, i: usize) { a[i >> 6] |= 1u64 << (i & 63); }
fn clr(a: &mut BS, i: usize) { a[i >> 6] &= !(1u64 << (i & 63)); }
fn get(a: &BS, i: usize) -> bool { a[i >> 6] >> (i & 63) & 1 == 1 }
fn iter(a: &BS) -> Vec<usize> { let mut v = vec![]; for w in 0..NW { let mut x = a[w]; while x != 0 { v.push(w * 64 + x.trailing_zeros() as usize); x &= x - 1; } } v }
// all literals are emitted RAW (`nat_lit`): an elaborated numeral is `OfNat.ofNat n` and the kernel
// unfolds the instance at every use (measured: 5x slower table lookups)
fn hexw(w: &[u64]) -> String { let mut i = w.len(); while i > 0 && w[i-1] == 0 { i -= 1; } if i == 0 { return "(nat_lit 0)".into(); } let mut s = format!("(nat_lit 0x{:x}", w[i-1]); for x in w[..i-1].iter().rev() { write!(s, "{:016x}", x).unwrap(); } s.push(')'); s }
fn nat16(f: &[u16]) -> String { let mut w = vec![0u64; (f.len() + 3) / 4]; for (i, x) in f.iter().enumerate() { w[i / 4] |= (*x as u64) << (16 * (i % 4)); } hexw(&w) }
fn gcd(a: usize, b: usize) -> usize { if b == 0 { a } else { gcd(b, a % b) } }
fn nrm(q: usize, x: usize) -> usize { let x = x % q; x.min(q - x) }

struct P { k: usize, q: usize, w: usize, cover: Vec<BS>, covby: Vec<BS>, even: BS, units: BS, m8: BS, inv: Vec<usize> }
#[derive(Clone)] struct St { sz: usize, avail: BS, unc: BS, ev: usize, d: usize }
#[derive(Default)] struct Stats { nodes: u64, leaves: [u64; 6], rest: u64, done: u64, work: u64, removals: u64, fields: u64, supp: u64, cnti: u64, kids: u64 }
static mut TPOS: Vec<usize> = Vec::new();
static mut SPLIT: bool = false;
static mut DELEG: Vec<St> = Vec::new();
fn push_leaf(out: &mut Vec<u16>, rec: Vec<u16>) { let t = out.len() + if rec[0] == 3 { 1 } else { 2 + rec[1] as usize }; unsafe { (*std::ptr::addr_of_mut!(TPOS)).push(t); } out.extend(rec); }
const YMAX: f64 = 31.0; const MWUIT: usize = 300; const MWUR: usize = 3; const RESTMWUR: usize = 3; const FILTR: usize = 4;

fn spread(a: &BS, w: usize) -> Vec<u64> { let mut o = vec![0u64; (16 * (w + 1) + 63) / 64]; for v in iter(a) { let b = 16 * v; o[b / 64] |= 1u64 << (b % 64); } o }

// weighted bound by multiplicative weights (identical loop to l7x2 mwu/mwu_y)
fn mwu_y(pr: &P, unc: &BS, avail: &BS, r: usize) -> Option<(Vec<(usize, u64)>, u64)> {
    let us = iter(unc); let av = iter(avail); let n = us.len();
    if n == 0 || av.is_empty() { return None; }
    let mut vidx = vec![usize::MAX; pr.w + 1]; for (i, &v) in av.iter().enumerate() { vidx[v] = i; }
    let lists: Vec<Vec<usize>> = us.iter().map(|&j| iter(&and(&pr.covby[j], avail)).into_iter().map(|v| vidx[v]).collect()).collect();
    let mut y = vec![1f64; n]; let eps = 0.25; let mut load = vec![0f64; av.len()];
    for _it in 0..MWUIT {
        for x in load.iter_mut() { *x = 0.0; }
        for (i, l) in lists.iter().enumerate() { for &v in l { load[v] += y[i]; } }
        let (mut bi, mut bl) = (0, -1.0); for (i, &l) in load.iter().enumerate() { if l > bl { bl = l; bi = i; } }
        let ym = y.iter().cloned().fold(0.0, f64::max);
        let yi: Vec<u64> = y.iter().map(|x| ((x / ym) * YMAX).round() as u64).collect();
        let yt: u64 = yi.iter().sum();
        let mut li = vec![0u64; av.len()]; for (i, l) in lists.iter().enumerate() { if yi[i] > 0 { for &v in l { li[v] += yi[i]; } } }
        let mx = *li.iter().max().unwrap();
        if mx * (r as u64) < yt { return Some((us.iter().zip(yi.iter()).filter(|(_, w)| **w > 0).map(|(j, w)| (*j, *w)).collect(), mx)); }
        let v = av[bi]; for (i, &j) in us.iter().enumerate() { if get(&pr.cover[v], j) { y[i] *= 1.0 - eps; } }
    }
    None
}
// bound leaf record (tag 3 or 5) if the (unc, avail, r) state is closed by a bound
fn prune_cert(pr: &P, unc: &BS, avail: &BS, r: usize, mwur: usize, st: &mut Stats) -> Option<Vec<u16>> {
    let nu = pc(unc); let al = iter(avail);
    let cnt: Vec<(u32, usize)> = al.iter().map(|&v| (pc_and(&pr.cover[v], unc), v)).collect();
    let mx = cnt.iter().map(|x| x.0).max().unwrap_or(0);
    if (mx as usize) * r < nu as usize { st.leaves[3] += 1; st.work += 3; return Some(vec![3, mx as u16, 0]); }
    let mut s = cnt.clone(); s.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
    let top: u32 = s.iter().take(r).map(|x| x.0).sum();
    if (top as usize) < nu as usize {
        let t = if s.len() >= r { s[r - 1].0 } else { 0 };
        let nt = (r - 1).min(s.len());
        let mut tv: Vec<usize> = s[..nt].iter().map(|x| x.1).collect(); tv.sort();
        let mut rec = vec![3u16, t as u16, nt as u16]; for v in tv { rec.push(v as u16); }
        st.leaves[4] += 1; st.work += 3 + nt as u64; return Some(rec); }
    if r <= mwur { if let Some((y, mx)) = mwu_y(pr, unc, avail, r) {
        let mut rec = vec![5u16, y.len() as u16]; for (j, w) in &y { assert!(*j < 1024 && *w < 64); rec.push((*j as u16) | ((*w as u16) << 10)); }
        rec.push(mx as u16); rec.push(0); st.leaves[5] += 1; st.supp += y.len() as u64; st.work += 3 + y.len() as u64; return Some(rec); } }
    None
}
// ratio-min filter after adding c at parameter d: (removed w, witness x) pairs
fn filter_e(pr: &P, avail: &mut BS, c: usize, d: usize) -> Vec<(usize, usize)> {
    let mut rm = vec![];
    if get(&pr.units, c) { for e in iter(&and(avail, &pr.m8)) { let x = nrm(pr.q, e * pr.inv[c] % pr.q); if x < d { assert!(x >= 1 && nrm(pr.q, x * c) == e); clr(avail, e); rm.push((e, x)); } } }
    else if get(&pr.m8, c) { for w in iter(&and(avail, &pr.units)) { let x = nrm(pr.q, c * pr.inv[w] % pr.q); if x < d { assert!(x >= 1 && nrm(pr.q, x * w) == c); clr(avail, w); rm.push((w, x)); } } }
    rm
}
// replay one subtree, appending its records; `tasks` collects (state, record range) at r = 4 nodes
fn node(pr: &P, st: &St, out: &mut Vec<u16>, s: &mut Stats, tasks: &mut Vec<(St, usize, usize)>) {
    if unsafe { SPLIT } && pr.k - st.sz == 4 { let d = unsafe { &mut *std::ptr::addr_of_mut!(DELEG) }; out.push(7); out.push(d.len() as u16); d.push(st.clone()); return; }
    s.nodes += 1; let start = out.len();
    let r = pr.k - st.sz; let nu = pc(&st.unc); let lim = pr.k - 2;
    let mut avail = st.avail; if st.ev >= lim { avail = andn(&avail, &pr.even); }
    if nu == 0 { s.done += 1; s.leaves[0] += 1; out.push(4); return; }
    if r == 0 { s.leaves[1] += 1; out.push(1); return; }
    let mut best = usize::MAX; let mut bc = u32::MAX;
    for j in iter(&st.unc) { let c = pc_and(&pr.covby[j], &avail); if c < bc { bc = c; best = j; if c == 0 { s.leaves[2] += 1; out.push(2); out.push(j as u16); return; } } }
    if let Some(rec) = prune_cert(pr, &st.unc, &avail, r, MWUR, s) { push_leaf(out, rec); return; }
    let mut cands = iter(&and(&pr.covby[best], &avail));
    cands.sort_by_key(|&c| std::cmp::Reverse(pc_and(&pr.cover[c], &st.unc)));
    out.push(0); out.push(best as u16); s.work += 1;
    let mut av = st.avail; let mut aveff = avail; let mut closed = false;
    for (ci, &c) in cands.iter().enumerate() {
        if ci > 0 { if let Some(rec) = prune_cert(pr, &st.unc, &aveff, r, RESTMWUR, s) { s.nodes += 1; s.rest += 1; out.push(2); push_leaf(out, rec); closed = true; break; } }
        clr(&mut aveff, c); clr(&mut av, c);
        let mut na = av;
        let rm = if r - 1 >= FILTR { filter_e(pr, &mut na, c, st.d) } else { vec![] };
        out.push(1); out.push(c as u16); out.push(rm.len() as u16); for (w, x) in &rm { out.push(*w as u16); out.push(*x as u16); }
        s.removals += rm.len() as u64; s.work += 2 + rm.len() as u64 + pc_and(&pr.cover[c], &st.unc) as u64; s.cnti += pc_and(&pr.cover[c], &st.unc) as u64; s.kids += 1;
        let ch = St { sz: st.sz + 1, avail: na, unc: andn(&st.unc, &pr.cover[c]), ev: st.ev + get(&pr.even, c) as usize, d: st.d };
        node(pr, &ch, out, s, tasks);
    }
    if !closed { out.push(0); }
    if r == 4 { tasks.push((st.clone(), start, out.len())); }
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let p: usize = a[1].parse().unwrap(); let mode = a[2].clone();
    let k = 7; let q = 8 * p; let w = q / 2; assert!(w < NW * 64 && w < 1024);
    let mut cover = vec![[0u64; NW]; w + 1]; let mut covby = vec![[0u64; NW]; w + 1];
    let (mut even, mut adm, mut unc, mut units, mut m8, mut all) = ([0u64; NW], [0u64; NW], [0u64; NW], [0u64; NW], [0u64; NW], [0u64; NW]);
    for v in 0..=w { set(&mut all, v); }
    for v in 1..=w { if v % p == 0 { continue; } set(&mut adm, v); if v % 2 == 0 { set(&mut even, v); } else { set(&mut units, v); } if v % 8 == 0 { set(&mut m8, v); }
        for j in 1..=w { let r = j * v % q; if 8 * r.min(q - r) < q { set(&mut cover[v], j); set(&mut covby[j], v); } } }
    for j in 1..=w { set(&mut unc, j); }
    let mut inv = vec![0usize; q]; for x in 1..q { if gcd(x, q) == 1 { for y in 1..q { if x * y % q == 1 { inv[x] = y; break; } } } }
    let pr = P { k, q, w, cover, covby, even, units, m8, inv };
    // root: S = {1}; children e over admissible multiples of 8 in increasing order
    let mut s = Stats::default(); s.nodes += 1;
    let mut av1 = adm; clr(&mut av1, 1); let unc1 = andn(&unc, &pr.cover[1]);
    let mut out: Vec<u16> = vec![]; let mut tasks = vec![]; let mut run = av1;
    for e in iter(&and(&av1, &pr.m8)) {
        clr(&mut run, e); let mut av = run;
        let rm = filter_e(&pr, &mut av, e, e);
        out.push(rm.len() as u16); for (x, y) in &rm { out.push(*x as u16); out.push(*y as u16); }
        s.removals += rm.len() as u64;
        node(&pr, &St { sz: 2, avail: av, unc: andn(&unc1, &pr.cover[e]), ev: 1, d: e }, &mut out, &mut s, &mut tasks);
    }
    s.fields = out.len() as u64;
    eprintln!("p={} W={} nodes={} leaves[done,r0,nocov,uni,top,mwu]={:?} rest={} removals={} work={} cert_fields={} r4_tasks={}", p, w, s.nodes, s.leaves, s.rest, s.removals, s.work, s.fields, tasks.len());
    if mode == "count" { return; }
    let outp = a[3].clone();
    let ctrl = a.iter().any(|x| x == "ctrl");
    let mut L = String::new();
    writeln!(L, "/- GENERATED by private/eight/src/l7v4.rs p={} mode={} (benchmark only; move out of lean-mathlib after use) -/\nimport LRSpectrumFull.EightCheckV4\n\nnamespace LRSpectrumFull.EightV4.Cert{}\nopen LRSpectrumFull.EightV4\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n-- data only: no compiled code is needed for kernel replay\nnoncomputable section\n", p, mode, p).unwrap();
    for v in 0..=w { writeln!(L, "def cvR{} : Nat := {}", v, hexw(&pr.cover[v][..])).unwrap(); }
    for j in 0..=w { writeln!(L, "def cbR{} : Nat := {}", j, hexw(&spread(&pr.covby[j], w))).unwrap(); }
    fn tree(L: &mut String, pre: &str, lo: usize, hi: usize) -> String {
        if hi - lo == 1 { return format!("{}R{}", pre, lo); }
        let mid = (lo + hi) / 2; let a = tree(L, pre, lo, mid); let b = tree(L, pre, mid, hi);
        let name = format!("{}T{}_{}", pre, lo, hi);
        let fa = if mid - lo == 1 { a.clone() } else { format!("{} j", a) }; let fb = if hi - mid == 1 { b.clone() } else { format!("{} j", b) };
        writeln!(L, "def {} (j : Nat) : Nat := bif Nat.ble (nat_lit {}) j then {} else {}", name, mid, fb, fa).unwrap(); name }
    let tc = tree(&mut L, "cv", 0, w + 1); let tb = tree(&mut L, "cb", 0, w + 1);
    // cntF: walk down a balanced tree of window masks, skipping empty ranges (default), or the lowest-bit loop
    // bit-keyed row tree for cntB
    fn btree(L: &mut String, lo: usize, hi: usize) -> String {
        if hi - lo == 1 { return format!("cbR{}", lo); }
        let mid = (lo + hi) / 2; let a = btree(L, lo, mid); let b = btree(L, mid, hi);
        let name = format!("cbB{}_{}", lo, hi);
        let fa = if mid - lo == 1 { a.clone() } else { format!("{} b", a) }; let fb = if hi - mid == 1 { b.clone() } else { format!("{} b", b) };
        let mut m = vec![0u64; mid / 64 + 1]; m[mid / 64] = 1u64 << (mid % 64);
        writeln!(L, "def {} (b : Nat) : Nat := bif Nat.ble {} b then {} else {}", name, hexw(&m), fb, fa).unwrap(); name }
    let cntf = if a.iter().any(|x| x == "bitkey") { let bt = btree(&mut L, 0, w + 1); format!("cntB {} (nat_lit 1024)", bt) }
      else if a.iter().any(|x| x == "loop") { format!("cntL {} (nat_lit 1024)", tb) } else {
        fn walk(L: &mut String, lo: usize, hi: usize) -> String {
            let name = format!("cw{}_{}", lo, hi);
            let mut m = vec![0u64; (hi + 63) / 64 + 1]; for j in lo..hi { m[j / 64] |= 1u64 << (j % 64); }
            if hi - lo == 1 { writeln!(L, "def {} (u acc : Nat) : Nat := bif Nat.beq (Nat.land u {}) 0 then acc else Nat.add acc cbR{}", name, hexw(&m), lo).unwrap(); return name; }
            let mid = (lo + hi) / 2; let a = walk(L, lo, mid); let b = walk(L, mid, hi);
            writeln!(L, "def {} (u acc : Nat) : Nat := bif Nat.beq (Nat.land u {}) 0 then acc else {} u ({} u acc)", name, hexw(&m), a, b).unwrap(); name }
        walk(&mut L, 1, w + 1) };
    writeln!(L, "def X : Ctx := {{ p := nat_lit {p}, W := nat_lit {w}, cov := {tc}, covby := {tb}, adm := {}, even := {}, m8 := {}, ones := {}, cntF := {cntf} }}\n",
        hexw(&spread(&adm, w)), hexw(&spread(&pr.even, w)), hexw(&spread(&pr.m8, w)), hexw(&spread(&all, w))).unwrap();
    // certificate as chunks of 512 fields behind a balanced tree; returns the accessor name
    let cert = |L: &mut String, name: &str, f: &[u16]| -> String {
        let nch = (f.len() + 2047) / 2048;
        for i in 0..nch { writeln!(L, "def {}_R{} : Nat := {}", name, i, nat16(&f[i * 2048..((i + 1) * 2048).min(f.len())])).unwrap(); }
        if nch == 1 { writeln!(L, "def {} (_ : Nat) : Nat := {}_R0", name, name).unwrap(); return name.to_string(); }
        let t = tree(L, &format!("{}_", name), 0, nch); t };
    let tpos: Vec<usize> = unsafe { (*std::ptr::addr_of_mut!(TPOS)).clone() };
    let semcorrupt = |rec: &[u16], lo: usize| -> Vec<u16> { let mut r = rec.to_vec();
        for &t in &tpos { if t >= lo && t < lo + r.len() && r[t - lo] > 0 { r[t - lo] -= 1; return r; } } panic!("no t field") };
    // corruption for controls: lower the threshold t of the first bound leaf record found after `from`
    let corrupt = |rec: &[u16]| -> Vec<u16> { let mut r = rec.to_vec();
        // scan for a tag-3 record "3 t n" whose t > 0 at a record boundary is hard to identify from the flat
        // stream; instead flip the final END marker / last field so the stream no longer parses correctly
        let n = r.len(); r[n - 1] ^= 1; r };
    if mode == "stage" {
        // l7v4 p stage OUTDIR MAXFIELDS TABB [ctrl]
        // OUTDIR/{Base,Tab,Top,S<g>,Asm}.lean, modules LRSpectrumFull.E8.P<p>.*; see private/eight/stage/README
        let od = a[3].clone(); let maxf: usize = a[4].parse().unwrap(); let tb: usize = a[5].parse().unwrap();
        std::fs::create_dir_all(&od).unwrap();
        let ns = format!("LRSpectrumFull.EightV4.Cert{}", p);
        let tabonly = a.iter().any(|x| x == "tabonly");
        let modp = if tabonly { format!("E8Tab.P{}", p) } else { format!("E8Stage.P{}", p) };
        let hdr = |imports: &str| -> String { format!("/- GENERATED by private/eight/src/l7v4.rs p={} mode=stage; staging only, deleted after verification -/\n{}\n\nnamespace {}\nopen LRSpectrumFull.EightV4\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n-- one kernel check at a time (async elaboration runs them in parallel: measured 1.5 GB vs 0.9 GB footprint)\nset_option Elab.async false\nnoncomputable section\n", p, imports, ns) };
        let ftr = format!("\nend\nend {}\n", ns);
        unsafe { SPLIT = true; }
        let mut top = vec![]; let mut st0 = Stats::default(); let mut tk = vec![]; let mut run = av1;
        for e in iter(&and(&av1, &pr.m8)) {
            clr(&mut run, e); let mut av = run;
            let rm = filter_e(&pr, &mut av, e, e);
            top.push(rm.len() as u16); for (x, y) in &rm { top.push(*x as u16); top.push(*y as u16); }
            node(&pr, &St { sz: 2, avail: av, unc: andn(&unc1, &pr.cover[e]), ev: 1, d: e }, &mut top, &mut st0, &mut tk);
        }
        unsafe { SPLIT = false; }
        let deleg: Vec<St> = unsafe { (*std::ptr::addr_of_mut!(DELEG)).clone() };
        let n = deleg.len(); assert!(n >= 1 && n < 65536);
        // ---- Base: tables, delegated states, top certificate
        let body = L.split("noncomputable section\n").nth(1).unwrap().to_string();
        let mut B = hdr("import LRSpectrumFull.EightCheckSound"); B.push_str(&body);
        if tabonly { B.push_str(&ftr); std::fs::write(format!("{}/Base.lean", od), &B).unwrap(); }
        for (i, st) in deleg.iter().enumerate() {
            writeln!(B, "def H{} : Nat × Nat × Nat × Nat × Nat := ((nat_lit {}), (nat_lit {}), (nat_lit {}), {}, {})", i, st.d, st.sz, st.ev, hexw(&spread(&st.avail, w)), hexw(&st.unc[..])).unwrap(); }
        writeln!(B, "def Hjunk : Nat × Nat × Nat × Nat × Nat := ((nat_lit 0), (nat_lit 99), (nat_lit 0), (nat_lit 0), (nat_lit 0))").unwrap();
        let mut size = 1; while size < n { size *= 2; }
        fn htree(L: &mut String, lo: usize, hi: usize, n: usize) -> String {
            if hi - lo == 1 { return if lo < n { format!("H{}", lo) } else { "Hjunk".to_string() }; }
            if lo >= n { return "Hjunk".to_string(); }
            let mid = (lo + hi) / 2; let a = htree(L, lo, mid, n); let b = htree(L, mid, hi, n);
            let name = format!("HT{}_{}", lo, hi);
            let fa = if a.starts_with("HT") { format!("{} i", a) } else { a.clone() }; let fb = if b.starts_with("HT") { format!("{} i", b) } else { b.clone() };
            writeln!(L, "def {} (i : Nat) : Nat × Nat × Nat × Nat × Nat := bif Nat.ble (nat_lit {}) i then {} else {}", name, mid, fb, fa).unwrap(); name }
        let ht = if n == 1 { writeln!(B, "def HT0_1 (_ : Nat) : Nat × Nat × Nat × Nat × Nat := H0").unwrap(); "HT0_1".to_string() } else { htree(&mut B, 0, size, n) };
        writeln!(B, "/-- delegated state `i` (the accessor `{ht}` below the last index) -/\ndef HS (i : Nat) : Nat × Nat × Nat × Nat × Nat := {ht} i\ndef Hc (i : Nat) : Nat × Nat × Nat × Nat × Nat := {ht} (min i {})", n - 1).unwrap();
        writeln!(B, "/-- the obligation of delegated state `k` against the certificate `c` -/\nabbrev SP (k : Nat) (c : Nat → Nat) : Prop :=\n  (HS k).2.1 ≤ 7 → checkState X (HS k).1 (HS k).2.1 (HS k).2.2.1 (HS k).2.2.2.1 (HS k).2.2.2.2 c = true").unwrap();
        let ct = cert(&mut B, "CT", &top);
        writeln!(B, "def CTop : Nat → Nat := {}\n-- top: records {} delegated {} top_nodes {}", ct, top.len(), n, st0.nodes).unwrap();
        if !tabonly { B.push_str(&ftr); std::fs::write(format!("{}/Base.lean", od), &B).unwrap(); }
        // ---- Top
        let mut T = hdr(&format!("import {}.Base", modp));
        writeln!(T, "theorem top_ok : checkRootH X CTop Hc = true := by decide +kernel").unwrap();
        T.push_str(&ftr); if !tabonly { std::fs::write(format!("{}/Top.lean", od), &T).unwrap(); }
        // ---- Tab: chunked TableOK (rows in chunks of tb), counter rows in chunks too
        let cbname = { let s = L.clone(); let i = s.find("cntF := cntB ").expect("stage needs bitkey"); s[i + 13..].split_whitespace().next().unwrap().to_string() };
        let mut nb = (w + tb) / tb; while !(w < tb * nb) { nb += 1; }
        let mut Tb = hdr(&format!("import {}.Base", modp));
        writeln!(Tb, "theorem tg : TableGlob X := by decide +kernel").unwrap();
        for k in 0..nb { writeln!(Tb, "theorem tc{k} : TableCovChunk X {tb} {k} := by decide +kernel\ntheorem tb{k} : TableCovbyChunk X {tb} {k} := by decide +kernel\ntheorem tr{k} : ∀ j ∈ winSet X.p, {tb} * {k} ≤ j → j < {tb} * ({k} + 1) → {cbname} (2 ^ j) = X.covby j := by decide +kernel").unwrap(); }
        for (nm, pre, t) in [("hc", "TableCovChunk X", "tc"), ("hcb", "TableCovbyChunk X", "tb")] {
            writeln!(Tb, "theorem {nm} : ∀ k < {nb}, {pre} {tb} k := fun k hk => match k, hk with").unwrap();
            for k in 0..nb { writeln!(Tb, "  | {k}, _ => {t}{k}").unwrap(); }
            writeln!(Tb, "  | _ + {nb}, h => absurd h (by omega)").unwrap(); }
        writeln!(Tb, "theorem hrow : ∀ k < {nb}, ∀ j ∈ winSet X.p, {tb} * k ≤ j → j < {tb} * (k + 1) → {cbname} (2 ^ j) = X.covby j := fun k hk => match k, hk with", ).unwrap();
        for k in 0..nb { writeln!(Tb, "  | {k}, _ => tr{k}").unwrap(); }
        writeln!(Tb, "  | _ + {nb}, h => absurd h (by omega)").unwrap();
        writeln!(Tb, "theorem tab_cb : ∀ j ∈ winSet X.p, {cbname} (2 ^ j) = X.covby j := by\n  intro j hj\n  have hw := (mem_winSet.1 hj).2\n  have hW : 4 * X.p = {w} := rfl\n  exact hrow (j / {tb}) (by omega) j hj (Nat.mul_div_le j {tb}) (Nat.lt_mul_div_succ j (by norm_num))").unwrap();
        writeln!(Tb, "theorem tab : TableOK X :=\n  tableOK_of_cntB X {cbname} rfl (tableFin_of_chunks X {tb} {nb} (by norm_num) (by decide) tg hc hcb) tab_cb").unwrap();
        Tb.push_str(&ftr);
        if tabonly { writeln!(Tb, "#print axioms {}.tab", ns).unwrap(); std::fs::write(format!("{}/Tab.lean", od), &Tb).unwrap();
            eprintln!("tabonly: p={} chunks={}", p, nb); return; }
        std::fs::write(format!("{}/Tab.lean", od), &Tb).unwrap();
        // ---- state groups
        let mut groups: Vec<(usize, usize)> = vec![]; let mut gs = 0; let mut gf = 0usize; let mut cur = String::new();
        let mut manifest = String::new(); let mut tn = 0u64;
        let flush = |g: usize, cur: &mut String, groups: &mut Vec<(usize, usize)>, lo: usize, hi: usize| {
            let mut S = hdr(&format!("import {}.Base", modp)); S.push_str(cur); S.push_str(&ftr);
            std::fs::write(format!("{}/S{}.lean", od, g), &S).unwrap(); groups.push((lo, hi)); cur.clear(); };
        for (i, st) in deleg.iter().enumerate() {
            let mut s2 = Stats::default(); let mut o2 = vec![]; let mut t2 = vec![]; node(&pr, st, &mut o2, &mut s2, &mut t2); tn += s2.nodes;
            if gf > 0 && gf + o2.len() > maxf { let g = groups.len(); flush(g, &mut cur, &mut groups, gs, i); gs = i; gf = 0; }
            let c = cert(&mut cur, &format!("C{}", i), &o2);
            if c != format!("C{}", i) { writeln!(cur, "def C{} : Nat → Nat := {}", i, c).unwrap(); }
            writeln!(cur, "-- task {} nodes {} work {} fields {}\ntheorem s{} : SP {} C{} := by decide +kernel", i, s2.nodes, s2.work, o2.len(), i, i, i).unwrap();
            gf += o2.len();
            writeln!(manifest, "state {} nodes {} fields {}", i, s2.nodes, o2.len()).unwrap();
        }
        { let g = groups.len(); flush(g, &mut cur, &mut groups, gs, n); }
        // ---- Asm
        let mut imps = format!("import {m}.Tab\nimport {m}.Top", m = modp);
        for g in 0..groups.len() { write!(imps, "\nimport {}.S{}", modp, g).unwrap(); }
        let mut A = hdr(&imps);
        fn ctree(L: &mut String, lo: usize, hi: usize) -> String {
            if hi - lo == 1 { return format!("C{}", lo); }
            let mid = (lo + hi) / 2; let a = ctree(L, lo, mid); let b = ctree(L, mid, hi);
            let name = format!("CsT{}_{}", lo, hi);
            let fa = if mid - lo == 1 { a.clone() } else { format!("{} i", a) }; let fb = if hi - mid == 1 { b.clone() } else { format!("{} i", b) };
            writeln!(L, "def {} (i : Nat) : Nat → Nat := bif Nat.ble (nat_lit {}) i then {} else {}", name, mid, fb, fa).unwrap(); name }
        let cst = if n == 1 { writeln!(A, "def CsT0_1 (_ : Nat) : Nat → Nat := C0").unwrap(); "CsT0_1".to_string() } else { ctree(&mut A, 0, n) };
        writeln!(A, "def Cs (i : Nat) : Nat → Nat := {cst} i\ndef Csc (i : Nat) : Nat → Nat := {cst} (min i {})\nabbrev PP (k : Nat) : Prop := SP k (Cs k)", n - 1).unwrap();
        writeln!(A, "theorem one {{P : Nat → Prop}} (a : Nat) (h : P a) : ∀ k, a ≤ k → k < a + 1 → P k := by\n  intro k h1 h2\n  have : k = a := by omega\n  subst this; exact h").unwrap();
        writeln!(A, "theorem comb {{P : Nat → Prop}} {{a m b : Nat}} (hl : ∀ k, a ≤ k → k < m → P k) (hr : ∀ k, m ≤ k → k < b → P k) :\n    ∀ k, a ≤ k → k < b → P k := by\n  intro k h1 h2\n  by_cases h : k < m\n  · exact hl k h1 h\n  · exact hr k (by omega) h2").unwrap();
        fn rtree(L: &mut String, lo: usize, hi: usize) -> String {
            let name = format!("R{}_{}", lo, hi);
            if hi - lo == 1 { writeln!(L, "theorem {} : ∀ k, {} ≤ k → k < {} → PP k := one (P := PP) {} s{}", name, lo, hi, lo, lo).unwrap(); return name; }
            let mid = (lo + hi) / 2; let a = rtree(L, lo, mid); let b = rtree(L, mid, hi);
            writeln!(L, "theorem {} : ∀ k, {} ≤ k → k < {} → PP k := comb (P := PP) {} {}", name, lo, hi, a, b).unwrap(); name }
        let rt = rtree(&mut A, 0, n);
        writeln!(A, "theorem lemma7Check_seven_p{p} : lemma7Check 7 {p} = true :=\n  lemma7Check_of_checkRootH {p} (by norm_num) (by norm_num) X tab rfl CTop Hc Csc\n    (fun i h => {rt} (min i {m}) (Nat.zero_le _) (by omega) h) top_ok", m = n - 1).unwrap();
        A.push_str(&ftr);
        writeln!(A, "#print axioms {}.lemma7Check_seven_p{}", ns, p).unwrap();
        std::fs::write(format!("{}/Asm.lean", od), &A).unwrap();
        let mut mf = format!("p {} delegated {} groups {} top_nodes {} task_nodes {} total_nodes {} top_fields {} tab_chunk {}\n", p, n, groups.len(), st0.nodes, tn, st0.nodes + tn, top.len(), tb);
        for (g, (lo, hi)) in groups.iter().enumerate() { writeln!(mf, "group S{} states {}..{}", g, lo, hi).unwrap(); }
        mf.push_str(&manifest);
        std::fs::write(format!("{}/manifest.txt", od), &mf).unwrap();
        eprintln!("stage: p={} delegated={} groups={} total_nodes={}", p, n, groups.len(), st0.nodes + tn);
        return;
    }
    if mode == "split" {
        // top certificate with delegated r = 4 states, then one checkState theorem per delegated state
        unsafe { SPLIT = true; }
        let mut top = vec![]; let mut st0 = Stats::default(); let mut tk = vec![]; let mut run = av1;
        for e in iter(&and(&av1, &pr.m8)) {
            clr(&mut run, e); let mut av = run;
            let rm = filter_e(&pr, &mut av, e, e);
            top.push(rm.len() as u16); for (x, y) in &rm { top.push(*x as u16); top.push(*y as u16); }
            node(&pr, &St { sz: 2, avail: av, unc: andn(&unc1, &pr.cover[e]), ev: 1, d: e }, &mut top, &mut st0, &mut tk);
        }
        unsafe { SPLIT = false; }
        let deleg: Vec<St> = unsafe { (*std::ptr::addr_of_mut!(DELEG)).clone() };
        assert!(deleg.len() < 65536);
        for (i, st) in deleg.iter().enumerate() {
            writeln!(L, "def H{} : Nat × Nat × Nat × Nat × Nat := ((nat_lit {}), (nat_lit {}), (nat_lit {}), {}, {})", i, st.d, st.sz, st.ev, hexw(&spread(&st.avail, w)), hexw(&st.unc[..])).unwrap(); }
        writeln!(L, "def Hjunk : Nat × Nat × Nat × Nat × Nat := ((nat_lit 0), (nat_lit 99), (nat_lit 0), (nat_lit 0), (nat_lit 0))").unwrap();
        // accessor tree over [0, 2^k) with junk beyond n
        let n = deleg.len(); let mut size = 1; while size < n { size *= 2; }
        fn htree(L: &mut String, lo: usize, hi: usize, n: usize) -> String {
            if hi - lo == 1 { return if lo < n { format!("H{}", lo) } else { "Hjunk".to_string() }; }
            if lo >= n { return "Hjunk".to_string(); }
            let mid = (lo + hi) / 2; let a = htree(L, lo, mid, n); let b = htree(L, mid, hi, n);
            let name = format!("HT{}_{}", lo, hi);
            let fa = if a.starts_with("HT") { format!("{} i", a) } else { a.clone() }; let fb = if b.starts_with("HT") { format!("{} i", b) } else { b.clone() };
            writeln!(L, "def {} (i : Nat) : Nat × Nat × Nat × Nat × Nat := bif Nat.ble (nat_lit {}) i then {} else {}", name, mid, fb, fa).unwrap(); name }
        let ht = if n == 1 { writeln!(L, "def HT (_ : Nat) : Nat × Nat × Nat × Nat × Nat := H0").unwrap(); "HT".to_string() } else { htree(&mut L, 0, size, n) };
        let ct = cert(&mut L, "CT", &top);
        let emit_tasks = !a.iter().any(|x| x == "toponly");
        writeln!(L, "-- top: records {} delegated {} top_nodes {}\ntheorem top_ok : checkRootH X {} {} = true := by decide +kernel", top.len(), n, st0.nodes, ct, ht).unwrap();
        if emit_tasks { let mut tn = 0;
            for (i, st) in deleg.iter().enumerate() {
                let mut s2 = Stats::default(); let mut o2 = vec![]; let mut t2 = vec![]; node(&pr, st, &mut o2, &mut s2, &mut t2); tn += s2.nodes;
                let c = cert(&mut L, &format!("C{}", i), &o2);
                writeln!(L, "-- task {} nodes {} work {} fields {}\ntheorem s{} : checkState X H{i}.1 H{i}.2.1 H{i}.2.2.1 H{i}.2.2.2.1 H{i}.2.2.2.2 {} = true := by decide +kernel", i, s2.nodes, s2.work, o2.len(), i, c, i = i).unwrap(); }
            eprintln!("split: delegated={} top_nodes={} task_nodes={} total={}", n, st0.nodes, tn, st0.nodes + tn); }
        else { eprintln!("split toponly: delegated={} top_nodes={} top_fields={}", n, st0.nodes, top.len()); }
    } else if mode == "root" {
        let expect = if a.iter().any(|x| x == "bad") { "false" } else { "true" };
        let c = cert(&mut L, "CR", &out);
        writeln!(L, "-- nodes {} cert_fields {}\ntheorem root_ok : checkRoot X {} = {} := by decide +kernel", s.nodes, out.len(), c, expect).unwrap();
        if ctrl { let c1 = cert(&mut L, "CC1", &corrupt(&out)); let c2 = cert(&mut L, "CC2", &semcorrupt(&out, 0));
            writeln!(L, "theorem root_ctrl1 : checkRoot X {} = false := by decide +kernel\ntheorem root_ctrl2 : checkRoot X {} = false := by decide +kernel", c1, c2).unwrap(); }
    } else {
        let nt: usize = a[4].parse().unwrap(); let stride = (tasks.len() / nt).max(1);
        let (mut tn, mut tf) = (0u64, 0usize);
        for t in 0..nt { let i = t * stride; if i >= tasks.len() { break; }
            let (st, lo, hi) = &tasks[i]; let rec = &out[*lo..*hi];
            // count nodes of this subtree by replay
            let mut s2 = Stats::default(); let mut o2 = vec![]; let mut t2 = vec![]; node(&pr, st, &mut o2, &mut s2, &mut t2); assert!(o2 == rec);
            tn += s2.nodes; tf += rec.len();
            let args = format!("X (nat_lit {}) (nat_lit {}) (nat_lit {}) {} {}", st.d, st.sz, st.ev, hexw(&spread(&st.avail, w)), hexw(&st.unc[..]));
            let c = cert(&mut L, &format!("C{}", t), rec);
            writeln!(L, "-- task {} nodes {} work {} fields {} F uni {} top {} mwu {} supp {} cnti {} kids {} nu0 {}\ntheorem t{} : checkState {} {} = true := by decide +kernel", i, s2.nodes, s2.work, rec.len(), s2.leaves[3], s2.leaves[4], s2.leaves[5], s2.supp, s2.cnti, s2.kids, pc(&st.unc), t, args, c).unwrap();
            if ctrl && t < 2 { let c1 = cert(&mut L, &format!("D{}", t), &corrupt(rec)); let c2 = cert(&mut L, &format!("E{}", t), &semcorrupt(rec, *lo));
                writeln!(L, "theorem c{t}a : checkState {args} {c1} = false := by decide +kernel\ntheorem c{t}b : checkState {args} {c2} = false := by decide +kernel").unwrap(); }
        }
        eprintln!("emitted tasks={} nodes={} fields={}", nt, tn, tf);
    }
    writeln!(L, "\nend\nend LRSpectrumFull.EightV4.Cert{}", p).unwrap();
    std::fs::write(&outp, L).unwrap();
}
