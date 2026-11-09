// gen94: Lean generator for PINNED cover-capacity leaf certificates, m = 94 (k = 93, window [1,188], floor 1/95).
// Derived from code/dense/src/lg/main.rs (family, greedy edge choice, split style, text re-parse), changed in:
//   * the certificate has a header (# I ..., # O ..., # BUDGET b) and parts "cap e1 e2 ...";
//   * edges are LINK edges: e \ I (e = full bad set of an event-point time), hcap is  bad j \ I subset S;
//   * hcover is  Icc 1 188 \ (I u O) subset biUnion U;  hsum is  sum c + |I| < 94;
//   * the emitted module proves a leaf theorem via floor_of_pinned_cover (Delta2PinnedCover).
// Every Lean-side condition is re-evaluated in exact integer arithmetic from the EMITTED TEXT.  No floats.
//   gen94 gen CERT SUFFIX OUT.lean.unbuilt [JC]      emit + self-check
//   gen94 verify FILE.lean                           re-parse an emitted module and re-check
//   gen94 controls FILE.lean                         negative controls (must all be REJECTED)
use std::collections::{HashMap, HashSet};

const M: u64 = 94;
type Bs = Vec<u64>;
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn words() -> usize { ((2 * M + 63) / 64) as usize }
/// Lean: goodAt k x p q := decide (q <= (k+2) * min (x*p % q) (q - x*p % q)), k+2 = 95.
fn good_at(x: u128, p: u128, q: u128) -> bool { let r = x * p % q; q <= (M as u128 + 1) * r.min(q - r) }
fn mk(el: &[u32]) -> Bs { let mut b = vec![0u64; words()]; for &x in el { let i = (x - 1) as usize; b[i / 64] |= 1 << (i % 64); } b }
fn subset(a: &[u64], b: &[u64]) -> bool { a.iter().zip(b).all(|(x, y)| x & !y == 0) }
fn andnot(a: &[u64], b: &[u64]) -> Bs { a.iter().zip(b).map(|(x, y)| x & !y).collect() }
fn pop(a: &[u64]) -> u32 { a.iter().map(|x| x.count_ones()).sum() }
fn elems_of(b: &[u64]) -> Vec<u32> { let mut v = vec![]; for (wi, &x) in b.iter().enumerate() { for j in 0..64 { if x >> j & 1 == 1 { v.push((wi * 64 + j + 1) as u32); } } } v }

#[derive(Clone, PartialEq)]
struct Data { p: Vec<u64>, q: Vec<u64>, bad: Vec<Vec<u32>>, u: Vec<Vec<u32>>, c: Vec<u32>, i: Vec<u32>, o: Vec<u32> }

struct Metrics { nw: usize, t: usize, maxpart: usize, cap_subsets: u64, sumc: u64, pins: usize }

/// Every Lean-side condition, literally.
fn check_data(d: &Data) -> Result<Metrics, String> {
    let n = 2 * M; let nw = d.p.len(); let t = d.u.len();
    if d.q.len() != nw || d.bad.len() != nw { return Err("length mismatch p/q/bad".into()); }
    if d.c.len() != t { return Err("length mismatch U/c".into()); }
    if d.q.iter().any(|&q| q == 0) { return Err("hq: some q = 0".into()); }
    // pins: I subset window; I, O disjoint (O subset window as well)
    for &x in d.i.iter().chain(d.o.iter()) { if x < 1 || x as u64 > n { return Err(format!("pin {} outside window", x)); } }
    if d.i.iter().any(|x| d.o.contains(x)) { return Err("I and O intersect".into()); }
    // hbad
    for j in 0..nw {
        let b: HashSet<u32> = d.bad[j].iter().cloned().collect();
        for x in 1..=n { if !good_at(x as u128, d.p[j] as u128, d.q[j] as u128) && !b.contains(&(x as u32)) {
            return Err(format!("hbad: j={} x={} fails goodAt but not in bad", j, x)); } } }
    // hcover: Icc 1 188 \ (I u O) subset biUnion U
    let mut cov = vec![false; (n + 1) as usize];
    for u in &d.u { for &x in u { if (x as u64) <= n { cov[x as usize] = true; } } }
    for x in 1..=n { if d.i.contains(&(x as u32)) || d.o.contains(&(x as u32)) { continue; }
        if !cov[x as usize] { return Err(format!("hcover: {} uncovered", x)); } }
    // hsum: sum c + |I| < k+1 = 94
    let sumc: u64 = d.c.iter().map(|&c| c as u64).sum();
    if sumc + d.i.len() as u64 >= M { return Err(format!("hsum: sum c {} + |I| {} >= {}", sumc, d.i.len(), M)); }
    // hcap (link form): every subset T of U_i with |T| > c_i contains  bad_j \ I  for some j
    let ib = mk(&d.i);
    let linkb: Vec<Bs> = d.bad.iter().map(|b| andnot(&mk(b), &ib)).collect();
    let mut cap_subsets = 0u64; let mut maxpart = 0;
    for i in 0..t {
        let u = &d.u[i]; let nn = u.len(); maxpart = maxpart.max(nn);
        let mut ue = u.clone(); ue.sort(); ue.dedup();
        if ue.len() != nn { return Err(format!("part {} has repeated elements", i)); }
        if nn > 24 { return Err(format!("part {} too large for brute force", i)); }
        let ub = mk(u);
        let inu: Vec<usize> = (0..nw).filter(|&j| subset(&linkb[j], &ub)).collect();
        for mask in 0u32..(1u32 << nn) {
            if (mask.count_ones() as usize) <= d.c[i] as usize { continue; }
            cap_subsets += 1;
            let tel: Vec<u32> = (0..nn).filter(|&b| mask >> b & 1 == 1).map(|b| u[b]).collect();
            let tb = mk(&tel);
            if !inu.iter().any(|&j| subset(&linkb[j], &tb)) {
                return Err(format!("hcap: part {} subset {:?} (size {} > cap {}) contains no link edge", i, tel, tel.len(), d.c[i])); } } }
    Ok(Metrics { nw, t, maxpart, cap_subsets, sumc, pins: d.i.len() + d.o.len() })
}

// ---------------------------------------------------------------- parsing
fn vecs(s: &str) -> Vec<u64> { s.split(',').filter(|x| !x.trim().is_empty()).map(|x| x.trim().parse().unwrap()).collect() }
fn group_after<'a>(text: &'a str, key: &str) -> Result<&'a str, String> {
    let i = text.find(key).ok_or(format!("missing {}", key))? + key.len();
    let rest = &text[i..]; let st = rest.find('[').ok_or("no [")?;
    let mut depth = 0; let mut end = None;
    for (k, ch) in rest[st..].char_indices() { match ch { '[' => depth += 1, ']' => { depth -= 1; if depth == 0 { end = Some(st + k); break; } } _ => {} } }
    Ok(&rest[st..=end.ok_or("unbalanced")?])
}
fn nested(g: &str) -> Vec<Vec<u32>> {
    let inner = &g[1..g.len() - 1]; let mut out = vec![]; let mut cur: Option<String> = None;
    for ch in inner.chars() { match ch { '[' => cur = Some(String::new()), ']' => { let c = cur.take().unwrap();
        out.push(c.split(',').filter(|x| !x.trim().is_empty()).map(|x| x.trim().parse().unwrap()).collect()); }
        c => if let Some(cc) = cur.as_mut() { cc.push(c) } } }
    out
}
fn flat(g: &str) -> Vec<u64> { vecs(&g[1..g.len() - 1]) }
fn listlit(v: &[u32]) -> String { format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")) }
fn ranges(n: usize, sz: usize) -> Vec<(usize, usize)> { let mut v = vec![]; let mut a = 0; while a < n { let b = (a + sz).min(n); v.push((a, b)); a = b; } v }
fn num_after(text: &str, key: &str) -> u64 {
    let i = text.find(key).unwrap_or_else(|| panic!("missing {}", key)) + key.len();
    text[i..].chars().take_while(|c| c.is_ascii_digit()).collect::<String>().parse().unwrap()
}

fn parse_text(text: &str) -> Result<Data, String> {
    if text.contains("sorry") || text.contains("native_decide") || text.contains("axiom ") { return Err("sorry/native_decide/axiom present".into()); }
    let c = |key: &str| -> Result<&str, String> { group_after(text, key) };
    let d = Data { p: flat(c("def PL : List ℕ := ")?), q: flat(c("def QL : List ℕ := ")?), bad: nested(c("def BL : List (List ℕ) := ")?),
        u: nested(c("def UL : List (List ℕ) := ")?), c: flat(c("def CL : List ℕ := ")?).into_iter().map(|x| x as u32).collect(),
        i: flat(c("def IL : List ℕ := ")?).into_iter().map(|x| x as u32).collect(), o: flat(c("def OL : List ℕ := ")?).into_iter().map(|x| x as u32).collect() };
    let (nn, t) = (d.p.len(), d.u.len());
    if d.q.len() != nn || d.bad.len() != nn || d.c.len() != t { return Err("data lengths do not match".into()); }
    // statement skeleton: exactly the expected declaration texts for these N and t
    for key in [format!("def pf (j : Fin {})", nn), format!("def qf (j : Fin {})", nn), format!("def bf (j : Fin {})", nn), format!("def Uf (i : Fin {})", t), format!("def cf (i : Fin {})", t),
        "def If : Finset ℕ := IL.toFinset".to_string(), "def Of : Finset ℕ := OL.toFinset".to_string(),
        format!("theorem hq_all : ∀ j : Fin {}, 0 < qf j", nn),
        format!("theorem hsum_all : ∑ i : Fin {t}, cf i + If.card < 93 + 1", t = t),
        "theorem hcover_all : Finset.Icc 1 (2 * (93 + 1)) \\ (If ∪ Of) ⊆ Finset.univ.biUnion Uf".to_string(),
        format!("theorem hbad_all : ∀ j : Fin {nb}, ∀ x, 1 ≤ x → x ≤ 2 * (93 + 1) → goodAt 93 x (pf j) (qf j) = false → x ∈ bf j", nb = nn),
        format!("theorem hcap_all : ∀ i : Fin {t}, ∀ S ∈ (Uf i).powerset, cf i < S.card → ∃ j : Fin {nb}, bf j \\ If ⊆ S", t = t, nb = nn),
        "floor_of_pinned_cover (k := 93)".to_string(), format!("(t := {})", t), format!("(N := {})", nn), "1 / (95 : ℝ) ≤ ML v".to_string(),
        "(v : Fin 94 → ℤ)".to_string(), "Finset.Icc 1 188".to_string(), "norm_num at h".to_string()] {
        if !text.contains(&key) { return Err(format!("missing declaration text: {}", key)); } }
    // chunk lemmas partition [0,N) and [0,t), and the assembly uses the same bounds
    let chunks = |prefix: &str, dom: usize, var: &str| -> Result<Vec<(usize, usize)>, String> {
        let mut v = vec![];
        for line in text.lines().filter(|l| l.starts_with(&format!("theorem {}_c", prefix))) {
            let head = format!("Fin {}, ", dom); let hi = line.find(&head).ok_or("chunk dom")? + head.len();
            let a: usize = line[hi..].chars().take_while(|c| c.is_ascii_digit()).collect::<String>().parse().map_err(|_| "chunk a")?;
            let key = format!("{}.val < ", var); let ki = line.find(&key).ok_or("chunk b")? + key.len();
            let b: usize = line[ki..].chars().take_while(|c| c.is_ascii_digit()).collect::<String>().parse().map_err(|_| "chunk b")?;
            v.push((a, b)); }
        if v.is_empty() { return Err(format!("no {} chunks", prefix)); }
        let mut at = 0; for &(a, b) in &v { if a != at || b <= a { return Err(format!("{} chunks do not partition: {:?}", prefix, v)); } at = b; }
        if at != dom { return Err(format!("{} chunks end at {} != {}", prefix, at, dom)); }
        Ok(v) };
    let hb = chunks("hbad", nn, "j")?; let hc = chunks("hcap", t, "i")?;
    for (name, v, var) in [("hbad_all", &hb, "j"), ("hcap_all", &hc, "i")] {
        let ti = text.find(&format!("theorem {} :", name)).ok_or("assembly")?; let body = &text[ti..];
        let end = body.find("\n\n").unwrap_or(body.len()); let body = &body[..end];
        for (ci, &(_, b)) in v.iter().enumerate() {
            if ci + 1 < v.len() { if !body.contains(&format!("by_cases c{ci} : {var}.val < {b}")) { return Err(format!("{}: assembly bound {} missing", name, b)); } } } }
    Ok(d)
}

// ---------------------------------------------------------------- generation
struct Cert { i: Vec<u32>, o: Vec<u32>, budget: Option<u32>, parts: Vec<(Vec<u32>, u32)> }
fn parse_cert(path: &str) -> Result<Cert, String> {
    let txt = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let mut c = Cert { i: vec![], o: vec![], budget: None, parts: vec![] };
    for (ln, line) in txt.lines().enumerate() {
        let tok: Vec<&str> = line.split_whitespace().collect(); if tok.is_empty() { continue; }
        if tok[0] == "#" {
            let nums = |from: usize| -> Result<Vec<u32>, String> { tok[from..].iter().map(|t| t.parse().map_err(|_| format!("line {}", ln + 1))).collect() };
            match tok.get(1) { Some(&"I") => c.i = nums(2)?, Some(&"O") => c.o = nums(2)?, Some(&"BUDGET") => c.budget = Some(nums(2)?[0]), _ => {} }
            continue; }
        if tok[0].starts_with('#') { continue; }
        let cap: u32 = tok[0].parse().map_err(|_| format!("line {}", ln + 1))?;
        let mut el: Vec<u32> = tok[1..].iter().map(|t| t.parse().map_err(|_| format!("line {}", ln + 1))).collect::<Result<_, _>>()?;
        el.sort();
        if el.windows(2).any(|a| a[0] == a[1]) || el.iter().any(|&x| x < 1 || x as u64 > 2 * M) { return Err(format!("line {}: bad element list", ln + 1)); }
        c.parts.push((el, cap));
    }
    Ok(c)
}

/// bad sets at all event-point times (plus t=0), smallest (q,p) per distinct set.  Same as code/dense/src/lg family().
fn family() -> HashMap<Bs, (u64, u64)> {
    let mut times: HashSet<(u64, u64)> = HashSet::new(); times.insert((0, 1));
    for x in 1..=2 * M { let d = x * (M + 1);
        for a in 0..=x { for s in [-1i64, 1] { let nu = (a * (M + 1)) as i64 + s; if nu < 0 || nu as u64 > d { continue; }
            let nu = nu as u64; let g = gcd(nu, d); times.insert((nu / g, d / g)); } } }
    let mut fam: HashMap<Bs, (u64, u64)> = HashMap::new();
    for &(p, q) in &times {
        let mut b = vec![0u64; words()];
        for x in 1..=2 * M { if !good_at(x as u128, p as u128, q as u128) { let i = (x - 1) as usize; b[i / 64] |= 1 << (i % 64); } }
        if pop(&b) == 0 { continue; }
        let e = fam.entry(b).or_insert((q, p)); if (q, p) < *e { *e = (q, p); }
    }
    fam
}
fn combos(n: usize, r: usize, mut f: impl FnMut(&[usize])) {
    if r > n { return; } let mut idx: Vec<usize> = (0..r).collect();
    loop { f(&idx); let mut k = r; while k > 0 && idx[k - 1] == n - r + k - 1 { k -= 1; } if k == 0 { break; } idx[k - 1] += 1; for j in k..r { idx[j] = idx[j - 1] + 1; } }
}

fn build(cert: &Cert) -> Result<Data, String> {
    let fam = family();
    let ib = mk(&cert.i);
    let pb: Vec<Bs> = cert.parts.iter().map(|(e, _)| mk(e)).collect();
    // distinct link sets e \ I that lie inside some part; per link set keep the full set with the smallest (q,p)
    let mut best: HashMap<Bs, (Bs, (u64, u64))> = HashMap::new();
    for (e, tm) in fam.into_iter() {
        let link = andnot(&e, &ib);
        if !pb.iter().any(|u| subset(&link, u)) { continue; }
        let ent = best.entry(link).or_insert((e.clone(), tm));
        if (tm.0, tm.1) < (ent.1 .0, ent.1 .1) { *ent = (e, tm); }
    }
    let mut cand: Vec<(Bs, Bs, (u64, u64))> = best.into_iter().map(|(l, (e, tm))| (l, e, tm)).collect();
    cand.sort_by(|a, b| (pop(&a.0), &a.0).cmp(&(pop(&b.0), &b.0)));
    let mut edges: Vec<(Bs, Bs, (u64, u64))> = vec![];   // (link, full, (q,p)) inclusion-minimal in the link
    for c in cand { if !edges.iter().any(|(l, _, _)| subset(l, &c.0)) { edges.push(c); } }
    let mut chosen: Vec<usize> = vec![];
    for (i, (el, cap)) in cert.parts.iter().enumerate() {
        let r = *cap as usize + 1; let n = el.len(); if r > n { continue; }
        let mut nsub = 1f64; for j in 0..r { nsub = nsub * (n - j) as f64 / (j + 1) as f64; }
        if nsub > 3e6 { return Err(format!("part {} too large ({} subsets)", i, nsub)); }
        let ein: Vec<usize> = (0..edges.len()).filter(|&e| subset(&edges[e].0, &pb[i])).collect();
        let mut subs: Vec<Bs> = vec![];
        combos(n, r, |ix| subs.push(mk(&ix.iter().map(|&j| el[j]).collect::<Vec<_>>())));
        let mut unc: Vec<bool> = subs.iter().map(|s| !chosen.iter().any(|&e| subset(&edges[e].0, s))).collect();
        for si in 0..subs.len() {
            if !unc[si] { continue; }
            let mut bestg: Option<(usize, usize)> = None;
            for &e in &ein { if !subset(&edges[e].0, &subs[si]) { continue; }
                let gain = (0..subs.len()).filter(|&s2| unc[s2] && subset(&edges[e].0, &subs[s2])).count();
                if bestg.map_or(true, |(_, g)| gain > g) { bestg = Some((e, gain)); } }
            let (e, _) = bestg.ok_or(format!("part {} (cap {}): subset {:?} contains no link edge: capacity too small", i, cap, elems_of(&subs[si])))?;
            chosen.push(e);
            for s2 in 0..subs.len() { if unc[s2] && subset(&edges[e].0, &subs[s2]) { unc[s2] = false; } }
        }
    }
    Ok(Data { p: chosen.iter().map(|&e| edges[e].2 .1).collect(), q: chosen.iter().map(|&e| edges[e].2 .0).collect(),
        bad: chosen.iter().map(|&e| elems_of(&edges[e].1)).collect(), u: cert.parts.iter().map(|(e, _)| e.clone()).collect(),
        c: cert.parts.iter().map(|(_, c)| *c).collect(), i: cert.i.clone(), o: cert.o.clone() })
}

fn emit(d: &Data, suffix: &str, source: &str, jc: usize, leafname: &str) -> String {
    let tac = "decide +kernel"; let k = M - 1; let nb = d.p.len(); let t = d.u.len(); let sum: u32 = d.c.iter().sum();
    let j = |v: &Vec<u64>| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
    let bs = d.bad.iter().map(|b| listlit(b)).collect::<Vec<_>>().join(",");
    let us = d.u.iter().map(|b| listlit(b)).collect::<Vec<_>>().join(",");
    let cs = d.c.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(",");
    let hbr = ranges(nb, jc); let hcr = ranges(t, 1);
    let mut s = String::new();
    s += &format!(r#"/-
# Pinned cover-capacity leaf certificate, split style (m = 94, leaf {leafname})

Generated by `code/dense/src/gen94/main.rs` (command gen) from {source}.
Pins: I = {il:?} (not speeds), O = {ol:?} (speeds).  Link-form capacities, budget `sum c + |I| < 94`
({sum} + {ni} < 94).  Data are plain `List` literals read through `List.getD`; every large check is a
separate lemma closed by `{tac}` on a small range of indices (hbad: {jc} witnesses per lemma, hcap: one part
per lemma).  Module name `Delta2CoverRange{suffix}`; leaf theorem `{leafname}`.
-/
import LRSpectrumFull.Delta2PinnedCover

namespace LRSpectrumFull

open Finset

namespace CR{suffix}

def PL : List ℕ := [{ps}]
def QL : List ℕ := [{qs}]
def BL : List (List ℕ) := [{bs}]
def UL : List (List ℕ) := [{us}]
def CL : List ℕ := [{cs}]
def IL : List ℕ := {ils}
def OL : List ℕ := {ols}

def pf (j : Fin {nb}) : ℕ := PL.getD j.val 0
def qf (j : Fin {nb}) : ℕ := QL.getD j.val 0
def bf (j : Fin {nb}) : Finset ℕ := (BL.getD j.val []).toFinset
def Uf (i : Fin {t}) : Finset ℕ := (UL.getD i.val []).toFinset
def cf (i : Fin {t}) : ℕ := CL.getD i.val 0
def If : Finset ℕ := IL.toFinset
def Of : Finset ℕ := OL.toFinset

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem hq_all : ∀ j : Fin {nb}, 0 < qf j := by
  {tac}

"#, leafname = leafname, il = d.i, ol = d.o, sum = sum, ni = d.i.len(), tac = tac, jc = jc, suffix = suffix, source = source,
        ps = j(&d.p), qs = j(&d.q), bs = bs, us = us, cs = cs, ils = listlit(&d.i), ols = listlit(&d.o), nb = nb, t = t);
    for (ci, &(a, b)) in hbr.iter().enumerate() {
        s += &format!("set_option maxHeartbeats 1000000 in\nset_option maxRecDepth 100000 in\ntheorem hbad_c{ci} : ∀ j : Fin {nb}, {a} ≤ j.val → j.val < {b} → ∀ x ∈ Finset.Icc 1 (2 * ({k} + 1)), goodAt {k} x (pf j) (qf j) = false → x ∈ bf j := by\n  {tac}\n\n", ci = ci, nb = nb, a = a, b = b, k = k, tac = tac);
    }
    s += &format!("theorem hbad_all : ∀ j : Fin {nb}, ∀ x, 1 ≤ x → x ≤ 2 * ({k} + 1) → goodAt {k} x (pf j) (qf j) = false → x ∈ bf j := by\n  intro j x h1 h2 hg\n  have hx : x ∈ Finset.Icc 1 (2 * ({k} + 1)) := Finset.mem_Icc.mpr ⟨h1, h2⟩\n", nb = nb, k = k);
    for (ci, &(_, b)) in hbr.iter().enumerate() {
        if ci + 1 < hbr.len() { s += &format!("  by_cases c{ci} : j.val < {b}\n  · exact hbad_c{ci} j (by omega) c{ci} x hx hg\n", ci = ci, b = b); }
        else { s += &format!("  exact hbad_c{ci} j (by omega) (by omega) x hx hg\n\n", ci = ci); } }
    s += &format!("set_option maxHeartbeats 1000000 in\nset_option maxRecDepth 100000 in\ntheorem hcover_all : Finset.Icc 1 (2 * ({k} + 1)) \\ (If ∪ Of) ⊆ Finset.univ.biUnion Uf := by\n  {tac}\n\n", k = k, tac = tac);
    s += &format!("set_option maxHeartbeats 1000000 in\nset_option maxRecDepth 100000 in\ntheorem hsum_all : ∑ i : Fin {t}, cf i + If.card < {k} + 1 := by\n  {tac}\n\n", t = t, k = k, tac = tac);
    for (ci, &(a, b)) in hcr.iter().enumerate() {
        s += &format!("set_option maxHeartbeats 1000000 in\nset_option maxRecDepth 100000 in\ntheorem hcap_c{ci} : ∀ i : Fin {t}, {a} ≤ i.val → i.val < {b} → ∀ S ∈ (Uf i).powerset, cf i < S.card → ∃ j : Fin {nb}, bf j \\ If ⊆ S := by\n  {tac}\n\n", ci = ci, t = t, a = a, b = b, nb = nb, tac = tac);
    }
    s += &format!("theorem hcap_all : ∀ i : Fin {t}, ∀ S ∈ (Uf i).powerset, cf i < S.card → ∃ j : Fin {nb}, bf j \\ If ⊆ S := by\n  intro i S hS hc\n  have hi : i.val < {t} := i.isLt\n", t = t, nb = nb);
    for (ci, &(_, b)) in hcr.iter().enumerate() {
        if ci + 1 < hcr.len() { s += &format!("  by_cases c{ci} : i.val < {b}\n  · exact hcap_c{ci} i (by omega) c{ci} S hS hc\n", ci = ci, b = b); }
        else { s += &format!("  exact hcap_c{ci} i (by omega) (by omega) S hS hc\n\n", ci = ci); } }
    s += &format!("theorem hIsub_all : If ⊆ Finset.Icc 1 (2 * ({k} + 1)) := by\n  {tac}\n\nend CR{suffix}\n\n", k = k, tac = tac, suffix = suffix);
    // leaf theorem: hypotheses are the pins as statements about v
    let mut hyps = String::new();
    for (n, x) in d.i.iter().enumerate() { hyps += &format!("\n    (hI{n} : ∀ i, (v i).toNat ≠ {x})", n = n, x = x); }
    for (n, x) in d.o.iter().enumerate() { hyps += &format!("\n    (hO{n} : ∃ i, (v i).toNat = {x})", n = n, x = x); }
    // hI : ∀ x ∈ If, ∀ i, (v i).toNat ≠ x     (|I| <= 1)
    if d.i.len() > 1 { panic!("gen94 supports |I| <= 1"); }
    let hi_final = if d.i.is_empty() { format!("(by intro x hx; simp [CR{suffix}.If, CR{suffix}.IL] at hx)", suffix = suffix) }
        else { format!("(by intro x hx; have hx' : x = {x} := (by simpa [CR{suffix}.If, CR{suffix}.IL] using hx); subst hx'; exact hI0)", x = d.i[0], suffix = suffix) };
    // hO : ∀ x ∈ Of, ∃ i, (v i).toNat = x     (|O| <= 2)
    if d.o.len() > 2 { panic!("gen94 supports |O| <= 2"); }
    let ho_proof = if d.o.is_empty() { format!("(by intro x hx; simp [CR{suffix}.Of, CR{suffix}.OL] at hx)", suffix = suffix) }
        else if d.o.len() == 1 { format!("(by intro x hx; have hx' : x = {x} := (by simpa [CR{suffix}.Of, CR{suffix}.OL] using hx); subst hx'; exact hO0)", x = d.o[0], suffix = suffix) }
        else { format!("(by intro x hx; have hx' : x = {x} ∨ x = {y} := (by simpa [CR{suffix}.Of, CR{suffix}.OL] using hx); rcases hx' with rfl | rfl <;> assumption)", x = d.o[0], y = d.o[1], suffix = suffix) };
    s += &format!(r#"set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **Dense window at m = 94, leaf `{leafname}`**: if the speeds avoid `I = {il:?}` and contain `O = {ol:?}`,
the floor `1/95` holds.  Cover-capacity certificate: {t} parts, capacities summing to {sum}, |I| = {ni},
{nb} witness times (split style). -/
theorem {leafname} (v : Fin 94 → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 188){hyps} :
    1 / (95 : ℝ) ≤ ML v := by
  have h := floor_of_pinned_cover (k := 93) (t := {t}) (N := {nb}) v hv hinj
    (by simpa using hden) CR{suffix}.pf CR{suffix}.qf CR{suffix}.hq_all CR{suffix}.bf CR{suffix}.hbad_all
    CR{suffix}.If CR{suffix}.Of CR{suffix}.hIsub_all
    {hip}
    {hop}
    CR{suffix}.Uf CR{suffix}.cf CR{suffix}.hcover_all CR{suffix}.hcap_all CR{suffix}.hsum_all
  norm_num at h
  exact h

end LRSpectrumFull
"#, leafname = leafname, il = d.i, ol = d.o, t = t, sum = sum, ni = d.i.len(), nb = nb, hyps = hyps, suffix = suffix, hip = hi_final, hop = ho_proof);
    s
}

fn report(tag: &str, mt: &Metrics, bytes: usize) {
    println!("{}: N(witness times)={} t(parts)={} maxpart={} cap-subsets-checked={} sum_c={} pins={} bytes={}", tag, mt.nw, mt.t, mt.maxpart, mt.cap_subsets, mt.sumc, mt.pins, bytes);
}

fn controls(d: &Data) {
    let ok = std::cell::Cell::new(0); let bad = std::cell::Cell::new(0);
    let run = |name: &str, dd: Data, expect_reject: bool| {
        let r = check_data(&dd);
        let rejected = r.is_err();
        let verdict = if rejected == expect_reject { ok.set(ok.get() + 1); "as expected" } else { bad.set(bad.get() + 1); "UNEXPECTED" };
        println!("  control {:44} -> {} ({})", name, if rejected { "REJECT" } else { "ACCEPT" }, verdict);
    };
    // 1. lower each capacity by one: every tight part must be rejected
    let mut tight_rej = 0; let mut nontight = 0;
    for i in 0..d.c.len() { if d.c[i] == 0 { continue; }
        let mut dd = d.clone(); dd.c[i] -= 1;
        match check_data(&dd) { Err(_) => tight_rej += 1, Ok(_) => nontight += 1 } }
    println!("  cap-1 mutants: rejected {} accepted {} (accepted = part not tight)", tight_rej, nontight);
    if nontight == 0 { ok.set(ok.get() + 1) } else { bad.set(bad.get() + 1) }
    // 2. drop one element from a part holding a uniquely covered element
    let mut cnt: HashMap<u32, usize> = HashMap::new(); for u in &d.u { for &x in u { *cnt.entry(x).or_insert(0) += 1; } }
    let mut dd = d.clone(); let mut done = false;
    'o: for i in 0..dd.u.len() { for k in 0..dd.u[i].len() { let x = dd.u[i][k]; if cnt[&x] == 1 { dd.u[i].remove(k); done = true; break 'o; } } }
    if done { run("remove a uniquely covered element", dd, true); }
    // 3. raise the pin count by one (budget) when the budget is exactly full
    let mut dd = d.clone(); dd.i.push(1); run("extra pin (budget off by one)", dd, true);
    // 4. pretend one more unit of capacity is needed: sum c + 1 (budget)
    let mut dd = d.clone(); if let Some(c) = dd.c.iter_mut().find(|c| **c > 0) { *c += 1; } run("one capacity raised by 1 (budget)", dd, true);
    // 5. witness with wrong q (hbad): change one q
    let mut dd = d.clone(); dd.q[0] += 1; run("wrong witness denominator", dd, true);
    // 6. remove O element's exclusion: O pin turned into plain nothing => uncovered
    if !d.o.is_empty() { let mut dd = d.clone(); dd.o.remove(0); run("drop an O pin (element then needs cover)", dd, true); }
    // 7. positive: the unchanged data
    run("unchanged data", d.clone(), false);
    println!("CONTROLS: {} as expected, {} unexpected", ok.get(), bad.get());
    if bad.get() > 0 { std::process::exit(9); }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("gen") => {
            let cert = parse_cert(&a[2]).unwrap_or_else(|e| { eprintln!("parse: {}", e); std::process::exit(2) });
            let suffix = a[3].clone(); let out = a[4].clone();
            let jc: usize = a.get(5).and_then(|x| x.parse().ok()).unwrap_or(4);
            let sumc: u32 = cert.parts.iter().map(|p| p.1).sum();
            if let Some(b) = cert.budget { println!("header: I={:?} O={:?} BUDGET={} parts={} sum_cap={} sum_cap+|I|={}", cert.i, cert.o, b, cert.parts.len(), sumc, sumc as usize + cert.i.len()); }
            let d = build(&cert).unwrap_or_else(|e| { eprintln!("build: {}", e); std::process::exit(3) });
            check_data(&d).unwrap_or_else(|e| { eprintln!("in-memory check: {}", e); std::process::exit(4) });
            let cname = std::path::Path::new(&a[2]).file_name().unwrap().to_string_lossy().to_string();
            let leafname = format!("leaf94_{}", suffix.trim_start_matches("S94"));
            let text = emit(&d, &suffix, &format!("`data/dense/m94_lean/certs/{}`", cname), jc, &leafname);
            let tmp = format!("{}.tmp", out);
            std::fs::write(&tmp, &text).unwrap(); std::fs::rename(&tmp, &out).unwrap();
            let back = std::fs::read_to_string(&out).unwrap();
            let d2 = parse_text(&back).unwrap_or_else(|e| { eprintln!("reparse: {}", e); std::process::exit(5) });
            if d2 != d { eprintln!("reparsed data differ from source data"); std::process::exit(7) }
            let mt = check_data(&d2).unwrap_or_else(|e| { eprintln!("text check: {}", e); std::process::exit(6) });
            println!("SELF-CHECK OK (from emitted text)"); report("gen94", &mt, back.len());
        }
        Some("verify") => { let t = std::fs::read_to_string(&a[2]).unwrap(); let d = parse_text(&t).unwrap_or_else(|e| { println!("PARSE FAIL: {}", e); std::process::exit(5) });
            match check_data(&d) { Ok(mt) => { println!("VERIFY OK {}", a[2]); report("gen94", &mt, t.len()) } Err(e) => { println!("VERIFY FAIL {}: {}", a[2], e); std::process::exit(6) } } }
        Some("controls") => { let t = std::fs::read_to_string(&a[2]).unwrap(); let d = parse_text(&t).unwrap(); check_data(&d).expect("base must pass"); controls(&d) }
        _ => eprintln!("usage: gen94 gen CERT SUFFIX OUT [JC] | verify F | controls F"),
    }
}
