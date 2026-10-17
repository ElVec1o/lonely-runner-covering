// lg: Lean generator for cover-capacity certificates (g1 list format, arbitrary width bitsets, any m).
// Emits a module in the style of Delta2CoverRangeAC.lean (theorem dense_floor_mM via floor_of_cover_capacity),
// then re-reads the emitted TEXT, parses the data vectors back and re-evaluates every Lean-side
// condition (hq, hbad, hcover, hcap, hsum) with exact integer arithmetic.  No floats.
//
// Commands (single thread; run under nice -n 10):
//   lg gen M CERT.sol SUFFIX OUT.lean.unbuilt   emit + self-check (module name Delta2CoverRange<SUFFIX>)
//   lg verify FILE.lean                          parse an existing/emitted module text and re-evaluate its conditions
//   lg controls FILE.lean                        negative controls (mutations of the parsed data) on a module
//   lg fit FILE.lean...                          cost metrics of modules + least-squares fit against measured build times
use std::collections::{HashMap, HashSet};

type Bs = Vec<u64>;
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn words(m: u64) -> usize { ((2 * m + 63) / 64) as usize }
/// Lean: goodAt k x p q := decide (q <= (k+2) * min (x*p % q) (q - x*p % q)), k+2 = m+1.
fn good_at(k2: u128, x: u128, p: u128, q: u128) -> bool { let r = x * p % q; q <= k2 * r.min(q - r) }
fn mk(el: &[u32], w: usize) -> Bs { let mut b = vec![0u64; w]; for &x in el { let i = (x - 1) as usize; b[i / 64] |= 1 << (i % 64); } b }
fn subset(a: &[u64], b: &[u64]) -> bool { a.iter().zip(b).all(|(x, y)| x & !y == 0) }
fn pop(a: &[u64]) -> u32 { a.iter().map(|x| x.count_ones()).sum() }

// ---------------------------------------------------------------- data
#[derive(Clone)]
struct Data { m: u64, t: usize, p: Vec<u64>, q: Vec<u64>, bad: Vec<Vec<u32>>, u: Vec<Vec<u32>>, c: Vec<u32> }

struct Metrics { h_goals: u64, cap_subsets: u64, cap_work: u64, cover_work: u64, np: usize, nw: usize, maxpart: usize, bytes: usize }

/// Every Lean-side condition, literally.  Returns metrics or the first failure.
fn check_data(d: &Data) -> Result<Metrics, String> {
    let m = d.m; let n = 2 * m; let k2 = (m + 1) as u128; let w = words(m);
    let nw = d.p.len();
    if d.q.len() != nw || d.bad.len() != nw { return Err("length mismatch p/q/bad".into()); }
    if d.u.len() != d.t || d.c.len() != d.t { return Err("length mismatch U/c".into()); }
    // hq
    if d.q.iter().any(|&q| q == 0) { return Err("hq: some q = 0".into()); }
    // hbad
    for j in 0..nw {
        let b: HashSet<u32> = d.bad[j].iter().cloned().collect();
        for x in 1..=n {
            if !good_at(k2, x as u128, d.p[j] as u128, d.q[j] as u128) && !b.contains(&(x as u32)) {
                return Err(format!("hbad: j={} x={} fails goodAt but not in bad", j, x)); } } }
    // hcover
    let mut cov = vec![false; (n + 1) as usize];
    for u in &d.u { for &x in u { if (x as u64) <= n { cov[x as usize] = true; } } }
    for x in 1..=n { if !cov[x as usize] { return Err(format!("hcover: {} uncovered", x)); } }
    // hsum
    let sum: u64 = d.c.iter().map(|&c| c as u64).sum();
    if sum >= m { return Err(format!("hsum: sum c = {} >= m = {}", sum, m)); }
    // hcap: every subset T of U_i with |T| > c_i contains some bad j (all subsets, as Lean's powerset)
    let badb: Vec<Bs> = d.bad.iter().map(|b| mk(b, w)).collect();
    let mut cap_subsets = 0u64; let mut maxpart = 0;
    for i in 0..d.t {
        let u = &d.u[i]; let nn = u.len(); maxpart = maxpart.max(nn);
        let mut ue = u.clone(); ue.sort(); ue.dedup();
        if ue.len() != nn { return Err(format!("part {} has repeated elements", i)); }
        if nn > 24 { return Err(format!("part {} too large for brute force", i)); }
        let inu: Vec<usize> = (0..nw).filter(|&j| subset(&badb[j], &mk(u, w))).collect();
        for mask in 0u32..(1u32 << nn) {
            if (mask.count_ones() as usize) <= d.c[i] as usize { continue; }
            cap_subsets += 1;
            let tel: Vec<u32> = (0..nn).filter(|&b| mask >> b & 1 == 1).map(|b| u[b]).collect();
            let tb = mk(&tel, w);
            if !inu.iter().any(|&j| subset(&badb[j], &tb)) {
                return Err(format!("hcap: part {} subset {:?} (size {} > cap {}) contains no bad set", i, tel, tel.len(), d.c[i])); } } }
    Ok(Metrics { h_goals: n * nw as u64, cap_subsets, cap_work: cap_subsets * nw as u64, cover_work: n * d.t as u64, np: d.t, nw, maxpart, bytes: 0 })
}

// ---------------------------------------------------------------- text <-> data
fn vecs(s: &str) -> Vec<u64> { s.split(',').filter(|x| !x.trim().is_empty()).map(|x| x.trim().parse().unwrap()).collect() }
fn sets(s: &str) -> Vec<Vec<u32>> {
    let mut out = vec![]; let mut cur: Option<String> = None;
    for ch in s.chars() { match ch { '{' => cur = Some(String::new()), '}' => { let c = cur.take().unwrap();
        out.push(c.split(',').filter(|x| !x.trim().is_empty()).map(|x| x.trim().parse().unwrap()).collect()); }
        c => if let Some(cc) = cur.as_mut() { cc.push(c) } } }
    out
}
fn num_after(text: &str, key: &str) -> u64 { let i = text.find(key).unwrap_or_else(|| panic!("missing {}", key)) + key.len();
    text[i..].chars().take_while(|c| c.is_ascii_digit()).collect::<String>().parse().unwrap() }
fn parse_text(text: &str) -> Result<Data, String> {
    if text.contains("def PL : List") { return parse_text2(text); }
    let ti = text.find("theorem dense_floor_m").ok_or("no theorem")?;
    let body = &text[ti..];
    let m = num_after(body, "theorem dense_floor_m");
    let k = num_after(body, "(k := "); let t = num_after(body, "(t := ") as usize; let nn = num_after(body, "(N := ") as usize;
    if k + 1 != m { return Err("k+1 != m".into()); }
    if num_after(body, "(v : Fin ") != m { return Err("Fin size != m".into()); }
    if num_after(body, "Finset.Icc 1 ") != 2 * m { return Err("hden bound != 2m".into()); }
    if num_after(body, "1 / (") != m + 1 { return Err("floor 1/(m+1) mismatch".into()); }
    let hi = body.find("(by simpa using hden)").ok_or("no hden")?;
    let rest = &body[hi..];
    let mut groups: Vec<String> = vec![]; let b: Vec<char> = rest.chars().collect(); let mut i = 0;
    while i + 1 < b.len() { if b[i] == '!' && b[i + 1] == '[' { let mut j = i + 2; while b[j] != ']' { j += 1; } groups.push(b[i + 2..j].iter().collect()); i = j; } i += 1; }
    if groups.len() != 5 { return Err(format!("expected 5 vectors, found {}", groups.len())); }
    let d = Data { m, t, p: vecs(&groups[0]), q: vecs(&groups[1]), bad: sets(&groups[2]), u: sets(&groups[3]), c: vecs(&groups[4]).into_iter().map(|x| x as u32).collect() };
    if d.p.len() != nn || d.t != d.u.len() { return Err("N or t does not match vector lengths".into()); }
    // tactic skeleton present exactly as in the m=62 module
    for s in ["(by intro j x h1 h2; interval_cases x <;> fin_cases j <;> decide)", "(by decide) (by decide) (by decide)", "norm_num at h", "exact h"] {
        if !body.contains(s) { return Err(format!("missing skeleton line {}", s)); } }
    if body.contains("sorry") || body.contains("native_decide") { return Err("sorry/native_decide present".into()); }
    Ok(d)
}

// ---------------------------------------------------------------- generation
fn parse_sol(path: &str, m: u64) -> Result<Vec<(Vec<u32>, u32)>, String> {
    let txt = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let mut parts = vec![];
    for (ln, line) in txt.lines().enumerate() {
        let tok: Vec<&str> = line.split_whitespace().collect(); if tok.is_empty() { continue; }
        let cap: u32 = tok[0].parse().map_err(|_| format!("line {}", ln + 1))?;
        let mut el: Vec<u32> = tok[1..].iter().map(|t| t.parse().map_err(|_| format!("line {}", ln + 1))).collect::<Result<_, _>>()?;
        el.sort();
        if el.windows(2).any(|a| a[0] == a[1]) || el.iter().any(|&x| x < 1 || x as u64 > 2 * m) { return Err(format!("line {}: bad element list", ln + 1)); }
        parts.push((el, cap));
    }
    Ok(parts)
}

/// bad sets at all breakpoint times (plus t=0), smallest (q,p) per distinct set.
fn family(m: u64) -> HashMap<Bs, (u64, u64)> {
    let w = words(m); let k2 = (m + 1) as u128;
    let mut times: HashSet<(u64, u64)> = HashSet::new(); times.insert((0, 1));
    for x in 1..=2 * m { let d = x * (m + 1);
        for a in 0..=x { for s in [-1i64, 1] { let nu = (a * (m + 1)) as i64 + s; if nu < 0 || nu as u64 > d { continue; }
            let nu = nu as u64; let g = gcd(nu, d); times.insert((nu / g, d / g)); } } }
    let mut fam: HashMap<Bs, (u64, u64)> = HashMap::new();
    for &(p, q) in &times {
        let mut b = vec![0u64; w];
        for x in 1..=2 * m { if !good_at(k2, x as u128, p as u128, q as u128) { let i = (x - 1) as usize; b[i / 64] |= 1 << (i % 64); } }
        if pop(&b) == 0 { continue; }
        let e = fam.entry(b).or_insert((q, p)); if (q, p) < *e { *e = (q, p); }
    }
    fam
}
fn elems_of(b: &[u64]) -> Vec<u32> { let mut v = vec![]; for (wi, &x) in b.iter().enumerate() { for j in 0..64 { if x >> j & 1 == 1 { v.push((wi * 64 + j + 1) as u32); } } } v }

fn combos(n: usize, r: usize, mut f: impl FnMut(&[usize])) {
    if r > n { return; } let mut idx: Vec<usize> = (0..r).collect();
    loop { f(&idx); let mut k = r; while k > 0 && idx[k - 1] == n - r + k - 1 { k -= 1; } if k == 0 { break; } idx[k - 1] += 1; for j in k..r { idx[j] = idx[j - 1] + 1; } }
}

fn build(m: u64, parts: &[(Vec<u32>, u32)]) -> Result<Data, String> {
    let w = words(m);
    let fam = family(m);
    let pb: Vec<Bs> = parts.iter().map(|(e, _)| mk(e, w)).collect();
    // edges inside some part, inclusion-minimal
    let mut cand: Vec<(Bs, (u64, u64))> = fam.into_iter().filter(|(b, _)| pb.iter().any(|u| subset(b, u))).collect();
    cand.sort_by(|a, b| (pop(&a.0), &a.0).cmp(&(pop(&b.0), &b.0)));
    let mut edges: Vec<(Bs, (u64, u64))> = vec![];
    for (b, t) in cand { if !edges.iter().any(|(e, _)| subset(e, &b)) { edges.push((b, t)); } }
    let mut chosen: Vec<usize> = vec![]; let mut inch = vec![false; edges.len()];
    for (i, (el, cap)) in parts.iter().enumerate() {
        let r = *cap as usize + 1; let n = el.len(); if r > n { continue; }
        let mut nsub = 1f64; for j in 0..r { nsub = nsub * (n - j) as f64 / (j + 1) as f64; }
        if nsub > 3e6 { return Err(format!("part {} too large ({} subsets)", i, nsub)); }
        let ein: Vec<usize> = (0..edges.len()).filter(|&e| subset(&edges[e].0, &pb[i])).collect();
        let mut subs: Vec<Bs> = vec![];
        combos(n, r, |ix| subs.push(mk(&ix.iter().map(|&j| el[j]).collect::<Vec<_>>(), w)));
        let mut unc: Vec<bool> = subs.iter().map(|s| !chosen.iter().any(|&e| subset(&edges[e].0, s))).collect();
        for si in 0..subs.len() {
            if !unc[si] { continue; }
            let mut best: Option<(usize, usize)> = None;
            for &e in &ein { if !subset(&edges[e].0, &subs[si]) { continue; }
                let gain = (0..subs.len()).filter(|&s2| unc[s2] && subset(&edges[e].0, &subs[s2])).count();
                if best.map_or(true, |(_, g)| gain > g) { best = Some((e, gain)); } }
            let (e, _) = best.ok_or(format!("part {} (cap {}): subset {:?} has no bad set inside: capacity too small", i, cap, elems_of(&subs[si])))?;
            chosen.push(e); inch[e] = true;
            for s2 in 0..subs.len() { if unc[s2] && subset(&edges[e].0, &subs[s2]) { unc[s2] = false; } }
        }
    }
    Ok(Data { m, t: parts.len(), p: chosen.iter().map(|&e| edges[e].1 .1).collect(), q: chosen.iter().map(|&e| edges[e].1 .0).collect(),
        bad: chosen.iter().map(|&e| elems_of(&edges[e].0)).collect(), u: parts.iter().map(|(e, _)| e.clone()).collect(), c: parts.iter().map(|(_, c)| *c).collect() })
}

fn setstr(v: &[u32]) -> String { format!("{{{}}}", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")) }
fn heartbeats(h_goals: u64) -> u64 { // 8M for the m=62 module (H = 124*81 = 10044); scale by 1.5 x ratio, round up to 1M, never below 8M
    let r = h_goals as f64 / 10044.0; let v = (8.0e6 * r * 1.5 / 1.0e6).ceil() as u64 * 1_000_000; v.max(8_000_000) }
fn emit(d: &Data, suffix: &str, hb: u64, certname: &str) -> String {
    let m = d.m; let n = 2 * m; let sum: u32 = d.c.iter().sum();
    let j = |v: &Vec<u64>| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
    let bs = d.bad.iter().map(|b| setstr(b)).collect::<Vec<_>>().join(",");
    let us = d.u.iter().map(|b| setstr(b)).collect::<Vec<_>>().join(",");
    let cs = d.c.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(",");
    format!(r#"/-
# Cover-capacity certificates, composite 2m+1, continued (m = {m}; see Delta2CoverRangeI)

Generated by `code/dense/bin/lg` (src/lg/main.rs) from `data/dense/certs/{certname}`
and checked by `lg verify` (exact integer re-evaluation of every hypothesis of
`floor_of_cover_capacity` from this file's text) and by the independent verifier `bin/v1`.
Module name `Delta2CoverRange{suffix}`.
-/
import LRSpectrumFull.Delta2CoverCapacity

namespace LRSpectrumFull

open Finset

set_option maxHeartbeats {hb} in
set_option maxRecDepth 100000 in
/-- **Dense window at m = {m}** (`2m+1 = {q}`, composite): every {m} distinct positive velocities
bounded by {n} meet the floor `1/{t}`.  Cover-capacity certificate: {np} parts, capacities
summing to {sum} < {m}, using {nb} witness times. -/
theorem dense_floor_m{m} (v : Fin {m} → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 {n}) :
    1 / ({t} : ℝ) ≤ ML v := by
  have h := floor_of_cover_capacity (k := {k}) (t := {np}) (N := {nb}) v hv hinj
    (by simpa using hden) ![{ps}] ![{qs}] (by decide)
    ![{bs}]
    (by intro j x h1 h2; interval_cases x <;> fin_cases j <;> decide)
    ![{us}] ![{cs}]
    (by decide) (by decide) (by decide)
  norm_num at h
  exact h

end LRSpectrumFull
"#, m = m, q = 2 * m + 1, n = n, t = m + 1, k = m - 1, np = d.t, nb = d.p.len(), sum = sum, ps = j(&d.p), qs = j(&d.q),
        bs = bs, us = us, cs = cs, hb = hb, suffix = suffix, certname = certname)
}


// ---------------------------------------------------------------- split style (LG2)
/// substring of the bracket group starting at the first '[' after `key` (matching depth), including outer brackets.
fn group_after<'a>(text: &'a str, key: &str) -> Result<&'a str, String> {
    let i = text.find(key).ok_or(format!("missing {}", key))? + key.len();
    let rest = &text[i..]; let st = rest.find('[').ok_or("no [")?;
    let mut depth = 0; let mut end = None;
    for (k, ch) in rest[st..].char_indices() { match ch { '[' => depth += 1, ']' => { depth -= 1; if depth == 0 { end = Some(st + k); break; } } _ => {} } }
    Ok(&rest[st..=end.ok_or("unbalanced")?])
}
fn nested(g: &str) -> Vec<Vec<u32>> { // g = "[[1,2],[3]]"
    let inner = &g[1..g.len() - 1]; let mut out = vec![]; let mut cur: Option<String> = None;
    for ch in inner.chars() { match ch { '[' => cur = Some(String::new()), ']' => { let c = cur.take().unwrap();
        out.push(c.split(',').filter(|x| !x.trim().is_empty()).map(|x| x.trim().parse().unwrap()).collect()); }
        c => if let Some(cc) = cur.as_mut() { cc.push(c) } } }
    out
}
fn flat(g: &str) -> Vec<u64> { vecs(&g[1..g.len() - 1]) }
fn listlit(v: &[u32]) -> String { format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")) }

/// chunk boundaries for the hbad lemmas: ranges of j of size `jc`.
fn ranges(n: usize, sz: usize) -> Vec<(usize, usize)> { let mut v = vec![]; let mut a = 0; while a < n { let b = (a + sz).min(n); v.push((a, b)); a = b; } v }

fn emit2(d: &Data, suffix: &str, source: &str, jc: usize, tac: &str) -> String {
    let m = d.m; let n = 2 * m; let k = m - 1; let sum: u32 = d.c.iter().sum(); let nb = d.p.len(); let t = d.t;
    let j = |v: &Vec<u64>| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
    let bs = d.bad.iter().map(|b| listlit(b)).collect::<Vec<_>>().join(",");
    let us = d.u.iter().map(|b| listlit(b)).collect::<Vec<_>>().join(",");
    let cs = d.c.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(",");
    let hbr = ranges(nb, jc); let hcr = ranges(t, 1);
    let mut s = String::new();
    s += &format!(r#"/-
# Cover-capacity certificate, split style (m = {m}; see Delta2CoverRangeI)

Generated by `code/dense/bin/lg2` (src/lg/main.rs, command gen2/conv) from {source}.
Same hypotheses and same final statement as the monolithic style of Delta2CoverRangeAC, but the
data are plain `List` literals read through `List.getD`, and every large check is a separate
lemma closed by `{tac}` on a small range of indices (hbad: {jc} witnesses per lemma, hcap: one part
per lemma).  The final theorem is `dense_floor_m{m}_split` (suffixed to avoid a clash with a
monolithic module of the same m).  Module name `Delta2CoverRange{suffix}`.
-/
import LRSpectrumFull.Delta2CoverCapacity

namespace LRSpectrumFull

open Finset

namespace CR{suffix}

def PL : List ℕ := [{ps}]
def QL : List ℕ := [{qs}]
def BL : List (List ℕ) := [{bs}]
def UL : List (List ℕ) := [{us}]
def CL : List ℕ := [{cs}]

def pf (j : Fin {nb}) : ℕ := PL.getD j.val 0
def qf (j : Fin {nb}) : ℕ := QL.getD j.val 0
def bf (j : Fin {nb}) : Finset ℕ := (BL.getD j.val []).toFinset
def Uf (i : Fin {t}) : Finset ℕ := (UL.getD i.val []).toFinset
def cf (i : Fin {t}) : ℕ := CL.getD i.val 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem hq_all : ∀ j : Fin {nb}, 0 < qf j := by
  {tac}

"#, m = m, suffix = suffix, source = source, jc = jc, tac = tac, ps = j(&d.p), qs = j(&d.q), bs = bs, us = us, cs = cs, nb = nb, t = t);
    for (ci, &(a, b)) in hbr.iter().enumerate() {
        s += &format!("set_option maxHeartbeats 1000000 in\nset_option maxRecDepth 100000 in\ntheorem hbad_c{ci} : ∀ j : Fin {nb}, {a} ≤ j.val → j.val < {b} → ∀ x ∈ Finset.Icc 1 (2 * ({k} + 1)), goodAt {k} x (pf j) (qf j) = false → x ∈ bf j := by\n  {tac}\n\n", ci = ci, nb = nb, a = a, b = b, k = k, tac = tac);
    }
    s += &format!("theorem hbad_all : ∀ j : Fin {nb}, ∀ x, 1 ≤ x → x ≤ 2 * ({k} + 1) → goodAt {k} x (pf j) (qf j) = false → x ∈ bf j := by\n  intro j x h1 h2 hg\n  have hx : x ∈ Finset.Icc 1 (2 * ({k} + 1)) := Finset.mem_Icc.mpr ⟨h1, h2⟩\n  have hj : j.val < {nb} := j.isLt\n", nb = nb, k = k);
    for (ci, &(a, b)) in hbr.iter().enumerate() { let _ = a;
        if ci + 1 < hbr.len() { s += &format!("  by_cases c{ci} : j.val < {b}\n  · exact hbad_c{ci} j (by omega) c{ci} x hx hg\n", ci = ci, b = b); }
        else { s += &format!("  exact hbad_c{ci} j (by omega) (by omega) x hx hg\n\n", ci = ci); } }
    s += &format!("set_option maxHeartbeats 1000000 in\nset_option maxRecDepth 100000 in\ntheorem hcover_all : Finset.Icc 1 (2 * ({k} + 1)) ⊆ Finset.univ.biUnion Uf := by\n  {tac}\n\n", k = k, tac = tac);
    s += &format!("set_option maxHeartbeats 1000000 in\nset_option maxRecDepth 100000 in\ntheorem hsum_all : ∑ i : Fin {t}, cf i < {k} + 1 := by\n  {tac}\n\n", t = t, k = k, tac = tac);
    for (ci, &(a, b)) in hcr.iter().enumerate() {
        s += &format!("set_option maxHeartbeats 1000000 in\nset_option maxRecDepth 100000 in\ntheorem hcap_c{ci} : ∀ i : Fin {t}, {a} ≤ i.val → i.val < {b} → ∀ S ∈ (Uf i).powerset, cf i < S.card → ∃ j : Fin {nb}, bf j ⊆ S := by\n  {tac}\n\n", ci = ci, t = t, a = a, b = b, nb = nb, tac = tac);
    }
    s += &format!("theorem hcap_all : ∀ i : Fin {t}, ∀ S ∈ (Uf i).powerset, cf i < S.card → ∃ j : Fin {nb}, bf j ⊆ S := by\n  intro i S hS hc\n  have hi : i.val < {t} := i.isLt\n", t = t, nb = nb);
    for (ci, &(_, b)) in hcr.iter().enumerate() {
        if ci + 1 < hcr.len() { s += &format!("  by_cases c{ci} : i.val < {b}\n  · exact hcap_c{ci} i (by omega) c{ci} S hS hc\n", ci = ci, b = b); }
        else { s += &format!("  exact hcap_c{ci} i (by omega) (by omega) S hS hc\n\n", ci = ci); } }
    s += &format!("end CR{suffix}\n\n", suffix = suffix);
    s += &format!(r#"set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **Dense window at m = {m}** (`2m+1 = {q}`): every {m} distinct positive velocities
bounded by {n} meet the floor `1/{mp}`.  Cover-capacity certificate: {t} parts, capacities
summing to {sum} < {m}, using {nb} witness times (split style). -/
theorem dense_floor_m{m}_split (v : Fin {m} → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective fun i => (v i).toNat)
    (hden : ∀ i, (v i).toNat ∈ Finset.Icc 1 {n}) :
    1 / ({mp} : ℝ) ≤ ML v := by
  have h := floor_of_cover_capacity (k := {k}) (t := {t}) (N := {nb}) v hv hinj
    (by simpa using hden) CR{suffix}.pf CR{suffix}.qf CR{suffix}.hq_all CR{suffix}.bf CR{suffix}.hbad_all
    CR{suffix}.Uf CR{suffix}.cf CR{suffix}.hcover_all CR{suffix}.hcap_all CR{suffix}.hsum_all
  norm_num at h
  exact h

end LRSpectrumFull
"#, m = m, q = 2 * m + 1, n = n, mp = m + 1, t = t, sum = sum, nb = nb, k = k, suffix = suffix);
    s
}

fn parse_text2(text: &str) -> Result<Data, String> {
    if text.contains("sorry") || text.contains("native_decide") { return Err("sorry/native_decide present".into()); }
    let ti = text.find("theorem dense_floor_m").ok_or("no theorem")?; let body = &text[ti..];
    let m = num_after(body, "theorem dense_floor_m");
    let k = num_after(body, "(k := "); let t = num_after(body, "(t := ") as usize; let nn = num_after(body, "(N := ") as usize;
    if k + 1 != m { return Err("k+1 != m".into()); }
    if num_after(body, "(v : Fin ") != m { return Err("Fin size != m".into()); }
    if num_after(body, "Finset.Icc 1 ") != 2 * m { return Err("hden bound != 2m".into()); }
    if num_after(body, "1 / (") != m + 1 { return Err("floor 1/(m+1) mismatch".into()); }
    if !body.contains("(by simpa using hden)") || !body.contains("norm_num at h") || !body.contains("exact h") { return Err("final skeleton missing".into()); }
    let c = |key: &str| -> Result<&str, String> { group_after(text, key) };
    let d = Data { m, t, p: flat(c("def PL : List ℕ := ")?), q: flat(c("def QL : List ℕ := ")?), bad: nested(c("def BL : List (List ℕ) := ")?),
        u: nested(c("def UL : List (List ℕ) := ")?), c: flat(c("def CL : List ℕ := ")?).into_iter().map(|x| x as u32).collect() };
    if d.p.len() != nn || d.q.len() != nn || d.bad.len() != nn || d.u.len() != t || d.c.len() != t { return Err("data lengths do not match N, t".into()); }
    // index types of the accessor defs
    for key in [format!("def pf (j : Fin {})", nn), format!("def qf (j : Fin {})", nn), format!("def bf (j : Fin {})", nn), format!("def Uf (i : Fin {})", t), format!("def cf (i : Fin {})", t),
        format!("theorem hq_all : ∀ j : Fin {}, 0 < qf j", nn), format!("theorem hsum_all : ∑ i : Fin {t}, cf i < {k} + 1", t = t, k = k),
        format!("theorem hcover_all : Finset.Icc 1 (2 * ({k} + 1)) ⊆ Finset.univ.biUnion Uf", k = k),
        format!("theorem hbad_all : ∀ j : Fin {nb}, ∀ x, 1 ≤ x → x ≤ 2 * ({k} + 1) → goodAt {k} x (pf j) (qf j) = false → x ∈ bf j", nb = nn, k = k),
        format!("theorem hcap_all : ∀ i : Fin {t}, ∀ S ∈ (Uf i).powerset, cf i < S.card → ∃ j : Fin {nb}, bf j ⊆ S", t = t, nb = nn),
        "CRPLACEHOLDER".to_string()] {
        if key == "CRPLACEHOLDER" { continue; }
        if !text.contains(&key) { return Err(format!("missing declaration text: {}", key)); } }
    // chunk lemmas: partition of [0,N) and [0,t), assembly bounds equal
    let chunks = |prefix: &str, dom: usize, var: &str, ty: &str| -> Result<Vec<(usize, usize)>, String> {
        let mut v = vec![];
        for line in text.lines().filter(|l| l.starts_with(&format!("theorem {}_c", prefix))) {
            let head = format!("Fin {}, ", dom);
            let hi = line.find(&head).ok_or("chunk dom")? + head.len();
            let a: usize = line[hi..].chars().take_while(|c| c.is_ascii_digit()).collect::<String>().parse().map_err(|_| "chunk a")?;
            let key = format!("{}.val < ", var); let ki = line.find(&key).ok_or("chunk b")? + key.len();
            let b: usize = line[ki..].chars().take_while(|c| c.is_ascii_digit()).collect::<String>().parse().map_err(|_| "chunk b")?;
            if !line.contains(ty) { return Err("chunk body mismatch".into()); }
            v.push((a, b)); }
        if v.is_empty() { return Err(format!("no {} chunks", prefix)); }
        let mut at = 0; for &(a, b) in &v { if a != at || b <= a { return Err(format!("{} chunks do not partition: {:?}", prefix, v)); } at = b; }
        if at != dom { return Err(format!("{} chunks end at {} not {}", prefix, at, dom)); }
        Ok(v) };
    let hb = chunks("hbad", nn, "j", &format!("goodAt {} x (pf j) (qf j) = false → x ∈ bf j := by", k))?;
    let hc = chunks("hcap", t, "i", &format!("cf i < S.card → ∃ j : Fin {}, bf j ⊆ S := by", nn))?;
    for (tag, ch, var) in [("hbad_all", &hb, "j"), ("hcap_all", &hc, "i")] {
        let pre = if tag == "hbad_all" { "hbad" } else { "hcap" };
        let sec = &text[text.find(&format!("theorem {} :", tag)).unwrap()..];
        let sec = &sec[..sec.find("\n\n").unwrap_or(sec.len())];
        for (ci, &(_, b)) in ch.iter().enumerate() {
            if ci + 1 < ch.len() {
                if !sec.contains(&format!("by_cases c{ci} : {var}.val < {b}\n  · exact {pre}_c{ci} ", ci = ci, var = var, b = b, pre = pre)) { return Err(format!("{}: dispatch for chunk {} missing", tag, ci)); }
            } else if !sec.contains(&format!("exact {pre}_c{ci} ", pre = pre, ci = ci)) { return Err(format!("{}: last dispatch missing", tag)); } }
        if sec.matches("exact ").count() != ch.len() + if tag == "hbad_all" { 0 } else { 0 } { return Err(format!("{}: unexpected number of exact lines", tag)); } }
    // tactic on every lemma body line: one of the two allowed
    let kn = text.matches("\n  decide +kernel\n").count(); let pl = text.matches("\n  decide\n").count();
    if kn + pl != 3 + hb.len() + hc.len() { return Err(format!("decide-lines {} != lemmas {}", kn + pl, 3 + hb.len() + hc.len())); }
    if !text.contains(&format!("floor_of_cover_capacity (k := {}) (t := {}) (N := {}) v hv hinj", k, t, nn)) { return Err("final call mismatch".into()); }
    Ok(d)
}

fn same_data(a: &Data, b: &Data) -> bool { a.m == b.m && a.t == b.t && a.p == b.p && a.q == b.q && a.bad == b.bad && a.u == b.u && a.c == b.c }

fn report(tag: &str, mt: &Metrics, d: &Data) {
    println!("{} m={} parts={} sum_cap={} max_part={} witnesses={} H(2m*N)={} cap_subsets={} cap_work(sub*N)={} cover_work={}", tag, d.m, mt.np,
        d.c.iter().sum::<u32>(), mt.maxpart, mt.nw, mt.h_goals, mt.cap_subsets, mt.cap_work, mt.cover_work);
}

fn controls(d: &Data) {
    let mut tot = [0usize; 5]; let mut rej = [0usize; 5];
    let mut run = |idx: usize, e: Data| { tot[idx] += 1; if check_data(&e).is_err() { rej[idx] += 1; } };
    for j in 0..d.p.len() { let mut e = d.clone(); e.p.remove(j); e.q.remove(j); e.bad.remove(j); run(0, e); }
    for i in 0..d.t { if d.c[i] >= 1 { let mut e = d.clone(); e.c[i] -= 1; run(1, e); } }
    for j in 0..d.p.len() { let mut e = d.clone(); e.p[j] += 1; run(2, e); }
    for i in 0..d.t { for a in 0..d.u[i].len() { let mut e = d.clone(); e.u[i].remove(a); run(3, e); } }
    { let mut e = d.clone(); e.c[0] += 1; run(4, e); }
    let names = ["C1 drop one witness", "C2 lower one cap by 1", "C3 p -> p+1 in one witness", "C4 delete one element from one part", "C5 raise a cap (sum -> m if tight)"];
    for i in 0..5 { println!("{}: rejected {} of {}", names[i], rej[i], tot[i]); }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("gen") => {
            let m: u64 = a[2].parse().unwrap(); let sol = &a[3]; let suffix = &a[4]; let out = &a[5];
            let parts = parse_sol(sol, m).unwrap_or_else(|e| { eprintln!("parse: {}", e); std::process::exit(2) });
            let d = build(m, &parts).unwrap_or_else(|e| { eprintln!("build: {}", e); std::process::exit(3) });
            let mt0 = check_data(&d).unwrap_or_else(|e| { eprintln!("in-memory check: {}", e); std::process::exit(4) });
            let hb = heartbeats(mt0.h_goals);
            let cert = std::path::Path::new(sol).file_name().unwrap().to_string_lossy().to_string();
            let text = emit(&d, suffix, hb, &cert);
            let tmp = format!("{}.tmp", out);
            std::fs::write(&tmp, &text).unwrap(); std::fs::rename(&tmp, out).unwrap();
            // re-read emitted text and check from scratch
            let back = std::fs::read_to_string(out).unwrap();
            let d2 = parse_text(&back).unwrap_or_else(|e| { eprintln!("reparse: {}", e); std::process::exit(5) });
            let mut mt = check_data(&d2).unwrap_or_else(|e| { eprintln!("text check: {}", e); std::process::exit(6) });
            mt.bytes = back.len();
            println!("SELF-CHECK OK (from emitted text) bytes={} maxHeartbeats={}", back.len(), hb); report("lg", &mt, &d2);
        }
        Some("gen2") | Some("conv") => {
            // gen2 M CERT.sol SUFFIX OUT [JCHUNK] [plain]   |   conv OLD.lean SUFFIX OUT [JCHUNK] [plain]
            let is_conv = a[1] == "conv";
            let (d, suffix, out, src, rest) = if is_conv {
                let t = std::fs::read_to_string(&a[2]).unwrap();
                let d = parse_text(&t).unwrap_or_else(|e| { eprintln!("parse old: {}", e); std::process::exit(2) });
                let nm = std::path::Path::new(&a[2]).file_name().unwrap().to_string_lossy().to_string();
                (d, a[3].clone(), a[4].clone(), format!("the data of `{}` (identical certificate)", nm), 5)
            } else {
                let m: u64 = a[2].parse().unwrap();
                let parts = parse_sol(&a[3], m).unwrap_or_else(|e| { eprintln!("parse: {}", e); std::process::exit(2) });
                let d = build(m, &parts).unwrap_or_else(|e| { eprintln!("build: {}", e); std::process::exit(3) });
                let cert = std::path::Path::new(&a[3]).file_name().unwrap().to_string_lossy().to_string();
                (d, a[4].clone(), a[5].clone(), format!("`data/dense/certs/{}`", cert), 6)
            };
            let jc: usize = a.get(rest).and_then(|x| x.parse().ok()).unwrap_or(4);
            let tac = if a.iter().skip(rest).any(|x| x == "plain") { "decide" } else { "decide +kernel" };
            check_data(&d).unwrap_or_else(|e| { eprintln!("in-memory check: {}", e); std::process::exit(4) });
            let text = emit2(&d, &suffix, &src, jc, tac);
            let tmp = format!("{}.tmp", out);
            std::fs::write(&tmp, &text).unwrap(); std::fs::rename(&tmp, &out).unwrap();
            let back = std::fs::read_to_string(&out).unwrap();
            let d2 = parse_text(&back).unwrap_or_else(|e| { eprintln!("reparse: {}", e); std::process::exit(5) });
            if !same_data(&d, &d2) { eprintln!("reparsed data differ from source data"); std::process::exit(7) }
            let mt = check_data(&d2).unwrap_or_else(|e| { eprintln!("text check: {}", e); std::process::exit(6) });
            println!("SELF-CHECK OK (split style, from emitted text) bytes={} chunk={} tactic={}", back.len(), jc, tac); report("lg2", &mt, &d2);
        }
        Some("verify") => { let t = std::fs::read_to_string(&a[2]).unwrap(); let d = parse_text(&t).unwrap_or_else(|e| { println!("PARSE FAIL: {}", e); std::process::exit(5) });
            match check_data(&d) { Ok(mt) => { println!("VERIFY OK {}", a[2]); report("lg", &mt, &d) } Err(e) => { println!("VERIFY FAIL {}: {}", a[2], e); std::process::exit(6) } } }
        Some("controls") => { let t = std::fs::read_to_string(&a[2]).unwrap(); let d = parse_text(&t).unwrap(); check_data(&d).expect("base must pass"); controls(&d) }
        Some("fit") => {
            // measured build seconds ((development file, not part of this archive)): file stem -> seconds
            let known: HashMap<&str, f64> = [("Delta2CoverRangeAA", 182.), ("Delta2CoverRangeAB", 379.), ("Delta2CoverRangeAC", 130.), ("Delta2CoverRangeAD", 169.),
                ("Delta2CoverRangeAE", 173.), ("Delta2CoverRangeAF", 323.), ("Delta2CoverRangeZ", 219.)].into_iter().collect();
            let mut rows: Vec<(String, f64, f64, Option<f64>)> = vec![];
            for f in &a[2..] { let t = std::fs::read_to_string(f).unwrap(); let d = parse_text(&t).unwrap(); let mt = check_data(&d).unwrap();
                let stem = std::path::Path::new(f).file_name().unwrap().to_string_lossy().split('.').next().unwrap().to_string();
                rows.push((format!("{} (m={})", stem, d.m), mt.h_goals as f64, mt.cap_work as f64, known.get(stem.as_str()).cloned())); }
            // fit t = a*H + b*C on rows with known time (normal equations, 2 unknowns)
            let kn: Vec<&(String, f64, f64, Option<f64>)> = rows.iter().filter(|r| r.3.is_some()).collect();
            let (mut shh, mut shc, mut scc, mut sht, mut sct) = (0., 0., 0., 0., 0.);
            for r in &kn { let t = r.3.unwrap(); shh += r.1 * r.1; shc += r.1 * r.2; scc += r.2 * r.2; sht += r.1 * t; sct += r.2 * t; }
            let det = shh * scc - shc * shc; let (fa, fb) = ((sht * scc - sct * shc) / det, (shh * sct - shc * sht) / det);
            println!("fit t = {:.5e}*H + {:.5e}*C  ({} calibration rows)", fa, fb, kn.len());
            for r in &rows { println!("{:34} H={:7.0} C={:10.0} measured={:?} predicted={:.0}s", r.0, r.1, r.2, r.3, fa * r.1 + fb * r.2); }
        }
        _ => eprintln!("usage: lg gen M CERT SUFFIX OUT | verify F | controls F | fit F..."),
    }
}
