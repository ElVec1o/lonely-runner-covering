// s4gen: (1) Rust mirror of the Lean Bool test `classB` (LRSpectrumFull/S4Class.lean), (2) census comparison against
// the RQ census predicates (copy of rq_census_v2::eval, rq = true), (3) per-a survey of the residual,
// (4) generator of Lean range modules (S4Loop.rangeB) with depth-0 certificates in the loop's order.
// usage:
//   s4gen census MAXSUM
//   s4gen survey MAXSUM OUT_NOCERT_FILE
//   s4gen gen A BLO N NAME OUT.lean [corrupt K | drop K]      (module text for S4Loop.rangeB A BLO N)
mod zono;
mod block2;
mod blk;
mod blk2;
use std::env;
use std::fs;
use std::io::Write;
use zono::*;

fn gcd(a: u32, b: u32) -> u32 { if b == 0 { a } else { gcd(b, a % b) } }
fn nonres(s: u32, a: u32, b: u32) -> bool { s != a + b && a != b + s && b != a + s }
fn sim7(x: u32, y: u32) -> bool { (x % 7 == y % 7) || (x + y) % 7 == 0 }

// ---------------- census (verbatim logic of rq_census_v2::eval with rq = true, r7excl = true) ----------------
// bits: 0 MSS29, 1 MSS65, 2 R5, 3 P3, 4 QGEN, 5 T, 6 G24, 7 R7, 8 Q3
fn census_mask(v: [u32; 4]) -> u16 {
    let tmin = 6u32;
    let mut m = 0u16;
    for z in 0..4 { let mut g = 0; for i in 0..4 { if i != z { g = gcd(g, v[i]); } } if g >= 2 { m |= 1; } }
    for i in 0..4 { for j in i + 1..4 { let g = gcd(v[i], v[j]); if (g % 2 == 1 && g >= 5) || (g % 2 == 0 && g >= 10) { m |= 2; } } }
    let c5 = v.iter().filter(|&&x| x % 5 == 0).count();
    if c5 >= 1 && c5 <= 3 { m |= 4; }
    for z in 0..4 { let mut g = 0; for i in 0..4 { if i != z { g = gcd(g, v[i]); } } for q in 2..=g { if g % q == 0 && v[z] % q != 0 { m |= 8; } } }
    for i in 0..4 { for j in i + 1..4 {
        let (k, l) = { let mut r = [0usize; 2]; let mut n = 0; for x in 0..4 { if x != i && x != j { r[n] = x; n += 1; } } (r[0], r[1]) };
        let g = gcd(v[i], v[j]);
        for q in 4..=g {
            if g % q != 0 { continue; }
            if gcd(v[k], q) != 1 || gcd(v[l], q) != 1 { continue; }
            if q >= tmin { m |= 32; }
            let cls = (v[k] + v[l]) % q == 0 || (v[k].max(v[l]) - v[k].min(v[l])) % q == 0;
            if cls && nonres(v[i], v[k], v[l]) && nonres(v[j], v[k], v[l]) { m |= 16; }
        }
    } }
    for s in 0..4 { for e in 0..4 { if e == s { continue; }
        let mut r = [0usize; 2]; let mut n = 0; for x in 0..4 { if x != s && x != e { r[n] = x; n += 1; } }
        let (a, b) = (r[0], r[1]);
        if v[a] % 2 == 1 && v[b] % 2 == 1 && v[e] % 4 == 2 && v[s] % 4 == 0 && nonres(v[s], v[a], v[b]) { m |= 64; }
    } }
    for s in 0..4 { if v[s] % 7 != 0 { continue; }
        let fr: Vec<usize> = (0..4).filter(|&x| x != s).collect();
        if fr.iter().any(|&i| v[i] % 7 == 0) { continue; }
        for &a in &fr { for &b in &fr { if b == a { continue; } for &c in &fr { if c == a || c == b { continue; }
            let pa = sim7(v[a], v[b]) && sim7(v[a], v[c]);
            let res = v[s] == v[b] + v[c] || v[b] == v[c] + v[s] || v[c] == v[b] + v[s];
            let m3 = v[b] % 7 == (3 * v[a]) % 7 || (v[b] + 3 * v[a]) % 7 == 0;
            let pb = sim7(v[b], v[c]) && !sim7(v[a], v[b]) && !(res && m3);
            if pa || pb { m |= 128; }
        } } }
    }
    let sl: Vec<usize> = (0..4).filter(|&x| v[x] % 3 == 0).collect();
    if sl.len() == 2 {
        let fr: Vec<usize> = (0..4).filter(|&x| v[x] % 3 != 0).collect();
        if nonres(v[sl[0]], v[fr[0]], v[fr[1]]) && nonres(v[sl[1]], v[fr[0]], v[fr[1]]) { m |= 256; }
    }
    m
}

// ---------------- mirror of the Lean classB (S4Class.lean), same lists, same tests ----------------
fn sel(i: u32, a: u32, b: u32, c: u32, d: u32) -> u32 { if i == 0 { a } else if i == 1 { b } else if i == 2 { c } else { d } }
const PAIR_L: [[u32; 4]; 6] = [[0,1,2,3],[0,2,1,3],[0,3,1,2],[1,2,0,3],[1,3,0,2],[2,3,0,1]];
const P3_L: [[u32; 4]; 4] = [[0,1,2,3],[0,1,3,2],[0,2,3,1],[1,2,3,0]];
const G24_L: [[u32; 4]; 12] = [[2,3,1,0],[1,3,2,0],[1,2,3,0],[2,3,0,1],[0,3,2,1],[0,2,3,1],[1,3,0,2],[0,3,1,2],[0,1,3,2],[1,2,0,3],[0,2,1,3],[0,1,2,3]];
const R7_L: [[u32; 4]; 12] = [[0,1,2,3],[0,2,1,3],[0,3,1,2],[1,0,2,3],[1,2,0,3],[1,3,0,2],[2,0,1,3],[2,1,0,3],[2,3,0,1],[3,0,1,2],[3,1,0,2],[3,2,0,1]];

fn r5_b(a: u32, b: u32, c: u32, d: u32) -> bool {
    (a % 5 == 0 || b % 5 == 0 || c % 5 == 0 || d % 5 == 0) && (a % 5 != 0 || b % 5 != 0 || c % 5 != 0 || d % 5 != 0)
}
fn f_p3(x: u32, y: u32, u: u32, w: u32) -> bool { let g = gcd(gcd(x, y), u); g >= 2 && w % g != 0 }
fn f_t(x: u32, y: u32, u: u32, w: u32) -> bool {
    let g = gcd(x, y);
    g >= 6 && (0..=g).any(|q| q >= 6 && g % q == 0 && gcd(u, q) == 1 && gcd(w, q) == 1)
}
fn f_q(x: u32, y: u32, u: u32, w: u32) -> bool {
    let g = gcd(x, y);
    g >= 4 && nonres(x, u, w) && nonres(y, u, w) &&
    (0..=g).any(|q| q >= 4 && g % q == 0 && gcd(u, q) == 1 && gcd(w, q) == 1 && (u % q == w % q || (u + w) % q == 0))
}
fn f_q3(x: u32, y: u32, u: u32, w: u32) -> bool {
    x % 3 == 0 && y % 3 == 0 && u % 3 != 0 && w % 3 != 0 && nonres(x, u, w) && nonres(y, u, w)
}
fn f_g24(x: u32, y: u32, u: u32, w: u32) -> bool {
    x % 2 == 1 && y % 2 == 1 && u % 4 == 2 && w % 4 == 0 && nonres(w, x, y)
}
fn f_r7(x: u32, y: u32, u: u32, w: u32) -> bool {
    x % 7 == 0 && y % 7 != 0 && u % 7 != 0 && w % 7 != 0 &&
    ((sim7(y, u) && sim7(y, w)) ||
     (sim7(u, w) && !sim7(y, u) &&
      !((x == u + w || u == w + x || w == u + x) && (u % 7 == (3 * y) % 7 || (u + 3 * y) % 7 == 0))))
}
fn any_perm<const N: usize>(l: &[[u32; 4]; N], f: &dyn Fn(u32, u32, u32, u32) -> bool, v: [u32; 4]) -> bool {
    l.iter().any(|p| f(sel(p[0], v[0], v[1], v[2], v[3]), sel(p[1], v[0], v[1], v[2], v[3]), sel(p[2], v[0], v[1], v[2], v[3]), sel(p[3], v[0], v[1], v[2], v[3])))
}
// per-test bit: 0 R5, 1 G24, 2 P3, 3 T, 4 Q, 5 Q3, 6 R7
fn class_bits(v: [u32; 4]) -> u8 {
    let mut m = 0u8;
    if r5_b(v[0], v[1], v[2], v[3]) { m |= 1; }
    if any_perm(&G24_L, &f_g24, v) { m |= 2; }
    if any_perm(&P3_L, &f_p3, v) { m |= 4; }
    if any_perm(&PAIR_L, &f_t, v) { m |= 8; }
    if any_perm(&PAIR_L, &f_q, v) { m |= 16; }
    if any_perm(&PAIR_L, &f_q3, v) { m |= 32; }
    if any_perm(&R7_L, &f_r7, v) { m |= 64; }
    m
}
fn class_b(v: [u32; 4]) -> bool { class_bits(v) != 0 }

// ---------------- loop (mirror of S4Loop.goB / goC / goD) ----------------
fn n_c(a: u32, b: u32) -> u32 { ((194u32.saturating_sub(a + b)) / 2).saturating_sub(b) }
fn n_d(a: u32, b: u32, c: u32) -> u32 { 195u32.saturating_sub(a + b + 2 * c) }
/// calls f(a,b,c,d) in the exact order of rangeB a blo n
fn for_range(a: u32, blo: u32, n: u32, f: &mut dyn FnMut(u32, u32, u32, u32)) {
    for b in blo..blo + n {
        let nc = n_c(a, b);
        for c in b + 1..b + 1 + nc {
            let nd = n_d(a, b, c);
            for d in c + 1..c + 1 + nd { f(a, b, c, d); }
        }
    }
}
fn full_n(a: u32) -> u32 { ((192u32.saturating_sub(a)) / 3).saturating_sub(a) }

// ---------------- certificates ----------------
fn lean_ok(v: &V4, k: &K3) -> bool {
    if det_cols(v, k) == 0 { return false; }
    for &(i, j) in [(0usize, 1usize), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)].iter() {
        let mut s: i128 = 0;
        for l in 0..3 { s += ((k[l][j] * v[i] - k[l][i] * v[j]) as i128).abs(); }
        if 5 * s > 3 * (v[i] + v[j]) as i128 { return false; }
    }
    true
}
fn find_cert(v: &V4) -> Option<K3> {
    let seed = 0x9E3779B97F4A7C15u64 ^ ((v[0] as u64) << 48 | (v[1] as u64) << 32 | (v[2] as u64) << 16 | v[3] as u64).wrapping_mul(0xD6E8FEB86659FD93);
    for &restarts in [40usize, 3000].iter() {
        let mut rng = Rng(seed | 1);
        let (k, _r, _) = best_basis(v, restarts, &mut rng);
        if lean_ok(v, &k) { return Some(k); }
    }
    None
}
fn lean_lit(v: &V4, k: &K3) -> String {
    let f = |x: i64| if x < 0 { format!("({})", x) } else { format!("{}", x) };
    let mut s = format!(".d0 {} {} {}", v[1], v[2], v[3]);
    for l in 0..3 { for r in 0..4 { s.push(' '); s.push_str(&f(k[l][r])); } }
    s
}

fn main() {
    let a: Vec<String> = env::args().collect();
    match a[1].as_str() {
        "census" => {
            let maxs: u32 = a[2].parse().unwrap();
            let (mut total, mut lean2, mut cb, mut miss, mut extra) = (0u64, 0u64, 0u64, 0u64, 0u64);
            let mut miss_by_cls = [0u64; 9]; // census bit 0..8
            let mut cls_tot = [0u64; 9];
            let mut test_tot = [0u64; 7];
            let mut test_only = [0u64; 7];
            let mut census_only_lean = [0u64; 9];
            let mut ex_list: Vec<[u32; 4]> = vec![]; let mut miss_list: Vec<[u32; 4]> = vec![];
            for aa in 1..=maxs { for b in aa + 1..=maxs { if aa + b + b + 1 > maxs { break; }
                for c in b + 1..=maxs { if aa + b + c + c + 1 > maxs { break; }
                    for d in c + 1..=maxs { if aa + b + c + d > maxs { break; }
                        if gcd(gcd(aa, b), gcd(c, d)) != 1 { continue; }
                        total += 1;
                        let v = [aa, b, c, d];
                        let cm = census_mask(v);
                        let in_lean2 = cm & (4 | 8 | 16 | 32 | 64 | 128 | 256) != 0;
                        let bits = class_bits(v);
                        let inb = bits != 0;
                        if in_lean2 { lean2 += 1; }
                        if inb { cb += 1; }
                        for t in 0..7 { if bits >> t & 1 == 1 { test_tot[t] += 1; if bits == 1 << t { test_only[t] += 1; } } }
                        for t in 2..9 { if cm >> t & 1 == 1 { cls_tot[t] += 1; } }
                        if in_lean2 && !inb { miss += 1; for t in 2..9 { if cm >> t & 1 == 1 { miss_by_cls[t] += 1; } } if miss_list.len() < 40 { miss_list.push(v); } }
                        if inb && !in_lean2 { extra += 1; if ex_list.len() < 40 { ex_list.push(v); } }
                        let _ = &mut census_only_lean;
                    } } } }
            println!("MAXSUM {}", maxs);
            println!("TOTAL {}", total);
            println!("CENSUS_LEAN2 {}", lean2);
            println!("CLASSB {}", cb);
            println!("CENSUS_CLASS_VECTORS_MISSED_BY_CLASSB {}", miss);
            println!("CLASSB_NOT_IN_CENSUS {}", extra);
            println!("RESIDUAL_BY_CLASSB {}", total - cb);
            let names = ["MSS29", "MSS65", "R5", "P3", "QGEN", "T", "G24", "R7", "Q3"];
            for t in 2..9 { println!("CENSUS_CLASS {} total {} missed_by_classB {}", names[t], cls_tot[t], miss_by_cls[t]); }
            let tn = ["R5", "G24", "P3", "T", "Q(Gen/4)", "Q3", "R7"];
            for t in 0..7 { println!("LEAN_TEST {} total {} only_this_test {}", tn[t], test_tot[t], test_only[t]); }
            for v in &miss_list { println!("MISSED {:?}", v); }
            for v in &ex_list { println!("EXTRA {:?}", v); }
        }
        "survey" => {
            let maxs: u32 = a[2].parse().unwrap();
            let mut f = fs::File::create(&a[3]).unwrap();
            println!("a enumerated primitive classB residual nocert");
            let (mut ta, mut tp, mut tc, mut tr, mut tn) = (0u64, 0u64, 0u64, 0u64, 0u64);
            for aa in 1..=maxs {
                let n = full_n(aa); if n == 0 { continue; }
                let (mut en, mut pr, mut cl, mut re, mut nc) = (0u64, 0u64, 0u64, 0u64, 0u64);
                for_range(aa, aa + 1, n, &mut |a0, b, c, d| {
                    en += 1;
                    if gcd(gcd(a0, b), gcd(c, d)) != 1 { return; }
                    pr += 1;
                    let v = [a0, b, c, d];
                    if class_b(v) { cl += 1; return; }
                    re += 1;
                    let vv: V4 = [a0 as i64, b as i64, c as i64, d as i64];
                    if find_cert(&vv).is_none() { nc += 1; writeln!(f, "{} {} {} {} a={}", a0, b, c, d, a0).unwrap(); }
                });
                println!("{} {} {} {} {} {}", aa, en, pr, cl, re, nc);
                ta += en; tp += pr; tc += cl; tr += re; tn += nc;
            }
            println!("TOTAL enumerated {} primitive {} classB {} residual {} nocert {}", ta, tp, tc, tr, tn);
        }
        "gen" => {
            let aa: u32 = a[2].parse().unwrap(); let blo: u32 = a[3].parse().unwrap(); let n: u32 = a[4].parse().unwrap();
            let name = a[5].clone(); let out = a[6].clone();
            let (mut mode, mut kidx) = ("none".to_string(), 0usize);
            if a.len() > 8 { mode = a[7].clone(); kidx = a[8].parse().unwrap(); }
            let mut recs: Vec<String> = vec![];
            let (mut en, mut pr, mut cl, mut nc) = (0u64, 0u64, 0u64, 0u64);
            let mut nocert: Vec<[u32; 4]> = vec![];
            for_range(aa, blo, n, &mut |a0, b, c, d| {
                en += 1;
                if gcd(gcd(a0, b), gcd(c, d)) != 1 { return; }
                pr += 1;
                if class_b([a0, b, c, d]) { cl += 1; return; }
                let vv: V4 = [a0 as i64, b as i64, c as i64, d as i64];
                match find_cert(&vv) { Some(k) => recs.push(lean_lit(&vv, &k)), None => { nc += 1; nocert.push([a0, b, c, d]); } }
            });
            eprintln!("GEN a={} blo={} n={} enumerated={} primitive={} classB={} certified={} nocert={}", aa, blo, n, en, pr, cl, recs.len(), nc);
            for v in nocert.iter().take(20) { eprintln!("NOCERT {:?}", v); }
            if nc > 0 { eprintln!("REFUSED: {} vectors without depth-0 certificate in this range, no module written", nc); std::process::exit(2); }
            if mode == "corrupt" {
                // flip the first entry of k1: x -> x + 1 (record kidx)
                let r = &recs[kidx]; let mut parts: Vec<String> = r.split(' ').map(|s| s.to_string()).collect();
                let t = parts[4].trim_matches(|c| c == '(' || c == ')').parse::<i64>().unwrap() + 1;
                parts[4] = if t < 0 { format!("({})", t) } else { format!("{}", t) };
                recs[kidx] = parts.join(" ");
            } else if mode == "drop" { recs.remove(kidx); }
            let mut s = String::new();
            s.push_str(&format!("/-\n# generated by s4gen (s4_range/census_b): range a={} b in [{}, {}), {} depth-0 records ({})\n-/\nimport LRSpectrumFull.S4Loop\n\nnamespace LRSpectrumFull\nnamespace D0\n\n", aa, blo, blo + n, recs.len(), mode));
            s.push_str(&format!("set_option maxRecDepth 1000000 in\ndef certs_{} : List Cert := [\n", name));
            for (i, r) in recs.iter().enumerate() { s.push_str("  "); s.push_str(r); if i + 1 < recs.len() { s.push_str(",\n"); } else { s.push('\n'); } }
            s.push_str("]\n\n");
            s.push_str(&format!("theorem rng_{n0} : rangeB {a} {blo} {n} certs_{n0} = true := by decide +kernel\n\n", n0 = name, a = aa, blo = blo, n = n));
            s.push_str(&format!("theorem S4_{n0} : ∀ b c d : ℕ, {blo} ≤ b → b < {blo} + {n} → b < c → c < d → {a} + b + c + d ≤ 195 →\n    Nat.gcd (Nat.gcd {a} b) (Nat.gcd c d) = 1 → S4 ![{a}, b, c, d] :=\n  rangeOK_sound (by norm_num) (by norm_num) rng_{n0}\n\n", n0 = name, a = aa, blo = blo, n = n));
            s.push_str(&format!("#print axioms S4_{}\n\nend D0\nend LRSpectrumFull\n", name));
            fs::write(&out, s).unwrap();
            println!("wrote {} records {}", recs.len(), out);
        }
        "plan" => block2::plan(a[2].parse().unwrap(), &a[3]),
        "genall" => block2::genall(&a[2], &a[3], a.len() > 4 && a[4] == "dry"),
        "verify" => block2::verify(&a[2..]),
        "check" => block2::check(&a[2], &a[3], a[4].parse().unwrap()),
        "blkgen" => blk::blkgen(&a[2..]),
        "blkverify" => blk::blkverify(&a[2..]),
        "asmgen" => blk2::asmgen(&a[2..]),
        "asmverify" => blk2::asmverify(&a[2..]),
        "asmcheck" => blk2::asmcheck(&a[2..]),
        _ => println!("modes: census survey gen plan genall verify check"),
    }
}
