// RQ census: exact count of covering classes over 4-sets of distinct positive integers, gcd 1, sum <= MAXSUM.
// usage: rq_census MAXSUM [std|nogcd|tq5]
use std::env;
fn gcd(a: u32, b: u32) -> u32 { if b == 0 { a } else { gcd(b, a % b) } }
fn nonres(s: u32, a: u32, b: u32) -> bool { s != a + b && a != b + s && b != a + s }
// bits: 0 MSS29, 1 MSS65, 2 R5, 3 P3, 4 QGEN, 5 T, 6 G24
struct Ev { mask: u8, q4: bool, qg5: bool, t7: bool, tg6: bool, tg8: bool, tgo: bool }
fn eval(v: [u32; 4], tmin: u32) -> Ev {
    let mut m = 0u8;
    // MSS29
    for z in 0..4 {
        let mut g = 0; for i in 0..4 { if i != z { g = gcd(g, v[i]); } }
        if g >= 2 { m |= 1; }
    }
    // MSS65
    for i in 0..4 { for j in i + 1..4 {
        let g = gcd(v[i], v[j]);
        if (g % 2 == 1 && g >= 5) || (g % 2 == 0 && g >= 10) { m |= 2; }
    } }
    // R5
    let c5 = v.iter().filter(|&&x| x % 5 == 0).count();
    if c5 >= 1 && c5 <= 3 { m |= 4; }
    // P3
    for z in 0..4 {
        let mut g = 0; for i in 0..4 { if i != z { g = gcd(g, v[i]); } }
        for q in 2..=g { if g % q == 0 && v[z] % q != 0 { m |= 8; } }
    }
    let (mut q4, mut qg5, mut t7, mut tg6, mut tg8, mut tgo) = (false, false, false, false, false, false);
    for i in 0..4 { for j in i + 1..4 {
        let (k, l) = { let mut r = [0usize; 2]; let mut n = 0; for x in 0..4 { if x != i && x != j { r[n] = x; n += 1; } } (r[0], r[1]) };
        let g = gcd(v[i], v[j]);
        for q in 4..=g {
            if g % q != 0 { continue; }
            if gcd(v[k], q) != 1 || gcd(v[l], q) != 1 { continue; }
            if q >= tmin { m |= 32; if q >= 7 && q != 8 { t7 = true; } if g == 6 { tg6 = true } else if g == 8 { tg8 = true } else { tgo = true } }
            let cls = (v[k] + v[l]) % q == 0 || (v[k].max(v[l]) - v[k].min(v[l])) % q == 0;
            if cls && nonres(v[i], v[k], v[l]) && nonres(v[j], v[k], v[l]) {
                m |= 16; if q == 4 { q4 = true; } if q >= 5 { qg5 = true; }
            }
        }
    } }
    // G24
    for s in 0..4 { for e in 0..4 { if e == s { continue; }
        let mut r = [0usize; 2]; let mut n = 0; for x in 0..4 { if x != s && x != e { r[n] = x; n += 1; } }
        let (a, b) = (r[0], r[1]);
        if v[a] % 2 == 1 && v[b] % 2 == 1 && v[e] % 4 == 2 && v[s] % 4 == 0 && nonres(v[s], v[a], v[b]) { m |= 64; }
    } }
    Ev { mask: m, q4, qg5, t7, tg6, tg8, tgo }
}
fn main() {
    let a: Vec<String> = env::args().collect();
    let maxs: u32 = a[1].parse().unwrap();
    let mode = if a.len() > 2 { a[2].as_str() } else { "std" };
    let tmin = if mode == "tq5" { 5 } else { 6 };
    let mut total = 0u64; let mut hist = [0u64; 128];
    let (mut nq4, mut nqg5, mut nqg5bad, mut nt7, mut nt7notmss65) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut tnm = [0u64; 8]; // T not in MSS: index by tg6|tg8<<1|tgo<<2
    let mut res_split = [[0u64; 5]; 2]; // [resonant][#even]
    let mut resid: Vec<(u32, [u32; 4])> = Vec::new();
    for aa in 1..=maxs { for b in aa + 1..=maxs { if aa + b + b + 1 > maxs { break; }
        for c in b + 1..=maxs { if aa + b + c + c + 1 > maxs { break; }
            for d in c + 1..=maxs { let s = aa + b + c + d; if s > maxs { break; }
                if mode != "nogcd" && gcd(gcd(aa, b), gcd(c, d)) != 1 { continue; }
                total += 1;
                let v = [aa, b, c, d];
                let ev = eval(v, tmin);
                hist[ev.mask as usize] += 1;
                let mss = ev.mask & 3 != 0;
                if ev.q4 { nq4 += 1; }
                if ev.qg5 { nqg5 += 1; if ev.mask & (1 | 2 | 4 | 32) == 0 { nqg5bad += 1; } }
                if ev.t7 { nt7 += 1; if ev.mask & 2 == 0 { nt7notmss65 += 1; } }
                if ev.mask & 32 != 0 && !mss { tnm[(ev.tg6 as usize) | (ev.tg8 as usize) << 1 | (ev.tgo as usize) << 2] += 1; }
                if ev.mask == 0 {
                    let mut res = false;
                    for i in 0..4 { for j in i + 1..4 { for k in 0..4 { if k != i && k != j && v[i] + v[j] == v[k] { res = true; } } } }
                    if v[0] + v[1] == v[2] + v[3] || v[0] + v[2] == v[1] + v[3] || v[0] + v[3] == v[1] + v[2] { res = true; }
                    let ne = v.iter().filter(|&&x| x % 2 == 0).count();
                    res_split[res as usize][ne] += 1;
                    resid.push((s, v));
                }
            } } } }
    println!("MAXSUM {} MODE {}", maxs, mode);
    println!("TOTAL {}", total);
    for m in 0..128 { if hist[m] > 0 { println!("H {} {}", m, hist[m]); } }
    println!("Q4 {}\nQG5 {}\nQG5_NOT_R5_MSS_T {}\nT7 {}\nT7_NOT_MSS65 {}", nq4, nqg5, nqg5bad, nt7, nt7notmss65);
    for i in 0..8 { if tnm[i] > 0 { println!("TNM g6={} g8={} other={} : {}", i & 1, (i >> 1) & 1, (i >> 2) & 1, tnm[i]); } }
    for r in 0..2 { println!("RES resonant={} even0..4 {:?}", r, res_split[r]); }
    resid.sort();
    println!("RESID {}", resid.len());
    for (s, v) in resid.iter().take(20) { println!("R {} {:?}", s, v); }
    for t in [[1u32,2,3,4],[1,3,4,6],[1,3,4,7]] { println!("INRES {:?} {}", t, resid.iter().any(|x| x.1 == t)); }
    // dump all class counts
    let names = ["MSS29","MSS65","R5","P3","QGEN","T","G24"];
    for (bit, n) in names.iter().enumerate() {
        let tot: u64 = (0..128).filter(|m| m >> bit & 1 == 1).map(|m| hist[m]).sum();
        let only: u64 = hist[1 << bit];
        println!("CLASS {} {} only {}", n, tot, only);
    }
    let sum = |f: &dyn Fn(usize) -> bool| -> u64 { (0..128).filter(|&m| f(m)).map(|m| hist[m]).sum() };
    let lean = |m: usize| m & (4 | 8 | 16 | 32 | 64) != 0;
    let mss = |m: usize| m & 3 != 0;
    println!("LEAN {}", sum(&|m| lean(m)));
    println!("MSS {}", sum(&|m| mss(m)));
    println!("COVERED {}", sum(&|m| lean(m) || mss(m)));
    println!("RESIDUAL {}", sum(&|m| !(lean(m) || mss(m))));
    println!("LEAN_NOT_MSS {}", sum(&|m| lean(m) && !mss(m)));
    println!("LEAN_NOT_MSS_OR_R5 {}", sum(&|m| lean(m) && !mss(m) && m & 4 == 0));
    println!("COVERED_NOT_LEAN {}", sum(&|m| !lean(m) && mss(m)));
    println!("P3_xor_MSS29 {}", sum(&|m| (m >> 3 & 1) != (m & 1)));
}
