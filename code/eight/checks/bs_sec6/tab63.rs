// robust version of the 6.3 (ii.2.b) table. Parameters: sg (sign of r(e45) vs r(e13)),
// dl = q(e13) - q(w) in {0,1} (w = +-e45), u = 3 q(e13) + 5 q(e23), c3 = q(e13) - q(e23) - q(e12) in {0,1}.
// Choose Y = q(e13) (Lambda_h). Then X = q(e23) = 3u - 2Y, Z = q(e12) = Y - X - c3, q(e45) = Y - dl (sg +)
// or 6 - (Y - dl) (sg -). A1 values {a, a+Y+c1, a+X+c2} with c1 = c2 + Z-carry... we require robustness
// over all carries consistent with q(d1) = q(d2) + Z + c3'. e~(d4,d5) in q(e45) + {-1,0,1}, d4 free.
fn ok7(v: i64) -> bool { let v = v.rem_euclid(7); v != 0 && v != 6 }
fn md(x: i64) -> i64 { x.rem_euclid(7) }
fn robust(a1: &[(i64, i64)], ets: &[i64]) -> bool {
    // a1: list of (o1, o2) possible A1 offsets; ets: possible e~45; d4 = p free, d5 = 2p - e
    for &(o1, o2) in a1 { for &e in ets { for p in 0..7 {
        let q5 = md(2 * p - e);
        if !(0..7).any(|k| ok7(k) && ok7(o1 + k) && ok7(o2 + k) && ok7(p + 2 * k) && ok7(q5 + 4 * k)) { return false; }
    } } }
    true
}
fn main() {
    let mut nofix = 0; let mut dbl_needed = vec![];
    for sg in [1i64, -1] { for dl in 0..2i64 { for u in 0..7i64 { for c3 in 0..2i64 {
        let mut good = vec![]; let mut goodd = vec![];
        for y in 0..7i64 {
            let x = md(3 * u - 2 * y); let z = md(y - x - c3);
            let q45 = if sg == 1 { md(y - dl) } else { md(6 - (y - dl)) };
            // offsets: d1 = C + Y + c1, d2 = C + X + c2, with Y + c1 = X + c2 + Z + c3' (mod 7)
            let mut a1 = vec![];
            for c1 in 0..2 { for c2 in 0..2 { for c3p in 0..2 { if md(y + c1 - (x + c2 + z + c3p)) == 0 { a1.push((md(y + c1), md(x + c2))); } } } }
            let ets: Vec<i64> = (-1..=1).map(|e| md(q45 + e)).collect();
            if robust(&a1, &ets) { good.push(y); }
            // doubled: q(2e) in 2q(e)+{0,1}; A1 offsets 2Y+g1+c1', 2X+g2+c2' with no constraint (robust over all)
            let mut a2 = vec![];
            for g1 in 0..2 { for g2 in 0..2 { for c1 in 0..2 { for c2 in 0..2 { a2.push((md(2 * y + g1 + c1), md(2 * x + g2 + c2))); } } } }
            let mut ets2 = vec![]; for g in 0..2 { for e in -1..=1 { ets2.push(md(2 * q45 + g + e)); } }
            if robust(&a2, &ets2) { goodd.push(y); }
        }
        if good.is_empty() { nofix += 1; dbl_needed.push((sg, dl, u, c3, goodd.clone())); }
        println!("sg={:2} dl={} u={} c3={}: robust Y = {:?} | robust after doubling Y = {:?}", sg, dl, u, c3, good, goodd);
    } } } }
    println!("cases without a direct Y: {} {:?}", nofix, dbl_needed);
}
