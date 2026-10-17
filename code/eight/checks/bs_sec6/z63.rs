// the exact Z7 statements for BarajasSerraSec6_3.
fn ok7(v: i64) -> bool { let v = v.rem_euclid(7); v != 0 && v != 6 }
fn md(x: i64) -> i64 { x.rem_euclid(7) }
fn t63(dl: i64, u: i64, c3: i64) -> i64 {
    if dl == 0 { [0, 6, 0, 3, 6, 0, 6][u as usize] } else { match u { 0 => 0, 1 => 1, 2 => 0, 3 => 1, 4 => if c3 == 0 { 6 } else { 0 }, 5 => 0, _ => 6 } }
}
fn main() {
    // z63w: window l<=2, one A2 one A4 element
    let mut f = 0; let mut nc = 0;
    for a in 0..7 { for g1 in 0..2 { for g2 in 0..3 { for p4 in 0..7 { for p5 in 0..7 {
        let g = (0..7).any(|k| ok7(a + k) && ok7(a + g1 + k) && ok7(a + g2 + k) && ok7(p4 + 2 * k) && ok7(p5 + 4 * k));
        if g2 < 2 { if !g { f += 1; } } else if !g { nc += 1; }
    } } } } }
    println!("z63w fail={} | NC(g2 up to 2) fails={}", f, nc);
    // z63top1: offsets 0,1,2 and e45 notin {2,4}
    let mut f = 0; let mut bad = std::collections::BTreeSet::new();
    for a in 0..7 { for p4 in 0..7 { for p5 in 0..7 { let e = md(2 * p4 - p5);
        let g = (0..7).any(|k| ok7(a + k) && ok7(a + 1 + k) && ok7(a + 2 + k) && ok7(p4 + 2 * k) && ok7(p5 + 4 * k));
        if !g { bad.insert(e); } if ![2, 4].contains(&e) && !g { f += 1; } } } }
    println!("z63top1 fail={} bad e45 values={:?}", f, bad);
    // z63l3: generic l(A1)<=3 via offsets in window {0,1,2} (as sets) and e notin {2,4}: Lemma 5 (3,1,1)
    // h=m (ii.2): offsets (0,1,3): bad (e34, e45)
    let mut bad = std::collections::BTreeSet::new(); let mut incons = 0;
    for a in 0..7 { for p4 in 0..7 { for p5 in 0..7 {
        let g = (0..7).any(|k| ok7(a + k) && ok7(a + 1 + k) && ok7(a + 3 + k) && ok7(p4 + 2 * k) && ok7(p5 + 4 * k));
        if !g { bad.insert((md(2 * a - p4), md(2 * p4 - p5))); } } } }
    for a in 0..7 { for p4 in 0..7 { for p5 in 0..7 {
        let g = (0..7).any(|k| ok7(a + k) && ok7(a + 1 + k) && ok7(a + 3 + k) && ok7(p4 + 2 * k) && ok7(p5 + 4 * k));
        if g == bad.contains(&(md(2 * a - p4), md(2 * p4 - p5))) { incons += 1; } } } }
    println!("h=m (ii.2) offsets (0,1,3): bad (e34,e45) = {:?}; function of (e34,e45) only: {}", bad, incons == 0);
    // escape: for all z, z' some eps1, eps2 in {0,1} with (z - eps1, z' - eps2) not bad
    let mut fe = 0; for z in 0..7 { for zp in 0..7 { if !(0..2).any(|e1| (0..2).any(|e2| !bad.contains(&(md(z - e1), md(zp - e2))))) { fe += 1; } } }
    println!("escape fail={}", fe);
    // table lemmas: qC = 0 normalized; sg = +1 / -1
    for sg in [1i64, -1] { let (mut cnt, mut fl) = (0u64, 0u64);
        for dl in 0..2 { for u in 0..7 { for c3 in 0..2 { if dl == 0 && u == 3 { continue; }
            let y = t63(dl, u, c3); let x = md(3 * u - 2 * y); let z = md(y - x - c3);
            let q45 = if sg == 1 { md(y - dl) } else { md(-(y - dl) - 1) };
            for c1 in 0..2 { for c2 in 0..2 { for c3p in 0..2 { if md(y + c1 - (x + c2 + z + c3p)) != 0 { continue; }
                for ep in -1..=1 { let e = md(q45 + ep); for p4 in 0..7 { cnt += 1;
                    if !(0..7).any(|k| ok7(k) && ok7(y + c1 + k) && ok7(x + c2 + k) && ok7(p4 + 2 * k) && ok7(2 * p4 - e + 4 * k)) { fl += 1; }
                } } } } }
        } } }
        println!("z63tab sg={}: {} cases fail={}", sg, cnt, fl);
    }
    // NC: table with u=4,dl=1 using the other c3 choice
    { let mut fl = 0; let (dl, u) = (1i64, 4i64); for c3 in 0..2 { let y = t63(dl, u, 1 - c3); let x = md(3 * u - 2 * y); let z = md(y - x - c3); let q45 = md(y - dl);
        for c1 in 0..2 { for c2 in 0..2 { for c3p in 0..2 { if md(y + c1 - (x + c2 + z + c3p)) != 0 { continue; }
            for ep in -1..=1 { let e = md(q45 + ep); for p4 in 0..7 {
                if !(0..7).any(|k| ok7(k) && ok7(y + c1 + k) && ok7(x + c2 + k) && ok7(p4 + 2 * k) && ok7(2 * p4 - e + 4 * k)) { fl += 1; } } } } } } }
      println!("NC table (u=4,dl=1 swapped c3) fails={}", fl); }
    // doubled exceptional
    let mut fl = 0; for g1 in 0..2 { for g2 in 0..2 { for g3 in 0..2 { for c1 in 0..2 { for c2 in 0..2 { for ep in -1..=1 { for p4 in 0..7 {
        let e = md(6 + g3 + ep);
        if !(0..7).any(|k| ok7(k) && ok7(6 + g1 + c1 + k) && ok7(6 + g2 + c2 + k) && ok7(p4 + 2 * k) && ok7(2 * p4 - e + 4 * k)) { fl += 1; } } } } } } } }
    println!("z63dbl fail={}", fl);
}
