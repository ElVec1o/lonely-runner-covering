// Z7 claims for Section 6.6.
fn ok7(v: i64) -> bool { let v = v.rem_euclid(7); v != 0 && v != 6 }
fn main() {
    let md = |x: i64| x.rem_euclid(7);
    // (15): offsets o1, o2 in {6,0,1}
    let (mut f, mut nc) = (0, 0);
    for a in 0..7 { for o1 in 0..7 { for b in 0..7 { for o2 in 0..7 { for c in 0..7 {
        let g = (0..7).any(|k| ok7(a + k) && ok7(a + o1 + k) && ok7(b + 2 * k) && ok7(b + o2 + 2 * k) && ok7(c + 4 * k));
        let inn = |o: i64| o == 6 || o == 0 || o == 1;
        if inn(o1) && inn(o2) { if !g { f += 1; } } else if inn(o1) && o2 == 2 && !g { nc += 1; }
    } } } } }
    println!("z66_15 fail={} | NC(o2=2) fails={}", f, nc);
    // (a): A1 offsets {0,2}, A2 offsets {0,1}; a = 2q2 - q4, b = 2q5 - q2
    let fa = |q2: i64, q4: i64, q5: i64| (0..7).any(|k| ok7(q2 + k) && ok7(q2 + 2 + k) && ok7(q4 + 2 * k) && ok7(q4 + 1 + 2 * k) && ok7(q5 + 4 * k));
    let fb = |q2: i64, q4: i64, q5: i64| (0..7).any(|k| ok7(q2 + k) && ok7(q2 + 1 + k) && ok7(q4 + 2 * k) && ok7(q4 + 2 + 2 * k) && ok7(q5 + 4 * k));
    let (mut za, mut za5, mut za6, mut zb, mut nca, mut ncb) = (0, 0, 0, 0, 0, 0);
    let mut bada = std::collections::BTreeSet::new(); let mut badb = std::collections::BTreeSet::new();
    for q2 in 0..7 { for q4 in 0..7 { for q5 in 0..7 {
        let a = md(2 * q2 - q4); let b = md(2 * q5 - q2);
        if !fa(q2, q4, q5) { bada.insert((a, b)); }
        if !fb(q2, q4, q5) { badb.insert((a, b)); }
        if ![4, 5, 6].contains(&a) && !fa(q2, q4, q5) { za += 1; }
        if (a == 5 || a == 4) && ![2, 4].contains(&b) && !fa(q2, q4, q5) { za5 += 1; }
        if (a == 6 || a == 5) && ![4, 6].contains(&b) && !fa(q2, q4, q5) { za6 += 1; }
        if ![2, 4].contains(&a) && !fb(q2, q4, q5) { zb += 1; }
        if ![5, 6].contains(&a) && !fa(q2, q4, q5) { nca += 1; }
        if ![2].contains(&a) && !fb(q2, q4, q5) { ncb += 1; }
    } } }
    println!("(a) bad (a,b) = {:?}", bada);
    println!("(b) bad (a,b) = {:?}", badb);
    println!("zA fail={} zA5 fail={} zA6 fail={} zB fail={} | NC(a notin {{5,6}}) fails={} NC(b: a!=2) fails={}", za, za5, za6, zb, nca, ncb);
}
