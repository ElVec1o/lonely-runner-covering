// Verbatim copy of type U, gcd, ml from the reference routine ml_standard.rs (lines 15-38) of the author's audit directory; only this comment line differs.
type U = u128;
fn gcd(a: U, b: U) -> U { let (mut a, mut b) = (a, b); while b != 0 { let t = a % b; a = b; b = t; } a }
/// Exact ML as a reduced fraction (num, den) together with one maximiser t = k/L (not reduced).
pub fn ml(v: &[u64]) -> ((U, U), (U, U)) {
    assert!(!v.is_empty() && v.iter().all(|&x| x > 0), "speeds must be positive integers");
    let (mut bn, mut bd): (U, U) = (0, 1);
    let mut arg: (U, U) = (0, 1);
    let mut ls: Vec<U> = Vec::new();
    for i in 0..v.len() { for j in i..v.len() { ls.push(v[i] as U + v[j] as U); } }
    ls.sort(); ls.dedup();
    for &l in &ls {
        for k in 0..l {                       // every numerator, no gcd filter, no symmetry shortcut
            let mut m = l;                    // min distance, in units of 1/l
            for &x in v {
                let r = (x as U * k) % l;
                let d = if r < l - r { r } else { l - r };
                if d < m { m = d; if m * bd <= bn * l { break; } }   // cannot beat the incumbent
            }
            if m * bd > bn * l { bn = m; bd = l; arg = (k, l); }
        }
    }
    let g = gcd(bn, bd).max(1);
    ((bn / g, bd / g), arg)
}
