// Can an exact bad set properly contain a DBL pair {a, 2a} with 3a > 2m?
//
// The reduction of SizeTwoReduction says a hypothetical exact bad set with a + b > 2m and a third
// member must have b = 2a and 3a > 2m, i.e. it is a DBL pair plus an extra element. And 3a > 2m is
// exactly DBL's own first disjunct, so the question is whether a DBL pair of that kind extends.
// Checking directly is far sharper than checking a + b > 2m in general.
fn g(a:i64,b:i64)->i64{ if b==0 {a.abs()} else {g(b,a%b)} }
fn main(){
    let mhi: i64 = std::env::args().nth(1).and_then(|s|s.parse().ok()).unwrap_or(150);
    let (mut pairs, mut ext) = (0usize, 0usize);
    let mut ex: Vec<(i64,i64,i64,Vec<i64>)> = vec![];
    for m in 2..=mhi {
        let t = m+1;
        for q in 1..=(2*m+2) {
            for p in 1..q {
                if g(p,q)!=1 { continue; }
                let s: Vec<i64> = (1..=2*m).filter(|&x| {
                    let r=(x*p).rem_euclid(q); let d=r.min(q-r); d*t < q }).collect();
                if s.len() < 2 { continue; }
                let a = s[0];
                // does the set contain the DBL pair {a, 2a} with 3a > 2m as its two smallest?
                if s[1] != 2*a { continue; }
                if 3*a <= 2*m { continue; }
                pairs += 1;
                if s.len() > 2 { ext += 1; if ex.len()<10 { ex.push((m,p,q,s.clone())); } }
            }
        }
    }
    println!("m in 2..{}", mhi);
    println!("  exact sets whose two smallest are a DBL pair with 3a > 2m : {}", pairs);
    println!("  of those, sets with a THIRD member                        : {}", ext);
    for (m,p,q,s) in ex.iter(){ println!("    m={} t={}/{} {:?}", m,p,q,s); }
    if ext==0 && pairs>0 {
        println!("  => such a pair NEVER extends. The open lemma holds on this range, and the");
        println!("     hypothesis is non-vacuous: {} pairs of the relevant kind occur.", pairs);
    }
}
