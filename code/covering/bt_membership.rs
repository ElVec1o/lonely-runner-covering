// Rule 3 check before formalizing: is every small bad set one of the predicted families?
//
// The third SUM branch carries `3(m+1) < 2a+3b`, added 2026-09-03. Without it the branch admits sets
// whose smallest member is not bad: a has residue 3 at modulus 2a+3b, so a is bad only when 3t < q,
// and the other branch-3 conditions give merely 2a+3b > 3m+1. bt_branch3_check finds 38 such sets
// below m = 60. The condition is needed for REALIZABILITY, the direction thm:fam63 depends on;
// adding it makes the test below stricter and it still reports zero counterexamples.
//
// Threshold T = m+1. At time p/q, x in [1,2m] is bad iff min(r, q-r) * T < q with r = x p mod q.
// The classification predicts the exact bad sets of size 1, 2 and 3. Before any of that goes into
// Lean, the weaker but fully checkable statement is tested here: for every m in range and every
// p/q with q <= 2m+2, if the bad set has size 1, 2 or 3 then it lies in one of the predicted
// families. A single counterexample kills the formalization plan before it is written.
fn g(a:i64,b:i64)->i64{ if b==0 {a.abs()} else {g(b,a%b)} }
fn xs(a:i64,m:i64)->i64{ for x in (2*m-a+1)..=(2*m) { if g(x,a)==1 { return x; } } i64::MAX }
fn predicted(s:&[i64], m:i64)->bool{
    match s.len() {
        1 => s[0]==1 || s[0]==m+1,
        2 => { let (a,b)=(s[0],s[1]);
               let cmp = (a+b==2*m+1 || a+b==2*m+2) && g(a,a+b)==1;
               let dbl = b==2*a && a<=m && (3*a>2*m || xs(a,m)<=3*(m+1-a));
               cmp||dbl }
        3 => { let (a,b,c)=(s[0],s[1],s[2]);
               let sum = c==a+b && b!=2*a && c<=2*m && g(a,b)==1 && (
                   (2*a+b>2*m && a+b>m+1) ||
                   (2*a+b<=2*m && b>=m+1 && a+2*b<=3*m+3) ||
                   (2*a+b<=2*m && b<=m && a+2*b>2*m && 2*a+3*b<=4*m+4 && a+b>m+1 && 3*(m+1)<2*a+3*b));
               let dbl3 = b==2*a && c!=3*a && c<=2*m && g(a,c)==1 && a+c>2*m && 2*a+c>2*m+2
                          && (3*a>2*m || 2*a+c<=3*m+3);
               let chn = b==2*a && c==3*a && 3*a<=2*m && (4*a>2*m || xs(a,m)<=4*(m+1-a));
               sum||dbl3||chn }
        _ => false,
    }
}
fn main(){
    let mlo: i64 = std::env::args().nth(1).and_then(|s|s.parse().ok()).unwrap_or(2);
    let mhi: i64 = std::env::args().nth(2).and_then(|s|s.parse().ok()).unwrap_or(60);
    let (mut tested, mut bad) = (0usize, 0usize);
    let mut ex: Vec<(i64,i64,i64,Vec<i64>)> = vec![];
    for m in mlo..=mhi {
        let t = m+1;
        for q in 1..=(2*m+2) {
            for p in 1..q {
                if g(p,q)!=1 { continue; }
                let s: Vec<i64> = (1..=2*m).filter(|&x| {
                    let r=(x*p).rem_euclid(q); let d=r.min(q-r); d*t < q }).collect();
                if s.is_empty() || s.len()>3 { continue; }
                tested += 1;
                if !predicted(&s,m) { bad += 1; if ex.len()<8 { ex.push((m,p,q,s.clone())); } }
            }
        }
    }
    println!("m in {}..{}   small bad sets tested : {}", mlo, mhi, tested);
    println!("  NOT in a predicted family : {}", bad);
    for (m,p,q,s) in ex.iter(){ println!("    m={} t={}/{}  bad set {:?}", m, p, q, s); }
    if bad==0 { println!("  => every small bad set is predicted; the Lean check is worth writing"); }
}
