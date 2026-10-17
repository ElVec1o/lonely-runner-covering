// Consistency check on the Goddyn-Wong tight set {1..29,31,90}, n=32.
// (a) confirm it is lonely at level 1/32 (exhibit an exact witness a/q);
// (b) confirm the general covering bound  minR <= 2k/(ell*(n-2k))  is respected;
// (c) confirm the *unit* bound 2n(n-1)/(n-2) would be VIOLATED, so coprimality is necessary.
fn g(a:u64,b:u64)->u64{ if b==0 {a} else {g(b,a%b)} }
fn main(){
    let n:u64=32;
    let mut v:Vec<u64>=(1..=29).collect(); v.push(31); v.push(90);
    println!("|V| = {} (needs n-1 = {})", v.len(), n-1);
    // exhaustive witness search over t = a/q
    let mut found=None;
    'outer: for q in 2..=20000u64 {
        let red:Vec<u64>=v.iter().map(|x| x%q).collect();
        if red.iter().any(|&r| r==0) { continue; }
        for a in 1..q {
            if g(a,q)!=1 { continue; }
            let mut ok=true;
            for &r in &red { let x=(r*a)%q; let d=if x<q-x {x} else {q-x};
                if n*d < q { ok=false; break; } }
            if ok { found=Some((q,a)); break 'outer; }
        }
    }
    match found {
        Some((q,a))=>{
            let mut worst=f64::MAX;
            for &s in &v { let x=(s%q*a)%q; let d=if x<q-x {x} else {q-x};
                let m=d as f64/q as f64; if m<worst {worst=m;} }
            println!("LONELY: witness t = {}/{},  min||v t|| = {:.8},  1/n = {:.8},  ratio = {:.6}",
                     a,q,worst,1.0/n as f64, worst*n as f64);
        }
        None=>println!("no witness found up to q=20000"),
    }
    let ell = 1.0/2576.0;            // computed exactly by ucomp/locate for U(32,{30})
    let k = 1.0;
    let gen_bound = 2.0*k/(ell*((n as f64)-2.0*k));
    let unit_bound = 2.0*k*(n as f64)*((n as f64)-1.0)/((n as f64)-2.0*k);
    println!("general bound on min R : {:.2}   (actual replacement 90 -> {})",
             gen_bound, if 90.0<=gen_bound {"RESPECTED"} else {"VIOLATED"});
    println!("unit-case bound        : {:.2}   (actual replacement 90 -> {})",
             unit_bound, if 90.0<=unit_bound {"respected"} else {"VIOLATED => coprimality necessary"});
    println!("gcd(30,32) = {}", g(30,32));
}
