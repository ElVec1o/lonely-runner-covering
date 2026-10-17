// emit.rs -- independent exact checker + Lean emitter for a cover-capacity certificate.
// usage: emit m sol.txt out.lean   (sol.txt lines: "mask cost"; mask bit x-1 <-> velocity x)
// Checks (exact integers): every part's true capacity (max independent subset w.r.t. ALL minimal bad
// sets, brute force over subsets) == claimed cost; parts cover [1,2m]; sum cost <= m-1.
// Bad sets emitted: exactly the minimal edges contained in some part, with witness p/q re-verified
// against the goodAt formula.
use std::collections::HashSet;
fn gcd(a:u64,b:u64)->u64{ if a==0{b}else{gcd(b%a,a)} }
fn main(){
    let a:Vec<String>=std::env::args().collect(); let m:u64=a[1].parse().unwrap(); let n=2*m; let t=m+1;
    let qmax=2*n*t; let mut seen:std::collections::HashMap<u64,(u64,u64)>=Default::default();
    for q in 1..=qmax { for p in 0..q { if gcd(p,q)!=1 {continue;}
        let mut mask=0u64; let mut r=0u64;
        for x in 1..=n { r+=p; if r>=q {r-=q;} let mn=if r<q-r {r} else {q-r}; if t*mn<q { mask|=1u64<<(x-1);} }
        if mask!=0 { seen.entry(mask).or_insert((p,q)); } }}
    let mut raw:Vec<(u64,(u64,u64))>=seen.into_iter().collect(); raw.sort_by_key(|&(s,(_,q))|(s.count_ones(),q,s));
    let mut es:Vec<(u64,(u64,u64))>=vec![]; for &(s,w) in &raw { if !es.iter().any(|&(u,_)|u&s==u){es.push((s,w));} }
    let sol=std::fs::read_to_string(&a[2]).unwrap();
    let parts:Vec<(u64,u32)>=sol.lines().filter(|l|!l.trim().is_empty()).map(|l|{let mut s=l.split_whitespace(); (s.next().unwrap().parse().unwrap(), s.next().unwrap().parse().unwrap())}).collect();
    let full=(1u64<<n)-1; let mut cov=0u64; let mut sum=0u32;
    for &(u,c) in &parts { cov|=u; sum+=c;
        // brute-force capacity
        let el:Vec<u64>=(0..n).filter(|b|u>>b&1==1).collect(); let k=el.len(); let mut best=0;
        for s in 0u32..(1<<k) { let mut w=0u64; for i in 0..k { if s>>i&1==1 { w|=1u64<<el[i]; } }
            if es.iter().all(|&(e,_)| e&!w!=0) { best=best.max(s.count_ones()); } }
        assert_eq!(best,c,"capacity mismatch for part {:x}",u); }
    assert_eq!(cov&full,full,"not a cover"); assert!(sum as u64<=m-1,"sum {} > m-1",sum);
    eprintln!("CHECK OK: {} parts, sum cap {} <= {}, exact capacities re-verified",parts.len(),sum,m-1);
    // used edges
    let used:Vec<&(u64,(u64,u64))>=es.iter().filter(|(e,_)| parts.iter().any(|&(u,_)| e&!u==0)).collect();
    for (e,(p,q)) in &used { // witness re-verification
        let mut mask=0u64; for x in 1..=n { let r=(x*p)%q; let mn=r.min(q-r); if t*mn<*q { mask|=1u64<<(x-1);} } assert_eq!(mask,*e); }
    let set=|u:u64|->String{ let v:Vec<String>=(1..=n).filter(|x|u>>(x-1)&1==1).map(|x|x.to_string()).collect(); format!("{{{}}}",v.join(",")) };
    let ps:Vec<String>=used.iter().map(|(_,(p,_))|p.to_string()).collect();
    let qs:Vec<String>=used.iter().map(|(_,(_,q))|q.to_string()).collect();
    let bs:Vec<String>=used.iter().map(|(e,_)|set(*e)).collect();
    let us:Vec<String>=parts.iter().map(|&(u,_)|set(u)).collect();
    let cs:Vec<String>=parts.iter().map(|&(_,c)|c.to_string()).collect();
    let k=m-1;
    let s=format!(r#"set_option maxHeartbeats 8000000 in
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
"#,m=m,q=2*m+1,n=n,t=t,k=k,np=parts.len(),nb=used.len(),sum=sum,ps=ps.join(","),qs=qs.join(","),bs=bs.join(","),us=us.join(","),cs=cs.join(","));
    std::fs::write(&a[3],s).unwrap();
}
