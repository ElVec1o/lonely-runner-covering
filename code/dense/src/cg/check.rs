// Independent exact checker + Lean emitter (u128). Capacities by brute force over all subsets of each part
// against ALL minimal bad sets; cover and sum re-checked; witnesses re-verified with the goodAt formula.
use crate::edges::*;
pub fn brute_cap(es:&[u128],part:u128)->u32{
    let el:Vec<u32>=(0..128).filter(|b|part>>b&1==1).collect(); let k=el.len(); assert!(k<=24,"part too large for brute force");
    let loc:Vec<u32>=es.iter().filter(|&&e|e&!part==0).map(|&e|{ let mut w=0u32; for (i,&b) in el.iter().enumerate(){ if e>>b&1==1 { w|=1<<i; } } w }).collect();
    let mut best=0; for s in 0u32..(1u32<<k) { let c=s.count_ones(); if c<=best {continue;} if loc.iter().all(|&e| e&!s!=0) { best=c; } } best }
pub fn check_emit(ed:&Edges,parts:&[(u128,u32)],out:&str)->Result<String,String>{
    let m=ed.m as u64; let n=2*m; let t=m+1;
    let full=(1u128<<n)-1; let mut cov=0u128; let mut sum=0u32; let mut maxsz=0;
    for &(u,c) in parts { cov|=u; sum+=c; maxsz=maxsz.max(u.count_ones());
        let b=brute_cap(&ed.es,u); if b!=c {return Err(format!("capacity mismatch part {:x}: brute {} claimed {}",u,b,c));} }
    if cov&full!=full {return Err("not a cover".into());}
    if sum as u64>m-1 {return Err(format!("sum {} > m-1",sum));}
    let used:Vec<usize>=(0..ed.es.len()).filter(|&i| parts.iter().any(|&(u,_)| ed.es[i]&!u==0)).collect();
    for &i in &used { let (p,q)=ed.wit[i]; let (p,q)=(p as u64,q as u64); let mut mask=0u128;
        for x in 1..=n { let r=(x*p)%q; let mn=r.min(q-r); if t*mn<q { mask|=1u128<<(x-1);} }
        if mask!=ed.es[i] {return Err("witness mismatch".into());} }
    let set=|u:u128|->String{ let v:Vec<String>=(1..=n).filter(|x|u>>(x-1)&1==1).map(|x|x.to_string()).collect(); format!("{{{}}}",v.join(",")) };
    let ps:Vec<String>=used.iter().map(|&i|ed.wit[i].0.to_string()).collect();
    let qs:Vec<String>=used.iter().map(|&i|ed.wit[i].1.to_string()).collect();
    let bs:Vec<String>=used.iter().map(|&i|set(ed.es[i])).collect();
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
    std::fs::write(out,s).map_err(|e|e.to_string())?;
    Ok(format!("CHECK OK: {} parts, sum cap {} <= {}, max part size {}, {} witness times, capacities brute-forced against {} minimal bad sets",parts.len(),sum,m-1,maxsz,used.len(),ed.es.len()))
}
