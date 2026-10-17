// Class form of the pair lemma (Theorem 3, Lemma 4). For prime N = 2m+1, m <= 9, every subset of [1,2m] of size <= m:
// if it contains x and N-x, it meets at most m-1 classes {s,N-s}, and for the least missed s the time c/N, c = s^-1 mod N,
// has (m+1)*min(r,N-r) >= N for every element. Negative control: sets without such a pair that meet all classes admit no c.
// Also controls ML(1..5)=1/6, ML(1,3,4,7)=1/5, ML(1)=1/2, ML(1,2)=1/3 (exact). Usage: rustc -O class_check.rs && ./class_check
// Exact check of the BP-form proof of Lemma 4 (missed class s, c = s^{-1} mod N).
fn gcd(a:u64,b:u64)->u64{if b==0{a}else{gcd(b,a%b)}}
fn ml(v:&[u64])->(u64,u64){ // exact ML as fraction (num,den)
    let mut ds=vec![];
    for i in 0..v.len(){for j in i..v.len(){ds.push(v[i]+v[j]); if v[i]>v[j]{ds.push(v[i]-v[j]);} else if v[j]>v[i]{ds.push(v[j]-v[i]);}}}
    ds.sort();ds.dedup();
    let mut best=(0u64,1u64);
    for &d in &ds{ if d==0{continue;} for a in 0..d{
        let mut mn=(d,1u64); // as fraction r/d: store numerator, den d
        let mut m=d;
        for &x in v{let r=(x*a)%d; let r=r.min(d-r); if r<m{m=r;}}
        let _=&mut mn;
        // compare m/d with best
        if m*best.1>best.0*d{best=(m,d);}
    }}
    let g=gcd(best.0,best.1); (best.0/g,best.1/g)
}
fn inv(s:u64,n:u64)->u64{ for c in 1..n{ if s*c%n==1{return c;} } 0 }
fn isprime(n:u64)->bool{ n>1 && (2..n).all(|d|n%d!=0)}
fn main(){
    // negative controls
    assert_eq!(ml(&[1,2,3,4,5]),(1,6)); assert_eq!(ml(&[1,3,4,7]),(1,5));
    assert_eq!(ml(&[1]),(1,2)); assert_eq!(ml(&[1,2]),(1,3));
    println!("controls ML(1..5)=1/6, ML(1,3,4,7)=1/5, ML(1)=1/2, ML(1,2)=1/3 OK");
    for m in 2u64..=9 {
        let n=2*m+1; if !isprime(n){continue;}
        let mut total=0u64; let mut withpair=0u64; let mut fail_missed=0u64; let mut fail_witness=0u64;
        let mut ctrl_all_classes=0u64; let mut ctrl_has_c=0u64;
        for mask in 1u32..(1u32<<(2*m)) {
            if mask.count_ones() as u64 > m {continue;}
            total+=1;
            let has=|x:u64|->bool{ mask>>(x-1)&1==1 };
            let vals:Vec<u64>=(1..=2*m).filter(|&x|has(x)).collect();
            let pair=vals.iter().any(|&x| x<n && has(n-x));
            // classes met
            let mut met=vec![false;(m+1) as usize];
            for &x in &vals{ let s=x.min(n-x); met[s as usize]=true; }
            let all_met=(1..=m).all(|s|met[s as usize]);
            if pair{
                withpair+=1;
                match (1..=m).find(|&s|!met[s as usize]){
                    None=>{fail_missed+=1;}
                    Some(s)=>{ let c=inv(s,n);
                        let ok=vals.iter().all(|&x|{let r=x*c%n; let r2=r.min(n-r); (m+1)*r2>=n});
                        if !ok{fail_witness+=1;} }
                }
            } else if all_met {
                // negative control: any c at all with all residues min>=2?
                ctrl_all_classes+=1;
                let any=(1..n).any(|c| vals.iter().all(|&x|{let r=x*c%n; let r2=r.min(n-r); r2>=2}));
                if any{ctrl_has_c+=1;}
            }
        }
        println!("m={} N={} subsets(size<=m)={} with_pair={} missed_class_absent={} witness_fail={} | control(no pair, all classes met): sets={} having_c={}",m,n,total,withpair,fail_missed,fail_witness,ctrl_all_classes,ctrl_has_c);
    }
}
