// Recount of the case split of Theorem 3 for 4 <= m <= 12 over all subsets of [1,2m] of size <= m:
// case 1: 1 absent; case 2: 1 present and some q in [2,m+1] divides no element; case 3: the rest.
// For case 3 it counts the sets with no c in [1,N-1] such that (m+1)*min(r,N-r) >= N for all elements. Usage: rustc -O case_recount.rs && ./case_recount
fn isprime(n:u64)->bool{ n>1 && (2..n).all(|d|n%d!=0)}
fn main(){
  for m in 4u64..=12 {
    let n=2*m+1; let w=2*m as usize;
    let (mut c1,mut c2,mut c3,mut nw)=(0u64,0u64,0u64,0u64);
    for mask in 1u32..(1u32<<w) {
      if mask.count_ones() as u64>m {continue;}
      if mask&1==0 {c1+=1; continue;}
      let vals:Vec<u64>=(1..=2*m).filter(|&x|mask>>(x-1)&1==1).collect();
      let res=(2..=m+1).all(|q| vals.iter().any(|&x|x%q==0));
      if !res {c2+=1; continue;}
      c3+=1;
      let ok=(1..n).any(|c| vals.iter().all(|&x|{let r=x*c%n; let r2=r.min(n-r); (m+1)*r2>=n}));
      if !ok {nw+=1;}
    }
    println!("m={} N={} prime={} case1={} case2={} case3={} case3_without_c/N={}",m,n,isprime(n),c1,c2,c3,nw);
  }
}
