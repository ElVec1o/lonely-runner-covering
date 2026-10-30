// exact check of the witness times of the lemma on the other deletions (c=1):  V = ([n-1] \ {r}) U {mu r}, s=n-r>=2, mu*s <= r+1, n >= 31.
// claim: for every j in V, j != n-1:  ML(V\j) > 1/(n-1), witnessed by R0 / R2 / R4 / R3 as in the proof.
fn isprime(n:u64)->bool{ if n<2 {return false;} let mut d=2; while d*d<=n { if n%d==0 {return false;} d+=1;} true }
fn inv(a:u64,m:u64)->u64{ let (mut t,mut nt,mut r,mut nr)=(0i128,1i128,m as i128,(a%m) as i128);
    while nr!=0 { let q=r/nr; let x=t-q*nt; t=nt; nt=x; let y=r-q*nr; r=nr; nr=y; } (((t%m as i128)+m as i128)%m as i128) as u64 }
fn strict(v:&[u64],j:u64,num:u128,den:u128,n:u64)->bool{ // all x != j : dist/den > 1/(n-1)
    v.iter().filter(|&&x|x!=j).all(|&x|{ let rr=(x as u128*num)%den; let d=rr.min(den-rr); d*((n-1) as u128) > den })
}
fn main(){
    let (mut cnt,mut fail,mut ptest,mut maxbad)=(0u64,0u64,0u64,0usize);
    for n in 31..=140u64 { for s in 2..=n/3 { let r=n-s; for mu in 2..=((r+1)/s) {
        let mut v:Vec<u64>=(1..n).filter(|&x|x!=r).collect(); v.push(mu*r);
        for &j in &v { if j==n-1 {continue;} cnt+=1;
            if j==mu*r { if !strict(&v,j,1,r as u128,n){fail+=1;println!("FAIL R0 n={} s={} mu={}",n,s,mu);} continue; }
            if 2*j>n {
                if (mu*r)%j!=0 { if !strict(&v,j,1,j as u128,n){fail+=1;println!("FAIL R2 n={} s={} mu={} j={}",n,s,mu,j);} }
                else { let d=mu*r/j; assert!(d>mu);
                    // eta = (2mu+1)/(2 mu * (n-1) * mu r);  t = 1/j + eta
                    let den_eta=(2*mu as u128)*((n-1) as u128)*((mu*r) as u128); let num_eta=(2*mu+1) as u128;
                    let den=(j as u128)*den_eta; let num=den_eta+ (j as u128)*num_eta;
                    if !strict(&v,j,num,den,n){fail+=1;println!("FAIL R4 n={} s={} mu={} j={}",n,s,mu,j);} }
                continue; }
            let mut bad=0usize; let lo=n+j; 
            for q in lo..=(2*n-3) { if !isprime(q) {continue;}
                if (mu*r+j)%q==0 || (mu*r+q-j%q)%q==0 { bad+=1; continue; }  // q | mu r + j  or  q | mu r - j
                ptest+=1; let a=inv(j,q);
                if !strict(&v,j,a as u128,q as u128,n){fail+=1;println!("FAIL R3 n={} s={} mu={} j={} q={}",n,s,mu,j,q);} }
            if bad>maxbad {maxbad=bad;}
        } } } }
    println!("removals {} ; R3 primes tested {} ; max bad primes {} ; failures {}",cnt,ptest,maxbad,fail);
}
