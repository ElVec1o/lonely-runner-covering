fn main(){ let nmax:usize=10_000_000; let lim=2*nmax+10; let mut c=vec![true;lim+1]; c[0]=false;c[1]=false;
 let mut i=2; while i*i<=lim{ if c[i]{ let mut k=i*i; while k<=lim{c[k]=false;k+=i;} } i+=1; }
 let mut pi=vec![0u32;lim+1]; for i in 1..=lim{ pi[i]=pi[i-1]+if c[i]{1}else{0}; }
 let (mut mn,mut at)=(u32::MAX,0); let mut lastbad=0; 
 for n in 33..=nmax{ let cnt=pi[2*n-5]-pi[(3*n)/2]; if cnt<mn{mn=cnt;at=n;} if cnt<3{lastbad=n;} }
 println!("min count over n in [33,1e7] = {} at n={}; largest n>=33 with count<3: {}",mn,at,lastbad);
 let mut b=0; for n in 20..33{ if pi[2*n-5]-pi[(3*n)/2]<3{b=n;} } println!("largest n in [20,32] with count<3: {}",b);
}
