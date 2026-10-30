fn main(){ let n=20_000_000usize; let mut s=vec![true;n+1]; s[0]=false; s[1]=false;
 let mut i=2; while i*i<=n { if s[i]{ let mut j=i*i; while j<=n { s[j]=false; j+=i; } } i+=1; }
 let mut pi=0u64; let (mut bl,mut bu)=(0,0); let (mut ml,mut mu_)=(f64::MAX,f64::MAX);
 for x in 2..=n { if s[x]{pi+=1;} let xf=x as f64; 
   if x>=5393 { let b=xf/(xf.ln()-1.0); if (pi as f64)<b {bl+=1;} ml=ml.min(pi as f64-b); }
   if x>=60184 { let b=xf/(xf.ln()-1.1); if (pi as f64)>b {bu+=1;} mu_=mu_.min(b-pi as f64); } }
 println!("x in [5393,2e7]: violations of pi>=x/(ln x-1): {} (min slack {:.1}); x in [60184,2e7]: violations of pi<=x/(ln x-1.1): {} (min slack {:.1})",bl,ml,bu,mu_); }
