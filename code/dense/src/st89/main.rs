// Independent exact check of Statements 8 and 9 of paper/dense-window (brute force over all pairs (T,L), |T|<=k).
// Usage: st89 control | st89 run M K | st89 s0 M      (M <= 31 for run; M <= 64 for s0). Own code; no shared source with the other programs.
use std::collections::{HashMap,HashSet};
use std::env;

fn gcd(a:u128,b:u128)->u128{ if b==0 {a} else {gcd(b,a%b)} }

// ---------- exact ML by candidate times k/D, D in {2v_i, v_i+v_j, |v_i-v_j|}  (all k in [0,D)) ----------
fn ml(v:&[u128])->(u128,u128){
    let mut cands:HashSet<u128>=HashSet::new();
    for i in 0..v.len(){ cands.insert(2*v[i]); for j in i+1..v.len(){ cands.insert(v[i]+v[j]); if v[i]!=v[j]{ cands.insert(if v[i]>v[j]{v[i]-v[j]}else{v[j]-v[i]}); } } }
    let (mut bn,mut bd)=(0u128,1u128);
    for &d in &cands { for k in 0..d {
        let mut mn=d; // gap*d
        for &x in v { let r=(x*k)%d; let q=r.min(d-r); if q<mn {mn=q;} }
        if mn*bd > bn*d { bn=mn; bd=d; }
    } }
    let g=gcd(bn,bd); (bn/g,bd/g)
}

// ---------- minimal bad sets of the window [1,2m] at level 1/(m+1): bit x-1 for velocity x ----------
fn bad_mask(m:u64,n:u128,d:u128)->u64{
    let mut b=0u64;
    for x in 1..=2*m { let r=(x as u128*n)%d; let q=r.min(d-r); if q*((m+1) as u128) < d { b|=1u64<<(x-1); } }
    b
}
fn edges(m:u64)->Vec<u64>{
    let mut bp:Vec<(u128,u128)>=vec![(0,1),(1,1)];
    for x in 1..=2*m { for k in 0..=x {
        let den=((m+1)*x) as u128;
        for s in [-1i128,1i128]{ let num=(k*(m+1)) as i128 + s; if num>=0 && num<=den as i128 { bp.push((num as u128,den)); } }
    } }
    bp.sort_by(|a,b| (a.0*b.1).cmp(&(b.0*a.1)));
    bp.dedup_by(|a,b| a.0*b.1==b.0*a.1);
    let mut set:HashSet<u64>=HashSet::new();
    for i in 0..bp.len(){
        set.insert(bad_mask(m,bp[i].0,bp[i].1));
        if i+1<bp.len(){ let (n1,d1)=bp[i]; let (n2,d2)=bp[i+1]; set.insert(bad_mask(m,n1*d2+n2*d1,2*d1*d2)); }
    }
    assert!(!set.contains(&0),"empty bad set");
    let mut all:Vec<u64>=set.into_iter().collect(); all.sort_by_key(|x|(x.count_ones(),*x));
    let mut min:Vec<u64>=vec![];
    for b in all { if !min.iter().any(|&e| e&!b==0) { min.push(b); } }
    min
}

// ---------- alpha: largest subset of avail containing no edge ----------
fn alpha(avail:u64,es:&[u64])->u32{
    let mut best_e=0u64; let mut bc=99;
    for &e in es { if e&!avail==0 { let c=e.count_ones(); if c<bc {bc=c;best_e=e;} } }
    if best_e==0 { return avail.count_ones(); }
    let mut best=0; let mut r=best_e;
    while r!=0 { let b=r&r.wrapping_neg(); r^=b; let a=alpha(avail&!b,es); if a>best {best=a;} }
    best
}
// tau by direct enumeration of subsets (control for the identity alpha+tau=|S|)
fn tau_direct(s:u64,es:&[u64])->u32{
    let loc:Vec<u64>=es.iter().cloned().filter(|e| e&!s==0).collect();
    let mut sub=s; let mut best=s.count_ones();
    loop { if loc.iter().all(|e| e&sub!=0) { let c=sub.count_ones(); if c<best {best=c;} }
        if sub==0 {break;} sub=(sub-1)&s; }
    best
}

fn submasks(t:u64)->Vec<u64>{ let mut v=vec![]; let mut s=t; loop { v.push(s); if s==0 {break;} s=(s-1)&t; } v }

fn cover_exists(fam:&[(u64,u64)],lowp:u64,tallowed:u64)->bool{
    // blocks with (T subset tallowed); cover lowp by blocks with pairwise disjoint T
    let f:Vec<(u64,u64)>=fam.iter().cloned().filter(|b| b.0&!tallowed==0).collect();
    let mut failed:HashSet<(u64,u64)>=HashSet::new();
    fn dfs(f:&[(u64,u64)],lowp:u64,cov:u64,used:u64,failed:&mut HashSet<(u64,u64)>)->bool{
        if cov&lowp==lowp {return true;}
        if failed.contains(&(cov,used)) {return false;}
        // branch on uncovered low with fewest candidates
        let mut bestl=0u64; let mut bestc=usize::MAX; let mut r=lowp&!cov;
        while r!=0 { let b=r&r.wrapping_neg(); r^=b;
            let c=f.iter().filter(|x| x.1&b!=0 && x.0&used==0).count();
            if c<bestc {bestc=c;bestl=b;} if c==0 {break;} }
        if bestc==0 { failed.insert((cov,used)); return false; }
        for x in f { if x.1&bestl!=0 && x.0&used==0 {
            if dfs(f,lowp,cov|x.1,used|x.0,failed) {return true;} } }
        failed.insert((cov,used)); false }
    dfs(&f,lowp,0,0,&mut failed)
}

fn main(){
    let a:Vec<String>=env::args().collect();
    match a[1].as_str() {
        "control" => {
            let v=[1u128,2,3,4,5]; let r=ml(&v); println!("ML(1,2,3,4,5) = {}/{}",r.0,r.1); assert_eq!(r,(1,6));
            let r=ml(&[1,3,4,7]); println!("ML(1,3,4,7) = {}/{}",r.0,r.1); assert_eq!(r,(1,5));
            let r=ml(&[1,2,4,6]); println!("ML(1,2,4,6) = {}/{}",r.0,r.1); assert_eq!(r,(1,4));
            // edges vs ML: V transversal of minimal bad sets  <=>  ML(V) < 1/(m+1)
            for m in 3..=8u64 {
                let es=edges(m); let mut n=0; let mut bad=0;
                // all m-subsets of [1,2m] and the (m+1)-set {1..m+1}
                for s in 0u64..(1u64<<(2*m)) { if s.count_ones() as u64!=m {continue;} n+=1;
                    let trans=es.iter().all(|e| e&s!=0);
                    let vs:Vec<u128>=(0..2*m).filter(|i| s>>i&1==1).map(|i|(i+1) as u128).collect();
                    let r=ml(&vs); let lt = r.0*((m+1) as u128) < r.1;
                    if trans!=lt {bad+=1;}
                    if trans {println!("transversal of size m found m={} {:?}",m,vs);} }
                let s=(1u64<<(m+1))-1; let vs:Vec<u128>=(1..=m+1).map(|x|x as u128).collect(); let r=ml(&vs);
                println!("m={} edges={} m-subsets={} mismatches(edge-hit vs ML<1/(m+1))={} ; control {{1..m+1}} transversal={} ML={}/{}",m,es.len(),n,bad,es.iter().all(|e| e&s!=0),r.0,r.1);
                assert_eq!(bad,0); assert!(es.iter().all(|e| e&s!=0));
            }
        }
        "run" => {
            let m:u64=a[2].parse().unwrap(); let kmax:u32=a[3].parse().unwrap();
            let es=edges(m);
            let lowb=(1u64<<(m+1))-1; // velocities 1..m+1
            let yb=((1u64<<(2*m))-1)&!lowb;
            let ysing=es.iter().filter(|&&e| e&!yb==0).count();
            let single:Vec<u32>=es.iter().filter(|e| e.count_ones()==1).map(|e| e.trailing_zeros()+1).collect();
            println!("m={} minimal bad sets={} Y-contained edges={} singleton edges at velocities {:?}",m,es.len(),ysing,single);
            // low' = velocities 2..m
            let lowp=((1u64<<m)-1)&!1u64; // bits 1..m-1 = velocities 2..m
            let ys:Vec<u32>=(0..2*m as u32).filter(|i| yb>>i&1==1).collect();
            let lowl:Vec<u32>=(0..m as u32).filter(|i| lowp>>i&1==1).collect();
            // enumerate T
            let mut ts:Vec<u64>=vec![0];
            { fn rec(ys:&[u32],from:usize,t:u64,k:u32,kmax:u32,out:&mut Vec<u64>){ if k==kmax {return;} for i in from..ys.len(){ let t2=t|1u64<<ys[i]; out.push(t2); rec(ys,i+1,t2,k+1,kmax,out);} } rec(&ys,0,0,0,kmax,&mut ts); }
            let mut valid_by_t:HashMap<u64,Vec<u64>>=HashMap::new(); let mut vset:HashSet<(u64,u64)>=HashSet::new();
            let mut npairs=0u64; let mut nvalid=0u64; let mut taudiff=0u64;
            let nl=lowl.len();
            for &t in &ts {
                let et:Vec<u64>=es.iter().cloned().filter(|e| e&!(t|lowp)==0).collect();
                for lm in 0u64..(1u64<<nl) {
                    let mut l=0u64; for i in 0..nl { if lm>>i&1==1 { l|=1u64<<lowl[i]; } }
                    npairs+=1;
                    let s=t|l; let loc:Vec<u64>=et.iter().cloned().filter(|e| e&!s==0).collect();
                    let al=alpha(s,&loc); let tau=s.count_ones()-al;
                    let ok = tau >= l.count_ones();
                    if ok { nvalid+=1; valid_by_t.entry(t).or_default().push(l); vset.insert((t,l));
                        // paper definition tau==|L| : check equals (L hits all local edges when Y independent)
                        if tau!=l.count_ones() {taudiff+=1;} }
                    if npairs%1_000_003==0 && s.count_ones()<=9 { assert_eq!(tau,tau_direct(s,&es)); }
                }
            }
            println!("pairs (T,L), |T|<={}: {} ; valid (tau>=|L|): {} ; of which tau>|L|: {}",kmax,npairs,nvalid,taudiff);
            let nvalid_nonempty_t = vset.iter().filter(|x| x.0!=0).count();
            println!("valid with T nonempty: {}  with T empty: {}",nvalid_nonempty_t,nvalid as usize-nvalid_nonempty_t);
            let pairs_nz = npairs - (1u64<<nl) - (ts.len() as u64 - 1);
            let valid_nz = vset.iter().filter(|x| x.0!=0 && x.1!=0).count();
            println!("pairs with T and L both nonempty: {} ; valid among them: {}",pairs_nz,valid_nz);
            // kept
            let mut kept:Vec<(u64,u64)>=vec![];
            for (&t,ls) in &valid_by_t { for &l in ls {
                let maximal = !ls.iter().any(|&l2| l2!=l && l2&l==l);
                if !maximal {continue;}
                let tmin = !submasks(t).iter().any(|&t2| t2!=t && vset.contains(&(t2,l)));
                if tmin { kept.push((t,l)); } } }
            kept.sort();
            println!("kept blocks: {}",kept.len());
            // Statement 8: every valid block dominated by a kept one
            let mut undom=0u64;
            for &(t0,l0) in &vset { if !kept.iter().any(|&(t,l)| t&!t0==0 && l0&!l==0) { undom+=1; } }
            println!("Statement 8: valid blocks not dominated by a kept block: {}",undom);
            // negative control: delete one kept block
            if kept.len()>0 { let k0=kept[kept.len()/2]; let rest:Vec<(u64,u64)>=kept.iter().cloned().filter(|&b| b!=k0).collect();
                let u2=vset.iter().filter(|&&(t0,l0)| !rest.iter().any(|&(t,l)| t&!t0==0 && l0&!l==0)).count();
                println!("control (one kept block deleted): undominated valid blocks = {} (must be >=1)",u2); assert!(u2>=1); }
            // Statement 9
            let reducible=|t:u64,l:u64|->bool{
                if t.count_ones()<2 || l.count_ones()<2 {return false;}
                for t1 in submasks(t) { if t1==0 || t1==t {continue;} let t2=t&!t1;
                    for l1 in submasks(l) { if l1==0 || l1==l {continue;} let l2=l&!l1;
                        if vset.contains(&(t1,l1)) && vset.contains(&(t2,l2)) {return true;} } }
                false };
            for variant in 0..2 {
                let fam:Vec<(u64,u64)>=kept.iter().cloned().filter(|b| variant==0 || b.0!=0).collect();
                let red:Vec<(u64,u64)>=fam.iter().cloned().filter(|&(t,l)| !reducible(t,l)).collect();
                let cf=cover_exists(&fam,lowp,yb); let cr=cover_exists(&red,lowp,yb);
                // local lemma: for every block B in fam, L(B) is coverable by irreducible blocks with T inside T(B)
                let mut locfail=0u64; for &(t,l) in &fam { if l!=0 && !cover_exists(&red,l,t) { locfail+=1; } }
                println!("variant {} (T=empty {}): |F|={} |R|={} cover(F)={} cover(R)={} local-lemma failures={}",variant,if variant==0 {"allowed"} else {"excluded"},fam.len(),red.len(),cf,cr,locfail);
                assert_eq!(cf,cr);
                // control: a wrong reduction (drop every block with |T|>=2) must be able to change the answer or the local lemma
                let wrong:Vec<(u64,u64)>=fam.iter().cloned().filter(|b| b.0.count_ones()<=1).collect();
                let cw=cover_exists(&wrong,lowp,yb);
                println!("   control (drop blocks with |T|>=2): cover={}",cw);
            }
        }
        "s0" => {
            // singleton minimal bad sets inside Low' = {2..m}: velocities x with a time t having B(t)={x}; u128 masks, m<=64
            let m:u64=a[2].parse().unwrap(); assert!(2*m<=128);
            let mut bp:Vec<(u128,u128)>=vec![(0,1),(1,1)];
            for x in 1..=2*m { for k in 0..=x { let den=((m+1)*x) as u128;
                for s in [-1i128,1i128]{ let num=(k*(m+1)) as i128+s; if num>=0 && num<=den as i128 { bp.push((num as u128,den)); } } } }
            bp.sort_by(|a,b| (a.0*b.1).cmp(&(b.0*a.1))); bp.dedup_by(|a,b| a.0*b.1==b.0*a.1);
            let mut sing:HashSet<u64>=HashSet::new();
            let chk=|n:u128,d:u128,sing:&mut HashSet<u64>|{ let mut cnt=0; let mut who=0u64;
                for x in 1..=2*m { let r=(x as u128*n)%d; let q=r.min(d-r); if q*((m+1) as u128)<d { cnt+=1; who=x; if cnt>1 {return;} } }
                if cnt==1 { sing.insert(who); } };
            for i in 0..bp.len(){ chk(bp[i].0,bp[i].1,&mut sing);
                if i+1<bp.len(){ let (n1,d1)=bp[i]; let (n2,d2)=bp[i+1]; chk(n1*d2+n2*d1,2*d1*d2,&mut sing); } }
            let mut v:Vec<u64>=sing.into_iter().collect(); v.sort();
            println!("m={} velocities x in [1,2m] with a singleton bad set {{x}}: {:?}",m,v);
        }
        _=>{}
    }
}
