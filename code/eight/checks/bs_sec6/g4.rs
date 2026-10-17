// G4 reduction check. For every 5-tuple of residues in Z7^*, after sign flips
// into {1,2,4}, some base b in {1,2,4} gives a relative class-count pattern (n_b,n_2b,n_4b)
// among the six Section 6 statements. Negative control: drop one pattern.
fn main() {
    let allowed_full: Vec<[u32;3]> = vec![[5,0,0],[4,1,0],[4,0,1],[3,2,0],[3,0,2],[3,1,1],[2,2,1]];
    for drop in 0..=allowed_full.len() {
        let allowed: Vec<[u32;3]> = allowed_full.iter().enumerate().filter(|(i,_)| *i!=drop).map(|(_,x)|*x).collect();
        let mut fails = 0u32; let mut total = 0u32;
        for code in 0..7776u32 {
            let mut c = code; let mut cnt = [0u32;7];
            for _ in 0..5 { let r = c%6+1; c/=6; let f = if [1,2,4].contains(&r) {r} else {7-r}; cnt[f as usize]+=1; }
            total+=1;
            let ok = [1u32,2,4].iter().any(|&b| { let p=[cnt[b as usize],cnt[(2*b%7) as usize],cnt[(4*b%7) as usize]]; allowed.contains(&p)});
            if !ok { fails+=1; }
        }
        if drop==allowed_full.len() { println!("FULL: {} tuples, {} failures", total, fails); }
        else { println!("NC drop {:?}: {} failures", allowed_full[drop], fails); }
    }
}
