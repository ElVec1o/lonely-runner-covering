// Recomputes the two worked examples of the dense-window paper with exact integer arithmetic.
fn good(x: u64, p: u64, q: u64, m: u64) -> bool {
    let r = (x * p) % q;
    q <= (m + 1) * r.min(q - r)
}
fn bad_set(p: u64, q: u64, m: u64) -> Vec<u64> {
    (1..=2 * m).filter(|&x| !good(x, p, q, m)).collect()
}
fn main() {
    // ---- Example A: m = 4, N = 9, five times, unit weights, D = 1
    let m = 4u64;
    let times: [(u64, u64); 5] = [(1, 5), (1, 10), (1, 4), (1, 3), (4, 9)];
    let bads: Vec<Vec<u64>> = times.iter().map(|&(p, q)| bad_set(p, q, m)).collect();
    println!("A: m=4 floor=1/5");
    for (i, &(p, q)) in times.iter().enumerate() {
        println!("A time {}/{} bad set {:?}", p, q, bads[i]);
    }
    let mut maxload = 0;
    for x in 1..=2 * m {
        let l = bads.iter().filter(|b| b.contains(&x)).count();
        print!("load({})={} ", x, l);
        maxload = maxload.max(l);
    }
    println!("\nA maxload D={} total={} m*D={} ok={}", maxload, times.len(), m * maxload as u64, times.len() as u64 > m * maxload as u64);
    // all 4-subsets of [1,8]
    let mut cnt = 0; let mut minw = 99; let mut allok = true;
    for mask in 0u32..256 {
        if mask.count_ones() != 4 { continue; }
        cnt += 1;
        let v: Vec<u64> = (1..=8).filter(|x| mask >> (x - 1) & 1 == 1).collect();
        let w: Vec<usize> = (0..5).filter(|&j| v.iter().all(|x| !bads[j].contains(x))).collect();
        if w.is_empty() { allok = false; }
        minw = minw.min(w.len());
        if v == vec![1, 3, 4, 7] || v == vec![1, 2, 3, 4] || v == vec![2, 3, 5, 7] || v == vec![1,2,4,8] { println!("A V={:?} witness time indices {:?} -> {:?}", v, w, w.iter().map(|&j| times[j]).collect::<Vec<_>>()); }
    }
    println!("A subsets={} all_have_witness={} min_number_of_witness_times={}", cnt, allok, minw);
    // ---- Example B: m = 10, N = 21, 14 times, 5 parts, capacities 0,0,3,3,3
    let m = 10u64;
    let p = [1u64,1,1,5,12,15,1,7,9,5,1,1,7,5];
    let q = [22u64,11,8,21,25,32,7,22,28,31,9,10,18,22];
    let declared: Vec<Vec<u64>> = vec![vec![1],vec![11],vec![8,16],vec![4,17],vec![2,4],vec![2,15,17],vec![7,14],vec![3,19],vec![3,6],vec![6,12,19],vec![9,18],vec![10,20],vec![5,13,18],vec![9,13]];
    let mut ok = true;
    for j in 0..14 {
        let a = bad_set(p[j], q[j], m);
        let sub = a.iter().all(|x| declared[j].contains(x));
        println!("B time {}/{} actual bad {:?} declared {:?} actual_subset_of_declared={} equal={}", p[j], q[j], a, declared[j], sub, a == declared[j]);
        ok &= sub;
    }
    println!("B all declared sets contain the true bad sets: {}", ok);
    let parts: Vec<Vec<u64>> = vec![vec![1],vec![11],vec![2,4,8,15,16,17],vec![3,6,7,12,14,19],vec![5,9,10,13,18,20]];
    let caps = [0usize,0,3,3,3];
    let mut cover = vec![false; 21];
    for pt in &parts { for &x in pt { cover[x as usize] = true; } }
    println!("B cover of [1,20]: {}  sum caps={} < m={}", (1..=20).all(|x| cover[x]), caps.iter().sum::<usize>(), m);
    for (i, pt) in parts.iter().enumerate() {
        let n = pt.len();
        let mut maxind = 0; let mut witness_ind = vec![];
        let mut allbig_ok = true;
        for mask in 0u32..(1 << n) {
            let s: Vec<u64> = (0..n).filter(|b| mask >> b & 1 == 1).map(|b| pt[b]).collect();
            let contains_bad = declared.iter().any(|d| d.iter().all(|x| s.contains(x)));
            if !contains_bad { if s.len() > maxind { maxind = s.len(); witness_ind = s.clone(); } }
            if s.len() > caps[i] && !contains_bad { allbig_ok = false; }
        }
        println!("B part {:?}: largest subset containing no bad set = {} e.g. {:?}; every subset larger than cap {} contains a bad set: {}", pt, maxind, witness_ind, caps[i], allbig_ok);
    }
    // brute force: all 10-subsets of [1,20] have a witness among the 14 times
    let mut cnt = 0u64; let mut fails = 0u64;
    for mask in 0u32..(1 << 20) {
        if mask.count_ones() != 10 { continue; }
        cnt += 1;
        let hit = |j: usize| (1..=20u64).any(|x| mask >> (x - 1) & 1 == 1 && !good(x, p[j], q[j], m));
        if (0..14).all(hit) { fails += 1; }
    }
    println!("B 10-subsets of [1,20]: {} without witness among the 14 times: {}", cnt, fails);
}
