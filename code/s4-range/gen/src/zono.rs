// Lattice (zonotope) certificates.  v in Z^4_{>0}, gcd 1.  K = (k1,k2,k3) in Z^4 with det[v,k1,k2,k3] = +-1.
// Statement S(v) follows if for every eps in {+-1}^3 the vertex kappa/2, kappa = sum eps_j k_j, lies in Box + R v,
// Box = [-rho/2, rho/2]^4, rho = 3/5.  (Box+Rv membership of X: for all i<j  |X_j v_i - X_i v_j| <= (rho/2)(v_i+v_j).)
pub type V4 = [i64; 4];
pub type K3 = [[i64; 4]; 3];
const PAIRS: [(usize, usize); 6] = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];
const EPS: [[i64; 3]; 4] = [[1, 1, 1], [1, 1, -1], [1, -1, 1], [1, -1, -1]];

pub struct Rng(pub u64);
impl Rng {
    pub fn next(&mut self) -> u64 { let mut x = self.0; x ^= x << 13; x ^= x >> 7; x ^= x << 17; self.0 = x; x }
    pub fn below(&mut self, n: u64) -> u64 { self.next() % n }
}

pub fn det4(m: [[i64; 4]; 4]) -> i128 {
    // cofactor expansion along first row, i128
    let mut d: i128 = 0;
    for c in 0..4 {
        let mut s = [[0i128; 3]; 3];
        for r in 1..4 { let mut cc = 0; for k in 0..4 { if k == c { continue; } s[r - 1][cc] = m[r][k] as i128; cc += 1; } }
        let det3 = s[0][0] * (s[1][1] * s[2][2] - s[1][2] * s[2][1]) - s[0][1] * (s[1][0] * s[2][2] - s[1][2] * s[2][0]) + s[0][2] * (s[1][0] * s[2][1] - s[1][1] * s[2][0]);
        d += if c % 2 == 0 { 1 } else { -1 } * (m[0][c] as i128) * det3;
    }
    d
}
/// det of the 4x4 matrix whose COLUMNS are v,k1,k2,k3
pub fn det_cols(v: &V4, k: &K3) -> i128 {
    let mut m = [[0i64; 4]; 4];
    for r in 0..4 { m[r][0] = v[r]; for j in 0..3 { m[r][j + 1] = k[j][r]; } }
    det4(m)
}

/// Euclid completion: three vectors k1,k2,k3 with det[v,k1,k2,k3] = +-1 (needs gcd(v)=1)
pub fn completion(v: &V4) -> K3 {
    let mut x = *v;
    let mut minv = [[0i64; 4]; 4];
    for i in 0..4 { minv[i][i] = 1; }
    loop {
        let mut p = usize::MAX;
        for i in 0..4 { if x[i] != 0 && (p == usize::MAX || x[i].abs() < x[p].abs()) { p = i; } }
        let mut done = true;
        for i in 0..4 { if i != p && x[i] != 0 {
            let q = x[i] / x[p];
            x[i] -= q * x[p];
            for r in 0..4 { minv[r][p] += q * minv[r][i]; }
            done = false;
        } }
        if done {
            if p != 0 { x.swap(0, p); for r in 0..4 { minv[r].swap(0, p); } }
            if x[0] < 0 { x[0] = -x[0]; for r in 0..4 { minv[r][0] = -minv[r][0]; } }
            break;
        }
    }
    assert!(x[0] == 1, "gcd != 1");
    for r in 0..4 { assert!(minv[r][0] == v[r], "completion: column 0 != v"); }
    let mut k = [[0i64; 4]; 3];
    for j in 0..3 { for r in 0..4 { k[j][r] = minv[r][j + 1]; } }
    k
}

fn dot(a: &[i64; 4], b: &[i64; 4]) -> i128 { (0..4).map(|i| a[i] as i128 * b[i] as i128).sum() }
fn bq(v: &V4, y: &[i64; 4], z: &[i64; 4]) -> i128 { dot(v, v) * dot(y, z) - dot(y, v) * dot(z, v) }
fn rnd_div(a: i128, b: i128) -> i128 { // nearest integer to a/b, b>0
    let q = a.div_euclid(b); let r = a.rem_euclid(b); if 2 * r > b { q + 1 } else { q }
}
/// pairwise size reduction in the quotient norm (Gram form), then entry normalisation modulo v
pub fn qreduce(v: &V4, k: &mut K3) {
    for _ in 0..200 {
        let mut ch = false;
        for a in 0..3 { for b in 0..3 { if a == b { continue; }
            let nb = bq(v, &k[b], &k[b]); if nb == 0 { continue; }
            let mu = rnd_div(bq(v, &k[a], &k[b]), nb);
            if mu != 0 { for t in 0..4 { k[a][t] -= (mu as i64) * k[b][t]; } ch = true; }
        } }
        // sort by quotient norm
        for _ in 0..2 { for a in 0..2 { if bq(v, &k[a], &k[a]) > bq(v, &k[a + 1], &k[a + 1]) { k.swap(a, a + 1); ch = true; } } }
        if !ch { break; }
    }
    norm_mod_v(v, k);
}
pub fn norm_mod_v(v: &V4, k: &mut K3) {
    let vv = dot(v, v);
    for a in 0..3 { let c = rnd_div(dot(&k[a], v), vv); for t in 0..4 { k[a][t] -= (c as i64) * v[t]; } }
}

/// exact predicate: all 4 sign patterns x 6 pairs satisfy  rq*|kap_j v_i - kap_i v_j| <= rp*(v_i+v_j)    (rho = rp/rq)
pub fn passes(v: &V4, k: &K3, rp: i64, rq: i64) -> bool {
    for e in EPS.iter() {
        let mut kap = [0i128; 4];
        for t in 0..4 { kap[t] = (0..3).map(|j| e[j] as i128 * k[j][t] as i128).sum(); }
        for &(i, j) in PAIRS.iter() {
            let lhs = (rq as i128) * (kap[j] * v[i] as i128 - kap[i] * v[j] as i128).abs();
            if lhs > (rp as i128) * (v[i] + v[j]) as i128 { return false; }
        }
    }
    true
}
/// max over patterns/pairs of |kap_j v_i - kap_i v_j|/(v_i+v_j)  (pass iff <= rho)
pub fn rmax(v: &V4, k: &K3) -> f64 {
    let mut r = 0f64;
    for e in EPS.iter() {
        let mut kap = [0f64; 4];
        for t in 0..4 { kap[t] = (0..3).map(|j| e[j] as f64 * k[j][t] as f64).sum(); }
        for &(i, j) in PAIRS.iter() {
            let x = (kap[j] * v[i] as f64 - kap[i] * v[j] as f64).abs() / (v[i] + v[j]) as f64;
            if x > r { r = x; }
        }
    }
    r
}
pub fn climb(v: &V4, k: &mut K3) -> f64 {
    let mut r = rmax(v, k);
    for _ in 0..500 {
        let mut imp = false;
        for a in 0..3 { for b in 0..3 { if a == b { continue; } for s in [-1i64, 1] {
            let mut k2 = *k; for t in 0..4 { k2[a][t] += s * k[b][t]; }
            let r2 = rmax(v, &k2); if r2 < r - 1e-12 { *k = k2; r = r2; imp = true; }
        } } }
        for a in 0..3 { let b = (a + 1) % 3; let c = (a + 2) % 3; for s1 in [-1i64, 1] { for s2 in [-1i64, 1] {
            let mut k2 = *k; for t in 0..4 { k2[a][t] += s1 * k[b][t] + s2 * k[c][t]; }
            let r2 = rmax(v, &k2); if r2 < r - 1e-12 { *k = k2; r = r2; imp = true; }
        } } }
        if !imp { break; }
    }
    r
}
/// best basis found: (K, r, restarts used)
pub fn best_basis(v: &V4, restarts: usize, rng: &mut Rng) -> (K3, f64, usize) {
    let mut k = completion(v);
    qreduce(v, &mut k);
    let mut r = climb(v, &mut k);
    let mut best = (k, r);
    let mut used = 0;
    while best.1 > 0.6 && used < restarts {
        used += 1;
        let mut k2 = best.0;
        for _ in 0..(2 + rng.below(6)) {
            let a = rng.below(3) as usize; let mut b = rng.below(3) as usize; if b == a { b = (a + 1) % 3; }
            let s = if rng.below(2) == 0 { 1 } else { -1 };
            for t in 0..4 { let x = k2[b][t]; k2[a][t] += s * x; }
        }
        r = climb(v, &mut k2);
        if r < best.1 { best = (k2, r); }
    }
    norm_mod_v(v, &mut best.0);
    (best.0, best.1, used)
}

// ---------- deeper certificate: adaptive dyadic subdivision of the unit cube in K-coordinates, each leaf with an integer shift ----------
pub struct DeepRes { pub resolved: bool, pub leaves: u64, pub depth: u32, pub nodes: u64, pub leaf_list: Vec<(u32, [i64; 3], [i64; 3])> }
pub fn deep(v: &V4, k: &K3, rp: i64, rq: i64, max_nodes: u64, max_depth: u32) -> DeepRes {
    // forms g_ij(y) = sum_l y_l (k_l[j] v_i - k_l[i] v_j)
    let mut g = [[0i64; 3]; 6]; let mut c = [0i64; 6]; let mut g1 = [0i64; 6];
    for (p, &(i, j)) in PAIRS.iter().enumerate() {
        for l in 0..3 { g[p][l] = k[l][j] * v[i] - k[l][i] * v[j]; }
        c[p] = v[i] + v[j]; g1[p] = g[p].iter().map(|x| x.abs()).sum();
    }
    const M: i64 = 4;
    let mut shifts: Vec<([i64; 3], [i64; 6])> = vec![];
    for a in -M..=M { for b in -M..=M { for d in -M..=M {
        let mut gm = [0i64; 6]; for p in 0..6 { gm[p] = g[p][0] * a + g[p][1] * b + g[p][2] * d; }
        shifts.push(([a, b, d], gm));
    } } }
    // sort shifts by |m|_1 to find fits quickly
    shifts.sort_by_key(|s| s.0.iter().map(|x| x.abs()).sum::<i64>());
    let mut res = DeepRes { resolved: true, leaves: 0, depth: 0, nodes: 0, leaf_list: vec![] };
    let mut stack: Vec<(u32, [i64; 3])> = vec![(0, [0, 0, 0])];
    while let Some((d, a)) = stack.pop() {
        res.nodes += 1;
        if res.nodes > max_nodes { res.resolved = false; return res; }
        let s: i64 = 1i64 << (d + 1);
        let cn = [-(1i64 << d) + 2 * a[0] + 1, -(1i64 << d) + 2 * a[1] + 1, -(1i64 << d) + 2 * a[2] + 1];
        let mut gc = [0i64; 6]; for p in 0..6 { gc[p] = g[p][0] * cn[0] + g[p][1] * cn[1] + g[p][2] * cn[2]; }
        let mut fit = false; let mut fm = [0i64; 3];
        'sh: for (mm, gm) in shifts.iter() {
            for p in 0..6 {
                if 2 * (rq as i128) * (((gc[p] + s * gm[p]).abs() + g1[p]) as i128) > (rp as i128) * (c[p] as i128) * (s as i128) { continue 'sh; }
            }
            fit = true; fm = *mm; break;
        }
        if fit { res.leaf_list.push((d, a, fm)); res.leaves += 1; if d > res.depth { res.depth = d; } continue; }
        if d >= max_depth { res.resolved = false; return res; }
        for dx in 0..2 { for dy in 0..2 { for dz in 0..2 { stack.push((d + 1, [2 * a[0] + dx, 2 * a[1] + dy, 2 * a[2] + dz])); } } }
    }
    res
}
