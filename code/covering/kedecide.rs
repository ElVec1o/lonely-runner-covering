// kedecide -- decide the KOENIG-EGERVARY property of the bad-pair graph exactly, per m.
//
// G is Koenig-Egervary iff its minimum vertex cover equals its maximum matching, rho = nu.  Testing
// that needs no independence-number computation, which would be exponential.  Fix a maximum
// matching M.  Any vertex cover of size |M| must contain exactly one endpoint of each M-edge and no
// M-exposed vertex, because the |M| edges are disjoint and already consume the whole budget.  So
// introduce one boolean per M-edge {u,v}, true meaning "u is in the cover", and require every edge
// of G to be covered:
//     edge between two matched vertices -> a 2-clause;
//     edge with one endpoint exposed    -> a unit clause on the matched endpoint;
//     edge between two exposed vertices -> impossible, M would not be maximum.
// That is 2-SAT, decided in linear time by implication-graph SCCs.  SATISFIABLE iff G is
// Koenig-Egervary, and the assignment is an explicit minimum vertex cover, whose complement is a
// maximum independent set: the answer certifies itself in the positive direction.
//
// Bad pairs come from the O(m^3) breakpoint sweep.  Maximum matching is Edmonds' blossom algorithm,
// lifted verbatim from gedm2.rs so the two tools share a tested implementation.
//
// Usage:  kedecide mlo mhi
// Build:  rustc -O -o kedecide kedecide.rs

use std::collections::{HashSet, VecDeque};
use std::fs::{rename, File};
use std::io::Write;
use std::time::Instant;
use std::env;

fn gcd(a: u64, b: u64) -> u64 { if a == 0 { b } else { gcd(b % a, a) } }
fn is_prime(x: u64) -> bool {
    if x < 2 { return false; }
    let mut d = 2;
    while d * d <= x { if x % d == 0 { return false; } d += 1; }
    true
}

struct M {
    n: usize,
    adj: Vec<Vec<usize>>,
    mate: Vec<i32>,
    p: Vec<i32>,
    base: Vec<usize>,
    used: Vec<bool>,
    blos: Vec<bool>,
}

impl M {
    fn lca(&self, a: usize, b: usize) -> usize {
        let mut seen = vec![false; self.n];
        let mut cur = a;
        loop {
            cur = self.base[cur];
            seen[cur] = true;
            if self.mate[cur] == -1 { break; }
            cur = self.p[self.mate[cur] as usize] as usize;
        }
        let mut cur = b;
        loop {
            cur = self.base[cur];
            if seen[cur] { return cur; }
            cur = self.p[self.mate[cur] as usize] as usize;
        }
    }
    fn mark_path(&mut self, v0: usize, b: usize, child0: usize) {
        let (mut v, mut child) = (v0, child0);
        while self.base[v] != b {
            self.blos[self.base[v]] = true;
            let mv = self.mate[v] as usize;
            self.blos[self.base[mv]] = true;
            self.p[v] = child as i32;
            child = mv;
            v = self.p[mv] as usize;
        }
    }
    fn find_path(&mut self, root: usize) -> i32 {
        self.used = vec![false; self.n];
        self.p = vec![-1; self.n];
        for i in 0..self.n { self.base[i] = i; }
        self.used[root] = true;
        let mut q: VecDeque<usize> = VecDeque::new();
        q.push_back(root);
        while let Some(v) = q.pop_front() {
            for idx in 0..self.adj[v].len() {
                let to = self.adj[v][idx];
                if self.base[v] == self.base[to] || self.mate[v] == to as i32 { continue; }
                if to == root || (self.mate[to] != -1 && self.p[self.mate[to] as usize] != -1) {
                    let cb = self.lca(v, to);
                    self.blos = vec![false; self.n];
                    self.mark_path(v, cb, to);
                    self.mark_path(to, cb, v);
                    for i in 0..self.n {
                        if self.blos[self.base[i]] {
                            self.base[i] = cb;
                            if !self.used[i] { self.used[i] = true; q.push_back(i); }
                        }
                    }
                } else if self.p[to] == -1 {
                    self.p[to] = v as i32;
                    if self.mate[to] == -1 {
                        return to as i32;
                    } else {
                        let mt = self.mate[to] as usize;
                        self.used[mt] = true;
                        q.push_back(mt);
                    }
                }
            }
        }
        -1
    }
    fn augment(&mut self, mut v: i32) {
        while v != -1 {
            let pv = self.p[v as usize];
            let ppv = if pv == -1 { -1 } else { self.mate[pv as usize] };
            self.mate[v as usize] = pv;
            if pv != -1 { self.mate[pv as usize] = v; }
            v = ppv;
        }
    }
}

/// maximum matching size on vertices `0..n` with `excl` removed

/// maximum matching; returns mate[] with -1 for exposed
fn matching(n: usize, edges: &[(usize, usize)]) -> Vec<i32> {
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for &(a, b) in edges { adj[a].push(b); adj[b].push(a); }
    let mut m = M { n, adj, mate: vec![-1; n], p: vec![-1; n], base: (0..n).collect(),
                    used: vec![false; n], blos: vec![false; n] };
    for v in 0..n {
        if m.mate[v] == -1 {
            let w = m.find_path(v);
            if w != -1 { m.augment(w); }
        }
    }
    m.mate
}

/// bad set of num/den inside [1,n]; returns Some(pair) when it has exactly two elements
fn badpair(num: u64, den: u64, n: u64, t: u64) -> Option<(u64, u64)> {
    let p = num % den;
    let (mut r, mut a, mut b, mut cnt) = (0u64, 0u64, 0u64, 0);
    for x in 1..=n {
        r += p; if r >= den { r -= den; }
        let mn = if r < den - r { r } else { den - r };
        if t * mn < den { cnt += 1; if cnt == 1 { a = x } else if cnt == 2 { b = x } else { return None; } }
    }
    if cnt == 2 { Some((a, b)) } else { None }
}

fn bad_pairs(m: u64) -> Vec<(u64, u64)> {
    let n = 2 * m; let t = m + 1;
    let mut pts: Vec<(u64, u64)> = vec![(0, 1), (1, 1)];
    for x in 1..=n {
        let den = x * t;
        for j in 0..=x { for s in [0i64, 1] {
            let numi = j as i64 * t as i64 + if s == 0 { -1 } else { 1 };
            if numi < 0 || numi as u64 > den { continue; }
            let num = numi as u64; let g = gcd(num, den).max(1);
            pts.push((num / g, den / g));
        }}
    }
    pts.sort_by(|a, b| (a.0 as u128 * b.1 as u128).cmp(&(b.0 as u128 * a.1 as u128)));
    pts.dedup();
    let mut out: HashSet<(u64, u64)> = HashSet::new();
    for &(nu, de) in &pts { if let Some(e) = badpair(nu, de, n, t) { out.insert(e); } }
    for w in pts.windows(2) {
        let (a, b) = (w[0], w[1]);
        if let Some(e) = badpair(a.0 + b.0, a.1 + b.1, n, t) { out.insert(e); }
    }
    let mut v: Vec<(u64, u64)> = out.into_iter().collect(); v.sort(); v
}

/// 2-SAT over `nv` variables; clauses are (var, positive) pairs. Returns an assignment if SAT.
fn two_sat(nv: usize, clauses: &[((usize, bool), (usize, bool))]) -> Option<Vec<bool>> {
    let n2 = 2 * nv;
    let lit = |v: usize, p: bool| if p { 2 * v } else { 2 * v + 1 };
    let neg = |l: usize| l ^ 1;
    let mut g: Vec<Vec<usize>> = vec![Vec::new(); n2];
    let mut gr: Vec<Vec<usize>> = vec![Vec::new(); n2];
    for &((a, pa), (b, pb)) in clauses {
        let (la, lb) = (lit(a, pa), lit(b, pb));
        g[neg(la)].push(lb); g[neg(lb)].push(la);
        gr[lb].push(neg(la)); gr[la].push(neg(lb));
    }
    // Kosaraju
    let mut order = Vec::with_capacity(n2);
    let mut vis = vec![false; n2];
    for s in 0..n2 {
        if vis[s] { continue; }
        let mut st = vec![(s, 0usize)]; vis[s] = true;
        while let Some((v, i)) = st.pop() {
            if i < g[v].len() {
                st.push((v, i + 1));
                let w = g[v][i];
                if !vis[w] { vis[w] = true; st.push((w, 0)); }
            } else { order.push(v); }
        }
    }
    let mut comp = vec![usize::MAX; n2];
    let mut c = 0;
    for &s in order.iter().rev() {
        if comp[s] != usize::MAX { continue; }
        let mut st = vec![s]; comp[s] = c;
        while let Some(v) = st.pop() {
            for &w in &gr[v] { if comp[w] == usize::MAX { comp[w] = c; st.push(w); } }
        }
        c += 1;
    }
    let mut asg = vec![false; nv];
    for v in 0..nv {
        if comp[lit(v, true)] == comp[lit(v, false)] { return None; }
        asg[v] = comp[lit(v, true)] > comp[lit(v, false)];
    }
    Some(asg)
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let (mlo, mhi): (u64, u64) = (a[1].parse().unwrap(), a[2].parse().unwrap());
    let logf = if a.len() > 3 { a[3].clone() } else { String::from("kedecide.log") };
    println!("  m     q  type    |  V    E   nu  def | KE? | check");
    let mut fails: Vec<u64> = Vec::new();
    let t0 = Instant::now();
    let mut lines: Vec<String> = Vec::new();
    for m in mlo..=mhi {
        let q = 2 * m + 1; let n = 2 * m;
        let ground: Vec<u64> = (1..=n).filter(|&x| x != 1 && x != m + 1).collect();
        let nv = ground.len();
        let pos = |v: u64| ground.iter().position(|&x| x == v);
        let mut ed: Vec<(usize, usize)> = Vec::new();
        for (x, y) in bad_pairs(m) {
            if let (Some(i), Some(j)) = (pos(x), pos(y)) { ed.push((i, j)); }
        }
        let mate = matching(nv, &ed);
        let nu = mate.iter().filter(|&&x| x >= 0).count() / 2;
        let def = nv as i64 - 2 * nu as i64;

        // one variable per matching edge; var_of[v] = (index, true if v is the "first" endpoint)
        let mut var_of: Vec<Option<(usize, bool)>> = vec![None; nv];
        let mut k = 0;
        for v in 0..nv {
            let w = mate[v];
            if w >= 0 && (w as usize) > v {
                var_of[v] = Some((k, true)); var_of[w as usize] = Some((k, false)); k += 1;
            }
        }
        let mut clauses: Vec<((usize, bool), (usize, bool))> = Vec::new();
        let mut impossible = false;
        for &(u, v) in &ed {
            match (var_of[u], var_of[v]) {
                (Some((iu, pu)), Some((iv, pv))) => {
                    if iu == iv { continue; }               // the matching edge itself is covered
                    clauses.push(((iu, pu), (iv, pv)));
                }
                (Some((iu, pu)), None) => clauses.push(((iu, pu), (iu, pu))), // unit
                (None, Some((iv, pv))) => clauses.push(((iv, pv), (iv, pv))),
                (None, None) => impossible = true,          // cannot happen for a maximum matching
            }
        }
        assert!(!impossible, "edge between two exposed vertices at m={}: matching not maximum", m);
        let sol = two_sat(k, &clauses);
        let ke = sol.is_some();
        if !ke { fails.push(m); }

        // certify the positive answer: the assignment must be a vertex cover of size nu
        let mut note = String::from("-");
        if let Some(asg) = sol {
            let mut cover = vec![false; nv];
            for v in 0..nv {
                if let Some((i, p)) = var_of[v] { if asg[i] == p { cover[v] = true; } }
            }
            let sz = cover.iter().filter(|&&b| b).count();
            let ok = ed.iter().all(|&(u, v)| cover[u] || cover[v]);
            assert!(ok && sz == nu, "bad cover certificate at m={}: size {} vs nu {}", m, sz, nu);
            note = format!("cover {} = nu, alpha = {}", sz, nv - sz);
        }
        let line = format!("{:3} {:5}  {}  | {:3} {:4} {:4} {:4} | {:3} | {}",
            m, q, if is_prime(q) { "prime  " } else { "compos." },
            nv, ed.len(), nu, def, if ke { "yes" } else { "*NO*" }, note);
        // Rule 8: progress, rate, ETA.  Cost is dominated by the O(m^3) sweep, so the remaining
        // time scales as the sum of m^3 over the tail, not linearly in the count of values left.
        let done = (m - mlo + 1) as f64;
        let el = t0.elapsed().as_secs_f64();
        let w_done: f64 = (mlo..=m).map(|x| (x as f64).powi(3)).sum();
        let w_left: f64 = ((m + 1)..=mhi).map(|x| (x as f64).powi(3)).sum();
        let eta = if w_done > 0.0 { el / w_done * w_left } else { 0.0 };
        if !ke || m % 10 == 0 || m == mhi {
            println!("{}   [{}/{} elapsed {:.0}s eta {:.0}s]", line, done as u64,
                     mhi - mlo + 1, el, eta);
        }
        lines.push(line);
        // atomic checkpoint after every m
        let tmp = format!("{}.tmp", logf);
        let mut f = File::create(&tmp).unwrap();
        for l in &lines { writeln!(f, "{}", l).unwrap(); }
        writeln!(f, "-- through m={}; KE FAILS at {:?}", m, fails).unwrap();
        drop(f);
        rename(&tmp, &logf).unwrap();
    }
    println!("\nKoenig-Egervary FAILS at: {:?}", fails);
}
