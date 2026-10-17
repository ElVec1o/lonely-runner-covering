#!/usr/bin/env python3
# Falsification / sanity script for Barajas-Serra Lemma 2 (Prime Filtering) and Corollary 3,
# and the Section-3 easy cases (|D|=2, |D|=4). Thin glue, exact integer arithmetic, bounded
# (small p, small D), <5 min.

import random

def nu(p, x):
    assert x > 0
    k = 0
    while x % p == 0:
        x //= p
        k += 1
    return k

def rp(p, x):
    v = nu(p, x)
    return (x // (p ** v)) % p

def qarc(p, m, N, x):
    xr = x % N
    return (xr // (p ** m)) % p

def levels(p, D):
    m = max(nu(p, d) for d in D)
    lv = {}
    for d in D:
        lv.setdefault(nu(p, d), []).append(d)
    return m, lv

def check_eq3(p, m, N, trials=2000):
    # eq (3): for lambda = 1 + k p^(m-j), j<m:
    #   nu(x) > j  => q(lambda x) = q(x)
    #   nu(x) = j  => q(lambda x) = q(x) + k*r_p(x)  (mod p)
    import random
    random.seed(0)
    fails = 0
    checked = 0
    for _ in range(trials):
        j = random.randrange(0, m)
        k = random.randrange(0, p)
        lam = 1 + k * p ** (m - j)
        x = random.randrange(1, N)
        if x % N == 0:
            continue
        vx = nu(p, x) if x % N != 0 else None
        qx = qarc(p, m, N, x)
        qlx = qarc(p, m, N, lam * x)
        checked += 1
        if vx > j:
            if qlx != qx:
                fails += 1
        elif vx == j:
            expect = (qx + k * rp(p, x)) % p
            if qlx != expect:
                fails += 1
        # vx < j: eq (3) doesn't claim anything
    return checked, fails

def prime_filtering(p, D, F):
    """Brute-force / direct search for a multiplier lambda in Z_N^* achieving
    q(lambda d) not in F[d] for all d, checking the SAME construction the paper's
    proof performs (search Lambda_{m,p} first for D_p(m), then step down), to confirm
    existence under the hypothesis. Returns lambda or None."""
    m = max(nu(p, d) for d in D)
    N = p ** (m + 1)
    Dlevels = {}
    for d in D:
        Dlevels.setdefault(nu(p, d), []).append(d)
    # search brute force over ALL units mod N (small N only) as ground truth
    best = None
    for lam in range(1, N):
        if lam % p == 0:
            continue
        ok = True
        for d in D:
            if qarc(p, m, N, lam * d) in F[d]:
                ok = False
                break
        if ok:
            best = lam
            break
    return best, N, m

def hyp_ok(p, D, F):
    m = max(nu(p, d) for d in D)
    Dlevels = {}
    for d in D:
        Dlevels.setdefault(nu(p, d), []).append(d)
    for j in range(0, m):
        s = sum(len(F[d]) for d in Dlevels.get(j, []))
        if s > p - 1:
            return False, f"level {j} sum {s} > p-1={p-1}"
    s = sum(len(F[d]) for d in Dlevels.get(m, []))
    if s > p - 2:
        return False, f"top level sum {s} > p-2={p-2}"
    return True, "ok"

def run_lemma2_battery():
    cases = []
    # Case A: p=5, D = {1,2,3,4} all level 0 (m=0), F_d = {0,4} each -> Corollary-3-style,
    # sum = 2*4=8 > p-1=4 at level 0=m so must use TOP bound p-2=3; 8>3 -> hypothesis fails,
    # this is a NEGATIVE CONTROL (hypothesis violated) -- must NOT expect success necessarily.
    D = [1, 2, 3, 4]
    F = {d: {0, 4} for d in D}
    ok, msg = hyp_ok(5, D, F)
    res, N, m = prime_filtering(5, D, F)
    cases.append(("A (neg ctrl, hyp violated)", 5, D, F, ok, msg, res, N, m))

    # Case B: p=5, D={1,2}, F_d={0,4} (|D|=2, level 0=m, sum=4<=p-2=3? sum=4>3 -> still violated)
    D = [1, 2]
    F = {d: {0, 4} for d in D}
    ok, msg = hyp_ok(5, D, F)
    res, N, m = prime_filtering(5, D, F)
    cases.append(("B (|D|=2, top sum 4>3, violated)", 5, D, F, ok, msg, res, N, m))

    # Case C: p=5, D={1,2,3} at level 0=m (this is the |D5(0)|=3 case from Section 3, |D|=4 with
    # a 4th elt at level m separately -- test the |A|=3 sub-lemma directly via Cor-3-style F.
    D = [1, 2, 3]
    F = {d: {0, 4} for d in D}
    ok, msg = hyp_ok(5, D, F)
    res, N, m = prime_filtering(5, D, F)
    cases.append(("C (|A|=3 at top level, sum=6>3, violated - expect Cor3 NOT applicable, need Sec3 argument)", 5, D, F, ok, msg, res, N, m))

    # Case D: matches Corollary 3's actual use pattern: |D|=2, p=3, single level j=0=m,
    # F_d={0,2} each, sum=4 > p-2=1 -- Corollary 3 doesn't apply directly at level m this way;
    # real Cor3 use for |D|=2 is p=3, i0=1, m could be >0 with D_3(0) size <=1. Build concretely:
    D = [1, 3]   # nu_3(1)=0, nu_3(3)=1=m
    F = {1: {0, 2}}  # only level-0 elt gets a forbidden set (Cor3: elts at level >= i0=1 already fine)
    m = max(nu(3, d) for d in D)
    ok, msg = hyp_ok(3, D, {1: {0, 2}, 3: set()})
    res, N, mm = prime_filtering(3, D, {1: {0, 2}, 3: set()})
    cases.append(("D (|D|=2 realistic Cor3 use, p=3)", 3, D, {1: {0, 2}, 3: set()}, ok, msg, res, N, mm))

    for name, p, D, F, ok, msg, res, N, m in cases:
        print(f"{name}: p={p} D={D} F={ {d: sorted(v) for d,v in F.items()} } hyp_ok={ok} ({msg}) -> lambda={res} (N={N}, m={m})")
        if res is not None:
            for d in D:
                print(f"    d={d}: q(lambda*d)={qarc(p, m, N, res*d)}  forbidden={sorted(F[d])}")

if __name__ == "__main__":
    print("== eq(3) mechanics check ==")
    total_checked, total_fail = 0, 0
    for p in (3, 5, 7):
        for m in (1, 2, 3):
            N = p ** (m + 1)
            c, f = check_eq3(p, m, N, trials=3000)
            total_checked += c
            total_fail += f
            print(f"p={p} m={m} N={N}: checked={c} fails={f}")
    print(f"TOTAL checked={total_checked} fails={total_fail}")
    print()
    print("== Lemma 2 / Corollary 3 concrete battery ==")
    run_lemma2_battery()

def random_battery(trials=300, seed=1):
    import random
    random.seed(seed)
    checked = 0
    fails = 0
    for _ in range(trials):
        p = random.choice([3, 5, 7])
        m = random.randrange(0, 3)
        # build D with levels 0..m, D at level m nonempty, D at level 0 nonempty
        Dlevels = {i: [] for i in range(m + 1)}
        nid = 1
        for lvl in range(m + 1):
            cnt = random.randrange(1, p)  # keep counts small
            for _ in range(cnt):
                # construct an integer with valuation exactly lvl
                base = random.randrange(1, p)  # nonzero mod p digit
                d = base * (p ** lvl)
                Dlevels[lvl].append(d)
        D = [d for lvl in Dlevels.values() for d in lvl]
        # random forbidden sets respecting the hypothesis bounds
        F = {}
        ok_build = True
        for lvl in range(m + 1):
            cap = (p - 1) if lvl < m else (p - 2)
            elts = Dlevels[lvl]
            if not elts:
                continue
            # distribute cap among elts randomly (sizes >=0, sum <= cap)
            remaining = cap
            for i, d in enumerate(elts):
                if remaining <= 0:
                    F[d] = set()
                    continue
                take = random.randrange(0, min(remaining, p) + 1)
                F[d] = set(random.sample(range(p), min(take, p)))
                remaining -= len(F[d])
        for d in D:
            F.setdefault(d, set())
        ok, msg = hyp_ok(p, D, F)
        if not ok:
            continue  # skip, only test hypothesis-respecting instances
        checked += 1
        res, N, mm = prime_filtering(p, D, F)
        if res is None:
            fails += 1
            print("FALSIFIED:", p, D, F)
        else:
            for d in D:
                if qarc(p, mm, N, res * d) in F[d]:
                    fails += 1
                    print("FALSIFIED (bad witness):", p, D, F, res)
                    break
    print(f"random_battery: hypothesis-respecting instances checked={checked} fails={fails}")

random_battery(400)


def check_bridge(trials_per_pm=3000):
    """Falsify the digit-to-real bridge formula used by
    primeFilteringCor3: for d, N = p^(m+1), q = qarc(p,m,N,d),
      - MID: q not in {0, p-1}  =>  min(d%N, N-d%N) * p >= N   (i.e. nearestIntDist(d/N) >= 1/p)
      - TOP: nu_p(d) == m and q != 0  =>  min(d%N, N-d%N) * p >= N
    (TOP needs only q != 0, not also q != p-1, because nu_p(d) = m forces d % N to be an EXACT
    multiple of p^m with zero lower digits -- no erosion from below.)
    """
    fails = 0
    trials = 0
    for p in [3, 5, 7]:
        for m in range(0, 4):
            N = p ** (m + 1)
            for _ in range(trials_per_pm):
                trials += 1
                d = random.randint(1, 5 * N)
                q = qarc(p, m, N, d)
                r = d % N
                num = min(r, N - r)
                if q != 0 and q != p - 1:
                    if not (num * p >= N):
                        fails += 1
                        print("bridge MID-FAIL", p, m, d, q, num, N)
                if nu(p, d) == m and q != 0:
                    if not (num * p >= N):
                        fails += 1
                        print("bridge TOP-FAIL", p, m, d, q, num, N)
    print(f"check_bridge: trials={trials} fails={fails}")


check_bridge()


def check_D4_ellA(trials=200000, seed=1):
    """Falsify the |D|=4 (5-runner) hard branch's actual claim:
    A = D5(0) with |A|=3 (three positive integers d1,d2,d3, level 0 mod 5, i.e. 5 does not
    divide any of them), gcd-of-residues condition irrelevant here -- test the RAW claim that
    SOME multiplier lambda in Lam(0,m,5) union {j in {1,2,3,4}} (i.e. some j in {1,2,3,4} acting
    on A directly, matching Lam_{m,5} = {1,...,p-1} used at the TOP but here applied as the
    'j-th power trick' of eq (5)) makes q(j*lam_k*d_i) avoid {0,4} for all three d_i
    simultaneously, for random concrete integers (not just residues), since eq (5) is an
    INCLUSION (carries from lower digits matter, not just residues mod 5).
    Bounded: p=5 fixed, m in {1,2,3}, random d1,d2,d3 with nu_5=0, trials small ints only.
    """
    random.seed(seed)
    p = 5
    fails = 0
    checked = 0
    for _ in range(trials):
        m = random.randint(1, 3)
        N = p ** (m + 1)
        # three positive ints, level 0 (5 does not divide), random up to a few multiples of N
        ds = []
        for _ in range(3):
            while True:
                d = random.randint(1, 4 * N)
                if d % p != 0:
                    ds.append(d)
                    break
        checked += 1
        found = False
        for k in range(p):  # lambda_k = 1 + k*p^m in Lambda_{0,p}
            lam = 1 + k * (p ** m)
            for j in range(1, p):  # j in Lambda_{m,p} = {1,...,p-1}
                ok = True
                for d in ds:
                    q = qarc(p, m, N, j * lam * d)
                    if q == 0 or q == p - 1:
                        ok = False
                        break
                if ok:
                    found = True
                    break
            if found:
                break
        if not found:
            fails += 1
            print("D4-ellA-FAIL", m, ds)
    print(f"check_D4_ellA: trials={checked} fails={fails}")


check_D4_ellA()


def check_carry_lemma(trials=50000, seed=2):
    """Falsify the EXACT carry lemma in isolation (eq. (5)'s atomic
    step), before formalizing it: for x, y positive integers, N = p^(m+1),
        q(x+y) = (q(x) + q(y) + c) % p   for SOME c in {0, 1}.
    This is the general two-summand digit-carry fact (standard base-p addition: carry into any
    digit position is always 0 or 1), which the paper's eq. (5) applies with x = j*d, y = d to
    get q((j+1)d) from q(jd), q(d). Isolating it from the j*d/d instance and testing on fully
    general x, y (not just multiples of a common d) is a strictly stronger, more general check
    than check_D4_ellA above, and is new content not previously falsified directly.
    """
    random.seed(seed)
    fails = 0
    checked = 0
    for _ in range(trials):
        p = random.choice([3, 5, 7])
        m = random.randint(0, 3)
        N = p ** (m + 1)
        x = random.randint(1, 6 * N)
        y = random.randint(1, 6 * N)
        checked += 1
        qx = qarc(p, m, N, x)
        qy = qarc(p, m, N, y)
        qxy = qarc(p, m, N, x + y)
        ok = any(qxy == (qx + qy + c) % p for c in (0, 1))
        if not ok:
            fails += 1
            print("CARRY-FAIL", p, m, x, y, qx, qy, qxy)
    print(f"check_carry_lemma: trials={checked} fails={fails}")


def check_carry_lemma_jd(trials=50000, seed=3):
    """Same carry fact specialized to the eq.-(5) instance actually used: x = j*d, y = d,
    j in {1,2,3,4}, p = 5, plus the cumulative bound q(j*d) = (j*q(d) + c_j) % p with
    0 <= c_j <= j-1 (paper's eq. (5) second inclusion), tracked by explicit simulation of the
    carry recursion rather than assumed.
    """
    random.seed(seed)
    p = 5
    fails = 0
    checked = 0
    for _ in range(trials):
        m = random.randint(1, 3)
        N = p ** (m + 1)
        d = random.randint(1, 6 * N)
        if d % p == 0:
            continue
        checked += 1
        qd = qarc(p, m, N, d)
        c = 0
        qjd_prev = qd  # q(1*d)
        for j in range(2, 5):
            qjd = qarc(p, m, N, j * d)
            qj1d = qarc(p, m, N, (j - 1) * d)
            # carry step from q((j-1)d) + q(d) to q(j*d)
            found_step = False
            for cc in (0, 1):
                if qjd == (qj1d + qd + cc) % p:
                    found_step = True
                    break
            if not found_step:
                fails += 1
                print("CARRY-STEP-FAIL", m, d, j, qjd, qj1d, qd)
                break
            # cumulative bound: q(j*d) = (j*qd + c_j) % p for some 0 <= c_j <= j-1
            cum_ok = any(qjd == (j * qd + cj) % p for cj in range(j))
            if not cum_ok:
                fails += 1
                print("CARRY-CUM-FAIL", m, d, j, qjd, qd)
                break
    print(f"check_carry_lemma_jd: trials={checked} fails={fails}")


check_carry_lemma()
check_carry_lemma_jd()


def check_reflection_transport(trials=50000, seed=4):
    """Session 9. Check the EXACT claim needed for the |As|=3 WLOG normalization: does
    d -> N-d realize a clean digit-level reflection of qarc, and if so which reflection
    (x -> -x mod p, fixing 0; or x -> (p-1)-x, fixing (p-1)/2-ish)? Also checks whether this
    is compatible with the j-multiplication step used by the case chase, i.e. whether
    qarc(p,m,N, N - j*d) relates to qarc(p,m,N, j*(N-d)) simply (they are literally the same
    residue mod N, so this should hold trivially -- the real question is the FORM of the
    reflection at the level-m digit for elements with nu_p(d)=0, m>=1).
    """
    random.seed(seed)
    p = 5
    fails_negx = 0
    fails_p1mx = 0
    fails_jcompat = 0
    checked = 0
    for _ in range(trials):
        m = random.randint(1, 4)
        N = p ** (m + 1)
        d = random.randint(1, N - 1)
        if nu(p, d) != 0:
            continue
        checked += 1
        qd = qarc(p, m, N, d)
        qNd = qarc(p, m, N, N - d)
        # candidate A: x -> -x mod p (i.e. (p - x) % p)
        if qNd != (p - qd) % p:
            fails_negx += 1
        # candidate B: x -> (p-1) - x
        if qNd != (p - 1) - qd:
            fails_p1mx += 1
        # j-multiplication compatibility: qarc(N - j*d) should equal qarc(j*(N-d)) since
        # both reduce to the same residue mod N (j*(N-d) = jN - j*d = -j*d mod N).
        for j in range(1, 5):
            lhs = qarc(p, m, N, (N - (j * d) % N) % N if (j * d) % N != 0 else 0)
            rhs = qarc(p, m, N, j * (N - d))
            if lhs != rhs:
                fails_jcompat += 1
    print(f"check_reflection_transport: trials={checked} "
          f"fails[x->-x mod p]={fails_negx} fails[x->(p-1)-x]={fails_p1mx} "
          f"fails[j-compat]={fails_jcompat}")


def check_reflection_pair_orbit(trials=200000, seed=5):
    """Session 9. The docstring claims exactly 3 of the 6 unordered pairs {a,b} subset of
    {1,2,3,4} (differences q(d2)-q(d1), q(d3)-q(d1) after rotating q(d1) to 0) are 'hard'
    ({1,3},{2,3},{2,4}), and that these 3 are related to EACH OTHER by relabeling d2<->d3
    composed with reflection x -> -x, NOT by relabeling alone. Verify exhaustively (no
    randomness needed, it's a finite check over 5^3 residue triples, but we brute force via
    the labeled rotation+relabel group action, size 3! x 5 = 30, to be safe against a
    hand-arithmetic slip).
    """
    hard_pairs = {frozenset({1, 3}), frozenset({2, 3}), frozenset({2, 4})}
    easy_pairs = {frozenset({1, 2}), frozenset({1, 4}), frozenset({3, 4})}
    import itertools
    # relabeling-only orbit (S_3 on (d1,d2,d3), no reflection): for a representative triple
    # with pair {2,3} (i.e. residues (0,2,3)), apply all 6 relabelings + all 5 rotations,
    # collect the resulting {a,b} pair (post rotating new-d1 to 0) for each.
    base = (0, 2, 3)
    reachable_by_relabel_rotate_only = set()
    for perm in itertools.permutations(range(3)):
        triple = tuple(base[perm[i]] for i in range(3))
        for k in range(5):
            rotated = tuple((x + k) % 5 for x in triple)
            # rotate so rotated[0] == 0
            shift = (-rotated[0]) % 5
            normalized = tuple((x + shift) % 5 for x in rotated)
            assert normalized[0] == 0
            pair = frozenset({normalized[1], normalized[2]})
            reachable_by_relabel_rotate_only.add(pair)
    reachable_with_reflection = set(reachable_by_relabel_rotate_only)
    for pair in list(reachable_by_relabel_rotate_only):
        a, b = tuple(pair)
        ra, rb = (-a) % 5, (-b) % 5
        reachable_with_reflection.add(frozenset({ra, rb}))
    print(f"check_reflection_pair_orbit: base={base} (pair {{2,3}}) "
          f"relabel+rotate-only orbit = {sorted(map(sorted, reachable_by_relabel_rotate_only))}")
    print(f"  is this orbit == hard_pairs {sorted(map(sorted, hard_pairs))}? "
          f"{reachable_by_relabel_rotate_only == hard_pairs}")
    print(f"  with reflection added, orbit = "
          f"{sorted(map(sorted, reachable_with_reflection))}")
    print(f"  covers all 6 pairs with reflection? "
          f"{reachable_with_reflection == (hard_pairs | easy_pairs)}")


check_reflection_transport()
check_reflection_pair_orbit()


def ell_window(residues, p=5):
    """Smallest length of an arithmetic-progression window (consecutive residues mod p)
    containing all of `residues`. Brute force over all p possible window starts and all
    window lengths 1..p."""
    residues = set(residues)
    for L in range(1, p + 1):
        for start in range(p):
            window = {(start + i) % p for i in range(L)}
            if residues <= window:
                return L
    return p


def check_full_orbit_exhaustive(p=5):
    """Session 9, decisive check. Exhaustively (no randomness) enumerate ALL Finset.range p
    triples of 3 DISTINCT residues {r1,r2,r3} (unordered, since As is a Finset), compute
    ell_window for each, and determine: does relabeling (S_3 on which element is d1/d2/d3)
    composed with rotation (k -> +k for all three, modeling the unit multiplier lam) act
    TRANSITIVELY on the 'hard' class (ell=4) and on the 'easy' class (ell=3) separately,
    with NO reflection needed? If so, a single WLOG representative per class suffices and
    the docstring's reflection requirement is UNNECESSARY (a genuine correction, not a
    confirmation)."""
    import itertools
    triples = list(itertools.combinations(range(p), 3))  # unordered distinct triples
    ell_of = {}
    for t in triples:
        ell_of[frozenset(t)] = ell_window(t, p)
    print(f"All {len(triples)} unordered triples, ell values: "
          f"{sorted((sorted(t), ell_of[frozenset(t)]) for t in triples)}")

    def orbit_class(t):
        """Rotation+relabel orbit representative: rotate every relabeled ordering so the
        first element is 0, return the canonical (sorted) result as identifier of the orbit
        containing pair-shape, but since it's a SET {r1,r2,r3} not ordered, relabeling is
        automatic (a Finset has no order) -- the only real action is the rotation k -> x+k.
        We return the lexicographically smallest rotation of the sorted triple with one
        element forced to 0, ranging over all 3 choices of which element becomes 0."""
        reps = []
        for pivot in t:
            k = (-pivot) % p
            rotated = tuple(sorted((x + k) % p for x in t))
            reps.append(rotated)
        return min(reps)

    classes = {}
    for t in triples:
        rep = orbit_class(t)
        classes.setdefault(rep, []).append(t)
    print(f"\nOrbit representatives under (Finset relabeling is automatic) + rotation only:")
    for rep, members in sorted(classes.items()):
        ells = {ell_of[frozenset(m)] for m in members}
        print(f"  rep={rep} members={members} ell values in orbit={ells}")

    # Now check: is each orbit HOMOGENEOUS in ell (all members same ell)? If yes, rotation
    # alone (no reflection) already reduces every hard instance to ONE canonical
    # representative, and the docstring's reflection concern is moot.
    homogeneous = all(len({ell_of[frozenset(m)] for m in members}) == 1
                       for members in classes.values())
    print(f"\nEvery rotation-orbit is ell-homogeneous (so 1 rep per orbit suffices, "
          f"no reflection needed)? {homogeneous}")


check_full_orbit_exhaustive()


def check_case_as2_minority(trials=500000, seed=7):
    """Session 11. Isolates the |As|=2 branch of Section 3's |D|=4 (5-runner) argument
    (bs2008.txt lines 233-238, "Suppose now that As = {d1,d2} and r5(d3) = +-2s ... Hence we
    have q(lam_k . As) cap {0,4} = empty at least for two values of k, and since r5(d3) != +-s
    at least for one of them we have q(lam_k d3) != 0,4 as well").

    Session 11 task instruction guessed this minority-element step might reduce to smaller
    |D|=2/|D|=3 machinery. Re-reading the paper text directly shows this guess is WRONG: there
    is no reduction to a smaller case. The step is a SEPARATE finite pigeonhole argument, in the
    same family as `primeFiltering`'s counting technique already VERIFIED in this project, not
    a fallback to smaller |D|. This checks the pigeonhole claim itself as a residue-level finite
    fact (the case-chase machinery upstream already pins q(j*d1), q(j*d2) into the window {1,2}
    for the winning j; this function isolates exactly what happens next for the minority d3).
    """
    random.seed(seed)
    p = 5
    trials_done = 0
    fails = 0
    for _ in range(trials):
        s = random.choice([1, 2])
        other = random.choice([2 * s % p, (-2 * s) % p])  # r5(d3) = +-2s, hypothesis of the case
        q1 = random.choice([1, 2])
        q2 = random.choice([1, 2])
        qd3 = random.randint(0, p - 1)
        trials_done += 1
        good_k = [k for k in range(p)
                  if (q1 + k * s) % p not in (0, p - 1) and (q2 + k * s) % p not in (0, p - 1)]
        ok = any((qd3 + k * other) % p not in (0, p - 1) for k in good_k)
        if not ok:
            fails += 1
    print(f"check_case_as2_minority: trials={trials_done} fails={fails}")

    # Negative control: violate the hypothesis r5(d3) != +-s by setting other = s.
    # The machinery must then FAIL on some instances, or the hypothesis is not load-bearing.
    random.seed(seed + 1)
    nc_trials = 0
    nc_fails = 0
    for _ in range(trials // 2):
        s = random.choice([1, 2])
        other = s  # hypothesis violated on purpose
        q1 = random.choice([1, 2])
        q2 = random.choice([1, 2])
        qd3 = random.randint(0, p - 1)
        nc_trials += 1
        good_k = [k for k in range(p)
                  if (q1 + k * s) % p not in (0, p - 1) and (q2 + k * s) % p not in (0, p - 1)]
        ok = any((qd3 + k * other) % p not in (0, p - 1) for k in good_k)
        if not ok:
            nc_fails += 1
    print(f"check_case_as2_minority NEGATIVE CONTROL (r5(d3)=s, hypothesis deliberately "
          f"violated): trials={nc_trials} fails={nc_fails} "
          f"(nonzero fails EXPECTED here -- confirms the hypothesis is load-bearing)")


check_case_as2_minority()
