"""Checks for the exact adapter (Section 2 of the paper). Exact arithmetic unless stated."""
import itertools, json, random, sys, time
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linear_sum_assignment, linprog

from adapter import (Adapter, diamond_chain, perm_cost, exact_min_assignment, exact_forced_min,
                     to_int_matrix, marginal_value, min_marginal)

random.seed(20261124)
REPORT = {}


def structural_checks(ad, label):
    N = ad.N
    nV, nA, nJ = len(ad.V), len(ad.arcs), len(ad.inter)
    assert N == nV + nA + 4 * nJ, "N formula"
    assert len(ad.dag_arcs) == 2 * nA + 4 * nJ, "chain arc count"
    assert ad.dprime_is_acyclic(), "D' acyclic"
    occ = ad.symbolic_occurrences()
    rows, cols = [], []
    for j, lst in occ.items():
        assert len(lst) == 2, "two occurrences"
        diag = [x for x in lst if x[0] == x[1]]
        off = [x for x in lst if x[0] != x[1]]
        assert len(diag) == 1 and len(off) == 1, "one diagonal (in F) and one off-diagonal"
        for (r, c) in lst:
            rows.append(r)
            cols.append(c)
    assert len(set(rows)) == len(rows) and len(set(cols)) == len(cols), "uncertain entries form a matching"
    # path bijection
    P = ad.original_paths()
    Pp = ad.dprime_paths()
    col = [ad.collapse(p) for p in Pp]
    assert sorted(col) == sorted(P) and len(set(col)) == len(col), "path bijection"
    return dict(label=label, N=N, V=nV, A=nA, J=nJ, paths=len(P), designated_offdiag=len(ad.designated))


def dual_check(ad, theta):
    """Explicit dual: p_{k_j}=theta_j, else 0; q=0. Check ALL N^2 entries, tightness of diagonal, objective."""
    C = ad.cost_matrix(theta)
    N = ad.N
    p = [Fr(0)] * N
    for j in range(len(ad.inter)):
        p[ad.idx[("k", j)]] = Fr(theta[j])
    minslack_off = None
    for i in range(N):
        for jx in range(N):
            sl = C[i][jx] - p[i]
            assert sl >= 0, f"dual infeasible at {ad.names[i]}->{ad.names[jx]}"
            assert C[i][jx] >= 0, "negative cost"
            if i == jx:
                assert sl == 0, "diagonal not tight"
    assert sum(p) == perm_cost(C, list(range(N))), "dual objective"
    return True


def route_checks(ad, theta):
    """Every D' route permutation: cost computed from the matrix equals the claimed formula."""
    C = ad.cost_matrix(theta)
    base = perm_cost(C, list(range(ad.N)))
    assert base == sum((Fr(x) for x in theta), Fr(0))
    best = None
    lo, hi = ad.delta, ad.delta + ad.A0 + ad.B0
    for vp in ad.dprime_paths():
        perm = ad.perm_of_dprime_path(vp)
        rel = perm_cost(C, perm) - base
        arcs = ad.collapse(vp)
        assert rel == ad.route_formula(arcs, theta), "relative cost formula (6)"
        assert lo <= rel <= hi, "route interval"
        best = rel if best is None else min(best, rel)
    return best


def scipy_min(Aint):
    A = np.array(Aint, dtype=np.float64)
    r, c = linear_sum_assignment(A)
    return int(round(A[r, c].sum())), c


def assignment_checks(ad, theta, exact=True, second_best=True, lp=False):
    C = ad.cost_matrix(theta)
    N = ad.N
    base = perm_cost(C, list(range(N)))
    Aint, L = to_int_matrix(C)
    out = {}
    # unforced optimum
    if exact:
        c0, perm0 = exact_min_assignment(C)
        assert c0 == base, "identity is not optimal"
    c0s, perm0s = scipy_min(Aint)
    assert Fr(c0s, L) == base, "identity not optimal (scipy)"
    # best non-identity permutation: forbid one diagonal entry at a time
    route_best = route_checks(ad, theta)
    if second_best:
        BIG = sum(max(row) for row in Aint) + 1
        sb = None
        for i in range(N):
            old = Aint[i][i]
            Aint[i][i] = BIG
            ci, _ = scipy_min(Aint)
            Aint[i][i] = old
            sb = ci if sb is None else min(sb, ci)
        sb = Fr(sb, L) - base
        assert sb >= ad.delta > 0, "uniqueness gap"
        assert sb == route_best, "best non-identity permutation is not the best route"
        out["second_best_gap"] = sb
    # forced optimum
    r, c = ad.e
    rows = [i for i in range(N) if i != r]
    cols = [j for j in range(N) if j != c]
    sub = [[Aint[i][j] for j in cols] for i in rows]
    cf, _ = scipy_min(sub)
    forced = Fr(cf + Aint[r][c], L) - base
    assert forced == route_best, f"forced value {forced} != route minimum {route_best}"
    if exact:
        fe, _ = exact_forced_min(C, ad.e)
        assert fe - base == route_best, "forced value (exact Hungarian) != route minimum"
    if lp:
        # LP over the full doubly-stochastic polytope (floating point cross-check of the fractional claims)
        cvec = np.array([[float(x) for x in row] for row in C]).ravel()
        Aeq = np.zeros((2 * N, N * N))
        for i in range(N):
            Aeq[i, i * N:(i + 1) * N] = 1
            Aeq[N + i, i::N] = 1
        beq = np.ones(2 * N)
        res = linprog(cvec, A_eq=Aeq, b_eq=beq, bounds=(0, 1), method="highs")
        assert res.status == 0 and abs(res.fun - float(base)) < 1e-7, "LP unforced"
        X = res.x.reshape(N, N)
        assert np.abs(X - np.eye(N)).max() < 1e-7, "LP unforced optimum is not the identity"
        bounds = [(0, 1)] * (N * N)
        bounds[r * N + c] = (1, 1)
        res2 = linprog(cvec, A_eq=Aeq, b_eq=beq, bounds=bounds, method="highs")
        assert res2.status == 0 and abs(res2.fun - float(base) - float(route_best)) < 1e-7, "LP forced"
        out["lp_forced"] = res2.fun - float(base)
    out["forced"] = forced
    return out


def random_dag(maxV=5, maxA=7, maxJ=4):
    while True:
        m = random.randint(2, maxV)
        s_i = random.randint(0, m - 2)
        t_i = random.randint(s_i + 1, m - 1)
        arcs = []
        for _ in range(random.randint(1, maxA)):
            i = random.randint(0, m - 2)
            j = random.randint(i + 1, m - 1)
            arcs.append((i, j))  # parallel arcs allowed
        if len(arcs) < 2:
            continue
        alpha = [Fr(random.choice([0, 0, 1, 2, 3, 5]), random.choice([1, 1, 2, 3])) for _ in arcs]
        inter = []
        for _ in range(random.randint(0, maxJ)):
            a, b = random.sample(range(len(arcs)), 2)
            inter.append((a, b, Fr(random.choice([0, 1, 2, 3, 7]), random.choice([1, 1, 2]))))
        delta = Fr(random.choice([1, 1, 2, 1]), random.choice([1, 2, 3]))
        ad = Adapter(list(range(m)), arcs, s_i, t_i, alpha, inter, delta)
        if ad.original_paths():
            return ad


def scenarios(ad, k_random=3, all_corners=False, max_corners=8):
    J = len(ad.inter)
    betas = [b for (_, _, b) in ad.inter]
    out = []
    out.append([Fr(0)] * J)
    out.append(list(betas))
    if all_corners:
        for bits in itertools.product((0, 1), repeat=J):
            out.append([betas[j] * bits[j] for j in range(J)])
    else:
        for _ in range(max_corners):
            out.append([betas[j] * random.randint(0, 1) for j in range(J)])
    for _ in range(k_random):
        out.append([betas[j] * Fr(random.randint(0, 97), 97) for j in range(J)])
    return out


# ---------------------------------------------------------------- 1. structure, formula N, dimension
t0 = time.time()
struct = []
for n in range(1, 7):
    ws = {(i, a): random.randint(0, 4) for i in range(1, n + 1) for a in (0, 1)}
    wp = {(i, j, a, b): random.randint(0, 4) for i in range(1, n + 1) for j in range(i + 1, n + 1)
          for a in (0, 1) for b in (0, 1)}
    ad = diamond_chain(n, ws, wp)
    st = structural_checks(ad, f"diamond n={n}")
    assert ad.N == 8 * n * n - n + 1
    assert len(ws) + len(wp) == 2 * n * n
    assert len(ad.inter) == 2 * n * (n - 1)
    assert st["paths"] == 2 ** n
    assert st["designated_offdiag"] == 8 * n * n + 1
    assert ad.H == 2 + sum(ws.values()) + 2 * sum(wp.values())
    struct.append(st)
REPORT["structure_diamond"] = struct
print("structure diamond ok", struct, flush=True)

# ---------------------------------------------------------------- 2. brute force over ALL permutations, tiny instances
def brute(ad, theta):
    C = ad.cost_matrix(theta)
    N = ad.N
    base = perm_cost(C, list(range(N)))
    best_nonid, best_forced = None, None
    r, c = ad.e
    nopt = 0
    for perm in itertools.permutations(range(N)):
        cost = sum(C[i][perm[i]] for i in range(N))
        rel = cost - base
        if rel < 0:
            raise AssertionError("identity not optimal")
        if rel == 0:
            nopt += 1
        if perm[r] == c:
            best_forced = rel if best_forced is None else min(best_forced, rel)
    assert nopt == 1, "identity not the unique optimal permutation"
    return best_forced

tiny = []
# (a) two-arc path with one interaction: N = 3+2+4 = 9
ad = Adapter(["s", "x", "t"], [("s", "x"), ("x", "t")], "s", "t", [Fr(1, 2), Fr(2)], [(0, 1, Fr(3))], Fr(1))
structural_checks(ad, "tiny path")
for th in [Fr(0), Fr(3), Fr(1), Fr(5, 2)]:
    bf = brute(ad, [th])
    rb = route_checks(ad, [th])
    dual_check(ad, [th])
    assert bf == rb
    tiny.append(("path2", str(th), str(bf)))
# (b) two parallel arcs with an interaction that can never be active together: N = 2+2+4 = 8
ad = Adapter(["s", "t"], [("s", "t"), ("s", "t")], "s", "t", [Fr(1), Fr(0)], [(0, 1, Fr(4))], Fr(1, 3))
structural_checks(ad, "tiny parallel")
for th in [Fr(0), Fr(4), Fr(7, 3)]:
    bf = brute(ad, [th])
    rb = route_checks(ad, [th])
    dual_check(ad, [th])
    assert bf == rb
    tiny.append(("par2", str(th), str(bf)))
# (c) reversed role: B-feature arc comes first on the path
ad = Adapter(["s", "x", "t"], [("s", "x"), ("x", "t")], "s", "t", [Fr(0), Fr(0)], [(1, 0, Fr(2))], Fr(1))
for th in [Fr(0), Fr(2), Fr(1, 2)]:
    bf = brute(ad, [th])
    assert bf == route_checks(ad, [th])
    tiny.append(("path2rev", str(th), str(bf)))
# (d) diamond n=1 (N=8, no interactions)
ad = diamond_chain(1, {(1, 0): 3, (1, 1): 2}, {})
assert brute(ad, []) == 3
REPORT["tiny_bruteforce_all_permutations"] = tiny
print("tiny brute force ok", tiny, time.time() - t0, flush=True)

# ---------------------------------------------------------------- 3. random small DAGs
rd = []
for it in range(60):
    ad = random_dag()
    st = structural_checks(ad, f"random {it}")
    for th in scenarios(ad, k_random=2, all_corners=(len(ad.inter) <= 3), max_corners=4):
        dual_check(ad, th)
        res = assignment_checks(ad, th, exact=(it < 20), second_best=True, lp=(it < 6))
    # eta over all corners vs delta + min Q(P)
    J = len(ad.inter)
    betas = [b for (_, _, b) in ad.inter]
    eta = None
    for bits in itertools.product((0, 1), repeat=J):
        th = [betas[j] * bits[j] for j in range(J)]
        C = ad.cost_matrix(th)
        f, _ = exact_forced_min(C, ad.e)
        f -= perm_cost(C, list(range(ad.N)))
        eta = f if eta is None else min(eta, f)
    target = ad.delta + min(ad.Q(P) for P in ad.original_paths())
    assert eta == target, (eta, target)
    rd.append((st["N"], st["J"], st["paths"], str(eta)))
REPORT["random_dags"] = dict(count=len(rd), max_N=max(x[0] for x in rd), examples=rd[:8])
print("random DAGs ok", len(rd), "max N", max(x[0] for x in rd), time.time() - t0, flush=True)

# ---------------------------------------------------------------- 4. diamond chain n=2, n=3: per-scenario checks
for n, nw, all_c in [(2, 12, True), (3, 4, False)]:
    cnt = 0
    for trial in range(nw):
        lo = 0 if trial % 2 == 0 else 1
        ws = {(i, a): random.randint(lo, 5) for i in range(1, n + 1) for a in (0, 1)}
        wp = {(i, j, a, b): random.randint(lo, 5) for i in range(1, n + 1) for j in range(i + 1, n + 1)
              for a in (0, 1) for b in (0, 1)}
        ad = diamond_chain(n, ws, wp)
        for th in scenarios(ad, k_random=3, all_corners=all_c, max_corners=6):
            dual_check(ad, th)
            assignment_checks(ad, th, exact=(cnt % 7 == 0), second_best=(cnt % 5 == 0), lp=(cnt % 23 == 0))
            cnt += 1
    REPORT[f"diamond_n{n}_scenarios_checked"] = cnt
    print(f"diamond n={n}: {cnt} scenarios ok", time.time() - t0, flush=True)

# ---------------------------------------------------------------- 5. eta(w) = 1 + min_z w.m(z)
def eta_by_corners(ad, exact_every=0):
    """min over all corner scenarios of the forced value computed by an assignment solver (no path enumeration).
    h_e is a minimum of affine functions of theta, hence concave, so the box minimum is at a corner."""
    J = len(ad.inter)
    betas = [b for (_, _, b) in ad.inter]
    N = ad.N
    r, c = ad.e
    rows = [i for i in range(N) if i != r]
    cols = [j for j in range(N) if j != c]
    C0 = ad.cost_matrix([Fr(0)] * J)
    A0, L = to_int_matrix(C0)
    assert L == 1
    A0 = np.array(A0, dtype=np.float64)
    rq = [ad.theta_pos[j][0] for j in range(J)]
    kk = [ad.theta_pos[j][1] for j in range(J)]
    best = None
    cnt = 0
    for bits in itertools.product((0, 1), repeat=J):
        A = A0.copy()
        base = 0
        for j in range(J):
            if bits[j]:
                b = int(betas[j])
                A[rq[j]] = b
                A[kk[j]] = b
                base += b
        sub = A[np.ix_(rows, cols)]
        rr, cc = linear_sum_assignment(sub)
        val = int(round(sub[rr, cc].sum())) + int(A[r, c]) - base
        if exact_every and cnt % exact_every == 0:
            th = [betas[j] * bits[j] for j in range(J)]
            C = ad.cost_matrix(th)
            f, _ = exact_forced_min(C, ad.e)
            assert f - perm_cost(C, list(range(N))) == val
        cnt += 1
        best = val if best is None else min(best, val)
    return best, cnt

for n, nw, ex in [(2, 300, 5), (3, 40, 0)]:
    ok = 0
    for trial in range(nw):
        mode = trial % 4
        hi = [4, 9, 1, 30][mode]
        lo = 1 if mode == 1 else 0
        ws = {(i, a): random.randint(lo, hi) for i in range(1, n + 1) for a in (0, 1)}
        wp = {(i, j, a, b): random.randint(lo, hi) for i in range(1, n + 1) for j in range(i + 1, n + 1)
              for a in (0, 1) for b in (0, 1)}
        ad = diamond_chain(n, ws, wp)
        eta, cnt = eta_by_corners(ad, exact_every=ex)
        target = 1 + min_marginal(n, ws, wp)
        assert eta == target, (n, ws, wp, eta, target)
        ok += 1
    REPORT[f"eta_formula_n{n}"] = dict(weight_vectors=ok, corners_each=cnt)
    print(f"eta formula n={n}: {ok} weight vectors, {cnt} corner scenarios each", time.time() - t0, flush=True)

# ---------------------------------------------------------------- 6. outside the box the claims FAIL (scope of "every real scenario")
n = 2
ws = {(i, a): 1 for i in range(1, n + 1) for a in (0, 1)}
wp = {(i, j, a, b): 1 for i in range(1, n + 1) for j in range(i + 1, n + 1) for a in (0, 1) for b in (0, 1)}
ad = diamond_chain(n, ws, wp)
J = len(ad.inter)
out = {}
for name, th in [("theta=beta+5 (above box)", [Fr(6)] * J), ("theta=-5 (below box)", [Fr(-5)] * J)]:
    C = ad.cost_matrix(th)
    base = perm_cost(C, list(range(ad.N)))
    c0, perm0 = exact_min_assignment(C)
    out[name] = dict(identity_cost=str(base), optimum=str(c0), identity_optimal=(c0 == base))
REPORT["outside_box"] = out
print("outside box:", out, flush=True)

json.dump(REPORT, open("adapter_results.json", "w"), indent=1, default=str)
print("ALL ADAPTER CHECKS PASSED", time.time() - t0)
