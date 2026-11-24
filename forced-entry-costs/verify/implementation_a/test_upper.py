"""Upper endpoint: max over the box of h_e(theta).
(1) Random DAGs: the potential LP  rho + max{pi_t - pi_s : pi_y - pi_x <= l_a(theta), 0<=theta<=beta}  equals the
    path-enumeration LP  rho + max{t : t <= c_theta(P) for all P, 0<=theta<=beta};  at the maximiser theta* the exact
    forced value of the assignment instance equals that number, and at random scenarios it is not larger.
(2) Diamond family n = 2, 3: the dual of the potential LP is ONE fixed polyhedron {A^T u = c, u >= 0} with 4n^2
    inequalities whose value  1 + min (Bw).u  equals the upper endpoint for random integer weights w.
Floating-point LPs (HiGHS); exact rational assignment values."""
from fractions import Fraction as Fr
import itertools, random, json
import numpy as np
from scipy.optimize import linprog
from adapter import Adapter, perm_cost, exact_min_assignment, exact_forced_min, diamond_chain
random.seed(2026)
TOL = 1e-7
def lengths_matrix(nA, inter):
    """l_a(theta) = alpha_a + sum_{j:a_j=a} theta_j + sum_{j:b_j=a} (beta_j - theta_j): returns (const part from beta, coefficient matrix)."""
    J = len(inter); L = np.zeros((nA, J)); c0 = np.zeros(nA)
    for j, (a, b, beta) in enumerate(inter):
        L[a, j] += 1.0; L[b, j] -= 1.0; c0[b] += float(beta)
    return c0, L
def potential_lp(V, arcs, s, t, alpha, inter):
    nV, nA, J = len(V), len(arcs), len(inter); vi = {v: i for i, v in enumerate(V)}
    c0, L = lengths_matrix(nA, inter)
    A = np.zeros((nA, nV + J)); b = np.zeros(nA)
    for a, (x, y) in enumerate(arcs):
        A[a, vi[y]] += 1.0; A[a, vi[x]] -= 1.0; A[a, nV:] = -L[a]; b[a] = float(alpha[a]) + c0[a]
    obj = np.zeros(nV + J); obj[vi[t]] = -1.0; obj[vi[s]] = 1.0
    bounds = [(None, None)] * nV + [(0.0, float(be)) for (_, _, be) in inter]
    r = linprog(obj, A_ub=A, b_ub=b, bounds=bounds, method="highs"); assert r.status == 0, r.message
    return -r.fun, r.x[nV:]
def path_lp(paths, alpha, inter):
    J = len(inter); rows = []; rhs = []
    for P in paths:
        Ps = set(P); row = np.zeros(1 + J); row[0] = 1.0; const = sum(float(alpha[a]) for a in P)
        for j, (a, b, beta) in enumerate(inter):
            if a in Ps: row[1 + j] -= 1.0
            if b in Ps: row[1 + j] += 1.0; const += float(beta)
        rows.append(row); rhs.append(const)
    obj = np.zeros(1 + J); obj[0] = -1.0
    r = linprog(obj, A_ub=np.array(rows), b_ub=np.array(rhs), bounds=[(None, None)] + [(0.0, float(be)) for (_, _, be) in inter], method="highs")
    assert r.status == 0, r.message
    return -r.fun
res = {"dags": 0, "max_abs_diff_lps": 0.0, "max_abs_diff_exact": 0.0, "strictly_interior_gain": 0}
while res["dags"] < 40:
    nv = random.randint(4, 6); V = list(range(nv)); s, t = 0, nv - 1
    arcs = [(u, v) for u in V for v in V if u < v and random.random() < 0.6]
    if random.random() < 0.3 and arcs: arcs.append(random.choice(arcs))      # a parallel arc
    reach = {s}
    for u in V:
        if u in reach: reach |= {v for (x, v) in arcs if x == u}
    if t not in reach or len(arcs) < 3: continue
    alpha = [Fr(random.randint(0, 4)) for _ in arcs]
    J = random.randint(1, 4); inter = []
    for _ in range(J):
        a, b = random.sample(range(len(arcs)), 2); inter.append((a, b, Fr(random.randint(1, 5))))
    ad = Adapter(V, arcs, s, t, alpha, inter, Fr(1)); P = ad.original_paths()
    v1, th = potential_lp(V, arcs, s, t, alpha, inter); v2 = path_lp(P, alpha, inter)
    res["max_abs_diff_lps"] = max(res["max_abs_diff_lps"], abs(v1 - v2)); assert abs(v1 - v2) < TOL, (v1, v2)
    betas = [b for (_, _, b) in inter]
    thq = [min(max(Fr(float(x)).limit_denominator(10**6), Fr(0)), betas[j]) for j, x in enumerate(th)]
    def h(theta):
        C = ad.cost_matrix(theta); base = perm_cost(C, list(range(ad.N))); f, _ = exact_forced_min(C, ad.e); return f - base
    hstar = h(thq); d = abs(float(hstar) - (1 + v1)); res["max_abs_diff_exact"] = max(res["max_abs_diff_exact"], d); assert d < 1e-4, (hstar, v1)
    corner_best = max(h([b * bit for b, bit in zip(betas, bits)]) for bits in itertools.product((0, 1), repeat=J))
    assert float(corner_best) <= 1 + v1 + TOL
    if float(corner_best) < 1 + v1 - 1e-6: res["strictly_interior_gain"] += 1
    for _ in range(5):
        assert float(h([b * Fr(random.randint(0, 9), 9) for b in betas])) <= 1 + v1 + TOL
    res["dags"] += 1
# (2) one fixed polyhedron for the diamond family
dia = {}
for n in (2, 3):
    ws0 = {(i, a): Fr(1) for i in range(1, n + 1) for a in (0, 1)}
    wp0 = {(i, j, a, b): Fr(1) for i in range(1, n + 1) for j in range(i + 1, n + 1) for a in (0, 1) for b in (0, 1)}
    ad = diamond_chain(n, ws0, wp0); V, arcs = ad.V, ad.arcs; nV, nA, J = len(V), len(arcs), len(ad.inter); vi = {v: i for i, v in enumerate(V)}
    # weights: alpha_a for the 2n weighted arcs (others are 0 by construction) and beta_j; w -> (alpha, beta) is a coordinate map.
    warcs = [a for a in range(nA) if ad.alpha[a] != 0]; assert len(warcs) == 2 * n and J == 2 * n * (n - 1)
    d = len(warcs) + J
    # primal: max pi_t - pi_s s.t. A x <= B w, x = (pi, theta); rows: nA arc rows, J rows theta_j <= w, J rows -theta_j <= 0
    m = nA + 2 * J; A = np.zeros((m, nV + J)); B = np.zeros((m, d))
    for a, (x, y) in enumerate(arcs):
        A[a, vi[y]] += 1.0; A[a, vi[x]] -= 1.0
        if a in warcs: B[a, warcs.index(a)] = 1.0
    for j, (a, b, _) in enumerate(ad.inter):
        A[a, nV + j] -= 1.0; A[b, nV + j] += 1.0; B[b, len(warcs) + j] += 1.0
        A[nA + j, nV + j] = 1.0; B[nA + j, len(warcs) + j] = 1.0
        A[nA + J + j, nV + j] = -1.0
    c = np.zeros(nV + J); c[vi[ad.t]] = 1.0; c[vi[ad.s]] = -1.0
    assert m == 4 * n * n, (m, n)
    worst = 0.0
    for _ in range(25):
        w = np.array([random.randint(0, 5) for _ in range(d)], dtype=float)
        rp = linprog(-c, A_ub=A, b_ub=B @ w, bounds=[(None, None)] * (nV + J), method="highs"); assert rp.status == 0
        rd = linprog(B @ w, A_eq=A.T, b_eq=c, bounds=[(0, None)] * m, method="highs"); assert rd.status == 0
        alpha = [Fr(0)] * nA
        for k, a in enumerate(warcs): alpha[a] = Fr(int(w[k]))
        inter = [(a, b, Fr(int(w[len(warcs) + j]))) for j, (a, b, _) in enumerate(ad.inter)]
        ad2 = Adapter(V, arcs, ad.s, ad.t, alpha, inter, Fr(1)); v2 = path_lp(ad2.original_paths(), alpha, inter)
        worst = max(worst, abs(-rp.fun - rd.fun), abs(rd.fun - v2)); assert worst < TOL, worst
    dia[n] = {"inequalities": m, "weights": d, "max_abs_diff": worst}
res["diamond_fixed_polyhedron"] = dia
print("upper endpoint ok:", res)
json.dump(res, open("upper_results.json", "w"))
