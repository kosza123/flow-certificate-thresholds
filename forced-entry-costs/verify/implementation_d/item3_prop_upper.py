"""Item 3: Proposition 9 (the upper endpoint).
 (A) general LP with (N-1)^2+k inequalities  vs  epigraph LP over all permutations with X_e=1
     (random affine C(theta), arbitrary signs, F not assumed optimal, Theta = box cut by random half-spaces).
 (B) potential LP with |A|+2|J| inequalities  vs  path enumeration, on random DAGs with dead ends,
     vertices unreachable from s, vertices not reaching t, zero lengths, parallel arcs;
     also vs the general LP (A) on the assignment instance of Section 2, and vs the integer forced value
     at the (rational) maximiser when it is half-integral.
 (C) diamond family n=2,3: the matrix A of the potential LP does not depend on w; the fixed polyhedron
     P = {u >= 0 : A^T u = c} has exactly 4n^2 inequalities; 1 + min_{u in P} (Bw).u  equals
     max_theta h_e(theta) for random w >= 0 including zeros and non-integers.
"""
import itertools, random, json
import numpy as np
from scipy.optimize import linprog, linear_sum_assignment
from adapter_sec2 import build, paths, diamond

TOL = 1e-7

def lp_max(c, A_ub, b_ub, A_eq=None, b_eq=None, bounds=None):
    r = linprog(-np.array(c, float), A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                bounds=bounds if bounds is not None else [(None, None)] * len(c), method='highs')
    assert r.status == 0, r.message
    return -r.fun, r.x

# ---------------------------------------------------------------- (A)
def general_lp(const, coef, F, e, G, g):
    """max C_e(th) - C(th).F + sum u + sum v ; u_i+v_j <= C_ij(th) (i!=r, j!=c) ; G th <= g.
    variables: theta (K), u (N), v (N)  (u_r, v_c fixed to 0, unused)."""
    N = const.shape[0]; K = len(coef); r_, c_ = e
    nvar = K + 2 * N
    obj = np.zeros(nvar)
    for k in range(K):
        obj[k] = coef[k][r_, c_] - sum(coef[k][i, F[i]] for i in range(N))
    cst = const[r_, c_] - sum(const[i, F[i]] for i in range(N))
    rows = []; rhs = []
    for i in range(N):
        if i == r_:
            continue
        obj[K + i] = 1
        for j in range(N):
            if j == c_:
                continue
            row = np.zeros(nvar); row[K + i] = 1; row[K + N + j] = 1
            for k in range(K):
                row[k] = -coef[k][i, j]
            rows.append(row); rhs.append(const[i, j])
    for j in range(N):
        if j != c_:
            obj[K + N + j] = 1
    n_dual = len(rows)
    for row_, b_ in zip(G, g):
        row = np.zeros(nvar); row[:K] = row_; rows.append(row); rhs.append(b_)
    val, x = lp_max(obj, np.array(rows, float), np.array(rhs, float))
    return float(cst) + val, x[:K], n_dual, len(G)

def epigraph_lp(const, coef, F, e, G, g):
    N = const.shape[0]; K = len(coef)
    rows = []; rhs = []
    for X in itertools.permutations(range(N)):
        if X[e[0]] != e[1]:
            continue
        # t <= C(th).(X-F)
        row = np.zeros(K + 1); row[K] = 1
        cst = 0
        for i in range(N):
            cst += const[i, X[i]] - const[i, F[i]]
            for k in range(K):
                row[k] -= coef[k][i, X[i]] - coef[k][i, F[i]]
        rows.append(row); rhs.append(cst)
    for row_, b_ in zip(G, g):
        row = np.zeros(K + 1); row[:K] = row_; rows.append(row); rhs.append(b_)
    obj = np.zeros(K + 1); obj[K] = 1
    val, x = lp_max(obj, np.array(rows, float), np.array(rhs, float))
    return val

def test_A(trials, seed):
    rng = random.Random(seed); worst = 0.0; neg = 0
    for _ in range(trials):
        N = rng.choice([2, 3, 4, 5]); K = rng.randint(1, 4)
        F = list(range(N)); rng.shuffle(F)
        out = [(i, j) for i in range(N) for j in range(N) if F[i] != j]
        e = rng.choice(out)
        const = np.array([[rng.randint(-5, 8) for _ in range(N)] for _ in range(N)], float)
        coef = [np.array([[rng.choice([0, 0, 1, -1, 2, -3]) for _ in range(N)] for _ in range(N)], float) for _ in range(K)]
        lo = [rng.randint(-2, 2) for _ in range(K)]; hi = [l + rng.randint(0, 3) for l in lo]
        G = []; g = []
        for k in range(K):
            r1 = [0] * K; r1[k] = 1; G.append(r1); g.append(hi[k])
            r2 = [0] * K; r2[k] = -1; G.append(r2); g.append(-lo[k])
        mid = [(l + h) / 2 for l, h in zip(lo, hi)]
        for _ in range(rng.randint(0, 2)):               # extra half-spaces through a neighbourhood of the centre
            a = [rng.randint(-2, 2) for _ in range(K)]
            G.append(a); g.append(sum(x * y for x, y in zip(a, mid)) + rng.randint(0, 2))
        v1, th, nd, k_ = general_lp(const, coef, F, e, G, g)
        assert nd == (N - 1) ** 2 and k_ == len(G)
        v2 = epigraph_lp(const, coef, F, e, G, g)
        worst = max(worst, abs(v1 - v2)); neg += (v1 < -TOL)
    return dict(trials=trials, max_abs_diff=worst, instances_with_negative_max=neg)

# ---------------------------------------------------------------- (B)
def potential_lp(nv, arcs, s, t, alpha, J, beta):
    """max pi_t - pi_s ; pi_y - pi_x - sum_{a_j=a} th_j + sum_{b_j=a} th_j <= alpha_a + sum_{b_j=a} beta_j ;
       -th_j <= 0 ; th_j <= beta_j.   Returns value, theta, A, rhs-builder pieces."""
    K = len(J); nvar = nv + K
    A = np.zeros((len(arcs) + 2 * K, nvar)); rhs = np.zeros(len(arcs) + 2 * K)
    for ai, (x, y) in enumerate(arcs):
        A[ai, y] += 1; A[ai, x] -= 1; rhs[ai] = alpha[ai]
        for j, (a, b) in enumerate(J):
            if a == ai:
                A[ai, nv + j] -= 1
            if b == ai:
                A[ai, nv + j] += 1; rhs[ai] += beta[j]
    for j in range(K):
        A[len(arcs) + 2 * j, nv + j] = -1
        A[len(arcs) + 2 * j + 1, nv + j] = 1; rhs[len(arcs) + 2 * j + 1] = beta[j]
    c = np.zeros(nvar); c[t] += 1; c[s] -= 1
    val, x = lp_max(c, A, rhs)
    return val, x[nv:], A, rhs, c

def path_epigraph(nv, arcs, s, t, alpha, J, beta):
    P = paths(nv, arcs, s, t); K = len(J)
    rows = []; rhs = []
    for p in P:
        ps = set(p); row = np.zeros(K + 1); row[K] = 1; cst = sum(alpha[a] for a in p)
        for j, (a, b) in enumerate(J):
            if a in ps:
                row[j] -= 1
            if b in ps:
                row[j] += 1; cst += beta[j]
        rows.append(row); rhs.append(cst)
    obj = np.zeros(K + 1); obj[K] = 1
    val, x = lp_max(obj, np.array(rows), np.array(rhs), bounds=[(0, b) for b in beta] + [(None, None)])
    return val, len(P)

def forced_int(C, e):
    N = C.shape[0]
    rows = [i for i in range(N) if i != e[0]]; cols = [j for j in range(N) if j != e[1]]
    sub = np.array(C[np.ix_(rows, cols)], dtype=np.int64)
    r, c = linear_sum_assignment(sub)
    return int(C[e]) + int(sub[r, c].sum())

def random_dag(rng):
    core = rng.randint(2, 5)                 # vertices 0..core-1 with s=0, t=core-1
    extra = rng.randint(0, 3)
    nv = core + extra
    arcs = [(x, y) for x in range(core) for y in range(x + 1, core) if rng.random() < 0.6]
    for z in range(core, nv):                # extra vertices: dead ends, unreachable sources, or both
        kind = rng.choice(['dead', 'source', 'isolated', 'through'])
        if kind in ('dead', 'through'):
            arcs.append((rng.randrange(0, core), z))            # leaves the core (possibly from t), may not reach t
        if kind in ('source',):
            arcs.append((z, rng.randrange(0, core)))            # not reachable from s, enters the core (possibly at s)
        if kind == 'through' and rng.random() < 0.5:
            arcs.append((z, core - 1))
    if rng.random() < 0.4:
        arcs.append((core - 1, rng.randrange(core, nv)) if extra else (0, core - 1))   # arc leaving t / parallel
    if arcs and rng.random() < 0.3:
        arcs.append(rng.choice(arcs))        # parallel arc
    return nv, arcs, 0, core - 1

def test_B(trials, seed):
    rng = random.Random(seed); done = 0; worst_pp = worst_gen = 0.0; exact_checked = 0; interior = 0
    stats = dict(with_unreachable=0, with_dead_end=0)
    while done < trials:
        nv, arcs, s, t = random_dag(rng)
        if len(arcs) < 2:
            continue
        P = paths(nv, arcs, s, t)
        if not P:
            continue
        # is the graph acyclic? (arcs out of t into an extra vertex that goes back to core would make a cycle)
        order_ok = True
        try:
            import networkx as nx
            Gx = nx.MultiDiGraph(); Gx.add_nodes_from(range(nv)); Gx.add_edges_from(arcs)
            order_ok = nx.is_directed_acyclic_graph(Gx)
            reach = nx.descendants(Gx, s) | {s}
            coreach = nx.ancestors(Gx, t) | {t}
        except ImportError:
            reach = coreach = set(range(nv))
        if not order_ok:
            continue
        stats['with_unreachable'] += any(v not in reach for v in range(nv))
        stats['with_dead_end'] += any(v in reach and v not in coreach for v in range(nv))
        K = rng.randint(1, min(4, len(arcs) * (len(arcs) - 1)))
        J = []
        for _ in range(K):
            a, b = rng.sample(range(len(arcs)), 2); J.append((a, b))
        alpha = [rng.randint(0, 3) for _ in arcs]; beta = [rng.randint(0, 4) for _ in J]
        v_pot, th, A, rhs, c = potential_lp(nv, arcs, s, t, alpha, J, beta)
        assert A.shape[0] == len(arcs) + 2 * len(J)
        v_path, npaths = path_epigraph(nv, arcs, s, t, alpha, J, beta)
        worst_pp = max(worst_pp, abs(v_pot - v_path))
        # assignment instance of Section 2 and the general LP
        names, idx, const, coef, e, N = build(nv, arcs, s, t, alpha, J, beta, rho=1)
        if N <= 40:
            Gm = []; g = []
            for j in range(len(J)):
                r1 = [0] * len(J); r1[j] = 1; Gm.append(r1); g.append(beta[j])
                r2 = [0] * len(J); r2[j] = -1; Gm.append(r2); g.append(0)
            v_gen, th2, nd, k_ = general_lp(np.array(const, float), [np.array(m, float) for m in coef],
                                            list(range(N)), e, Gm, g)
            assert nd == (N - 1) ** 2 and k_ == 2 * len(J)
            worst_gen = max(worst_gen, abs(v_gen - (1 + v_pot)))
        # exact forced value at the maximiser, when it is half-integral
        th_r = [round(2 * x) / 2 for x in th]
        if max(abs(a - b) for a, b in zip(th, th_r)) < 1e-9:
            C2 = 2 * const.copy()
            for j, x in enumerate(th_r):
                C2 = C2 + int(round(2 * x)) * coef[j]
            hval = (forced_int(C2, e) - int(sum(C2[i, i] for i in range(N)))) / 2
            assert abs(hval - (1 + v_pot)) < TOL, (hval, v_pot)
            exact_checked += 1
            interior += any(0 < x < b for x, b in zip(th_r, beta))
        done += 1
    return dict(trials=trials, max_diff_potential_vs_paths=worst_pp, max_diff_general_vs_potential=worst_gen,
                exact_forced_value_checked=exact_checked, maximiser_not_a_corner=interior, **stats)

# ---------------------------------------------------------------- (C)
def test_C(n, nw, seed):
    rng = random.Random(seed)
    edges = [(i, j) for i in range(1, n + 1) for j in range(i + 1, n + 1)]
    Aref = None; worst = worst_gen = 0.0; lower_vs_upper = 0
    for trial in range(nw):
        mode = trial % 4
        def draw():
            if mode == 0: return rng.randint(0, 5)
            if mode == 1: return rng.choice([0, 0, 1, 5])
            if mode == 2: return rng.uniform(0, 5) if rng.random() < 0.8 else 0.0
            return rng.randint(1, 5)
        w1 = {(i, a): draw() for i in range(1, n + 1) for a in (0, 1)}
        w2 = {(i, j, a, b): draw() for (i, j) in edges for a in (0, 1) for b in (0, 1)}
        nv, arcs, s, t, alpha, J, beta, keys = diamond(n, edges, w1, w2)
        v_pot, th, A, rhs, c = potential_lp(nv, arcs, s, t, alpha, J, beta)
        m = A.shape[0]
        assert m == len(arcs) + 2 * len(J) == 4 * n + 4 * n * (n - 1) == 4 * n * n
        if Aref is None:
            Aref = A.copy()
            # rhs = B w with a fixed 0/1 matrix B: recover B column by column from unit weights
            wkeys = [('s', k) for k in w1] + [('p', k) for k in w2]
            B = np.zeros((m, len(wkeys)))
            for col, (kind, k) in enumerate(wkeys):
                u1 = {kk: 0 for kk in w1}; u2 = {kk: 0 for kk in w2}
                (u1 if kind == 's' else u2)[k] = 1
                d = diamond(n, edges, u1, u2)
                _, _, A1, rhs1, _ = potential_lp(d[0], d[1], d[2], d[3], d[4], d[5], d[6])
                assert (A1 == Aref).all()
                B[:, col] = rhs1
            assert len(wkeys) == 2 * n * n
            # rhs at w = 0 is 0  (b = 0)
            z1 = {kk: 0 for kk in w1}; z2 = {kk: 0 for kk in w2}
            d = diamond(n, edges, z1, z2)
            assert not potential_lp(d[0], d[1], d[2], d[3], d[4], d[5], d[6])[3].any()
        assert (A == Aref).all()                     # weights only in the right-hand side
        wvec = np.array([w1[k] for k in w1] + [w2[k] for k in w2], float)
        assert np.allclose(B @ wvec, rhs)
        # fixed polyhedron P = {u >= 0 : A^T u = c}; value 1 + min (B w).u
        r = linprog(B @ wvec, A_eq=Aref.T, b_eq=c, bounds=[(0, None)] * m, method='highs')
        assert r.status == 0
        v_fixed = 1 + r.fun
        v_path, npaths = path_epigraph(nv, arcs, s, t, alpha, J, beta)
        assert npaths == 2 ** n
        worst = max(worst, abs(v_fixed - (1 + v_path)), abs(v_fixed - (1 + v_pot)))
        # lower endpoint for comparison
        zs = list(itertools.product((0, 1), repeat=n))
        low = 1 + min(sum(w1[(i, z[i - 1])] for i in range(1, n + 1)) +
                      sum(w2[(i, j, z[i - 1], z[j - 1])] for (i, j) in edges) for z in zs)
        assert low <= v_fixed + TOL
        lower_vs_upper += (v_fixed > low + TOL)
        if trial < 6:                                # general LP on the N x N assignment instance
            names, idx, const, coef, e, N = build(nv, arcs, s, t, alpha, J, beta, rho=1)
            assert N == 8 * n * n - n + 1
            Gm = []; g = []
            for j in range(len(J)):
                r1 = [0] * len(J); r1[j] = 1; Gm.append(r1); g.append(beta[j])
                r2 = [0] * len(J); r2[j] = -1; Gm.append(r2); g.append(0)
            v_gen, _, nd, k_ = general_lp(np.array(const, float), [np.array(mm, float) for mm in coef],
                                          list(range(N)), e, Gm, g)
            worst_gen = max(worst_gen, abs(v_gen - v_fixed))
    return dict(n=n, inequalities_of_fixed_polyhedron=int(m), four_n_squared=4 * n * n, weight_vectors=nw,
                max_abs_diff=worst, max_abs_diff_vs_general_LP=worst_gen, upper_strictly_above_lower=lower_vs_upper,
                equations=int(Aref.shape[1]), rank_of_equations=int(np.linalg.matrix_rank(Aref.T)))

if __name__ == '__main__':
    res = {}
    res['A_general_LP_vs_permutation_epigraph'] = test_A(400, 11)
    print(json.dumps(res, indent=1), flush=True)
    res['B_potential_LP_vs_paths'] = test_B(300, 12)
    print(json.dumps(res['B_potential_LP_vs_paths'], indent=1), flush=True)
    res['C_diamond'] = [test_C(1, 20, 13), test_C(2, 200, 14), test_C(3, 60, 15)]
    print(json.dumps(res['C_diamond'], indent=1))
    json.dump(res, open(__file__.replace('.py', '_results.json'), 'w'), indent=1)
