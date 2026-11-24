"""Independent implementation (B): the construction of Section 2 of the paper, written FROM THE TEXT OF THE PAPER ONLY
(no import of implementation A) and check the statements of Theorem 2, the five lemmas of Section 2,
formula (1) and the formula of the proof of Corollary 3 on small instances, in exact arithmetic."""
import itertools, random, sys
from fractions import Fraction as Fr
from math import lcm, comb
import numpy as np
from scipy.optimize import linear_sum_assignment

random.seed(7)


def build(V, arcs, s, t, alpha, inter, rho, Gamma=None):
    """arcs: list of (x,y); inter: list of (a_j, b_j, beta_j) with arc indices; returns a function theta->matrix."""
    A0 = sum(alpha, Fr(0))
    B0 = sum((b for (_, _, b) in inter), Fr(0))
    if Gamma is None:
        Gamma = rho + A0 + 2 * B0 + 1
    assert Gamma >= rho + A0 + 2 * B0 + 1
    names = list(V)
    names += [("p", a) for a in range(len(arcs))]
    for j in range(len(inter)):
        names += [("f", j), ("f'", j), ("g", j), ("g'", j)]
    idx = {v: i for i, v in enumerate(names)}
    N = len(names)
    assert N == len(V) + len(arcs) + 4 * len(inter)
    darcs = []  # (u, v, kind, data)
    for a, (x, y) in enumerate(arcs):
        cur = ("p", a)
        darcs.append((x, cur, "const", alpha[a]))
        for j, (aj, bj, beta) in enumerate(inter):  # fixed order: by index j
            assert aj != bj
            if aj == a:
                darcs.append((cur, ("f", j), "const", Fr(0)))
                darcs.append((("f", j), ("f'", j), "theta", j))
                cur = ("f'", j)
            if bj == a:
                darcs.append((cur, ("g", j), "const", Fr(0)))
                darcs.append((("g", j), ("g'", j), "const", beta))
                cur = ("g'", j)
        darcs.append((cur, y, "const", Fr(0)))
    e = (idx[t], idx[s])
    # designated entries must be distinct off-diagonal positions
    pos = [(idx[u], idx[v]) for (u, v, _, _) in darcs] + [e]
    assert len(set(pos)) == len(pos) and all(i != j for i, j in pos)

    def C(theta):
        M = [[Gamma] * N for _ in range(N)]
        for i in range(N):
            M[i][i] = Fr(0)
        for j in range(len(inter)):
            M[idx[("g", j)]][idx[("g", j)]] = Fr(theta[j])
        for (u, v, kind, data) in darcs:
            M[idx[u]][idx[v]] = Fr(theta[data]) if kind == "theta" else data
        M[e[0]][e[1]] = rho
        return M

    return dict(N=N, idx=idx, names=names, e=e, C=C, darcs=darcs, Gamma=Gamma, A0=A0, B0=B0)


def paths(V, arcs, s, t):
    out = []

    def rec(v, used):
        if v == t:
            out.append(tuple(used))
            return
        for a, (x, y) in enumerate(arcs):
            if x == v:
                rec(y, used + [a])

    rec(s, [])
    return out


def formula_h(P_list, alpha, inter, rho, theta):
    best = None
    for P in P_list:
        S = set(P)
        v = rho + sum((alpha[a] for a in P), Fr(0))
        for j, (aj, bj, beta) in enumerate(inter):
            if aj in S:
                v += theta[j]
            if bj in S:
                v += beta - theta[j]
        best = v if best is None else min(best, v)
    return best


def Qmin(P_list, alpha, inter):
    best = None
    for P in P_list:
        S = set(P)
        v = sum((alpha[a] for a in P), Fr(0)) + sum((b for (aj, bj, b) in inter if aj in S and bj in S), Fr(0))
        best = v if best is None else min(best, v)
    return best


def to_int(M):
    L = 1
    for row in M:
        for x in row:
            L = lcm(L, x.denominator)
    return [[int(x * L) for x in row] for row in M], L


def hung(Aint):
    A = np.array(Aint, dtype=np.float64)
    r, c = linear_sum_assignment(A)
    return int(round(A[r, c].sum()))


def check_instance(V, arcs, s, t, alpha, inter, rho, thetas, brute=False, Gamma=None):
    B = build(V, arcs, s, t, alpha, inter, rho, Gamma)
    N, e = B["N"], B["e"]
    P_list = paths(V, arcs, s, t)
    assert P_list
    for th in thetas:
        M = B["C"](th)
        assert all(x >= 0 for row in M for x in row)  # (C4)
        base = sum(M[i][i] for i in range(N))
        assert base == sum(th, Fr(0))
        # dual certificate of Lemma 13
        lam = [Fr(0)] * N
        for j in range(len(inter)):
            lam[B["idx"][("g", j)]] = Fr(th[j])
        assert all(lam[i] <= M[i][k] for i in range(N) for k in range(N))
        assert all(lam[i] == M[i][i] for i in range(N)) and sum(lam) == base
        target = formula_h(P_list, alpha, inter, rho, th)
        if brute:
            nopt, forced = 0, None
            for perm in itertools.permutations(range(N)):
                c = sum(M[i][perm[i]] for i in range(N)) - base
                assert c >= 0
                nopt += (c == 0)
                if perm[e[0]] == e[1]:
                    forced = c if forced is None else min(forced, c)
                if c != 0:
                    assert c >= rho
            assert nopt == 1 and forced == target, (forced, target)
        else:
            Aint, L = to_int(M)
            assert Fr(hung(Aint), L) == base
            BIG = sum(max(r) for r in Aint) + 1
            sb = None
            for i in range(N):  # best permutation different from the identity
                old = Aint[i][i]
                Aint[i][i] = BIG
                v = hung(Aint)
                Aint[i][i] = old
                sb = v if sb is None else min(sb, v)
            assert Fr(sb, L) - base >= rho
            rows = [i for i in range(N) if i != e[0]]
            cols = [k for k in range(N) if k != e[1]]
            sub = [[Aint[i][k] for k in cols] for i in rows]
            forced = Fr(hung(sub) + Aint[e[0]][e[1]], L) - base
            assert forced == target, (forced, target)
    return B, P_list


def corners(betas):
    for bits in itertools.product((0, 1), repeat=len(betas)):
        yield [betas[j] * bits[j] for j in range(len(betas))]


# ---- 1. tiny instances, all permutations ---------------------------------------------------------
V = ["s", "x", "t"]
arcs = [("s", "x"), ("x", "t")]
for inter in ([(0, 1, Fr(3))], [(1, 0, Fr(3))]):
    ths = [[Fr(0)], [Fr(3)], [Fr(1, 3)], [Fr(5, 2)]]
    check_instance(V, arcs, "s", "t", [Fr(1, 2), Fr(2)], inter, Fr(1, 4), ths, brute=True)
check_instance(["s", "t"], [("s", "t"), ("s", "t")], "s", "t", [Fr(1), Fr(0)], [(0, 1, Fr(4))], Fr(1, 3),
               [[Fr(0)], [Fr(4)], [Fr(7, 3)]], brute=True)
# direct arc s->t plus arc into s and out of t (N = 4+3 = 7)
check_instance(["x", "s", "t", "y"], [("x", "s"), ("s", "t"), ("t", "y")], "s", "t", [Fr(1), Fr(2), Fr(3)], [],
               Fr(1, 2), [[]], brute=True)
print("tiny instances (all permutations): ok")

# ---- 2. random DAGs ---------------------------------------------------------------------------
cnt = 0
for it in range(40):
    m = random.randint(2, 5)
    Vv = list(range(m))
    arcs = []
    for _ in range(random.randint(2, 7)):
        i = random.randint(0, m - 2)
        arcs.append((i, random.randint(i + 1, m - 1)))
    s, t = 0, m - 1
    if not paths(Vv, arcs, s, t):
        continue
    alpha = [Fr(random.choice([0, 1, 2, 5]), random.choice([1, 2, 3])) for _ in arcs]
    inter = []
    for _ in range(random.randint(0, 4)):
        a, b = random.sample(range(len(arcs)), 2)
        inter.append((a, b, Fr(random.choice([0, 1, 3, 7]), random.choice([1, 2]))))
    betas = [b for (_, _, b) in inter]
    ths = list(corners(betas)) + [[b * Fr(random.randint(0, 11), 11) for b in betas] for _ in range(3)]
    rho = Fr(random.choice([1, 2]), random.choice([1, 3]))
    B, P_list = check_instance(Vv, arcs, s, t, alpha, inter, rho, ths)
    # eta_e over corners (h_e is concave in theta) equals rho + min Q
    eta = min(formula_h(P_list, alpha, inter, rho, th) for th in corners(betas))
    assert eta == rho + Qmin(P_list, alpha, inter)
    cnt += 1
print("random DAGs ok:", cnt)


# ---- 3. diamond family, formula (1), constant Gamma, Corollary 3 --------------------------------
def diamond(n, ws, wp):
    V = [("v", i) for i in range(n + 1)] + [("b", i, a) for i in range(1, n + 1) for a in (0, 1)]
    arcs, alpha, d = [], [], {}
    for i in range(1, n + 1):
        for a in (0, 1):
            d[(i, a)] = len(arcs)
            arcs.append((("v", i - 1), ("b", i, a)))
            alpha.append(Fr(ws[(i, a)]))
            arcs.append((("b", i, a), ("v", i)))
            alpha.append(Fr(0))
    inter = [(d[(i, a)], d[(j, b)], Fr(wp[(i, j, a, b)])) for i in range(1, n + 1) for j in range(i + 1, n + 1)
             for a in (0, 1) for b in (0, 1)]
    return V, arcs, ("v", 0), ("v", n), alpha, inter


def marg_min(n, ws, wp):
    return min(sum(ws[(i, z[i - 1])] for i in range(1, n + 1)) +
               sum(wp[(i, j, z[i - 1], z[j - 1])] for i in range(1, n + 1) for j in range(i + 1, n + 1))
               for z in itertools.product((0, 1), repeat=n))


def eta_via_matrix(n, ws, wp, Gamma):
    V, arcs, s, t, alpha, inter = diamond(n, ws, wp)
    B = build(V, arcs, s, t, alpha, inter, Fr(1), Gamma)
    assert B["N"] == 8 * n * n - n + 1
    N, e = B["N"], B["e"]
    betas = [b for (_, _, b) in inter]
    rows = [i for i in range(N) if i != e[0]]
    cols = [k for k in range(N) if k != e[1]]
    best = None
    for th in corners(betas):
        M = B["C"](th)
        Aint, L = to_int(M)
        base = sum(Aint[i][i] for i in range(N))
        assert hung(Aint) == base  # identity optimal
        sub = [[Aint[i][k] for k in cols] for i in rows]
        f = Fr(hung(sub) + Aint[e[0]][e[1]] - base, L)
        best = f if best is None else min(best, f)
    return best


for n in (1, 2, 3):
    kappa = n + comb(n, 2)
    assert kappa == comb(n + 1, 2)
    GammaConst = Fr(2 + 10 * n + 20 * n * (n - 1))
    pairs = [(i, j) for i in range(1, n + 1) for j in range(i + 1, n + 1)]
    graphs = list(itertools.product((0, 1), repeat=len(pairs)))
    for gbits in graphs:
        E = [p for p, bit in zip(pairs, gbits) if bit]
        ws = {(i, a): 1 for i in range(1, n + 1) for a in (0, 1)}
        wp = {(i, j, a, b): (5 if ((i, j) in E and a == b) else 1) for (i, j) in pairs for a in (0, 1) for b in (0, 1)}
        u = min(sum(1 for (i, j) in E if z[i - 1] == z[j - 1]) for z in itertools.product((0, 1), repeat=n))
        assert 1 + marg_min(n, ws, wp) == 1 + kappa + 4 * u
        if n <= 2 or gbits in (graphs[0], graphs[-1], graphs[3]):
            assert eta_via_matrix(n, ws, wp, GammaConst) == 1 + kappa + 4 * u
    print(f"diamond n={n}: Corollary-3 formula 1+kappa+4u(G) ok for {len(graphs)} graphs "
          f"(matrix-level check with the constant Gamma of Remark 15 on a subset)")
# random weights in {0..5}, n = 2, via the matrix with constant Gamma
for _ in range(25):
    n = 2
    ws = {(i, a): random.randint(0, 5) for i in range(1, n + 1) for a in (0, 1)}
    wp = {(1, 2, a, b): random.randint(0, 5) for a in (0, 1) for b in (0, 1)}
    assert eta_via_matrix(n, ws, wp, Fr(2 + 10 * n + 20 * n * (n - 1))) == 1 + marg_min(n, ws, wp)
print("formula (1), n=2, constant Gamma: ok")
print("ALL CONSTRUCTION CHECKS PASSED")
