"""Checks for the approximation results (Sections 5 and 6 of the paper): the sandwich for L_t, the entropy/rounding certificate, identities of the additive-error theorem."""
import itertools, json, math, random, time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

random.seed(7)
rng = np.random.default_rng(7)
REPORT = {}
t0 = time.time()


def kn(n):
    return n + n * (n - 1) // 2


def all_h(n, ws, wp):
    """vector of w.m(z) over all z (ws[i][a], wp[(i,j)][a][b])."""
    vals = []
    for z in itertools.product((0, 1), repeat=n):
        v = sum(ws[i][z[i]] for i in range(n))
        v += sum(wp[(i, j)][z[i]][z[j]] for i in range(n) for j in range(i + 1, n))
        vals.append(v)
    return np.array(vals)


class LocalLP:
    """Sherali-Adams style local-marginal polytope of level r=t+1 exactly as in the proof of the fixed-relative-error theorem (Section 6 of the paper):
    variables mu_S(x_S) for all |S|<=r, normalization + marginal consistency EQUATIONS,
    nonnegativity ONLY on |S|=r."""

    def __init__(self, n, t):
        self.n, self.t, self.r = n, t, t + 1
        assert 1 <= t and self.r <= n
        self.sets = [S for s in range(self.r + 1) for S in itertools.combinations(range(n), s)]
        self.var = {}
        for S in self.sets:
            for x in itertools.product((0, 1), repeat=len(S)):
                self.var[(S, x)] = len(self.var)
        nv = len(self.var)
        rows = []
        rhs = []
        # normalization: mu_emptyset = 1
        rows.append({self.var[((), ())]: 1.0})
        rhs.append(1.0)
        for S in self.sets:
            for pos, i in enumerate(S):
                Sm = S[:pos] + S[pos + 1:]
                for xm in itertools.product((0, 1), repeat=len(Sm)):
                    row = {self.var[(Sm, xm)]: -1.0}
                    for xi in (0, 1):
                        x = xm[:pos] + (xi,) + xm[pos:]
                        row[self.var[(S, x)]] = 1.0
                    rows.append(row)
                    rhs.append(0.0)
        A = lil_matrix((len(rows), nv))
        for ri, row in enumerate(rows):
            for c, v in row.items():
                A[ri, c] = v
        self.Aeq = A.tocsr()
        self.beq = np.array(rhs)
        self.bounds = [(0, None) if len(S) == self.r else (None, None) for (S, x) in self.var]
        self.n_ineq = sum(1 for b in self.bounds if b[0] == 0)
        assert self.n_ineq == 2 ** self.r * math.comb(n, self.r)

    def solve(self, ws, wp):
        c = np.zeros(len(self.var))
        n = self.n
        for i in range(n):
            for a in (0, 1):
                c[self.var[((i,), (a,))]] = ws[i][a]
        for i in range(n):
            for j in range(i + 1, n):
                for a in (0, 1):
                    for b in (0, 1):
                        c[self.var[((i, j), (a, b))]] = wp[(i, j)][a][b]
        res = linprog(c, A_eq=self.Aeq, b_eq=self.beq, bounds=self.bounds, method="highs")
        assert res.status == 0, res.message
        return 1.0 + res.fun, res.x

    def dist(self, x, S):
        S = tuple(sorted(set(S)))
        return np.array([max(0.0, x[self.var[(S, xs)]]) for xs in itertools.product((0, 1), repeat=len(S))]), S


def rand_weights(n, mode):
    def val():
        if mode == "uniform":
            return random.uniform(1, 5)
        if mode == "ends":
            return random.choice([1.0, 5.0])
        if mode == "int":
            return float(random.randint(1, 5))
    ws = [[val(), val()] for _ in range(n)]
    wp = {(i, j): [[val(), val()], [val(), val()]] for i in range(n) for j in range(i + 1, n)}
    if mode == "antiferro":
        ws = [[1.0, 1.0] for _ in range(n)]
        wp = {(i, j): [[5.0, 1.0], [1.0, 5.0]] for i in range(n) for j in range(i + 1, n)}
    if mode == "frustrated":
        ws = [[1.0, 1.0] for _ in range(n)]
        wp = {}
        for i in range(n):
            for j in range(i + 1, n):
                wp[(i, j)] = [[5.0, 1.0], [1.0, 5.0]] if random.random() < 0.5 else [[1.0, 5.0], [5.0, 1.0]]
    return ws, wp


# ------------------------------------------------------------------ 1. sandwich (3.1)
sand = []
maxratio = 0.0
for n in range(2, 7):
    for t in range(1, n):
        lp = LocalLP(n, t)
        bound = n * n * math.sqrt(2 * math.log(2) / t)
        worst_gap = 0.0
        cnt = 0
        modes = ["uniform"] * 12 + ["ends"] * 8 + ["int"] * 4 + ["frustrated"] * 8 + ["antiferro"]
        if n == 6 and t >= 4:
            modes = modes[::3]
        for mode in modes:
            ws, wp = rand_weights(n, mode)
            L, x = lp.solve(ws, wp)
            eta = 1.0 + all_h(n, ws, wp).min()
            tol = 1e-7
            assert 1 + kn(n) <= L + tol, "L_t < 1+k_n"
            assert L <= eta + tol, "L_t > eta"
            assert eta <= L + bound + tol, "eta > L_t + bound"
            if t + 1 == n:
                assert abs(L - eta) < 1e-6, "full level not exact"
            worst_gap = max(worst_gap, eta - L)
            cnt += 1
        maxratio = max(maxratio, worst_gap / bound)
        sand.append(dict(n=n, t=t, inequalities=lp.n_ineq, variables=len(lp.var), instances=cnt,
                         max_gap=round(worst_gap, 6), bound=round(bound, 4)))
        print(sand[-1], round(time.time() - t0, 1), flush=True)
REPORT["sandwich"] = sand
REPORT["sandwich_max_gap_over_bound"] = maxratio

# ------------------------------------------------------------------ 2. section 4 gap example (pair-local LP, t=1)
ex = []
for n in (2, 4, 6):
    lp = LocalLP(n, 1)
    ws, wp = rand_weights(n, "antiferro")
    L, x = lp.solve(ws, wp)
    eta = 1.0 + all_h(n, ws, wp).min()
    claimed_true = 1 + kn(n) + n * n - 2 * n
    claimed_lp = 1 + kn(n)
    assert abs(eta - claimed_true) < 1e-9
    if n >= 3:  # for n=2 level r=2 is the exact simplex, so the "pair-local" fractional point is NOT feasible
        assert abs(L - claimed_lp) < 1e-7
    ex.append(dict(n=n, L1=L, eta=eta, claimed_LP=claimed_lp, claimed_true=claimed_true))
REPORT["gap_example"] = ex
print("gap example", ex, flush=True)

# ------------------------------------------------------------------ 3. entropy telescoping (3.6),(3.7) and rounding (3.8),(3.9) on LP optima
def H(p):
    p = p[p > 1e-15]
    return float(-(p * np.log(p)).sum())


def cert(lp, x, ws, wp):
    n, t = lp.n, lp.t
    ent = {}

    def HS(S):
        S = tuple(sorted(set(S)))
        if S not in ent:
            ent[S] = H(lp.dist(x, S)[0])
        return ent[S]

    Hs = []
    EI = []
    for s in range(t + 1):
        acc = 0.0
        acci = 0.0
        for S in itertools.product(range(n), repeat=s):
            for i in range(n):
                acc += HS(S + (i,)) - HS(S)
                if s < t:
                    for j in range(n):
                        mi = HS(S + (i,)) + HS(S + (j,)) - HS(S + (i, j)) - HS(S)
                        assert mi > -1e-7, "negative conditional mutual information"
                        acci += mi
        Hs.append(acc / (n ** (s + 1)))
        if s < t:
            EI.append(acci / (n ** (s + 2)))
    for s in range(t):
        assert abs(Hs[s] - Hs[s + 1] - EI[s]) < 1e-7, "telescoping identity (3.6)"
    assert -1e-9 <= Hs[t] <= Hs[0] + 1e-9 <= math.log(2) + 2e-9
    s = int(np.argmin(EI))
    assert EI[s] <= math.log(2) / t + 1e-9, "(3.7)"
    # rounding with seed tuples of length s
    exp_cost = 0.0
    exp_tv = 0.0
    lp_single = 0.0
    lp_pair = 0.0
    for S in itertools.product(range(n), repeat=s):
        pS, Sset = lp.dist(x, S)
        for xi, xS in enumerate(itertools.product((0, 1), repeat=len(Sset))):
            pr = pS[xi]
            if pr <= 1e-13:
                continue
            seed = dict(zip(Sset, xS))

            def cond(T):
                """conditional law of X_T given the seed, T tuple of distinct indices."""
                out = np.zeros((2,) * len(T))
                U = tuple(sorted(set(Sset) | set(T)))
                pU, _ = lp.dist(x, U)
                for ui, xU in enumerate(itertools.product((0, 1), repeat=len(U))):
                    asg = dict(zip(U, xU))
                    if all(asg[v] == seed[v] for v in Sset):
                        out[tuple(asg[v] for v in T)] += pU[ui]
                return out / pr

            p1 = [cond((i,)) for i in range(n)]
            cost = sum(ws[i][a] * p1[i][a] for i in range(n) for a in (0, 1))
            tvsum = 0.0
            for i in range(n):
                for j in range(i + 1, n):
                    prod = np.outer(p1[i], p1[j])
                    pij = cond((i, j))
                    W = np.array(wp[(i, j)])
                    cost += float((W * prod).sum())
                    tv = 0.5 * np.abs(pij - prod).sum()
                    assert abs(float((W * prod).sum()) - float((W * pij).sum())) <= 4 * tv + 1e-9
                    tvsum += 4 * tv
                    lp_pair += pr * float((W * pij).sum()) / n ** s
            lp_single += pr * sum(ws[i][a] * p1[i][a] for i in range(n) for a in (0, 1)) / n ** s
            exp_cost += pr * cost / n ** s
            exp_tv += pr * tvsum / n ** s
    obj = sum(ws[i][a] * x[lp.var[((i,), (a,))]] for i in range(n) for a in (0, 1)) + \
        sum(wp[(i, j)][a][b] * x[lp.var[((i, j), (a, b))]] for i in range(n) for j in range(i + 1, n)
            for a in (0, 1) for b in (0, 1))
    assert abs(lp_single + lp_pair - obj) < 1e-6, "seed-averaging does not recover LP cost"
    bound = n * n * math.sqrt(2 * math.log(2) / t)
    assert exp_tv <= bound + 1e-9, "(3.9)"
    assert exp_cost <= obj + exp_tv + 1e-7
    hmin = all_h(n, ws, wp).min()
    assert hmin <= exp_cost + 1e-7
    return dict(s=s, EI=EI[s], exp_round_cost=exp_cost, lp_obj=obj, exp_4tv=exp_tv, bound=bound, true_min=float(hmin))


certs = []
for (n, t) in [(4, 1), (4, 2), (5, 2), (5, 3), (6, 2), (6, 3)]:
    lp = LocalLP(n, t)
    for mode in ["uniform", "frustrated", "ends", "antiferro"]:
        ws, wp = rand_weights(n, mode)
        L, x = lp.solve(ws, wp)
        c = cert(lp, x, ws, wp)
        c.update(n=n, t=t, mode=mode)
        certs.append(c)
REPORT["rounding_certificates"] = certs
print("entropy/rounding certificate ok on", len(certs), "LP optima; max E[4TV]/bound =",
      max(c["exp_4tv"] / c["bound"] for c in certs), round(time.time() - t0, 1), flush=True)

# ------------------------------------------------------------------ 4. Theorem A identities
def coords(n):
    c = [("s", i, a) for i in range(n) for a in (0, 1)]
    c += [("p", i, j, a, b) for i in range(n) for j in range(i + 1, n) for a in (0, 1) for b in (0, 1)]
    return c


def Mmat(n):
    C = coords(n)
    return np.array([[int(z[c[1]] == c[2]) if c[0] == "s" else int((z[c[1]], z[c[2]]) == (c[3], c[4])) for c in C]
                     for z in itertools.product((0, 1), repeat=n)]), C


# 4a. h(c_q + r) = k + r.q for all q, random sign vectors r
for n in range(1, 6):
    M, C = Mmat(n)
    d = len(C)
    for qi in range(len(M)):
        q = M[qi]
        cq = 3 - 2 * q
        for _ in range(40):
            r = rng.choice([-1, 1], size=d)
            probe = cq + r
            assert probe.min() >= 0 and probe.max() <= 4
            assert (M @ probe).min() == kn(n) + r @ q
print("4a ok", flush=True)

# 4b. copy amplification identity (2.11)
amp = []
for (n, T, m) in [(4, 2, 2), (5, 2, 2), (6, 3, 2), (6, 2, 3), (7, 2, 3), (7, 3, 2), (8, 2, 4)]:
    Mn, Cn = Mmat(n)
    Mm, Cm = Mmat(m)
    for _ in range(10):
        w = rng.integers(1, 6, size=len(Cm))
        wm = dict(zip(Cm, w))
        Wv = np.ones(len(Cn), dtype=int)
        for idx, c in enumerate(Cn):
            if c[0] == "s" and c[1] < T * m:
                Wv[idx] = wm[("s", c[1] % m, c[2])]
            if c[0] == "p" and c[2] < T * m and c[1] // m == c[2] // m:
                Wv[idx] = wm[("p", c[1] % m, c[2] % m, c[3], c[4])]
        K = kn(n) - T * kn(m)
        hn = (Mn @ Wv).min()
        hm = (Mm @ w).min()
        assert hn == T * hm + K
        assert 1 + hn == T * (1 + hm) + K + 1 - T
    amp.append((n, T, m))
REPORT["copy_amplification_checked"] = amp
print("4b ok", amp, flush=True)

# 4c. synthetic approximate LP at n=2, promise verified on the WHOLE cube {0..4}^8, then (2.4),(2.6),(2.7)
n = 2
M, C = Mmat(n)
d = len(C)
k = kn(n)
Wc = np.array(list(itertools.product(range(5), repeat=d)), dtype=np.int64)
hW = (Wc @ M.T).min(axis=1)
delta = 0.05
tested = 0
for trial in range(20):
    pts_pi = []
    pts_b = []
    for qi in range(4):
        for rep in range(3):
            e = rng.normal(size=d)
            e *= rng.uniform(0, 0.004) / np.abs(e).sum()
            pts_pi.append(M[qi] + e)
            pts_b.append(1 - rng.uniform(0.018, 0.022))
    pts_pi = np.array(pts_pi)
    pts_b = np.array(pts_b)
    vals = (Wc @ pts_pi.T + pts_b).min(axis=1)
    if not ((vals <= 1 + hW + 1e-12).all() and (vals >= 1 + hW - delta - 1e-12).all()):
        continue
    tested += 1
    ys = {}
    for qi in range(4):
        q = M[qi]
        cq = 3 - 2 * q
        v = pts_pi @ cq + pts_b
        yi = int(np.argmin(v))
        s_q = 1 + k - v[yi]
        assert -1e-12 <= s_q <= delta + 1e-12
        e_q = pts_pi[yi] - q
        assert np.abs(e_q).sum() <= delta - s_q + 1e-12, "(2.4)"
        assert abs(pts_b[yi] - 1 - (-s_q - cq @ e_q)) < 1e-12, "(2.5)"
        ys[qi] = (yi, s_q, e_q)
    zs = list(itertools.product((0, 1), repeat=n))
    for Abits in itertools.product((0, 1), repeat=n):
        A = [i for i in range(n) if Abits[i]]
        if not A:
            continue
        wA = np.zeros(d)
        for idx, c in enumerate(C):
            if c[0] == "s" and c[1] in A and c[2] == 0:
                wA[idx] = 1
            if c[0] == "p" and c[1] in A and c[2] in A and (c[3], c[4]) == (1, 1):
                wA[idx] = 2
        for qi, z in enumerate(zs):
            yi, s_q, e_q = ys[qi]
            S = pts_b[yi] + wA @ pts_pi[yi] - len(A) + delta
            h = sum(1 for i in A if z[i] == 1)
            assert S >= -1e-12
            if h == 0:
                assert 1 - 2 * delta - 1e-12 <= S <= 1 + 4 * delta + 1e-12
            if h == 1:
                assert S <= 4 * delta + 1e-12
REPORT["synthetic_approx_LP_n2_instances"] = tested
print("4c ok on", tested, "synthetic approximate LPs (promise checked on all 5^8 probes)", flush=True)

json.dump(REPORT, open("C_results.json", "w"), indent=1, default=str)
print("ALL PART-C CHECKS PASSED", time.time() - t0)
