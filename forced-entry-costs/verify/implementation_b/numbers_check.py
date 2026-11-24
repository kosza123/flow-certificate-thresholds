"""Independent checks (B) of the identities and constants stated in Sections 3-6 of the paper."""
import itertools, math, random
from math import comb
import numpy as np
from scipy.optimize import linprog

random.seed(11)


def coords(n):
    c = [("s", i, a) for i in range(1, n + 1) for a in (0, 1)]
    c += [("p", i, j, a, b) for i in range(1, n + 1) for j in range(i + 1, n + 1) for a in (0, 1) for b in (0, 1)]
    return c


def m(n, z, C):
    return np.array([1 if (c[0] == "s" and z[c[1] - 1] == c[2]) or
                     (c[0] == "p" and z[c[1] - 1] == c[3] and z[c[2] - 1] == c[4]) else 0 for c in C])


for n in range(1, 5):
    C = coords(n)
    d = len(C)
    kappa = n + comb(n, 2)
    assert d == 2 * n * n and kappa == comb(n + 1, 2)
    assert (3 * n + 1) + 4 * n + 4 * (2 * n * (n - 1)) == 8 * n * n - n + 1
    Z = list(itertools.product((0, 1), repeat=n))
    Mv = np.array([m(n, z, C) for z in Z])
    assert (Mv.sum(axis=1) == kappa).all()
    h = lambda w: int((Mv @ np.array(w)).min())
    # blocks
    blocks = [[k for k, c in enumerate(C) if c[0] == "s" and c[1] == i] for i in range(1, n + 1)]
    blocks += [[k for k, c in enumerate(C) if c[0] == "p" and (c[1], c[2]) == (i, j)]
               for i in range(1, n + 1) for j in range(i + 1, n + 1)]
    assert len(blocks) == kappa
    for B in blocks:
        ind = np.zeros(d, dtype=int)
        ind[B] = 1
        assert h(ind) == 1
    for k in range(d):
        u = np.zeros(d, dtype=int)
        u[k] = 1
        assert h(u) == 0
    for q in Mv:
        wq = 2 - q
        assert h(wq) == kappa and h(2 * wq) == 2 * kappa
        assert sum(1 for p in Mv if p @ wq == kappa) == 1  # unique minimiser among vertices
        cq = 3 - 2 * q
        assert h(cq) == kappa
    # w_S . q_T = |S|-1+(k-1)^2, h(w_S) = |S|-1 ; sup-norm of w_S - c_q at most 3
    subsets = [frozenset(s) for r in range(n + 1) for s in itertools.combinations(range(1, n + 1), r)]
    for S in subsets:
        if not S:
            continue
        wS = np.array([1 if (c[0] == "s" and c[2] == 0 and c[1] in S) else
                       2 if (c[0] == "p" and c[3] == 1 and c[4] == 1 and c[1] in S and c[2] in S) else 0 for c in C])
        for T in subsets:
            z = tuple(1 if i in T else 0 for i in range(1, n + 1))
            k = len(S & T)
            assert wS @ m(n, z, C) == len(S) - 1 + (k - 1) ** 2
            assert np.abs(wS - (3 - 2 * m(n, z, C))).max() <= 3
        assert h(wS) == len(S) - 1
    # h(c_q + sigma) = kappa + sigma.q for all sign vectors (n <= 3), random sample otherwise
    if n <= 3:
        sig = np.array(list(itertools.product((-1, 1), repeat=d)), dtype=np.int16)
    else:
        sig = np.array([[random.choice((-1, 1)) for _ in range(d)] for _ in range(4000)], dtype=np.int16)
    for q in Mv:
        cq = 3 - 2 * q
        W = cq[None, :] + sig
        assert W.min() >= 0 and W.max() <= 4
        vals = (W @ Mv.T).min(axis=1)
        assert (vals == kappa + sig @ q).all()
    print(f"n={n}: d={d}, kappa={kappa}, identities of Sections 3-5 ok ({len(sig)} sign vectors per vertex)")

# ---- copy amplification (proof of Theorem 7) ----
for (n, T, mm) in [(4, 2, 2), (5, 2, 2), (6, 2, 3), (6, 3, 2), (7, 2, 3)]:
    Cn, Cm = coords(n), coords(mm)
    kn, km = comb(n + 1, 2), comb(mm + 1, 2)
    K = kn - T * km
    Zn = list(itertools.product((0, 1), repeat=n))
    Zm = list(itertools.product((0, 1), repeat=mm))
    Mn = np.array([m(n, z, Cn) for z in Zn])
    Mm = np.array([m(mm, z, Cm) for z in Zm])
    for _ in range(20):
        w = {c: random.randint(1, 5) for c in Cm}
        Wv = []
        for c in Cn:
            if c[0] == "s":
                g, r = divmod(c[1] - 1, mm)
                Wv.append(w[("s", r + 1, c[2])] if g < T else 1)
            else:
                g1, r1 = divmod(c[1] - 1, mm)
                g2, r2 = divmod(c[2] - 1, mm)
                Wv.append(w[("p", r1 + 1, r2 + 1, c[3], c[4])] if (g1 == g2 and g1 < T) else 1)
        eta_n = 1 + (Mn @ np.array(Wv)).min()
        eta_m = 1 + (Mm @ np.array([w[c] for c in Cm])).min()
        assert eta_n == T * eta_m + K + 1 - T
print("copy identity eta_n(W(w)) = T eta_m(w) + K + 1 - T: ok")

# ---- constants of Proposition 18 / Theorem 7 ----
g = 1 / 20
assert abs(0.5 * (1 - 2 * g) - 4 * g - 0.25) < 1e-15 and abs(1 + 4 * g - 6 / 5) < 1e-15
print("1/(64 ln 2) =", 1 / (64 * math.log(2)), " 1/(256 ln 2) =", 1 / (256 * math.log(2)))

# ---- Theorem 8: epsilon=1 -> t ; crossover with 2^n ----
t1 = math.ceil(8 * math.log(2) / 1.0)
first = next(n for n in range(t1 + 1, 200) if 2 ** (t1 + 1) * comb(n, t1 + 1) < 2 ** n)
print("epsilon=1: t =", t1, "; size bound below 2^n first at n =", first,
      "; always below afterwards:", all(2 ** (t1 + 1) * comb(n, t1 + 1) < 2 ** n for n in range(first, 400)))
for eps in (0.5, 0.25):
    t = math.ceil(8 * math.log(2) / eps ** 2)
    f = next(n for n in range(t + 1, 5000) if 2 ** (t + 1) * comb(n, t + 1) < 2 ** n)
    print(f"epsilon={eps}: t={t}, bound below 2^n first at n={f}")


# ---- Remark 19: pair-local gap ----
def sa_lp(n, r, wvec, C):
    """Sherali-Adams style local LP of Section 6: variables mu_S(x_S), |S|<=r; nonnegativity only for |S|=r."""
    sets = [frozenset(s) for k in range(r + 1) for s in itertools.combinations(range(1, n + 1), k)]
    var = {}
    for S in sets:
        for x in itertools.product((0, 1), repeat=len(S)):
            var[(S, x)] = len(var)
    nv = len(var)
    Aeq, beq = [], []
    row = np.zeros(nv)
    row[var[(frozenset(), ())]] = 1
    Aeq.append(row)
    beq.append(1)
    for S in sets:
        Sl = sorted(S)
        for i in Sl:
            Rl = [j for j in Sl if j != i]
            R = frozenset(Rl)
            for xr in itertools.product((0, 1), repeat=len(Rl)):
                row = np.zeros(nv)
                row[var[(R, xr)]] = -1
                for a in (0, 1):
                    full = dict(zip(Rl, xr))
                    full[i] = a
                    row[var[(S, tuple(full[j] for j in Sl))]] += 1
                Aeq.append(row)
                beq.append(0)
    cost = np.zeros(nv)
    for k, c in enumerate(C):
        if c[0] == "s":
            cost[var[(frozenset([c[1]]), (c[2],))]] += wvec[k]
        else:
            cost[var[(frozenset([c[1], c[2]]), (c[3], c[4]))]] += wvec[k]
    bounds = [(0, None) if len(S) == r else (None, None) for (S, x) in var]
    res = linprog(cost, A_eq=np.array(Aeq), b_eq=np.array(beq), bounds=bounds, method="highs")
    assert res.status == 0, res.message
    ninq = sum(1 for (S, x) in var if len(S) == r)
    assert ninq == 2 ** r * comb(n, r)
    return 1 + res.fun


for n in (2, 4, 6, 8):
    C = coords(n)
    w = np.array([1 if c[0] == "s" else (5 if c[3] == c[4] else 1) for c in C])
    Mv = np.array([m(n, z, C) for z in itertools.product((0, 1), repeat=n)])
    eta = 1 + (Mv @ w).min()
    kappa = comb(n + 1, 2)
    assert eta == 1 + kappa + n * n - 2 * n
    if n <= 6:
        L1 = sa_lp(n, 2, w, C)
        assert abs(L1 - (1 + kappa)) < 1e-7, (L1, 1 + kappa)
print("Remark 19: pair-local value 1+kappa and eta = 1+kappa+n^2-2n (even n): ok")

# ---- Theorem 8 first display, small n, random real weights in [1,5] ----
worst = 0
for n, t in [(3, 1), (3, 2), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2)]:
    C = coords(n)
    Mv = np.array([m(n, z, C) for z in itertools.product((0, 1), repeat=n)])
    kappa = comb(n + 1, 2)
    for trial in range(6):
        if trial == 0:
            w = np.array([1 if c[0] == "s" else (5 if c[3] == c[4] else 1) for c in C], dtype=float)
        else:
            w = np.array([random.choice([1, 5, random.uniform(1, 5)]) for _ in C], dtype=float)
        eta = 1 + (Mv @ w).min()
        L = sa_lp(n, t + 1, w, C)
        bound = n * n * math.sqrt(2 * math.log(2) / t)
        assert 1 + kappa - 1e-7 <= L <= eta + 1e-7 and eta <= L + bound + 1e-7
        worst = max(worst, (eta - L) / bound)
print("Theorem 8 sandwich on small cases: ok; largest (eta-L_t)/bound =", round(worst, 4))
print("ALL NUMBER CHECKS PASSED")
