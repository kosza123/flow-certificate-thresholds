"""Checks for the exact representations and bounded weights (Section 4 of the paper) on tiny cases."""
import itertools, json, time
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog

REPORT = {}
t0 = time.time()


def coords(n):
    c = [("s", i, a) for i in range(n) for a in (0, 1)]
    c += [("p", i, j, a, b) for i in range(n) for j in range(i + 1, n) for a in (0, 1) for b in (0, 1)]
    return c


def mvec(n, z, C):
    return np.array([int(z[c[1]] == c[2]) if c[0] == "s" else int((z[c[1]], z[c[2]]) == (c[3], c[4])) for c in C])


def blocks(n, C):
    bl = {}
    for idx, c in enumerate(C):
        key = ("s", c[1]) if c[0] == "s" else ("p", c[1], c[2])
        bl.setdefault(key, []).append(idx)
    return list(bl.values())


# ------------------------------------------------------------------ algebraic identities, n <= 6
for n in range(1, 7):
    C = coords(n)
    d = len(C)
    k = n + n * (n - 1) // 2
    assert d == 2 * n * n
    M = np.array([mvec(n, z, C) for z in itertools.product((0, 1), repeat=n)])  # 2^n x d
    assert (M.sum(axis=1) == k).all()
    # w_q = 2*1 - q exposes q uniquely among vertices with value k
    for qi in range(len(M)):
        wq = 2 - M[qi]
        vals = M @ wq
        assert vals[qi] == k and (np.delete(vals, qi) > k).all()
    # every coordinate vanishes at some vertex (needed for pi_i >= 0 and its tightness) -- needs n>=1
    assert (M.min(axis=0) == 0).all()
    # probes w_A : slack matrix (|A cap B| - 1)^2, min = |A|-1
    zs = list(itertools.product((0, 1), repeat=n))
    for Abits in itertools.product((0, 1), repeat=n):
        A = [i for i in range(n) if Abits[i]]
        if not A:
            continue
        wA = np.zeros(d, dtype=int)
        for idx, c in enumerate(C):
            if c[0] == "s" and c[1] in A and c[2] == 0:
                wA[idx] = 1
            if c[0] == "p" and c[1] in A and c[2] in A and (c[3], c[4]) == (1, 1):
                wA[idx] = 2
        vals = M @ wA
        for zi, z in enumerate(zs):
            h = sum(1 for i in A if z[i] == 1)
            assert vals[zi] == len(A) - 1 + (h - 1) ** 2
        assert vals.min() == len(A) - 1
print("algebraic identities ok (n<=6)", time.time() - t0, flush=True)

# ------------------------------------------------------------------ Kaibel-Weltge rectangle lemma by brute force, n <= 4
kw = {}
for n in range(1, 5):
    subs = list(range(2 ** n))
    pop = [bin(x).count("1") for x in range(2 ** n)]
    ok_cols = []  # for each row a: bitmask over columns b with |a&b| != 1
    disj = []
    for a in subs:
        m1 = 0
        m2 = 0
        for b in subs:
            if pop[a & b] != 1:
                m1 |= 1 << b
            if a & b == 0:
                m2 |= 1 << b
        ok_cols.append(m1)
        disj.append(m2)
    assert sum(bin(x).count("1") for x in disj) == 3 ** n
    best = 0
    # maximal rectangles: choose row family, columns = intersection of allowed column sets
    if n <= 3:
        fams = range(1, 2 ** (2 ** n))
    else:
        fams = range(1, 2 ** (2 ** n))  # 65535 families for n=4
    for fam in fams:
        cols = (1 << (2 ** n)) - 1
        rows = [a for a in subs if fam >> a & 1]
        for a in rows:
            cols &= ok_cols[a]
        cnt = sum(bin(disj[a] & cols).count("1") for a in rows)
        best = max(best, cnt)
    kw[n] = dict(max_disjoint_pairs_in_valid_rectangle=best, bound=2 ** n, disjoint_pairs=3 ** n)
    assert best <= 2 ** n
REPORT["kaibel_weltge_rectangle_lemma_bruteforce"] = kw
print("KW rectangle lemma brute force:", kw, time.time() - t0, flush=True)

# ------------------------------------------------------------------ n = 2: the "universal" feasible set for the cube {0..4}^8
# Any exact representation (P,a,pi) on W={0..4}^d has image (a,pi)(P) inside
#   U = {(a,pi): a + w.pi >= 1 + h(w) for all w in W}.
# We test the conclusions of section 5 on U itself (the weakest possible hypothesis).
n = 2
C = coords(n)
d = len(C)
k = 3
Mv = np.array([mvec(n, z, C) for z in itertools.product((0, 1), repeat=n)])
W = np.array(list(itertools.product(range(5), repeat=d)), dtype=np.int64)  # 390625 x 8
hW = (W @ Mv.T).min(axis=1)
A_ub = -np.hstack([np.ones((len(W), 1)), W.astype(float)])  # -(a + w.pi) <= -(1+h)
b_ub = -(1.0 + hW)
bounds = [(None, None)] * (d + 1)


def solve(c, A_eq=None, b_eq=None):
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
    return res


out = {}
res = solve(np.eye(d + 1)[0])
out["min a over U"] = res.fun
assert abs(res.fun - 1) < 1e-8
worst = 0.0
for qi in range(4):
    q = Mv[qi]
    wq = 2 - q
    Aeq = np.array([[1.0] + list(wq.astype(float))])
    beq = np.array([1.0 + k])
    r = solve(-np.eye(d + 1)[0], Aeq, beq)  # max a on the w_q-optimal face
    assert r.status == 0
    worst = max(worst, abs(-r.fun - 1))
    for i in range(d):
        for sgn in (1, -1):
            r = solve(sgn * np.eye(d + 1)[i + 1], Aeq, beq)
            assert r.status == 0
            worst = max(worst, abs(sgn * r.fun - q[i]))
out["max deviation of (a,pi) from (1,q) on the w_q-optimal faces"] = worst
assert worst < 1e-7
# face P0 = {2a + 1.pi = 2+k}: a=1, pi>=0, block sums = 1
Aeq = np.array([[2.0] + [1.0] * d])
beq = np.array([2.0 + k])
dev = 0.0
r1 = solve(np.eye(d + 1)[0], Aeq, beq)
r2 = solve(-np.eye(d + 1)[0], Aeq, beq)
dev = max(dev, abs(r1.fun - 1), abs(-r2.fun - 1))
minpi = min(solve(np.eye(d + 1)[i + 1], Aeq, beq).fun for i in range(d))
for bl in blocks(n, C):
    c = np.zeros(d + 1)
    c[[b + 1 for b in bl]] = 1
    lo = solve(c, Aeq, beq).fun
    hi = -solve(-c, Aeq, beq).fun
    dev = max(dev, abs(lo - 1), abs(hi - 1))
out["P0: max deviation of a and block sums from 1"] = dev
out["P0: min coordinate of pi"] = minpi
assert dev < 1e-7 and minpi > -1e-8
# is pi(P0) equal to Q_2 here?  check the marginal-consistency equations  pi_{1,a} = sum_b pi_{12,ab}
cons = 0.0
idx = {c: i for i, c in enumerate(C)}
for a in (0, 1):
    c = np.zeros(d + 1)
    c[idx[("s", 0, a)] + 1] = 1
    for b in (0, 1):
        c[idx[("p", 0, 1, a, b)] + 1] -= 1
    cons = max(cons, abs(solve(c, Aeq, beq).fun), abs(solve(-c, Aeq, beq).fun))
out["P0 (n=2): max violation of marginal consistency"] = cons
REPORT["n2_universal_set_cube_0_4"] = out
print("n=2 universal set:", out, time.time() - t0, flush=True)

# ------------------------------------------------------------------ what if the alphabet is only {0,1,2}?  (is 2*w_q really needed?)
W2mask = (W.max(axis=1) <= 2)
A2, b2 = A_ub[W2mask], b_ub[W2mask]
q = Mv[0]
wq = 2 - q
Aeq = np.array([[1.0] + list(wq.astype(float))])
beq = np.array([1.0 + k])
r = linprog(-np.eye(d + 1)[0], A_ub=A2, b_ub=b2, A_eq=Aeq, b_eq=beq, bounds=bounds, method="highs")
REPORT["alphabet_0_2_only: max a on w_q-optimal face"] = (-r.fun if r.status == 0 else f"status {r.status}: {r.message}")
print("alphabet {0,1,2}: max a on the w_q-face:", REPORT["alphabet_0_2_only: max a on w_q-optimal face"], flush=True)

json.dump(REPORT, open("B_results.json", "w"), indent=1, default=str)
print("ALL PART-B CHECKS PASSED", time.time() - t0)
