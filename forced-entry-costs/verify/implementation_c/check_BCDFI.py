"""Items B, C, D, F, I: small exact computations (integers / Fractions only)."""
import itertools, random
from fractions import Fraction
from math import comb, ceil, log


# ---------- eta_n for the diamond family (formula (1) of the paper) ----------
def coords(n):
    c = [('s', i, a) for i in range(n) for a in (0, 1)]
    c += [('p', i, j, a, b) for i in range(n) for j in range(i + 1, n) for a in (0, 1) for b in (0, 1)]
    return c


def m_vec(n, z):
    return [1 if (c[0] == 's' and z[c[1]] == c[2]) or (c[0] == 'p' and (z[c[1]], z[c[2]]) == (c[3], c[4])) else 0
            for c in coords(n)]


def eta(n, w):
    cs = coords(n)
    assert len(cs) == 2 * n * n == len(w)
    return 1 + min(sum(wi * mi for wi, mi in zip(w, m_vec(n, z))) for z in itertools.product((0, 1), repeat=n))


kappa = lambda n: n + comb(n, 2)

# ---------- B and C: the three collinear weights ----------
print("B/C: one singleton block through (1,3),(2,2),(3,1), all other weights 1")
for n in range(1, 6):
    vals = []
    for blk in ((1, 3), (2, 2), (3, 1)):
        w = [1] * (2 * n * n); w[0], w[1] = blk
        vals.append(eta(n, w))
    v = 1 + kappa(n)
    assert vals == [v, v + 1, v], vals
    # midpoint convexity fails by exactly 1; no affine function within delta < 1/2 of these three values
    # (affine A: A(mid) = (A(w1)+A(w3))/2 ; need v+1-delta <= v+delta  <=>  delta >= 1/2)
    assert Fraction(1, 40) < Fraction(1, 2)
    print(f"  n={n}: values {vals}  (v = 1+kappa_n = {v})")
assert [eta(1, [1, 3]), eta(1, [2, 2]), eta(1, [3, 1])] == [2, 3, 2]
print("  n=1 values 2,3,2 as in Remark 19: OK")

# B: role of W in the last sentence of Remark 19 -- on a two-letter alphabet convexity is no obstruction.
# n=1, W={1,5}^2: min{t : t>=2, t>=w1+w2-4} (w only in the right-hand side) equals eta_1 on W.
for w in itertools.product((1, 5), repeat=2):
    assert max(2, w[0] + w[1] - 4) == eta(1, list(w))
print("B: min{t: t>=2, t>=w1+w2-4} = eta_1 on {1,5}^2  -> a min program with w in the rhs DOES represent eta_1 there")
# general: on {1,5}^d every function is the restriction of max_v [ f(v) - K * dist_v(w) ], dist_v affine in w on [1,5]^d
n = 2; d = 2 * n * n
verts = list(itertools.product((1, 5), repeat=d))
f = {v: eta(n, list(v)) for v in verts}
K = max(f.values()) - min(f.values())            # any K >= (max-min)/4 works, distance between vertices >= 4
ok = True
for w in verts:
    g = max(f[v] - K * sum((wc - 1) if vc == 1 else (5 - wc) for wc, vc in zip(w, v)) for v in verts)
    ok &= (g == f[w])
assert ok
print(f"B: n=2: eta_2 on {{1,5}}^8 equals a max of {len(verts)} affine functions of w (= value of a min program, w in rhs only): OK")

# B: duality statement on the smallest example: eta_1(w) = max{1+x : x<=w0, x<=w1} (m=2 rows)
#    dual: min{1 + w0*u0 + w1*u1 : u0+u1=1, u>=0}  -- the simplex, 2 inequalities = xc(COR(1))
for w in itertools.product(range(0, 6), repeat=2):
    primal = 1 + min(w)                                # max of 1+x under x<=w0, x<=w1
    dual = min(1 + w[0], 1 + w[1])                     # vertices of the simplex
    assert primal == dual == eta(1, list(w))
print("B: duality on the n=1 example: OK")

# ---------- D: arithmetic ----------
print("D: eps_n = 1/(40(1+5 kappa_n))")
for n in (1, 2, 3, 10, 100, 1000):
    k = kappa(n)
    eps = Fraction(1, 40 * (1 + 5 * k))
    assert k == n * (n + 1) // 2
    assert 1 / eps == 40 + 100 * n * (n + 1)
    Delta = eps * (1 + 5 * k)                           # eps * max eta_n
    assert Delta == Fraction(1, 40)
    nu = max(1, ceil(40 * Delta))
    assert nu == 1
    print(f"  n={n}: kappa={k}, max eta=1+5kappa={1+5*k}, 1/eps={1/eps} = 100n(n+1)+40, 40*Delta={40*Delta}, nu={nu}")
# max of eta_n on {1..5}^d is 1+5 kappa_n (all weights 5), min is 1+kappa_n: brute force n<=2
for n in (1, 2):
    d = 2 * n * n
    vals = [eta(n, list(w)) for w in itertools.product((1, 5), repeat=d)]   # extremes are at corners (eta monotone)
    assert max(vals) == 1 + 5 * kappa(n) and min(vals) == 1 + kappa(n)
print("  max eta_n = 1+5kappa_n, min = 1+kappa_n on the box (n<=2, corners): OK")

# ---------- F: Proposition 1 by brute force ----------
random.seed(7)
def perms(N):
    return list(itertools.permutations(range(N)))
cntF = 0; cnt_nec = [0, 0]
for trial in range(400):
    N = random.choice([2, 3])
    lo = [[random.randint(0, 6) for _ in range(N)] for _ in range(N)]
    hi = [[lo[i][j] + random.randint(0, 3) for j in range(N)] for i in range(N)]
    if random.random() < 0.6:                 # make the identity likely optimal everywhere
        for i in range(N):
            hi[i][i] = 0; lo[i][i] = 0
    F = tuple(range(N))
    cost = lambda C, s: sum(C[i][s[i]] for i in range(N))
    star = [[hi[i][j] if i == j else lo[i][j] for j in range(N)] for i in range(N)]
    cells = [(i, j) for i in range(N) for j in range(N)]
    corners = []
    for bits in itertools.product((0, 1), repeat=N * N):
        C = [[0] * N for _ in range(N)]
        for (i, j), b in zip(cells, bits):
            C[i][j] = hi[i][j] if b else lo[i][j]
        corners.append(C)
    P = perms(N)
    opt_all = all(cost(C, F) == min(cost(C, s) for s in P) for C in corners)   # linear in theta: corners suffice
    opt_star = cost(star, F) == min(cost(star, s) for s in P)
    assert opt_all == opt_star                                                  # sentence after Proposition 1
    cnt_nec[opt_all] += 1
    for e in [(i, j) for i in range(N) for j in range(N) if i != j]:
        h = lambda C: min(cost(C, s) - cost(C, F) for s in P if s[e[0]] == e[1])
        eta_e = min(h(C) for C in corners)                                      # h concave in theta: corners suffice
        assert eta_e == h(star)                                                 # Proposition 1 (no optimality needed)
        cntF += 1
print(f"F: eta_e = h_e(theta*) on {cntF} (instance, entry) pairs; 'optimal everywhere iff optimal at theta*' on 400 instances "
      f"(necessarily optimal: {cnt_nec[1]}, not: {cnt_nec[0]}): OK")

# ---------- I: Remark 21 and Remark 18 ----------
print("I: Remark 21")
for n in range(2, 11):
    w = [1] * (2 * n) + [5 if c[3] == c[4] else 1 for c in coords(n) if c[0] == 'p']
    assert len(w) == 2 * n * n
    # eta_n by the count of equal pairs (k ones): 1 + kappa + 4*min_k [C(k,2)+C(n-k,2)]
    val = 1 + kappa(n) + 4 * min(comb(k, 2) + comb(n - k, 2) for k in range(n + 1))
    if n <= 6:
        assert val == eta(n, w)
    gap = val - (1 + kappa(n))
    if n % 2 == 0:
        assert gap == n * n - 2 * n
    print(f"  n={n}: eta_n - (1+kappa_n) = {gap}" + (f" = n^2-2n" if n % 2 == 0 else f" (odd n: (n-1)^2 = {(n-1)**2})"))
# pair-local point: mu_i uniform, mu_ij = half on (0,1), half on (1,0): consistent, cost 1 per block -> value 1+kappa_n
t = ceil(8 * log(2) / 1.0 ** 2)
assert t == 6
first = None
for n in range(t + 1, 200):
    below = 2 ** (t + 1) * comb(n, t + 1) < 2 ** n
    if below and first is None:
        first = n
    if first is not None:
        assert below
print(f"  eps=1: t={t}, bound 2^(t+1)*C(n,t+1) < 2^n first at n={first} and for all larger n<200; "
      f"n=26: {128*comb(26,7)} vs {2**26}; n=27: {128*comb(27,7)} vs {2**27}")
assert first == 27

# Remark 18: weight values used in the proof of Theorem 7 (shifted alphabet {0..4}), n=3
n = 3; cs = coords(n); d = len(cs)
used = set()
used |= {0}; used |= {1}                                    # w=0, w=1
for z in itertools.product((0, 1), repeat=n):
    q = m_vec(n, z)
    wq = [2 - x for x in q]
    used |= set(wq) | set(2 * x for x in wq)                # w_q and 2 w_q
used |= {0, 1}                                              # unit vectors, block indicators
for r in range(1, n + 1):
    for S in itertools.combinations(range(n), r):
        wS = [1 if (c[0] == 's' and c[1] in S and c[2] == 0) else
              2 if (c[0] == 'p' and c[1] in S and c[2] in S and (c[3], c[4]) == (1, 1)) else 0 for c in cs]
        used |= set(wS)
        # check the slack identity w_S . q_T = |S|-1+(k-1)^2
        for z in itertools.product((0, 1), repeat=n):
            k = sum(z[i] for i in S)
            assert sum(a * b for a, b in zip(wS, m_vec(n, z))) == len(S) - 1 + (k - 1) ** 2
print(f"I: Remark 18: weight values used in the proof of Theorem 7 (shifted): {sorted(used)} -> alphabet {sorted(x+1 for x in used)}")
assert used == {0, 1, 2, 4}
print("ALL OK")
