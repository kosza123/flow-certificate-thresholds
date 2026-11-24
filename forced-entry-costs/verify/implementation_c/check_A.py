"""Independent check (C): brute-force test of the reduction in the proof of Corollary 4 (no approximation in general).

Written from Section 2.1 of the paper and the proof of the corollary only.
Exact integer arithmetic throughout (own Hungarian algorithm on Python ints).
For every instance and every corner scenario theta in {0,M}^J (h_e is concave in theta, so the
minimum over the box is at a corner; a few midpoints are tested as well):
  * (C2),(C3),(C4) structurally, N = |V|+|A|+4|J|,
  * identity optimal, dual certificate feasible, identity the unique optimal permutation,
  * h_e(theta) = 1 + min_P [...] (formula of Theorem 2), by an assignment problem with X_e = 1,
  * eta_e = 1 + M * (min number of violated pairs)  ->  eta_e = 1 iff a safe path exists, else >= 1+M,
  * the threshold test "output <= M" decides the path problem for both extreme outputs
    eta_e and 2^{p(N)} eta_e of an approximation algorithm.
"""
import itertools, random, sys
from fractions import Fraction


def hungarian(c):
    """exact min-cost perfect matching, c square list of lists of ints/Fractions. returns (value, assignment)"""
    n = len(c)
    INF = None
    u = [0] * (n + 1); v = [0] * (n + 1); p = [0] * (n + 1); way = [0] * (n + 1)
    for i in range(1, n + 1):
        p[0] = i; j0 = 0
        minv = [INF] * (n + 1); used = [False] * (n + 1)
        while True:
            used[j0] = True; i0 = p[j0]; delta = INF; j1 = -1
            for j in range(1, n + 1):
                if not used[j]:
                    cur = c[i0 - 1][j - 1] - u[i0] - v[j]
                    if minv[j] is INF or cur < minv[j]:
                        minv[j] = cur; way[j] = j0
                    if delta is INF or minv[j] < delta:
                        delta = minv[j]; j1 = j
            for j in range(n + 1):
                if used[j]:
                    u[p[j]] += delta; v[j] -= delta
                else:
                    minv[j] -= delta
            j0 = j1
            if p[j0] == 0:
                break
        while True:
            j1 = way[j0]; p[j0] = p[j1]; j0 = j1
            if j0 == 0:
                break
    ass = [0] * n
    for j in range(1, n + 1):
        ass[p[j] - 1] = j - 1
    return sum(c[i][ass[i]] for i in range(n)), ass


def split_graph(k, arcsG, pairs):
    """vertex splitting of the proof: v -> v-, v+, arc (v-,v+); (u,v) -> (u+,v-)."""
    V = []
    for v in range(k):
        V += [('-', v), ('+', v)]
    A = [(('-', v), ('+', v)) for v in range(k)]          # arc index v is \bar a_v
    A += [(('+', u), ('-', v)) for (u, v) in arcsG]
    J = [(u, v) for (u, v) in pairs]                         # interaction (\bar a_u, \bar a_v): arc indices u, v
    return V, A, J


def adapter(V, A, J, alpha, beta, rho, Gamma, s, t):
    """Section 2.1. Returns (names, const matrix, list of (row,col,j) carrying +theta_j, e=(row,col))."""
    names = list(V)
    desig = {}            # (x,y) -> ('const', c) or ('theta', j)
    for ai, (x, y) in enumerate(A):
        pa = ('p', ai); names.append(pa)
        desig[(x, pa)] = ('const', alpha[ai])
        cur = pa
        for j, (aj, bj) in enumerate(J):                     # fixed order: by j
            assert aj != bj, "a_j and b_j must be distinct arcs"
            if aj == ai:
                f, f2 = ('f', j), ("f'", j); names += [f, f2]
                desig[(cur, f)] = ('const', 0); desig[(f, f2)] = ('theta', j); cur = f2
            if bj == ai:
                g, g2 = ('g', j), ("g'", j); names += [g, g2]
                desig[(cur, g)] = ('const', 0); desig[(g, g2)] = ('const', beta[j]); cur = g2
        desig[(cur, y)] = ('const', 0)
    idx = {nm: i for i, nm in enumerate(names)}
    N = len(names)
    assert N == len(V) + len(A) + 4 * len(J)
    assert (t, s) not in desig
    C0 = [[Gamma] * N for _ in range(N)]
    th = []
    for i in range(N):
        C0[i][i] = 0
    for (x, y), (kind, val) in desig.items():
        if kind == 'const':
            C0[idx[x]][idx[y]] = val
        else:
            C0[idx[x]][idx[y]] = 0; th.append((idx[x], idx[y], val))
    for j in range(len(J)):
        th.append((idx[('g', j)], idx[('g', j)], j))        # diagonal entry theta_j at g_j
    C0[idx[t]][idx[s]] = rho
    return names, idx, C0, th, (idx[t], idx[s])


def paths(k, arcsG, s, t):
    out = []
    def rec(v, vis):
        if v == t:
            out.append(tuple(vis)); return
        for (x, y) in arcsG:
            if x == v:
                rec(y, vis + [y])
    rec(s, [s])
    return out


def check_instance(k, arcsG, pairs, pfun, extra_mid=True, verbose=False):
    s, t = 0, k - 1
    PS = paths(k, arcsG, s, t)
    assert PS, "need an s-t path"
    V, A, J = split_graph(k, arcsG, pairs)
    N = len(V) + len(A) + 4 * len(J)
    M = 2 ** pfun(N)
    Gamma = 2 + 2 * M * len(J)
    alpha = [0] * len(A); beta = [M] * len(J); rho = 1
    assert Gamma >= rho + sum(alpha) + 2 * sum(beta) + 1                      # condition (2)
    names, idx, C0, th, e = adapter(V, A, J, alpha, beta, rho, Gamma, ('-', s), ('+', t))
    assert len(names) == N
    # (C2): each theta_j in exactly two entries, coefficient +1, one on the diagonal
    for j in range(len(J)):
        ent = [(r, c) for (r, c, jj) in th if jj == j]
        assert len(ent) == 2 and sum(1 for (r, c) in ent if r == c) == 1
    # (C3): no two uncertain entries share a row or a column
    rows = [r for (r, c, j) in th]; cols = [c for (r, c, j) in th]
    assert len(set(rows)) == len(rows) and len(set(cols)) == len(cols)
    viol = lambda P: sum(1 for (u, v) in pairs if u in P and v in P)
    minviol = min(viol(P) for P in PS)
    BIG = (N + 2) * (Gamma + M) + 7
    scen = list(itertools.product([0, M], repeat=len(J)))
    if extra_mid and J:
        scen.append(tuple(Fraction(M, 2) for _ in J)); scen.append(tuple(Fraction(M * (j + 1), len(J) + 2) for j in range(len(J))))
    eta = None
    for theta in scen:
        C = [row[:] for row in C0]
        for (r, c, j) in th:
            C[r][c] += theta[j]
        assert all(x >= 0 for row in C for x in row)                           # (C4)
        costF = sum(C[i][i] for i in range(N))
        val, ass = hungarian(C)
        assert val == costF, "identity not optimal"
        # dual certificate of Lemma 14
        lam = [0] * N
        for j in range(len(J)):
            lam[idx[('g', j)]] = theta[j]
        assert all(lam[u] <= C[u][v] for u in range(N) for v in range(N)) and sum(lam) == costF
        # uniqueness among permutations: forbid (i,i) for each i
        for i in range(N):
            C2 = [row[:] for row in C]; C2[i][i] = BIG
            v2, _ = hungarian(C2)
            assert v2 > costF, "identity not unique"
        # forced value: delete row of t+, column of s-
        r_e, c_e = e
        Cm = [[C[i][j] for j in range(N) if j != c_e] for i in range(N) if i != r_e]
        v3, _ = hungarian(Cm)
        h = v3 + C[r_e][c_e] - costF
        formula = rho + min(sum(theta[j] * (1 if u in P else 0) + (M - theta[j]) * (1 if v in P else 0)
                                for j, (u, v) in enumerate(pairs)) for P in PS)
        assert h == formula, (h, formula)
        if all(x in (0, M) for x in theta):
            eta = h if eta is None else min(eta, h)
        else:
            assert h >= eta                                                    # interior not below corner min
    assert eta == 1 + M * minviol
    safe = (minviol == 0)
    assert (eta == 1) == safe and (safe or eta >= 1 + M)
    # decision procedure: any output in [eta, 2^{p(N)} eta]; test both ends
    for out in (eta, 2 ** pfun(N) * eta):
        assert (out <= M) == safe
    if verbose:
        print(f"  k={k} arcs={arcsG} pairs={pairs} N={N} M=2^{pfun(N)} safe={safe} eta_e-1={(eta-1)//M}*M")
    return N, safe


def main():
    random.seed(20261124)
    pfun = lambda N: N                     # p(N) = N; M = 2^N
    # hand-made edge cases: pair with s, pair with t, pair {s,t}, vertex in several pairs, duplicated pair,
    # both orders of the same pair, no pairs
    full4 = [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (0, 3)]
    cases = [
        (3, [(0, 1), (1, 2), (0, 2)], [(0, 1)]),            # pair contains s; safe path 0-2
        (3, [(0, 1), (1, 2)], [(0, 1)]),                    # pair contains s; no safe path
        (3, [(0, 1), (1, 2), (0, 2)], [(1, 2)]),            # pair contains t
        (3, [(0, 1), (1, 2), (0, 2)], [(0, 2)]),            # pair {s,t}: never safe
        (4, full4, [(1, 2), (1, 3), (1, 0)]),               # vertex 1 in three pairs
        (4, full4, [(1, 2), (1, 2)]),                       # duplicated pair
        (4, full4, [(1, 2), (2, 1)]),                       # both orders
        (4, [(0, 1), (1, 2), (2, 3)], [(1, 2), (0, 3)]),    # two violated pairs on the only path
        (3, [(0, 1), (1, 2)], []),                          # no pairs
        (2, [(0, 1), (0, 1)], [(0, 1)]),                    # parallel arcs, pair {s,t}
    ]
    res = []
    for (k, arcs, pairs) in cases:
        res.append(check_instance(k, arcs, pairs, pfun, verbose=True))
    nrand = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    cnt = 0
    while cnt < nrand:
        k = random.choice([3, 4, 4, 5])
        arcs = [(i, j) for i in range(k) for j in range(i + 1, k) if random.random() < 0.6]
        if not paths(k, arcs, 0, k - 1):
            continue
        allp = [(i, j) for i in range(k) for j in range(k) if i != j]
        pairs = [random.choice(allp) for _ in range(random.choice([1, 2, 2, 3]))]
        res.append(check_instance(k, arcs, pairs, pfun, verbose=(cnt < 5)))
        cnt += 1
    ns = [r[0] for r in res]
    print(f"A: {len(res)} instances OK (N from {min(ns)} to {max(ns)}; safe: {sum(r[1] for r in res)}, unsafe: {sum(not r[1] for r in res)})")


if __name__ == '__main__':
    main()
