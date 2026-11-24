"""Independent implementation (D): the construction of Section 2 of the paper, written from the text (not from other code).

D: vertices 0..nv-1, arcs list of (x,y), s, t, alpha[a] >= 0, J list of (a_j, b_j), beta[j] >= 0.
Returns names, index and (const, coef) with C(theta) = const + sum_j theta_j * coef[j]   (numpy int arrays).
"""
import numpy as np

def build(nv, arcs, s, t, alpha, J, beta, rho=1, Gamma=None):
    names = [('v', x) for x in range(nv)]
    darcs = []                                  # (u, v, constant cost, parameter index or None)
    for ai, (x, y) in enumerate(arcs):
        p = ('p', ai); names.append(p)
        darcs.append((('v', x), p, alpha[ai], None)); cur = p
        for j, (a, b) in enumerate(J):          # "in a fixed order, for every interaction j in which a occurs"
            assert a != b
            if a == ai:
                names += [('f', j), ('f2', j)]
                darcs.append((cur, ('f', j), 0, None)); darcs.append((('f', j), ('f2', j), 0, j)); cur = ('f2', j)
            if b == ai:
                names += [('g', j), ('g2', j)]
                darcs.append((cur, ('g', j), 0, None)); darcs.append((('g', j), ('g2', j), beta[j], None)); cur = ('g2', j)
        darcs.append((cur, ('v', y), 0, None))
    N = len(names)
    idx = {nm: i for i, nm in enumerate(names)}
    A0 = sum(alpha); B0 = sum(beta)
    if Gamma is None:
        Gamma = rho + A0 + 2 * B0 + 1
    const = np.full((N, N), Gamma, dtype=object)
    coef = [np.zeros((N, N), dtype=object) for _ in J]
    for i in range(N):
        const[i, i] = 0
    for (u, v, c, k) in darcs:
        const[idx[u], idx[v]] = c
        if k is not None:
            coef[k][idx[u], idx[v]] = 1
    for j in range(len(J)):                     # C_{g_j g_j}(theta) = theta_j
        coef[j][idx[('g', j)], idx[('g', j)]] = 1
    e = (idx[('v', t)], idx[('v', s)])
    const[e] = rho
    return names, idx, const, coef, e, N

def C_of(const, coef, theta):
    C = const.copy()
    for j, th in enumerate(theta):
        C = C + th * coef[j]
    return C

def paths(nv, arcs, s, t):
    out = []
    def rec(x, used, seen):
        if x == t:
            out.append(tuple(used)); return
        for ai, (u, v) in enumerate(arcs):
            if u == x and v not in seen:
                rec(v, used + [ai], seen | {v})
    rec(s, [], {s})
    return out

def diamond(n, edges, w1, w2):
    """Reduced diamond chain: layers 1..n, interactions (d_{i,a}, d_{j,b}) for ij in edges (i<j).
    w1[(i,a)], w2[(i,j,a,b)]. Vertices v_0..v_n -> 0..n ; b_{i,a} -> n + 2(i-1) + a + 1."""
    nv = 3 * n + 1
    arcs = []; alpha = []; dpos = {}
    for i in range(1, n + 1):
        for a in (0, 1):
            bia = n + 2 * (i - 1) + a + 1
            dpos[(i, a)] = len(arcs); arcs.append((i - 1, bia)); alpha.append(w1[(i, a)])
            arcs.append((bia, i)); alpha.append(0)
    J = []; beta = []; keys = []
    for (i, j) in edges:
        assert i < j
        for a in (0, 1):
            for b in (0, 1):
                J.append((dpos[(i, a)], dpos[(j, b)])); beta.append(w2[(i, j, a, b)]); keys.append((i, j, a, b))
    return nv, arcs, 0, n, alpha, J, beta, keys
