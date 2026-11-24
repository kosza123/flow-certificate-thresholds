"""Item 2: Corollary 8 (sparse interactions).
 (a) N_G = 7n+1+16|E| by building the instance of Section 2;
 (b) eta_G(w) = 1 + min_z w.m_G(z)  (all corner scenarios when 4|E| <= 12, else sampled corners; integer Hungarian);
 (c) m_G(z) are 0/1 vectors with coordinate sum n+|E|, and Q_G <-> COR(G) is an affine bijection
     (explicit affine map and its inverse, checked on all vertices; equal affine dimensions);
 (d) (C1)-(C4) spot checks: F optimal in each tested scenario, entries >= 0, parameter pattern.
"""
import itertools, random, json
import numpy as np
from scipy.optimize import linear_sum_assignment
from adapter_sec2 import build, C_of, diamond

def forced(C, e):
    N = C.shape[0]
    rows = [i for i in range(N) if i != e[0]]; cols = [j for j in range(N) if j != e[1]]
    sub = np.array(C[np.ix_(rows, cols)], dtype=np.int64)
    r, c = linear_sum_assignment(sub)
    return int(C[e]) + int(sub[r, c].sum())

def assign(C):
    M = np.array(C, dtype=np.int64); r, c = linear_sum_assignment(M); return int(M[r, c].sum())

def mG(n, edges, z):
    v = []
    for i in range(1, n + 1):
        v += [int(z[i - 1] == 0), int(z[i - 1] == 1)]
    for (i, j) in edges:
        for a in (0, 1):
            for b in (0, 1):
                v.append(int((z[i - 1], z[j - 1]) == (a, b)))
    return v

def corG(n, edges, z):
    return list(z) + [z[i - 1] * z[j - 1] for (i, j) in edges]

def lift(n, edges, x):       # affine map COR(G) -> Q_G, the change of coordinates of Section 3
    v = []
    for i in range(1, n + 1):
        v += [1 - x[i - 1], x[i - 1]]
    for k, (i, j) in enumerate(edges):
        X = x[n + k]; xi = x[i - 1]; xj = x[j - 1]
        v += [1 - xi - xj + X, xj - X, xi - X, X]      # order (a,b) = 00, 01, 10, 11
    return v

def proj(n, edges, m):       # coordinate projection Q_G -> COR(G)
    return [m[2 * i + 1] for i in range(n)] + [m[2 * n + 4 * k + 3] for k in range(len(edges))]

def affdim(pts):
    P = np.array(pts, dtype=float); return int(np.linalg.matrix_rank(P[1:] - P[0]))

GRAPHS = [
    (1, []), (2, []), (2, [(1, 2)]), (3, [(1, 2), (2, 3)]), (3, [(1, 3)]), (3, [(1, 2), (1, 3), (2, 3)]),
    (4, [(1, 2), (3, 4)]), (4, [(1, 2), (2, 3), (3, 4)]), (4, [(1, 2), (2, 3), (3, 4), (1, 4)]),
    (4, [(1, 2), (1, 3), (1, 4)]), (5, [(1, 2), (2, 3), (3, 4), (4, 5), (1, 5)]),
]

if __name__ == '__main__':
    rng = random.Random(7); out = []
    for (n, edges) in GRAPHS:
        for rep in range(3):
            lo = 0 if rep < 2 else 1                    # zeros allowed in two of three weight draws
            w1 = {(i, a): rng.randint(lo, 5) for i in range(1, n + 1) for a in (0, 1)}
            w2 = {(i, j, a, b): rng.randint(lo, 5) for (i, j) in edges for a in (0, 1) for b in (0, 1)}
            nv, arcs, s, t, alpha, J, beta, keys = diamond(n, edges, w1, w2)
            assert nv == 3 * n + 1 and len(arcs) == 4 * n and len(J) == 4 * len(edges)
            names, idx, const, coef, e, N = build(nv, arcs, s, t, alpha, J, beta, rho=1)
            assert N == nv + len(arcs) + 4 * len(J) == 7 * n + 1 + 16 * len(edges), (N, n, edges)
            # (C2),(C3): each theta_j in exactly two entries, coefficient 1, one on the diagonal; matching support
            rows_used = []; cols_used = []
            for j in range(len(J)):
                nz = list(zip(*np.nonzero(coef[j])))
                assert len(nz) == 2 and all(coef[j][p] == 1 for p in nz) and sum(p[0] == p[1] for p in nz) == 1
                rows_used += [p[0] for p in nz]; cols_used += [p[1] for p in nz]
            assert len(set(rows_used)) == len(rows_used) and len(set(cols_used)) == len(cols_used)
            wvec = [w1[(i, a)] for i in range(1, n + 1) for a in (0, 1)] + \
                   [w2[(i, j, a, b)] for (i, j) in edges for a in (0, 1) for b in (0, 1)]
            assert len(wvec) == 2 * n + 4 * len(edges)
            zs = list(itertools.product((0, 1), repeat=n))
            ms = [mG(n, edges, z) for z in zs]
            assert all(set(m) <= {0, 1} and sum(m) == n + len(edges) for m in ms)
            target = 1 + min(sum(a * b for a, b in zip(wvec, m)) for m in ms)
            # affine isomorphism
            cs = [corG(n, edges, z) for z in zs]
            assert all(lift(n, edges, c) == m and proj(n, edges, m) == c for c, m in zip(cs, ms))
            assert affdim(cs) == affdim(ms) == n + len(edges)
            # eta_G over corner scenarios
            K = len(J)
            if K <= 12:
                corners = list(itertools.product(*[(0, b) for b in beta]))
            else:
                corners = [tuple(rng.choice((0, b)) for b in beta) for _ in range(300)]
                # add, for every z, the scenario that realises min_theta for the path P_z
                for z in zs:
                    th = []
                    for (i, j, a, b), bt in zip(keys, beta):
                        u = z[i - 1] == a; v = z[j - 1] == b
                        th.append(0 if u else bt)       # minimiser of theta*u + (beta-theta)*v
                    corners.append(tuple(th))
            eta = None
            for th in corners:
                C = C_of(const, coef, th)
                assert (np.array(C, dtype=np.int64) >= 0).all()
                CF = int(sum(C[i, i] for i in range(N)))
                assert assign(C) == CF                   # F optimal in this scenario
                hval = forced(C, e) - CF
                # value formula of Theorem 2 in this scenario
                form = 1 + min(sum(w1[(i, z[i - 1])] for i in range(1, n + 1)) +
                               sum((th[k] if z[i - 1] == a else 0) + ((beta[k] - th[k]) if z[j - 1] == b else 0)
                                   for k, (i, j, a, b) in enumerate(keys)) for z in zs)
                assert hval == form, (hval, form)
                eta = hval if eta is None else min(eta, hval)
            assert eta == target, (eta, target)
            out.append(dict(n=n, E=edges, N=N, eta=eta, scenarios=len(corners)))
    # grid h x h : N_G and Theta(n)
    grid = {}
    for hh in (2, 3, 5, 10, 100):
        n = hh * hh; m = 2 * hh * (hh - 1); grid[hh] = dict(n=n, E=m, N_G=7 * n + 1 + 16 * m, ratio=(7 * n + 1 + 16 * m) / n)
    # K_n consistency with N = 8n^2 - n + 1
    assert all(7 * n + 1 + 16 * (n * (n - 1) // 2) == 8 * n * n - n + 1 for n in range(1, 50))
    print(json.dumps(dict(instances=len(out), all_ok=True, sample=out[:6], grid=grid), indent=1))
    json.dump(dict(instances=out, grid=grid), open(__file__.replace('.py', '_results.json'), 'w'), indent=1)
