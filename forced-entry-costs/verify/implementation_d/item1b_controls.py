"""Item 1, two further controls (exact integers).
 (i)  Mixed-sign adapter on larger DAGs with the Hungarian method: all parameters occur only OUTSIDE F
      (theta_j on f_j->f_j', beta_j - theta_j on g_j->g_j', zero diagonal); eta_e = rho + min_P Q(P),
      F optimal with all costs >= 0 in every corner.  Records how often the quadratic term matters.
 (ii) Partial sharing with nonnegative coefficients: eta_e = min over the corners of the SHARED parameters,
      with the unshared ones fixed as in theta*  (the per-parameter reading of "only shared parameters
      cause difficulty").
"""
import itertools, random, json
import numpy as np
from scipy.optimize import linear_sum_assignment
from adapter_sec2 import paths
from item1_prop_indep import all_perms, h

def build_mixed(nv, arcs, s, t, alpha, J, beta, rho=1):
    names = [('v', x) for x in range(nv)]; darcs = []
    for ai, (x, y) in enumerate(arcs):
        p = ('p', ai); names.append(p); darcs.append((('v', x), p, alpha[ai], None, 0)); cur = p
        for j, (a, b) in enumerate(J):
            if a == ai:
                names += [('f', j), ('f2', j)]
                darcs += [(cur, ('f', j), 0, None, 0), (('f', j), ('f2', j), 0, j, 1)]; cur = ('f2', j)
            if b == ai:
                names += [('g', j), ('g2', j)]
                darcs += [(cur, ('g', j), 0, None, 0), (('g', j), ('g2', j), beta[j], j, -1)]; cur = ('g2', j)
        darcs.append((cur, ('v', y), 0, None, 0))
    N = len(names); idx = {nm: i for i, nm in enumerate(names)}
    Gamma = rho + sum(alpha) + 2 * sum(beta) + 1
    const = np.full((N, N), Gamma, dtype=np.int64); np.fill_diagonal(const, 0)
    coef = [np.zeros((N, N), dtype=np.int64) for _ in J]
    for (u, v, c, k, sg) in darcs:
        const[idx[u], idx[v]] = c
        if k is not None:
            coef[k][idx[u], idx[v]] = sg
    e = (idx[('v', t)], idx[('v', s)]); const[e] = rho
    return const, coef, e, N

def forced(C, e):
    N = C.shape[0]
    rows = [i for i in range(N) if i != e[0]]; cols = [j for j in range(N) if j != e[1]]
    sub = C[np.ix_(rows, cols)]; r, c = linear_sum_assignment(sub)
    return int(C[e]) + int(sub[r, c].sum())

def test_mixed(trials, seed):
    rng = random.Random(seed); done = 0; nontrivial = 0; maxN = 0
    while done < trials:
        nv = rng.randint(3, 6)
        arcs = [(x, y) for x in range(nv) for y in range(x + 1, nv) if rng.random() < 0.7]
        P = paths(nv, arcs, 0, nv - 1)
        if len(arcs) < 3 or not P:
            continue
        K = rng.randint(1, 6)
        J = [tuple(rng.sample(range(len(arcs)), 2)) for _ in range(K)]
        alpha = [rng.randint(0, 3) for _ in arcs]; beta = [rng.randint(0, 5) for _ in J]
        const, coef, e, N = build_mixed(nv, arcs, 0, nv - 1, alpha, J, beta)
        assert all(np.diag(c).sum() == 0 and (np.diag(c) == 0).all() for c in coef)   # nothing on F
        lin = min(sum(alpha[a] for a in p) for p in P)
        quad = min(sum(alpha[a] for a in p) + sum(b for (x, y), b in zip(J, beta) if x in p and y in p) for p in P)
        eta = None
        for th in itertools.product(*[(0, b) for b in beta]):
            C = const.copy()
            for j, x in enumerate(th):
                C = C + x * coef[j]
            assert (C >= 0).all()
            r, c = linear_sum_assignment(C); assert int(C[r, c].sum()) == 0      # F (cost 0) optimal
            v = forced(C, e); eta = v if eta is None else min(eta, v)
        assert eta == 1 + quad, (eta, quad)
        nontrivial += (quad > lin); maxN = max(maxN, N); done += 1
    return dict(instances=trials, all_equal_rho_plus_QSPP=True, quadratic_term_matters=nontrivial, max_N=maxN)

def test_partial(trials, seed):
    rng = random.Random(seed); bad = 0; star_fails = 0
    for _ in range(trials):
        N = rng.choice([3, 4]); F = list(range(N)); rng.shuffle(F); F = tuple(F)
        Fset = sorted((i, F[i]) for i in range(N)); out = [(i, j) for i in range(N) for j in range(N) if F[i] != j]
        e = rng.choice(out); K = rng.randint(2, 5)
        const = [[rng.randint(-4, 6) for _ in range(N)] for _ in range(N)]
        coef = [[[0] * N for _ in range(N)] for _ in range(K)]; kind = []
        for k in range(K):
            kd = rng.choice(['F', 'out', 'shared']); kind.append(kd)
            if kd in ('F', 'shared'):
                for (i, j) in rng.sample(Fset, rng.randint(1, N)):
                    coef[k][i][j] = rng.randint(1, 3)
            if kd in ('out', 'shared'):
                for (i, j) in rng.sample(out, rng.randint(1, len(out))):
                    coef[k][i][j] = rng.randint(1, 3)
        lo = [rng.randint(-3, 3) for _ in range(K)]; hi = [l + rng.randint(0, 4) for l in lo]
        perms = all_perms(N)
        eta = min(h(const, coef, th, e, F, perms) for th in itertools.product(*[(lo[k], hi[k]) for k in range(K)]))
        cand = itertools.product(*[((lo[k], hi[k]) if kind[k] == 'shared' else ((hi[k],) if kind[k] == 'F' else (lo[k],)))
                                   for k in range(K)])
        red = min(h(const, coef, th, e, F, perms) for th in cand)
        bad += (red != eta)
    return dict(trials=trials, mismatches=bad)

if __name__ == '__main__':
    res = dict(mixed_sign_adapter=test_mixed(60, 21), partial_sharing=test_partial(600, 22))
    print(json.dumps(res, indent=1)); json.dump(res, open('item1b_controls_results.json', 'w'), indent=1)
