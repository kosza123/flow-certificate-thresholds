"""Item 1: Proposition 1 (no parameter shared across F). Exact integer arithmetic, brute force.

For a permutation X the map theta -> C(theta).(X-F) is affine, so
  eta_e = min_theta min_X = min_X min_theta
is attained at a corner of the box; enumerating corners x permutations is exact.
"""
import itertools, random, json

def all_perms(N):
    return list(itertools.permutations(range(N)))

def val(const, coef, theta, X, F):
    # C(theta).(X-F), C_ij = const[i][j] + sum_k coef[k][i][j]*theta_k
    N = len(X)
    tot = 0
    for i in range(N):
        for (j, sgn) in ((X[i], 1), (F[i], -1)):
            c = const[i][j]
            for k, th in enumerate(theta):
                c += coef[k][i][j] * th
            tot += sgn * c
    return tot

def h(const, coef, theta, e, F, perms):
    return min(val(const, coef, theta, X, F) for X in perms if X[e[0]] == e[1])

def gap_all(const, coef, theta, F, perms):
    return min(val(const, coef, theta, X, F) for X in perms)

def make(N, rng, mode):
    F = list(range(N)); rng.shuffle(F); F = tuple(F)
    Fset = {(i, F[i]) for i in range(N)}
    out = [(i, j) for i in range(N) for j in range(N) if (i, j) not in Fset]
    e = rng.choice(out)
    K = rng.randint(1, 4)
    const = [[rng.randint(-4, 6) for _ in range(N)] for _ in range(N)]
    coef = [[[0] * N for _ in range(N)] for _ in range(K)]
    side = []
    for k in range(K):
        if mode in ('valid', 'mixedsign'):
            s = rng.choice(['F', 'out'])
            pool = sorted(Fset) if s == 'F' else out
            m = rng.randint(1, len(pool))            # "however often they occur"
            for (i, j) in rng.sample(pool, m):
                c = rng.randint(1, 3)
                if mode == 'mixedsign' and rng.random() < 0.5:
                    c = -c
                coef[k][i][j] = c
            side.append(s)
        elif mode == 'shared':
            (i, j) = rng.choice(sorted(Fset)); coef[k][i][j] = rng.randint(1, 3)
            for (i, j) in rng.sample(out, rng.randint(1, len(out))):
                coef[k][i][j] = rng.randint(1, 3)
            side.append('F')   # recipe ambiguous; test both below
    lo = [rng.randint(-3, 3) for _ in range(K)]
    hi = [l + rng.randint(0, 4) for l in lo]          # zero-length intervals allowed
    return F, e, const, coef, side, lo, hi

def run(mode, trials, seed):
    rng = random.Random(seed)
    bad_eta = bad_opt = 0; strict = 0; F_notopt = 0
    for _ in range(trials):
        N = rng.choice([2, 3, 3, 4, 4, 5]) if mode == 'valid' else rng.choice([3, 4])
        F, e, const, coef, side, lo, hi = make(N, rng, mode)
        perms = all_perms(N)
        K = len(lo)
        corners = list(itertools.product(*[(lo[k], hi[k]) for k in range(K)]))
        eta = min(h(const, coef, th, e, F, perms) for th in corners)
        if mode == 'shared':
            # best single-corner "recipe" of either orientation for the shared parameters
            cand = [tuple(hi), tuple(lo)]
            ok = any(h(const, coef, th, e, F, perms) == eta for th in cand)
            bad_eta += (not ok)
            continue
        star = tuple(hi[k] if side[k] == 'F' else lo[k] for k in range(K))
        hstar = h(const, coef, star, e, F, perms)
        assert hstar >= eta
        if hstar != eta:
            bad_eta += 1
        # interior points never go below eta (sanity of the corner enumeration)
        for _ in range(3):
            th = tuple(lo[k] + (hi[k] - lo[k]) * rng.randint(0, 4) / 4 for k in range(K))
            assert h(const, coef, th, e, F, perms) >= eta - 1e-9
        # "F optimal in every scenario iff optimal at theta*"
        opt_all = all(gap_all(const, coef, th, F, perms) >= 0 for th in corners)
        opt_star = gap_all(const, coef, star, F, perms) >= 0
        if opt_all != opt_star:
            bad_opt += 1
        F_notopt += (not opt_all)
        strict += (max(h(const, coef, th, e, F, perms) for th in corners) > eta)
    return dict(mode=mode, trials=trials, eta_mismatch=bad_eta, optimality_mismatch=bad_opt,
                instances_F_not_always_optimal=F_notopt, instances_h_nonconstant=strict)

# ---- mixed-sign control: all parameters OUTSIDE F, coefficients +1 and -1 --------------------
# D' as in Section 2 but arc g_j->g_j' costs beta_j - theta_j and the diagonal is identically 0.
def mixed_sign_adapter(rng):
    # tiny DAG on vertices 0..nv-1 (topological), s=0, t=nv-1
    nv = rng.choice([3, 4])
    arcs = [(x, y) for x in range(nv) for y in range(x + 1, nv) if rng.random() < 0.8]
    if not any(a[1] == nv - 1 for a in arcs) or not any(a[0] == 0 for a in arcs):
        return None
    arcs += [rng.choice(arcs)] if rng.random() < 0.3 else []      # a parallel arc
    if len(arcs) < 2:
        return None
    J = []
    for _ in range(rng.randint(1, 2)):
        a, b = rng.sample(range(len(arcs)), 2)
        J.append((a, b, rng.randint(0, 4)))
    alpha = [rng.randint(0, 3) for _ in arcs]
    rho = 1
    # vertices of D'
    names = [('v', x) for x in range(nv)]
    darcs = []  # (u, v, const, param index or None, sign)
    for ai, (x, y) in enumerate(arcs):
        p = ('p', ai); names.append(p)
        darcs.append((('v', x), p, alpha[ai], None, 0)); cur = p
        for jj, (a, b, beta) in enumerate(J):
            if a == ai:
                f, f2 = ('f', jj), ('f2', jj); names += [f, f2]
                darcs.append((cur, f, 0, None, 0)); darcs.append((f, f2, 0, jj, +1)); cur = f2
            if b == ai:
                g, g2 = ('g', jj), ('g2', jj); names += [g, g2]
                darcs.append((cur, g, 0, None, 0)); darcs.append((g, g2, beta, jj, -1)); cur = g2
        darcs.append((cur, ('v', y), 0, None, 0))
    N = len(names)
    assert N == nv + len(arcs) + 4 * len(J)
    if N > 9:
        return None
    idx = {nm: i for i, nm in enumerate(names)}
    A0 = sum(alpha); B0 = sum(b for (_, _, b) in J)
    Gamma = rho + A0 + 2 * B0 + 1
    K = len(J)
    const = [[Gamma] * N for _ in range(N)]
    coef = [[[0] * N for _ in range(N)] for _ in range(K)]
    for i in range(N):
        const[i][i] = 0
    for (u, v, c, k, sgn) in darcs:
        const[idx[u]][idx[v]] = c
        if k is not None:
            coef[k][idx[u]][idx[v]] = sgn
    e = (idx[('v', nv - 1)], idx[('v', 0)]); const[e[0]][e[1]] = rho
    F = tuple(range(N))
    # every parameter occurs only outside F (diagonal coefficients all zero)
    assert all(coef[k][i][i] == 0 for k in range(K) for i in range(N))
    # quadratic shortest path by path enumeration
    best = None
    def rec(x, used):
        nonlocal best
        if x == nv - 1:
            q = sum(alpha[a] for a in used) + sum(b for (a, bb, b) in J if a in used and bb in used)
            best = q if best is None else min(best, q)
            return
        for ai, (u, v) in enumerate(arcs):
            if u == x:
                rec(v, used | {ai})
    rec(0, frozenset())
    if best is None:
        return None
    perms = all_perms(N)
    corners = list(itertools.product(*[(0, b) for (_, _, b) in J]))
    eta = min(h(const, coef, th, e, F, perms) for th in corners)
    Fopt = all(gap_all(const, coef, th, F, perms) >= 0 for th in corners)
    # is eta attained at one of the two "uniform" corners?
    return eta == rho + best, Fopt, N

if __name__ == '__main__':
    res = {}
    res['valid'] = run('valid', 1500, 1)
    res['mixedsign_one_side'] = run('mixedsign', 600, 2)
    res['shared_nonneg'] = run('shared', 600, 3)
    rng = random.Random(4); ok = tot = 0; allF = True
    while tot < 25:
        r = mixed_sign_adapter(rng)
        if r is None:
            continue
        tot += 1; ok += r[0]; allF &= r[1]
    res['mixed_sign_adapter_no_parameter_on_F'] = dict(instances=tot, eta_equals_rho_plus_QSPP=ok,
                                                        F_optimal_in_all_corners=allF)
    print(json.dumps(res, indent=1))
    json.dump(res, open(__file__.replace('.py', '_results.json'), 'w'), indent=1)
