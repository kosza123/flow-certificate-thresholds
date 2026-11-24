"""Forbidden pairs -> adapter (Corollary on inapproximability): on random small DAGs with forbidden vertex pairs,
vertex splitting + alpha = 0 + beta = M + rho = 1 gives eta = 1 if a safe s-t path exists and eta >= 1 + M otherwise.
Exact arithmetic; every scenario with theta_j in {0, beta_j/2, beta_j} is checked (identity optimal, dual feasible,
forced value = route formula)."""
from fractions import Fraction as Fr
import itertools, random, json
from adapter import Adapter, perm_cost, exact_min_assignment, exact_forced_min
random.seed(20261124)
M = 1000
res = {"instances": 0, "safe": 0, "unsafe": 0, "scenarios": 0, "maxN": 0}
tries = 0
while res["instances"] < 40:
    tries += 1
    nv = random.randint(4, 6)
    V = list(range(nv)); s, t = 0, nv - 1
    E = [(u, v) for u in V for v in V if u < v and random.random() < 0.55]
    # s-t path must exist
    reach = {s}
    for u in V:
        if u in reach:
            reach |= {v for (x, v) in E if x == u}
    if t not in reach: continue
    k = random.randint(1, 3)
    pairs = set()
    while len(pairs) < k:
        u, v = random.sample(V, 2); pairs.add((min(u, v), max(u, v)))
    pairs = sorted(pairs)
    # vertex splitting: arc index v for (v-,v+), then one arc per edge
    V2 = [("in", v) for v in V] + [("out", v) for v in V]
    arcs = [(("in", v), ("out", v)) for v in V] + [(("out", u), ("in", v)) for (u, v) in E]
    alpha = [Fr(0)] * len(arcs)
    inter = [(u, v, Fr(M)) for (u, v) in pairs]
    ad = Adapter(V2, arcs, ("in", s), ("out", t), alpha, inter, Fr(1))
    assert ad.N == len(V2) + len(arcs) + 4 * len(inter) and ad.dprime_is_acyclic()
    P = ad.original_paths(); assert P
    def vertices(path): return {a for a in path if a < nv}
    safe_exists = any(all(not (u in vertices(p) and v in vertices(p)) for (u, v) in pairs) for p in P)
    betas = [b for (_, _, b) in inter]
    eta = None
    for bits in itertools.product((0, 1, 2), repeat=len(inter)):
        th = [betas[j] * Fr(bits[j], 2) for j in range(len(inter))]
        C = ad.cost_matrix(th); base = perm_cost(C, list(range(ad.N)))
        p = [Fr(0)] * ad.N
        for j in range(len(inter)): p[ad.idx[("k", j)]] = th[j]
        assert all(C[i][jx] - p[i] >= 0 for i in range(ad.N) for jx in range(ad.N))
        c0, _ = exact_min_assignment(C); assert c0 == base
        f, _ = exact_forced_min(C, ad.e); f -= base
        assert f == min(ad.route_formula(Pp, th) for Pp in P)
        eta = f if eta is None else min(eta, f)
        res["scenarios"] += 1
    assert eta == 1 + min(ad.Q(Pp) for Pp in P)
    if safe_exists: assert eta == 1; res["safe"] += 1
    else: assert eta >= 1 + M; res["unsafe"] += 1
    res["instances"] += 1; res["maxN"] = max(res["maxN"], ad.N)
print("forbidden pairs ok:", res)
json.dump(res, open("pafp_results.json", "w"))
