"""Corollary on sparse interactions: for small graphs G, the diamond chain with interactions only along E(G) has
dimension N_G = 7n+1+16|E|, the identity is optimal with the dual certificate, the forced value equals the route
formula in every corner scenario, and eta_G(w) = 1 + min_z w.m_G(z).  Exact arithmetic."""
from fractions import Fraction as Fr
import itertools, random, json
from adapter import Adapter, perm_cost, exact_min_assignment, exact_forced_min
random.seed(7)
def build(n, E, ws, wp):
    V = [("v", i) for i in range(n + 1)] + [("b", i, a) for i in range(1, n + 1) for a in (0, 1)]
    arcs = []; idx = {}
    for i in range(1, n + 1):
        for a in (0, 1):
            idx[(i, a)] = len(arcs); arcs.append((("v", i - 1), ("b", i, a)))
    alpha = [ws[(i, a)] for i in range(1, n + 1) for a in (0, 1)]
    for i in range(1, n + 1):
        for a in (0, 1):
            arcs.append((("b", i, a), ("v", i))); alpha.append(Fr(0))
    inter = [(idx[(i, a)], idx[(j, b)], wp[(i, j, a, b)]) for (i, j) in E for a in (0, 1) for b in (0, 1)]
    return Adapter(V, arcs, ("v", 0), ("v", n), alpha, inter, Fr(1)), idx
res = []
graphs = [(3, [(1, 2), (2, 3)]), (3, [(1, 3)]), (4, [(1, 2), (2, 3), (3, 4)]), (4, [(1, 2), (3, 4)]), (4, [(1, 2), (2, 3), (3, 4), (1, 4)])]
for (n, E) in graphs:
    for trial in range(2):
        ws = {(i, a): Fr(random.randint(0, 5)) for i in range(1, n + 1) for a in (0, 1)}
        wp = {(i, j, a, b): Fr(random.randint(0, 5)) for (i, j) in E for a in (0, 1) for b in (0, 1)}
        ad, idx = build(n, E, ws, wp)
        assert ad.N == 7 * n + 1 + 16 * len(E), (ad.N, n, E)
        betas = [b for (_, _, b) in ad.inter]; J = len(betas)
        P = ad.original_paths(); assert len(P) == 2 ** n
        truth = 1 + min(sum(ws[(i, z[i - 1])] for i in range(1, n + 1)) + sum(wp[(i, j, z[i - 1], z[j - 1])] for (i, j) in E)
                        for z in itertools.product((0, 1), repeat=n))
        assert 1 + min(ad.Q(p) for p in P) == truth
        scen = [[Fr(0)] * J, list(betas)] + [[b * random.randint(0, 1) for b in betas] for _ in range(6)] + [[b * Fr(random.randint(0, 7), 7) for b in betas] for _ in range(3)]
        eta = None
        for th in scen:
            C = ad.cost_matrix(th); base = perm_cost(C, list(range(ad.N)))
            p = [Fr(0)] * ad.N
            for j in range(J): p[ad.idx[("k", j)]] = th[j]
            assert all(C[i][jx] - p[i] >= 0 for i in range(ad.N) for jx in range(ad.N))
            c0, _ = exact_min_assignment(C); assert c0 == base
            f, _ = exact_forced_min(C, ad.e); f -= base
            assert f == min(ad.route_formula(pp, th) for pp in P)
            assert f >= truth
            eta = f if eta is None else min(eta, f)
        # the minimising corner scenario of the best z
        zb = min(itertools.product((0, 1), repeat=n), key=lambda z: sum(ws[(i, z[i - 1])] for i in range(1, n + 1)) + sum(wp[(i, j, z[i - 1], z[j - 1])] for (i, j) in E))
        th = [betas[q] * (0 if ad.inter[q][0] == idx[(ad_i, zb[ad_i - 1])] else 1) for q, ad_i in enumerate([i for (i, j) in E for a in (0, 1) for b in (0, 1)])]
        C = ad.cost_matrix(th); base = perm_cost(C, list(range(ad.N)))
        f, _ = exact_forced_min(C, ad.e); f -= base
        assert f == truth, (f, truth)
        res.append({"n": n, "E": E, "N": ad.N, "eta": str(truth), "scenarios": len(scen) + 1})
print("sparse interactions ok:", len(res), "instances; N =", sorted({r["N"] for r in res}))
json.dump(res, open("sparse_results.json", "w"))
