"""Explicit DAG with an arc INTO s, an arc OUT OF t, parallel arcs, a dead end, repeated and reversed interactions."""
from fractions import Fraction as Fr
import itertools
from adapter import Adapter, perm_cost, exact_min_assignment, exact_forced_min
V = ["x", "s", "m", "t", "y", "dead"]
arcs = [("x", "s"), ("s", "m"), ("s", "m"), ("m", "t"), ("s", "t"), ("t", "y"), ("m", "dead")]
alpha = [Fr(3), Fr(1, 2), Fr(0), Fr(2), Fr(7, 2), Fr(1), Fr(0)]
inter = [(1, 3, Fr(2)), (3, 2, Fr(5, 3)), (1, 3, Fr(1)), (0, 5, Fr(4)), (4, 6, Fr(0)), (2, 1, Fr(3))]
ad = Adapter(V, arcs, "s", "t", alpha, inter, Fr(2, 5))
assert ad.N == len(V) + len(arcs) + 4 * len(inter) and ad.dprime_is_acyclic()
P = ad.original_paths()
assert sorted(ad.collapse(p) for p in ad.dprime_paths()) == sorted(P) and len(P) == 3
betas = [b for (_, _, b) in inter]
eta = None; n = 0
for bits in itertools.product((0, 1, 2), repeat=len(inter)):
    th = [betas[j] * Fr(bits[j], 2) for j in range(len(inter))]
    C = ad.cost_matrix(th)
    base = perm_cost(C, list(range(ad.N)))
    p = [Fr(0)] * ad.N
    for j in range(len(inter)): p[ad.idx[("k", j)]] = th[j]
    assert all(C[i][jx] - p[i] >= 0 for i in range(ad.N) for jx in range(ad.N))
    c0, _ = exact_min_assignment(C); assert c0 == base
    f, _ = exact_forced_min(C, ad.e); f -= base
    assert f == min(ad.route_formula(Pp, th) for Pp in P)
    if all(b != 1 for b in bits): eta = f if eta is None else min(eta, f)
    n += 1
assert eta == ad.delta + min(ad.Q(Pp) for Pp in P)
print("explicit DAG ok: N =", ad.N, "paths =", len(P), "scenarios =", n, "eta =", eta)
