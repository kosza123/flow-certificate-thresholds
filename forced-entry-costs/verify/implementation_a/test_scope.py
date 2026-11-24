"""Scope probes: (1) outside the box [0,beta] the 'unique optimum in every real scenario' claim fails;
(2) a constant completion cost works for bounded weights; (3) alternative uniqueness proof via reduced costs:
the tight off-diagonal entries of the supplied dual form an acyclic digraph."""
from fractions import Fraction as Fr
import itertools, random, json
from adapter import diamond_chain, perm_cost, exact_min_assignment, exact_forced_min, min_marginal

random.seed(3)
out = {}
n = 2
ws = {(i, a): 1 for i in range(1, n + 1) for a in (0, 1)}
wp = {(i, j, a, b): 1 for i in range(1, n + 1) for j in range(i + 1, n + 1) for a in (0, 1) for b in (0, 1)}
ad = diamond_chain(n, ws, wp)
J = len(ad.inter)
# (1a) one theta above its upper endpoint
th = [Fr(0)] * J
th[ad.pair_keys.index((1, 2, 1, 0))] = Fr(6)  # beta = 1
C = ad.cost_matrix(th)
base = perm_cost(C, list(range(ad.N)))
c0, p0 = exact_min_assignment(C)
out["theta above box (one theta = beta+5)"] = dict(identity_cost=str(base), optimum=str(c0))
assert c0 < base
# (1b) one theta below 0
th = [Fr(0)] * J
th[ad.pair_keys.index((1, 2, 0, 0))] = Fr(-7)
C = ad.cost_matrix(th)
base = perm_cost(C, list(range(ad.N)))
c0, p0 = exact_min_assignment(C)
out["theta below box (one theta = -7)"] = dict(identity_cost=str(base), optimum=str(c0))
assert c0 < base

# (3) tight digraph of the supplied dual is acyclic (=> uniqueness even among fractional points)
def tight_acyclic(ad, th):
    C = ad.cost_matrix(th)
    N = ad.N
    p = [Fr(0)] * N
    for j in range(len(ad.inter)):
        p[ad.idx[("k", j)]] = Fr(th[j])
    adj = {i: [jx for jx in range(N) if jx != i and C[i][jx] - p[i] == 0] for i in range(N)}
    indeg = [0] * N
    for i in adj:
        for jx in adj[i]:
            indeg[jx] += 1
    st = [i for i in range(N) if indeg[i] == 0]
    cnt = 0
    while st:
        u = st.pop()
        cnt += 1
        for v in adj[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                st.append(v)
    return cnt == N

cnt = 0
for n in (2, 3):
    for trial in range(10):
        ws = {(i, a): random.randint(0, 5) for i in range(1, n + 1) for a in (0, 1)}
        wp = {(i, j, a, b): random.randint(0, 5) for i in range(1, n + 1) for j in range(i + 1, n + 1)
              for a in (0, 1) for b in (0, 1)}
        ad = diamond_chain(n, ws, wp)
        betas = [b for (_, _, b) in ad.inter]
        for th in ([Fr(0)] * len(betas), list(betas), [b * Fr(random.randint(0, 9), 9) for b in betas]):
            assert tight_acyclic(ad, th)
            cnt += 1
out["tight digraph of supplied dual acyclic (scenarios)"] = cnt

# (2) constant completion cost H_max for weights in {1..5}
n = 2
Hmax = 2 + 10 * n + 20 * n * (n - 1)
ok = 0
for trial in range(30):
    ws = {(i, a): random.randint(1, 5) for i in range(1, n + 1) for a in (0, 1)}
    wp = {(i, j, a, b): random.randint(1, 5) for i in range(1, n + 1) for j in range(i + 1, n + 1)
          for a in (0, 1) for b in (0, 1)}
    ad = diamond_chain(n, ws, wp)
    assert ad.H <= Hmax
    ad.H = Fr(Hmax)
    betas = [b for (_, _, b) in ad.inter]
    eta = None
    for bits in itertools.product((0, 1), repeat=len(betas)):
        th = [betas[j] * bits[j] for j in range(len(betas))]
        C = ad.cost_matrix(th)
        base = perm_cost(C, list(range(ad.N)))
        c0, _ = exact_min_assignment(C)
        assert c0 == base
        f, _ = exact_forced_min(C, ad.e)
        eta = f - base if eta is None else min(eta, f - base)
    assert eta == 1 + min_marginal(n, ws, wp)
    ok += 1
out["constant completion cost Hmax works (n=2 weight vectors)"] = ok
json.dump(out, open("scope_results.json", "w"), indent=1)
print(out)
