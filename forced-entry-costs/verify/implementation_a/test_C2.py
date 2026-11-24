"""(a) size crossover of the eps=1 LP (t=6) against the exact simplex 2^n; (b) the eps=1 instance at n=8 (t=6, r=7)."""
import math, json, random, itertools, time, importlib.util, sys, io, contextlib
out = {}
# (a)
t = math.ceil(8 * math.log(2) / 1.0)
assert t == 6
cross = None
for n in range(t + 1, 200):
    if 2 ** (t + 1) * math.comb(n, t + 1) < 2 ** n:
        cross = n
        break
out["eps=1: t"] = t
out["eps=1: smallest n with 2^(t+1)C(n,t+1) < 2^n"] = cross
t2 = math.ceil(8 * math.log(2) / 0.25)
cross2 = next(n for n in range(t2 + 1, 5000) if 2 ** (t2 + 1) * math.comb(n, t2 + 1) < 2 ** n)
out["eps=1/2: t"] = t2
out["eps=1/2: smallest n with 2^(t+1)C(n,t+1) < 2^n"] = cross2
t3 = math.ceil(8 * math.log(2) / 0.01)
out["eps=0.1: t"] = t3
print(out, flush=True)

# (b) reuse the LocalLP class from test_C without running its script body
src = open("test_C.py").read().split("# ------------------------------------------------------------------ 1. sandwich")[0]
ns = {}
exec(compile(src, "test_C_head", "exec"), ns)
LocalLP, rand_weights, all_h, kn = ns["LocalLP"], ns["rand_weights"], ns["all_h"], ns["kn"]
t0 = time.time()
n = 8
lp = LocalLP(n, 6)
res = []
for mode in ["frustrated", "antiferro", "uniform", "ends"]:
    ws, wp = rand_weights(n, mode)
    L, x = lp.solve(ws, wp)
    eta = 1.0 + all_h(n, ws, wp).min()
    assert 1 + kn(n) <= L + 1e-6 and L <= eta + 1e-6 and eta <= 2 * L + 1e-6
    assert eta <= L + n * n * math.sqrt(2 * math.log(2) / 6) + 1e-6
    res.append(dict(mode=mode, L=round(L, 6), eta=round(float(eta), 6)))
    print(res[-1], round(time.time() - t0, 1), flush=True)
out["n=8,t=6"] = dict(inequalities=lp.n_ineq, variables=len(lp.var), results=res)
json.dump(out, open("C2_results.json", "w"), indent=1)
