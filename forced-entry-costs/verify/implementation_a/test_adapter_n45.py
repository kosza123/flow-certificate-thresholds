"""Sampled per-scenario checks for the diamond chain at n=4 (N=125) and n=5 (N=196)."""
import random, json, time, itertools
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linear_sum_assignment
from adapter import diamond_chain, perm_cost, to_int_matrix, exact_forced_min, exact_min_assignment, min_marginal
random.seed(11)
t0=time.time(); res={}
for n, nw, nsc in [(4, 6, 12), (5, 3, 8)]:
    cnt=0
    for trial in range(nw):
        lo = trial % 2
        ws = {(i, a): random.randint(lo, 5) for i in range(1, n + 1) for a in (0, 1)}
        wp = {(i, j, a, b): random.randint(lo, 5) for i in range(1, n + 1) for j in range(i + 1, n + 1) for a in (0, 1) for b in (0, 1)}
        ad = diamond_chain(n, ws, wp)
        assert ad.N == 8*n*n-n+1
        betas = [b for (_, _, b) in ad.inter]; J=len(betas)
        # scenario attaining the minimum according to (7): theta=0 if only A used ... take theta_j = beta_j * [z*_i != a] (so cost is beta*u*v on z*)
        zbest = min(itertools.product((0,1), repeat=n), key=lambda z: sum(ws[(i,z[i-1])] for i in range(1,n+1)) + sum(wp[(i,j,z[i-1],z[j-1])] for i in range(1,n+1) for j in range(i+1,n+1)))
        scen = [[Fr(0)]*J, list(betas)]
        scen.append([betas[q]*(0 if zbest[i-1]==a else 1) for q,(i,j,a,b) in enumerate(ad.pair_keys)])
        for _ in range(nsc):
            scen.append([b*Fr(random.randint(0,13),13) for b in betas])
            scen.append([b*random.randint(0,1) for b in betas])
        vals=[]
        for th in scen:
            C = ad.cost_matrix(th); N=ad.N
            # dual
            p=[Fr(0)]*N
            for j in range(J): p[ad.idx[("k",j)]] = Fr(th[j])
            assert all(C[i][jx]-p[i] >= 0 for i in range(N) for jx in range(N))
            assert all(C[i][i]-p[i]==0 for i in range(N))
            base = perm_cost(C, list(range(N)))
            A,L = to_int_matrix(C); An=np.array(A,dtype=np.float64)
            r,c = linear_sum_assignment(An); assert Fr(int(round(An[r,c].sum())),L)==base
            rr,cc = ad.e
            rows=[i for i in range(N) if i!=rr]; cols=[j for j in range(N) if j!=cc]
            sub=An[np.ix_(rows,cols)]; r2,c2=linear_sum_assignment(sub)
            forced = Fr(int(round(sub[r2,c2].sum()))+A[rr][cc], L) - base
            # claimed route minimum via z-enumeration
            best=None
            for z in itertools.product((0,1), repeat=n):
                v = Fr(1)+sum(Fr(ws[(i,z[i-1])]) for i in range(1,n+1))
                for q,(i,j,a,b) in enumerate(ad.pair_keys):
                    if z[i-1]==a: v+=th[q]
                    if z[j-1]==b: v+=betas[q]-th[q]
                best = v if best is None else min(best,v)
            assert forced==best, (forced,best)
            vals.append(forced); cnt+=1
        target = 1+min_marginal(n, ws, wp)
        assert min(vals) >= target and vals[2]==target, (min(vals), vals[2], target)
    res[f"n={n}"]=dict(N=ad.N, scenarios=cnt)
    print(n, res[f"n={n}"], round(time.time()-t0,1), flush=True)
json.dump(res, open("adapter_n45_results.json","w"), indent=1)
