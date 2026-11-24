"""Proposition 1 (no parameter shared across F), brute force: random N x N matrices (N = 3, 4) affine in theta with
nonnegative integer coefficients; each parameter occurs in 1-3 entries, all on F (identity) or all off F.
h_e(theta) = min over permutations with the entry e; eta_e = min over all corner scenarios (h_e is concave in theta,
so the minimum over the box is attained at a corner).  Claim: eta_e = h_e(theta*), and F is optimal in every corner
scenario iff it is optimal at theta*.  Control: with one parameter shared across F the claim fails in some instances."""
import itertools, random, json
random.seed(11)
def run(shared):
    bad = 0; n_inst = 0; optimal_equiv_bad = 0
    for _ in range(400):
        N = random.choice((3, 4)); K = random.randint(1, 4)
        base = [[random.randint(0, 6) for _ in range(N)] for _ in range(N)]
        lo = [random.randint(0, 2) for _ in range(K)]; hi = [l + random.randint(1, 4) for l in lo]
        occ = []; onF = []
        for k in range(K):
            side = random.random() < 0.5; onF.append(side)
            cells = [(i, i) for i in range(N)] if side else [(i, j) for i in range(N) for j in range(N) if i != j]
            ch = random.sample(cells, random.randint(1, min(3, len(cells))))
            if shared and k == 0:
                ch = [random.choice([(i, i) for i in range(N)]), random.choice([(i, j) for i in range(N) for j in range(N) if i != j])]
            occ.append([(c, random.randint(1, 3)) for c in ch])
        def C(theta):
            M = [row[:] for row in base]
            for k in range(K):
                for ((i, j), co) in occ[k]: M[i][j] += co * theta[k]
            return M
        e = random.choice([(i, j) for i in range(N) for j in range(N) if i != j])
        perms = list(itertools.permutations(range(N)))
        def h(theta):
            M = C(theta); f = sum(M[i][i] for i in range(N))
            return min(sum(M[i][p[i]] for i in range(N)) for p in perms if p[e[0]] == e[1]) - f
        def Fopt(theta):
            M = C(theta); f = sum(M[i][i] for i in range(N))
            return min(sum(M[i][p[i]] for i in range(N)) for p in perms) == f
        star = [hi[k] if onF[k] else lo[k] for k in range(K)]
        corners = [[hi[k] if b else lo[k] for k, b in enumerate(bits)] for bits in itertools.product((0, 1), repeat=K)]
        eta = min(h(th) for th in corners)
        if eta != h(star): bad += 1
        if all(Fopt(th) for th in corners) != Fopt(star): optimal_equiv_bad += 1
        n_inst += 1
    return n_inst, bad, optimal_equiv_bad
a = run(False); b = run(True)
assert a[1] == 0 and a[2] == 0, a
assert b[1] > 0, b
print("proposition 1 ok:", {"instances": a[0], "violations": a[1], "optimality_equivalence_violations": a[2],
      "control_with_one_shared_parameter": {"instances": b[0], "violations_of_the_formula": b[1]}})
json.dump({"main": a, "control": b}, open("prop1_results.json", "w"))
