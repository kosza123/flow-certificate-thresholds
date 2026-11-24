"""Independent implementation (A) of the exact adapter: quadratic shortest path -> assignment.

Written only from a written description of the construction (Section 2 of the paper), not from other code.
All arithmetic is exact (fractions.Fraction / Python ints).
"""
from fractions import Fraction as Fr
from math import lcm
import itertools


class Adapter:
    """D=(V,arcs) DAG, terminals s,t, alpha[a]>=0, inter=[(a_idx,b_idx,beta)], delta>0."""

    def __init__(self, V, arcs, s, t, alpha, inter, delta=Fr(1)):
        self.V = list(V)
        self.arcs = list(arcs)
        self.s, self.t = s, t
        self.alpha = [Fr(x) for x in alpha]
        self.inter = [(a, b, Fr(beta)) for (a, b, beta) in inter]
        self.delta = Fr(delta)
        for (a, b, beta) in self.inter:
            assert a != b, "interaction must pair two distinct arcs"
        self.A0 = sum(self.alpha, Fr(0))
        self.B0 = sum((b for (_, _, b) in self.inter), Fr(0))
        self.H = self.delta + self.A0 + 2 * self.B0 + 1
        self._build()

    def _build(self):
        names = [("V", v) for v in self.V]
        names += [("p", a) for a in range(len(self.arcs))]
        for j in range(len(self.inter)):
            names += [("r", j), ("q", j), ("k", j), ("h", j)]
        self.names = names
        self.idx = {nm: i for i, nm in enumerate(names)}
        self.N = len(names)
        # designated off-diagonal arcs of D' : dict (row,col) -> ("const", value) or ("theta", j)
        des = {}
        self.chain = {}  # arc index -> list of D' vertices of its chain (u, p_a, ..., v)

        def add(u, v, kind, val):
            key = (self.idx[u], self.idx[v])
            assert key not in des, f"entry collision {u}->{v}"
            assert key[0] != key[1]
            des[key] = (kind, val)

        for a, (u, v) in enumerate(self.arcs):
            cur = ("p", a)
            add(("V", u), cur, "const", self.alpha[a])
            ch = [("V", u), cur]
            for j, (aj, bj, beta) in enumerate(self.inter):  # fixed order of incidences
                if aj == a:
                    add(cur, ("r", j), "const", Fr(0))
                    add(("r", j), ("q", j), "theta", j)
                    ch += [("r", j), ("q", j)]
                    cur = ("q", j)
                if bj == a:
                    add(cur, ("k", j), "const", Fr(0))
                    add(("k", j), ("h", j), "const", beta)
                    ch += [("k", j), ("h", j)]
                    cur = ("h", j)
            add(cur, ("V", v), "const", Fr(0))
            ch.append(("V", v))
            self.chain[a] = ch
        self.dag_arcs = dict(des)  # D' only
        self.e = (self.idx[("V", self.t)], self.idx[("V", self.s)])
        assert self.e not in des
        des[self.e] = ("const", self.delta)
        self.designated = des
        self.theta_pos = {}
        for j in range(len(self.inter)):
            self.theta_pos[j] = [(self.idx[("r", j)], self.idx[("q", j)]),
                                 (self.idx[("k", j)], self.idx[("k", j)])]

    # ------------------------------------------------------------------
    def cost_matrix(self, theta):
        """Full N x N matrix of Fractions for scenario theta (list of Fractions)."""
        N = self.N
        C = [[self.H] * N for _ in range(N)]
        for i in range(N):
            C[i][i] = Fr(0)
        for (i, j), (kind, val) in self.designated.items():
            C[i][j] = Fr(theta[val]) if kind == "theta" else val
        for j in range(len(self.inter)):
            kk = self.idx[("k", j)]
            C[kk][kk] = Fr(theta[j])
        return C

    def symbolic_occurrences(self):
        """Return for each theta_j the list of matrix entries whose cost is theta_j (coeff +1)."""
        occ = {j: [] for j in range(len(self.inter))}
        for (i, jx), (kind, val) in self.designated.items():
            if kind == "theta":
                occ[val].append((i, jx))
        for j in range(len(self.inter)):
            kk = self.idx[("k", j)]
            occ[j].append((kk, kk))
        return occ

    # ------------------------------------------------------------------
    def original_paths(self):
        """All s-t paths of D as tuples of arc indices."""
        out = {}
        for a, (u, v) in enumerate(self.arcs):
            out.setdefault(u, []).append(a)
        res = []

        def rec(u, acc, seen):
            if u == self.t:
                res.append(tuple(acc))
                # a DAG path may not continue through t back to t, so stop
                return
            for a in out.get(u, []):
                v = self.arcs[a][1]
                if v in seen:
                    raise RuntimeError("input graph is not acyclic")
                rec(v, acc + [a], seen | {v})

        rec(self.s, [], {self.s})
        return res

    def dprime_paths(self):
        """All s-t paths in D' as lists of vertex indices (computed on D' itself)."""
        out = {}
        for (i, j) in self.dag_arcs:
            out.setdefault(i, []).append(j)
        s, t = self.idx[("V", self.s)], self.idx[("V", self.t)]
        res = []

        def rec(u, acc):
            if u == t:
                res.append(list(acc))
                return
            for v in out.get(u, []):
                assert v not in acc
                rec(v, acc + [v])

        rec(s, [s])
        return res

    def dprime_is_acyclic(self):
        indeg = [0] * self.N
        out = {}
        for (i, j) in self.dag_arcs:
            out.setdefault(i, []).append(j)
            indeg[j] += 1
        stack = [i for i in range(self.N) if indeg[i] == 0]
        cnt = 0
        while stack:
            u = stack.pop()
            cnt += 1
            for v in out.get(u, []):
                indeg[v] -= 1
                if indeg[v] == 0:
                    stack.append(v)
        return cnt == self.N

    def route_formula(self, path_arcs, theta):
        """Claimed relative cost of the route permutation of original path P (cost identity, Section 2 of the paper)."""
        y = set(path_arcs)
        val = self.delta + sum((self.alpha[a] for a in y), Fr(0))
        for j, (aj, bj, beta) in enumerate(self.inter):
            if aj in y:
                val += Fr(theta[j])
            if bj in y:
                val += beta - Fr(theta[j])
        return val

    def Q(self, path_arcs):
        y = set(path_arcs)
        val = sum((self.alpha[a] for a in y), Fr(0))
        for (aj, bj, beta) in self.inter:
            if aj in y and bj in y:
                val += beta
        return val

    def perm_of_dprime_path(self, vpath):
        perm = list(range(self.N))
        for x, y in zip(vpath, vpath[1:]):
            perm[x] = y
        perm[vpath[-1]] = vpath[0]
        return perm

    def collapse(self, vpath):
        """Map a D' path (vertex list) to the tuple of original arcs whose p_a it visits."""
        res = []
        for v in vpath:
            nm = self.names[v]
            if nm[0] == "p":
                res.append(nm[1])
        return tuple(res)


# ----------------------------------------------------------------------
def perm_cost(C, perm):
    return sum((C[i][perm[i]] for i in range(len(perm))), Fr(0))


def to_int_matrix(C):
    """Scale a Fraction matrix to integers; returns (int matrix, scale)."""
    L = 1
    for row in C:
        for x in row:
            L = lcm(L, Fr(x).denominator)
    return [[int(Fr(x) * L) for x in row] for row in C], L


def hungarian_int(a):
    """Exact min-cost perfect matching on a square integer matrix (O(n^3)).
    Returns (cost, assignment row->col, row potentials u, col potentials v)."""
    n = len(a)
    INF = float("inf")
    u = [0] * (n + 1)
    v = [0] * (n + 1)
    p = [0] * (n + 1)
    way = [0] * (n + 1)
    for i in range(1, n + 1):
        p[0] = i
        j0 = 0
        minv = [INF] * (n + 1)
        used = [False] * (n + 1)
        while True:
            used[j0] = True
            i0 = p[j0]
            delta = INF
            j1 = 0
            row = a[i0 - 1]
            ui0 = u[i0]
            for j in range(1, n + 1):
                if not used[j]:
                    cur = row[j - 1] - ui0 - v[j]
                    if cur < minv[j]:
                        minv[j] = cur
                        way[j] = j0
                    if minv[j] < delta:
                        delta = minv[j]
                        j1 = j
            for j in range(n + 1):
                if used[j]:
                    u[p[j]] += delta
                    v[j] -= delta
                else:
                    minv[j] -= delta
            j0 = j1
            if p[j0] == 0:
                break
        while True:
            j1 = way[j0]
            p[j0] = p[j1]
            j0 = j1
            if j0 == 0:
                break
    assign = [0] * n
    for j in range(1, n + 1):
        assign[p[j] - 1] = j - 1
    cost = sum(a[i][assign[i]] for i in range(n))
    return cost, assign, u[1:], v[1:]


def exact_min_assignment(C):
    """Exact min cost assignment of a Fraction matrix. Returns (Fraction cost, perm)."""
    A, L = to_int_matrix(C)
    cost, assign, u, v = hungarian_int(A)
    # self-check of optimality through the dual produced by the algorithm
    n = len(A)
    for i in range(n):
        for j in range(n):
            assert u[i] + v[j] <= A[i][j]
    assert sum(u) + sum(v) == cost
    return Fr(cost, L), assign


def exact_forced_min(C, e):
    """Exact min cost over permutations with perm[e[0]] == e[1]."""
    r, c = e
    n = len(C)
    rows = [i for i in range(n) if i != r]
    cols = [j for j in range(n) if j != c]
    sub = [[C[i][j] for j in cols] for i in rows]
    cost, assign = exact_min_assignment(sub)
    perm = [None] * n
    perm[r] = c
    for a, i in enumerate(rows):
        perm[i] = cols[assign[a]]
    return cost + C[r][c], perm


# ----------------------------------------------------------------------
def diamond_chain(n, w_single, w_pair, delta=Fr(1)):
    """The diamond family (Section 3 of the paper).
    w_single[(i,a)], i in 1..n, a in {0,1};  w_pair[(i,j,a,b)], i<j."""
    V = [("v", i) for i in range(n + 1)] + [("b", i, a) for i in range(1, n + 1) for a in (0, 1)]
    arcs, alpha, did = [], [], {}
    for i in range(1, n + 1):
        for a in (0, 1):
            did[(i, a)] = len(arcs)
            arcs.append((("v", i - 1), ("b", i, a)))
            alpha.append(Fr(w_single[(i, a)]))
            arcs.append((("b", i, a), ("v", i)))
            alpha.append(Fr(0))
    inter = []
    keys = []
    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):
            for a in (0, 1):
                for b in (0, 1):
                    inter.append((did[(i, a)], did[(j, b)], Fr(w_pair[(i, j, a, b)])))
                    keys.append((i, j, a, b))
    ad = Adapter(V, arcs, ("v", 0), ("v", n), alpha, inter, delta)
    ad.did = did
    ad.pair_keys = keys
    return ad


def marginal_value(n, w_single, w_pair, z):
    val = Fr(0)
    for i in range(1, n + 1):
        val += Fr(w_single[(i, z[i - 1])])
    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):
            val += Fr(w_pair[(i, j, z[i - 1], z[j - 1])])
    return val


def min_marginal(n, w_single, w_pair):
    return min(marginal_value(n, w_single, w_pair, z) for z in itertools.product((0, 1), repeat=n))
