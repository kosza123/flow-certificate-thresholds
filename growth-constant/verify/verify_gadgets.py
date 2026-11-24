"""Exact verification of the gadgets of the note "Two-Port Substitution and the Growth of the Smallest Current in
Planar Networks".  Python 3 with networkx (planarity tests only); all arithmetic is exact (fractions).
Run:  python3 verify_gadgets.py
"""
import math, json, sys
from fractions import Fraction as Fr
import networkx as nx

def green(n, E):
    # Laplacian reduced at vertex 0, exact inverse by Gauss-Jordan; returns (det, X) or (0, None)
    m = n - 1
    L = [[Fr(0)] * m for _ in range(m)]
    for u, v in E:
        if u == v: continue
        for a, b in ((u, v), (v, u)):
            if a > 0:
                L[a-1][a-1] += 1
                if b > 0: L[a-1][b-1] -= 1
    A = [row[:] + [Fr(int(i == j)) for j in range(m)] for i, row in enumerate(L)]
    det = Fr(1)
    for c in range(m):
        p = next((r for r in range(c, m) if A[r][c] != 0), None)
        if p is None: return 0, None
        if p != c: A[c], A[p] = A[p], A[c]; det = -det
        det *= A[c][c]; inv = 1 / A[c][c]
        A[c] = [x * inv for x in A[c]]
        for r in range(m):
            if r != c and A[r][c] != 0:
                f = A[r][c]; A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    X = [[Fr(0)] * n for _ in range(n)]
    for i in range(m):
        for j in range(m): X[i+1][j+1] = A[i][m + j]
    return det, X

def reff(X, s, t): return X[s][s] + X[t][t] - 2 * X[s][t]
def reff(X, s, t): return X[s][s] + X[t][t] - 2 * X[s][t]

def twoport(E, n, s, t, ei):
    tau, X = green(n, E)
    x, y = E[ei]; Ed = E[:ei] + E[ei+1:]
    gam, Xd = green(n, Ed)
    if gam == 0: return None
    lab = {}; k = 0
    for v in range(n):
        w = x if v == y else v
        if w not in lab: lab[w] = k; k += 1
    mp = lambda v: lab[x if v == y else v]
    Ec = [(mp(a), mp(b)) for a, b in Ed]; dlt, Xc = green(n - 1, Ec)
    kap = tau * (X[x][s] - X[x][t] - X[y][s] + X[y][t])
    alp = gam * reff(Xd, s, t); bet = dlt * (0 if mp(s) == mp(t) else reff(Xc, mp(s), mp(t)))
    return int(alp), int(bet), int(gam), int(dlt), int(kap), int(tau)

def rho(a, b, g, d):
    tr = a + d; dt = a * d - b * g
    return (tr + math.sqrt(max(tr * tr - 4 * dt, 0))) / 2

def dual_gadget(n, G, s, t, e):
    """planar dual of G + f (f = st); ports = the two faces at f; observed = dual of e.  Returns (n*, G*, s*, t*, e*)."""
    Hs = [tuple(x) for x in G] + [(s, t)]
    Gx = nx.Graph(Hs); assert Gx.number_of_edges() == len(Hs), 'needs a simple graph'
    ok, emb = nx.check_planarity(Gx); assert ok
    fid = {}; nf = 0; seen = set()
    for u, v in emb.edges():
        if (u, v) in seen: continue
        cyc = emb.traverse_face(u, v, mark_half_edges=seen)
        for i in range(len(cyc)): fid[(cyc[i], cyc[(i + 1) % len(cyc)])] = nf
        nf += 1
    D = [(fid[(u, v)], fid[(v, u)]) for u, v in Hs]
    sd, td = D[-1]
    return nf, D[:-1], sd, td, e

def dagger(n, G, s, t, e):
    x, y = G[e]; G2 = [g for i, g in enumerate(G) if i != e] + [(s, t)]
    return n, G2, x, y, len(G2) - 1

def info(name, n, G, s, t, e):
    tp = twoport(G, n, s, t, e); a, b, g, d, k, tau = tp
    Gx = nx.MultiGraph(); Gx.add_edges_from(G); simple = nx.Graph(Gx).number_of_edges() == len(G)
    G2 = nx.Graph(Gx); G2.add_edge(s, t)
    print('%-12s n=%d q=%d M=%s kappa=%d det=%d simple=%s planar=%s cofacial=%s' % (name, n, len(G), (a, b, g, d), k, a * d - b * g, simple, nx.check_planarity(nx.Graph(Gx))[0], nx.check_planarity(G2)[0]))
    return (a, b, g, d), k

def nest(chain):
    """chain[0] outermost.  Each item (n, G, s, t, e)."""
    n0, G0, s0, t0, e0 = chain[0]; nv = n0; EE = list(G0); obs = e0
    for (n, G, s, t, e) in chain[1:]:
        x, y = EE[obs]; del EE[obs]; mp = {}
        for v in range(n):
            if v == s: mp[v] = x
            elif v == t: mp[v] = y
            else: mp[v] = nv; nv += 1
        new = [(mp[u], mp[w]) for u, w in G]; EE.extend(new); obs = len(EE) - len(new) + e
    return nv, EE, obs, s0, t0


def mul(A, B): return (A[0]*B[0]+A[1]*B[2], A[0]*B[1]+A[1]*B[3], A[2]*B[0]+A[3]*B[2], A[2]*B[1]+A[3]*B[3])

def check(cond, msg):
    print(('ok   ' if cond else 'FAIL ') + msg)
    if not cond: sys.exit(1)

def current(chain):
    nv, EE, obs, s, t = nest(chain)
    T, Gm = green(nv, EE); x, y = EE[obs]
    I = Gm[x][s] - Gm[x][t] - Gm[y][s] + Gm[y][t]
    Gx = nx.Graph(EE); G2 = nx.Graph(Gx); G2.add_edge(s, t)
    ok = Gx.number_of_edges() == len(EE) and nx.check_planarity(Gx)[0] and nx.check_planarity(G2)[0]
    return len(EE), 1 / abs(I), T, ok

# --- H7
H7 = [(0,4),(0,5),(0,6),(1,3),(1,5),(1,6),(2,3),(2,4),(2,6),(3,6),(4,5)]
X7 = (7, H7, 3, 4, H7.index((0,5)))
a, b, g, d, k, tau = twoport(H7, 7, 3, 4, X7[4])
check((a, b, g, d) == (83, 94, 98, 111) and abs(k) == 1 and tau == 209, 'H7: M = (83,94,98,111), |kappa| = 1, tau = 209')
for lev, want in ((1, 209), (2, 40545), (3, 7865521)):
    q, inv, T, ok = current([X7] * lev)
    check(q == 10 * lev + 1 and inv == want and T == want and ok, 'H7 level %d: %d edges, 1/|I| = tau = %d, simple, planar, co-facial' % (lev, q, want))

# --- X23
import os
data = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gadgets.json')))['23']
n = data['n']; G = [tuple(x) for x in data['edges']]; s, t = data['s'], data['t']; e = G.index(tuple(data['e']))
X = (n, G, s, t, e)
a, b, g, d, k, tau = twoport(G, n, s, t, e); M = (a, b, g, d)
check(M == (63678, 75857, 73105, 87087) and abs(k) == 1 and a*d - b*g == 1 and tau == 160192, 'X23: M = (63678,75857,73105,87087), |kappa| = 1, det = 1, tau = 160192')
q, inv, T, ok = current([X]); check(q == 23 and inv == 160192 and ok, 'X23: 23 edges, 1/|I| = 160192, simple, planar, co-facial')
Xd = dagger(*X); ad, bd, gd, dd, kd, _ = twoport(Xd[1], Xd[0], Xd[2], Xd[3], Xd[4])
check((ad, bd, gd, dd) == (d, b, g, a), 'role swap: M = Pi M^T Pi')
Y = dual_gadget(*Xd); ay, by, gy, dy, ky, _ = twoport(Y[1], Y[0], Y[2], Y[3], Y[4]); MY = (ay, by, gy, dy)
check(MY == (a, g, b, d) and abs(ky) == 1 and len(Y[1]) == 23, 'dual of the role swap: 23 edges, M = M^T, |kappa| = 1')
for name, chain, mats, want in (('X23 o Y', [X, Y], [M, MY], 24189825343), ('(X23 o Y)^2', [X, Y, X, Y], [M, MY, M, MY], 550019993314869718360)):
    P = (1, 0, 0, 1)
    for A in mats: P = mul(P, A)
    q, inv, T, ok = current(chain)
    check(inv == want == P[2] + P[3] == T and ok, '%s: %d edges, 1/|I| = tau = %d = matrix prediction, simple, planar, co-facial' % (name, q, want))
from decimal import Decimal, getcontext
getcontext().prec = 40
tr = sum(v * v for v in M); r1 = (Decimal(a + d) + (Decimal(a + d) ** 2 - 4).sqrt()) / 2; r2 = (Decimal(tr) + (Decimal(tr) ** 2 - 4).sqrt()) / 2
print('rho(M)^(1/22)     =', str(r1 ** (Decimal(1) / 22))[:14])
print('rho(M M^T)^(1/44) =', str(r2 ** (Decimal(1) / 44))[:14], ' (trace', tr, ')')
print('ALL CHECKS PASSED')
