"""Independent numerical cross-check of Theorem 1 (not part of the formal proof).

For small planar multigraphs: build the plane dual from a combinatorial embedding, build networks A and B(e)
exactly as in the paper, compute both optima and the least shared tolerance by linear programming (HiGHS), and
compare with |I_e|/(1+|I_e|) computed in exact rational arithmetic.  Also reports D, N for worked examples.
"""
import itertools, json, sys
from fractions import Fraction
import networkx as nx
import numpy as np
import sympy
from scipy.optimize import linprog


def faces_of(n, edges):
    """Plane embedding of a multigraph (parallel edges allowed, no loops) via networkx on a subdivision.
    Returns face label of each dart (i,0) at src, (i,1) at tgt."""
    H = nx.Graph()
    mid = {}
    for i, (u, v) in enumerate(edges):
        m = ('m', i); mid[i] = m
        H.add_edge(('v', u), m); H.add_edge(m, ('v', v))
    ok, emb = nx.check_planarity(H)
    assert ok
    # rotation at original vertex: order of midpoints around it; dart (i,side) sits at vertex
    # face traversal on H: half-edges; map H-faces to darts of G
    seen = set(); face_of_he = {}
    fid = 0
    for (a, b) in emb.edges():
        if (a, b) in seen:
            continue
        cyc = emb.traverse_face(a, b, mark_half_edges=seen)
        for k in range(len(cyc)):
            face_of_he[(cyc[k], cyc[(k + 1) % len(cyc)])] = fid
        fid += 1
    face = {}
    for i, (u, v) in enumerate(edges):
        # dart (i,0): half-edge from ('v',u) to mid ; dart (i,1): from ('v',v) to mid
        face[(i, 0)] = face_of_he[(('v', u), mid[i])]
        face[(i, 1)] = face_of_he[(('v', v), mid[i])]
    return face, fid


def currents(n, edges, s, t):
    q = len(edges)
    M = sympy.zeros(n + 1, q)
    for i, (u, v) in enumerate(edges):
        M[u, i] += 1; M[v, i] -= 1
    A = M[1:, :]
    L = A * A.T
    D = L.det()
    b = sympy.zeros(n, 1)
    if s != 0: b[s - 1] += 1
    if t != 0: b[t - 1] -= 1
    N = A.T * L.adjugate() * b
    return [Fraction(int(N[i]), int(D)) for i in range(q)], int(D), [int(N[i]) for i in range(q)]


def threshold_lp(n, edges, face, nf, s, t, e, I):
    q = len(edges)
    # reorient primal and dual edges with negative current
    E = []; Fd = []
    for i, (u, v) in enumerate(edges):
        fu, fv = face[(i, 0)], face[(i, 1)]
        if I[i] < 0:
            E.append((v, u)); Fd.append((fv, fu))
        else:
            E.append((u, v)); Fd.append((fu, fv))
    # nodes: vertices 0..n, faces, u_i, v_i
    V = n + 1
    node_face = lambda F: V + F
    node_u = lambda i: V + nf + i
    node_v = lambda i: V + nf + q + i
    NN = V + nf + 2 * q
    arcs = []  # (tail, head, kind, i)
    for i in range(q):
        arcs.append((node_u(i), node_v(i), 'obs', i))
    for i in range(q):
        arcs.append((E[i][0], node_u(i), 'pin', i)); arcs.append((node_v(i), E[i][1], 'pout', i))
    for i in range(q):
        arcs.append((node_face(Fd[i][0]), node_u(i), 'din', i)); arcs.append((node_v(i), node_face(Fd[i][1]), 'dout', i))
    arcs.append((t, s, 'ret', -1))
    m = len(arcs)

    def capcost(version):
        cap = []; cost = []
        for (a, b, k, i) in arcs:
            if version == 'A':
                c = {'obs': 1, 'pin': 1, 'pout': 1, 'din': 0, 'dout': 0, 'ret': 1}[k]
                w = -1 if k == 'ret' else 0
            else:
                c = {'obs': 1, 'pin': 0, 'pout': 0, 'din': 1, 'dout': 1, 'ret': 0}[k]
                w = 1 if (k == 'obs' and i == e) else 0
            cap.append(c); cost.append(w)
        return np.array(cap, float), np.array(cost, float)

    Bal = np.zeros((NN, m))
    for j, (a, b, k, i) in enumerate(arcs):
        Bal[a, j] += 1; Bal[b, j] -= 1
    capA, costA = capcost('A'); capB, costB = capcost('B')
    optA = linprog(costA, A_eq=Bal, b_eq=np.zeros(NN), bounds=list(zip([0] * m, capA)), method='highs').fun
    optB = linprog(costB, A_eq=Bal, b_eq=np.zeros(NN), bounds=list(zip([0] * m, capB)), method='highs').fun
    # joint LP over (xA, xB, eps)
    Z = np.zeros((NN, m))
    Aeq = np.vstack([np.hstack([Bal, Z, np.zeros((NN, 1))]), np.hstack([Z, Bal, np.zeros((NN, 1))])])
    obs = np.zeros((q, 2 * m + 1))
    for i in range(q):
        obs[i, i] = 1; obs[i, m + i] = -1
    Aeq = np.vstack([Aeq, obs]); beq = np.zeros(Aeq.shape[0])
    Aub = np.array([np.concatenate([costA, np.zeros(m), [-1]]), np.concatenate([np.zeros(m), costB, [-1]])])
    bub = np.array([optA, optB])
    c = np.zeros(2 * m + 1); c[-1] = 1
    bounds = list(zip([0] * m, capA)) + list(zip([0] * m, capB)) + [(None, None)]
    res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=bounds, method='highs')
    return optA, optB, res.fun


def run(name, n, edges, all_triples=True):
    face, nf_total = faces_of(n, edges)
    nf = nf_total  # number of faces; face nodes 0..nf-1
    q = len(edges)
    assert (n + 1) - q + nf == 2, 'Euler'
    worst = 0.0; cnt = 0; minpos = None; D0 = None
    for s, t in itertools.permutations(range(n + 1), 2):
        I, D, N = currents(n, edges, s, t); D0 = D
        for e in range(q):
            if I[e] == 0:
                continue
            a = abs(I[e]); pred = a / (1 + a)
            optA, optB, eps = threshold_lp(n, edges, face, nf, s, t, e, I)
            worst = max(worst, abs(eps - float(pred)), abs(optA + 1), abs(optB))
            cnt += 1
            if minpos is None or pred < minpos[0]:
                minpos = (pred, s, t, e, N[e], D)
    return {'graph': name, 'n_vertices': n + 1, 'q': q, 'faces': nf, 'D': D0, 'triples_checked': cnt,
            'max_abs_deviation': worst, 'min_threshold': str(minpos[0]), 'witness_s_t_e': minpos[1:4],
            'witness_N_D': [minpos[4], minpos[5]]}


if __name__ == '__main__':
    out = []
    out.append(run('triangle+pendant', 3, [(0, 1), (1, 2), (2, 0), (0, 3)]))
    out.append(run('K4+parallel edge', 3, [(0, 1), (0, 2), (0, 3), (1, 2), (2, 3), (3, 1), (0, 1)]))
    for k in (2, 3, 4, 5):  # fan: hub 0, path 1..k
        ed = [(0, j) for j in range(1, k + 1)] + [(j, j + 1) for j in range(1, k)]
        out.append(run(f'fan, path of {k} vertices', k, ed))
    out.append(run('octahedron', 5, [(0, 1), (0, 2), (0, 3), (0, 4), (5, 1), (5, 2), (5, 3), (5, 4), (1, 2), (2, 3), (3, 4), (4, 1)]))
    out.append(run('cube', 7, [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4), (0, 4), (1, 5), (2, 6), (3, 7)]))
    for r in out:
        print(json.dumps(r))
