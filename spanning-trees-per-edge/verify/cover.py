"""Universal-cover quantities of a finite multigraph (edge list on vertices 0..n-1, loopless, minimum degree >= 2).

solve(n, edges)      -> degrees, x_v, r_e, hitting probabilities h (fixed point of
                        h_{u->v} = 1/(d_u - sum of h_{w->u} over the other darts into u), iterated from 0)
phi_closed(n, edges) -> sum_e log(1+r_e) - sum_v log x_v                      (the closed formula of the paper)
phi_integral(n, edges) -> sum_v [log d_v - int_0^1 (G_v(z)-1)/z dz]           (definition; Gauss-Legendre quadrature,
                        with the return generating function G_v(z) computed from first-passage generating functions)
The two functions use different code paths."""
import math
import numpy as np


def solve(n, edges, iters=200000, tol=1e-15):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1; deg[v] += 1
    D = 2 * len(edges)                               # dart 2i: u->v, dart 2i+1: v->u
    tail = [0] * D; head = [0] * D
    for i, (u, v) in enumerate(edges):
        tail[2 * i], head[2 * i], tail[2 * i + 1], head[2 * i + 1] = u, v, v, u
    h = np.zeros(D)
    for _ in range(iters):
        tot = np.zeros(n)
        for j in range(D): tot[head[j]] += h[j]
        new = np.empty(D)
        for j in range(D):
            u = tail[j]; new[j] = 1.0 / (deg[u] - (tot[u] - h[j ^ 1]))
        if np.max(np.abs(new - h)) < tol:
            h = new; break
        h = new
    tot = np.zeros(n)
    for j in range(D): tot[head[j]] += h[j]
    x = 1.0 / (np.array(deg, float) - tot)
    q = np.array([h[2 * i] * h[2 * i + 1] for i in range(len(edges))]); r = q / (1 - q)
    return deg, x, r, h


def phi_closed(n, edges):
    deg, x, r, h = solve(n, edges)
    return sum(math.log1p(t) for t in r) - sum(math.log(t) for t in x)


def phi_integral(n, edges, nodes=240, iters=4000):
    m = len(edges); deg = [0] * n; darts = []
    for u, v in edges:
        deg[u] += 1; deg[v] += 1; darts.append((u, v)); darts.append((v, u))
    out = [[] for _ in range(n)]
    for j, (u, v) in enumerate(darts): out[u].append(j)
    D = len(darts)
    dd = np.array([deg[t] * deg[hd] for t, hd in darts], float)
    C = np.zeros((D, D))
    for j in range(D):
        for k in out[darts[j][1]]:
            if k != (j ^ 1): C[j, k] = 1
    O = np.zeros((n, D))
    for v in range(n):
        for k in out[v]: O[v, k] = 1
    xs, ws = np.polynomial.legendre.leggauss(nodes); xs = (xs + 1) / 2; ws = ws / 2
    integ = np.zeros(n)
    for z, w in zip(xs, ws):
        F = np.zeros(D)                              # excursion generating functions per dart
        for _ in range(iters):
            Fn = (z * z / dd) / (1 - C @ F)
            if np.max(np.abs(Fn - F)) < 1e-14: F = Fn; break
            F = Fn
        G = 1 / (1 - O @ F)
        integ += w * (G - 1) / z
    return sum(math.log(d) for d in deg) - integ.sum()
