"""Consistency check (not part of the proof) on random multigraphs of the class C of the paper: connected, loopless,
minimum degree >= 2, no two adjacent vertices of degree 2.  Degree-2 vertices are included.
 (1) the closed formula against the integral definition;   (2) the two identities r_e(1+r_e) = x_u x_v and
 sum_{e at v} r_e = d_v x_v - 1;   (3) the ranges of rbar_v stated in the paper (lemma on ranges);
 (4) E_e <= L for every edge and Phi <= m L,  L = 1/2 log(27/8).
Usage: python3 check_class.py SEED NUMBER_OF_GRAPHS"""
import math, random, sys
from cover import solve, phi_integral
L = 0.5 * math.log(27 / 8)
gp = lambda r: 9 / 16 / (1 + r) + 1 / 16 / r


def sample(rng):
    while True:
        n = rng.randrange(3, 12); m = rng.randrange(n, 3 * n + 1); E = []
        for _ in range(m):
            u, v = rng.randrange(n), rng.randrange(n)
            if u != v: E.append((u, v))
        deg = [0] * n
        for u, v in E: deg[u] += 1; deg[v] += 1
        if min(deg) < 2 or any(deg[u] == 2 and deg[v] == 2 for u, v in E): continue
        adj = {i: set() for i in range(n)}
        for u, v in E: adj[u].add(v); adj[v].add(u)
        seen = {0}; st = [0]
        while st:
            a = st.pop()
            for b in adj[a]:
                if b not in seen: seen.add(b); st.append(b)
        if len(seen) == n: return n, E, deg


if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); N = int(sys.argv[2])
    w = dict(formula=0.0, ident=0.0, rng=-9.0, edge=-9.0, phi=-9.0); with2 = 0
    for _ in range(N):
        n, E, deg = sample(rng); m = len(E)
        _, x, r, h = solve(n, E)
        with2 += 2 in deg
        Phi = sum(math.log1p(t) for t in r) - sum(math.log(t) for t in x)
        w['formula'] = max(w['formula'], abs(Phi - phi_integral(n, E)))
        R = [0.0] * n
        for (u, v), t in zip(E, r):
            w['ident'] = max(w['ident'], abs(t * (1 + t) - x[u] * x[v])); R[u] += t; R[v] += t
        for v in range(n):
            w['ident'] = max(w['ident'], abs(R[v] - (deg[v] * x[v] - 1)))
            w['rng'] = max(w['rng'], R[v] / deg[v] - (1.0 if deg[v] == 2 else 3.0 / deg[v]))
        for (u, v), t in zip(E, r):
            ru, rv = R[u] / deg[u], R[v] / deg[v]
            e = math.log1p(t) - math.log(x[u]) / deg[u] - math.log(x[v]) / deg[v] - gp(ru) * (t - ru) - gp(rv) * (t - rv)
            w['edge'] = max(w['edge'], e - L)
            if deg[u] >= 3 and deg[v] >= 3:
                for d, rb in ((deg[u], ru), (deg[v], rv)):
                    w['rng'] = max(w['rng'], rb - (9 * d - 1) / (d * (3 * d + 1)))
        w['phi'] = max(w['phi'], Phi / m - L)
    print('graphs:', N, ' with a vertex of degree 2:', with2)
    print('max |closed formula - integral|  = %.2e' % w['formula'])
    print('max defect of the identities     = %.2e' % w['ident'])
    print('max (rbar - range bound)         = %.3e   (must be <= 0)' % w['rng'])
    print('max (E_e - L)                    = %.3e   (must be <= 0 up to rounding)' % w['edge'])
    print('max (Phi/m - L)                  = %.3e   (must be <= 0 up to rounding)' % w['phi'])
