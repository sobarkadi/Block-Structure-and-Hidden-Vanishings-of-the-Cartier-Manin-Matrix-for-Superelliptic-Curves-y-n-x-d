#!/usr/bin/env python3
"""Census of hidden vanishings with det Phi == 0 identically in Z[sigma] (Section 4.1).

Domain: primes p <= PMAX, 3 <= n <= NMAX with p^2 = 1 mod n, p != 1 mod n, 3 <= d <= DMAX,
gcd(d,n)=1, all 1 <= r < d, 2 <= g0 <= GMAX, pairs (k0,k1) with k1 > k0.
A case is kept if (i) det Phi vanishes at a random sigma modulo 2^61-1 (probabilistic test of an
identity in Z[sigma]) and (ii) the support of Phi (non-zero entries at that sigma) has a perfect matching and (iii) the Menger flow of the
3-layer support graph a -> b -> i equals g0 (so the vanishing is NOT explained by Menger's theorem).
Cases are deduplicated by (p,d,r,k0/n).  Each kept case is labelled at the first smooth sigma in F_p:
  'deficient block' (rk M0 or rk M1 < g0; the finer split into twin columns of M0, twin rows of M1 or a
  three-column relation is done in the document), 'cut' (both blocks of full rank, a rank cut < g0 is found:
  exhaustive if g1 <= 14, hill-climbing otherwise), 'other' (no cut found: arithmetic cancellation).
The document's census used  PMAX=31, NMAX=12, DMAX=25, GMAX=12 : this script reproduces its 27 distinct cases
(11 deficient-block, 13 cut, 3 other) in about 10 s.
Usage: python3 census_exact_zero.py [PMAX NMAX DMAX GMAX]      default 31 12 25 12
"""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
from math import gcd
from collections import deque
from tvariant import phi, rank_mod, has_perfect_matching, isprime, squarefree, BIG
from cut_search import blocks_mod_p, best_cut, local_cut
from tvariant import coef, setup

def blocks_mod_p_big(n, p, d, r, k0, sg):
    k1, g0, g1, N0, N1 = setup(n, p, d, r, k0)
    M0 = [[coef(N0, sg, 1, r, d, p * b - i, p, BIG) for i in range(1, g0 + 1)] for b in range(1, g1 + 1)]
    M1 = [[coef(N1, sg, 1, r, d, p * a - b, p, BIG) for b in range(1, g1 + 1)] for a in range(1, g0 + 1)]
    return M0, M1, g0, g1

def menger_flow(g0, g1, S1, S0):
    """Maximum number of vertex-disjoint paths a -> b -> i (unit vertex capacities)."""
    cap = {}
    def add(u, v):
        cap.setdefault(u, {}); cap.setdefault(v, {})
        cap[u][v] = cap[u].get(v, 0) + 1; cap[v].setdefault(u, 0)
    s, t = 's', 't'
    for a in range(g0): add(s, ('Ai', a)); add(('Ai', a), ('Ao', a))
    for i in range(g0): add(('Io', i), t); add(('Ii', i), ('Io', i))
    for b in range(g1): add(('Bi', b), ('Bo', b))
    for a, b in S1: add(('Ao', a), ('Bi', b))
    for b, i in S0: add(('Bo', b), ('Ii', i))
    fl = 0
    while True:
        par = {s: None}; q = deque([s])
        while q and t not in par:
            u = q.popleft()
            for v, c in cap[u].items():
                if c > 0 and v not in par: par[v] = u; q.append(v)
        if t not in par: break
        v = t
        while par[v] is not None:
            u = par[v]; cap[u][v] -= 1; cap[v][u] += 1; v = u
        fl += 1
    return fl

def main(pmax=31, nmax=12, dmax=25, gmax=12):
    random.seed(11)
    seen = {}
    for p in [q for q in range(3, pmax + 1) if isprime(q)]:
        for n in range(3, nmax + 1):
            if p % n == 0 or p % n == 1 or (p * p - 1) % n: continue
            for d in range(3, dmax + 1):
                if gcd(d, n) != 1: continue
                for r in range(1, d):
                    for k0 in range(1, n):
                        k1 = k0 * pow(p, -1, n) % n
                        if k1 <= k0: continue
                        g0 = k0 * d // n
                        if not (2 <= g0 <= gmax): continue
                        key = (p, d, r, Fraction(k0, n))
                        if key in seen: continue
                        sg = random.randrange(2, BIG)
                        P, _ = phi(n, p, d, r, k0, sg, 1, BIG)
                        if rank_mod(P, BIG) == g0: continue
                        supp = {(a, i) for a in range(g0) for i in range(g0) if P[a][i] % BIG}
                        if not has_perfect_matching(supp, g0): continue
                        # exclude Menger cases: keep only those with flow Delta = g0 (3-layer support graph)
                        M0z, M1z, _, g1z = blocks_mod_p_big(n, p, d, r, k0, sg)
                        S1 = {(a, b) for a in range(g0) for b in range(g1z) if M1z[a][b]}
                        S0 = {(b, i) for b in range(g1z) for i in range(g0) if M0z[b][i]}
                        if menger_flow(g0, g1z, S1, S0) < g0: continue
                        # mechanism at a smooth sigma in F_p
                        sm = [s for s in range(2, p) if squarefree(s, 1, r, d, p)]
                        label = 'other'
                        if sm:
                            M0, M1, g0_, g1 = blocks_mod_p(n, p, d, r, k0, sm[0])
                            r0, r1 = rank_mod(M0, p), rank_mod(M1, p)
                            if r0 < g0 or r1 < g0: label = 'deficient block (rk M0=%d, rk M1=%d, g0=%d)' % (r0, r1, g0)
                            else:
                                v, S = best_cut(M0, M1, g0_, g1, p) if g1 <= 14 else local_cut(M0, M1, g0_, g1, p)
                                label = 'cut' if v < g0 else 'other (no cut found: cancellation?)'
                        seen[key] = ((n, p, d, r, k0), g0, label)
    for key, (case, g0, label) in sorted(seen.items(), key=lambda kv: kv[1][0]):
        print(case, 'g0=%d' % g0, label)
    print("distinct cases:", len(seen))

if __name__ == "__main__":
    main(*([int(x) for x in sys.argv[1:5]] or [31, 12, 25, 12]))
