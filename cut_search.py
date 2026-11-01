#!/usr/bin/env python3
"""Search for a rank cut (Prop. prop:cut): minimise rk M1[:,S] + rk M0[S^c,:] over all subsets S of
{1..g1} at a given sigma in F_p.  If the minimum is < g0 the cut explains rk Phi < g0.
Usage: python3 cut_search.py n p d r k0 [sigma]      e.g.  python3 cut_search.py 12 23 13 10 5 2
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from itertools import combinations
from tvariant import phi, rank_mod, coef, setup

def blocks_mod_p(n, p, d, r, k0, sg):
    k1, g0, g1, N0, N1 = setup(n, p, d, r, k0)
    M0 = [[coef(N0, sg, 1, r, d, p * b - i, p) for i in range(1, g0 + 1)] for b in range(1, g1 + 1)]
    M1 = [[coef(N1, sg, 1, r, d, p * a - b, p) for b in range(1, g1 + 1)] for a in range(1, g0 + 1)]
    return M0, M1, g0, g1

def best_cut(M0, M1, g0, g1, p):
    best = (10 ** 9, None)
    idx = list(range(g1))
    for size in range(0, g1 + 1):
        for S in combinations(idx, size):
            Sc = [b for b in idx if b not in S]
            a = rank_mod([[M1[x][b] for b in S] for x in range(g0)], p) if S else 0
            b_ = rank_mod([M0[b][:] for b in Sc], p) if Sc else 0
            if a + b_ < best[0]: best = (a + b_, S)
    return best

def local_cut(M0, M1, g0, g1, p, restarts=60, seed=1):
    """Hill-climbing search for a cut with value < g0 when g1 is too large to enumerate all subsets."""
    import random
    rnd = random.Random(seed); idx = list(range(g1))
    def val(S):
        Sc = [b for b in idx if b not in S]
        a = rank_mod([[M1[x][b] for b in S] for x in range(g0)], p) if S else 0
        c = rank_mod([M0[b][:] for b in Sc], p) if Sc else 0
        return a + c
    best = (10 ** 9, None)
    for _ in range(restarts):
        S = {b for b in idx if rnd.random() < 0.5}; v = val(sorted(S)); improved = True
        while improved:
            improved = False
            for b in idx:
                T = set(S); T ^= {b}; w = val(sorted(T))
                if w < v: S, v, improved = T, w, True
        if v < best[0]: best = (v, sorted(S))
        if best[0] < g0: break
    return best

if __name__ == "__main__":
    n, p, d, r, k0 = map(int, sys.argv[1:6])
    sg = int(sys.argv[6]) if len(sys.argv) > 6 else 2
    M0, M1, g0, g1 = blocks_mod_p(n, p, d, r, k0, sg)
    Phi = [[sum(M1[a][b] * M0[b][i] for b in range(g1)) % p for i in range(g0)] for a in range(g0)]
    val, S = best_cut(M0, M1, g0, g1, p)
    print(f"case {(n,p,d,r,k0)} sigma={sg}: g0={g0} g1={g1} rk M0={rank_mod(M0,p)} rk M1={rank_mod(M1,p)} rk Phi={rank_mod(Phi,p)}")
    print(f"best cut value = {val} with S (0-based columns of M1 / rows of M0) = {list(S) if S is not None else None}")
    print("cut explains the deficiency" if val < g0 else "no cut with value < g0")
