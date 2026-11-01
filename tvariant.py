#!/usr/bin/env python3
"""t-variant sweep: y^n = x^d + sigma x^r + t over F_p.

For every case (n,p,d,r,k0) of a 2-cycle with gcd(d,p-1)>1 whose rank Phi < g0
for ALL smooth sigma at t=1, compute rank Phi(sigma,t) for all (sigma,t) in
(F_p^*)^2 with f squarefree, and split by whether t is a d-th power in F_p
(then sigma' = sigma*lambda^(r-d) lies in F_p) or not (sigma' outside F_p).
Phi = M1*M0 is the honest Cartier-Manin product of the F_p-curve.
Usage: python3 tvariant.py [pmax] [gmax]      (defaults 31 12 = the domain of the document, about 40 s)
This file is also the common library (coef, phi, rank_mod, squarefree, has_perfect_matching, ...) of the other scripts.
"""
import sys
from math import factorial as F, gcd

def coef(N, sg, t, r, d, e, p, mod=None):
    mod = mod or p
    s = 0
    for v in range(N + 1):
        for w in range(N + 1 - v):
            if r * v + d * w == e:
                u = N - v - w
                s += F(N) // (F(u) * F(v) * F(w)) * pow(sg, v, mod) * pow(t, u, mod)
    return s % mod

def rank_mod(A, p):
    A = [x[:] for x in A]; rk = 0
    if not A: return 0
    for c in range(len(A[0])):
        pv = next((i for i in range(rk, len(A)) if A[i][c] % p), None)
        if pv is None: continue
        A[rk], A[pv] = A[pv], A[rk]; iv = pow(A[rk][c], -1, p)
        A[rk] = [x * iv % p for x in A[rk]]
        for i in range(len(A)):
            if i != rk and A[i][c] % p:
                f = A[i][c]; A[i] = [(x - f * y) % p for x, y in zip(A[i], A[rk])]
        rk += 1
    return rk

def padd(a, b, p):
    n = max(len(a), len(b)); return [((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % p for i in range(n)]
def trim(a):
    while a and a[-1] == 0: a.pop()
    return a
def pmod(a, b, p):
    a = a[:]; ib = pow(b[-1], -1, p)
    while len(trim(a)) >= len(b):
        c = a[-1] * ib % p; s = len(a) - len(b)
        for i, x in enumerate(b): a[s + i] = (a[s + i] - c * x) % p
    return a
def pgcd(a, b, p):
    a = trim(a[:]); b = trim(b[:])
    while b: a, b = b, pmod(a, b, p)
    return a
def squarefree(sg, t, r, d, p):
    f = [0] * (d + 1); f[0] = t % p; f[r] = (f[r] + sg) % p; f[d] = (f[d] + 1) % p
    fp = trim([(i * f[i]) % p for i in range(1, d + 1)])
    if not fp: return False
    return len(pgcd(f, fp, p)) == 1

def setup(n, p, d, r, k0):
    k1 = k0 * pow(p, -1, n) % n
    return k1, k0 * d // n, k1 * d // n, (k1 * p - k0) // n, (k0 * p - k1) // n

def phi(n, p, d, r, k0, sg, t, mod=None):
    mod = mod or p
    k1, g0, g1, N0, N1 = setup(n, p, d, r, k0)
    M0 = [[coef(N0, sg, t, r, d, p * b - i, p, mod) for i in range(1, g0 + 1)] for b in range(1, g1 + 1)]
    M1 = [[coef(N1, sg, t, r, d, p * a - b, p, mod) for b in range(1, g1 + 1)] for a in range(1, g0 + 1)]
    P = [[sum(M1[a][b] * M0[b][i] for b in range(g1)) % mod for i in range(g0)] for a in range(g0)]
    return P, g0

def has_perfect_matching(S, g):
    """S: set of (a,i) support pairs; Kuhn bipartite matching."""
    adj = {a: [i for (b, i) in S if b == a] for a in range(g)}
    match = {}
    def tr(a, seen):
        for i in adj[a]:
            if i in seen: continue
            seen.add(i)
            if i not in match or tr(match[i], seen):
                match[i] = a; return True
        return False
    return all(tr(a, set()) for a in range(g))

BIG = 2**61 - 1
def z_identical(n, p, d, r, k0, g0):
    """det Phi == 0 identically in Z[sigma]? (random sigma modulo 2^61-1; probabilistic)"""
    import random
    sg = random.randrange(2, BIG)
    P, _ = phi(n, p, d, r, k0, sg, 1, BIG)
    return rank_mod(P, BIG) < g0

def isprime(m): return m > 1 and all(m % q for q in range(2, int(m ** .5) + 1))

if __name__ == "__main__":
    pmax = int(sys.argv[1]) if len(sys.argv) > 1 else 31
    gmax = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    total = 0
    tally = {}
    for p in [q for q in range(5, pmax + 1) if isprime(q)]:
        for n in range(3, 13):
            if p % n == 0 or p % n == 1 or (p * p - 1) % n: continue
            for d in range(3, 26):
                if gcd(d, n) != 1 or gcd(d, p - 1) == 1: continue
                for r in range(1, d):
                    for k0 in range(1, n):
                        k1 = k0 * pow(p, -1, n) % n
                        if k1 <= k0: continue
                        g0 = k0 * d // n
                        if not (2 <= g0 <= gmax): continue
                        sm = [s for s in range(1, p) if squarefree(s, 1, r, d, p)]
                        if not sm: continue
                        if any(rank_mod(phi(n, p, d, r, k0, s, 1)[0], p) == g0 for s in sm): continue
                        # deficient for all smooth sigma at t=1: keep only HIDDEN cases
                        supp = set()
                        for s_ in sm:
                            P_, _ = phi(n, p, d, r, k0, s_, 1)
                            supp |= {(a, i) for a in range(g0) for i in range(g0) if P_[a][i]}
                        if not has_perfect_matching(supp, g0): continue
                        dp = set(pow(x, gcd(d, p - 1), p) for x in range(1, p))  # (F_p^*)^g
                        res = {"dth": [], "nondth": []}
                        for t in range(1, p):
                            key = "dth" if t in dp else "nondth"
                            for s in range(1, p):
                                if squarefree(s, t, r, d, p):
                                    res[key].append(g0 - rank_mod(phi(n, p, d, r, k0, s, t)[0], p))
                        total += 1
                        zid = z_identical(n, p, d, r, k0, g0)
                        tally_key = ("Z-identical" if zid else "mod-p only",)
                        dth_ok = all(x > 0 for x in res["dth"]); nd_ok = all(x > 0 for x in res["nondth"]) if res["nondth"] else None
                        tally.setdefault(tally_key, []).append((dth_ok, nd_ok))
                        def summ(l): return "none" if not l else f"corank min/max {min(l)}/{max(l)} (all>0: {all(x>0 for x in l)}, n={len(l)})"
                        print((n, p, d, r, k0), "Zident" if zid else "modp-only", "g0", g0, "gcd(d,p-1)", gcd(d, p - 1),
                              "| t d-th power:", summ(res["dth"]), "| t not d-th power:", summ(res["nondth"]))
    print("hidden cases with gcd(d,p-1)>1:", total)
    for key, lst in sorted(tally.items()):
        print("%-12s cases=%d | deficient for all (sigma,t), t a d-th power: %d | t not a d-th power: %d (lose the deficiency: %d)" % (
            key[0], len(lst), sum(1 for a, b in lst if a), sum(1 for a, b in lst if b is not False),
            sum(1 for a, b in lst if b is False)))
