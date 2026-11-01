#!/usr/bin/env python3
"""Check the by-hand proofs of the document (all numbers quoted there).

 1. Example A (8,3,7,2,5): det Phi = -9 sigma^3 over Z; hidden vanishing at sigma=2 over F_3.
 2. Example B (8,3,5,1,5): det Phi = 2 sigma (sigma^2-1) in F_3[sigma].
 3. Mixed case (12,23,13,10,5): the three steps of the hand proof, the perfect matching,
    rank Phi = 4, and the rank bound for M1*D*M0 with random invertible diagonal D.
Usage: python3 verify_hand_proofs.py
"""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
from math import factorial as F
from tvariant import rank_mod, phi, coef

def exact_blocks(n, p, d, r, k0, sg):
    """Blocks over Z at an integer sigma (no reduction)."""
    k1 = k0 * pow(p, -1, n) % n
    g0, g1 = k0 * d // n, k1 * d // n
    N0, N1 = (k1 * p - k0) // n, (k0 * p - k1) // n
    BIG = 10 ** 60
    M0 = [[coef(N0, sg, 1, r, d, p * b - i, p, BIG) for i in range(1, g0 + 1)] for b in range(1, g1 + 1)]
    M1 = [[coef(N1, sg, 1, r, d, p * a - b, p, BIG) for b in range(1, g1 + 1)] for a in range(1, g0 + 1)]
    return M0, M1, g0, g1

def det_frac(A):
    A = [[Fraction(x) for x in row] for row in A]; n = len(A); det = Fraction(1)
    for c in range(n):
        pv = next((i for i in range(c, n) if A[i][c] != 0), None)
        if pv is None: return Fraction(0)
        if pv != c: A[c], A[pv] = A[pv], A[c]; det = -det
        det *= A[c][c]
        for i in range(c + 1, n):
            f = A[i][c] / A[c][c]
            A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return det

def det_phi_int(case, sg):
    M0, M1, g0, g1 = exact_blocks(*case, sg)
    Phi = [[sum(M1[a][b] * M0[b][i] for b in range(g1)) for i in range(g0)] for a in range(g0)]
    return det_frac(Phi)

def poly_from_values(vals):
    """Lagrange interpolation at x=0..m-1 -> integer coefficient list (Fractions)."""
    m = len(vals); coeffs = [Fraction(0)] * m
    for i, y in enumerate(vals):
        num = [Fraction(1)]; den = Fraction(1)
        for j in range(m):
            if j == i: continue
            num = [Fraction(0)] + num  # multiply by x
            for k in range(len(num) - 1): num[k] -= j * num[k + 1]
            den *= (i - j)
        for k in range(len(num)): coeffs[k] += y * num[k] / den
    while coeffs and coeffs[-1] == 0: coeffs.pop()
    return coeffs

ok = True
def check(name, cond):
    global ok
    print(('PASS  ' if cond else 'FAIL  ') + name); ok &= bool(cond)

# ---- Example A
caseA = (8, 3, 7, 2, 5)
valsA = [det_phi_int(caseA, s) for s in range(0, 14)]
pa = poly_from_values(valsA)
check("Example A: det Phi = -9 sigma^3 in Z[sigma]", pa == [0, 0, 0, Fraction(-9)])
P, g0 = phi(*caseA, 2, 1)
check("Example A: rank Phi(sigma=2) < 4 over F_3", rank_mod(P, 3) < g0 == 4)

# ---- Example B
caseB = (8, 3, 5, 1, 5)
valsB = [det_phi_int(caseB, s) for s in range(0, 14)]
pb = poly_from_values(valsB)
cb = [int(c) % 3 for c in pb]
while cb and cb[-1] == 0: cb.pop()
check("Example B: det Phi mod 3 = 2 sigma (sigma^2-1) as a polynomial", cb == [0, 1, 0, 2])
P, g0 = phi(*caseB, 2, 1)
check("Example B: Phi(sigma=2) = [[1,0,1],[1,1,1],[0,1,0]] and rank 2",
      P == [[1, 0, 1], [1, 1, 1], [0, 1, 0]] and rank_mod(P, 3) == 2)

# ---- Mixed case (12,23,13,10,5)
n, p, d, r, k0 = 12, 23, 13, 10, 5
random.seed(7)
for sg in [1, 2, 5, 11, 22]:
    k1 = k0 * pow(p, -1, n) % n
    g0, g1 = k0 * d // n, k1 * d // n
    N0, N1 = (k1 * p - k0) // n, (k0 * p - k1) // n
    M0 = [[coef(N0, sg, 1, r, d, p * b - i, p) for i in range(1, g0 + 1)] for b in range(1, g1 + 1)]
    M1 = [[coef(N1, sg, 1, r, d, p * a - b, p) for b in range(1, g1 + 1)] for a in range(1, g0 + 1)]
    rows123 = [M0[b][:] for b in range(3)]
    check(f"sigma={sg}: rows 1-3 of M0 are supported on columns {{3,4}}",
          all(row[i] == 0 for row in rows123 for i in (0, 1, 4)))
    check(f"sigma={sg}: column 5 of M1 is zero", all(M1[a][4] == 0 for a in range(g0)))
    check(f"sigma={sg}: 13 s^5 c4 + 7 c6 + s^4 c7 = 0 mod 23",
          all((13 * pow(sg, 5, p) * M1[a][3] + 7 * M1[a][5] + pow(sg, 4, p) * M1[a][6]) % p == 0 for a in range(g0)))
    S, Sc = [3, 4, 5, 6], [0, 1, 2]
    rM1 = rank_mod([[M1[a][b] for b in S] for a in range(g0)], p)
    rM0 = rank_mod([M0[b][:] for b in Sc], p)
    check(f"sigma={sg}: rank M1[:,S] <= 2 and rank M0[S^c,:] <= 2", rM1 <= 2 and rM0 <= 2)
    Phi = [[sum(M1[a][b] * M0[b][i] for b in range(g1)) % p for i in range(g0)] for a in range(g0)]
    check(f"sigma={sg}: rank Phi = 4 < 5", rank_mod(Phi, p) == 4)
    for _ in range(5):
        D = [random.randrange(1, p) for _ in range(g1)]
        PhiD = [[sum(M1[a][b] * D[b] * M0[b][i] for b in range(g1)) % p for i in range(g0)] for a in range(g0)]
        if rank_mod(PhiD, p) > 4: check("rank(M1 D M0) <= 4", False)
    paths = [(1, 3, 4), (5, 1, 3), (2, 7, 5), (3, 6, 1), (4, 4, 2)]
    check(f"sigma={sg}: the 5 disjoint paths of the matching use non-zero entries",
          all(M1[a - 1][b - 1] % p and M0[b - 1][i - 1] % p for a, b, i in paths)
          and len({a for a, _, _ in paths}) == 5 and len({b for _, b, _ in paths}) == 5 and len({i for _, _, i in paths}) == 5)
print("ALL PASS" if ok else "SOME CHECK FAILED")
raise SystemExit(0 if ok else 1)
