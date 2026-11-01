#!/usr/bin/env python3
"""Check Lemma (recurrence), Corollary (twin columns) and the examples of Section 4.1.

 1. Recurrence  e a_e + s (e-(N+1)r) a_{e-r} + (e-(N+1)d) a_{e-d} = 0  for f^N, exactly over Z.
 2. Examples (a) (d,r,p,k)=(4,1,7,2), n=3 and (b) (8,19,11,3,5): column identities.
 3. The seven single-twin-column cases of the census: which ones satisfy the hypothesis of the
    corollary (expected: 5 of 7), and for those, the predicted column relation holds mod p.
Usage: python3 verify_recurrence_twins.py
"""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tvariant import coef, phi, rank_mod

BIG = 10 ** 90
ok = True
def check(name, cond):
    global ok
    print(('PASS  ' if cond else 'FAIL  ') + name); ok &= bool(cond)

# 1. recurrence over Z
random.seed(3); bad = 0; tot = 0
for _ in range(400):
    d = random.randrange(3, 14); r = random.randrange(1, d); N = random.randrange(1, 12); s = random.randrange(-6, 7)
    a = lambda e: coef(N, s, 1, r, d, e, 10 ** 9, BIG) if e >= 0 else 0
    # coef() reduces mod BIG: s may be negative -> use python ints, so recompute without reduction issues
    e = random.randrange(0, N * d + 2)
    val = e * a(e) + s * (e - (N + 1) * r) * a(e - r) + (e - (N + 1) * d) * a(e - d)
    tot += 1; bad += (val % BIG != 0)
check(f"recurrence holds exactly over Z on {tot} random (d,r,N,sigma,e)", bad == 0)

# 2a. example (a): n=3, d=4, r=1, p=7, k=2 -> N=4
for sg in (2, 3, 5):
    M = [[coef(4, sg, 1, 1, 4, 7 * b - i, 7, BIG) for i in (1, 2)] for b in (1, 2)]
    check(f"example (a), sigma={sg}: M = [[12s^2,12s],[4s,4]], col1 = s*col2, det = 0",
          M == [[12 * sg * sg, 12 * sg], [4 * sg, 4]] and M[0][0] == sg * M[0][1] and M[1][0] == sg * M[1][1]
          and M[0][0] * M[1][1] - M[0][1] * M[1][0] == 0)

# 2b. example (b): (8,19,11,3,5): N=16, c_3 = sigma c_6 exactly over Z
n, p, d, r, k0 = 8, 19, 11, 3, 5
k1 = k0 * pow(p, -1, n) % n; N0 = (k1 * p - k0) // n; g0, g1 = k0 * d // n, k1 * d // n
for sg in (2, 3, 7):
    col = lambda i: [coef(N0, sg, 1, r, d, p * b - i, p, BIG) for b in range(1, g1 + 1)]
    check(f"example (b), sigma={sg}: N={N0}, column 3 = sigma * column 6 exactly over Z",
          N0 == 16 and col(3) == [sg * x for x in col(6)])

# 3. the seven twin cases
cases = [(8, 11, 13, 4, 5), (8, 11, 17, 1, 5), (8, 11, 19, 14, 5), (12, 17, 19, 4, 7),
         (8, 19, 11, 3, 5), (8, 29, 15, 1, 3), (12, 31, 17, 3, 5)]
covered = 0
for (n, p, d, r, k0) in cases:
    k1 = k0 * pow(p, -1, n) % n; N = (k1 * p - k0) // n; g0, g1 = k0 * d // n, k1 * d // n
    i0 = (-(N + 1) * d) % p
    cand = [i for i in range(1, g0 + 1) if i % p == i0 and i + r <= g0 and i % p]
    if not cand:
        print(f"      {(n,p,d,r,k0)}: hypothesis of the corollary NOT satisfied (g0={g0}, i0={i0}); other relation"); continue
    i = cand[0]; covered += 1; good = True
    for sg in (2, 3, 5, 7):
        sg %= p
        col = lambda m: [coef(N, sg, 1, r, d, p * b - m, p) for b in range(1, g1 + 1)]
        ci, cj = col(i), col(i + r)
        fac = (-sg * (i + (N + 1) * r) * pow(i, -1, p)) % p
        good &= all((x - fac * y) % p == 0 for x, y in zip(ci, cj))
    check(f"{(n,p,d,r,k0)}: i={i}: c_i = -s (i+(N+1)r)/i * c_(i+r) mod p, hence rank M0 < g0", good)
check("exactly 5 of the 7 cases are covered by the corollary", covered == 5)
print("ALL PASS" if ok else "SOME CHECK FAILED")
raise SystemExit(0 if ok else 1)
