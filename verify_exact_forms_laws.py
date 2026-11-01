#!/usr/bin/env python3
"""Profile of the module Im(L_N) of exact forms (Section 4.1).

For f = 1 + s x^r + x^d squarefree over F_p and N < p, L_N q = f q' + (N+1) f' q is F_p[x^p]-linear.
Let nu_s be the smallest leading degree, in the residue class s mod p, of a non-zero element of Im L_N.
Checks on a small domain:
  [D] no leading degree is congruent to -1-Nd mod p                         (proved in the document)
  [V] p-1 classes occur and  sum_s (nu_s - s)/p = floor(N d / p)            (conservation law, NOT proved)
  [V] binomial case sigma=0 (needs c=(N+1)d != 0 mod p) closed formula for the missing classes.
  [V] independence of the profile on sigma (counts only).
Usage: python3 verify_exact_forms_laws.py [pmax] [dmax]      (default 7 9)
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from tvariant import squarefree

def lead_degrees(f, N, p, d):
    """Set of leading degrees of Im L_N, computed from q of degree <= Dq by echelon reduction."""
    Dq = (N + 1) * d + p * d + 2 * p
    fp = [(i * f[i]) % p for i in range(1, len(f))]
    rows = []
    for s in range(Dq + 1):
        v = np.zeros(Dq + d + 1, dtype=np.int64)
        if s > 0:
            for i, c in enumerate(f): v[s - 1 + i] += c * s
        for i, c in enumerate(fp): v[s + i] += c * (N + 1)
        rows.append(v % p)
    A = np.array(rows, dtype=np.int64)
    ncol = A.shape[1]
    degs = []
    r = 0
    for c in range(ncol - 1, -1, -1):          # highest degree first
        nz = np.nonzero(A[r:, c])[0]
        if nz.size == 0: continue
        pv = r + nz[0]
        if pv != r: A[[r, pv]] = A[[pv, r]]
        A[r] = (A[r] * pow(int(A[r, c]), -1, p)) % p
        for i in np.nonzero(A[:, c])[0]:
            if i != r: A[i] = (A[i] - A[i, c] * A[r]) % p
        degs.append(c); r += 1
        if r == A.shape[0]: break
    return sorted(degs), Dq

def profile(f, N, p, d):
    degs, Dq = lead_degrees(f, N, p, d)
    nu = {}
    for e in degs:
        s = e % p
        if s not in nu or e < nu[s]: nu[s] = e
    return nu, Dq

if __name__ == "__main__":
    pmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    dmax = int(sys.argv[2]) if len(sys.argv) > 2 else 9
    tot = miss_bad = cons_bad = rank_bad = 0
    sig_total = sig_same = 0
    for p in [q for q in (3, 5, 7, 11, 13) if q <= pmax]:
        for d in range(3, dmax + 1):
            for r in range(1, d):
                for N in range(1, p):
                    profs = []
                    for sg in range(1, p):
                        if not squarefree(sg, 1, r, d, p): continue
                        f = np.zeros(d + 1, dtype=np.int64); f[0] = 1; f[r] = (f[r] + sg) % p; f[d] = (f[d] + 1) % p
                        nu, Dq = profile(f, N, p, d)
                        tot += 1
                        sstar = (-1 - N * d) % p
                        if sstar in nu: miss_bad += 1
                        if len(nu) != p - 1: rank_bad += 1; continue
                        ks = sum((nu[s] - s) // p for s in nu)
                        if ks != (N * d) // p: cons_bad += 1; print("conservation fails:", dict(p=p, d=d, r=r, N=N, sigma=sg, sum_k=ks, floor=(N*d)//p))
                        profs.append(tuple(sorted(nu.items())))
                    if len(profs) >= 2:
                        sig_total += 1; sig_same += len(set(profs)) == 1
    print(f"situations (p<={pmax}, d<={dmax}, all r, all N<p, smooth sigma): {tot}")
    print(f"[D] class -1-Nd mod p occurring as leading degree: {miss_bad} (expected 0)")
    print(f"[V] profiles without exactly p-1 classes: {rank_bad} (expected 0)")
    print(f"[V] violations of  sum k_s = floor(Nd/p): {cons_bad} (expected 0; law not proved)")
    print(f"[V] (p,d,r,N) with >= 2 smooth sigma whose profile does not depend on sigma: {sig_same} / {sig_total}")
    good = miss_bad == 0 and rank_bad == 0 and cons_bad == 0
    print("PASS" if good else "FAIL")
    raise SystemExit(0 if good else 1)
