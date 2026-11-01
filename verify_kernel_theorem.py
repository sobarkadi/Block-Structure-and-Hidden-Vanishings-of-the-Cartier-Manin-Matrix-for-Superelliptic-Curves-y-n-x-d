#!/usr/bin/env python3
"""Numerical check of Theorem (kernel of a block, Th. thm:ker):

    for f squarefree over F_p and N < p, the kernel of the block
        B[b,i] = [x^{pb-i}] f^N   (b >= 1, 1 <= i <= g)
    has dimension  dim { L_N q : deg L_N q < g },   L_N q = f q' + (N+1) f' q.

The image side is computed with q of degree <= Dq = (N+1)d + p d + g (a smaller
Dq gives wrong, too small, kernels: this was an early error of the project).
Usage: python3 verify_kernel_theorem.py [number_of_random_cases] [seed]
"""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from tvariant import squarefree

def rank_np(A, p):
    A = (np.array(A, dtype=np.int64) % p).copy()
    if A.size == 0: return 0
    rk = 0; rows, cols = A.shape
    for c in range(cols):
        nz = np.nonzero(A[rk:, c])[0]
        if nz.size == 0: continue
        pv = rk + nz[0]
        if pv != rk: A[[rk, pv]] = A[[pv, rk]]
        A[rk] = (A[rk] * pow(int(A[rk, c]), -1, p)) % p
        others = np.nonzero(A[:, c])[0]
        for i in others:
            if i != rk: A[i] = (A[i] - A[i, c] * A[rk]) % p
        rk += 1
        if rk == rows: break
    return rk

def polmul(a, b, p):
    return (np.convolve(a, b) % p)

def block_kernel_dim(f, N, g, p, d):
    fN = np.array([1], dtype=np.int64)
    for _ in range(N): fN = polmul(fN, f, p)
    Bmax = (N * d + g) // p + 1
    B = np.zeros((Bmax, g), dtype=np.int64)
    for b in range(1, Bmax + 1):
        for i in range(1, g + 1):
            e = p * b - i
            if 0 <= e < len(fN): B[b - 1, i - 1] = fN[e]
    return g - rank_np(B, p)

def image_dim(f, N, g, p, d):
    Dq = (N + 1) * d + p * d + g
    fp = np.array([(i * f[i]) % p for i in range(1, len(f))], dtype=np.int64)  # f'
    L = np.zeros((Dq + d + 1, Dq + 1), dtype=np.int64)
    for s in range(Dq + 1):
        col = np.zeros(Dq + d + 1, dtype=np.int64)
        if s > 0:
            t = polmul(f, np.array([0] * (s - 1) + [s % p], dtype=np.int64), p)
            col[:len(t)] += t
        t2 = polmul(fp, np.array([0] * s + [(N + 1) % p], dtype=np.int64), p)
        col[:len(t2)] += t2
        L[:, s] = col % p
    dimK = (Dq + 1) - rank_np(L[g:, :], p)
    dimkerL = (Dq + 1) - rank_np(L, p)
    return dimK - dimkerL

if __name__ == "__main__":
    ncases = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    tested = bad = nonzero = 0
    while tested < ncases:
        p = random.choice([3, 5, 7]); d = random.randrange(3, 10); r = random.randrange(1, d)
        sg = random.randrange(1, p); N = random.randrange(1, p); g = random.randrange(1, d)
        if not squarefree(sg, 1, r, d, p): continue
        f = np.zeros(d + 1, dtype=np.int64); f[0] = 1; f[r] = (f[r] + sg) % p; f[d] = (f[d] + 1) % p
        kd = block_kernel_dim(f, N, g, p, d); im = image_dim(f, N, g, p, d)
        tested += 1; nonzero += kd > 0
        if kd != im:
            bad += 1; print("MISMATCH", dict(p=p, d=d, r=r, sigma=sg, N=N, g=g, kernel=kd, image=im))
    print(f"tested {tested} random smooth cases ({nonzero} with non-zero kernel): {bad} mismatches")
    print("PASS" if bad == 0 else "FAIL")
    raise SystemExit(0 if bad == 0 else 1)
