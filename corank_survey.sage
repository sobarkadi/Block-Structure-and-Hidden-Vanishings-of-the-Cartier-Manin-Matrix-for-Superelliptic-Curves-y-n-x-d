# -*- coding: utf-8 -*-
# corank_survey.sage -- survey of the corank of hidden vanishings (2-cycles p^2=1 mod n, p != +-1 mod n)
# Usage: sage corank_survey.sage [PMAX NMAX DMAX GMAX]     (default 31 40 30 12 ; e.g. 47 60 40 16 = longer run)
# Writes corank_survey.csv (columns: n,p,d,r,k0,g0,g1,N0,N1,corank,pur) -- send me the CSV.
# The corank is g0 - (max rank of Phi over the squarefree sigma) ; "pur" = blocks of full rank
# and perfect matching of the support (hence a hidden vanishing). Status: exact computation, not a proof.
from fractions import Fraction
import sys, random, itertools
from math import factorial, gcd, comb
from collections import deque

try:
    from sage.all import GF, matrix, PolynomialRing
    HAVE_SAGE = True
except Exception:
    HAVE_SAGE = False

# ---------------------------------------------------------------- utilities
def inv(a, m):
    return pow(int(a) % int(m), -1, int(m))

CB_MAX = 20000   # bound on C(g1,g0) for Cauchy-Binet

def Nof(n, p, k):
    s = (k * inv(p, n)) % n
    return (s * p - k) // n

def pmul_list(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    r[i + j] = (r[i + j] + x * y) % p
    return r

def fpow(f, N, p):
    res = [1]; base = f[:]
    while N:
        if N & 1: res = pmul_list(res, base, p)
        N >>= 1
        if N: base = pmul_list(base, base, p)
    return res

def rank_mod(M, p):
    if not M or not M[0]: return 0
    if HAVE_SAGE:
        try:
            return int(matrix(GF(p), M).rank())
        except Exception:
            pass
    M = [r[:] for r in M]; rk = 0
    for c in range(len(M[0])):
        pr = None
        for i in range(rk, len(M)):
            if M[i][c] % p: pr = i; break
        if pr is None: continue
        M[rk], M[pr] = M[pr], M[rk]
        iv = inv(M[rk][c], p); M[rk] = [x * iv % p for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c] % p:
                f = M[i][c]; M[i] = [(x - f * y) % p for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk

def matmul(A, B, p):
    return [[sum(a * b for a, b in zip(row, col)) % p for col in zip(*B)] for row in A]

def stab_rank(Phi, p):
    g = len(Phi); P = Phi; last = rank_mod(P, p)
    for _ in range(g):
        P = matmul(P, Phi, p); r = rank_mod(P, p)
        if r == last: break
        last = r
    return last

def polygcd(a, b, p):
    def trim(x):
        while x and x[-1] % p == 0: x = x[:-1]
        return x
    a = trim([c % p for c in a]); b = trim([c % p for c in b])
    while b:
        iv = inv(b[-1], p)
        while len(a) >= len(b) and a:
            f = a[-1] * iv % p; sh = len(a) - len(b)
            for i, c in enumerate(b): a[sh + i] = (a[sh + i] - f * c) % p
            a = trim(a)
        a, b = b, a
    return a

def squarefree(f, p):
    df = [(i * c) % p for i, c in enumerate(f)][1:]
    return len(polygcd(f, df, p)) <= 1

# polynomials in s (dict exponent -> coefficient)
def padd(A, B, p, sg=1):
    R = dict(A)
    for e, c in B.items(): R[e] = (R.get(e, 0) + sg * c) % p
    return {e: c for e, c in R.items() if c}

def pmul(A, B, p):
    R = {}
    for a, x in A.items():
        for b, y in B.items(): R[a + b] = (R.get(a + b, 0) + x * y) % p
    return {e: c for e, c in R.items() if c}

def pmm(A, B, p):
    n = len(A); m = len(B[0]); k = len(B)
    C = [[{} for _ in range(m)] for _ in range(n)]
    for i in range(n):
        for j in range(m):
            t = {}
            for l in range(k):
                if A[i][l] and B[l][j]: t = padd(t, pmul(A[i][l], B[l][j], p), p)
            C[i][j] = t
    return C

def pdet(M, p):
    n = len(M); memo = {}
    def F(mask):
        if mask == (1 << n) - 1: return {0: 1}
        if mask in memo: return memo[mask]
        r = bin(mask).count('1'); tot = {}
        for i in range(n):
            if (mask >> i) & 1 or not M[r][i]: continue
            sub = F(mask | (1 << i))
            if not sub: continue
            sg = -1 if bin(mask >> (i + 1)).count('1') % 2 else 1
            tot = padd(tot, pmul(M[r][i], sub, p), p, sg)
        memo[mask] = tot; return tot
    return F(0)

def pdivisible_by_fermat(D, p):
    # D divisible by s^(p-1)-1 ? reduction s^(p-1) -> 1
    R = {}
    for e, c in D.items(): R[e % (p - 1)] = (R.get(e % (p - 1), 0) + c) % p
    return all(c == 0 for c in R.values())

def nullity(rows, ncol, p):
    return ncol - rank_mod(rows, p) if rows else ncol

# --------------------------------------------------- symbolic blocks (in s)
def blockpoly(N, d, r, p, rows, cols):
    M = [[{} for _ in cols] for _ in rows]
    for v in range(N + 1):
        for u in range(N + 1 - v):
            e = d * u + r * v
            c = (factorial(N) // (factorial(u) * factorial(v) * factorial(N - u - v))) % p
            if c == 0: continue
            for ri, b in enumerate(rows):
                for ci, j in enumerate(cols):
                    if p * b - j == e: M[ri][ci][v] = (M[ri][ci].get(v, 0) + c) % p
    return M

def evalblock(Mp, s, p):
    return [[sum(c * pow(s, e, p) for e, c in ent.items()) % p for ent in row] for row in Mp]

# ------------------------------------------------------------ Menger flow
def sumset(E, N):
    cur = {0}
    for _ in range(N): cur = cur | {x + e for x in cur for e in E}
    return cur

def supports_from_E(E, N0, N1, p, g0, g1):
    s1 = sumset(E, N1); s0 = sumset(E, N0)
    S1 = {(a - 1, b - 1) for a in range(1, g0 + 1) for b in range(1, g1 + 1) if p * a - b in s1}
    S0 = {(b - 1, i - 1) for b in range(1, g1 + 1) for i in range(1, g0 + 1) if p * b - i in s0}
    return S1, S0

def matchsize(adj, nc):
    mt = [-1] * nc
    def tr(u, seen):
        for v in adj[u]:
            if v in seen: continue
            seen.add(v)
            if mt[v] < 0 or tr(mt[v], seen): mt[v] = u; return True
        return False
    return sum(tr(u, set()) for u in range(len(adj)))

def maxflow(g0, g1, S1, S0):
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

def stages(g0, g1, S1, S0):
    R0 = {b for (b, i) in S0}; C1 = {b for (a, b) in S1}
    Bs = sorted(R0 & C1)
    adj1 = [[bi for bi, b in enumerate(Bs) if (a, b) in S1] for a in range(g0)]
    adj2 = [[bi for bi, b in enumerate(Bs) if (b, i) in S0] for i in range(g0)]
    return len(Bs), matchsize(adj1, len(Bs)), matchsize(adj2, len(Bs))

# ------------------------------------------- closed criterion for d = p (theorem)
def critere_dp(n, p, r, k0, k1):
    g0 = k0 * p // n; g1 = k1 * p // n
    c = lambda v: -((-r * v) // p)
    w = lambda v: v - c(v)
    beta = lambda v: p * c(v) - r * v
    rinv = inv(r, p)
    VI = [(-i * rinv) % p for i in range(1, g0 + 1)]
    if any(v < 1 or v > g1 for v in VI): return False, 'column i empty'
    vm = min(VI); J = lambda v: (c(v), g1 - w(v)); lo, hi = J(vm)
    Bs = [beta(v) for v in range(1, g0 + 1) if 1 <= beta(v) <= g1 and lo <= beta(v) <= hi]
    if len(Bs) != g0: return False, '|B*|<g0'
    for v0 in VI:
        l, h = J(v0); cnt = sum(1 for b in Bs if l <= b <= h)
        if sum(1 for v in VI if v >= v0) > cnt: return False, 'Hall stage 2'
    return True, 'ok'

# =============================================================== analysis of one case
def analyse(n, p, d, r, k0, nb_s4=4, leger=False, gmax_det=8):
    n, p, d, r, k0 = int(n), int(p), int(d), int(r), int(k0)
    out = {}
    k1 = (k0 * inv(p, n)) % n
    if k1 == 0 or k1 == k0 or (k1 * inv(p, n)) % n != k0:
        return {'label': "not a 2-cycle (k0,k1)", 'cas': (n, p, d, r, k0)}
    g0 = k0 * d // n; g1 = k1 * d // n
    N0 = Nof(n, p, k0); N1 = Nof(n, p, k1)
    out.update(cas=(n, p, d, r, k0, k1), g0=g0, g1=g1, N0=N0, N1=N1)
    if g0 == 0 or g1 == 0: out['label'] = 'empty block'; return out
    # [2] ranks over F_p^*
    rkM0 = rkM1 = rkPhi = -1; defs = 0; tested = 0; stab = []
    for s in range(1, p):
        f = [0] * (d + 1); f[0] += 1; f[d] += 1; f[r] += s
        if not squarefree(f, p): continue
        tested += 1
        c0 = fpow(f, N0, p); c1 = fpow(f, N1, p)
        M0 = [[c0[p * b - i] if 0 <= p * b - i < len(c0) else 0 for i in range(1, g0 + 1)] for b in range(1, g1 + 1)]
        M1 = [[c1[p * a - b] if 0 <= p * a - b < len(c1) else 0 for b in range(1, g1 + 1)] for a in range(1, g0 + 1)]
        Phi = matmul(M1, M0, p)
        rkM0 = max(rkM0, rank_mod(M0, p)); rkM1 = max(rkM1, rank_mod(M1, p))
        rP = rank_mod(Phi, p); rkPhi = max(rkPhi, rP)
        if rP < g0: defs += 1
        stab.append(stab_rank(Phi, p))
    out.update(sigma_testes=tested, rank_M0=rkM0, rank_M1=rkM1, rank_Phi_max=rkPhi,
               sigma_deficients=defs, p_rank_cycle_min_max=(min(stab), max(stab)) if stab else None)
    if leger and tested and defs == 0:
        out['label'] = 'not deficient'; return out
    # [3] supports / flow
    E = [0, r, d]
    S1, S0 = supports_from_E(E, N0, N1, p, g0, g1)
    phi = {(a, i) for (a, b) in S1 for (b2, i) in S0 if b == b2}
    nuPhi = matchsize([[i for i in range(g0) if (a, i) in phi] for a in range(g0)], g0)
    Delta = maxflow(g0, g1, S1, S0)
    nB, m1, m2 = stages(g0, g1, S1, S0)
    out.update(nu_Phi=nuPhi, flow_Delta=Delta, B_star=nB, stage1=m1, stage2=m2)
    # [4] exact det
    if leger and (g0 > gmax_det or rkM0 < g0 or rkM1 < g0 or nuPhi < g0 or Delta < g0):
        out['det_Phi_zero'] = None if g0 > gmax_det else (Delta < g0)
        out['label'] = ('deficient block (M0 or M1 of rank < g0)' if (rkM0 < g0 or rkM1 < g0) else
                            'support (nu(Phi) < g0)' if nuPhi < g0 else
                            'Menger (flow < g0)' if Delta < g0 else 'formal/Fermat undecided (g0 too large)')
        out['menger_theorem_checked'] = True
        return out
    M0p = blockpoly(N0, d, r, p, range(1, g1 + 1), range(1, g0 + 1))
    M1p = blockpoly(N1, d, r, p, range(1, g0 + 1), range(1, g1 + 1))
    Phip = pmm(M1p, M0p, p)
    D = pdet(Phip, p)
    out['det_Phi_zero'] = (len(D) == 0)
    if D:
        out['det_Phi_divisible_par_s^(p-1)-1'] = pdivisible_by_fermat(D, p)
        out['det_Phi_terms'] = sorted(D.items())[:6]
    if HAVE_SAGE and g0 <= 12 and not leger:
        try:
            R = PolynomialRing(GF(p), 's'); sg = R.gen()
            Mx = matrix(R, g0, g0, [sum(c * sg ** e for e, c in Phip[a][i].items()) for a in range(g0) for i in range(g0)])
            out['det_Phi_zero_sage'] = (Mx.det() == 0)
        except Exception as ex:
            out['det_Phi_zero_sage'] = 'error: %s' % ex
    # [5] Cauchy-Binet (full mode only)
    cb = None
    if not leger:
        if comb(g1, g0) > CB_MAX:
            out['CauchyBinet'] = 'SKIPPED (C(g1,g0)=%d > %d): minors not tested' % (comb(g1, g0), CB_MAX)
        else:
            npass = nz = 0; zeroA = zeroB = 0
            for S in itertools.combinations(range(g1), g0):
                adjA = [[j for j in range(g0) if (a, S[j]) in S1] for a in range(g0)]
                adjB = [[j for j in range(g0) if (S[b], j) in S0] for b in range(g0)]
                if matchsize(adjA, g0) < g0 or matchsize(adjB, g0) < g0: continue
                npass += 1
                A = pdet([[M1p[a][b] for b in S] for a in range(g0)], p)
                B = pdet(M0p_rows(M0p, S), p)
                if not A: zeroA += 1
                if not B: zeroB += 1
                if A and B: nz += 1
            cb = dict(S_admissibles=npass, A_S_zero=zeroA, B_S_zero=zeroB, nonzero_products=nz)
            out['CauchyBinet'] = cb
        # [6] common kernel of the layers
        lay = {}
        for a in range(g0):
            for i in range(g0):
                for e, c in Phip[a][i].items():
                    lay.setdefault(e, [[0] * g0 for _ in range(g0)])[a][i] = c
        rowsR = [row for L in lay.values() for row in L]
        rowsL = [list(col) for L in lay.values() for col in zip(*L)]
        out['common_layer_kernel(right,left)'] = (nullity(rowsR, g0, p), nullity(rowsL, g0, p))
        # [7] fourth term
        t4 = []
        rnd = random.Random(int(1))
        cand = [s for s in range(1, d) if s != r]
        for s4 in rnd.sample(cand, min(nb_s4, len(cand))):
            E4 = [0, r, s4, d]
            T1, T0 = supports_from_E(E4, N0, N1, p, g0, g1)
            fl4 = maxflow(g0, g1, T1, T0); best = 0
            for _ in range(5):
                f = [0] * (d + 1)
                for e in E4: f[e] = rnd.randrange(1, p)
                c0 = fpow(f, N0, p); c1 = fpow(f, N1, p)
                M0 = [[c0[p * b - i] if 0 <= p * b - i < len(c0) else 0 for i in range(1, g0 + 1)] for b in range(1, g1 + 1)]
                M1 = [[c1[p * a - b] if 0 <= p * a - b < len(c1) else 0 for b in range(1, g1 + 1)] for a in range(1, g0 + 1)]
                best = max(best, rank_mod(matmul(M1, M0, p), p))
                if best == g0: break
            t4.append((s4, fl4, best))
        out['4e_terme (s,flow,rank_max)'] = t4
    # [8] d = p
    if d == p:
        ok, why = critere_dp(n, p, r, k0, k1)
        out['critere_ferme_d=p'] = (ok, why, 'agrees with flow' if ok == (Delta == g0) else 'MISMATCH')
    # [9] label
    if rkM0 < g0 or rkM1 < g0: lab = 'deficient block (M0 or M1 of rank < g0)'
    elif nuPhi < g0: lab = 'support (nu(Phi) < g0)'
    elif Delta < g0: lab = 'Menger (flow < g0)'
    elif out['det_Phi_zero']:
        if cb is None: lab = 'formal outside Menger (zero minor or cancellation: undecided)'
        elif cb['nonzero_products'] == 0: lab = 'formal outside Menger: ZERO MINOR (every product A_S*B_S is zero)'
        else: lab = 'formal outside Menger: CANCELLATION between nonzero products A_S*B_S'
    elif tested and defs == tested and rkPhi < g0: lab = 'Fermat (det != 0, zero on F_p^*)'
    elif rkPhi < g0: lab = 'deficient for some sigma only'
    else: lab = 'not deficient'
    out['label'] = lab
    out['menger_theorem_checked'] = (not (Delta < g0)) or bool(out['det_Phi_zero'])   # [D]
    return out


def est_premier(m):
    return m > 1 and all(m % q for q in range(2, int(m ** 0.5) + 1))

def survey(pmax=31, nmax=40, dmax=30, gmax=12, pmin=3, fichier='corank_survey.csv'):
    """Survey of the corank of the 'hidden' cases for the 2-cycles p^2=1 mod n, p != +-1 mod n
    (all r from 1 to d-1: the symmetry r <-> d-r is FALSE for y^n). Writes a CSV and a summary."""
    from collections import Counter, defaultdict
    seen = set(); rows_found = []
    for p in range(pmin, pmax + 1):
        if not est_premier(p): continue
        for n in range(3, nmax + 1):
            if n % p == 0 or (p * p) % n != 1 or p % n in (1, n - 1): continue
            for k0 in range(1, n):
                k1 = (k0 * inv(p, n)) % n
                if k1 <= k0: continue
                for d in range(2, dmax + 1):
                    if gcd(d, n) != 1: continue
                    g0 = k0 * d // n; g1 = k1 * d // n
                    if g0 == 0 or g1 == 0 or g0 > gmax: continue
                    N0 = Nof(n, p, k0); N1 = Nof(n, p, k1)
                    for r in range(1, d):
                        key = (p, d, r, Fraction(k0, n))
                        if key in seen: continue
                        seen.add(key)
                        best = -1; rk0 = rk1 = 0; tested = 0
                        for s in range(1, p):
                            f = [0] * (d + 1); f[0] += 1; f[d] += 1; f[r] += s
                            if not squarefree(f, p): continue
                            tested += 1
                            c0 = fpow(f, N0, p); c1 = fpow(f, N1, p)
                            M0 = [[c0[p * b - i] if 0 <= p * b - i < len(c0) else 0 for i in range(1, g0 + 1)] for b in range(1, g1 + 1)]
                            M1 = [[c1[p * a - b] if 0 <= p * a - b < len(c1) else 0 for b in range(1, g1 + 1)] for a in range(1, g0 + 1)]
                            rp = rank_mod(matmul(M1, M0, p), p); best = max(best, rp)
                            rk0 = max(rk0, rank_mod(M0, p)); rk1 = max(rk1, rank_mod(M1, p))
                            if best == g0: break
                        if tested and best < g0:
                            S1, S0 = supports_from_E([0, r, d], N0, N1, p, g0, g1)
                            phi = {(a, i) for (a, b) in S1 for (b2, i) in S0 if b == b2}
                            nu = matchsize([[i for i in range(g0) if (a, i) in phi] for a in range(g0)], g0)
                            pur = int(rk0 == g0 and rk1 == g0 and nu == g0)
                            rows_found.append((n, p, d, r, k0, g0, g1, N0, N1, g0 - best, pur))
    with open(fichier, 'w') as fh:
        fh.write('n,p,d,r,k0,g0,g1,N0,N1,corank,pur\n')
        for l in rows_found: fh.write(','.join(str(int(x)) for x in l) + '\n')
    purs = [l for l in rows_found if l[-1]]
    print('hidden cases: %d  of which pure: %d' % (len(rows_found), len(purs)))
    print('corank among pure:', dict(Counter(l[9] for l in purs)))
    for lab, cond in [('N0+N1 < p', lambda l: l[7] + l[8] < l[1]), ('N0+N1 >= p', lambda l: l[7] + l[8] >= l[1]),
                      ('g0 <= 5', lambda l: l[5] <= 5), ('g0 >= 6', lambda l: l[5] >= 6)]:
        print('  %-12s' % lab, dict(Counter(l[9] for l in purs if cond(l))))
    print('CSV written to', fichier)

if __name__ == '__main__':
    a = [int(x) for x in sys.argv[1:]]
    survey(*a)
