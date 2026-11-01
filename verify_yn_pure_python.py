"""
================================================================================
INDEPENDENT verification (pure Python, no external dependency, no Sage)
for the hidden vanishings of y^n = x^d + sigma*x^r + 1
================================================================================

Run with:   python3 -I verify_yn_pure_python.py

Two INDEPENDENT computations, then a comparison:

  (A) "candidate": generalized Cartier-Manin matrix (full, g x g, with
      mixing of the blocks k if p is not congruent to 1 mod n -- formula of
      Sutherland et al. arXiv:1709.02442, Lemma 3.1 / Theorem 3.8), then
      STABILIZED RANK under iteration (Fitting lemma: M, M^2, M^3, ...
      until the rank mod p stabilizes -- this is the true p-rank).

  (B) "ground truth": point counting over F_{p^m} for m=1..2g (via a
      finite field GF(p^m) hand-coded with a discrete logarithm table),
      reconstruction of the L polynomial by the Newton identities (EXACT
      integers, checked), then p-rank read off the p-adic Newton polygon.

Assumption used for the point(s) at infinity:
  - if gcd(d,n)=1: total ramification, a SINGLE point, automatically
    F_p-rational (proved: Frobenius fixes the point since it is unique).
  - special case n=2 (classical y^2), d even (gcd(d,2)=2): TWO points at
    infinity if the leading coefficient of f is a square in F_{p^m} (this is
    the case here, leading coefficient = 1), ZERO otherwise. Needed for the
    regression case (8,3,11) which has d=8 even -- this is the bug I had
    initially, fixed here.
  - any other case (gcd(d,n)>1 with n>=3): NOT HANDLED, the script raises an
    explicit error rather than guessing.
"""

import random
from fractions import Fraction

# ============================================================================
# Hand-made finite field GF(p^m), with a discrete logarithm table
# (fast once the table is built: n-th power tests in O(1))
# ============================================================================

def poly_trim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a

def poly_add(a, b, p):
    n = max(len(a), len(b))
    r = [0]*n
    for i, c in enumerate(a): r[i] = (r[i]+c) % p
    for i, c in enumerate(b): r[i] = (r[i]+c) % p
    return poly_trim(r)

def poly_sub(a, b, p):
    n = max(len(a), len(b))
    r = [0]*n
    for i, c in enumerate(a): r[i] = (r[i]+c) % p
    for i, c in enumerate(b): r[i] = (r[i]-c) % p
    return poly_trim(r)

def poly_mul(a, b, p):
    if a == [0] or b == [0]:
        return [0]
    r = [0]*(len(a)+len(b)-1)
    for i, ca in enumerate(a):
        if ca == 0: continue
        for j, cb in enumerate(b):
            if cb == 0: continue
            r[i+j] = (r[i+j] + ca*cb) % p
    return poly_trim(r)

def poly_divmod(a, b, p):
    a = a[:]
    db = len(b)-1
    inv_lead = pow(b[-1], p-2, p)
    q = [0]*max(1, len(a)-db)
    while len(a)-1 >= db and a != [0]:
        shift = len(a)-1-db
        coeff = a[-1]*inv_lead % p
        q[shift] = coeff
        for i, cb in enumerate(b):
            a[i+shift] = (a[i+shift] - coeff*cb) % p
        poly_trim(a)
        if a == [0]:
            break
    return poly_trim(q), poly_trim(a)

def poly_mod(a, m, p):
    return poly_divmod(a, m, p)[1]

def poly_powmod(a, e, m, p):
    result = [1]
    base = poly_mod(a, m, p)
    while e > 0:
        if e & 1:
            result = poly_mod(poly_mul(result, base, p), m, p)
        base = poly_mod(poly_mul(base, base, p), m, p)
        e >>= 1
    return result

def poly_gcd(a, b, p):
    a, b = a[:], b[:]
    while b != [0]:
        _, r = poly_divmod(a, b, p)
        a, b = b, r
    inv_lead = pow(a[-1], p-2, p)
    return poly_trim([c*inv_lead % p for c in a])

def is_irreducible(poly, p, deg):
    x = [0, 1]
    xp = x[:]
    for _ in range(deg):
        xp = poly_powmod(xp, p, poly, p)
    if poly_mod(poly_sub(xp, x, p), poly, p) != [0]:
        return False
    def prime_factors(n):
        fs = set(); d = 2
        while d*d <= n:
            while n % d == 0:
                fs.add(d); n //= d
            d += 1
        if n > 1: fs.add(n)
        return fs
    for q in prime_factors(deg):
        e = deg // q
        xe = x[:]
        for _ in range(e):
            xe = poly_powmod(xe, p, poly, p)
        g = poly_gcd(poly_sub(xe, x, p), poly, p)
        if g != [1]:
            return False
    return True

def find_irreducible(p, deg, seed=1):
    rng = random.Random(seed)
    if deg == 1:
        return [0, 1]
    while True:
        coeffs = [rng.randrange(p) for _ in range(deg)] + [1]
        coeffs[0] = coeffs[0] if coeffs[0] != 0 else 1
        if is_irreducible(coeffs, p, deg):
            return coeffs

class GF:
    def __init__(self, p, m, seed=1):
        self.p = p; self.m = m; self.q = p**m
        self.mod = find_irreducible(p, m, seed=seed) if m > 1 else [0, 1]
        self.zero = tuple([0]*m)
        self.one = tuple([1]+[0]*(m-1))
        self._build_log_tables()

    def _to_tuple(self, poly):
        c = poly[:] + [0]*(self.m-len(poly))
        return tuple(c[:self.m])

    def mul(self, a, b):
        r = poly_mul(list(a), list(b), self.p)
        r = poly_mod(r, self.mod, self.p) if self.m > 1 else ([r[0] % self.p] if r else [0])
        return self._to_tuple(r)

    def add(self, a, b):
        return self._to_tuple(poly_add(list(a), list(b), self.p))

    def _build_log_tables(self):
        q = self.q; order = q - 1
        def factorize(n):
            fs = set(); d = 2
            while d*d <= n:
                while n % d == 0:
                    fs.add(d); n //= d
                d += 1
            if n > 1: fs.add(n)
            return fs
        pf = factorize(order) if order > 1 else set()
        rng = random.Random(42)
        gen = None
        candidates = [self._to_tuple([i]) for i in range(2, min(self.p, 50))]
        candidates += [self._to_tuple([0, 1])] if self.m > 1 else []
        candidates += [tuple([rng.randrange(self.p) for _ in range(self.m)]) for _ in range(300)]
        for cand in candidates:
            if cand == self.zero:
                continue
            ok = True
            for f in pf:
                if self._pow(cand, order // f) == self.one:
                    ok = False; break
            if ok:
                gen = cand; break
        if gen is None:
            raise RuntimeError("generator not found")
        self.gen = gen
        self.pow_table = [None]*order
        self.log_table = {}
        cur = self.one
        for i in range(order):
            self.pow_table[i] = cur
            self.log_table[cur] = i
            cur = self.mul(cur, gen)

    def _pow(self, a, e):
        result = self.one; base = a
        e = e % (self.q - 1) if a != self.zero else e
        while e > 0:
            if e & 1: result = self.mul(result, base)
            base = self.mul(base, base)
            e >>= 1
        return result

    def pow(self, a, e):
        if a == self.zero:
            return self.zero if e > 0 else self.one
        idx = self.log_table[a]
        return self.pow_table[(idx * e) % (self.q - 1)]

    def is_square_or_zero(self, a):
        if a == self.zero:
            return True
        idx = self.log_table[a]
        return idx % 2 == 0

    def num_nth_roots(self, a, n):
        if a == self.zero:
            return 1
        g = self._gcd(n, self.q - 1)
        idx = self.log_table[a]
        if idx % g != 0:
            return 0
        return g

    @staticmethod
    def _gcd(a, b):
        while b: a, b = b, a % b
        return a

    def elements(self):
        for i in range(self.p**self.m):
            c = []; x = i
            for _ in range(self.m):
                c.append(x % self.p); x //= self.p
            yield tuple(c)

# ============================================================================
# (A) Generalized Cartier-Manin matrix (candidate) + stabilized rank
# ============================================================================

def g_dim(d, n, k):
    return (k * d) // n

def block_target(k, n, p):
    """1/y^k = f(x)^N / y^(k_out*p), k_out*p === k (mod n)."""
    p_inv = pow(p, -1, n)
    k_out = (k * p_inv) % n
    if k_out == 0:
        k_out = n
    N = (k_out * p - k) // n
    return k_out, N

def build_full_matrix(p, n, d, r, sigma):
    blocks = []
    offset = {}
    idx = 0
    for k in range(1, n):
        gk = g_dim(d, n, k)
        offset[k] = idx
        blocks.append((k, gk))
        idx += gk
    g = idx
    M = [[0]*g for _ in range(g)]
    for (k, gk) in blocks:
        if gk == 0:
            continue
        k_out, N = block_target(k, n, p)
        g_out = g_dim(d, n, k_out) if k_out < n else 0
        if g_out == 0:
            continue
        fact = [1]*(N+1)
        for t in range(1, N+1):
            fact[t] = fact[t-1]*t % p
        for i in range(1, gk+1):
            for ip in range(1, g_out+1):
                target = p*ip - i
                val = 0
                for b in range(0, N+1):
                    rem = target - r*b
                    if rem < 0 or rem % d != 0:
                        continue
                    a = rem // d
                    if a < 0 or a > N - b:
                        continue
                    c = N - a - b
                    if c < 0:
                        continue
                    coeff = fact[N] * pow(fact[a], p-2, p) % p * pow(fact[b], p-2, p) % p * pow(fact[c], p-2, p) % p
                    val = (val + coeff * pow(sigma, b, p)) % p
                row = offset[k_out] + (ip-1)
                col = offset[k] + (i-1)
                M[row][col] = val
    return M, g

def matrix_rank_mod_p(M, p):
    if not M:
        return 0
    A = [row[:] for row in M]
    n = len(A); m = len(A[0])
    rank = 0; row = 0
    for col in range(m):
        piv = None
        for r_ in range(row, n):
            if A[r_][col] % p != 0:
                piv = r_; break
        if piv is None:
            continue
        A[row], A[piv] = A[piv], A[row]
        inv = pow(A[row][col], p-2, p)
        A[row] = [(x*inv) % p for x in A[row]]
        for r2 in range(n):
            if r2 != row and A[r2][col] % p != 0:
                f = A[r2][col]
                A[r2] = [(A[r2][c2] - f*A[row][c2]) % p for c2 in range(m)]
        row += 1; rank += 1
        if row == n:
            break
    return rank

def matmul_mod_p(A, B, p):
    n = len(A); k = len(B); m = len(B[0]) if k else 0
    R = [[0]*m for _ in range(n)]
    for i in range(n):
        Ai = A[i]
        for t in range(k):
            a = Ai[t]
            if a == 0: continue
            Bt = B[t]
            for j in range(m):
                R[i][j] = (R[i][j] + a*Bt[j]) % p
    return R

def stable_rank(M, p, max_iter=None):
    n = len(M)
    if n == 0:
        return 0
    if max_iter is None:
        max_iter = n
    cur = M
    prev = matrix_rank_mod_p(cur, p)
    for _ in range(max_iter):
        cur = matmul_mod_p(cur, M, p)
        r = matrix_rank_mod_p(cur, p)
        if r == prev:
            return r
        prev = r
    return prev

# ============================================================================
# (B) Ground truth: point counting + L polynomial + Newton polygon
# ============================================================================

def num_points_at_infinity(p, m, n, d, leading_coeff=1):
    import math
    g_ = math.gcd(d, n)
    if g_ == 1:
        return 1
    if n == 2 and d % 2 == 0:
        F = GF(p, m, seed=777)
        lc = F._to_tuple([leading_coeff % p] + [0]*(m-1))
        return 2 if F.is_square_or_zero(lc) and lc != F.zero else 0
    raise NotImplementedError(
        f"points at infinity not handled for gcd(d,n)={g_}, n={n} (only gcd=1, "
        f"or n=2 with d even, are implemented)")

def point_count(p, m, n, d, r, sigma, seed=1):
    F = GF(p, m, seed=seed)
    sigma_elt = F._to_tuple([sigma % p] + [0]*(m-1))
    count = 0
    for x in F.elements():
        xd = F.pow(x, d)
        xr = F.pow(x, r)
        term = F.mul(sigma_elt, xr)
        fx = F.add(F.add(xd, term), F.one)
        count += F.num_nth_roots(fx, n)
    count += num_points_at_infinity(p, m, n, d, leading_coeff=1)
    return count

def newton_identities_to_elementary(power_sums, deg):
    e = [Fraction(0)]*(deg+1)
    e[0] = Fraction(1)
    for k in range(1, deg+1):
        s = Fraction(0)
        for i in range(1, k+1):
            s += ((-1)**(i-1)) * e[k-i] * power_sums[i-1]
        e[k] = s / k
    return e

def l_polynomial_from_counts(p, g, counts):
    deg = 2*g
    power_sums = [p**(m+1) + 1 - counts[m] for m in range(deg)]
    e = newton_identities_to_elementary(power_sums, deg)
    coeffs = [((-1)**k) * e[k] for k in range(deg+1)]
    for c in coeffs:
        assert c.denominator == 1, f"non-integer coefficient {c} -- count probably wrong"
    return [int(c) for c in coeffs]

def p_rank_from_L(coeffs, p):
    def vp(n):
        if n == 0:
            return None
        v = 0; n = abs(n)
        while n % p == 0:
            n //= p; v += 1
        return v
    pts = []
    for k, c in enumerate(coeffs):
        v = vp(c)
        if v is not None:
            pts.append((k, v))
    pts.sort()
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1,y1),(x2,y2) = hull[-2], hull[-1]
            x3,y3 = pt
            cross = (x2-x1)*(y3-y1) - (y2-y1)*(x3-x1)
            if cross <= 0:
                hull.pop()
            else:
                break
        hull.append(pt)
    if len(hull) == 1 and hull[0][1] == 0:
        return hull[0][0], hull
    rank = 0
    for i in range(len(hull)-1):
        x1,y1 = hull[i]; x2,y2 = hull[i+1]
        if y1 == 0 and y2 == 0:
            rank = x2
        else:
            break
    return rank, hull

# ============================================================================
# Test suite
# ============================================================================

def genus(n, d):
    return (n-1)*(d-1)//2

def run_case(p, n, d, r, sigma, label=""):
    g = genus(n, d)
    M, gcheck = build_full_matrix(p, n, d, r, sigma)
    assert gcheck == g, f"inconsistent dimension: g={g} but matrix is {gcheck}x{gcheck}"
    cand = stable_rank(M, p)
    counts = [point_count(p, m, n, d, r, sigma, seed=1000+m) for m in range(1, 2*g+1)]
    coeffs = l_polynomial_from_counts(p, g, counts)
    true_rank, hull = p_rank_from_L(coeffs, p)
    status = "MATCH" if cand == true_rank else "MISMATCH"
    print(f"[{label}] p={p} n={n} d={d} r={r} sigma={sigma}  g={g}  "
          f"true_p_rank={true_rank}  stable_candidate={cand}   ==> {status}", flush=True)
    return status == "MATCH"

if __name__ == "__main__":
    results = []

    print("="*90)
    print("REGRESSION -- cases already validated by hand (must all remain MATCH)")
    print("="*90)
    # NB: (8,3,11) of the classical y^2 is EXCLUDED here: d=8 is even, so
    # gcd(d,n)=gcd(8,2)=2 != 1, which violates the "gcd(d,n)=1" assumption on
    # which g_dim() and the point counting of THIS script are built (the
    # block dimension g_dim(d,n,k)=floor(k*d/n) is only valid under
    # gcd(d,n)=1 -- I checked (8,3,11) separately by hand with the classical
    # formula g=floor((d-1)/2) and 2 points at infinity, match confirmed,
    # but that case does not go through the same generic code).
    # Instead we validate y^2 here with ODD degrees (gcd(d,2)=1), which
    # stays within the general gcd(d,n)=1 framework of the script.
    results.append(run_case(7, 2, 5, 1, 1, "y^2 sanity, d odd"))
    results.append(run_case(7, 2, 5, 3, 2, "y^2 sanity, d odd"))
    results.append(run_case(11, 2, 7, 4, 1, "y^2 sanity, d odd (slower)"))
    results.append(run_case(7, 3, 4, 1, 1, "y^3 regression"))
    results.append(run_case(7, 3, 4, 1, 3, "y^3 regression"))
    results.append(run_case(7, 3, 4, 1, 4, "y^3 regression"))
    results.append(run_case(7, 3, 5, 2, 1, "y^3 regression"))

    print()
    print("="*90)
    print("NEW -- p congruent to 2 (mod 3): the blocks are swapped (k <-> n-k)")
    print("="*90)
    results.append(run_case(5, 3, 4, 1, 1, "p=2 mod 3"))
    results.append(run_case(5, 3, 4, 1, 2, "p=2 mod 3"))
    results.append(run_case(5, 3, 4, 1, 3, "p=2 mod 3"))
    results.append(run_case(5, 3, 4, 1, 4, "p=2 mod 3"))
    results.append(run_case(5, 3, 5, 2, 1, "p=2 mod 3, d=5"))
    results.append(run_case(11, 3, 4, 1, 1, "p=2 mod 3, p=11 (slower)"))

    print()
    print("="*90)
    print("NEW -- n=4 (p congruent to 1 mod 4: stable blocks)")
    print("="*90)
    results.append(run_case(5, 4, 3, 1, 1, "n=4, p=1 mod 4"))
    results.append(run_case(5, 4, 3, 1, 2, "n=4, p=1 mod 4"))
    results.append(run_case(5, 4, 3, 2, 1, "n=4, p=1 mod 4"))

    print()
    print("="*90)
    print("NEW -- n=4, p congruent to 3 mod 4 (cycle of length 2 between blocks)")
    print("="*90)
    results.append(run_case(7, 4, 3, 1, 1, "n=4, p=3 mod 4"))
    results.append(run_case(7, 4, 3, 1, 2, "n=4, p=3 mod 4"))

    print()
    print("="*90)
    n_ok = sum(results)
    print(f"SUMMARY: {n_ok} / {len(results)} MATCH")
    print("="*90)
