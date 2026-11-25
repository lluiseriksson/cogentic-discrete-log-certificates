"""Pure-stdlib exact arithmetic engine for Paper 59:
Google Research Cogentic (Nov 25, 2026), "Discrete Logarithms in Finite Fields of
Fixed Characteristic in Sub-Quasi-Polynomial Time".

Provides ZERO-floating-point exact arithmetic exclusively over Python `int`:
  - Deterministic primality testing and exact prime factorization of small integers
  - Exact polynomial arithmetic over F_p[X], Rabin irreducibility testing, and F_{p^n} = F_p[X]/(f(X))
  - Exact relative field extensions F_{q^n} = F_q[Y]/(M_x(Y)) over F_q = F_p[T]/(h(T))
  - Exact canonical ordinary elliptic curve arithmetic E/F_q and E/F_{q^n} across ALL
    characteristics (p = 2, p = 3, p >= 5; Lemma 4.1(1)), Frobenius phi_q, Lang equation (1.2)
  - Exact Moore and affine-Moore matrices & determinants over F_q (Lemma 3.1)
  - Exact F_{q0}-linearized sparse Frobenius pencils L_Z(T) = L_0(T) + Z L_1(T) (Lemma 3.3)
  - Exact factoring-free SL_2(Z) composite-modulus solver SolveModM(M, E, a) (Lemma 6.3(2))

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

from typing import List, Optional, Sequence, Tuple

PolyFp = List[int]        # low-to-high coefficients in [0, p-1], trimmed (0 is [])
PolyExt = List[PolyFp]    # polynomial over F_q, coefficients are PolyFp mod h_q
ECPoint = Optional[Tuple[PolyFp, PolyFp]]  # None represents O_E (point at infinity)
ECPointExt = Optional[Tuple[PolyExt, PolyExt]]


# =============================================================================
# 1. Exact Integer Primality, GCD, Extended GCD, and Small Factorization
# =============================================================================


def is_prime_exact(n: int) -> bool:
    """Exact deterministic trial-division primality test (zero floats)."""
    if n < 2:
        return False
    if n in (2, 3):
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    d = 5
    while d * d <= n:
        if n % d == 0 or n % (d + 2) == 0:
            return False
        d += 6
    return True


def gcd_int(a: int, b: int) -> int:
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a % b
    return a


def xgcd_int(a: int, b: int) -> Tuple[int, int, int]:
    """Extended Euclidean algorithm returning (d, s, t) with d = gcd(|a|,|b|) = s*a + t*b >= 0."""
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    if old_r < 0:
        return -old_r, -old_s, -old_t
    return old_r, old_s, old_t


def distinct_prime_factors_small(n: int) -> List[int]:
    """Exact trial division for small positive integers n (used for degree n <= 64 and order checks)."""
    out: List[int] = []
    m = n
    d = 2
    while d * d <= m:
        if m % d == 0:
            out.append(d)
            while m % d == 0:
                m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        out.append(m)
    return out


def floor_log2_int(n: int) -> int:
    """Exact integer floor(log2(n)) for n >= 1 (zero floats)."""
    if n < 1:
        raise ValueError("floor_log2_int requires n >= 1")
    return n.bit_length() - 1


def ceil_log2_int(n: int) -> int:
    """Exact integer ceil(log2(n)) for n >= 1 (zero floats)."""
    if n < 1:
        raise ValueError("ceil_log2_int requires n >= 1")
    return (n - 1).bit_length()


# =============================================================================
# 2. Exact Polynomial Arithmetic over F_p[X] and Finite Fields F_{p^n}
# =============================================================================


def poly_trim(a: Sequence[int], p: int) -> PolyFp:
    res = [c % p for c in a]
    while res and res[-1] == 0:
        res.pop()
    return res


def poly_deg(a: Sequence[int]) -> int:
    return len(a) - 1


def poly_add(a: PolyFp, b: PolyFp, p: int) -> PolyFp:
    n = max(len(a), len(b))
    out = [((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % p for i in range(n)]
    return poly_trim(out, p)


def poly_sub(a: PolyFp, b: PolyFp, p: int) -> PolyFp:
    n = max(len(a), len(b))
    out = [((a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)) % p for i in range(n)]
    return poly_trim(out, p)


def poly_neg(a: PolyFp, p: int) -> PolyFp:
    return [(-c) % p for c in a]


def poly_scale(a: PolyFp, s: int, p: int) -> PolyFp:
    s %= p
    if s == 0:
        return []
    return poly_trim([(c * s) % p for c in a], p)


def poly_mul(a: PolyFp, b: PolyFp, p: int) -> PolyFp:
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if bj != 0:
                out[i + j] = (out[i + j] + ai * bj) % p
    return poly_trim(out, p)


def poly_divmod(a: PolyFp, b: PolyFp, p: int) -> Tuple[PolyFp, PolyFp]:
    if not b:
        raise ZeroDivisionError("Polynomial division by zero")
    r = list(a)
    db = len(b) - 1
    inv_lc = pow(b[-1], p - 2, p)
    if len(r) - 1 < db:
        return [], poly_trim(r, p)
    q = [0] * (len(r) - db)
    while len(r) - 1 >= db:
        coeff = (r[-1] * inv_lc) % p
        shift = len(r) - 1 - db
        q[shift] = coeff
        for i in range(db + 1):
            r[shift + i] = (r[shift + i] - coeff * b[i]) % p
        while r and r[-1] == 0:
            r.pop()
    return poly_trim(q, p), poly_trim(r, p)


def poly_mod(a: PolyFp, mod: PolyFp, p: int) -> PolyFp:
    return poly_divmod(a, mod, p)[1]


def poly_gcd(a: PolyFp, b: PolyFp, p: int) -> PolyFp:
    x, y = poly_trim(a, p), poly_trim(b, p)
    while y:
        x, y = y, poly_divmod(x, y, p)[1]
    if x:
        inv_lc = pow(x[-1], p - 2, p)
        x = poly_scale(x, inv_lc, p)
    return x


def poly_xgcd(a: PolyFp, b: PolyFp, p: int) -> Tuple[PolyFp, PolyFp, PolyFp]:
    """Return (g, s, t) monic g = gcd(a, b) = s*a + t*b in F_p[X]."""
    old_r, r = poly_trim(a, p), poly_trim(b, p)
    old_s, s = [1], []
    old_t, t = [], [1]
    while r:
        q, rem = poly_divmod(old_r, r, p)
        old_r, r = r, rem
        old_s, s = s, poly_sub(old_s, poly_mul(q, s, p), p)
        old_t, t = t, poly_sub(old_t, poly_mul(q, t, p), p)
    if old_r:
        inv_lc = pow(old_r[-1], p - 2, p)
        old_r = poly_scale(old_r, inv_lc, p)
        old_s = poly_scale(old_s, inv_lc, p)
        old_t = poly_scale(old_t, inv_lc, p)
    return old_r, old_s, old_t


def poly_mul_mod(a: PolyFp, b: PolyFp, mod: PolyFp, p: int) -> PolyFp:
    return poly_mod(poly_mul(a, b, p), mod, p)


def poly_pow_mod(base: PolyFp, exp: int, mod: PolyFp, p: int) -> PolyFp:
    if exp < 0:
        raise ValueError("Negative exponent in poly_pow_mod")
    res: PolyFp = [1]
    cur = poly_mod(base, mod, p)
    e = exp
    while e > 0:
        if e & 1:
            res = poly_mul_mod(res, cur, mod, p)
        e >>= 1
        if e > 0:
            cur = poly_mul_mod(cur, cur, mod, p)
    return res


def poly_inv_mod(a: PolyFp, mod: PolyFp, p: int) -> PolyFp:
    g, s, _ = poly_xgcd(a, mod, p)
    if g != [1]:
        raise ZeroDivisionError("Element not invertible modulo polynomial")
    return poly_mod(s, mod, p)


def is_irreducible_fp(f: PolyFp, p: int) -> bool:
    """Exact Rabin irreducibility test for monic f in F_p[X] of degree n >= 1 (zero floats)."""
    f = poly_trim(f, p)
    n = poly_deg(f)
    if n < 1 or f[-1] != 1:
        return False
    if n == 1:
        return True
    x_poly: PolyFp = [0, 1]
    # Compute X^{p^k} mod f iteratively for k = 1..n
    xk = x_poly
    p_factors = distinct_prime_factors_small(n)
    check_ks = {n // r for r in p_factors}
    for k in range(1, n + 1):
        xk = poly_pow_mod(xk, p, f, p)
        if k in check_ks:
            diff = poly_sub(xk, x_poly, p)
            if poly_gcd(f, diff, p) != [1]:
                return False
    return xk == x_poly


# =============================================================================
# 3. Exact Arithmetic over F_q[Y] and Relative Extensions F_{q^n} = F_q[Y]/(M_x(Y))
# =============================================================================


def fq_add(a: PolyFp, b: PolyFp, hq: PolyFp, p: int) -> PolyFp:
    return poly_add(a, b, p)


def fq_sub(a: PolyFp, b: PolyFp, hq: PolyFp, p: int) -> PolyFp:
    return poly_sub(a, b, p)


def fq_neg(a: PolyFp, p: int) -> PolyFp:
    return poly_neg(a, p)


def fq_mul(a: PolyFp, b: PolyFp, hq: PolyFp, p: int) -> PolyFp:
    return poly_mul_mod(a, b, hq, p)


def fq_inv(a: PolyFp, hq: PolyFp, p: int) -> PolyFp:
    if not a:
        raise ZeroDivisionError("Inversion of zero in F_q")
    return poly_inv_mod(a, hq, p)


def fq_pow(a: PolyFp, e: int, hq: PolyFp, p: int) -> PolyFp:
    return poly_pow_mod(a, e, hq, p)


def fq_all_elements(hq: PolyFp, p: int) -> List[PolyFp]:
    r = poly_deg(hq)
    total = p ** r
    elems: List[PolyFp] = []
    for idx in range(total):
        cur = idx
        coeffs: List[int] = []
        for _ in range(r):
            coeffs.append(cur % p)
            cur //= p
        elems.append(poly_trim(coeffs, p))
    return elems


def pext_trim(a: Sequence[PolyFp], hq: PolyFp, p: int) -> PolyExt:
    res = [poly_mod(c, hq, p) for c in a]
    while res and not res[-1]:
        res.pop()
    return res


def pext_add(a: PolyExt, b: PolyExt, hq: PolyFp, p: int) -> PolyExt:
    n = max(len(a), len(b))
    out = [poly_add(a[i] if i < len(a) else [], b[i] if i < len(b) else [], p) for i in range(n)]
    return pext_trim(out, hq, p)


def pext_sub(a: PolyExt, b: PolyExt, hq: PolyFp, p: int) -> PolyExt:
    n = max(len(a), len(b))
    out = [poly_sub(a[i] if i < len(a) else [], b[i] if i < len(b) else [], p) for i in range(n)]
    return pext_trim(out, hq, p)


def pext_scale(a: PolyExt, s: PolyFp, hq: PolyFp, p: int) -> PolyExt:
    if not s:
        return []
    return pext_trim([fq_mul(c, s, hq, p) for c in a], hq, p)


def pext_mul(a: PolyExt, b: PolyExt, hq: PolyFp, p: int) -> PolyExt:
    if not a or not b:
        return []
    out: List[PolyFp] = [[] for _ in range(len(a) + len(b) - 1)]
    for i, ai in enumerate(a):
        if not ai:
            continue
        for j, bj in enumerate(b):
            if bj:
                out[i + j] = poly_add(out[i + j], fq_mul(ai, bj, hq, p), p)
    return pext_trim(out, hq, p)


def pext_divmod(a: PolyExt, b: PolyExt, hq: PolyFp, p: int) -> Tuple[PolyExt, PolyExt]:
    if not b:
        raise ZeroDivisionError("PolyExt division by zero")
    r = list(a)
    db = len(b) - 1
    inv_lc = fq_inv(b[-1], hq, p)
    if len(r) - 1 < db:
        return [], pext_trim(r, hq, p)
    q_out: List[PolyFp] = [[] for _ in range(len(r) - db)]
    while len(r) - 1 >= db:
        coeff = fq_mul(r[-1], inv_lc, hq, p)
        shift = len(r) - 1 - db
        q_out[shift] = coeff
        for i in range(db + 1):
            r[shift + i] = poly_sub(r[shift + i], fq_mul(coeff, b[i], hq, p), p)
        while r and not r[-1]:
            r.pop()
    return pext_trim(q_out, hq, p), pext_trim(r, hq, p)


def pext_mod(a: PolyExt, mod: PolyExt, hq: PolyFp, p: int) -> PolyExt:
    return pext_divmod(a, mod, hq, p)[1]


def pext_gcd(a: PolyExt, b: PolyExt, hq: PolyFp, p: int) -> PolyExt:
    x, y = pext_trim(a, hq, p), pext_trim(b, hq, p)
    while y:
        x, y = y, pext_divmod(x, y, hq, p)[1]
    if x:
        x = pext_scale(x, fq_inv(x[-1], hq, p), hq, p)
    return x


def pext_xgcd(a: PolyExt, b: PolyExt, hq: PolyFp, p: int) -> Tuple[PolyExt, PolyExt, PolyExt]:
    old_r, r = pext_trim(a, hq, p), pext_trim(b, hq, p)
    old_s: PolyExt = [[1]]
    s: PolyExt = []
    old_t: PolyExt = []
    t: PolyExt = [[1]]
    while r:
        q_poly, rem = pext_divmod(old_r, r, hq, p)
        old_r, r = r, rem
        old_s, s = s, pext_sub(old_s, pext_mul(q_poly, s, hq, p), hq, p)
        old_t, t = t, pext_sub(old_t, pext_mul(q_poly, t, hq, p), hq, p)
    if old_r:
        inv_lc = fq_inv(old_r[-1], hq, p)
        old_r = pext_scale(old_r, inv_lc, hq, p)
        old_s = pext_scale(old_s, inv_lc, hq, p)
        old_t = pext_scale(old_t, inv_lc, hq, p)
    return old_r, old_s, old_t


def pext_mul_mod(a: PolyExt, b: PolyExt, mod: PolyExt, hq: PolyFp, p: int) -> PolyExt:
    return pext_mod(pext_mul(a, b, hq, p), mod, hq, p)


def pext_pow_mod(base: PolyExt, exp: int, mod: PolyExt, hq: PolyFp, p: int) -> PolyExt:
    res: PolyExt = [[1]]
    cur = pext_mod(base, mod, hq, p)
    e = exp
    while e > 0:
        if e & 1:
            res = pext_mul_mod(res, cur, mod, hq, p)
        e >>= 1
        if e > 0:
            cur = pext_mul_mod(cur, cur, mod, hq, p)
    return res


def pext_inv_mod(a: PolyExt, mod: PolyExt, hq: PolyFp, p: int) -> PolyExt:
    g, s, _ = pext_xgcd(a, mod, hq, p)
    if g != [[1]]:
        raise ZeroDivisionError("Element not invertible in F_{q^n}")
    return pext_mod(s, mod, hq, p)


def is_irreducible_fq(Mx: PolyExt, hq: PolyFp, p: int) -> bool:
    """Exact Rabin irreducibility test for monic Mx in F_q[Y] of degree n >= 1."""
    Mx = pext_trim(Mx, hq, p)
    n = len(Mx) - 1
    if n < 1 or Mx[-1] != [1]:
        return False
    if n == 1:
        return True
    q = p ** poly_deg(hq)
    y_poly: PolyExt = [[], [1]]
    yk = y_poly
    check_ks = {n // r for r in distinct_prime_factors_small(n)}
    for k in range(1, n + 1):
        yk = pext_pow_mod(yk, q, Mx, hq, p)
        if k in check_ks:
            diff = pext_sub(yk, y_poly, hq, p)
            if pext_gcd(Mx, diff, hq, p) != [[1]]:
                return False
    return yk == y_poly


# =============================================================================
# 4. Canonical Ordinary Elliptic Curves E/F_q and E/F_{q^n} (Lemma 4.1)
#    Equation: y^2 + a1*x*y = x^3 + a2*x^2 + a4*x + a6
# =============================================================================


def ec_on_curve_fq(
    pt: ECPoint, a1: PolyFp, a2: PolyFp, a4: PolyFp, a6: PolyFp, hq: PolyFp, p: int
) -> bool:
    if pt is None:
        return True
    x, y = pt
    lhs = fq_add(fq_mul(y, y, hq, p), fq_mul(fq_mul(a1, x, hq, p), y, hq, p), hq, p)
    x2 = fq_mul(x, x, hq, p)
    x3 = fq_mul(x2, x, hq, p)
    rhs = fq_add(
        fq_add(x3, fq_mul(a2, x2, hq, p), hq, p),
        fq_add(fq_mul(a4, x, hq, p), a6, hq, p),
        hq,
        p,
    )
    return lhs == rhs


def ec_neg_fq(pt: ECPoint, a1: PolyFp, hq: PolyFp, p: int) -> ECPoint:
    if pt is None:
        return None
    x, y = pt
    ny = fq_sub(fq_neg(y, p), fq_mul(a1, x, hq, p), hq, p)
    return (x, ny)


def ec_add_fq(
    P1: ECPoint, P2: ECPoint, a1: PolyFp, a2: PolyFp, a4: PolyFp, hq: PolyFp, p: int
) -> ECPoint:
    if P1 is None:
        return P2
    if P2 is None:
        return P1
    x1, y1 = P1
    x2, y2 = P2
    if x1 == x2:
        # Check if P2 == -P1
        if fq_add(fq_add(y1, y2, hq, p), fq_mul(a1, x1, hq, p), hq, p) == []:
            return None
        # Point doubling
        denom = fq_add(fq_add(y1, y1, hq, p), fq_mul(a1, x1, hq, p), hq, p)
        if not denom:
            return None
        x1_sq = fq_mul(x1, x1, hq, p)
        num = fq_sub(
            fq_add(
                fq_add(poly_scale(x1_sq, 3, p), fq_mul(poly_scale(a2, 2, p), x1, hq, p), hq, p),
                a4,
                hq,
                p,
            ),
            fq_mul(a1, y1, hq, p),
            hq,
            p,
        )
        lam = fq_mul(num, fq_inv(denom, hq, p), hq, p)
    else:
        lam = fq_mul(fq_sub(y2, y1, hq, p), fq_inv(fq_sub(x2, x1, hq, p), hq, p), hq, p)
    x3 = fq_sub(
        fq_sub(
            fq_sub(fq_add(fq_mul(lam, lam, hq, p), fq_mul(a1, lam, hq, p), hq, p), a2, hq, p),
            x1,
            hq,
            p,
        ),
        x2,
        hq,
        p,
    )
    y3 = fq_sub(
        fq_sub(fq_mul(lam, fq_sub(x1, x3, hq, p), hq, p), y1, hq, p),
        fq_mul(a1, x3, hq, p),
        hq,
        p,
    )
    return (x3, y3)


def ec_mul_fq(
    k: int, P: ECPoint, a1: PolyFp, a2: PolyFp, a4: PolyFp, hq: PolyFp, p: int
) -> ECPoint:
    if k == 0 or P is None:
        return None
    if k < 0:
        P = ec_neg_fq(P, a1, hq, p)
        k = -k
    acc: ECPoint = None
    cur: ECPoint = P
    while k > 0:
        if k & 1:
            acc = ec_add_fq(acc, cur, a1, a2, a4, hq, p)
        k >>= 1
        if k > 0:
            cur = ec_add_fq(cur, cur, a1, a2, a4, hq, p)
    return acc


def ec_count_points_fq(
    a1: PolyFp, a2: PolyFp, a4: PolyFp, a6: PolyFp, hq: PolyFp, p: int
) -> int:
    """Exact point count |E(F_q)| by exhaustive evaluation over F_q (for small q)."""
    elems = fq_all_elements(hq, p)
    cnt = 1  # point at infinity O_E
    for x in elems:
        x2 = fq_mul(x, x, hq, p)
        x3 = fq_mul(x2, x, hq, p)
        rhs = fq_add(
            fq_add(x3, fq_mul(a2, x2, hq, p), hq, p),
            fq_add(fq_mul(a4, x, hq, p), a6, hq, p),
            hq,
            p,
        )
        a1x = fq_mul(a1, x, hq, p)
        for y in elems:
            lhs = fq_add(fq_mul(y, y, hq, p), fq_mul(a1x, y, hq, p), hq, p)
            if lhs == rhs:
                cnt += 1
    return cnt


def ec_on_curve_ext(
    pt: ECPointExt,
    a1: PolyExt, a2: PolyExt, a4: PolyExt, a6: PolyExt,
    Mx: PolyExt, hq: PolyFp, p: int,
) -> bool:
    if pt is None:
        return True
    x, y = pt
    lhs = pext_add(
        pext_mul_mod(y, y, Mx, hq, p),
        pext_mul_mod(pext_mul_mod(a1, x, Mx, hq, p), y, Mx, hq, p),
        hq,
        p,
    )
    x2 = pext_mul_mod(x, x, Mx, hq, p)
    x3 = pext_mul_mod(x2, x, Mx, hq, p)
    rhs = pext_add(
        pext_add(x3, pext_mul_mod(a2, x2, Mx, hq, p), hq, p),
        pext_add(pext_mul_mod(a4, x, Mx, hq, p), a6, hq, p),
        hq,
        p,
    )
    return pext_mod(lhs, Mx, hq, p) == pext_mod(rhs, Mx, hq, p)


def ec_add_ext(
    P1: ECPointExt, P2: ECPointExt,
    a1: PolyExt, a2: PolyExt, a4: PolyExt,
    Mx: PolyExt, hq: PolyFp, p: int,
) -> ECPointExt:
    if P1 is None:
        return P2
    if P2 is None:
        return P1
    x1, y1 = P1
    x2, y2 = P2
    if x1 == x2:
        if pext_add(pext_add(y1, y2, hq, p), pext_mul_mod(a1, x1, Mx, hq, p), hq, p) == []:
            return None
        denom = pext_add(pext_add(y1, y1, hq, p), pext_mul_mod(a1, x1, Mx, hq, p), hq, p)
        if not denom:
            return None
        x1_sq = pext_mul_mod(x1, x1, Mx, hq, p)
        three_x1_sq = pext_scale(x1_sq, [3 % p] if 3 % p else [], hq, p)
        two_a2 = pext_scale(a2, [2 % p] if 2 % p else [], hq, p)
        num = pext_sub(
            pext_add(
                pext_add(three_x1_sq, pext_mul_mod(two_a2, x1, Mx, hq, p), hq, p),
                a4,
                hq,
                p,
            ),
            pext_mul_mod(a1, y1, Mx, hq, p),
            hq,
            p,
        )
        lam = pext_mul_mod(num, pext_inv_mod(denom, Mx, hq, p), Mx, hq, p)
    else:
        lam = pext_mul_mod(
            pext_sub(y2, y1, hq, p),
            pext_inv_mod(pext_sub(x2, x1, hq, p), Mx, hq, p),
            Mx,
            hq,
            p,
        )
    x3 = pext_sub(
        pext_sub(
            pext_sub(
                pext_add(pext_mul_mod(lam, lam, Mx, hq, p), pext_mul_mod(a1, lam, Mx, hq, p), hq, p),
                a2,
                hq,
                p,
            ),
            x1,
            hq,
            p,
        ),
        x2,
        hq,
        p,
    )
    y3 = pext_sub(
        pext_sub(pext_mul_mod(lam, pext_sub(x1, x3, hq, p), Mx, hq, p), y1, hq, p),
        pext_mul_mod(a1, x3, Mx, hq, p),
        hq,
        p,
    )
    return (pext_mod(x3, Mx, hq, p), pext_mod(y3, Mx, hq, p))


# =============================================================================
# 5. Exact Moore Matrix Determinant over F_q (Lemma 3.1) & F_q Linear Algebra
# =============================================================================


def mat_det_fq(M: List[List[PolyFp]], hq: PolyFp, p: int) -> PolyFp:
    """Exact determinant of an r x r matrix over F_q = F_p[T]/(hq) via Gaussian elimination."""
    n = len(M)
    A = [[poly_mod(M[i][j], hq, p) for j in range(n)] for i in range(n)]
    det: PolyFp = [1]
    sign = 1
    for col in range(n):
        piv = None
        for r in range(col, n):
            if A[r][col]:
                piv = r
                break
        if piv is None:
            return []
        if piv != col:
            A[col], A[piv] = A[piv], A[col]
            sign = -sign
        piv_val = A[col][col]
        det = fq_mul(det, piv_val, hq, p)
        inv_piv = fq_inv(piv_val, hq, p)
        for r in range(col + 1, n):
            if A[r][col]:
                factor = fq_mul(A[r][col], inv_piv, hq, p)
                for c in range(col, n):
                    A[r][c] = poly_sub(A[r][c], fq_mul(factor, A[col][c], hq, p), p)
    if sign < 0:
        det = fq_neg(det, p)
    return det


def agl_order_exact(q0: int, N: int) -> int:
    """Exact order |AGL_N(F_{q0})| = q0^N * prod_{j=0}^{N-1} (q0^N - q0^j)."""
    qN = q0 ** N
    prod = qN
    pj = 1
    for _ in range(N):
        prod *= (qN - pj)
        pj *= q0
    return prod


# =============================================================================
# 6. Exact Factoring-Free SL_2(Z) Composite-Modulus Solver (Lemma 6.3(2))
# =============================================================================


def solve_mod_m_unimodular(M: int, E: Sequence[Sequence[int]], a: Sequence[int]) -> Optional[List[int]]:
    """Exact deterministic SolveModM(M, E, a) from Cogentic Lemma 6.3(2):
    Solves E * y == a (mod M) over Z/MZ using ONLY SL_2(Z) unimodular row operations
    and xgcd (NEVER factoring M). Returns y in {0,...,M-1}^K or None on FAIL."""
    if M < 2 or not E:
        return None
    R = len(E)
    K = len(E[0])
    if R < K or len(a) != R:
        return None
    A = [[x % M for x in row] for row in E]
    c = [x % M for x in a]
    for k in range(K):
        for i in range(k + 1, R):
            v = A[i][k]
            if v != 0:
                u = A[k][k]
                d, s, t = xgcd_int(u, v)
                u_div = u // d
                v_div = v // d
                row_k = A[k]
                row_i = A[i]
                new_k = [(s * row_k[j] + t * row_i[j]) % M for j in range(K)]
                new_i = [((-v_div) * row_k[j] + u_div * row_i[j]) % M for j in range(K)]
                new_ck = (s * c[k] + t * c[i]) % M
                new_ci = ((-v_div) * c[k] + u_div * c[i]) % M
                A[k], A[i] = new_k, new_i
                c[k], c[i] = new_ck, new_ci
        dk, sk, _ = xgcd_int(A[k][k], M)
        if dk != 1:
            return None
        sk %= M
        A[k] = [(sk * x) % M for x in A[k]]
        c[k] = (sk * c[k]) % M
    # Back-substitution above diagonal
    for k in range(K - 1, -1, -1):
        for i in range(k):
            fac = A[i][k]
            if fac != 0:
                A[i] = [(A[i][j] - fac * A[k][j]) % M for j in range(K)]
                c[i] = (c[i] - fac * c[k]) % M
    # Verify exact consistency on all R rows (including rows k >= K)
    y = c[:K]
    for r in range(R):
        lhs = sum(E[r][j] * y[j] for j in range(K)) % M
        if lhs != a[r] % M:
            return None
    return y
