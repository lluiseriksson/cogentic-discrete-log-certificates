"""Pure-stdlib zero-floating-point verifier for Paper 59 (DLP-COGENTIC-CERT-1.0):
Google Research Cogentic (Nov 25, 2026), "Discrete Logarithms in Finite Fields of
Fixed Characteristic in Sub-Quasi-Polynomial Time".

Strictly rejects IEEE-754 decimals, NaN/Infinity, duplicate JSON keys, oversized ASTs,
and non-canonical types across four exact modes:
  - Mode 1 (`dlp_zero_error_certificate`): Def. 1.1 & Sec. 6.2 exact zero-error
    (LOG, x) and (NOT_IN_SUBGROUP, E) verification in F_{p^n}^x = (F_p[X]/(f(X)))^x
    with Rabin irreducibility check and optional CRT small-prime/cofactor audit.
  - Mode 2 (`ordinary_elliptic_lang_presentation`): Lemma 4.1 & Eq. (1.2) canonical
    ordinary elliptic curve E/F_q (all characteristics p = 2, 3, >= 5), exact point
    count N_E, Hasse bound, ord(Q) = n, exact Lang-isogeny point I_0 in E(F_{q^n})
    satisfying phi_q(I_0) = I_0 + Q, and Frobenius translation x_P(I_0)^q = x_tilde_P(I_0).
  - Mode 3 (`sparse_moore_linearized_pencil`): Lemmas 3.1 & 3.3 exact Moore & affine
    Moore determinant cross-check over F_q, sparse F_{q0}-affine pencil L_Z(T) = L_0 + Z L_1
    hypotheses (A1)-(A4), exact |AGL_N(F_{q0})|, and complete splitting witness z_0 in F_q.
  - Mode 4 (`unimodular_composite_dlp_solver`): Lemmas 6.3, 6.4 & Thm. 1.2 deterministic
    factoring-free SL_2(Z) composite-modulus solver SolveModM(M_L, E, a) in a cyclic
    subgroup G_L <= F_{p^n}^x, exact LOG / NOT_IN_SUBGROUP deduction, and Thm. 1.2(2)
    asymptotic parameter tuple verification.

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

from src.dlp_exact import (
    ECPoint,
    ECPointExt,
    PolyExt,
    PolyFp,
    agl_order_exact,
    ceil_log2_int,
    distinct_prime_factors_small,
    ec_add_ext,
    ec_add_fq,
    ec_count_points_fq,
    ec_mul_fq,
    ec_on_curve_ext,
    ec_on_curve_fq,
    floor_log2_int,
    fq_add,
    fq_all_elements,
    fq_mul,
    fq_pow,
    gcd_int,
    is_irreducible_fp,
    is_irreducible_fq,
    is_prime_exact,
    mat_det_fq,
    pext_mod,
    pext_pow_mod,
    pext_trim,
    poly_add,
    poly_deg,
    poly_gcd,
    poly_mod,
    poly_mul_mod,
    poly_pow_mod,
    poly_trim,
    solve_mod_m_unimodular,
    xgcd_int,
)

SCHEMA_ID = "DLP-COGENTIC-CERT-1.0"
MAX_AST_DEPTH = 20
MAX_INT_BITS = 4096
MAX_STR_LEN = 2000


class CertificateError(ValueError):
    """Raised whenever a DLP-COGENTIC-CERT-1.0 certificate fails any audit check."""


# =============================================================================
# Strict Zero-Float JSON Ingestion & AST Validation
# =============================================================================


def _deny_ieee754(raw: str) -> Any:
    raise CertificateError(f"IEEE-754 floating-point literal forbidden: {raw!r}")


def _deny_nonfinite(raw: str) -> Any:
    raise CertificateError(f"Non-finite JSON constant forbidden: {raw!r}")


def _no_duplicate_keys(pairs: List[Tuple[str, Any]]) -> Dict[str, Any]:
    obj: Dict[str, Any] = {}
    for k, v in pairs:
        if k in obj:
            raise CertificateError(f"Duplicate JSON object key forbidden: {k!r}")
        obj[k] = v
    return obj


def _validate_ast(obj: Any, depth: int = 0) -> None:
    if depth > MAX_AST_DEPTH:
        raise CertificateError(f"JSON nesting depth exceeds cap {MAX_AST_DEPTH}")
    t = type(obj)
    if t is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise CertificateError("JSON object key must be str")
            if len(k) > MAX_STR_LEN:
                raise CertificateError("JSON key length exceeds cap")
            _validate_ast(v, depth + 1)
    elif t is list:
        for item in obj:
            _validate_ast(item, depth + 1)
    elif t is int:
        if obj.bit_length() > MAX_INT_BITS:
            raise CertificateError(f"Integer bit-length exceeds cap {MAX_INT_BITS}")
    elif t is str:
        if len(obj) > MAX_STR_LEN:
            raise CertificateError(f"String length exceeds cap {MAX_STR_LEN}")
    elif t is bool or obj is None:
        return
    else:
        raise CertificateError(f"Forbidden JSON value type: {t.__name__}")


def _parse_int(val: Any, name: str) -> int:
    if type(val) is not int:
        raise CertificateError(f"Field {name} must be strict int (not bool/str/decimal)")
    if val.bit_length() > MAX_INT_BITS:
        raise CertificateError(f"Field {name} exceeds bit cap")
    return val


def _parse_int_str(val: Any, name: str) -> int:
    """Parse canonical non-negative or signed ASCII decimal integer string (for huge exact ints)."""
    if type(val) is not str or not val:
        raise CertificateError(f"Field {name} must be canonical decimal integer str")
    if len(val) > MAX_STR_LEN:
        raise CertificateError(f"Field {name} exceeds string cap")
    s = val
    if s[0] == "+":
        raise CertificateError(f"Field {name} forbids leading '+'")
    if s == "-0":
        raise CertificateError(f"Field {name} forbids negative zero")
    neg = False
    if s[0] == "-":
        neg = True
        s = s[1:]
    if not s or not (s.isascii() and s.isdigit()):
        raise CertificateError(f"Field {name} must contain ASCII digits only")
    if len(s) > 1 and s[0] == "0":
        raise CertificateError(f"Field {name} forbids leading zeros")
    out = int(s)
    return -out if neg else out


def _parse_poly_fp(val: Any, p: int, name: str, max_len: int = 64) -> PolyFp:
    if type(val) is not list or len(val) > max_len:
        raise CertificateError(f"Field {name} must be list of length <= {max_len}")
    coeffs: List[int] = []
    for i, c in enumerate(val):
        ci = _parse_int(c, f"{name}[{i}]")
        if not (0 <= ci < p):
            raise CertificateError(f"Coefficient {name}[{i}]={ci} outside [0, {p - 1}]")
        coeffs.append(ci)
    if coeffs and coeffs[-1] == 0:
        raise CertificateError(f"Polynomial {name} must be canonical (no trailing zero)")
    return coeffs


def _parse_poly_ext(val: Any, hq: PolyFp, p: int, name: str, max_len: int = 32) -> PolyExt:
    if type(val) is not list or len(val) > max_len:
        raise CertificateError(f"Field {name} must be PolyExt list of length <= {max_len}")
    deg_hq = poly_deg(hq)
    out: PolyExt = []
    for i, c in enumerate(val):
        ci = _parse_poly_fp(c, p, f"{name}[{i}]", max_len=deg_hq)
        if len(ci) > deg_hq:
            raise CertificateError(f"Coefficient {name}[{i}] not reduced mod h_q")
        out.append(ci)
    if out and not out[-1]:
        raise CertificateError(f"PolyExt {name} must be canonical (no trailing zero)")
    return out


def _check_keys(cert: Dict[str, Any], required: set[str], label: str) -> None:
    keys = set(cert.keys())
    if keys != required:
        missing = sorted(required - keys)
        extra = sorted(keys - required)
        raise CertificateError(f"{label} schema key mismatch: missing={missing}, extra={extra}")


# =============================================================================
# Mode 1: Zero-Error Las Vegas DLP Certificate (Definition 1.1 & Sec. 6.2)
# =============================================================================


def _verify_mode1(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "cert_id",
        "p", "n", "f_irred", "g", "h",
        "verdict", "witness_int",
        "crt_audit",
    }
    _check_keys(cert, req, "Mode 1")
    p = _parse_int(cert["p"], "p")
    n = _parse_int(cert["n"], "n")
    if not (2 <= p <= 1009 and is_prime_exact(p)):
        raise CertificateError(f"p={p} must be a prime in [2, 1009]")
    if not (1 <= n <= 32):
        raise CertificateError(f"n={n} must be in [1, 32]")

    f = _parse_poly_fp(cert["f_irred"], p, "f_irred", max_len=n + 1)
    if poly_deg(f) != n or f[-1] != 1:
        raise CertificateError("f_irred must be monic of exact degree n")
    if not is_irreducible_fp(f, p):
        raise CertificateError("f_irred is not irreducible over F_p")

    g = _parse_poly_fp(cert["g"], p, "g", max_len=n)
    h = _parse_poly_fp(cert["h"], p, "h", max_len=n)
    if not g or not h:
        raise CertificateError("g and h must be nonzero elements of F_{p^n}^x")

    group_order = p ** n - 1
    if group_order < 1:
        raise CertificateError("Multiplicative group order must be >= 1")

    verdict = cert["verdict"]
    if verdict not in ("LOG", "NOT_IN_SUBGROUP"):
        raise CertificateError("verdict must be 'LOG' or 'NOT_IN_SUBGROUP'")
    w = _parse_int_str(cert["witness_int"], "witness_int")

    if verdict == "LOG":
        if not (0 <= w <= group_order - 1):
            raise CertificateError("LOG witness x must satisfy 0 <= x <= p^n - 2")
        gx = poly_pow_mod(g, w, f, p)
        if gx != h:
            raise CertificateError("LOG verification failed: g^x != h in F_{p^n}^x")
    else:
        if not (1 <= w <= group_order):
            raise CertificateError("NOT_IN_SUBGROUP exponent E must satisfy 1 <= E <= p^n - 1")
        gE = poly_pow_mod(g, w, f, p)
        hE = poly_pow_mod(h, w, f, p)
        if gE != [1]:
            raise CertificateError("NOT_IN_SUBGROUP verification failed: g^E != 1")
        if hE == [1]:
            raise CertificateError("NOT_IN_SUBGROUP verification failed: h^E == 1 (does not certify non-membership)")

    # Optional Section 6.2 Step 4-5 CRT small-prime / large-cofactor audit
    crt = cert["crt_audit"]
    if crt is not None:
        if type(crt) is not dict:
            raise CertificateError("crt_audit must be dict or null")
        _check_keys(crt, {"S", "L", "xS", "xL", "sigS", "sigL"}, "Mode 1 crt_audit")
        if verdict != "LOG":
            raise CertificateError("crt_audit is only valid for LOG verdict")
        S = _parse_int_str(crt["S"], "S")
        L = _parse_int_str(crt["L"], "L")
        xS = _parse_int_str(crt["xS"], "xS")
        xL = _parse_int_str(crt["xL"], "xL")
        sigS = _parse_int_str(crt["sigS"], "sigS")
        sigL = _parse_int_str(crt["sigL"], "sigL")
        if S < 1 or L < 1 or S * L != group_order:
            raise CertificateError("CRT split must satisfy S >= 1, L >= 1, S * L == p^n - 1")
        if gcd_int(S, L) != 1 or sigS * S + sigL * L != 1:
            raise CertificateError("CRT Bezout identity sigS * S + sigL * L == 1 failed")
        if not (0 <= xS < S and 0 <= xL < L):
            raise CertificateError("CRT components xS, xL out of range")
        # Verify g_S^{xS} == h_S and g_L^{xL} == h_L
        gS = poly_pow_mod(g, L, f, p)
        hS = poly_pow_mod(h, L, f, p)
        if poly_pow_mod(gS, xS, f, p) != hS:
            raise CertificateError("CRT small-prime check g_S^{xS} != h_S failed")
        gL = poly_pow_mod(g, S, f, p)
        hL = poly_pow_mod(h, S, f, p)
        if poly_pow_mod(gL, xL, f, p) != hL:
            raise CertificateError("CRT cofactor check g_L^{xL} != h_L failed")
        x_crt = (xS * sigL * L + xL * sigS * S) % group_order
        if x_crt != w:
            raise CertificateError(f"CRT recombined x={x_crt} != witness_int={w}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "p": p,
        "n": n,
        "verdict": verdict,
        "witness_int": str(w),
    }


# =============================================================================
# Mode 2: Canonical Ordinary Elliptic Curve & Lang Equation (1.2) (Lemma 4.1)
# =============================================================================


def _verify_mode2(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "cert_id",
        "p", "hq_irred",
        "a1", "a2", "a4", "a6",
        "claimed_NE", "point_Q", "order_n",
        "Mx_irred", "I0_x", "I0_y",
        "trans_P",
    }
    _check_keys(cert, req, "Mode 2")
    p = _parse_int(cert["p"], "p")
    if not (2 <= p <= 31 and is_prime_exact(p)):
        raise CertificateError(f"Mode 2 prime p={p} must be in [2, 31]")
    hq = _parse_poly_fp(cert["hq_irred"], p, "hq_irred", max_len=9)
    r = poly_deg(hq)
    if r < 1 or hq[-1] != 1 or not is_irreducible_fp(hq, p):
        raise CertificateError("hq_irred must be monic irreducible over F_p")
    q = p ** r
    if q > 64:
        raise CertificateError(f"Mode 2 exact enumeration cap requires q <= 64, got q={q}")

    a1 = _parse_poly_fp(cert["a1"], p, "a1", max_len=r)
    a2 = _parse_poly_fp(cert["a2"], p, "a2", max_len=r)
    a4 = _parse_poly_fp(cert["a4"], p, "a4", max_len=r)
    a6 = _parse_poly_fp(cert["a6"], p, "a6", max_len=r)

    # Check canonical ordinary form from Lemma 4.1(1)
    if p == 2:
        if a1 != [1] or a4 != [] or not a6:
            raise CertificateError("Canonical p=2 ordinary curve requires a1=1, a4=0, a6!=0")
    elif p == 3:
        if a1 != [] or a4 != [] or not a2 or not a6:
            raise CertificateError("Canonical p=3 ordinary curve requires a1=0, a4=0, a2!=0, a6!=0")
    else:
        if a1 != [] or a2 != []:
            raise CertificateError("Canonical p>=5 curve requires a1=0, a2=0")
        # 4 a4^3 + 27 a6^2 != 0 in F_q
        a4_3 = fq_mul(fq_mul(a4, a4, hq, p), a4, hq, p)
        a6_2 = fq_mul(a6, a6, hq, p)
        disc_part = fq_add(
            poly_trim([4 * c for c in a4_3], p),
            poly_trim([27 * c for c in a6_2], p),
            hq,
            p,
        )
        if not disc_part:
            raise CertificateError("Curve is singular: 4 a4^3 + 27 a6^2 == 0")

    # Exact point count N_E = |E(F_q)|, Hasse bound, and ordinarity p nmid (q + 1 - N_E)
    NE = ec_count_points_fq(a1, a2, a4, a6, hq, p)
    if _parse_int(cert["claimed_NE"], "claimed_NE") != NE:
        raise CertificateError(f"claimed_NE mismatch: exact={NE}")
    trace = q + 1 - NE
    if trace * trace > 4 * q:
        raise CertificateError("Hasse bound violated")
    if trace % p == 0:
        raise CertificateError("Curve is supersingular (p divides q + 1 - NE), not ordinary")

    # Verify Q in E(F_q) has exact order n >= 3
    n = _parse_int(cert["order_n"], "order_n")
    if not (3 <= n <= 16):
        raise CertificateError("order_n must be in [3, 16]")
    raw_Q = cert["point_Q"]
    if type(raw_Q) is not list or len(raw_Q) != 2:
        raise CertificateError("point_Q must be [xQ, yQ]")
    Q: ECPoint = (
        _parse_poly_fp(raw_Q[0], p, "point_Q[0]", max_len=r),
        _parse_poly_fp(raw_Q[1], p, "point_Q[1]", max_len=r),
    )
    if not ec_on_curve_fq(Q, a1, a2, a4, a6, hq, p):
        raise CertificateError("point_Q is not on E(F_q)")
    if ec_mul_fq(n, Q, a1, a2, a4, hq, p) is not None:
        raise CertificateError("[n]Q != O_E")
    for pf in distinct_prime_factors_small(n):
        if ec_mul_fq(n // pf, Q, a1, a2, a4, hq, p) is None:
            raise CertificateError(f"point_Q has smaller order dividing {n // pf}")

    # Verify M_x in F_q[Y] monic irreducible of degree n, and I_0 = (I0_x, I0_y) in E(F_{q^n})
    Mx = _parse_poly_ext(cert["Mx_irred"], hq, p, "Mx_irred", max_len=n + 1)
    if len(Mx) - 1 != n or Mx[-1] != [1]:
        raise CertificateError("Mx_irred must be monic of exact degree n over F_q")
    if not is_irreducible_fq(Mx, hq, p):
        raise CertificateError("Mx_irred is not irreducible over F_q")

    I0_x = _parse_poly_ext(cert["I0_x"], hq, p, "I0_x", max_len=n)
    I0_y = _parse_poly_ext(cert["I0_y"], hq, p, "I0_y", max_len=n)
    a1e: PolyExt = [a1] if a1 else []
    a2e: PolyExt = [a2] if a2 else []
    a4e: PolyExt = [a4] if a4 else []
    a6e: PolyExt = [a6] if a6 else []
    I0: ECPointExt = (I0_x, I0_y)
    if not ec_on_curve_ext(I0, a1e, a2e, a4e, a6e, Mx, hq, p):
        raise CertificateError("Lang point I0 is not on E(F_{q^n})")

    # Exact Eq. (1.2): phi_q(I0) = (I0_x^q, I0_y^q) == I0 + Q in E(F_{q^n})!
    phi_I0: ECPointExt = (
        pext_pow_mod(I0_x, q, Mx, hq, p),
        pext_pow_mod(I0_y, q, Mx, hq, p),
    )
    Qe: ECPointExt = ([Q[0]] if Q[0] else [], [Q[1]] if Q[1] else [])
    I0_plus_Q = ec_add_ext(I0, Qe, a1e, a2e, a4e, Mx, hq, p)
    if phi_I0 != I0_plus_Q:
        raise CertificateError("Lang isogeny Eq. (1.2) failed: phi_q(I0) != I0 + Q")

    # Verify Frobenius translation identity x_P(I0)^q == x_tilde_P(I0) for P in E(F_q)
    raw_P = cert["trans_P"]
    if type(raw_P) is not list or len(raw_P) != 2:
        raise CertificateError("trans_P must be [xP, yP]")
    P: ECPoint = (
        _parse_poly_fp(raw_P[0], p, "trans_P[0]", max_len=r),
        _parse_poly_fp(raw_P[1], p, "trans_P[1]", max_len=r),
    )
    if not ec_on_curve_fq(P, a1, a2, a4, a6, hq, p):
        raise CertificateError("trans_P is not on E(F_q)")
    Pe: ECPointExt = ([P[0]] if P[0] else [], [P[1]] if P[1] else [])
    P_plus_Q = ec_add_fq(P, Q, a1, a2, a4, hq, p)
    if P_plus_Q is None:
        raise CertificateError("trans_P + Q cannot be O_E")
    PQe: ECPointExt = ([P_plus_Q[0]] if P_plus_Q[0] else [], [P_plus_Q[1]] if P_plus_Q[1] else [])

    I0_plus_P = ec_add_ext(I0, Pe, a1e, a2e, a4e, Mx, hq, p)
    I0_plus_PQ = ec_add_ext(I0, PQe, a1e, a2e, a4e, Mx, hq, p)
    if I0_plus_P is None or I0_plus_PQ is None:
        raise CertificateError("Translation hit O_E along I0")
    xP_I0_q = pext_pow_mod(I0_plus_P[0], q, Mx, hq, p)
    xtildeP_I0 = I0_plus_PQ[0]
    if xP_I0_q != xtildeP_I0:
        raise CertificateError("Frobenius translation identity x_P(I0)^q != x_tilde_P(I0) failed")

    return {
        "verified": True,
        "mode": cert["mode"],
        "p": p,
        "q": q,
        "NE": NE,
        "order_n": n,
        "trace": trace,
    }


# =============================================================================
# Mode 3: Moore Determinants & Sparse F_{q0}-Affine Pencils (Lemmas 3.1 & 3.3)
# =============================================================================


def _eval_sparse_linearized_fq(
    coeffs: Dict[int, PolyFp], d0: PolyFp, val: PolyFp, q0: int, hq: PolyFp, p: int
) -> PolyFp:
    acc = d0
    for exp_idx, c in coeffs.items():
        if c:
            term = fq_mul(c, fq_pow(val, q0 ** exp_idx, hq, p), hq, p)
            acc = fq_add(acc, term, hq, p)
    return acc


def _verify_mode3(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "cert_id",
        "p", "s", "t", "hq_irred",
        "moore_z", "claimed_moore_det", "claimed_affine_moore_det",
        "pencil_N", "pencil_L0_terms", "pencil_L1_terms",
        "pencil_delta0", "pencil_delta1",
        "splitting_z0",
        "claimed_agl_order", "claimed_split_root_count",
    }
    _check_keys(cert, req, "Mode 3")
    p = _parse_int(cert["p"], "p")
    s = _parse_int(cert["s"], "s")
    t = _parse_int(cert["t"], "t")
    if not (2 <= p <= 7 and is_prime_exact(p)):
        raise CertificateError("Mode 3 requires prime p in [2, 7]")
    if not (1 <= s <= 4 and 2 <= t <= 6):
        raise CertificateError("Mode 3 requires 1 <= s <= 4 and 2 <= t <= 6")
    q0 = p ** s
    if q0 < 3:
        raise CertificateError("Lemma 3.3 requires q0 = p^s >= 3")
    deg_fq = s * t
    hq = _parse_poly_fp(cert["hq_irred"], p, "hq_irred", max_len=deg_fq + 1)
    if poly_deg(hq) != deg_fq or hq[-1] != 1 or not is_irreducible_fp(hq, p):
        raise CertificateError("hq_irred must be monic irreducible of degree s*t over F_p")
    q = p ** deg_fq
    if q > 729:
        raise CertificateError(f"Mode 3 exact field enumeration requires q <= 729, got q={q}")

    # Collect exact subfield F_{q0} = {u in F_q : u^{q0} == u}
    fq_elems = fq_all_elements(hq, p)
    fq0_elems = [u for u in fq_elems if fq_pow(u, q0, hq, p) == u]
    if len(fq0_elems) != q0:
        raise CertificateError("Subfield F_{q0} extraction failed")

    # 1. Verify Lemma 3.1 Moore and affine Moore determinants via BOTH matrix det AND product formula
    raw_z = cert["moore_z"]
    if type(raw_z) is not list or not (2 <= len(raw_z) <= 4):
        raise CertificateError("moore_z must have length in [2, 4]")
    r_m = len(raw_z)
    zs = [_parse_poly_fp(raw_z[i], p, f"moore_z[{i}]", max_len=deg_fq) for i in range(r_m)]

    M_moore: List[List[PolyFp]] = [
        [fq_pow(zs[i], q0 ** j, hq, p) for j in range(r_m)] for i in range(r_m)
    ]
    det_moore = mat_det_fq(M_moore, hq, p)
    if not det_moore:
        raise CertificateError("moore_z is F_{q0}-linearly dependent (det M_{q0} == 0)")

    # Cross-check exact Lemma 3.1(1) product formula: prod_{j=0}^{r-1} prod_{c in F_{q0}^j} (z_j - sum c_i z_i)
    prod_det: PolyFp = [1]
    span_list: List[PolyFp] = [[]]  # span of z_0..z_{j-1} over F_{q0}
    for j in range(r_m):
        for comb in span_list:
            diff = poly_trim([((zs[j][k] if k < len(zs[j]) else 0) - (comb[k] if k < len(comb) else 0)) % p
                              for k in range(max(len(zs[j]), len(comb)))], p)
            prod_det = fq_mul(prod_det, diff, hq, p)
        if j + 1 < r_m:
            new_span: List[PolyFp] = []
            for comb in span_list:
                for c in fq0_elems:
                    new_span.append(fq_add(comb, fq_mul(c, zs[j], hq, p), hq, p))
            span_list = new_span
    if det_moore != prod_det:
        raise CertificateError("Lemma 3.1(1) Moore determinant product formula mismatch")

    M_aff: List[List[PolyFp]] = []
    for i in range(r_m):
        row_i: List[PolyFp] = [[1]]
        for j in range(r_m - 1):
            row_i.append(fq_pow(zs[i], q0 ** j, hq, p))
        M_aff.append(row_i)
    det_aff = mat_det_fq(M_aff, hq, p)
    if not det_aff:
        raise CertificateError("moore_z is F_{q0}-affinely dependent (det M_aff == 0)")

    if _parse_poly_fp(cert["claimed_moore_det"], p, "claimed_moore_det", max_len=deg_fq) != det_moore:
        raise CertificateError("claimed_moore_det mismatch")
    if _parse_poly_fp(cert["claimed_affine_moore_det"], p, "claimed_affine_moore_det", max_len=deg_fq) != det_aff:
        raise CertificateError("claimed_affine_moore_det mismatch")

    # 2. Verify Lemma 3.3 sparse F_{q0}-affine pencil L_Z(T) = L_0(T) + Z L_1(T) hypotheses (A1)-(A4)
    N = _parse_int(cert["pencil_N"], "pencil_N")
    if not (2 <= N <= 4):
        raise CertificateError("pencil_N must be in [2, 4]")
    if q0 ** N > q:
        raise CertificateError("Complete splitting over F_q requires q0^N <= q")

    def _parse_terms(raw: Any, label: str) -> Dict[int, PolyFp]:
        if type(raw) is not dict or not raw:
            raise CertificateError(f"{label} must be non-empty dict mapping exponent index str to F_q element")
        out_t: Dict[int, PolyFp] = {}
        for k_str, v in raw.items():
            idx = _parse_int_str(k_str, f"{label}.key")
            if not (0 <= idx <= N):
                raise CertificateError(f"{label} exponent index {idx} outside [0, {N}]")
            out_t[idx] = _parse_poly_fp(v, p, f"{label}[{k_str}]", max_len=deg_fq)
        return out_t

    L0_t = _parse_terms(cert["pencil_L0_terms"], "pencil_L0_terms")
    L1_t = _parse_terms(cert["pencil_L1_terms"], "pencil_L1_terms")
    d0 = _parse_poly_fp(cert["pencil_delta0"], p, "pencil_delta0", max_len=deg_fq)
    d1 = _parse_poly_fp(cert["pencil_delta1"], p, "pencil_delta1", max_len=deg_fq)

    a0N = L0_t.get(N, [])
    a1N = L1_t.get(N, [])
    a00 = L0_t.get(0, [])
    a10 = L1_t.get(0, [])
    a0Nm1 = L0_t.get(N - 1, [])
    a1Nm1 = L1_t.get(N - 1, [])

    # (A1): a_{0,N} a_{1,0} - a_{1,N} a_{0,0} != 0
    delta1 = poly_trim(
        poly_add(
            fq_mul(a0N, a10, hq, p),
            [(-c) % p for c in fq_mul(a1N, a00, hq, p)],
            p,
        ),
        p,
    )
    if not delta1:
        raise CertificateError("Lemma 3.3 hypothesis (A1) failed: Delta_1 == 0")

    # (A2): a_{0,N} a_{1,N-1} - a_{1,N} a_{0,N-1} != 0
    delta2 = poly_trim(
        poly_add(
            fq_mul(a0N, a1Nm1, hq, p),
            [(-c) % p for c in fq_mul(a1N, a0Nm1, hq, p)],
            p,
        ),
        p,
    )
    if not delta2:
        raise CertificateError("Lemma 3.3 hypothesis (A2) failed: Delta_2 == 0")

    # Build full polynomials A0, A1, L0, L1 in F_q[T] and check (A3) gcd(A0, A1) == 1, (A4) gcd(L0, L1) == 1
    deg_T = q0 ** N

    def _to_pext(terms: Dict[int, PolyFp], const_term: Optional[PolyFp], shift: int) -> PolyExt:
        arr: List[PolyFp] = [[] for _ in range(deg_T + 1 - shift)]
        if const_term is not None:
            arr[0] = const_term
        for idx, c in terms.items():
            if c:
                arr[q0 ** idx - shift] = c
        return pext_trim(arr, hq, p)

    A0_poly = _to_pext(L0_t, None, 1)
    A1_poly = _to_pext(L1_t, None, 1)
    L0_poly = _to_pext(L0_t, d0, 0)
    L1_poly = _to_pext(L1_t, d1, 0)

    from src.dlp_exact import pext_gcd as _pext_gcd

    if _pext_gcd(A0_poly, A1_poly, hq, p) != [[1]]:
        raise CertificateError("Lemma 3.3 hypothesis (A3) failed: gcd(A0, A1) != 1")
    if _pext_gcd(L0_poly, L1_poly, hq, p) != [[1]]:
        raise CertificateError("Lemma 3.3 hypothesis (A4) failed: gcd(L0, L1) != 1")

    # 3. Verify explicit complete splitting specialization z0 in F_q:
    #    L_{z0}(T) has nonzero leading & linear coeffs and EXACTLY q0^N distinct roots in F_q!
    z0 = _parse_poly_fp(cert["splitting_z0"], p, "splitting_z0", max_len=deg_fq)
    lc_z0 = fq_add(a0N, fq_mul(z0, a1N, hq, p), hq, p)
    lin_z0 = fq_add(a00, fq_mul(z0, a10, hq, p), hq, p)
    if not lc_z0 or not lin_z0:
        raise CertificateError("Specialization z0 degenerates leading or linear coefficient")

    Lz0_terms: Dict[int, PolyFp] = {}
    for idx in range(N + 1):
        c0 = L0_t.get(idx, [])
        c1 = L1_t.get(idx, [])
        comb = fq_add(c0, fq_mul(z0, c1, hq, p), hq, p)
        if comb:
            Lz0_terms[idx] = comb
    dz0 = fq_add(d0, fq_mul(z0, d1, hq, p), hq, p)

    roots = [
        u for u in fq_elems
        if not _eval_sparse_linearized_fq(Lz0_terms, dz0, u, q0, hq, p)
    ]
    if len(roots) != q0 ** N:
        raise CertificateError(
            f"Specialization z0 does not split completely over F_q: found {len(roots)} != {q0 ** N} roots"
        )

    agl_ord = agl_order_exact(q0, N)
    if _parse_int_str(cert["claimed_agl_order"], "claimed_agl_order") != agl_ord:
        raise CertificateError(f"claimed_agl_order mismatch: exact={agl_ord}")
    if _parse_int(cert["claimed_split_root_count"], "claimed_split_root_count") != len(roots):
        raise CertificateError("claimed_split_root_count mismatch")

    return {
        "verified": True,
        "mode": cert["mode"],
        "q0": q0,
        "q": q,
        "N": N,
        "agl_order": str(agl_ord),
        "split_roots": len(roots),
    }


# =============================================================================
# Mode 4: Factoring-Free SL_2(Z) Composite Linear Algebra & Thm. 1.2 Guards
# =============================================================================


def _verify_mode4(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "cert_id",
        "p", "n", "f_irred",
        "M_L", "gamma", "deltas",
        "rel_matrix_E", "rel_rhs_a",
        "claimed_y",
        "g_L", "h_L", "e_g", "e_h",
        "subgroup_verdict", "subgroup_witness",
        "thm12_param_probe",
    }
    _check_keys(cert, req, "Mode 4")
    p = _parse_int(cert["p"], "p")
    n = _parse_int(cert["n"], "n")
    if not (2 <= p <= 1009 and is_prime_exact(p)):
        raise CertificateError("Mode 4 requires prime p in [2, 1009]")
    if not (1 <= n <= 32):
        raise CertificateError("Mode 4 requires n in [1, 32]")
    f = _parse_poly_fp(cert["f_irred"], p, "f_irred", max_len=n + 1)
    if poly_deg(f) != n or f[-1] != 1 or not is_irreducible_fp(f, p):
        raise CertificateError("Mode 4 f_irred must be monic irreducible of degree n")

    ML = _parse_int_str(cert["M_L"], "M_L")
    group_order = p ** n - 1
    if ML < 2 or group_order % ML != 0:
        raise CertificateError("M_L must be >= 2 and divide p^n - 1")

    gamma = _parse_poly_fp(cert["gamma"], p, "gamma", max_len=n)
    if not gamma:
        raise CertificateError("gamma must be nonzero")
    if gamma == [1]:
        raise CertificateError("gamma must be nontrivial (gamma != 1)")
    if poly_pow_mod(gamma, ML, f, p) != [1]:
        raise CertificateError("gamma^{M_L} != 1")

    raw_deltas = cert["deltas"]
    if type(raw_deltas) is not list or not (1 <= len(raw_deltas) <= 12):
        raise CertificateError("deltas must be list of length in [1, 12]")
    K = len(raw_deltas)
    deltas = [_parse_poly_fp(raw_deltas[j], p, f"deltas[{j}]", max_len=n) for j in range(K)]
    for j, dj in enumerate(deltas):
        if not dj or poly_pow_mod(dj, ML, f, p) != [1]:
            raise CertificateError(f"deltas[{j}] not in order-M_L subgroup G_L")

    raw_E = cert["rel_matrix_E"]
    raw_a = cert["rel_rhs_a"]
    if type(raw_E) is not list or type(raw_a) is not list or len(raw_E) != len(raw_a):
        raise CertificateError("rel_matrix_E and rel_rhs_a must have matching row count")
    R = len(raw_E)
    if not (K <= R <= 48):
        raise CertificateError("Row count R must satisfy K <= R <= 48")
    E_mat: List[List[int]] = []
    a_vec: List[int] = []
    for r_idx in range(R):
        row = raw_E[r_idx]
        if type(row) is not list or len(row) != K:
            raise CertificateError(f"rel_matrix_E[{r_idx}] must have length {K}")
        er = [_parse_int_str(row[j], f"E[{r_idx}][{j}]") for j in range(K)]
        if any(not (0 <= v < ML) for v in er):
            raise CertificateError(f"E[{r_idx}] entry outside [0, M_L - 1]")
        ar = _parse_int_str(raw_a[r_idx], f"a[{r_idx}]")
        if not (0 <= ar < ML):
            raise CertificateError(f"a[{r_idx}] outside [0, M_L - 1]")
        E_mat.append(er)
        a_vec.append(ar)

        # Verify actual multiplicative relation prod_j delta_j^{E_{r,j}} == gamma^{a_r} in F_{p^n}^x!
        lhs_elt: PolyFp = [1]
        for j in range(K):
            if er[j] != 0:
                lhs_elt = poly_mul_mod(lhs_elt, poly_pow_mod(deltas[j], er[j], f, p), f, p)
        rhs_elt = poly_pow_mod(gamma, ar, f, p)
        if lhs_elt != rhs_elt:
            raise CertificateError(f"Multiplicative relation row {r_idx} failed in F_{{p^n}}^x")

    # Run deterministic factoring-free SL_2(Z) SolveModM(M_L, E, a) (Lemma 6.3(2))
    y_sol = solve_mod_m_unimodular(ML, E_mat, a_vec)
    if y_sol is None:
        raise CertificateError("SolveModM failed (relation matrix does not have full row span mod M_L)")
    raw_cy = cert["claimed_y"]
    if type(raw_cy) is not list or len(raw_cy) != K:
        raise CertificateError("claimed_y length mismatch")
    claimed_y = [_parse_int_str(raw_cy[j], f"claimed_y[{j}]") for j in range(K)]
    if claimed_y != y_sol:
        raise CertificateError(f"claimed_y mismatch: exact={y_sol}")
    for j in range(K):
        if poly_pow_mod(gamma, y_sol[j], f, p) != deltas[j]:
            raise CertificateError(f"SolveModM output failed group check delta_{j} == gamma^{{y_{j}}}")

    # Audit Lemma 6.4 deduction on (g_L, h_L) from factor-base decompositions e_g, e_h
    gL = _parse_poly_fp(cert["g_L"], p, "g_L", max_len=n)
    hL = _parse_poly_fp(cert["h_L"], p, "h_L", max_len=n)
    if not gL or not hL:
        raise CertificateError("g_L and h_L must be nonzero")
    raw_eg = cert["e_g"]
    raw_eh = cert["e_h"]
    if type(raw_eg) is not list or type(raw_eh) is not list or len(raw_eg) != K or len(raw_eh) != K:
        raise CertificateError("e_g and e_h must have length K")
    e_g = [_parse_int_str(raw_eg[j], f"e_g[{j}]") for j in range(K)]
    e_h = [_parse_int_str(raw_eh[j], f"e_h[{j}]") for j in range(K)]
    if any(not (0 <= v < ML) for v in e_g) or any(not (0 <= v < ML) for v in e_h):
        raise CertificateError("e_g, e_h entries must lie in [0, M_L - 1]")

    def _prod_deltas(exps: List[int]) -> PolyFp:
        acc: PolyFp = [1]
        for j in range(K):
            if exps[j] != 0:
                acc = poly_mul_mod(acc, poly_pow_mod(deltas[j], exps[j], f, p), f, p)
        return acc

    if _prod_deltas(e_g) != gL:
        raise CertificateError("Factor-base decomposition failed for g_L")
    if _prod_deltas(e_h) != hL:
        raise CertificateError("Factor-base decomposition failed for h_L")

    Yg = sum(e_g[j] * y_sol[j] for j in range(K)) % ML
    Yh = sum(e_h[j] * y_sol[j] for j in range(K)) % ML
    Dg, sg, _ = xgcd_int(Yg, ML)

    sub_v = cert["subgroup_verdict"]
    sub_w = _parse_int_str(cert["subgroup_witness"], "subgroup_witness")
    if sub_v == "LOG":
        if Yh % Dg != 0:
            raise CertificateError("LOG claimed when Dg does not divide Yh")
        xL = (sg * (Yh // Dg)) % ML
        if not (0 <= sub_w < ML):
            raise CertificateError("subgroup_witness xL out of range")
        if poly_pow_mod(gL, sub_w, f, p) != hL:
            raise CertificateError("g_L^{xL} != h_L")
        if (Yg * sub_w) % ML != Yh:
            raise CertificateError("Modular equation Yg * xL == Yh (mod M_L) failed")
        if (Yg * xL) % ML != Yh:
            raise CertificateError("Internal xgcd solution check failed")
    elif sub_v == "NOT_IN_SUBGROUP":
        if Yh % Dg == 0:
            raise CertificateError("NOT_IN_SUBGROUP claimed when Dg divides Yh")
        Eg = ML // Dg
        if sub_w != Eg or not (1 <= Eg < ML):
            raise CertificateError(f"subgroup_witness Eg mismatch: exact={Eg}")
        if poly_pow_mod(gL, Eg, f, p) != [1]:
            raise CertificateError("g_L^{Eg} != 1")
        if poly_pow_mod(hL, Eg, f, p) == [1]:
            raise CertificateError("h_L^{Eg} == 1 (does not certify non-membership)")
    else:
        raise CertificateError("subgroup_verdict must be 'LOG' or 'NOT_IN_SUBGROUP'")

    # Audit exact Theorem 1.2(2) asymptotic parameter tuple (ell_2, ell_3, ell_p, s, B, m)
    tp = cert["thm12_param_probe"]
    if type(tp) is not dict:
        raise CertificateError("thm12_param_probe must be dict")
    _check_keys(
        tp,
        {"p_probe", "ell2_log2_ell1", "claimed_ell3", "claimed_ellp", "claimed_s", "claimed_B", "claimed_m"},
        "Mode 4 thm12_param_probe",
    )
    p_pr = _parse_int(tp["p_probe"], "p_probe")
    if not (2 <= p_pr <= 1009 and is_prime_exact(p_pr)):
        raise CertificateError("p_probe must be prime in [2, 1009]")
    ell2 = _parse_int(tp["ell2_log2_ell1"], "ell2_log2_ell1")
    if ell2 < 1024:
        raise CertificateError("ell2_log2_ell1 must be >= 1024 (ell3 >= 10)")
    ell3 = floor_log2_int(ell2)
    ellp = ceil_log2_int(p_pr)
    s_exact = max(3, (ell3 * ell3 + ellp - 1) // ellp)
    B_exact = ell2 // (32 * s_exact * ellp)
    m_exact = 2 * B_exact + 4
    if ell3 < 10 or B_exact < 4:
        raise CertificateError("Theorem 1.2(2) asymptotic regime requires ell3 >= 10 and B >= 4")
    if _parse_int(tp["claimed_ell3"], "claimed_ell3") != ell3:
        raise CertificateError(f"claimed_ell3 mismatch: exact={ell3}")
    if _parse_int(tp["claimed_ellp"], "claimed_ellp") != ellp:
        raise CertificateError(f"claimed_ellp mismatch: exact={ellp}")
    if _parse_int(tp["claimed_s"], "claimed_s") != s_exact:
        raise CertificateError(f"claimed_s mismatch: exact={s_exact}")
    if _parse_int(tp["claimed_B"], "claimed_B") != B_exact:
        raise CertificateError(f"claimed_B mismatch: exact={B_exact}")
    if _parse_int(tp["claimed_m"], "claimed_m") != m_exact:
        raise CertificateError(f"claimed_m mismatch: exact={m_exact}")
    # Verify Sec. 6.3 cofactor cap: m * s * ell_p < ell_2 / 8 (exact integer: 8 * m * s * ell_p < ell_2)
    if 8 * m_exact * s_exact * ellp >= ell2:
        raise CertificateError("Sec. 6.3 cofactor cap 8 * m * s * ell_p < ell_2 failed")

    return {
        "verified": True,
        "mode": cert["mode"],
        "M_L": str(ML),
        "K": K,
        "R": R,
        "subgroup_verdict": sub_v,
        "B_exact": B_exact,
    }


# =============================================================================
# Public API
# =============================================================================


def verify_certificate(cert: Any) -> Dict[str, Any]:
    _validate_ast(cert)
    if type(cert) is not dict:
        raise CertificateError("Certificate root must be JSON object")
    if cert.get("schema") != SCHEMA_ID:
        raise CertificateError(f"Unsupported schema: {cert.get('schema')!r}")
    cid = cert.get("cert_id")
    if type(cid) is not str or not cid.strip():
        raise CertificateError("cert_id must be a non-empty string")
    mode = cert.get("mode")
    if mode == "dlp_zero_error_certificate":
        return _verify_mode1(cert)
    if mode == "ordinary_elliptic_lang_presentation":
        return _verify_mode2(cert)
    if mode == "sparse_moore_linearized_pencil":
        return _verify_mode3(cert)
    if mode == "unimodular_composite_dlp_solver":
        return _verify_mode4(cert)
    raise CertificateError(f"Unknown verification mode: {mode!r}")


def verify_certificate_json_text(text: str) -> Dict[str, Any]:
    data = json.loads(
        text,
        parse_float=_deny_ieee754,
        parse_constant=_deny_nonfinite,
        object_pairs_hook=_no_duplicate_keys,
    )
    return verify_certificate(data)


def verify_certificate_file(path: str | Path) -> Dict[str, Any]:
    return verify_certificate_json_text(Path(path).read_text(encoding="utf-8"))
