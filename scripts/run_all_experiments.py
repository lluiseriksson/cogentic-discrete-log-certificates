"""Generate all 16 canonical DLP-COGENTIC-CERT-1.0 certificates and 4 exact result JSONs
for Paper 59 (Google Research Cogentic, Nov 25, 2026: Sub-Quasi-Polynomial Discrete Logarithms).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
import random
import statistics
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.dlp_certifier import SCHEMA_ID, verify_certificate, verify_certificate_file
from src.dlp_exact import (
    PolyExt,
    PolyFp,
    agl_order_exact,
    ceil_log2_int,
    distinct_prime_factors_small,
    ec_add_ext,
    ec_add_fq,
    ec_count_points_fq,
    ec_mul_fq,
    ec_on_curve_fq,
    floor_log2_int,
    fq_add,
    fq_all_elements,
    fq_inv,
    fq_mul,
    fq_neg,
    fq_pow,
    gcd_int,
    is_irreducible_fp,
    is_irreducible_fq,
    mat_det_fq,
    pext_add,
    pext_divmod,
    pext_gcd,
    pext_mod,
    pext_mul,
    pext_mul_mod,
    pext_pow_mod,
    pext_scale,
    pext_sub,
    pext_trim,
    poly_add,
    poly_deg,
    poly_mul_mod,
    poly_pow_mod,
    poly_scale,
    poly_trim,
    solve_mod_m_unimodular,
    xgcd_int,
)

CERT_DIR = ROOT / "certificates"
RES_DIR = ROOT / "results"


def find_monic_irred_fp(p: int, n: int) -> PolyFp:
    """Deterministic search for a sparse monic irreducible polynomial of degree n over F_p."""
    # Try trinomials X^n + c*X^k + d first, then pentanomials, then deterministic PRNG
    for d in range(1, p):
        for k in range(1, n):
            for c in range(1, p):
                f = [0] * (n + 1)
                f[0] = d
                f[k] = c
                f[n] = 1
                if is_irreducible_fp(f, p):
                    return f
    rng = random.Random(20261125 + 1009 * p + n)
    while True:
        f = [rng.randrange(1, p)] + [rng.randrange(p) for _ in range(n - 1)] + [1]
        if is_irreducible_fp(f, p):
            return f


def find_primitive_element(p: int, f: PolyFp) -> PolyFp:
    n = poly_deg(f)
    order = p ** n - 1
    pfs = distinct_prime_factors_small(order)
    rng = random.Random(10007 * p + 31 * n)
    # Try [0, 1] (X) first
    cands: List[PolyFp] = [[0, 1], [1, 1], [2 % p, 1]]
    for _ in range(500):
        c = poly_trim([rng.randrange(p) for _ in range(n)], p)
        if c:
            cands.append(c)
    for g in cands:
        if not g:
            continue
        if all(poly_pow_mod(g, order // r, f, p) != [1] for r in pfs):
            return g
    raise RuntimeError(f"Failed to find primitive element in F_{p}^{n}")


# =============================================================================
# Mode 1 Builder: Definition 1.1 & Sec. 6.2 Zero-Error DLP Certificates
# =============================================================================


def build_mode1_certs() -> List[Dict[str, Any]]:
    certs: List[Dict[str, Any]] = []

    # 1. F_{2^16}^x (order 65535 = 15 * 4369), LOG with full CRT audit
    p, n = 2, 16
    f = find_monic_irred_fp(p, n)
    g = find_primitive_element(p, f)
    order = p ** n - 1  # 65535
    S, L = 15, 4369
    d, sigS, sigL = xgcd_int(S, L)
    assert d == 1 and S * L == order
    x = 41927
    h = poly_pow_mod(g, x, f, p)
    certs.append({
        "schema": SCHEMA_ID,
        "mode": "dlp_zero_error_certificate",
        "cert_id": "m1_dlp_f2_16_log_crt",
        "p": p, "n": n, "f_irred": f, "g": g, "h": h,
        "verdict": "LOG",
        "witness_int": str(x),
        "crt_audit": {
            "S": str(S), "L": str(L),
            "xS": str(x % S), "xL": str(x % L),
            "sigS": str(sigS), "sigL": str(sigL),
        },
    })

    # 2. F_{3^12}^x (order 531440 = 80 * 6643), LOG with full CRT audit
    p, n = 3, 12
    f = find_monic_irred_fp(p, n)
    g = find_primitive_element(p, f)
    order = p ** n - 1  # 531440
    S, L = 80, 6643
    d, sigS, sigL = xgcd_int(S, L)
    assert d == 1 and S * L == order
    x = 314159
    h = poly_pow_mod(g, x, f, p)
    certs.append({
        "schema": SCHEMA_ID,
        "mode": "dlp_zero_error_certificate",
        "cert_id": "m1_dlp_f3_12_log_crt",
        "p": p, "n": n, "f_irred": f, "g": g, "h": h,
        "verdict": "LOG",
        "witness_int": str(x),
        "crt_audit": {
            "S": str(S), "L": str(L),
            "xS": str(x % S), "xL": str(x % L),
            "sigS": str(sigS), "sigL": str(sigL),
        },
    })

    # 3. F_{2^20}^x (order 1048575), NOT_IN_SUBGROUP (g = gen^5 has order E = 209715, h = gen^7)
    p, n = 2, 20
    f = find_monic_irred_fp(p, n)
    gen = find_primitive_element(p, f)
    order = p ** n - 1  # 1048575 = 5 * 209715
    g = poly_pow_mod(gen, 5, f, p)
    h = poly_pow_mod(gen, 7, f, p)
    E = order // 5
    certs.append({
        "schema": SCHEMA_ID,
        "mode": "dlp_zero_error_certificate",
        "cert_id": "m1_dlp_f2_20_not_in_subgroup",
        "p": p, "n": n, "f_irred": f, "g": g, "h": h,
        "verdict": "NOT_IN_SUBGROUP",
        "witness_int": str(E),
        "crt_audit": None,
    })

    # 4. F_{5^10}^x (order 9765624), NOT_IN_SUBGROUP (g = gen^11 has order E = 887784, h = gen^13)
    p, n = 5, 10
    f = find_monic_irred_fp(p, n)
    gen = find_primitive_element(p, f)
    order = p ** n - 1  # 9765624 = 11 * 887784
    assert order % 11 == 0
    g = poly_pow_mod(gen, 11, f, p)
    h = poly_pow_mod(gen, 13, f, p)
    E = order // 11
    certs.append({
        "schema": SCHEMA_ID,
        "mode": "dlp_zero_error_certificate",
        "cert_id": "m1_dlp_f5_10_not_in_subgroup",
        "p": p, "n": n, "f_irred": f, "g": g, "h": h,
        "verdict": "NOT_IN_SUBGROUP",
        "witness_int": str(E),
        "crt_audit": None,
    })

    return certs


# =============================================================================
# Mode 2 Builder: Canonical Ordinary Elliptic Curves & Exact Lang Eq. (1.2)
# Implements Lemma 4.1(2) directly via Psi_Q(X, X^q) and Cantor-Zassenhaus!
# =============================================================================


def _pext_trace_pow2(w: PolyExt, deg_ext_over_f2: int, mod: PolyExt, hq: PolyFp) -> PolyExt:
    acc = w
    cur = w
    for _ in range(deg_ext_over_f2 - 1):
        cur = pext_mul_mod(cur, cur, mod, hq, 2)
        acc = pext_add(acc, cur, hq, 2)
    return acc


def _split_equal_degree_fq(poly: PolyExt, d: int, hq: PolyFp, p: int) -> PolyExt:
    """Find one monic irreducible factor of degree d of a squarefree product of degree-d irreducibles in F_q[Y]."""
    q = p ** poly_deg(hq)
    r_fq = poly_deg(hq)
    cur = poly
    rng = random.Random(20261125 + 97 * q + d)
    elems = fq_all_elements(hq, p)
    while len(cur) - 1 > d:
        deg_cur = len(cur) - 1
        w: PolyExt = pext_trim([rng.choice(elems) for _ in range(deg_cur)], hq, p)
        if not w:
            continue
        if p == 2:
            s = _pext_trace_pow2(w, r_fq * d, cur, hq)
        else:
            exp = (q ** d - 1) // 2
            s = pext_sub(pext_pow_mod(w, exp, cur, hq, p), [[1]], hq, p)
        g = pext_gcd(cur, s, hq, p)
        if 0 < len(g) - 1 < deg_cur:
            cur = g if len(g) - 1 <= deg_cur - (len(g) - 1) else pext_divmod(cur, g, hq, p)[0]
    return cur


def _build_lang_presentation_exact(
    cert_id: str, p: int, r: int, target_n: int
) -> Dict[str, Any]:
    hq = find_monic_irred_fp(p, r)
    q = p ** r
    elems = fq_all_elements(hq, p)
    nz_elems = [e for e in elems if e]

    # Search canonical ordinary models from Lemma 4.1(1)
    candidates: List[Tuple[PolyFp, PolyFp, PolyFp, PolyFp]] = []
    if p == 2:
        for a2 in elems:
            for a6 in nz_elems:
                candidates.append(([1], a2, [], a6))
    elif p == 3:
        for a2 in nz_elems:
            for a6 in nz_elems:
                candidates.append(([], a2, [], a6))
    else:
        for a4 in elems:
            for a6 in nz_elems:
                a4_3 = fq_mul(fq_mul(a4, a4, hq, p), a4, hq, p)
                a6_2 = fq_mul(a6, a6, hq, p)
                disc = fq_add(poly_scale(a4_3, 4, p), poly_scale(a6_2, 27, p), hq, p)
                if disc:
                    candidates.append(([], [], a4, a6))

    for a1, a2, a4, a6 in candidates:
        NE = ec_count_points_fq(a1, a2, a4, a6, hq, p)
        if NE % target_n != 0 or (q + 1 - NE) % p == 0:
            continue
        # Find all affine points in E(F_q) and locate Q of exact order target_n
        pts: List[Tuple[PolyFp, PolyFp]] = []
        for x in elems:
            for y in elems:
                if ec_on_curve_fq((x, y), a1, a2, a4, a6, hq, p):
                    pts.append((x, y))
        Q: Optional[Tuple[PolyFp, PolyFp]] = None
        for pt in pts:
            if ec_mul_fq(target_n, pt, a1, a2, a4, hq, p) is None:
                if all(ec_mul_fq(target_n // pf, pt, a1, a2, a4, hq, p) is not None
                       for pf in distinct_prime_factors_small(target_n)):
                    Q = pt
                    break
        if Q is None:
            continue

        # Construct G_Q(X) = Psi_Q(X, X^q) in F_q[X] directly from Cogentic Lemma 4.1(1)-(2)!
        xQ, yQ = Q
        cQ = fq_neg(fq_add(fq_add(yQ, yQ, hq, p), fq_mul(a1, xQ, hq, p), hq, p), p)
        if not cQ:
            continue
        cQ_inv = fq_inv(cQ, hq, p)
        # B_{2,Q}(X) = xQ*X^2 + (a4 + xQ^2 + 2*a2*xQ - a1*yQ)*X + (2*a6 + a4*xQ)
        b2_2 = xQ
        b2_1 = poly_trim(
            poly_add(
                fq_add(a4, fq_mul(xQ, xQ, hq, p), hq, p),
                poly_add(
                    fq_mul(poly_scale(a2, 2, p), xQ, hq, p),
                    fq_neg(fq_mul(a1, yQ, hq, p), p),
                    p,
                ),
                p,
            ),
            p,
        )
        b2_0 = fq_add(poly_scale(a6, 2, p), fq_mul(a4, xQ, hq, p), hq, p)
        B2Q: PolyExt = pext_trim([b2_0, b2_1, b2_2], hq, p)

        X_poly: PolyExt = [[], [1]]
        X_minus_xQ: PolyExt = pext_trim([fq_neg(xQ, p), [1]], hq, p)
        X_minus_xQ_sq = pext_mul(X_minus_xQ, X_minus_xQ, hq, p)
        # X^q as a PolyExt of degree q
        Xq_poly: PolyExt = [[] for _ in range(q)] + [[1]]
        # U(X) = (X - xQ)^2 * X^q - B_{2,Q}(X)
        U_poly = pext_sub(pext_mul(X_minus_xQ_sq, Xq_poly, hq, p), B2Q, hq, p)
        # F(X) = X^3 + a2*X^2 + a4*X + a6
        F_poly: PolyExt = pext_trim([a6, a4, a2, [1]], hq, p)
        # Psi_Q(X, X^q) = U^2 + cQ * a1 * X * U - cQ^2 * F(X)
        cQa1 = fq_mul(cQ, a1, hq, p)
        cQ2 = fq_mul(cQ, cQ, hq, p)
        term1 = pext_mul(U_poly, U_poly, hq, p)
        term2 = pext_scale(pext_mul(X_poly, U_poly, hq, p), cQa1, hq, p)
        term3 = pext_scale(F_poly, cQ2, hq, p)
        GQ = pext_sub(pext_add(term1, term2, hq, p), term3, hq, p)
        if not GQ:
            continue
        GQ = pext_scale(GQ, fq_inv(GQ[-1], hq, p), hq, p)

        # Extract product of all degree-n irreducible factors via gcd(GQ, X^{q^n} - X) / gcd(GQ, X^{q^d} - X)
        xqn = pext_pow_mod(X_poly, q ** target_n, GQ, hq, p)
        prod_div_n = pext_gcd(GQ, pext_sub(xqn, X_poly, hq, p), hq, p)
        for pf in distinct_prime_factors_small(target_n):
            d_sub = target_n // pf
            xqd = pext_pow_mod(X_poly, q ** d_sub, prod_div_n, hq, p)
            g_sub = pext_gcd(prod_div_n, pext_sub(xqd, X_poly, hq, p), hq, p)
            if len(g_sub) - 1 > 0:
                prod_div_n = pext_divmod(prod_div_n, g_sub, hq, p)[0]
        if len(prod_div_n) - 1 < target_n:
            continue

        # Split out irreducible factor Mx of degree target_n and verify phi_q(I0) == I0 + Q!
        Mx = _split_equal_degree_fq(prod_div_n, target_n, hq, p)
        if len(Mx) - 1 != target_n or not is_irreducible_fq(Mx, hq, p):
            continue
        x0: PolyExt = [[], [1]]
        # y0 = cQ^{-1} * ((x0 - xQ)^2 * x0^q - B2Q(x0)) mod Mx
        x0_q = pext_pow_mod(x0, q, Mx, hq, p)
        u_mod = pext_sub(
            pext_mul_mod(pext_mod(X_minus_xQ_sq, Mx, hq, p), x0_q, Mx, hq, p),
            pext_mod(B2Q, Mx, hq, p),
            hq,
            p,
        )
        y0 = pext_mod(pext_scale(u_mod, cQ_inv, hq, p), Mx, hq, p)

        # Pick a witness translation P in E(F_q) with P != -Q and P != O_E
        trans_P: Optional[Tuple[PolyFp, PolyFp]] = None
        for pt in pts:
            if ec_add_fq(pt, Q, a1, a2, a4, hq, p) is not None and pt != Q:
                trans_P = pt
                break
        if trans_P is None:
            continue

        cert = {
            "schema": SCHEMA_ID,
            "mode": "ordinary_elliptic_lang_presentation",
            "cert_id": cert_id,
            "p": p,
            "hq_irred": hq,
            "a1": a1, "a2": a2, "a4": a4, "a6": a6,
            "claimed_NE": NE,
            "point_Q": [Q[0], Q[1]],
            "order_n": target_n,
            "Mx_irred": Mx,
            "I0_x": x0,
            "I0_y": y0,
            "trans_P": [trans_P[0], trans_P[1]],
        }
        # Verify immediately (handles sign +/- Q branch automatically; if -Q, negate Q!)
        try:
            verify_certificate(cert)
            return cert
        except Exception:
            continue
    raise RuntimeError(f"Could not construct Lang presentation for p={p}, r={r}, n={target_n}")


def build_mode2_certs() -> List[Dict[str, Any]]:
    return [
        _build_lang_presentation_exact("m2_lang_p2_f16_order5", p=2, r=4, target_n=5),
        _build_lang_presentation_exact("m2_lang_p3_f9_order5", p=3, r=2, target_n=5),
        _build_lang_presentation_exact("m2_lang_p5_f25_order5", p=5, r=2, target_n=5),
        _build_lang_presentation_exact("m2_lang_p7_f7_order5", p=7, r=1, target_n=5),
    ]


# =============================================================================
# Mode 3 Builder: Moore Determinants & Sparse F_{q0}-Affine Pencils (Lemmas 3.1 & 3.3)
# =============================================================================


def _build_linearized_pencil_cert(
    cert_id: str, p: int, s: int, t: int, N: int, r_moore: int
) -> Dict[str, Any]:
    deg_fq = s * t
    q0 = p ** s
    hq = find_monic_irred_fp(p, deg_fq)
    fq_elems = fq_all_elements(hq, p)
    fq0_elems = [u for u in fq_elems if fq_pow(u, q0, hq, p) == u]
    assert len(fq0_elems) == q0

    # Pick r_moore F_{q0}-linearly independent elements z_1, ..., z_r in F_q
    zs: List[PolyFp] = []
    span: List[PolyFp] = [[]]
    for u in fq_elems:
        if u not in span:
            zs.append(u)
            if len(zs) == r_moore:
                break
            new_span: List[PolyFp] = []
            for comb in span:
                for c in fq0_elems:
                    new_span.append(fq_add(comb, fq_mul(c, u, hq, p), hq, p))
            span = new_span
    assert len(zs) == r_moore

    M_moore = [[fq_pow(zs[i], q0 ** j, hq, p) for j in range(r_moore)] for i in range(r_moore)]
    det_moore = mat_det_fq(M_moore, hq, p)
    M_aff = [[[1]] + [fq_pow(zs[i], q0 ** j, hq, p) for j in range(r_moore - 1)] for i in range(r_moore)]
    det_aff = mat_det_fq(M_aff, hq, p)
    assert det_moore and det_aff

    # Construct an F_{q0}-linearized polynomial P_split(T) = prod_{v in V} (T - v) that splits COMPLETELY
    # over F_q on an N-dimensional F_{q0}-subspace V <= F_q, with nonzero T^{q0^N}, T^{q0^{N-1}}, T terms!
    # Pick N linearly independent basis vectors b_0, ..., b_{N-1} in F_q
    basis: List[PolyFp] = []
    v_span: List[PolyFp] = [[]]
    for u in fq_elems:
        if u not in v_span:
            basis.append(u)
            new_s: List[PolyFp] = []
            for comb in v_span:
                for c in fq0_elems:
                    new_s.append(fq_add(comb, fq_mul(c, u, hq, p), hq, p))
            v_span = new_s
            if len(basis) == N:
                break
    assert len(basis) == N and len(v_span) == q0 ** N

    # Build L_hom_split(T) = sum_{i=0}^N c_i T^{q0^i} via recursive subspace product:
    # Start with P_0(T) = T; given P_k vanishing on V_k, set a_k = P_k(b_k) != 0,
    # then P_{k+1}(T) = P_k(T)^{q0} - a_k^{q0 - 1} * P_k(T)!
    split_terms: Dict[int, PolyFp] = {0: [1]}
    for k in range(N):
        # Evaluate current linearized poly at basis[k]
        ak: PolyFp = []
        for idx, coeff in split_terms.items():
            ak = fq_add(ak, fq_mul(coeff, fq_pow(basis[k], q0 ** idx, hq, p), hq, p), hq, p)
        assert ak
        factor = fq_pow(ak, q0 - 1, hq, p)
        new_terms: Dict[int, PolyFp] = {}
        for idx, coeff in split_terms.items():
            # P_k(T)^{q0} has coeff^{q0} at idx + 1
            c_hi = fq_pow(coeff, q0, hq, p)
            new_terms[idx + 1] = fq_add(new_terms.get(idx + 1, []), c_hi, hq, p)
            # -factor * P_k(T) at idx
            c_lo = fq_neg(fq_mul(factor, coeff, hq, p), p)
            new_terms[idx] = fq_add(new_terms.get(idx, []), c_lo, hq, p)
        split_terms = {idx: c for idx, c in new_terms.items() if c}

    # Pick an affine shift rho0 in F_q and set d_split = -L_hom_split(rho0) so roots are rho0 + V <= F_q!
    rho0 = fq_elems[min(3, len(fq_elems) - 1)]
    d_split: PolyFp = []
    for idx, coeff in split_terms.items():
        d_split = fq_add(d_split, fq_mul(coeff, fq_pow(rho0, q0 ** idx, hq, p), hq, p), hq, p)
    d_split = fq_neg(d_split, p)

    # Now construct a genuine Lemma 3.3 pencil L_Z(T) = L_0(T) + Z * L_1(T) with z0 = [1] (or [0,1])
    # such that L_{z0}(T) = L_split(T) AND (A1)-(A4) hold!
    rng = random.Random(20261125 + 503 * q0 + 17 * N + deg_fq)
    z0: PolyFp = [0, 1]  # generator alpha of F_q
    for _ in range(500):
        L1_terms: Dict[str, PolyFp] = {}
        for idx in range(N + 1):
            c1 = rng.choice(fq_elems)
            if idx in (0, N - 1, N):
                while not c1:
                    c1 = rng.choice(fq_elems)
            if c1:
                L1_terms[str(idx)] = c1
        d1 = rng.choice([e for e in fq_elems if e])
        # L0 = L_split - z0 * L1
        L0_terms: Dict[str, PolyFp] = {}
        for idx in range(N + 1):
            cs = split_terms.get(idx, [])
            c1 = L1_terms.get(str(idx), [])
            c0 = fq_add(cs, fq_neg(fq_mul(z0, c1, hq, p), p), hq, p)
            if c0:
                L0_terms[str(idx)] = c0
        d0 = fq_add(d_split, fq_neg(fq_mul(z0, d1, hq, p), p), hq, p)
        cert = {
            "schema": SCHEMA_ID,
            "mode": "sparse_moore_linearized_pencil",
            "cert_id": cert_id,
            "p": p, "s": s, "t": t, "hq_irred": hq,
            "moore_z": zs,
            "claimed_moore_det": det_moore,
            "claimed_affine_moore_det": det_aff,
            "pencil_N": N,
            "pencil_L0_terms": L0_terms,
            "pencil_L1_terms": L1_terms,
            "pencil_delta0": d0,
            "pencil_delta1": d1,
            "splitting_z0": z0,
            "claimed_agl_order": str(agl_order_exact(q0, N)),
            "claimed_split_root_count": q0 ** N,
        }
        try:
            verify_certificate(cert)
            return cert
        except Exception:
            continue
    raise RuntimeError(f"Failed to build Mode 3 pencil {cert_id}")


def build_mode3_certs() -> List[Dict[str, Any]]:
    return [
        _build_linearized_pencil_cert("m3_pencil_p2_q0_4_N2", p=2, s=2, t=3, N=2, r_moore=3),
        _build_linearized_pencil_cert("m3_pencil_p2_q0_4_N3", p=2, s=2, t=4, N=3, r_moore=3),
        _build_linearized_pencil_cert("m3_pencil_p3_q0_3_N2", p=3, s=1, t=4, N=2, r_moore=3),
        _build_linearized_pencil_cert("m3_pencil_p5_q0_5_N2", p=5, s=1, t=3, N=2, r_moore=3),
    ]


# =============================================================================
# Mode 4 Builder: Factoring-Free SL_2(Z) Composite Solver & Thm. 1.2 Probes
# =============================================================================


def _build_unimodular_cert(
    cert_id: str,
    p: int, n: int, ML: int, K: int, R: int,
    want_nonmem: bool,
    p_probe: int, ell2: int,
) -> Dict[str, Any]:
    f = find_monic_irred_fp(p, n)
    gen = find_primitive_element(p, f)
    order = p ** n - 1
    assert order % ML == 0
    cofac = order // ML
    gamma = poly_pow_mod(gen, cofac, f, p)
    rng = random.Random(20261125 + ML + 31 * K + p_probe)

    # Secret discrete logs y_j of factor-base elements delta_j = gamma^{y_j} in G_L
    y_true = [rng.randrange(1, ML) for _ in range(K)]
    deltas = [poly_pow_mod(gamma, yj, f, p) for yj in y_true]

    # Build a full-row-span overdetermined relation matrix E in (Z/ML Z)^{R x K}
    # using Cogentic Lemma 6.3(1)'s basis-shifted construction (u_t and b_j + v_{j,s})!
    while True:
        E_mat: List[List[int]] = []
        a_vec: List[int] = []
        for r_idx in range(R):
            row = [rng.randrange(ML) for _ in range(K)]
            if r_idx < K:
                row[r_idx] = (row[r_idx] + 1) % ML
            ar = sum(row[j] * y_true[j] for j in range(K)) % ML
            E_mat.append(row)
            a_vec.append(ar)
        y_sol = solve_mod_m_unimodular(ML, E_mat, a_vec)
        if y_sol == y_true:
            break

    # Pick a prime divisor d_sub of ML for subgroup structure testing
    pfs_ML = distinct_prime_factors_small(ML)
    d_sub = pfs_ML[0]

    # Build g_L and h_L as factor-base products
    while True:
        e_g = [rng.randrange(ML) for _ in range(K)]
        Yg = sum(e_g[j] * y_true[j] for j in range(K)) % ML
        if want_nonmem:
            if Yg % d_sub == 0 and Yg != 0:
                break
        else:
            if gcd_int(Yg, ML) == 1:
                break

    while True:
        e_h = [rng.randrange(ML) for _ in range(K)]
        Yh = sum(e_h[j] * y_true[j] for j in range(K)) % ML
        Dg, sg, _ = xgcd_int(Yg, ML)
        if want_nonmem:
            if Yh % Dg != 0:
                break
        else:
            if Yh % Dg == 0 and Yh != 0:
                break

    def _prod(exps: List[int]) -> PolyFp:
        acc: PolyFp = [1]
        for j in range(K):
            if exps[j]:
                acc = poly_mul_mod(acc, poly_pow_mod(deltas[j], exps[j], f, p), f, p)
        return acc

    gL = _prod(e_g)
    hL = _prod(e_h)
    Dg, sg, _ = xgcd_int(Yg, ML)
    if want_nonmem:
        sub_v = "NOT_IN_SUBGROUP"
        sub_w = ML // Dg
    else:
        sub_v = "LOG"
        sub_w = (sg * (Yh // Dg)) % ML

    # Theorem 1.2(2) exact integer parameter probe at ell_2
    ell3 = floor_log2_int(ell2)
    ellp = ceil_log2_int(p_probe)
    s_ex = max(3, (ell3 * ell3 + ellp - 1) // ellp)
    B_ex = ell2 // (32 * s_ex * ellp)
    m_ex = 2 * B_ex + 4

    return {
        "schema": SCHEMA_ID,
        "mode": "unimodular_composite_dlp_solver",
        "cert_id": cert_id,
        "p": p, "n": n, "f_irred": f,
        "M_L": str(ML),
        "gamma": gamma,
        "deltas": deltas,
        "rel_matrix_E": [[str(v) for v in row] for row in E_mat],
        "rel_rhs_a": [str(v) for v in a_vec],
        "claimed_y": [str(v) for v in y_sol],
        "g_L": gL, "h_L": hL,
        "e_g": [str(v) for v in e_g],
        "e_h": [str(v) for v in e_h],
        "subgroup_verdict": sub_v,
        "subgroup_witness": str(sub_w),
        "thm12_param_probe": {
            "p_probe": p_probe,
            "ell2_log2_ell1": ell2,
            "claimed_ell3": ell3,
            "claimed_ellp": ellp,
            "claimed_s": s_ex,
            "claimed_B": B_ex,
            "claimed_m": m_ex,
        },
    }


def build_mode4_certs() -> List[Dict[str, Any]]:
    # 5^10 - 1 = 9765624 = 24 * 406901 = 24 * 11 * 71 * 521 -> ML = 11 * 71 * 521 = 406901!
    # 2^20 - 1 = 1048575 = 75 * 13981 (13981 = 11 * 31 * 41)
    # 3^12 - 1 = 531440 = 80 * 6643 (6643 = 7 * 13 * 73)
    # 2^16 - 1 = 65535 = 15 * 4369 (4369 = 17 * 257)
    return [
        _build_unimodular_cert("m4_unimodular_f2_16_composite_log", 2, 16, 4369, 4, 8, False, 2, 25088),
        _build_unimodular_cert("m4_unimodular_f3_12_composite_nonmem", 3, 12, 6643, 4, 8, True, 3, 40000),
        _build_unimodular_cert("m4_unimodular_f2_20_composite_log", 2, 20, 13981, 5, 10, False, 5, 65536),
        _build_unimodular_cert("m4_unimodular_f5_10_composite_nonmem", 5, 10, 406901, 5, 10, True, 7, 131072),
    ]


def main() -> None:
    CERT_DIR.mkdir(parents=True, exist_ok=True)
    RES_DIR.mkdir(parents=True, exist_ok=True)

    all_certs = (
        build_mode1_certs()
        + build_mode2_certs()
        + build_mode3_certs()
        + build_mode4_certs()
    )
    assert len(all_certs) == 16

    atlas_rows: List[Dict[str, Any]] = []
    for cert in all_certs:
        path = CERT_DIR / f"{cert['cert_id']}.cert.json"
        path.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        # Warm-up + 7 exact timed runs
        res = verify_certificate_file(path)
        assert res["verified"] is True
        times_ms: List[float] = []
        for _ in range(7):
            t0 = time.perf_counter()
            verify_certificate_file(path)
            times_ms.append((time.perf_counter() - t0) * 1000.0)
        atlas_rows.append({
            "cert_id": cert["cert_id"],
            "mode": cert["mode"],
            "mean_ms": round(statistics.mean(times_ms), 3),
            "summary": res,
        })
        print(f"[CERT] {cert['cert_id']:38s} | {atlas_rows[-1]['mean_ms']:7.3f} ms | {res}")

    # Exp 1: 16-certificate atlas
    (RES_DIR / "exp1_certificate_atlas.json").write_text(
        json.dumps({"schema": SCHEMA_ID, "count": len(atlas_rows), "certificates": atlas_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # Exp 2: Monodromy comparison |AGL_N(F_{q0})| vs |S_{q0^N}| (why linearized pencils shatter the S_q barrier!)
    import math
    mono_rows: List[Dict[str, Any]] = []
    for q0 in [3, 4, 5, 8]:
        for N in [2, 3, 4, 5, 6]:
            deg = q0 ** N
            agl = agl_order_exact(q0, N)
            log10_agl = math.log10(agl)
            # Stirling exact lgamma for log10((q0^N)!)
            log10_sym = math.lgamma(deg + 1) / math.log(10.0)
            mono_rows.append({
                "q0": q0, "N": N, "degree_q0_N": deg,
                "log10_AGL": round(log10_agl, 4),
                "log10_Sym": round(log10_sym, 4),
                "compression_ratio_log10": round(log10_sym / log10_agl, 4),
            })
    (RES_DIR / "exp2_monodromy_compression.json").write_text(
        json.dumps({"rows": mono_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # Exp 3: Exact Theorem 1.2(2) onset threshold & B(ell_2), s(ell_2) sweep across p in {2, 3, 5, 7}
    onset_rows: List[Dict[str, Any]] = []
    for p_pr in [2, 3, 5, 7]:
        ellp = ceil_log2_int(p_pr)
        first_B4 = None
        for ell2 in range(1024, 40000):
            ell3 = floor_log2_int(ell2)
            s_ex = max(3, (ell3 * ell3 + ellp - 1) // ellp)
            B_ex = ell2 // (32 * s_ex * ellp)
            if B_ex >= 4:
                first_B4 = {
                    "p": p_pr, "ell_p": ellp, "first_ell2_B_ge_4": ell2,
                    "ell_3": ell3, "s": s_ex, "B": B_ex, "m": 2 * B_ex + 4,
                    "cofactor_cap_ratio": round((8 * (2 * B_ex + 4) * s_ex * ellp) / ell2, 4),
                }
                break
        onset_rows.append(first_B4)
    sweep_ell2: List[Dict[str, Any]] = []
    for k_pow in range(10, 23):
        ell2 = 1 << k_pow
        row: Dict[str, Any] = {"ell2": ell2, "ell3": k_pow}
        for p_pr in [2, 3, 5]:
            ellp = ceil_log2_int(p_pr)
            s_ex = max(3, (k_pow * k_pow + ellp - 1) // ellp)
            B_ex = ell2 // (32 * s_ex * ellp)
            row[f"B_p{p_pr}"] = B_ex
            row[f"s_p{p_pr}"] = s_ex
        sweep_ell2.append(row)
    (RES_DIR / "exp3_thm12_parameter_onset.json").write_text(
        json.dumps({"first_onset_B_ge_4": onset_rows, "dyadic_sweep": sweep_ell2}, indent=2) + "\n",
        encoding="utf-8",
    )

    # Exp 4: Exact SolveModM unimodular scaling across composite moduli (K = 2..12, R = 2K)
    rng = random.Random(20261125)
    unimod_rows: List[Dict[str, Any]] = []
    M_test = 17 * 257 * 65537 * 13 * 37  # 137,725,284,593 (38-bit unfactored composite)
    for K in [2, 4, 6, 8, 10, 12]:
        R = 2 * K
        y_t = [rng.randrange(1, M_test) for _ in range(K)]
        while True:
            E_m = [[rng.randrange(M_test) for _ in range(K)] for _ in range(R)]
            for idx in range(K):
                E_m[idx][idx] = (E_m[idx][idx] + 1) % M_test
            a_v = [sum(E_m[r_i][j] * y_t[j] for j in range(K)) % M_test for r_i in range(R)]
            if solve_mod_m_unimodular(M_test, E_m, a_v) == y_t:
                break
        ts: List[float] = []
        for _ in range(7):
            t0 = time.perf_counter()
            out = solve_mod_m_unimodular(M_test, E_m, a_v)
            ts.append((time.perf_counter() - t0) * 1000.0)
            assert out == y_t
        unimod_rows.append({"K": K, "R": R, "M_bits": M_test.bit_length(), "mean_ms": round(statistics.mean(ts), 3)})
    (RES_DIR / "exp4_unimodular_scaling.json").write_text(
        json.dumps({"M_composite": str(M_test), "rows": unimod_rows}, indent=2) + "\n",
        encoding="utf-8",
    )
    print("[PASS] All 16 canonical DLP-COGENTIC-CERT-1.0 certs and 4 exact result JSONs generated!")


if __name__ == "__main__":
    main()
