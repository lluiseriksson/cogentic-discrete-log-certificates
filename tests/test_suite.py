"""64-test pytest suite (1 test covering all 16 canonical certs + 3 raw-JSON parser tests
+ 60 parametrized live adversarial forgery attacks, with exact branch regex assertions) for
Paper 59 (DLP-COGENTIC-CERT-1.0).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any, Callable, Dict, List, Tuple

import pytest

from src.dlp_certifier import (
    CertificateError,
    verify_certificate,
    verify_certificate_file,
    verify_certificate_json_text,
)

ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = ROOT / "certificates"


def _load(stem: str) -> Dict[str, Any]:
    return json.loads((CERT_DIR / f"{stem}.cert.json").read_text(encoding="utf-8"))


def test_all_16_canonical_certificates_pass() -> None:
    paths = sorted(CERT_DIR.glob("*.cert.json"))
    assert len(paths) == 16
    for p in paths:
        res = verify_certificate_file(p)
        assert res["verified"] is True


def test_raw_json_rejects_ieee754_float() -> None:
    raw = json.dumps(_load("m1_dlp_f2_16_log_crt")).replace('"p": 2', '"p": 2.0', 1)
    with pytest.raises(CertificateError, match="floating-point"):
        verify_certificate_json_text(raw)


def test_raw_json_rejects_nan_infinity() -> None:
    raw = '{"schema": "DLP-COGENTIC-CERT-1.0", "mode": "dlp_zero_error_certificate", "cert_id": "x", "p": NaN}'
    with pytest.raises(CertificateError, match="Non-finite"):
        verify_certificate_json_text(raw)


def test_raw_json_rejects_duplicate_keys() -> None:
    raw = '{"schema": "DLP-COGENTIC-CERT-1.0", "schema": "DLP-COGENTIC-CERT-1.0", "mode": "dlp_zero_error_certificate", "cert_id": "x"}'
    with pytest.raises(CertificateError, match="Duplicate"):
        verify_certificate_json_text(raw)


def _build_60_attacks() -> List[Tuple[str, str, Callable[[], Dict[str, Any]]]]:
    m1_log = _load("m1_dlp_f2_16_log_crt")
    m1_non = _load("m1_dlp_f2_20_not_in_subgroup")
    m2_p2 = _load("m2_lang_p2_f16_order5")
    m2_p3 = _load("m2_lang_p3_f9_order5")
    m2_p7 = _load("m2_lang_p7_f7_order5")
    m3 = _load("m3_pencil_p2_q0_4_N2")
    m4_log = _load("m4_unimodular_f2_16_composite_log")
    m4_non = _load("m4_unimodular_f3_12_composite_nonmem")

    def mod(base: Dict[str, Any], fn: Callable[[Dict[str, Any]], None]) -> Callable[[], Dict[str, Any]]:
        def _run() -> Dict[str, Any]:
            c = copy.deepcopy(base)
            fn(c)
            return c
        return _run

    def _m2_supersingular(c: Dict[str, Any]) -> None:
        # Over F_7, y^2 = x^3 + 1 has NE = 12? Wait: y^2 = x^3 + x has trace 0 (NE = 8, 7 | 7+1-8 = 0) -> supersingular!
        c["a4"] = [1]
        c["a6"] = []
        c["claimed_NE"] = 8

    def _m2_singular_p7(c: Dict[str, Any]) -> None:
        c["a4"] = []
        c["a6"] = []

    def _m2_bad_lang_I0(c: Dict[str, Any]) -> None:
        # Negate I0_y on p=7 (still on curve y^2 = x^3 + a4*x + a6, but satisfies phi_q(-I0) = -I0 - Q != -I0 + Q!)
        c["I0_y"] = [[(-coeff) % 7 for coeff in poly] if poly else [] for poly in c["I0_y"]]

    def _m3_break_A1(c: Dict[str, Any]) -> None:
        # Set L0_terms["0"] = L1_terms["0"] = [] so Delta_1 = 0
        c["pencil_L0_terms"]["0"] = []
        c["pencil_L1_terms"]["0"] = []

    def _m3_break_A2(c: Dict[str, Any]) -> None:
        c["pencil_L0_terms"]["1"] = []
        c["pencil_L1_terms"]["1"] = []

    def _m3_break_A3(c: Dict[str, Any]) -> None:
        # Make L1 homogeneous proportional to L0? That breaks A1/A2 first.
        # Instead keep A1, A2 nonzero? If N=2, A0(T) and A1(T) share a root iff we multiply both by common factor?
        # Easier: take a nonzero F_q element u0 and adjust L0_terms["0"] so A0(u0)=0 and A1(u0)=0?
        # Even simpler: check m3_pencil_p3_q0_3_N2 (q0=3, N=2) or set A0(1) = A1(1) = 0 -> gcd has (T-1)!
        # For p=2, q0=4, N=2: A_r(T) = a_{r,2} T^{15} + a_{r,1} T^3 + a_{r,0}. At T=1, A_r(1) = a_{r,2} + a_{r,1} + a_{r,0}!
        # Pick a_{0,2}=1, a_{0,1}=1, a_{0,0}=0 (Wait: sum=0 in F_2!), and a_{1,2}=1, a_{1,1}=[0,1], a_{1,0}=[1,1] (sum=0 in F_2)!
        # Check Delta_1 = 1*[1,1] - 1*0 = [1,1] != 0! Check Delta_2 = 1*[0,1] - 1*1 = [1,1] != 0!
        # And A_0(1) = 1+1+0 = 0, A_1(1) = 1 + x + (1+x) = 0 => (T - 1) | gcd(A0, A1)!
        c["pencil_L0_terms"] = {"2": [1], "1": [1]}
        c["pencil_L1_terms"] = {"2": [1], "1": [0, 1], "0": [1, 1]}

    def _m3_break_A4(c: Dict[str, Any]) -> None:
        # Make L0(0) = L1(0) = 0 (delta0 = delta1 = []) while A0, A1 remain coprime -> T | gcd(L0, L1)!
        c["pencil_delta0"] = []
        c["pencil_delta1"] = []

    def _m4_rank_deficient_E(c: Dict[str, Any]) -> None:
        # Duplicate row 0 across all rows: every multiplicative relation holds in F_{2^16}^x,
        # yet rank(E) = 1 < K = 4 so SolveModM fails cleanly!
        row0 = list(c["rel_matrix_E"][0])
        a0 = c["rel_rhs_a"][0]
        c["rel_matrix_E"] = [list(row0) for _ in c["rel_matrix_E"]]
        c["rel_rhs_a"] = [a0 for _ in c["rel_rhs_a"]]

    attacks: List[Tuple[str, str, Callable[[], Dict[str, Any]]]] = [
        # --- 12 Schema / Parser / AST Attacks ---
        ("S01_wrong_schema", "Unsupported schema", mod(m1_log, lambda c: c.__setitem__("schema", "DLP-0.9"))),
        ("S02_unknown_mode", "Unknown verification mode", mod(m1_log, lambda c: c.__setitem__("mode", "bogus"))),
        ("S03_empty_cert_id", "cert_id", mod(m1_log, lambda c: c.__setitem__("cert_id", "   "))),
        ("S04_bool_in_int_field", "strict int", mod(m1_log, lambda c: c.__setitem__("p", True))),
        ("S05_plus_int_str", "leading '\\+'", mod(m1_log, lambda c: c.__setitem__("witness_int", "+41927"))),
        ("S06_neg_zero_int_str", "negative zero", mod(m1_log, lambda c: c.__setitem__("witness_int", "-0"))),
        ("S07_leading_zero_int_str", "leading zeros", mod(m1_log, lambda c: c.__setitem__("witness_int", "041927"))),
        ("S08_unicode_digit_int_str", "ASCII digits", mod(m1_log, lambda c: c.__setitem__("witness_int", "٤١٩٢٧"))),
        ("S09_int_in_int_str", "decimal integer str", mod(m1_log, lambda c: c.__setitem__("witness_int", 41927))),
        ("S10_oversized_str", "exceeds cap", mod(m1_log, lambda c: c.__setitem__("witness_int", "1" + "0" * 2005))),
        ("S11_trailing_zero_poly", "trailing zero", mod(m1_log, lambda c: c["g"].append(0))),
        ("S12_extra_key", "schema key mismatch", mod(m1_log, lambda c: c.__setitem__("extra", 1))),

        # --- 12 Mode 1 (Definition 1.1 & Sec. 6.2 Zero-Error DLP) Forgeries ---
        ("M1_01_composite_p", "must be a prime", mod(m1_log, lambda c: c.__setitem__("p", 4))),
        ("M1_02_reducible_f", "not irreducible", mod(m1_log, lambda c: c.__setitem__("f_irred", [0] * 16 + [1]))),
        ("M1_03_wrong_deg_f", "monic of exact degree", mod(m1_log, lambda c: c.__setitem__("f_irred", [1, 1]))),
        ("M1_04_zero_g", "nonzero elements", mod(m1_log, lambda c: c.__setitem__("g", []))),
        ("M1_05_bad_verdict", "verdict must be", mod(m1_log, lambda c: c.__setitem__("verdict", "MAYBE"))),
        ("M1_06_log_x_out_of_range", "0 <= x <= p\\^n - 2", mod(m1_log, lambda c: c.__setitem__("witness_int", "65535"))),
        ("M1_07_forged_log_x", "g\\^x != h", mod(m1_log, lambda c: c.__setitem__("witness_int", "41928"))),
        ("M1_08_nonmem_E_zero", "1 <= E <= p\\^n - 1", mod(m1_non, lambda c: c.__setitem__("witness_int", "0"))),
        ("M1_09_nonmem_gE_ne_1", "g\\^E != 1", mod(m1_non, lambda c: c.__setitem__("witness_int", "209714"))),
        ("M1_10_nonmem_hE_eq_1", "h\\^E == 1", mod(m1_non, lambda c: c.__setitem__("witness_int", "1048575"))),
        ("M1_11_crt_bad_bezout", "Bezout identity", mod(m1_log, lambda c: c["crt_audit"].__setitem__("sigS", "0"))),
        ("M1_12_crt_bad_xS", "g_S\\^\\{xS\\} != h_S", mod(m1_log, lambda c: c["crt_audit"].__setitem__("xS", "0"))),

        # --- 12 Mode 2 (Lemma 4.1 & Eq. (1.2) Ordinary Elliptic Lang Presentation) Forgeries ---
        ("M2_01_bad_p2_canonical", "Canonical p=2", mod(m2_p2, lambda c: c.__setitem__("a1", []))),
        ("M2_02_bad_p3_canonical", "Canonical p=3", mod(m2_p3, lambda c: c.__setitem__("a2", []))),
        ("M2_03_singular_p7", "Curve is singular", mod(m2_p7, _m2_singular_p7)),
        ("M2_04_forged_NE", "claimed_NE mismatch", mod(m2_p7, lambda c: c.__setitem__("claimed_NE", 6))),
        ("M2_05_supersingular_p7", "supersingular", mod(m2_p7, _m2_supersingular)),
        ("M2_06_Q_not_on_curve", "point_Q is not on", mod(m2_p7, lambda c: c["point_Q"].__setitem__(1, []))),
        ("M2_07_Q_wrong_order", "\\[n\\]Q != O_E", mod(m2_p7, lambda c: c.__setitem__("order_n", 4))),
        ("M2_08_Mx_reducible", "not irreducible over F_q", mod(m2_p7, lambda c: c.__setitem__("Mx_irred", [[], [], [], [], [], [1]]))),
        ("M2_09_I0_not_on_curve", "I0 is not on", mod(m2_p7, lambda c: c["I0_y"].__setitem__(0, [1]))),
        ("M2_10_lang_eq12_sign_flip", "Lang isogeny Eq\\. \\(1\\.2\\) failed", mod(m2_p7, _m2_bad_lang_I0)),
        ("M2_11_trans_P_off_curve", "trans_P is not on", mod(m2_p7, lambda c: c["trans_P"].__setitem__(1, []))),
        ("M2_12_reducible_hq", "hq_irred must be monic irreducible", mod(m2_p2, lambda c: c.__setitem__("hq_irred", [0, 0, 0, 0, 1]))),

        # --- 12 Mode 3 (Lemmas 3.1 & 3.3 Moore Determinants & Sparse Linearized Pencils) Forgeries ---
        ("M3_01_q0_lt_3", "q0 = p\\^s >= 3", mod(m3, lambda c: (c.__setitem__("s", 1), c.__setitem__("t", 6)))),
        ("M3_02_moore_dependent", "linearly dependent", mod(m3, lambda c: c["moore_z"].__setitem__(1, c["moore_z"][0]))),
        ("M3_03_forged_moore_det", "claimed_moore_det", mod(m3, lambda c: c.__setitem__("claimed_moore_det", [0, 1]))),
        ("M3_04_forged_aff_det", "claimed_affine_moore_det", mod(m3, lambda c: c.__setitem__("claimed_affine_moore_det", [0, 1]))),
        ("M3_05_break_A1", "hypothesis \\(A1\\) failed", mod(m3, _m3_break_A1)),
        ("M3_06_break_A2", "hypothesis \\(A2\\) failed", mod(m3, _m3_break_A2)),
        ("M3_07_break_A3", "hypothesis \\(A3\\) failed", mod(m3, _m3_break_A3)),
        ("M3_08_break_A4", "hypothesis \\(A4\\) failed", mod(m3, _m3_break_A4)),
        ("M3_09_bad_split_z0", "does not split completely", mod(m3, lambda c: c.__setitem__("splitting_z0", [1]))),
        ("M3_10_forged_agl_order", "claimed_agl_order", mod(m3, lambda c: c.__setitem__("claimed_agl_order", "2881"))),
        ("M3_11_forged_root_count", "claimed_split_root_count", mod(m3, lambda c: c.__setitem__("claimed_split_root_count", 15))),
        ("M3_12_bad_pencil_N", "pencil_N must be in", mod(m3, lambda c: c.__setitem__("pencil_N", 1))),

        # --- 12 Mode 4 (Lemmas 6.3, 6.4 & Thm. 1.2 Unimodular Composite Solver) Forgeries ---
        ("M4_01_ML_not_divisor", "divide p\\^n - 1", mod(m4_log, lambda c: c.__setitem__("M_L", "4370"))),
        ("M4_02_gamma_bad_order", "gamma\\^\\{M_L\\} != 1", mod(m4_log, lambda c: c.__setitem__("gamma", [0, 1]))),
        ("M4_03_rel_row_mismatch", "Multiplicative relation row", mod(m4_log, lambda c: c["rel_rhs_a"].__setitem__(0, "0"))),
        ("M4_04_rank_deficient_E", "SolveModM failed", mod(m4_log, _m4_rank_deficient_E)),
        ("M4_05_forged_claimed_y", "claimed_y mismatch", mod(m4_log, lambda c: c["claimed_y"].__setitem__(0, "0"))),
        ("M4_06_bad_e_g_decomp", "decomposition failed for g_L", mod(m4_log, lambda c: c["e_g"].__setitem__(0, "0"))),
        ("M4_07_forged_sub_log", "g_L\\^\\{xL\\} != h_L", mod(m4_log, lambda c: c.__setitem__("subgroup_witness", "1"))),
        ("M4_08_forged_sub_nonmem", "subgroup_witness Eg mismatch", mod(m4_non, lambda c: c.__setitem__("subgroup_witness", "1"))),
        ("M4_09_wrong_sub_verdict_log", "Dg does not divide Yh", mod(m4_non, lambda c: c.__setitem__("subgroup_verdict", "LOG"))),
        ("M4_10_wrong_sub_verdict_nonmem", "Dg divides Yh", mod(m4_log, lambda c: c.__setitem__("subgroup_verdict", "NOT_IN_SUBGROUP"))),
        ("M4_11_thm12_B_below_4", "requires ell3 >= 10 and B >= 4", mod(m4_log, lambda c: c["thm12_param_probe"].__setitem__("ell2_log2_ell1", 25087))),
        ("M4_12_thm12_forged_B", "claimed_B mismatch", mod(m4_log, lambda c: c["thm12_param_probe"].__setitem__("claimed_B", 5))),
        ("M4_13_trivial_gamma_one", "gamma must be nontrivial", mod(m4_log, lambda c: c.__setitem__("gamma", [1]))),
    ]
    assert len(attacks) == 61
    return attacks


@pytest.mark.parametrize("name,pattern,builder", _build_60_attacks(), ids=[a[0] for a in _build_60_attacks()])
def test_live_adversarial_forgery_rejected(
    name: str,
    pattern: str,
    builder: Callable[[], Dict[str, Any]],
) -> None:
    forged = builder()
    with pytest.raises(CertificateError, match=pattern):
        verify_certificate(forged)
