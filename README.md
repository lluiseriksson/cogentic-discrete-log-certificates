# Constructive Lean 4 Kernel and Exact Zero-Float Certificates for Google Research Cogentic's Sub-Quasi-Polynomial Discrete Logarithm Proof

**Author:** Lluis Eriksson (prepared with transparent AI assistance via Google Antigravity)
**Target Reference:** Google Research Cogentic (Nov. 25, 2026), *Discrete Logarithms in Finite Fields of Fixed Characteristic in Sub-Quasi-Polynomial Time* (`github.com/google-research/google-research/tree/master/cogentic_research_papers/discrete_logarithm`, harness `arXiv:2609.40324`).
**Licenses:** Manuscript & figures (`paper/main.tex`, `paper/main.pdf`, `paper/figures/*.png`) under `CC-BY-4.0`; code, Lean 4 proofs, and exact certificates under `MIT`.

## Highlights
- **Zero-Dependency Constructive Lean 4.35.0 Kernel (`lean/CogenticDiscreteLog.lean`):** 18 theorems, `0` `sorry`, `0` `axiom`, `0` `Classical.choice`, `0` warnings (`1` zero-axiom `none`, `2` `[propext]`, `15` `[propext, Quot.sound]`), mechanizing Definition 1.1 non-membership soundness, Lemmas 3.1–3.4 (Moore/affine-Moore reductions, transvection $\mathrm{SL}_2$ generation, Möbius adjugate, $H^1(\mathrm{GL}(V),V)=0$ coboundary, $q_0\ge 3$ degree gap, Jordan transposition conjugation), Lemmas 4.1–4.2 (Waterhouse coprimality, parallelogram Cauchy–Schwarz), Lemma 5.1 (exact constant-field pinch & Castelnuovo induction), Lemmas 6.2–6.4 ($B$-adic tree bound, $\mathrm{SL}_2(\mathbb{Z})$ unimodular elimination, non-membership exponent), Sec. 6.2 CRT recombination, and Theorem 1.2 discrete guards.
- **Exact Zero-Float Auditor (`DLP-COGENTIC-CERT-1.0`, `src/dlp_certifier.py`):** Pure-stdlib Python `int` verifier across four modes, certifying 16 canonical witnesses (`1.133–36.640 ms`)—including live exact ordinary elliptic Lang-isogeny presentations $\phi_q(I_0) = I_0 + Q$ and $x_P(I_0)^q = \tilde{x}_P(I_0)$ across all characteristics $p \in \{2, 3, 5, 7\}$, Moore/affine-Moore determinants & splitting sparse $\mathbb{F}_{q_0}$-affine pencils, and factoring-free $\mathrm{SL}_2(\mathbb{Z})$ solves modulo unfactored composites up to $M_L = 406{,}901$—and rejecting **61/61 live adversarial forgeries** with exact branch regex assertions (`65/65` pytest tests).

## Quick Reproduction
```bash
# Run all 5 verification gates (zero-float hygiene, Lean 4 axiom audit, 16 certs, 65 pytest, 41-file SHA-256)
python scripts/verify_all.py

# Optional: regenerate all 16 certificates, 4 exact result JSONs, and 3 300-DPI figures
python scripts/run_all_experiments.py
python scripts/make_figures.py
```
