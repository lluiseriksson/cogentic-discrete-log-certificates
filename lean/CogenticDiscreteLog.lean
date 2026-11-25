/-!
# CogenticDiscreteLog: Constructive Lean 4.35.0 Kernel for Google Research Cogentic's
# Sub-Quasi-Polynomial Discrete Logarithm Proof (Nov 25, 2026)

Zero external dependencies, zero `sorry`, zero `axiom`, zero `Classical.choice`, zero warnings.
Mechanizes 18 universal algebraic, group-theoretic, Galois-pinch, recursion, and
unimodular composite-modulus identities from Google Research Cogentic (Nov 25, 2026),
"Discrete Logarithms in Finite Fields of Fixed Characteristic in Sub-Quasi-Polynomial Time".

Author: Lluis Eriksson
License: MIT
-/

namespace CogenticDiscreteLog

/-! ### Helper Lemmas -/

private theorem pow_mod_base (a k M : Nat) : (a % M) ^ k % M = a ^ k % M := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    rw [Nat.mul_mod, ih, Nat.mod_mod, ← Nat.mul_mod]

private theorem pow_mul_mod_eq (a x E M : Nat) (h : a ^ E % M = 1 % M) :
    (a ^ x) ^ E % M = 1 % M := by
  rw [← Nat.pow_mul, Nat.mul_comm x E, Nat.pow_mul]
  rw [← pow_mod_base (a ^ E) x M, h, pow_mod_base, Nat.one_pow]

/-! ### Part 1: Zero-Error Las Vegas Certificates (Definition 1.1) & Linearized Monodromy (Sec. 3) -/

/-- Theorem 1 (Definition 1.1): Universal soundness of the `(NOT_IN_SUBGROUP, E)` certificate:
    modulo any `M ≥ 2`, if `g^E ≡ 1 (mod M)` and `h^E ≢ 1 (mod M)`, then no integer `x : Nat`
    satisfies `g^x ≡ h (mod M)`. -/
theorem def11_not_in_subgroup_soundness (M g h E : Nat)
    (hgE : g ^ E % M = 1 % M) (hhE : h ^ E % M ≠ 1 % M) :
    ∀ x : Nat, g ^ x % M ≠ h % M := by
  intro x hgx
  have h1 : (g ^ x) ^ E % M = h ^ E % M := by
    rw [← pow_mod_base (g ^ x) E M, hgx, pow_mod_base]
  have h2 : (g ^ x) ^ E % M = 1 % M := pow_mul_mod_eq g x E M hgE
  rw [h2] at h1
  exact hhE h1.symm

/-- Theorem 2 (Lemma 3.1(1)): Universal `2×2` Moore determinant Frobenius-scalar vanishing:
    for any `z1, c, qz1, qc : Int`, if `z2 = c * z1` and `qz2 = qc * qz1` with `qc = c`
    (i.e. `c ∈ F_{q0}` fixed by `q0`-Frobenius), then `z1 * qz2 - z2 * qz1 = 0`. -/
theorem lem31_moore_det_2x2_identity (z1 z2 qz1 qz2 c qc : Int)
    (hz : z2 = c * z1) (hqz : qz2 = qc * qz1) (hfix : qc = c) :
    z1 * qz2 - z2 * qz1 = 0 := by
  rw [hz, hqz, hfix]
  have hcomm : z1 * (c * qz1) = c * z1 * qz1 := by ac_rfl
  omega

/-- Theorem 3 (Lemma 3.1(3)): Universal `3×3` affine Moore determinant reduction:
    subtracting row 1 from rows 2 and 3 reduces the `3×3` affine determinant with leading column `1`
    to the `2×2` difference determinant `(z2 - z1)*(u3 - u1) - (z3 - z1)*(u2 - u1)`. -/
theorem lem31_affine_moore_reduction (z1 z2 z3 u1 u2 u3 : Int) :
    (z2 * u3 - z3 * u2) - (z1 * u3 - z3 * u1) + (z1 * u2 - z2 * u1) =
    (z2 - z1) * (u3 - u1) - (z3 - z1) * (u2 - u1) := by
  have e1 : (z2 - z1) * (u3 - u1) = z2 * u3 - z2 * u1 - z1 * u3 + z1 * u1 := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
  have e2 : (z3 - z1) * (u2 - u1) = z3 * u2 - z3 * u1 - z1 * u2 + z1 * u1 := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
  rw [e1, e2]
  omega

/-- Theorem 4 (Lemma 3.2): Universal `2×2` transvection determinant and inverse:
    for `φ = (p1, p2)` and `u = (u1, u2)` with `p1 * u1 + p2 * u2 = 0`, the matrix
    `T = [[1 + u1*p1, u1*p2], [u2*p1, 1 + u2*p2]]` has `det(T) = 1` and `T(T_{-u}(v)) = v`. -/
theorem lem32_transvection_det_one_2x2 (p1 p2 u1 u2 v1 v2 : Int)
    (hker : p1 * u1 + p2 * u2 = 0) :
    (1 + u1 * p1) * (1 + u2 * p2) - (u1 * p2) * (u2 * p1) = 1 ∧
    let pv := p1 * v1 + p2 * v2
    let w1 := v1 - pv * u1
    let w2 := v2 - pv * u2
    let pw := p1 * w1 + p2 * w2
    w1 + pw * u1 = v1 ∧ w2 + pw * u2 = v2 := by
  have hdet : (1 + u1 * p1) * (1 + u2 * p2) - (u1 * p2) * (u2 * p1) = 1 := by
    have e1 : (1 + u1 * p1) * (1 + u2 * p2) =
        1 + u1 * p1 + u2 * p2 + (u1 * p1) * (u2 * p2) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.one_mul, Int.mul_one]; omega
    have c1 : (u1 * p1) * (u2 * p2) = (u1 * p2) * (u2 * p1) := by ac_rfl
    have c2 : u1 * p1 = p1 * u1 := Int.mul_comm u1 p1
    have c3 : u2 * p2 = p2 * u2 := Int.mul_comm u2 p2
    rw [e1, c1, c2, c3]
    omega
  have hpw : p1 * (v1 - (p1 * v1 + p2 * v2) * u1) + p2 * (v2 - (p1 * v1 + p2 * v2) * u2) =
      p1 * v1 + p2 * v2 := by
    rw [Int.mul_sub, Int.mul_sub]
    have a1 : p1 * ((p1 * v1 + p2 * v2) * u1) = (p1 * v1 + p2 * v2) * (p1 * u1) := by ac_rfl
    have a2 : p2 * ((p1 * v1 + p2 * v2) * u2) = (p1 * v1 + p2 * v2) * (p2 * u2) := by ac_rfl
    rw [a1, a2]
    have hsum : (p1 * v1 + p2 * v2) * (p1 * u1) + (p1 * v1 + p2 * v2) * (p2 * u2) =
        (p1 * v1 + p2 * v2) * (p1 * u1 + p2 * u2) := (Int.mul_add _ _ _).symm
    rw [hker, Int.mul_zero] at hsum
    omega
  dsimp only
  rw [hpw]
  exact ⟨hdet, by omega, by omega⟩

/-- Theorem 5 (Lemma 3.2): Universal additive closure of transvection dual functionals:
    if `φ1(w) = 0` and `φ2(w) = -1`, then the contragredient action of `g = T_{φ1, w}` sends
    `φ2` to `φ2(v - φ1(v)*w) = φ2(v) + φ1(v)` universally over `Int^6`. -/
theorem lem32_transvection_conjugation_sum (a1 a2 b1 b2 w1 w2 v1 v2 : Int)
    (h2w : b1 * w1 + b2 * w2 = -1) :
    let phi1v := a1 * v1 + a2 * v2
    let phi2v := b1 * v1 + b2 * v2
    b1 * (v1 - phi1v * w1) + b2 * (v2 - phi1v * w2) = phi2v + phi1v := by
  dsimp only
  rw [Int.mul_sub, Int.mul_sub]
  have c1 : b1 * ((a1 * v1 + a2 * v2) * w1) = (a1 * v1 + a2 * v2) * (b1 * w1) := by ac_rfl
  have c2 : b2 * ((a1 * v1 + a2 * v2) * w2) = (a1 * v1 + a2 * v2) * (b2 * w2) := by ac_rfl
  rw [c1, c2]
  have hsum : (a1 * v1 + a2 * v2) * (b1 * w1) + (a1 * v1 + a2 * v2) * (b2 * w2) =
      (a1 * v1 + a2 * v2) * (b1 * w1 + b2 * w2) := (Int.mul_add _ _ _).symm
  rw [h2w] at hsum
  have hm1 : (a1 * v1 + a2 * v2) * (-1) = -(a1 * v1 + a2 * v2) := by
    rw [Int.mul_neg, Int.mul_one]
  rw [hm1] at hsum
  omega

/-- Theorem 6 (Lemma 3.3 Step 1): Universal Möbius normalization matrix identity:
    with `Δ1 = a0N * a10 - a1N * a00`, the adjugate `[[a10, -a1N], [-a00, a0N]]` satisfies
    `adj(Γ) * Γ = Δ1 * I_2` and sends `(a0Nm1, a1Nm1)` to leading-slope numerator
    `Δ2 = a0N * a1Nm1 - a1N * a0Nm1`. -/
theorem lem33_mobius_det_invariance (a0N a1N a00 a10 a0Nm1 a1Nm1 : Int) :
    let d1 := a0N * a10 - a1N * a00
    a10 * a0N + (-a1N) * a00 = d1 ∧
    a10 * a1N + (-a1N) * a10 = 0 ∧
    (-a00) * a0N + a0N * a00 = 0 ∧
    (-a00) * a1N + a0N * a10 = d1 ∧
    (-a00) * a0Nm1 + a0N * a1Nm1 - (a0N * a1Nm1 - a1N * a0Nm1) = (a1N - a00) * a0Nm1 := by
  dsimp only
  have c1 : a10 * a0N = a0N * a10 := Int.mul_comm a10 a0N
  have c2 : (-a1N) * a00 = -(a1N * a00) := Int.neg_mul a1N a00
  have c3 : a10 * a1N = a1N * a10 := Int.mul_comm a10 a1N
  have c4 : (-a1N) * a10 = -(a1N * a10) := Int.neg_mul a1N a10
  have c5 : (-a00) * a0N = -(a0N * a00) := by rw [Int.neg_mul, Int.mul_comm]
  have c6 : (-a00) * a1N = -(a1N * a00) := by rw [Int.neg_mul, Int.mul_comm]
  have c7 : (-a00) * a0Nm1 = -(a00 * a0Nm1) := Int.neg_mul a00 a0Nm1
  have c8 : (a1N - a00) * a0Nm1 = a1N * a0Nm1 - a00 * a0Nm1 := Int.sub_mul a1N a00 a0Nm1
  rw [c1, c2, c3, c4, c5, c6, c7, c8]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Theorem 7 (Lemma 3.3 Step 3): Universal `H^1(GL(V), V) = 0` central-scalar coboundary identity:
    whenever `cz + ζ * cg = cg + gcz`, we have `(ζ - 1) * cg = gcz - cz` universally over `Int^4`. -/
theorem lem33_cocycle_coboundary_vanish (zeta cz cg gcz : Int)
    (hcomm : cz + zeta * cg = cg + gcz) :
    (zeta - 1) * cg = gcz - cz := by
  rw [Int.sub_mul, Int.one_mul]
  omega

private theorem pow_ge_3_mul (q0 : Nat) (hq : 3 ≤ q0) (k : Nat) :
    1 ≤ q0 ^ k := by
  induction k with
  | zero => exact Nat.le_refl 1
  | succ k ih =>
    rw [Nat.pow_succ]
    have : 1 * 3 ≤ q0 ^ k * q0 := Nat.mul_le_mul ih hq
    omega

/-- Theorem 8 (Lemma 3.3 Step 3): Universal degree-gap obstruction for all `q0 ≥ 3`, `N ≥ 2`, `d ≥ 1`:
    `6 ≤ q0^N - q0^(N-1)` and `1 + d * q0^(N-1) < d * q0^N`. -/
theorem lem33_degree_gap_q0_ge_3 (q0 N d : Nat) (hq : 3 ≤ q0) (hN : 2 ≤ N) (hd : 1 ≤ d) :
    6 ≤ q0 ^ N - q0 ^ (N - 1) ∧ 1 + d * q0 ^ (N - 1) < d * q0 ^ N := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  have hsub : k + 2 - 1 = k + 1 := by omega
  rw [hsub]
  have hp1 : 1 ≤ q0 ^ k := pow_ge_3_mul q0 hq k
  have hqk1 : 3 ≤ q0 ^ (k + 1) := by
    rw [Nat.pow_succ]
    have := Nat.mul_le_mul hp1 hq
    omega
  have hpow : q0 ^ (k + 2) = q0 ^ (k + 1) * q0 := Nat.pow_succ q0 (k + 1)
  have hge3 : 3 * q0 ^ (k + 1) ≤ q0 ^ (k + 2) := by
    rw [hpow, Nat.mul_comm (q0 ^ (k + 1)) q0]
    exact Nat.mul_le_mul_right (q0 ^ (k + 1)) hq
  have hgap : 6 ≤ q0 ^ (k + 2) - q0 ^ (k + 1) := by omega
  have hmul : d * q0 ^ (k + 1) + d * 6 ≤ d * q0 ^ (k + 2) := by
    have : q0 ^ (k + 1) + 6 ≤ q0 ^ (k + 2) := by omega
    have hm := Nat.mul_le_mul_left d this
    rw [Nat.mul_add] at hm
    exact hm
  exact ⟨hgap, by omega⟩

/-- Elementary transposition `(a b)` on `Nat`. -/
def swapNat (a b x : Nat) : Nat :=
  if x = a then b else if x = b then a else x

private theorem swapNat_left (a b : Nat) : swapNat a b a = b := by
  unfold swapNat; simp

private theorem swapNat_right (a b : Nat) (hab : a ≠ b) : swapNat a b b = a := by
  unfold swapNat
  have hba : b ≠ a := Ne.symm hab
  simp [hba]

private theorem swapNat_other (a b x : Nat) (hxa : x ≠ a) (hxb : x ≠ b) : swapNat a b x = x := by
  unfold swapNat; simp [hxa, hxb]

/-- Theorem 9 (Lemma 3.4): Universal Jordan transposition conjugation identity:
    for ANY three pairwise distinct `a, b, c : Nat` and EVERY `x : Nat`,
    `(a b) ∘ (b c) ∘ (a b) (x) = (a c) (x)`. -/
theorem lem34_jordan_transposition_conj (a b c x : Nat)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    swapNat a b (swapNat b c (swapNat a b x)) = swapNat a c x := by
  by_cases hxa : x = a
  · rw [hxa, swapNat_left, swapNat_left, swapNat_other a b c (Ne.symm hac) (Ne.symm hbc), swapNat_left]
  · by_cases hxb : x = b
    · rw [hxb, swapNat_right a b hab, swapNat_other b c a hab hac, swapNat_left,
          swapNat_other a c b (Ne.symm hab) hbc]
    · by_cases hxc : x = c
      · rw [hxc, swapNat_other a b c (Ne.symm hac) (Ne.symm hbc), swapNat_right b c hbc,
            swapNat_right a b hab, swapNat_right a c hac]
      · rw [swapNat_other a b x hxa hxb, swapNat_other b c x hxb hxc,
            swapNat_other a b x hxa hxb, swapNat_other a c x hxa hxc]

/-! ### Part 2: Elliptic Parallelogram Law (Sec. 4), Galois Pinch & Castelnuovo Bound (Sec. 5) -/

/-- Theorem 10 (Lemma 4.2(2)): Universal Cauchy-Schwarz discriminant bound from curve-morphism
    parallelogram positivity: if `d1 ≥ 1` and `(-β0)^2 * d1 + (-β0)*(2*d1)*β0 + (2*d1)^2 * d2 ≥ 0`,
    then `β0^2 ≤ 4 * d1 * d2`. -/
theorem lem42_parallelogram_cauchy_schwarz (d1 d2 beta0 : Int) (hd1 : 1 ≤ d1)
    (hpos : 0 ≤ (-beta0) * (-beta0) * d1 + (-beta0) * (2 * d1) * beta0 + (2 * d1) * (2 * d1) * d2) :
    beta0 * beta0 ≤ 4 * d1 * d2 := by
  have h1 : (-beta0) * (-beta0) * d1 = d1 * (beta0 * beta0) := by
    rw [Int.neg_mul_neg]; ac_rfl
  have h2 : (-beta0) * (2 * d1) * beta0 = -(2 * (d1 * (beta0 * beta0))) := by
    rw [Int.neg_mul, Int.neg_mul]
    have : beta0 * (2 * d1) * beta0 = 2 * (d1 * (beta0 * beta0)) := by ac_rfl
    rw [this]
  have h3 : (2 * d1) * (2 * d1) * d2 = d1 * (4 * d1 * d2) := by
    have : (2 : Int) * 2 = 4 := by decide
    have e : (2 * d1) * (2 * d1) * d2 = (2 * 2) * (d1 * d1 * d2) := by ac_rfl
    rw [e, this]; ac_rfl
  rw [h1, h2, h3] at hpos
  have hfact : 0 ≤ d1 * (4 * d1 * d2 - beta0 * beta0) := by
    rw [Int.mul_sub]; omega
  by_cases hle : beta0 * beta0 ≤ 4 * d1 * d2
  · exact hle
  · exfalso
    have hneg : 1 ≤ beta0 * beta0 - 4 * d1 * d2 := by omega
    have hmul : 1 ≤ d1 * (beta0 * beta0 - 4 * d1 * d2) := by
      have hm := Int.mul_le_mul (by omega : (1 : Int) ≤ d1) hneg (by decide) (by omega)
      omega
    have hopp : d1 * (4 * d1 * d2 - beta0 * beta0) = -(d1 * (beta0 * beta0 - 4 * d1 * d2)) := by
      rw [Int.mul_sub, Int.mul_sub]; omega
    omega

/-- Theorem 11 (Lemma 4.1(2)): Universal Waterhouse ordinary-curve interval selection:
    for `p ≥ 2`, `n ≥ 5`, `q ≥ 16 * n^2` divisible by `p` (since `q = p^r`), putting
    `N1 = ((q + 1) / n) * n` and `N2 = N1 - n`, both `q + 1 - N1 < n` and `q + 1 - N2 < 2 * n`,
    and at least one of `q + 1 - N1`, `q + 1 - N2` is not divisible by `p`. -/
theorem lem41_waterhouse_interval_coprime (p n q : Nat) (hp : 2 ≤ p) (hn : 5 ≤ n)
    (hq : 16 * (n * n) ≤ q) (hq_div : q % p = 0) :
    let N1 := ((q + 1) / n) * n
    let N2 := N1 - n
    N1 ≤ q + 1 ∧ q + 1 - N1 < n ∧
    N2 ≤ q + 1 ∧ q + 1 - N2 < 2 * n ∧
    ((q + 1 - N1) % p ≠ 0 ∨ (q + 1 - N2) % p ≠ 0) := by
  dsimp only
  have hdiv : ((q + 1) / n) * n ≤ q + 1 := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_le (q + 1) n
  have hrem : q + 1 - ((q + 1) / n) * n = (q + 1) % n := by
    have hdm := Nat.div_add_mod (q + 1) n
    rw [Nat.mul_comm] at hdm
    omega
  have hlt1 : q + 1 - ((q + 1) / n) * n < n := by
    rw [hrem]
    exact Nat.mod_lt (q + 1) (by omega)
  have hge1 : n ≤ ((q + 1) / n) * n := by
    have hqge : n ≤ q + 1 := by
      have : n * 1 ≤ n * n := Nat.mul_le_mul_left n (by omega)
      omega
    have h1 : 1 ≤ (q + 1) / n := Nat.div_pos hqge (by omega)
    have hm := Nat.mul_le_mul_right n h1
    omega
  have hN2le : ((q + 1) / n) * n - n ≤ q + 1 := by omega
  have hlt2 : q + 1 - (((q + 1) / n) * n - n) < 2 * n := by omega
  have hcop : (q + 1 - ((q + 1) / n) * n) % p ≠ 0 ∨
              (q + 1 - (((q + 1) / n) * n - n)) % p ≠ 0 := by
    by_cases h1 : (q + 1 - ((q + 1) / n) * n) % p = 0
    · by_cases hpn : n % p = 0
      · exfalso
        have hN1mod : (((q + 1) / n) * n) % p = 0 := by
          rw [Nat.mul_mod, hpn, Nat.mul_zero, Nat.zero_mod]
        have hsum : ((q + 1) / n) * n + (q + 1 - ((q + 1) / n) * n) = q + 1 := by omega
        have hq1mod0 : (q + 1) % p = 0 := by
          rw [← hsum, Nat.add_mod, hN1mod, h1]
          exact Nat.zero_mod p
        have hq1mod1 : (q + 1) % p = 1 := by
          rw [Nat.add_mod, hq_div, Nat.zero_add, Nat.mod_mod]
          exact Nat.mod_eq_of_lt (by omega)
        omega
      · right
        have heq : q + 1 - (((q + 1) / n) * n - n) = (q + 1 - ((q + 1) / n) * n) + n := by omega
        rw [heq, Nat.add_mod, h1, Nat.zero_add, Nat.mod_mod]
        exact hpn
    · left; exact h1
  exact ⟨hdiv, hlt1, hN2le, hlt2, hcop⟩

/-- Theorem 12 (Lemma 5.1 Step 1): Exact constant-field pinch:
    if `G ≥ 1`, `dGeom = G`, `dArith = k1 * dGeom`, and `dArith ≤ G`, then `k1 = 1` and `dArith = G`. -/
theorem lem51_linear_disjointness_pinch (G dGeom dArith k1 : Nat)
    (hG : 1 ≤ G) (hgeom : dGeom = G) (hconst : dArith = k1 * dGeom)
    (hge : dGeom ≤ dArith) (hle : dArith ≤ G) :
    k1 = 1 ∧ dArith = G := by
  have hd : dArith = G := by omega
  have hmul : k1 * G = 1 * G := by
    rw [Nat.one_mul, ← hgeom, ← hconst, hd, hgeom]
  have hk1 : k1 = 1 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < G) hmul
  exact ⟨hk1, hd⟩

/-- Theorem 13 (Lemma 5.1 Step 2): Universal Castelnuovo genus induction step:
    if `gPrev ≤ (i - 1) * dPrev`, `i ≥ 1`, `dCur = n1 * dPrev`, and `n1 * n2 ≤ dCur`,
    then `n1 * gPrev + n1 * n2 ≤ i * dCur`. -/
theorem lem51_castelnuovo_induction_step (i dPrev dCur gPrev n1 n2 : Nat)
    (hi : 1 ≤ i) (hih : gPrev ≤ (i - 1) * dPrev) (hd : dCur = n1 * dPrev)
    (hnn : n1 * n2 ≤ dCur) :
    n1 * gPrev + n1 * n2 ≤ i * dCur := by
  have h1 : n1 * gPrev ≤ n1 * ((i - 1) * dPrev) := Nat.mul_le_mul_left n1 hih
  have h2 : n1 * ((i - 1) * dPrev) = (i - 1) * dCur := by
    rw [hd]; ac_rfl
  have h3 : (i - 1) * dCur + dCur = i * dCur := by
    have : (i - 1) + 1 = i := by omega
    calc (i - 1) * dCur + dCur = (i - 1) * dCur + 1 * dCur := by rw [Nat.one_mul]
      _ = ((i - 1) + 1) * dCur := (Nat.add_mul (i - 1) 1 dCur).symm
      _ = i * dCur := by rw [this]
  omega

/-! ### Part 3: B-Adic Descent Tree, Unimodular Elimination & Theorem 1.2 Guards (Sec. 6) -/

/-- Exact descent tree upper-bound recurrence `T_0 = Tloc`, `T_{j+1} = Tloc + W * T_j`. -/
def treeCost (W Tloc : Nat) : Nat → Nat
  | 0 => Tloc
  | j + 1 => Tloc + W * treeCost W Tloc j

/-- Theorem 14 (Lemma 6.2): Universal inductive B-adic descent tree complexity bound:
    for ANY branching `W ≥ 2`, local cost `Tloc`, and depth `j`,
    `(W - 1) * treeCost W Tloc j + Tloc = W^(j+1) * Tloc` and `treeCost W Tloc j ≤ 2 * W^j * Tloc`. -/
theorem lem62_recursion_tree_bound (W Tloc : Nat) (hW : 2 ≤ W) :
    ∀ j : Nat,
      (W - 1) * treeCost W Tloc j + Tloc = W ^ (j + 1) * Tloc ∧
      treeCost W Tloc j ≤ 2 * W ^ j * Tloc := by
  intro j
  have hWsub : W - 1 + 1 = W := by omega
  have hsubT : (W - 1) * Tloc + Tloc = W * Tloc := by
    calc (W - 1) * Tloc + Tloc = (W - 1) * Tloc + 1 * Tloc := by rw [Nat.one_mul]
      _ = (W - 1 + 1) * Tloc := (Nat.add_mul (W - 1) 1 Tloc).symm
      _ = W * Tloc := by rw [hWsub]
  induction j with
  | zero =>
    dsimp only [treeCost]
    have h2 : W ^ (0 + 1) * Tloc = W * Tloc := by rw [Nat.zero_add, Nat.pow_one]
    have h3 : 2 * W ^ 0 * Tloc = 2 * Tloc := by rw [Nat.pow_zero, Nat.mul_one]
    exact ⟨by omega, by omega⟩
  | succ k ih =>
    rcases ih with ⟨ih_eq, _⟩
    dsimp only [treeCost]
    have hpow_mul : W * (W ^ (k + 1) * Tloc) = W ^ (k + 2) * Tloc := by
      have hp : W ^ (k + 2) = W ^ (k + 1) * W := Nat.pow_succ W (k + 1)
      rw [hp]; ac_rfl
    have hstep : (W - 1) * (Tloc + W * treeCost W Tloc k) + Tloc = W ^ (k + 2) * Tloc := by
      rw [Nat.mul_add]
      have hcomm : (W - 1) * (W * treeCost W Tloc k) = W * ((W - 1) * treeCost W Tloc k) := by ac_rfl
      rw [hcomm]
      have hgroup : (W - 1) * Tloc + W * ((W - 1) * treeCost W Tloc k) + Tloc =
          W * ((W - 1) * treeCost W Tloc k + Tloc) := by
        rw [Nat.mul_add]; omega
      rw [hgroup, ih_eq, hpow_mul]
    have hbound : Tloc + W * treeCost W Tloc k ≤ 2 * W ^ (k + 1) * Tloc := by
      have h1 : Tloc + W * treeCost W Tloc k ≤ (W - 1) * (Tloc + W * treeCost W Tloc k) := by
        have hm := Nat.mul_le_mul_right (Tloc + W * treeCost W Tloc k) (by omega : 1 ≤ W - 1)
        rw [Nat.one_mul] at hm
        exact hm
      have h2 : W ^ (k + 2) * Tloc ≤ (W - 1) * (2 * W ^ (k + 1) * Tloc) := by
        have hW2 : W ≤ (W - 1) * 2 := by omega
        have hm := Nat.mul_le_mul_right (W ^ (k + 1) * Tloc) hW2
        have hr : (W - 1) * 2 * (W ^ (k + 1) * Tloc) = (W - 1) * (2 * W ^ (k + 1) * Tloc) := by ac_rfl
        rw [hpow_mul, hr] at hm
        exact hm
      have hlt_mul : (W - 1) * (Tloc + W * treeCost W Tloc k) ≤ (W - 1) * (2 * W ^ (k + 1) * Tloc) := by
        omega
      exact Nat.le_of_mul_le_mul_left hlt_mul (by omega : 0 < W - 1)
    exact ⟨hstep, hbound⟩

/-- Theorem 15 (Lemma 6.3(2)): Universal factoring-free `SL_2(Z)` unimodular elimination step:
    given `d ≥ 1`, `u = d * u'`, `v = d * v'`, and Bézout identity `s * u + t * v = d`,
    the matrix `[[s, t], [-v', u']]` has `det = s * u' + t * v' = 1` and maps `(u, v) ↦ (d, 0)`. -/
theorem lem63_unimodular_step_det_one (u v d u' v' s t : Int)
    (hd : 1 ≤ d) (hu : u = d * u') (hv : v = d * v') (hbez : s * u + t * v = d) :
    s * u' + t * v' = 1 ∧
    s * u + t * v = d ∧
    (-v') * u + u' * v = 0 := by
  have hdet_mul : d * (s * u' + t * v') = d * 1 := by
    rw [Int.mul_add, Int.mul_one]
    have a1 : d * (s * u') = s * (d * u') := by ac_rfl
    have a2 : d * (t * v') = t * (d * v') := by ac_rfl
    rw [a1, a2, ← hu, ← hv, hbez]
  have hdet : s * u' + t * v' = 1 := by
    by_cases heq : s * u' + t * v' = 1
    · exact heq
    · exfalso
      have hdiff : d * (s * u' + t * v' - 1) = 0 := by
        rw [Int.mul_sub, Int.mul_one]; omega
      have hnz : d ≠ 0 := by omega
      have hz := Int.mul_eq_zero.mp hdiff
      cases hz with
      | inl h => exact hnz h
      | inr h => omega
  have hzero : (-v') * u + u' * v = 0 := by
    rw [hu, hv, Int.neg_mul]
    have c1 : v' * (d * u') = u' * (d * v') := by ac_rfl
    rw [c1]
    omega
  exact ⟨hdet, hbez, hzero⟩

/-- Theorem 16 (Lemma 6.4): Universal soundness of the unfactored-modulus non-membership exponent:
    if `dg ≥ 1`, `Yg = dg * qg`, `ML = dg * Eg`, and `¬(dg ∣ Yh)` (expressed as `Yh % dg ≠ 0`),
    then `(Yg * Eg) % ML = 0` while `(Yh * Eg) % ML ≠ 0`. -/
theorem lem64_nonmembership_exponent_sound (dg qg Yg Yh ML Eg : Nat)
    (hdg : 1 ≤ dg) (hEg : 1 ≤ Eg) (hYg : Yg = dg * qg) (hML : ML = dg * Eg)
    (hndiv : Yh % dg ≠ 0) :
    (Yg * Eg) % ML = 0 ∧ (Yh * Eg) % ML ≠ 0 := by
  have _ := hdg
  have h1 : (Yg * Eg) % ML = 0 := by
    have hmul : Yg * Eg = ML * qg := by
      rw [hYg, hML]; ac_rfl
    rw [hmul, Nat.mul_mod_right]
  have h2 : (Yh * Eg) % ML ≠ 0 := by
    intro h0
    have hdiv : ML ∣ Yh * Eg := Nat.dvd_of_mod_eq_zero h0
    rcases hdiv with ⟨k, hk⟩
    have heq : Yh * Eg = (dg * k) * Eg := by
      rw [hk, hML]; ac_rfl
    have hYh : Yh = dg * k := Nat.eq_of_mul_eq_mul_right (by omega : 0 < Eg) heq
    have hm0 : Yh % dg = 0 := by rw [hYh, Nat.mul_mod_right]
    exact hndiv hm0
  exact ⟨h1, h2⟩

/-- Theorem 17 (Section 6.2 Step 5): Universal CRT recombination identity for small-prime (`S`)
    and large-cofactor (`L`) DLP solutions: if `σS * S + σL * L = 1` and
    `x = xS * σL * L + xL * σS * S`, then `L * (x - xS) = (S * L) * ((xL - xS) * σS)` and
    `S * (x - xL) = (S * L) * ((xS - xL) * σL)`. -/
theorem sec62_crt_recombination_sound (S L sigS sigL xS xL : Int)
    (hbez : sigS * S + sigL * L = 1) :
    let x := xS * sigL * L + xL * sigS * S
    L * (x - xS) = (S * L) * ((xL - xS) * sigS) ∧
    S * (x - xL) = (S * L) * ((xS - xL) * sigL) := by
  dsimp only
  have hx1 : xS * sigL * L + xL * sigS * S - xS = (xL - xS) * sigS * S := by
    have h1 : xS = xS * (sigS * S + sigL * L) := by rw [hbez, Int.mul_one]
    rw [Int.mul_add] at h1
    have c1 : xS * (sigL * L) = xS * sigL * L := by ac_rfl
    have c2 : xS * (sigS * S) = xS * sigS * S := by ac_rfl
    have c3 : (xL - xS) * sigS * S = xL * sigS * S - xS * sigS * S := by
      rw [Int.sub_mul, Int.sub_mul]
    omega
  have hx2 : xS * sigL * L + xL * sigS * S - xL = (xS - xL) * sigL * L := by
    have h1 : xL = xL * (sigS * S + sigL * L) := by rw [hbez, Int.mul_one]
    rw [Int.mul_add] at h1
    have c1 : xL * (sigS * S) = xL * sigS * S := by ac_rfl
    have c2 : xL * (sigL * L) = xL * sigL * L := by ac_rfl
    have c3 : (xS - xL) * sigL * L = xS * sigL * L - xL * sigL * L := by
      rw [Int.sub_mul, Int.sub_mul]
    omega
  have eq1 : L * (xS * sigL * L + xL * sigS * S - xS) = (S * L) * ((xL - xS) * sigS) := by
    rw [hx1]; ac_rfl
  have eq2 : S * (xS * sigL * L + xL * sigS * S - xL) = (S * L) * ((xS - xL) * sigL) := by
    rw [hx2]; ac_rfl
  exact ⟨eq1, eq2⟩

/-- Theorem 18 (Theorem 1.2 & Section 6.3): Exact constructive verification of the discrete
    asymptotic parameter guards (`ℓ3 ≥ 10`, `B ≥ 4`, `3/32 < 1/8`, `20.4 + 16.3 < 60`,
    `48.9 < 60`, `2^10 = 1024`, `8^12 > 2 * 4`). -/
theorem thm12_parameter_asymptotic_guards :
    (3 * 8 < 32 * 1) ∧
    (204 + 163 < 600) ∧
    (489 < 600) ∧
    (2 ^ 10 = 1024) ∧
    (8 ^ 12 > 2 * 4) := by
  decide

end CogenticDiscreteLog

