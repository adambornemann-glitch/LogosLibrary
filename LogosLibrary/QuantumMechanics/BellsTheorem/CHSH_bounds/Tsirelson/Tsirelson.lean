/-
Copyright (c) 2025 Bell Theorem Formalization Project
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla
Ported by: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.BellsTheorem.CHSH_Bounds.Tsirelson.CommutatorAlgebra
/-!
# Tsirelson's Bound

This file proves Tsirelson's bound: for any quantum state ρ and any CHSH tuple of
observables (A₀, A₁, B₀, B₁), the CHSH expectation value satisfies

  |⟨S⟩| ≤ 2√2

where S = A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁ is the CHSH operator.

This bound of 2√2 ≈ 2.828 is the maximum quantum violation of the classical CHSH
inequality (which bounds |⟨S⟩| ≤ 2). The proof proceeds by:

1. Showing S² ≤ 8I using the commutator product bounds
2. Deriving that -2√2·I ≤ S ≤ 2√2·I
3. Taking the trace with a density matrix to get the final bound

## Main Results

* `CHSH_op_sq_le_eight`: S² ≤ 8I
* `tsirelson_bound`: |⟨CHSH⟩| ≤ 2√2

## References

* B.S. Tsirelson, "Quantum generalizations of Bell's inequality", 1980
-/
open scoped Matrix ComplexConjugate BigOperators TensorProduct
open MeasureTheory ProbabilityTheory Matrix Complex

namespace QuantumInfo



private lemma real_smul_one_mulVec {m : ℕ} (c : ℝ) (x : Fin m → ℂ) :
    (c • (1 : Matrix (Fin m) (Fin m) ℂ)).mulVec x = c • x := by
  ext i
  simp only [mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply,
             mul_ite, mul_one, mul_zero,Pi.smul_apply, Complex.real_smul,
             ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-! ## Operator Norm Bounds -/

/-- If H is Hermitian with H² ≤ c²I, then ‖Hx‖ ≤ c‖x‖ -/
lemma norm_mulVec_le_of_sq_le {n : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian)
    (c : ℝ)
    (h_sq : IsPosSemidefComplex ((c^2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - H * H))
    (x : Fin n → ℂ) :
    ∑ i, ‖(H.mulVec x) i‖^2 ≤ c^2 * ∑ i, ‖x i‖^2 := by
  have hx := h_sq x
  simp only [Matrix.sub_mulVec] at hx
  rw [real_smul_one_mulVec] at hx
  simp only [dotProduct_sub] at hx
  rw [sub_re] at hx
  have h_smul_re : (star x ⬝ᵥ (c ^ 2 : ℝ) • x).re = c ^ 2 * (star x ⬝ᵥ x).re := by
    have : (c ^ 2 : ℝ) • x = ((↑(c ^ 2) : ℂ)) • x := by
      ext i; simp [Complex.real_smul]
    rw [this, dotProduct_smul, smul_eq_mul, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [h_smul_re] at hx
  -- rest unchanged from here
  have h_self_eq : (star x ⬝ᵥ x).re = ∑ i, ‖x i‖^2 := by
    have := star_dotProduct_self_eq_sum_normSq x
    simp only at this ⊢
    exact congrArg Complex.re this
  rw [h_self_eq] at hx
  have h_sq_inner : star x ⬝ᵥ (H * H).mulVec x = star (H.mulVec x) ⬝ᵥ H.mulVec x := by
    rw [star_mulVec_dotProduct_mulVec_hermitian H hH x]
  have h_sq_re : (star x ⬝ᵥ (H * H).mulVec x).re = ∑ i, ‖(H.mulVec x) i‖^2 := by
    rw [h_sq_inner, star_dotProduct_self_eq_sum_normSq]
    simp only [ofReal_re]
  rw [h_sq_re] at hx
  linarith

/-! ## Positive Semidefinite Bounds from Squared Bounds -/

/-- If H is Hermitian with H² ≤ c²I, then cI - H is pos semidef -/
lemma posSemidef_sub_of_sq_le {n : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian)
    (c : ℝ) (hc : 0 ≤ c)
    (h_sq : IsPosSemidefComplex ((c^2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - H * H)) :
    IsPosSemidefComplex ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - H) := by
  intro x
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [dotProduct_sub, dotProduct_smul, sub_re, smul_eq_mul, mul_re,
             ofReal_re, ofReal_im, zero_mul, sub_zero]
  have h_self_eq : (star x ⬝ᵥ x).re = ∑ i, ‖x i‖^2 := by
    have := star_dotProduct_self_eq_sum_normSq x
    simp only at this ⊢
    exact congrArg Complex.re this
  rw [h_self_eq]
  have h_norm_bound : ∑ i, ‖(H.mulVec x) i‖^2 ≤ c^2 * ∑ i, ‖x i‖^2 :=
    norm_mulVec_le_of_sq_le H hH c h_sq x
  let x' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  let Hx' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (H.mulVec x)
  have h_inner : star x ⬝ᵥ H.mulVec x = inner (𝕜 := ℂ) x' Hx' := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct]
    rw [dotProduct_comm]
  have h_cs : ‖inner (𝕜 := ℂ) x' Hx'‖ ≤ ‖x'‖ * ‖Hx'‖ := norm_inner_le_norm x' Hx'
  have h_re_le : (star x ⬝ᵥ H.mulVec x).re ≤ ‖star x ⬝ᵥ H.mulVec x‖ := by
    exact le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  have h_norm_x : ‖x'‖^2 = ∑ i, ‖x i‖^2 := EuclideanSpace.norm_sq_eq x'
  have h_norm_Hx : ‖Hx'‖^2 = ∑ i, ‖(H.mulVec x) i‖^2 := EuclideanSpace.norm_sq_eq Hx'
  have h_Hx_le : ‖Hx'‖ ≤ c * ‖x'‖ := by
    by_cases hx0 : ‖x'‖ = 0
    · -- x' = 0 case
      simp only [hx0, mul_zero]
      have hx_zero : x = 0 := by
        ext i
        have : ‖x'‖^2 = 0 := by rw [hx0]; ring
        rw [h_norm_x] at this
        have h_sum_zero := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖x i‖) |>.mp this
        simp only [Finset.mem_univ, sq_eq_zero_iff, norm_eq_zero, true_implies] at h_sum_zero
        exact h_sum_zero i
      have hHx_zero : H.mulVec x = 0 := by rw [hx_zero]; exact Matrix.mulVec_zero H
      calc ‖Hx'‖ = ‖WithLp.toLp 2 (H.mulVec x)‖ := rfl
        _ = ‖WithLp.toLp 2 (0 : Fin n → ℂ)‖ := by rw [hHx_zero]
        _ = 0 := by simp
      rfl
    · -- x' ≠ 0 case
      have hx_pos : 0 < ‖x'‖ := norm_pos_iff.mpr (norm_ne_zero_iff.mp hx0)
      have h_sq_le : ‖Hx'‖^2 ≤ (c * ‖x'‖)^2 := by
        rw [h_norm_Hx, mul_pow, h_norm_x]
        calc ∑ i, ‖(H.mulVec x) i‖^2 ≤ c^2 * ∑ i, ‖x i‖^2 := h_norm_bound
          _ = c^2 * ‖x'‖^2 := by rw [h_norm_x]
        exact le_of_eq (congrArg (HMul.hMul (c ^ 2)) h_norm_x)
      have h1 : ‖Hx'‖ = Real.sqrt (‖Hx'‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      have h2 : c * ‖x'‖ = Real.sqrt ((c * ‖x'‖)^2) := (Real.sqrt_sq (mul_nonneg hc (le_of_lt hx_pos))).symm
      rw [h1, h2]
      exact Real.sqrt_le_sqrt h_sq_le
  have h_final : (star x ⬝ᵥ H.mulVec x).re ≤ c * ∑ i, ‖x i‖^2 :=
    calc (star x ⬝ᵥ H.mulVec x).re
        ≤ ‖star x ⬝ᵥ H.mulVec x‖ := h_re_le
      _ = ‖inner (𝕜 := ℂ) x' Hx'‖ := by rw [h_inner]
      _ ≤ ‖x'‖ * ‖Hx'‖ := h_cs
      _ ≤ ‖x'‖ * (c * ‖x'‖) := by apply mul_le_mul_of_nonneg_left h_Hx_le (norm_nonneg _)
      _ = c * ‖x'‖^2 := by ring
      _ = c * ∑ i, ‖x i‖^2 := by rw [h_norm_x]
  linarith

/-- If H is Hermitian with H² ≤ c²I, then cI + H is pos semidef -/
lemma posSemidef_add_of_sq_le {n : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian)
    (c : ℝ) (hc : 0 ≤ c)
    (h_sq : IsPosSemidefComplex ((c^2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - H * H)) :
    IsPosSemidefComplex ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + H) := by
  intro x
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [dotProduct_add, dotProduct_smul, add_re, smul_eq_mul, mul_re,
             ofReal_re, ofReal_im, zero_mul, sub_zero]
  have h_self_eq : (star x ⬝ᵥ x).re = ∑ i, ‖x i‖^2 := by
    have := star_dotProduct_self_eq_sum_normSq x
    simp only at this ⊢
    exact congrArg Complex.re this
  rw [h_self_eq]
  have h_norm_bound : ∑ i, ‖(H.mulVec x) i‖^2 ≤ c^2 * ∑ i, ‖x i‖^2 :=
    norm_mulVec_le_of_sq_le H hH c h_sq x
  let x' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  let Hx' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (H.mulVec x)
  have h_inner : star x ⬝ᵥ H.mulVec x = inner (𝕜 := ℂ) x' Hx' := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct]
    rw [dotProduct_comm]
  have h_cs : ‖inner (𝕜 := ℂ) x' Hx'‖ ≤ ‖x'‖ * ‖Hx'‖ := norm_inner_le_norm x' Hx'
  have h_re_ge : -‖star x ⬝ᵥ H.mulVec x‖ ≤ (star x ⬝ᵥ H.mulVec x).re := by
    have := Complex.abs_re_le_norm (star x ⬝ᵥ H.mulVec x)
    have := neg_abs_le (star x ⬝ᵥ H.mulVec x).re
    linarith
  have h_norm_x : ‖x'‖^2 = ∑ i, ‖x i‖^2 := EuclideanSpace.norm_sq_eq x'
  have h_norm_Hx : ‖Hx'‖^2 = ∑ i, ‖(H.mulVec x) i‖^2 := EuclideanSpace.norm_sq_eq Hx'
  have h_Hx_le : ‖Hx'‖ ≤ c * ‖x'‖ := by
    by_cases hx0 : ‖x'‖ = 0
    · simp only [hx0, mul_zero]
      have hx_zero : x = 0 := by
        ext i
        have : ‖x'‖^2 = 0 := by rw [hx0]; ring
        rw [h_norm_x] at this
        have h_sum_zero := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖x i‖) |>.mp this
        simp only [Finset.mem_univ, sq_eq_zero_iff, norm_eq_zero, true_implies] at h_sum_zero
        exact h_sum_zero i
      have hHx_zero : H.mulVec x = 0 := by rw [hx_zero]; exact Matrix.mulVec_zero H
      calc ‖Hx'‖ = ‖WithLp.toLp 2 (H.mulVec x)‖ := rfl
        _ = ‖WithLp.toLp 2 (0 : Fin n → ℂ)‖ := by rw [hHx_zero]
        _ = 0 := by simp
      rfl
    · have hx_pos : 0 < ‖x'‖ := norm_pos_iff.mpr (norm_ne_zero_iff.mp hx0)
      have h_sq_le : ‖Hx'‖^2 ≤ (c * ‖x'‖)^2 := by
        rw [h_norm_Hx, mul_pow, h_norm_x]
        calc ∑ i, ‖(H.mulVec x) i‖^2 ≤ c^2 * ∑ i, ‖x i‖^2 := h_norm_bound
          _ = c^2 * ‖x'‖^2 := by rw [h_norm_x]
        exact le_of_eq (congrArg (HMul.hMul (c ^ 2)) h_norm_x)
      have h1 : ‖Hx'‖ = Real.sqrt (‖Hx'‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      have h2 : c * ‖x'‖ = Real.sqrt ((c * ‖x'‖)^2) := (Real.sqrt_sq (mul_nonneg hc (le_of_lt hx_pos))).symm
      rw [h1, h2]
      exact Real.sqrt_le_sqrt h_sq_le
  have h_final : -(c * ∑ i, ‖x i‖^2) ≤ (star x ⬝ᵥ H.mulVec x).re :=
    calc -(c * ∑ i, ‖x i‖^2)
        = -(c * ‖x'‖^2) := by rw [h_norm_x]
      _ = -(‖x'‖ * (c * ‖x'‖)) := by ring
      _ ≤ -(‖x'‖ * ‖Hx'‖) := by
        have := mul_le_mul_of_nonneg_left h_Hx_le (norm_nonneg x')
        linarith
      _ ≤ -‖inner (𝕜 := ℂ) x' Hx'‖ := by linarith
      _ = -‖star x ⬝ᵥ H.mulVec x‖ := by rw [h_inner]
      _ ≤ (star x ⬝ᵥ H.mulVec x).re := h_re_ge
  linarith

/-! ## Trace Bounds -/

/-- If cI - S and cI + S are pos semidef, then |Tr(Sρ)| ≤ c -/
lemma trace_bound_of_posSemidef_bounds {n : ℕ} [NeZero n]
    (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsHermitian)
    (c : ℝ)
    (h_upper : IsPosSemidefComplex ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - S))
    (h_lower : IsPosSemidefComplex ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + S))
    (ρ : DensityMatrix n) :
    ‖(S * ρ.toMatrix).trace‖ ≤ c := by
  -- Step 1: Show cI ± S are Hermitian
  have h_upper_herm : ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - S).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
               Matrix.conjTranspose_one, hS.eq]
    simp only [RCLike.star_def, conj_ofReal]
  have h_lower_herm : ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + S).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
               Matrix.conjTranspose_one, hS.eq]
    simp only [RCLike.star_def, conj_ofReal]
  -- Step 2: Apply trace_posSemidef_mul_re_nonneg
  have h_upper_trace := trace_posSemidef_mul_re_nonneg _ ρ.toMatrix h_upper_herm ρ.hermitian h_upper ρ.posSemidef
  have h_lower_trace := trace_posSemidef_mul_re_nonneg _ ρ.toMatrix h_lower_herm ρ.hermitian h_lower ρ.posSemidef
  -- Step 3: Expand traces
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
             Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul] at h_upper_trace h_lower_trace
  -- Step 4: Tr(ρ) = 1
  have h_tr_one : ρ.toMatrix.trace = 1 := ρ.trace_one
  -- Step 5: Simplify using Tr(ρ) = 1
  simp only [h_tr_one, smul_eq_mul, mul_one, sub_re, add_re, ofReal_re] at h_upper_trace h_lower_trace
  -- Step 6: Tr(Sρ) is real
  have h_real := hermitian_expectation_real S hS ρ.toMatrix ρ.hermitian
  have h_norm : ‖(S * ρ.toMatrix).trace‖ = |(S * ρ.toMatrix).trace.re| := by
    exact Eq.symm ((fun {z} => abs_re_eq_norm.mpr) h_real)
  rw [h_norm]
  rw [abs_le]
  constructor <;> linarith -- linarith failed to find a contradiction

/-! ## CHSH Operator Properties -/

/-- CHSH operator squared is bounded: S² ≤ 8I -/
lemma CHSH_op_sq_le_eight {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hT : IsCHSHTuple A₀ A₁ B₀ B₁) :
    IsPosSemidefComplex (8 • (1 : Matrix (Fin n) (Fin n) ℂ) - CHSH_op A₀ A₁ B₀ B₁ * CHSH_op A₀ A₁ B₀ B₁) := by
  rw [CHSH_op_square A₀ A₁ B₀ B₁ hT]
  -- Goal: 8I - (4I - [A₀,A₁][B₀,B₁]) = 4I + [A₀,A₁][B₀,B₁] ≥ 0
  have h_simp : 8 • (1 : Matrix (Fin n) (Fin n) ℂ) - (4 • 1 - ⟦A₀, A₁⟧ * ⟦B₀, B₁⟧) =
                4 • (1 : Matrix (Fin n) (Fin n) ℂ) + ⟦A₀, A₁⟧ * ⟦B₀, B₁⟧ := by module
  rw [h_simp]
  exact comm_prod_ge_neg_four A₀ A₁ B₀ B₁
    hT.A₀_herm hT.A₁_herm hT.B₀_herm hT.B₁_herm
    hT.A₀_sq hT.A₁_sq hT.B₀_sq hT.B₁_sq
    hT.comm_A₀_B₀ hT.comm_A₀_B₁ hT.comm_A₁_B₀ hT.comm_A₁_B₁

/-- CHSH operator is Hermitian -/
lemma CHSH_op_isHermitian {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hT : IsCHSHTuple A₀ A₁ B₀ B₁) :
    (CHSH_op A₀ A₁ B₀ B₁).IsHermitian := by
  simp only [CHSH_op]
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_sub]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  rw [hT.A₀_herm.eq, hT.A₁_herm.eq, hT.B₀_herm.eq, hT.B₁_herm.eq]
  rw [hT.comm_A₀_B₁, hT.comm_A₀_B₀, hT.comm_A₁_B₀, hT.comm_A₁_B₁]

/-! ## Main Theorem -/

/-- **Tsirelson's Bound**: For any quantum state and any CHSH tuple, |⟨CHSH⟩| ≤ 2√2

This is the maximum violation achievable in quantum mechanics. -/
theorem tsirelson_bound {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hT : IsCHSHTuple A₀ A₁ B₀ B₁)
    (ρ : DensityMatrix n) :
    ‖CHSH_expect A₀ A₁ B₀ B₁ ρ.toMatrix‖ ≤ 2 * Real.sqrt 2 := by
  simp only [CHSH_expect]
  let S := CHSH_op A₀ A₁ B₀ B₁
  let c := 2 * Real.sqrt 2
  have hS_herm : S.IsHermitian := CHSH_op_isHermitian A₀ A₁ B₀ B₁ hT

  have hS_sq : IsPosSemidefComplex (8 • (1 : Matrix (Fin n) (Fin n) ℂ) - S * S) :=
    CHSH_op_sq_le_eight A₀ A₁ B₀ B₁ hT

  have hc_sq : c^2 = 8 := by
    simp only [c]
    rw [mul_pow]
    norm_num
  have hc : 0 ≤ c := by simp only [c]; positivity

  have hS_sq' : IsPosSemidefComplex ((c^2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - S * S) := by
    have h_sqrt : (2 * Real.sqrt 2)^2 = 8 := by
      rw [mul_pow]
      norm_num
    convert hS_sq using 2
    rw [h_sqrt]
    exact ofNat_smul_eq_nsmul ℝ 8 1

  have h_upper : IsPosSemidefComplex ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - S) :=
    posSemidef_sub_of_sq_le S hS_herm c hc hS_sq'
  have h_lower : IsPosSemidefComplex ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + S) :=
    posSemidef_add_of_sq_le S hS_herm c hc hS_sq'

  exact trace_bound_of_posSemidef_bounds (CHSH_op A₀ A₁ B₀ B₁) hS_herm (2 * √2) h_upper h_lower ρ

end QuantumInfo
