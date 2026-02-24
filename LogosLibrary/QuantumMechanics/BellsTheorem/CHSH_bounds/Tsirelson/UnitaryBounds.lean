/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.BellsTheorem.CHSH_Bounds.Commuting

/-!
# Unitary Operator Bounds

This file develops the theory of unitary operators and Hermitian involutions needed for
Tsirelson's bound. The key results are:

* `unitary_add_conjTranspose_le_two`: For unitary U, we have 2I - (U + U†) ≥ 0
* `unitary_add_conjTranspose_ge_neg_two`: For unitary U, we have 2I + (U + U†) ≥ 0
* `involution_mul_involution_unitary`: Product of Hermitian involutions is unitary
* `unitary_add_conjTranspose_sq_le_four`: For unitary U, we have (U + U†)² ≤ 4I

These bounds are fundamental to establishing the 2√2 quantum limit.
-/

open scoped Matrix ComplexConjugate BigOperators TensorProduct
open MeasureTheory ProbabilityTheory Matrix Complex

namespace QuantumInfo

/-! ## Basic Inner Product Lemmas -/

/-- For any matrix, ⟨Ax, Ax⟩ = ⟨x, (A†A)x⟩ -/
lemma star_mulVec_dotProduct_self (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    star (A.mulVec x) ⬝ᵥ (A.mulVec x) = star x ⬝ᵥ (Aᴴ * A).mulVec x := by
  rw [Matrix.star_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_vecMul]
  exact Eq.symm (dotProduct_mulVec (star x) (Aᴴ * A) x)

/-! ## Unitary Norm Preservation -/

/-- Unitary matrices preserve the norm squared -/
lemma sum_normSq_mulVec_eq_of_unitary (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) (x : Fin n → ℂ) :
    ∑ i, ‖(U.mulVec x) i‖^2 = ∑ i, ‖x i‖^2 := by
  have h1 : star (U.mulVec x) ⬝ᵥ (U.mulVec x) = star x ⬝ᵥ (Uᴴ * U).mulVec x :=
    star_mulVec_dotProduct_self U x
  have h2 : Uᴴ * U = 1 := Matrix.mul_eq_one_comm.mpr hU
  rw [h2, Matrix.one_mulVec] at h1
  rw [star_dotProduct_self_eq_sum_normSq, star_dotProduct_self_eq_sum_normSq] at h1
  exact_mod_cast h1

/-- For unitary U: |⟨x, Ux⟩| ≤ ‖x‖² -/
lemma inner_mulVec_self_bound_unitary {n : ℕ} [NeZero n]
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1)
    (x : Fin n → ℂ) :
    ‖star x ⬝ᵥ U.mulVec x‖ ≤ ‖star x ⬝ᵥ x‖ := by
  let x' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  let y' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (U.mulVec x)
  have h_inner : star x ⬝ᵥ U.mulVec x = inner (𝕜 := ℂ) x' y' := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct]
    rw [dotProduct_comm]
    rfl
  rw [h_inner]
  have h_cs : ‖inner (𝕜 := ℂ) x' y'‖ ≤ ‖x'‖ * ‖y'‖ := norm_inner_le_norm x' y'
  have h_norm_y : ‖y'‖ = ‖x'‖ := by
    simp only [EuclideanSpace.norm_eq]
    congr 1
    exact sum_normSq_mulVec_eq_of_unitary U hU x
  rw [h_norm_y] at h_cs
  rw [norm_star_dotProduct_self]
  convert h_cs using 1
  ring_nf
  exact Eq.symm (EuclideanSpace.norm_sq_eq x')

/-! ## Unitary Operator Bounds -/

/-- For unitary U: 2I - (U + U†) is positive semidefinite -/
lemma unitary_add_conjTranspose_le_two {n : ℕ} [NeZero n]
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) :
    IsPosSemidefComplex (2 • (1 : Matrix (Fin n) (Fin n) ℂ) - (U + Uᴴ)) := by
  intro x
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
  simp only [dotProduct_sub, dotProduct_smul, dotProduct_add]
  -- Goal: 0 ≤ (2 • (star x ⬝ᵥ x) - (star x ⬝ᵥ U.mulVec x + star x ⬝ᵥ Uᴴ.mulVec x)).re
  have h_self_nonneg := star_dotProduct_self_re_nonneg x
  have h_self_eq : (star x ⬝ᵥ x).re = ∑ i, ‖x i‖^2 := by
    have := star_dotProduct_self_eq_sum_normSq x
    simp only at this ⊢
    exact congrArg Complex.re this
  -- Key: star x ⬝ᵥ Uᴴ.mulVec x = conj (star x ⬝ᵥ U.mulVec x)
  have h_conj : star x ⬝ᵥ Uᴴ.mulVec x = conj (star x ⬝ᵥ U.mulVec x) := by
    symm
    calc conj (star x ⬝ᵥ U.mulVec x)
        = star (star x ⬝ᵥ U.mulVec x) := rfl
      _ = star (U.mulVec x) ⬝ᵥ star (star x) := Eq.symm (star_dotProduct_star _ _)
      _ = star (U.mulVec x) ⬝ᵥ x := by rw [star_star]
      _ = Matrix.vecMul (star x) Uᴴ ⬝ᵥ x := by rw [Matrix.star_mulVec]
      _ = star x ⬝ᵥ Uᴴ.mulVec x := by rw [← Matrix.dotProduct_mulVec]
  -- So (⟨x,Ux⟩ + ⟨x,U†x⟩).re = 2 * Re⟨x,Ux⟩
  have h_sum_re : (star x ⬝ᵥ U.mulVec x + star x ⬝ᵥ Uᴴ.mulVec x).re =
                   2 * (star x ⬝ᵥ U.mulVec x).re := by
    rw [h_conj, add_re, conj_re]
    ring
  -- Goal: 0 ≤ (2 • (star x ⬝ᵥ x) - (star x ⬝ᵥ U *ᵥ x + star x ⬝ᵥ Uᴴ *ᵥ x)).re
  rw [sub_re, h_sum_re]
  -- Now deal with the smul
  have h_smul_re : (2 • (star x ⬝ᵥ x)).re = 2 * (star x ⬝ᵥ x).re := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
  rw [h_smul_re, h_self_eq]
  -- Goal: 0 ≤ 2 * ∑ i, ‖x i‖^2 - 2 * (star x ⬝ᵥ U.mulVec x).re
  have h_bound := inner_mulVec_self_bound_unitary U hU x
  rw [norm_star_dotProduct_self] at h_bound
  have h_re_le : (star x ⬝ᵥ U.mulVec x).re ≤ ∑ i, ‖x i‖^2 := by
    have h_abs : |(star x ⬝ᵥ U.mulVec x).re| ≤ ‖star x ⬝ᵥ U.mulVec x‖ := Complex.abs_re_le_norm _
    have h_le_abs : (star x ⬝ᵥ U.mulVec x).re ≤ |(star x ⬝ᵥ U.mulVec x).re| := le_abs_self _
    linarith
  linarith

/-! ## Hermitian Involutions -/

/-- For Hermitian involutions, A₀A₁ is unitary -/
lemma involution_mul_involution_unitary {n : ℕ} [NeZero n]
    (A₀ A₁ : Matrix (Fin n) (Fin n) ℂ)
    (hA₀_herm : A₀.IsHermitian) (hA₁_herm : A₁.IsHermitian)
    (hA₀_sq : A₀ * A₀ = 1) (hA₁_sq : A₁ * A₁ = 1) :
    (A₀ * A₁) * (A₀ * A₁)ᴴ = 1 := by
  rw [Matrix.conjTranspose_mul, hA₀_herm.eq, hA₁_herm.eq]
  calc (A₀ * A₁) * (A₁ * A₀)
      = A₀ * (A₁ * A₁) * A₀ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = A₀ * 1 * A₀ := by rw [hA₁_sq]
    _ = A₀ * A₀ := by rw [Matrix.mul_one]
    _ = 1 := hA₀_sq

/-- For unitary U: (U + U†) + 2I is positive semidefinite -/
lemma unitary_add_conjTranspose_ge_neg_two {n : ℕ} [NeZero n]
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) :
    IsPosSemidefComplex (2 • (1 : Matrix (Fin n) (Fin n) ℂ) + (U + Uᴴ)) := by
  intro x
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [dotProduct_add, dotProduct_smul]
  have h_conj : star x ⬝ᵥ Uᴴ.mulVec x = conj (star x ⬝ᵥ U.mulVec x) := by
    symm
    calc conj (star x ⬝ᵥ U.mulVec x)
        = star (star x ⬝ᵥ U.mulVec x) := rfl
      _ = star (U.mulVec x) ⬝ᵥ star (star x) := Eq.symm (star_dotProduct_star _ _)
      _ = star (U.mulVec x) ⬝ᵥ x := by rw [star_star]
      _ = Matrix.vecMul (star x) Uᴴ ⬝ᵥ x := by rw [Matrix.star_mulVec]
      _ = star x ⬝ᵥ Uᴴ.mulVec x := by rw [← Matrix.dotProduct_mulVec]
  have h_sum_re : (star x ⬝ᵥ U.mulVec x + star x ⬝ᵥ Uᴴ.mulVec x).re =
                   2 * (star x ⬝ᵥ U.mulVec x).re := by
    rw [h_conj, add_re, conj_re]
    ring
  rw [add_re, h_sum_re]
  have h_smul_re : (2 • (star x ⬝ᵥ x)).re = 2 * (star x ⬝ᵥ x).re := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
  rw [h_smul_re]
  have h_self_eq : (star x ⬝ᵥ x).re = ∑ i, ‖x i‖^2 := by
    have := star_dotProduct_self_eq_sum_normSq x
    simp only at this ⊢
    exact congrArg Complex.re this
  rw [h_self_eq]
  -- Goal: 0 ≤ 2 * ∑ i, ‖x i‖^2 + 2 * (star x ⬝ᵥ U.mulVec x).re
  have h_bound := inner_mulVec_self_bound_unitary U hU x
  rw [norm_star_dotProduct_self] at h_bound
  have h_re_ge : -(∑ i, ‖x i‖^2) ≤ (star x ⬝ᵥ U.mulVec x).re := by
    have h_abs : |(star x ⬝ᵥ U.mulVec x).re| ≤ ‖star x ⬝ᵥ U.mulVec x‖ := Complex.abs_re_le_norm _
    have h_neg_le_abs : -|(star x ⬝ᵥ U.mulVec x).re| ≤ (star x ⬝ᵥ U.mulVec x).re := neg_abs_le _
    linarith
  linarith

/-! ## Norm Bounds for U + U† -/

/-- For unitary U: ‖(U + U†)x‖ ≤ 2‖x‖ -/
lemma norm_unitary_add_conjTranspose_mulVec {n : ℕ} [NeZero n]
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1)
    (x : Fin n → ℂ) :
    ∑ i, ‖((U + Uᴴ).mulVec x) i‖^2 ≤ 4 * ∑ i, ‖x i‖^2 := by
  -- (U + U†)x = Ux + U†x, so ‖(U + U†)x‖ ≤ ‖Ux‖ + ‖U†x‖ = 2‖x‖
  have hUH_U : Uᴴ * U = 1 := Matrix.mul_eq_one_comm.mpr hU
  have hUH_unitary : Uᴴ * Uᴴᴴ = 1 := by simp [hUH_U]
  have h_U_norm : ∑ i, ‖(U.mulVec x) i‖^2 = ∑ i, ‖x i‖^2 :=
    sum_normSq_mulVec_eq_of_unitary U hU x
  have h_UH_norm : ∑ i, ‖(Uᴴ.mulVec x) i‖^2 = ∑ i, ‖x i‖^2 :=
    sum_normSq_mulVec_eq_of_unitary Uᴴ hUH_unitary x
  -- Use triangle inequality in EuclideanSpace
  let x' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  let Ux' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (U.mulVec x)
  let UHx' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (Uᴴ.mulVec x)
  have h_add : (U + Uᴴ).mulVec x = U.mulVec x + Uᴴ.mulVec x := Matrix.add_mulVec U Uᴴ x
  have h_norm_sq : ∑ i, ‖((U + Uᴴ).mulVec x) i‖^2 = ‖WithLp.toLp 2 ((U + Uᴴ).mulVec x)‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h_norm_x : ∑ i, ‖x i‖^2 = ‖x'‖^2 := by rw [EuclideanSpace.norm_sq_eq]; rfl
  have h_norm_Ux : ‖Ux'‖^2 = ∑ i, ‖(U.mulVec x) i‖^2 := by rw [EuclideanSpace.norm_sq_eq]; rfl
  have h_norm_UHx : ‖UHx'‖^2 = ∑ i, ‖(Uᴴ.mulVec x) i‖^2 := by rw [EuclideanSpace.norm_sq_eq]; rfl
  rw [h_norm_sq, h_add]
  have h_triangle : ‖WithLp.toLp 2 (U.mulVec x + Uᴴ.mulVec x)‖ ≤ ‖Ux'‖ + ‖UHx'‖ := by
    have : WithLp.toLp 2 (U.mulVec x + Uᴴ.mulVec x) = Ux' + UHx' := by
      ext i; simp [Ux', UHx']
    rw [this]
    exact norm_add_le Ux' UHx'
  have h_Ux_eq : ‖Ux'‖ = ‖x'‖ := by
    rw [← Real.sqrt_sq (norm_nonneg Ux'), ← Real.sqrt_sq (norm_nonneg x')]
    congr 1
    rw [h_norm_Ux, h_U_norm, ← h_norm_x]
  have h_UHx_eq : ‖UHx'‖ = ‖x'‖ := by
    rw [← Real.sqrt_sq (norm_nonneg UHx'), ← Real.sqrt_sq (norm_nonneg x')]
    congr 1
    rw [h_norm_UHx, h_UH_norm, ← h_norm_x]
  calc ‖WithLp.toLp 2 (U.mulVec x + Uᴴ.mulVec x)‖^2
      ≤ (‖Ux'‖ + ‖UHx'‖)^2 := sq_le_sq' (by linarith [norm_nonneg (WithLp.toLp 2 (U.mulVec x + Uᴴ.mulVec x))]) h_triangle
    _ = (‖x'‖ + ‖x'‖)^2 := by rw [h_Ux_eq, h_UHx_eq]
    _ = 4 * ‖x'‖^2 := by ring
    _ = 4 * ∑ i, ‖x i‖^2 := by rw [h_norm_x]

/-- For unitary U and H = U + U†: H² ≤ 4I -/
lemma unitary_add_conjTranspose_sq_le_four {n : ℕ} [NeZero n]
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) :
    IsPosSemidefComplex (4 • (1 : Matrix (Fin n) (Fin n) ℂ) - (U + Uᴴ) * (U + Uᴴ)) := by
  intro x
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [dotProduct_sub, dotProduct_smul]
  rw [sub_re]
  have h_smul : (4 • (star x ⬝ᵥ x)).re = 4 * (star x ⬝ᵥ x).re := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
  rw [h_smul]
  have h_self_eq : (star x ⬝ᵥ x).re = ∑ i, ‖x i‖^2 := by
    have := star_dotProduct_self_eq_sum_normSq x
    simp only at this ⊢
    exact congrArg Complex.re this
  rw [h_self_eq]
  let H := U + Uᴴ
  have hH_herm : H.IsHermitian := by
    simp only [H, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    module
  have h_sq : star x ⬝ᵥ (H * H).mulVec x = star (H.mulVec x) ⬝ᵥ H.mulVec x := by
    rw [star_mulVec_dotProduct_mulVec_hermitian H hH_herm x]
  have h_sq_re : (star x ⬝ᵥ (H * H).mulVec x).re = ∑ i, ‖(H.mulVec x) i‖^2 := by
    rw [h_sq, star_dotProduct_self_eq_sum_normSq]
    simp only [ofReal_re]
  rw [h_sq_re]
  have h_bound := norm_unitary_add_conjTranspose_mulVec U hU x
  linarith

end QuantumInfo
