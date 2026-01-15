/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.ExpBounded.Basic

/-!
# Adjoint Properties of Bounded Exponentials

This file establishes that the adjoint of `exp(tB)` equals `exp(tB*)`.
This is crucial for proving unitarity of exponentials of skew-adjoint operators.

## Main results

* `adjoint_pow`: `(B^k)* = (B*)^k`
* `adjoint_expBounded`: `exp(tB)* = exp(tB*)`
* `tsum_apply_of_summable`: Applying a tsum of operators to a vector
* `inner_tsum_right'`: Inner product with tsum on the right
* `tsum_inner_left'`: Inner product with tsum on the left

-/

namespace QuantumMechanics.Yosida

open Complex Filter Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Power of adjoint -/

theorem adjoint_pow (B : H →L[ℂ] H) (k : ℕ) :
    (B ^ k).adjoint = B.adjoint ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    ext φ
    apply ext_inner_right ℂ
    intro ψ
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [ContinuousLinearMap.one_apply]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    ext φ
    apply ext_inner_right ℂ
    intro ψ
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [ContinuousLinearMap.mul_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left (B ^ k)]
    rw [ih]
    rw [← ContinuousLinearMap.adjoint_inner_left B]
    congr 1
    have h_comm : B.adjoint * B.adjoint ^ k = B.adjoint ^ k * B.adjoint := by
      rw [← pow_succ, ← pow_succ', add_comm]
    calc B.adjoint ((B.adjoint ^ k) φ)
        = (B.adjoint * B.adjoint ^ k) φ := rfl
      _ = (B.adjoint ^ k * B.adjoint) φ := by rw [h_comm]
      _ = (B.adjoint ^ k) (B.adjoint φ) := rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Tsum lemmas -/

lemma tsum_apply_of_summable (f : ℕ → H →L[ℂ] H) (hf : Summable f) (x : H) :
    (∑' n, f n) x = ∑' n, f n x := by
  let evalx : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H x
  calc (∑' n, f n) x
      = evalx (∑' n, f n) := rfl
    _ = ∑' n, evalx (f n) := evalx.map_tsum hf
    _ = ∑' n, f n x := rfl

lemma inner_tsum_right' (x : H) (f : ℕ → H) (hf : Summable f) :
    ⟪x, ∑' n, f n⟫_ℂ = ∑' n, ⟪x, f n⟫_ℂ := by
  let L : H →L[ℂ] ℂ := innerSL ℂ x
  have hL : ∀ y, L y = ⟪x, y⟫_ℂ := fun y => rfl
  calc ⟪x, ∑' n, f n⟫_ℂ
      = L (∑' n, f n) := (hL _).symm
    _ = ∑' n, L (f n) := L.map_tsum hf
    _ = ∑' n, ⟪x, f n⟫_ℂ := by simp only [hL]

lemma tsum_inner_left' (f : ℕ → H) (y : H) (hf : Summable f) :
    ⟪∑' n, f n, y⟫_ℂ = ∑' n, ⟪f n, y⟫_ℂ := by
  have h_conj : ⟪∑' n, f n, y⟫_ℂ = (starRingEnd ℂ) ⟪y, ∑' n, f n⟫_ℂ :=
    (inner_conj_symm (∑' n, f n) y).symm
  rw [h_conj, inner_tsum_right' y f hf]
  rw [conj_tsum]
  · congr 1
    ext n
    exact (inner_conj_symm (f n) y)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Adjoint of exponential -/

theorem adjoint_expBounded (B : H →L[ℂ] H) (t : ℝ) :
    (expBounded B t).adjoint = expBounded B.adjoint t := by
  unfold expBounded
  have h_summable : Summable (fun k : ℕ => (1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k) :=
    expBounded_summable B t
  have h_summable_adj : Summable (fun k : ℕ => (1 / k.factorial : ℂ) • ((t : ℂ) • B.adjoint) ^ k) :=
    expBounded_summable B.adjoint t
  ext φ
  apply ext_inner_right ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [tsum_apply_of_summable _ h_summable ψ]
  rw [tsum_apply_of_summable _ h_summable_adj φ]
  have h_inner_summable : Summable (fun k => ((1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k) ψ) := by
    apply Summable.of_norm
    have h_norm_sum := expBounded_norm_summable B t
    have h_scaled : Summable (fun k => ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖ * ‖ψ‖) :=
      h_norm_sum.mul_right ‖ψ‖
    apply Summable.of_nonneg_of_le
    · intro k; exact norm_nonneg _
    · intro k
      exact ContinuousLinearMap.le_opNorm _ _
    · exact h_scaled
  have h_inner_summable_adj : Summable
      (fun k => ((1 / k.factorial : ℂ) • ((t : ℂ) • B.adjoint) ^ k) φ) := by
    apply Summable.of_norm
    have h_norm_sum := expBounded_norm_summable B.adjoint t
    have h_scaled : Summable
        (fun k => ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B.adjoint) ^ k‖ * ‖φ‖) :=
      h_norm_sum.mul_right ‖φ‖
    apply Summable.of_nonneg_of_le
    · intro k; exact norm_nonneg _
    · intro k
      exact ContinuousLinearMap.le_opNorm _ _
    · exact h_scaled
  rw [inner_tsum_right' φ _ h_inner_summable]
  rw [tsum_inner_left' _ ψ h_inner_summable_adj]
  congr 1
  ext k
  simp only [ContinuousLinearMap.smul_apply]
  rw [inner_smul_right, inner_smul_left]
  have h_real : (starRingEnd ℂ) (1 / k.factorial : ℂ) = (1 / k.factorial : ℂ) := by
    simp only [map_div₀, map_one, map_natCast]
  rw [h_real]
  congr 1
  have h_smul_pow : ∀ (c : ℂ) (T : H →L[ℂ] H) (n : ℕ), (c • T) ^ n = c ^ n • T ^ n := by
    intro c T n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, pow_succ, ih]
      ext x
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply]
      rw [ContinuousLinearMap.map_smul]
      rw [smul_smul]
  rw [h_smul_pow, h_smul_pow]
  simp only [ContinuousLinearMap.smul_apply]
  rw [inner_smul_right, inner_smul_left]
  have h_t_real : (starRingEnd ℂ) ((t : ℂ) ^ k) = (t : ℂ) ^ k := by
    simp only [map_pow, conj_ofReal]
  rw [h_t_real]
  congr 1
  rw [← ContinuousLinearMap.adjoint_inner_left (B ^ k)]
  rw [adjoint_pow]

/-- Synonym for `adjoint_expBounded`. -/
lemma expBounded_adjoint (B : H →L[ℂ] H) (t : ℝ) :
    ContinuousLinearMap.adjoint (expBounded B t) = expBounded (ContinuousLinearMap.adjoint B) t :=
  adjoint_expBounded B t

end QuantumMechanics.Yosida
