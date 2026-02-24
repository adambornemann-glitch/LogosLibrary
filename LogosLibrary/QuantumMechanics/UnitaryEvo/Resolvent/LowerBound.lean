/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Basic
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner

/-!
# Lower Bound Estimate for Self-Adjoint Generators

This file proves the fundamental estimate for self-adjoint operators:
for `A` self-adjoint and `Im(z) ≠ 0`, we have `‖(A - zI)ψ‖ ≥ |Im(z)| · ‖ψ‖`.

This estimate is the key to proving that the resolvent is bounded and that
`(A - zI)` has closed range.

## Main statements

* `lower_bound_estimate`: `‖(A - zI)ψ‖ ≥ |Im(z)| · ‖ψ‖` for self-adjoint `A`

## Physics interpretation

This estimate shows that `(A - zI)` is bounded below when `z` is off the real axis.
The spectrum of a self-adjoint operator is real, so moving `z` off the real axis
creates a "gap" proportional to `|Im(z)|`.
-/

namespace QuantumMechanics.Resolvent

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The fundamental lower bound: for self-adjoint `A` and `Im(z) ≠ 0`,
    we have `‖(A - zI)ψ‖ ≥ |Im(z)| · ‖ψ‖`. -/
lemma lower_bound_estimate {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (z : ℂ) (_ : z.im ≠ 0)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ‖gen.op ⟨ψ, hψ⟩ - z • ψ‖ ≥ |z.im| * ‖ψ‖ := by
  set x := z.re
  set y := z.im
  have h_decomp : gen.op ⟨ψ, hψ⟩ - z • ψ = (gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ := by
    have hz_eq : z = x + y * I := by simp [x, y]
    calc gen.op ⟨ψ, hψ⟩ - z • ψ
        = gen.op ⟨ψ, hψ⟩ - (x + y * I) • ψ := by rw [hz_eq]
      _ = gen.op ⟨ψ, hψ⟩ - (x • ψ + (y * I) • ψ) := by rw [add_smul]; rfl
      _ = (gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ := by abel
  rw [h_decomp]
  have h_expand : ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖^2 =
                ‖gen.op ⟨ψ, hψ⟩ - x • ψ‖^2 + ‖(y * I) • ψ‖^2 +
                2 * (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, -((y * I) • ψ)⟫_ℂ).re := by
    have h_formula : ∀ (a b : H), ‖a - b‖^2 = ‖a‖^2 + ‖b‖^2 - 2 * (⟪a, b⟫_ℂ).re := by
      intro a b
      have h_inner : (⟪a - b, a - b⟫_ℂ).re = ‖a - b‖ ^ 2 := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (a - b)
        rw [this]; norm_cast
      rw [← h_inner, inner_sub_left, inner_sub_right, inner_sub_right]
      simp only [Complex.sub_re]
      have h1 : (⟪a, a⟫_ℂ).re = ‖a‖^2 := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) a
        rw [this]; norm_cast
      have h2 : (⟪b, b⟫_ℂ).re = ‖b‖^2 := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) b
        rw [this]; norm_cast
      rw [h1, h2]
      have h_cross : (⟪a, b⟫_ℂ).re + (⟪b, a⟫_ℂ).re = 2 * (⟪a, b⟫_ℂ).re := by
        have : (⟪b, a⟫_ℂ).re = (⟪a, b⟫_ℂ).re := by
          calc (⟪b, a⟫_ℂ).re
              = ((starRingEnd ℂ) ⟪a, b⟫_ℂ).re := by rw [inner_conj_symm]
            _ = (⟪a, b⟫_ℂ).re := by simp only [Complex.conj_re]
        rw [this]; ring
      rw [h_cross.symm]; ring
    calc ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖^2
        = ‖gen.op ⟨ψ, hψ⟩ - x • ψ‖^2 + ‖(y * I) • ψ‖^2 -
          2 * (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, (y * I) • ψ⟫_ℂ).re :=
            h_formula (gen.op ⟨ψ, hψ⟩ - x • ψ) ((y * I) • ψ)
      _ = ‖gen.op ⟨ψ, hψ⟩ - x • ψ‖^2 + ‖(y * I) • ψ‖^2 +
          2 * (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, -((y * I) • ψ)⟫_ℂ).re := by
          have : (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, -((y * I) • ψ)⟫_ℂ).re =
                 -(⟪gen.op ⟨ψ, hψ⟩ - x • ψ, (y * I) • ψ⟫_ℂ).re := by
            rw [inner_neg_right]; simp only [Complex.neg_re]
          rw [this]; ring
  have h_norm_scale : ‖(y * I) • ψ‖ = |y| * ‖ψ‖ := by
    calc ‖(y * I) • ψ‖
        = ‖(y * I : ℂ)‖ * ‖ψ‖ := norm_smul _ _
      _ = |y| * ‖ψ‖ := by simp
  have h_cross_zero : (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, -((y * I) • ψ)⟫_ℂ).re = 0 := by
    rw [inner_neg_right, inner_smul_right]
    have h_real : (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ).im = 0 := by
      rw [inner_sub_left]
      have h_Areal : (⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ).im = 0 := by
        have h_sym := gen.symmetric ⟨ψ, hψ⟩ ⟨ψ, hψ⟩
        have h_conj : ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ := by
          calc ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ
              = ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ := h_sym
            _ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ :=
                (inner_conj_symm ψ (gen.op ⟨ψ, hψ⟩)).symm
        have h_parts := Complex.ext_iff.mp h_conj
        simp only [Complex.conj_im] at h_parts
        linarith [h_parts.2]
      have h_xreal : (⟪x • ψ, ψ⟫_ℂ).im = 0 := by
        have h_eq : x • ψ = (x : ℂ) • ψ := (RCLike.real_smul_eq_coe_smul x ψ).symm
        rw [h_eq, inner_smul_left]
        have h_inner_real : (⟪ψ, ψ⟫_ℂ).im = 0 := by
          have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
          rw [this]; norm_cast
        simp [h_inner_real]
      simp [h_Areal, h_xreal]
    have h_as_real : ⟪gen.op ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ =
        ((⟪gen.op ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ).re : ℂ) := by
      conv_lhs => rw [← Complex.re_add_im (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ), h_real]
      simp
    rw [h_as_real]
    simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im,
              Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
    simp only [I_re, mul_zero, zero_mul, neg_zero]
  have h_sq : ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖^2 ≥ (|y| * ‖ψ‖)^2 := by
    rw [h_expand, h_norm_scale, h_cross_zero]
    simp only [mul_zero, add_zero]
    have : 0 ≤ ‖gen.op ⟨ψ, hψ⟩ - x • ψ‖^2 := sq_nonneg _
    linarith
  by_contra h_not
  push_neg at h_not
  have h1 : 0 ≤ ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖ := norm_nonneg _
  have h2 : 0 ≤ |y| * ‖ψ‖ := by
    apply mul_nonneg
    · exact abs_nonneg _
    · exact norm_nonneg _
  nlinarith [sq_nonneg (|y| * ‖ψ‖ - ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖), h_sq, h_not, h1, h2]

end QuantumMechanics.Resolvent
