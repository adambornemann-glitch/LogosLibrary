/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Identities

/-!
# Analyticity of the Resolvent

This file proves that the resolvent `R(z)` is analytic as a function of `z`
in the region where `Im(z) ≠ 0`. Specifically, we show that near any point
`z₀` with `Im(z₀) ≠ 0`, the resolvent has a convergent power series expansion.

## Main statements

* `resolventFun_hasSum`: Near `z₀`, the resolvent has power series
  `R(z) = ∑ₙ (z - z₀)ⁿ R(z₀)^{n+1}`

## Implementation notes

The proof uses the Neumann series: since `R(z₀)` is bounded by `1/|Im(z₀)|`,
for `z` close enough to `z₀` the operator `(z - z₀) R(z₀)` has norm less than 1,
and we can expand `R(z) = R(z₀) (1 - (z - z₀) R(z₀))⁻¹` using the Neumann series.

## Physics interpretation

Analyticity of the resolvent is fundamental to spectral theory. It allows us to
define the spectral projections via contour integrals (Stone's formula) and
underlies perturbation theory for quantum systems.
-/

namespace QuantumMechanics.Resolvent

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The resolvent has a convergent power series expansion near any point
    `z₀` with `Im(z₀) ≠ 0`. -/
theorem resolventFun_hasSum {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z₀ : OffRealAxis) (z : ℂ) (hz : ‖z - z₀.val‖ < |z₀.val.im|) :
    ∃ (hz' : z.im ≠ 0),
    HasSum (fun n => (z - z₀.val)^n • (resolventFun gen hsa z₀)^(n+1))
           (resolvent gen z hz' hsa) := by
  have hz' : z.im ≠ 0 := im_ne_zero_of_near z₀.property hz
  use hz'
  set R₀ := resolventFun gen hsa z₀ with hR₀_def
  set T := (z - z₀.val) • R₀ with hT_def
  have hT_norm : ‖T‖ < 1 := by
    have h_smul_bound : ‖T‖ ≤ ‖z - z₀.val‖ * ‖R₀‖ := by
      simp only [hT_def]
      exact norm_smul_le (z - z₀.val) R₀
    have h_R₀_bound : ‖R₀‖ ≤ 1 / |z₀.val.im| := resolventFun_bound gen hsa z₀
    calc ‖T‖
        ≤ ‖z - z₀.val‖ * ‖R₀‖ := h_smul_bound
      _ ≤ ‖z - z₀.val‖ * (1 / |z₀.val.im|) := by
          apply mul_le_mul_of_nonneg_left h_R₀_bound (norm_nonneg _)
      _ = ‖z - z₀.val‖ / |z₀.val.im| := by ring
      _ < |z₀.val.im| / |z₀.val.im| := by
          apply div_lt_div_of_pos_right hz (abs_pos.mpr z₀.property)
      _ = 1 := div_self (ne_of_gt (abs_pos.mpr z₀.property))
  have h_neumann := neumannSeries_hasSum T hT_norm
  -- Show that resolvents commute
  have h_comm : R₀.comp (resolvent gen z hz' hsa) =
              (resolvent gen z hz' hsa).comp R₀ := by
    have hR₀_eq : R₀ = resolvent gen z₀.val z₀.property hsa := rfl
    have h1 := resolvent_identity gen hsa z z₀.val hz' z₀.property
    have h2 := resolvent_identity gen hsa z₀.val z z₀.property hz'
    set Rz := resolvent gen z hz' hsa with hRz_def
    set Rz₀ := resolvent gen z₀.val z₀.property hsa with hRz₀_def
    have h_add : (Rz - Rz₀) + (Rz₀ - Rz) = 0 := by
      simp only [sub_add_sub_cancel, sub_self]
    rw [h1, h2] at h_add
    have h_factor : (z - z₀.val) • (Rz.comp Rz₀ - Rz₀.comp Rz) = 0 := by
      have h_neg : z₀.val - z = -(z - z₀.val) := by ring
      rw [h_neg, neg_smul] at h_add
      rw [← sub_eq_add_neg, ← smul_sub] at h_add
      exact h_add
    by_cases hzeq : z = z₀.val
    · simp only [hRz_def, hzeq]; rfl
    · have hz_sub_ne : z - z₀.val ≠ 0 := sub_ne_zero.mpr hzeq
      rw [smul_eq_zero] at h_factor
      cases h_factor with
      | inl h => exact absurd h hz_sub_ne
      | inr h => exact (eq_of_sub_eq_zero h).symm
  -- Express R(z) in terms of R(z₀) and Neumann series
  have h_resolvent_eq : resolvent gen z hz' hsa =
    R₀.comp (neumannSeries T hT_norm) := by
    set Rz := resolvent gen z hz' hsa with hRz_def
    have h_res_id := resolvent_identity gen hsa z₀.val z z₀.property hz'
    have h1 : Rz = R₀ + (z - z₀.val) • R₀.comp Rz := by
      have hsub : R₀ - Rz = (z₀.val - z) • R₀.comp Rz := h_res_id
      have hneg : (z₀.val - z) = -(z - z₀.val) := by ring
      rw [hneg, neg_smul] at hsub
      calc Rz = R₀ - (R₀ - Rz) := by abel
        _ = R₀ - (-((z - z₀.val) • R₀.comp Rz)) := by rw [hsub]
        _ = R₀ + (z - z₀.val) • R₀.comp Rz := by abel
    rw [h_comm] at h1
    have h2 : (z - z₀.val) • Rz.comp R₀ = Rz.comp T := by
      rw [hT_def, ContinuousLinearMap.comp_smul]
    rw [h2] at h1
    have h3 : Rz.comp (ContinuousLinearMap.id ℂ H - T) = R₀ := by
      have : Rz - Rz.comp T = R₀ := by exact sub_eq_iff_eq_add.mpr h1
      calc Rz.comp (ContinuousLinearMap.id ℂ H - T)
          = Rz.comp (ContinuousLinearMap.id ℂ H) - Rz.comp T := by
              rw [ContinuousLinearMap.comp_sub]
        _ = Rz - Rz.comp T := by rw [ContinuousLinearMap.comp_id]
        _ = R₀ := by exact this
    calc Rz = Rz.comp (ContinuousLinearMap.id ℂ H) := by rw [ContinuousLinearMap.comp_id]
      _ = Rz.comp ((ContinuousLinearMap.id ℂ H - T) * (neumannSeries T hT_norm)) := by
          rw [neumannSeries_mul_left T hT_norm]
      _ = Rz.comp ((ContinuousLinearMap.id ℂ H - T).comp (neumannSeries T hT_norm)) := rfl
      _ = (Rz.comp (ContinuousLinearMap.id ℂ H - T)).comp (neumannSeries T hT_norm) := by
          rw [ContinuousLinearMap.comp_assoc]
      _ = R₀.comp (neumannSeries T hT_norm) := by rw [h3]
  -- Show that each term matches
  have h_term_eq : ∀ n, R₀.comp (T^n) = (z - z₀.val)^n • R₀^(n+1) := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, one_smul]
      simp_all only [ne_eq, zero_add, pow_one, R₀, T]
      rfl
    | succ n ih =>
      calc R₀.comp (T^(n+1))
          = R₀.comp (T^n * T) := by rw [pow_succ]
        _ = (R₀.comp (T^n)).comp T := by rfl
        _ = ((z - z₀.val)^n • R₀^(n+1)).comp T := by rw [ih]
        _ = (z - z₀.val)^n • (R₀^(n+1)).comp ((z - z₀.val) • R₀) := by
            rw [ContinuousLinearMap.smul_comp]
        _ = (z - z₀.val)^n • ((z - z₀.val) • (R₀^(n+1)).comp R₀) := by
            rw [ContinuousLinearMap.comp_smul]
        _ = (z - z₀.val)^n • ((z - z₀.val) • R₀^(n+2)) := by
            congr 2
        _ = (z - z₀.val)^(n+1) • R₀^(n+2) := by
            rw [smul_smul]
            congr 1
  rw [h_resolvent_eq]
  have h_comp_hasSum : HasSum (fun n => R₀.comp (T^n)) (R₀.comp (neumannSeries T hT_norm)) :=
    ((ContinuousLinearMap.compL ℂ H H H) R₀).hasSum h_neumann
  convert h_comp_hasSum using 1
  · ext n
    exact Eq.symm (DFunLike.congr (h_term_eq n) rfl)

end QuantumMechanics.Resolvent
