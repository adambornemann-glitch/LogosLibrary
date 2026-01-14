/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform.Eigenvalue

/-!
# Spectral Correspondence for the Cayley Transform

This file proves the full spectral correspondence between a self-adjoint operator `A` and
its Cayley transform `U`: `μ` is in the approximate point spectrum of `A` if and only if
`(μ - i)/(μ + i)` is in the spectrum of `U`.

## Main statements

* `cayley_maps_resolvent`: The Cayley transform maps resolvent sets appropriately
* `cayley_spectrum_backward`: Invertibility of `U - w` implies `A - μ` is bounded below
* `cayley_approx_eigenvalue_backward`: Approximate eigenvalues of `U` give approximate
  eigenvalues of `A`
* `cayley_approx_eigenvalue_forward`: Approximate eigenvalues of `A` give approximate
  eigenvalues of `U`
* `cayley_spectrum_correspondence`: Full spectral correspondence
-/

namespace QuantumMechanics.Cayley

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Bochner QuantumMechanics.Generators

set_option maxHeartbeats 300000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Cayley transform maps non-real spectral values to invertible operators. -/
theorem cayley_maps_resolvent {U_grp : OneParameterUnitaryGroup (H := H)} [Nontrivial H]
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : ℂ) (hz : z.im ≠ 0) :
    let w := (z - I) * (z + I)⁻¹
    IsUnit (cayleyTransform gen hsa - w • ContinuousLinearMap.id ℂ H) := by
  intro w
  have hw_norm_ne_one : ‖w‖ ≠ 1 := by
    simp only [w, norm_mul, norm_inv]
    intro h_eq
    have h_abs_eq : ‖z - I‖ = ‖z + I‖ := by
      have h_ne : ‖z + I‖ ≠ 0 := by
        simp_all only [ne_eq, norm_eq_zero]
        apply Aesop.BuiltinRules.not_intro
        intro a
        simp_all only [norm_zero, inv_zero, mul_zero, zero_ne_one]
      calc ‖z - I‖ = ‖z - I‖ / ‖z + I‖ * ‖z + I‖ := by field_simp
        _ = 1 * ‖z + I‖ := by exact congrFun (congrArg HMul.hMul h_eq) ‖z + I‖
        _ = ‖z + I‖ := one_mul _
    have : z.im = 0 := by
      have h1 : ‖z - I‖ ^ 2 = z.re ^ 2 + (z.im - 1) ^ 2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq, Complex.I_re, Complex.I_im]
        ring
      have h2 : ‖z + I‖ ^ 2 = z.re ^ 2 + (z.im + 1) ^ 2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq, Complex.I_re, Complex.I_im]
        ring
      have h3 : ‖z - I‖ ^ 2 = ‖z + I‖ ^ 2 := by rw [h_abs_eq]
      rw [h1, h2] at h3
      nlinarith
    exact hz this
  have hU := cayleyTransform_unitary gen hsa
  set U := cayleyTransform gen hsa with hU_def
  rcases hw_norm_ne_one.lt_or_gt with hw_lt | hw_gt
  · have h_adj_norm : ‖w • U.adjoint‖ < 1 := by
      calc ‖w • U.adjoint‖
          ≤ ‖w‖ * ‖U.adjoint‖ := by exact
            ContinuousLinearMap.opNorm_smul_le w (ContinuousLinearMap.adjoint U)
        _ = ‖w‖ * 1 := by
          congr 1
          simp only [LinearIsometryEquiv.norm_map]
          exact cayleyTransform_norm_one gen hsa
        _ = ‖w‖ := mul_one _
        _ < 1 := hw_lt
    have h_inv : IsUnit (ContinuousLinearMap.id ℂ H - w • U.adjoint) :=
      Resolvent.isUnit_one_sub (w • U.adjoint) h_adj_norm
    have h_factor : U - w • ContinuousLinearMap.id ℂ H =
        U.comp (ContinuousLinearMap.id ℂ H - w • U.adjoint) := by
      ext ψ
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
      have hUU : U.comp U.adjoint = ContinuousLinearMap.id ℂ H :=
        cayleyTransform_comp_adjoint gen hsa
      rw [map_sub, map_smul]
      congr 1
      have : U (U.adjoint ψ) = ψ := by
        calc U (U.adjoint ψ) = (U.comp U.adjoint) ψ := rfl
          _ = (ContinuousLinearMap.id ℂ H) ψ := by rw [hUU]
          _ = ψ := rfl
      exact congrArg (HSMul.hSMul w) (id (Eq.symm this))
    rw [h_factor]
    exact (cayleyTransform_isUnit gen hsa).mul h_inv
  · have hw_ne : w ≠ 0 := fun h => by
      simp only [h, norm_zero] at hw_gt
      exact not_lt.mpr zero_le_one hw_gt
    have h_inv_norm : ‖w⁻¹ • U‖ < 1 := by
      calc ‖w⁻¹ • U‖
          ≤ ‖w⁻¹‖ * ‖U‖ := by exact ContinuousLinearMap.opNorm_smul_le w⁻¹ U
        _ = ‖w‖⁻¹ * 1 := by rw [norm_inv, cayleyTransform_norm_one gen hsa]
        _ = ‖w‖⁻¹ := mul_one _
        _ < 1 := inv_lt_one_of_one_lt₀ hw_gt
    have h_inv : IsUnit (ContinuousLinearMap.id ℂ H - w⁻¹ • U) :=
      Resolvent.isUnit_one_sub (w⁻¹ • U) h_inv_norm
    have h_factor : U - w • ContinuousLinearMap.id ℂ H =
        -w • (ContinuousLinearMap.id ℂ H - w⁻¹ • U) := by
      ext ψ
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply, smul_sub, smul_smul]
      rw [neg_mul, mul_inv_cancel₀ hw_ne]
      simp_all only [ne_eq, Complex.norm_mul, norm_inv, mul_eq_zero, inv_eq_zero,
                     not_or, mul_inv_rev, inv_inv, neg_smul, one_smul, sub_neg_eq_add, w, U]
      obtain ⟨left, right⟩ := hU
      obtain ⟨left_1, right_1⟩ := hw_ne
      exact sub_eq_neg_add ((cayleyTransform gen hsa) ψ) (((z - I) * (z + I)⁻¹) • ψ)
    rw [h_factor]
    have hw_neg_unit : IsUnit (-w) := Ne.isUnit (neg_ne_zero.mpr hw_ne)
    have h_smul_eq : -w • (ContinuousLinearMap.id ℂ H - w⁻¹ • U) =
        (-w • ContinuousLinearMap.id ℂ H) * (ContinuousLinearMap.id ℂ H - w⁻¹ • U) := by
      ext ψ
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply]
    rw [h_smul_eq]
    apply IsUnit.mul _ h_inv
    refine ⟨⟨-w • ContinuousLinearMap.id ℂ H, (-w)⁻¹ • ContinuousLinearMap.id ℂ H, ?_, ?_⟩, rfl⟩
    · ext ψ
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply, ContinuousLinearMap.one_apply,
                smul_smul, mul_inv_cancel₀ (neg_ne_zero.mpr hw_ne), one_smul]
    · ext ψ
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply, ContinuousLinearMap.one_apply,
                smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hw_ne), one_smul]

/-- If `U - w` is invertible, then `A - μ` is bounded below. -/
lemma cayley_spectrum_backward {U_grp : OneParameterUnitaryGroup (H := H)} [Nontrivial H]
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (h_unit : IsUnit (cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H)) :
    ∃ C : ℝ, C > 0 ∧ ∀ ψ (hψ : ψ ∈ gen.domain), ‖gen.op ⟨ψ, hψ⟩ - μ • ψ‖ ≥ C * ‖ψ‖ := by
  set U := cayleyTransform gen hsa with hU_def
  set w := (↑μ - I) * (↑μ + I)⁻¹ with hw_def
  have hμ_ne : (↑μ : ℂ) + I ≠ 0 := real_add_I_ne_zero μ
  obtain ⟨⟨T, T_inv, hT_left, hT_right⟩, hT_eq⟩ := h_unit
  simp only at hT_eq
  have hT_inv_ne : T_inv ≠ 0 := by
    intro h
    have : (1 : H →L[ℂ] H) = 0 := by
      calc (1 : H →L[ℂ] H) = T_inv * T := hT_right.symm
        _ = 0 * T := by rw [h]
        _ = 0 := zero_mul T
    exact one_ne_zero this
  have hT_inv_norm_pos : ‖T_inv‖ > 0 := norm_pos_iff.mpr hT_inv_ne
  have h_T_bounded_below : ∀ φ, ‖T φ‖ ≥ ‖T_inv‖⁻¹ * ‖φ‖ := by
    intro φ
    have h := ContinuousLinearMap.le_opNorm T_inv (T φ)
    have h' : T_inv (T φ) = φ := by
      have := congr_arg (· φ) hT_right
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
      exact this
    rw [h'] at h
    exact (inv_mul_le_iff₀ hT_inv_norm_pos).mpr h
  have h_one_sub_w_ne : (1 : ℂ) - w ≠ 0 := one_sub_mobius_ne_zero μ hμ_ne
  have h_one_sub_w_norm_pos : ‖(1 : ℂ) - w‖ > 0 := norm_pos_iff.mpr h_one_sub_w_ne
  use ‖T_inv‖⁻¹ / ‖(1 : ℂ) - w‖
  constructor
  · positivity
  intro ψ hψ
  let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
  have h_key : T φ = ((1 : ℂ) - w) • (gen.op ⟨ψ, hψ⟩ - ↑μ • ψ) := by
    rw [hT_eq]
    exact cayley_shift_identity gen hsa μ hμ_ne ψ hψ
  have h_phi_bound : ‖φ‖ ≥ ‖ψ‖ := by
    have h_sq := self_adjoint_norm_sq_add gen hsa ψ hψ
    have h_ge : ‖φ‖^2 ≥ ‖ψ‖^2 := by
      calc ‖φ‖^2 = ‖gen.op ⟨ψ, hψ⟩‖^2 + ‖ψ‖^2 := h_sq
        _ ≥ 0 + ‖ψ‖^2 := by linarith [sq_nonneg ‖gen.op ⟨ψ, hψ⟩‖]
        _ = ‖ψ‖^2 := by ring
    nlinarith [norm_nonneg φ, norm_nonneg ψ, sq_nonneg (‖φ‖ - ‖ψ‖)]
  have h_Tφ_eq : ‖T φ‖ = ‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - ↑μ • ψ‖ := by
    rw [h_key, norm_smul]
  have h_chain : ‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - ↑μ • ψ‖ ≥ ‖T_inv‖⁻¹ * ‖ψ‖ := by
    calc ‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - ↑μ • ψ‖
        = ‖T φ‖ := h_Tφ_eq.symm
      _ ≥ ‖T_inv‖⁻¹ * ‖φ‖ := h_T_bounded_below φ
      _ ≥ ‖T_inv‖⁻¹ * ‖ψ‖ := by apply mul_le_mul_of_nonneg_left h_phi_bound; positivity
  calc ‖gen.op ⟨ψ, hψ⟩ - ↑μ • ψ‖
      = ‖(1 : ℂ) - w‖⁻¹ * (‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - ↑μ • ψ‖) := by
          field_simp [ne_of_gt h_one_sub_w_norm_pos]
    _ ≥ ‖(1 : ℂ) - w‖⁻¹ * (‖T_inv‖⁻¹ * ‖ψ‖) := by
          apply mul_le_mul_of_nonneg_left h_chain; positivity
    _ = ‖T_inv‖⁻¹ / ‖(1 : ℂ) - w‖ * ‖ψ‖ := by ring

/-- If `U - w` is bounded below, then `A - μ` is bounded below. -/
lemma cayley_shift_bounded_below_backward {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (hμ_ne : (↑μ : ℂ) + I ≠ 0)
    (c : ℝ) (hc_pos : c > 0)
    (hc_bound : ∀ φ, ‖(cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ‖ ≥ c * ‖φ‖) :
    ∃ C > 0, ∀ ψ (hψ : ψ ∈ gen.domain), ‖gen.op ⟨ψ, hψ⟩ - μ • ψ‖ ≥ C * ‖ψ‖ := by
  set U := cayleyTransform gen hsa
  set w := (↑μ - I) * (↑μ + I)⁻¹
  have h_one_sub_w_norm_pos := one_sub_mobius_norm_pos μ hμ_ne
  use c / ‖(1 : ℂ) - w‖
  constructor
  · positivity
  · intro ψ hψ
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    have h_key := cayley_shift_identity gen hsa μ hμ_ne ψ hψ
    have h_bound : ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ ≥ c * ‖φ‖ := hc_bound φ
    have h_phi_bound : ‖φ‖ ≥ ‖ψ‖ := by
      have h_sq := self_adjoint_norm_sq_add gen hsa ψ hψ
      have h1 : ‖φ‖^2 = ‖gen.op ⟨ψ, hψ⟩‖^2 + ‖ψ‖^2 := h_sq
      have h2 : ‖φ‖^2 ≥ ‖ψ‖^2 := by rw [h1]; linarith [sq_nonneg ‖gen.op ⟨ψ, hψ⟩‖]
      nlinarith [norm_nonneg φ, norm_nonneg ψ, sq_nonneg ‖φ‖, sq_nonneg ‖ψ‖]
    have h_chain : ‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - (↑μ • ψ)‖ ≥ c * ‖ψ‖ := by
      have h_eq : ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ =
                  ‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - (↑μ • ψ)‖ := by
        simp only [U, w, φ] at h_key ⊢
        rw [h_key, norm_smul]
      calc ‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - (↑μ • ψ)‖
          = ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ := h_eq.symm
        _ ≥ c * ‖φ‖ := h_bound
        _ ≥ c * ‖ψ‖ := mul_le_mul_of_nonneg_left h_phi_bound (le_of_lt hc_pos)
    have h_ne := ne_of_gt h_one_sub_w_norm_pos
    calc ‖gen.op ⟨ψ, hψ⟩ - ↑μ • ψ‖
        = ‖(1 : ℂ) - w‖⁻¹ * (‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - (↑μ • ψ)‖) := by
            field_simp [h_ne]
            exact Eq.symm (mul_div_cancel_right₀ ‖gen.op ⟨ψ, hψ⟩ - μ • ψ‖ h_ne)
      _ ≥ ‖(1 : ℂ) - w‖⁻¹ * (c * ‖ψ‖) :=
            mul_le_mul_of_nonneg_left h_chain (inv_nonneg.mpr (norm_nonneg _))
      _ = c / ‖(1 : ℂ) - w‖ * ‖ψ‖ := by ring


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- Lower bound on `‖ψ‖` from approximate eigenvalue data. -/
lemma approx_eigenvalue_norm_lower_bound {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (ψ : H) (hψ : ψ ∈ gen.domain) (hψ_ne : ψ ≠ 0)
    (h_norm : ‖gen.op ⟨ψ, hψ⟩ + I • ψ‖ = 1)
    (δ : ℝ) (hδ_pos : 0 ≤ δ) (hδ_small : δ^2 < 1 + μ^2)
    (h_approx : ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ ≤ δ) :
    ‖ψ‖ ≥ (Real.sqrt (1 + μ^2 - δ^2) - |μ| * δ) / (1 + μ^2) := by
  have h_pythag := self_adjoint_norm_sq_add gen hsa ψ hψ
  have h_sum_one : ‖gen.op ⟨ψ, hψ⟩‖^2 + ‖ψ‖^2 = 1 := by
    have : ‖gen.op ⟨ψ, hψ⟩ + I • ψ‖^2 = 1 := by rw [h_norm]; ring
    linarith [h_pythag]
  have h_Aμψ_bound : ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ ≤ δ := h_approx
  have h_triangle : |‖gen.op ⟨ψ, hψ⟩‖ - |μ| * ‖ψ‖| ≤ δ := by
    have h1 : ‖(↑μ : ℂ) • ψ‖ = |μ| * ‖ψ‖ := by
      rw [norm_smul]
      simp only [norm_real, Real.norm_eq_abs]
    calc |‖gen.op ⟨ψ, hψ⟩‖ - |μ| * ‖ψ‖|
        = |‖gen.op ⟨ψ, hψ⟩‖ - ‖(↑μ : ℂ) • ψ‖| := by rw [h1]
      _ ≤ ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ := abs_norm_sub_norm_le _ _
      _ ≤ δ := h_approx
  have h_Aψ_lower : ‖gen.op ⟨ψ, hψ⟩‖ ≥ |μ| * ‖ψ‖ - δ := by
    have ⟨h1, _⟩ := abs_le.mp h_triangle
    linarith
  set x := ‖ψ‖ with hx_def
  have hx_pos : x > 0 := norm_pos_iff.mpr hψ_ne
  have h_Aψ_upper : ‖gen.op ⟨ψ, hψ⟩‖ ≤ |μ| * x + δ := by
    have ⟨_, h2⟩ := abs_le.mp h_triangle
    linarith
  have h_Aψ_sq : ‖gen.op ⟨ψ, hψ⟩‖^2 = 1 - x^2 := by linarith [h_sum_one]
  have h_ineq : (1 + μ^2) * x^2 + 2 * |μ| * δ * x + (δ^2 - 1) ≥ 0 := by
    have h1 : 1 - x^2 ≤ (|μ| * x + δ)^2 := by
      calc 1 - x^2 = ‖gen.op ⟨ψ, hψ⟩‖^2 := h_Aψ_sq.symm
        _ ≤ (|μ| * x + δ)^2 := by
            apply sq_le_sq'
            · linarith [norm_nonneg (gen.op ⟨ψ, hψ⟩), hδ_pos,
                        mul_nonneg (abs_nonneg μ) (le_of_lt hx_pos)]
            · exact h_Aψ_upper
    calc (1 + μ^2) * x^2 + 2 * |μ| * δ * x + (δ^2 - 1)
        = μ^2 * x^2 + 2 * |μ| * δ * x + δ^2 + x^2 - 1 := by ring
      _ = (|μ| * x + δ)^2 - (1 - x^2) := by rw [← sq_abs μ]; ring
      _ ≥ 0 := by linarith [h1]
  have h_discriminant : 1 + μ^2 - δ^2 > 0 := by linarith [hδ_small]
  have h_sqrt_exists : Real.sqrt (1 + μ^2 - δ^2) > 0 := Real.sqrt_pos.mpr h_discriminant
  set t_plus := (Real.sqrt (1 + μ^2 - δ^2) - |μ| * δ) / (1 + μ^2) with htplus_def
  set t_minus := (-Real.sqrt (1 + μ^2 - δ^2) - |μ| * δ) / (1 + μ^2) with htminus_def
  have htminus_neg : t_minus < 0 := by
    rw [htminus_def]
    apply div_neg_of_neg_of_pos
    · linarith [h_sqrt_exists, mul_nonneg (abs_nonneg μ) hδ_pos]
    · linarith [sq_nonneg μ]
  have h_coeff_pos : 1 + μ^2 > 0 := by linarith [sq_nonneg μ]
  have h_at_root : (1 + μ^2) * t_plus^2 + 2 * |μ| * δ * t_plus + (δ^2 - 1) = 0 := by
    rw [htplus_def]
    field_simp
    rw [← sq_abs μ]
    ring_nf
    have h_sq : Real.sqrt (1 + (|μ|^2 - δ^2)) ^ 2 = 1 + (|μ|^2 - δ^2) := by
      apply Real.sq_sqrt
      have : |μ|^2 = μ^2 := sq_abs μ
      linarith [h_discriminant]
    rw [h_sq]
    ring
  have h_x_ge_t_plus : x ≥ t_plus := by
    by_contra h_lt
    push_neg at h_lt
    have h_neg : (1 + μ^2) * x^2 + 2 * |μ| * δ * x + (δ^2 - 1) < 0 := by
      have h_factored : ∀ t, (1 + μ^2) * t^2 + 2 * |μ| * δ * t + (δ^2 - 1) =
                  (1 + μ^2) * (t - t_minus) * (t - t_plus) := by
        intro t
        rw [htplus_def, htminus_def]
        field_simp
        rw [← sq_abs μ]
        ring_nf
        have h_sq : Real.sqrt (1 + (|μ|^2 - δ^2)) ^ 2 = 1 + (|μ|^2 - δ^2) := by
          apply Real.sq_sqrt
          have : |μ|^2 = μ^2 := sq_abs μ
          linarith [h_discriminant]
        rw [h_sq]
        ring
      rw [h_factored]
      apply mul_neg_of_pos_of_neg
      · apply mul_pos h_coeff_pos
        linarith [htminus_neg]
      · linarith [h_lt]
    linarith [h_ineq, h_neg]
  calc ‖ψ‖ = x := rfl
    _ ≥ t_plus := h_x_ge_t_plus
    _ = (Real.sqrt (1 + μ^2 - δ^2) - |μ| * δ) / (1 + μ^2) := htplus_def

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- Approximate eigenvalues of `U` give approximate eigenvalues of `A`. -/
lemma cayley_approx_eigenvalue_backward {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧
      ‖(cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ‖ < ε) →
    (∀ C > 0, ∃ ψ, ∃ hψ : ψ ∈ gen.domain, ‖ψ‖ ≠ 0 ∧ ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ < C * ‖ψ‖) := by
  intro h_approx C hC
  set U := cayleyTransform gen hsa with hU_def
  set w := (↑μ - I) * (↑μ + I)⁻¹ with hw_def
  have h_one_sub_w_ne : (1 : ℂ) - w ≠ 0 := one_sub_mobius_ne_zero μ hμ_ne
  have h_one_sub_w_norm_pos : ‖(1 : ℂ) - w‖ > 0 := norm_pos_iff.mpr h_one_sub_w_ne
  set denom := Real.sqrt (1 + μ^2) with hdenom
  have hdenom_pos : denom > 0 := Real.sqrt_pos.mpr (by linarith [sq_nonneg μ])
  have hdenom_ge_one : denom ≥ 1 := by
    rw [hdenom]
    calc Real.sqrt (1 + μ^2) ≥ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith [sq_nonneg μ])
      _ = 1 := Real.sqrt_one
  set C' := min C (1/2) with hC'_def
  have hC'_pos : C' > 0 := lt_min hC (by norm_num : (0:ℝ) < 1/2)
  have hC'_le_half : C' ≤ 1/2 := min_le_right C (1/2)
  have hC'_le_C : C' ≤ C := min_le_left C (1/2)
  obtain ⟨φ, hφ_norm, hφ_bound⟩ := h_approx (C' * ‖(1 : ℂ) - w‖ / (2 * denom)) (by positivity)
  set ψ := Resolvent.resolvent_at_neg_i gen hsa φ with hψ_def
  have hψ_mem : ψ ∈ gen.domain := Resolvent.resolvent_solution_mem_plus gen hsa φ
  have hφ_eq : gen.op ⟨ψ, hψ_mem⟩ + I • ψ = φ := Resolvent.resolvent_solution_eq_plus gen hsa φ
  use ψ, hψ_mem
  have hφ_ne : φ ≠ 0 := by
    intro h; rw [h, norm_zero] at hφ_norm; exact one_ne_zero hφ_norm.symm
  have hψ_ne : ψ ≠ 0 := by
    intro h
    have hψ_eq_zero : (⟨ψ, hψ_mem⟩ : gen.domain) = 0 := by ext; exact h
    have : φ = 0 := by
      calc φ = gen.op ⟨ψ, hψ_mem⟩ + I • ψ := hφ_eq.symm
        _ = gen.op 0 + I • 0 := by rw [hψ_eq_zero, h]
        _ = 0 := by simp
    exact hφ_ne this
  constructor
  · exact norm_ne_zero_iff.mpr hψ_ne
  have h_key := cayley_shift_identity gen hsa μ hμ_ne ψ hψ_mem
  simp only at h_key
  rw [← hφ_eq.symm] at h_key
  have h_norm_eq : ‖gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ‖ =
      ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ / ‖(1 : ℂ) - w‖ := by
    have : (U - w • ContinuousLinearMap.id ℂ H) φ =
           ((1 : ℂ) - w) • (gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ) := h_key
    rw [this, norm_smul]
    field_simp [ne_of_gt h_one_sub_w_norm_pos]
  have h_norm_identity : ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖ψ‖^2 = 1 := by
    have h := self_adjoint_norm_sq_add gen hsa ψ hψ_mem
    rw [hφ_eq, hφ_norm] at h
    linarith [h, sq_nonneg ‖gen.op ⟨ψ, hψ_mem⟩‖]
  set δ := ‖gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ‖ with hδ_def
  have hδ_bound : δ < C' / (2 * denom) := by
    calc δ = ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ / ‖(1 : ℂ) - w‖ := h_norm_eq
      _ < (C' * ‖(1 : ℂ) - w‖ / (2 * denom)) / ‖(1 : ℂ) - w‖ := by
          apply div_lt_div_of_pos_right hφ_bound h_one_sub_w_norm_pos
      _ = C' / (2 * denom) := by field_simp
  have hδ_nonneg : δ ≥ 0 := norm_nonneg _
  have hδ_small : δ < 1 / (4 * denom) := by
    calc δ < C' / (2 * denom) := hδ_bound
      _ ≤ (1/2) / (2 * denom) := by apply div_le_div_of_nonneg_right hC'_le_half (by positivity)
      _ = 1 / (4 * denom) := by ring
  have hψ_norm_lower : ‖ψ‖ ≥ 1 / (2 * denom) := by
    have h_Aψ_upper : ‖gen.op ⟨ψ, hψ_mem⟩‖ ≤ |μ| * ‖ψ‖ + δ := by
      have h1 : ‖(↑μ : ℂ) • ψ‖ = |μ| * ‖ψ‖ := by
        rw [norm_smul]
        simp only [norm_real, Real.norm_eq_abs]
      calc ‖gen.op ⟨ψ, hψ_mem⟩‖
        = ‖gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ + (↑μ : ℂ) • ψ‖ := by rw [sub_add_cancel]
        _ ≤ ‖gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ‖ + ‖(↑μ : ℂ) • ψ‖ := norm_add_le _ _
        _ = δ + |μ| * ‖ψ‖ := by rw [← hδ_def, h1]
        _ = |μ| * ‖ψ‖ + δ := by ring
    have h_quad : 1 - ‖ψ‖^2 ≤ (|μ| * ‖ψ‖ + δ)^2 := by
      have h1 : ‖gen.op ⟨ψ, hψ_mem⟩‖^2 = 1 - ‖ψ‖^2 := by linarith [h_norm_identity]
      calc 1 - ‖ψ‖^2 = ‖gen.op ⟨ψ, hψ_mem⟩‖^2 := h1.symm
        _ ≤ (|μ| * ‖ψ‖ + δ)^2 := by
            apply sq_le_sq'
            · linarith [norm_nonneg (gen.op ⟨ψ, hψ_mem⟩),
                        mul_nonneg (abs_nonneg μ) (norm_nonneg ψ), hδ_nonneg]
            · exact h_Aψ_upper
    set x := ‖ψ‖ with hx_def
    have hx_nonneg : x ≥ 0 := norm_nonneg ψ
    have h_expanded : (1 + μ^2) * x^2 + 2 * |μ| * δ * x + (δ^2 - 1) ≥ 0 := by
      have h1 : 1 - x^2 ≤ (|μ| * x + δ)^2 := h_quad
      have h2 : (|μ| * x + δ)^2 = μ^2 * x^2 + 2 * |μ| * δ * x + δ^2 := by
        rw [← sq_abs μ]; ring
      calc (1 + μ^2) * x^2 + 2 * |μ| * δ * x + (δ^2 - 1)
          = μ^2 * x^2 + 2 * |μ| * δ * x + δ^2 + x^2 - 1 := by ring
        _ = (|μ| * x + δ)^2 - (1 - x^2) := by rw [h2]; ring
        _ ≥ 0 := by linarith [h1]
    have h_denom_sq : denom^2 = 1 + μ^2 := by
      rw [hdenom]; exact Real.sq_sqrt (by linarith [sq_nonneg μ])
    have hδ_sq_small : δ^2 < 1 + μ^2 := by
      have h1 : δ < 1 / (4 * denom) := hδ_small
      have h2 : δ^2 < 1 / (16 * denom^2) := by
        have h_lb : -(1 / (4 * denom)) < δ := by linarith
        have h1 : δ^2 < (1 / (4 * denom))^2 := sq_lt_sq' h_lb hδ_small
        calc δ^2 < (1 / (4 * denom))^2 := h1
          _ = 1 / (16 * denom^2) := by ring
      calc δ^2 < 1 / (16 * denom^2) := h2
        _ = 1 / (16 * (1 + μ^2)) := by rw [h_denom_sq]
        _ < 1 + μ^2 := by
            have : 1 + μ^2 ≥ 1 := by linarith [sq_nonneg μ]
            have : 16 * (1 + μ^2) ≥ 16 := by linarith
            have : 1 / (16 * (1 + μ^2)) ≤ 1/16 := by simp only [one_div, mul_inv_rev, inv_pos,
              Nat.ofNat_pos, mul_le_iff_le_one_left] ; (expose_names; exact inv_le_one_of_one_le₀ this_1)
            linarith
    by_contra h_neg
    push_neg at h_neg
    have h_contra : (1 + μ^2) * x^2 + 2 * |μ| * δ * x + (δ^2 - 1) < 0 := by
      have hx_upper : x < 1 / (2 * denom) := h_neg
      have hδ_upper : δ < 1 / (4 * denom) := hδ_small
      have h_term1 : (1 + μ^2) * x^2 < 1/4 := by
        have h1 : x^2 < 1 / (4 * denom^2) := by
          have h_lb : -(1 / (2 * denom)) < x := by linarith
          have h1' : x^2 < (1 / (2 * denom))^2 := sq_lt_sq' h_lb hx_upper
          calc x^2 < (1 / (2 * denom))^2 := h1'
            _ = 1 / (4 * denom^2) := by ring
        calc (1 + μ^2) * x^2 < (1 + μ^2) * (1 / (4 * denom^2)) := by
              apply mul_lt_mul_of_pos_left h1 (by linarith [sq_nonneg μ])
          _ = (1 + μ^2) / (4 * (1 + μ^2)) := by rw [h_denom_sq]; ring
          _ = 1/4 := by field_simp
      have h_term2' : 2 * |μ| * δ * x < 1/4 := by
        by_cases hμ_zero : μ = 0
        · simp [hμ_zero]
        · have hμ_pos : |μ| > 0 := abs_pos.mpr hμ_zero
          have h_mu_bound : |μ| ≤ denom := by
            rw [hdenom]
            calc |μ| = Real.sqrt (μ^2) := (Real.sqrt_sq_eq_abs μ).symm
              _ ≤ Real.sqrt (1 + μ^2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg μ])
          have h1 : δ * x < 1/(4*denom) * (1/(2*denom)) := by
            apply mul_lt_mul hδ_upper (le_of_lt hx_upper) (by positivity) (by positivity)
          have h2 : 1/(4*denom) * (1/(2*denom)) = 1/(8*denom^2) := by field_simp; ring
          calc 2 * |μ| * δ * x = 2 * |μ| * (δ * x) := by ring
            _ < 2 * |μ| * (1/(8*denom^2)) := by
                rw [h2] at h1
                exact mul_lt_mul_of_pos_left h1 (by linarith : 2 * |μ| > 0)
            _ = |μ| / (4 * denom^2) := by ring
            _ = |μ| / (4 * (1 + μ^2)) := by rw [h_denom_sq]
            _ ≤ denom / (4 * (1 + μ^2)) := by
                apply div_le_div_of_nonneg_right h_mu_bound (by positivity)
            _ = Real.sqrt (1 + μ^2) / (4 * (1 + μ^2)) := by rw [hdenom]
            _ = 1 / (4 * Real.sqrt (1 + μ^2)) := by
                have h_sqrt_sq : Real.sqrt (1 + μ^2) * Real.sqrt (1 + μ^2) = 1 + μ^2 :=
                  Real.mul_self_sqrt (by linarith [sq_nonneg μ])
                rw [div_eq_div_iff (by positivity) (by positivity)]
                simp only [one_mul]
                calc Real.sqrt (1 + μ^2) * (4 * Real.sqrt (1 + μ^2))
                    = 4 * (Real.sqrt (1 + μ^2) * Real.sqrt (1 + μ^2)) := by ring
                  _ = 4 * (1 + μ^2) := by rw [h_sqrt_sq]
            _ ≤ 1/4 := by
                apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by norm_num)
                calc 4 * Real.sqrt (1 + μ^2) ≥ 4 * 1 := by
                      apply mul_le_mul_of_nonneg_left hdenom_ge_one (by norm_num)
                  _ = 4 := by ring
      have h_mu_bound : |μ| ≤ denom := by
        rw [hdenom]
        calc |μ| = Real.sqrt (μ^2) := (Real.sqrt_sq_eq_abs μ).symm
          _ ≤ Real.sqrt (1 + μ^2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg μ])
      have h_term3 : δ^2 - 1 < -1/2 := by
        have h1 : δ^2 < 1 / (16 * denom^2) := by
          have h_lb : -(1 / (4 * denom)) < δ := by linarith
          have h1 : δ^2 < (1 / (4 * denom))^2 := sq_lt_sq' h_lb hδ_small
          calc δ^2 < (1 / (4 * denom))^2 := h1
            _ = 1 / (16 * denom^2) := by ring
        have h2 : 1 / (16 * denom^2) ≤ 1/16 := by
          apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by norm_num)
          calc 16 * denom^2 ≥ 16 * 1 := by nlinarith [hdenom_ge_one]
            _ = 16 := by ring
        linarith
      linarith
    linarith [h_expanded, h_contra]
  calc ‖gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ‖
      = δ := rfl
    _ < C' / (2 * denom) := hδ_bound
    _ ≤ C / (2 * denom) := by apply div_le_div_of_nonneg_right hC'_le_C (by positivity)
    _ ≤ C * ‖ψ‖ := by
        calc C / (2 * denom) = C * (1 / (2 * denom)) := by ring
          _ ≤ C * ‖ψ‖ := mul_le_mul_of_nonneg_left hψ_norm_lower (le_of_lt hC)

/-- Approximate eigenvalues of `A` give approximate eigenvalues of `U`. -/
lemma cayley_approx_eigenvalue_forward {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (∀ C > 0, ∃ ψ, ∃ hψ : ψ ∈ gen.domain, ‖ψ‖ ≠ 0 ∧ ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ < C * ‖ψ‖) →
    (∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧
      ‖(cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ‖ < ε) := by
  intro h_approx ε hε
  set U := cayleyTransform gen hsa with hU_def
  set w := (↑μ - I) * (↑μ + I)⁻¹ with hw_def
  have h_one_sub_w_ne : (1 : ℂ) - w ≠ 0 := one_sub_mobius_ne_zero μ hμ_ne
  have h_one_sub_w_norm_pos : ‖(1 : ℂ) - w‖ > 0 := norm_pos_iff.mpr h_one_sub_w_ne
  obtain ⟨ψ, hψ_mem, hψ_norm_ne, h_Aμψ_bound⟩ := h_approx (ε / ‖(1 : ℂ) - w‖) (by positivity)
  have hψ_ne : ψ ≠ 0 := norm_ne_zero_iff.mp hψ_norm_ne
  have hψ_norm_pos : ‖ψ‖ > 0 := norm_pos_iff.mpr hψ_ne
  set φ' := gen.op ⟨ψ, hψ_mem⟩ + I • ψ with hφ'_def
  have hφ'_norm_pos : ‖φ'‖ > 0 := by
    have h_sq := self_adjoint_norm_sq_add gen hsa ψ hψ_mem
    have h_ge : ‖φ'‖^2 ≥ ‖ψ‖^2 := by
      calc ‖φ'‖^2 = ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖ψ‖^2 := h_sq
        _ ≥ 0 + ‖ψ‖^2 := by linarith [sq_nonneg ‖gen.op ⟨ψ, hψ_mem⟩‖]
        _ = ‖ψ‖^2 := by ring
    nlinarith [norm_nonneg φ', sq_nonneg ‖φ'‖, sq_nonneg ‖ψ‖]
  have hφ'_ne : φ' ≠ 0 := norm_pos_iff.mp hφ'_norm_pos
  have hφ'_norm_ge_ψ : ‖φ'‖ ≥ ‖ψ‖ := by
    have h_sq := self_adjoint_norm_sq_add gen hsa ψ hψ_mem
    have h_ge : ‖φ'‖^2 ≥ ‖ψ‖^2 := by
      calc ‖φ'‖^2 = ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖ψ‖^2 := h_sq
        _ ≥ ‖ψ‖^2 := by linarith [sq_nonneg ‖gen.op ⟨ψ, hψ_mem⟩‖]
    nlinarith [norm_nonneg φ', norm_nonneg ψ, sq_nonneg (‖φ'‖ - ‖ψ‖)]
  set φ := ‖φ'‖⁻¹ • φ' with hφ_def
  use φ
  constructor
  · rw [hφ_def, norm_smul, norm_inv, norm_norm]
    field_simp [ne_of_gt hφ'_norm_pos]
  have h_key := cayley_shift_identity gen hsa μ hμ_ne ψ hψ_mem
  simp only at h_key
  have h_Uwφ' : (U - w • ContinuousLinearMap.id ℂ H) φ' =
      ((1 : ℂ) - w) • (gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ) := h_key
  have h_norm_Uwφ' : ‖(U - w • ContinuousLinearMap.id ℂ H) φ'‖ =
      ‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ‖ := by
    rw [h_Uwφ', norm_smul]
  calc ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖
      = ‖(U - w • ContinuousLinearMap.id ℂ H) (‖φ'‖⁻¹ • φ')‖ := by rw [hφ_def]
    _ = ‖‖φ'‖⁻¹ • (U - w • ContinuousLinearMap.id ℂ H) φ'‖ := by
        simp only [ContinuousLinearMap.map_smul_of_tower,
          ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_smul',
          ContinuousLinearMap.coe_id', Pi.sub_apply, Pi.smul_apply, id_eq]
    _ = ‖φ'‖⁻¹ * ‖(U - w • ContinuousLinearMap.id ℂ H) φ'‖ := by
        rw [norm_smul, norm_inv, norm_norm]
    _ = ‖φ'‖⁻¹ * (‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ‖) := by rw [h_norm_Uwφ']
    _ < ‖φ'‖⁻¹ * (‖(1 : ℂ) - w‖ * (ε / ‖(1 : ℂ) - w‖ * ‖ψ‖)) := by
        apply mul_lt_mul_of_pos_left _ (inv_pos.mpr hφ'_norm_pos)
        apply mul_lt_mul_of_pos_left h_Aμψ_bound h_one_sub_w_norm_pos
    _ = ‖φ'‖⁻¹ * (ε * ‖ψ‖) := by field_simp
    _ ≤ ‖φ'‖⁻¹ * (ε * ‖φ'‖) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
        apply mul_le_mul_of_nonneg_left hφ'_norm_ge_ψ (le_of_lt hε)
    _ = ε := by field_simp [ne_of_gt hφ'_norm_pos]

/-- Full spectral correspondence: bounded below for `A - μ` iff `U - w` is invertible. -/
theorem cayley_spectrum_correspondence {U_grp : OneParameterUnitaryGroup (H := H)} [Nontrivial H]
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ) :
    (∃ C : ℝ, C > 0 ∧ ∀ ψ (hψ : ψ ∈ gen.domain), ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ ≥ C * ‖ψ‖) ↔
    IsUnit (cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) := by
  set U := cayleyTransform gen hsa with hU_def
  set w := (↑μ - I) * (↑μ + I)⁻¹ with hw_def
  have hμ_ne : (↑μ : ℂ) + I ≠ 0 := real_add_I_ne_zero μ
  constructor
  · intro ⟨C, hC_pos, hC_bound⟩
    by_contra h_not_unit
    have h_approx_U := unitary_not_isUnit_approx_eigenvalue
                         (cayleyTransform_unitary gen hsa) w h_not_unit
    have h_approx_A := cayley_approx_eigenvalue_backward gen hsa μ hμ_ne h_approx_U
    obtain ⟨ψ, hψ_mem, hψ_norm_ne, h_small⟩ := h_approx_A C hC_pos
    have hψ_ne : ψ ≠ 0 := norm_ne_zero_iff.mp hψ_norm_ne
    have hψ_norm_pos : ‖ψ‖ > 0 := norm_pos_iff.mpr hψ_ne
    have h_ge := hC_bound ψ hψ_mem
    linarith
  · intro hU
    obtain ⟨c, hc_pos, hc_bound⟩ := isUnit_bounded_below hU
    exact cayley_shift_bounded_below_backward gen hsa μ hμ_ne c hc_pos hc_bound

end QuantumMechanics.Cayley
