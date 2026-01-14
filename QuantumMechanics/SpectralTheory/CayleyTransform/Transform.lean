/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform.Unitary

/-!
# The Cayley Transform

This file defines the Cayley transform of a self-adjoint generator and proves its
fundamental properties: it is an isometry, surjective, and unitary.

## Main definitions

* `cayleyTransform`: The Cayley transform `(A - iI)(A + iI)⁻¹` of a self-adjoint generator

## Main statements

* `cayleyTransform_isometry`: The Cayley transform preserves norms
* `cayleyTransform_surjective`: The Cayley transform is surjective
* `cayleyTransform_unitary`: The Cayley transform is unitary
* `cayleyTransform_norm_one`: The operator norm of the Cayley transform is 1
-/

namespace QuantumMechanics.Cayley

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Cayley transform of a self-adjoint generator, defined as `I - 2i(A + iI)⁻¹`. -/
noncomputable def cayleyTransform {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - (2 * I) • Resolvent.resolvent_at_neg_i gen hsa

/-- The Cayley transform maps `(A + iI)ψ` to `(A - iI)ψ`. -/
lemma cayleyTransform_apply {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    let ψ := Resolvent.resolvent_at_neg_i gen hsa φ
    let hψ := Resolvent.resolvent_solution_mem_plus gen hsa φ
    cayleyTransform gen hsa φ = gen.op ⟨ψ, hψ⟩ - I • ψ := by
  simp only [cayleyTransform]
  let ψ := Resolvent.resolvent_at_neg_i gen hsa φ
  have hψ_mem := Resolvent.resolvent_solution_mem_plus gen hsa φ
  have hψ_eq : gen.op ⟨ψ, hψ_mem⟩ + I • ψ = φ := Resolvent.resolvent_solution_eq_plus gen hsa φ
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
             ContinuousLinearMap.smul_apply]
  calc φ - (2 * I) • ψ
      = (gen.op ⟨ψ, hψ_mem⟩ + I • ψ) - (2 * I) • ψ := by rw [← hψ_eq]
    _ = gen.op ⟨ψ, hψ_mem⟩ + I • ψ - (2 * I) • ψ := rfl
    _ = gen.op ⟨ψ, hψ_mem⟩ - I • ψ := by
      rw [mul_smul, two_smul ℂ (I • ψ)]
      abel
    _ = gen.op ⟨ψ, hψ_mem⟩ - I • ψ := rfl

/-- The Cayley transform is an isometry. -/
theorem cayleyTransform_isometry {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    ∀ φ : H, ‖cayleyTransform gen hsa φ‖ = ‖φ‖ := by
  intro φ
  let ψ := Resolvent.resolvent_at_neg_i gen hsa φ
  have hψ_mem : ψ ∈ gen.domain := Resolvent.resolvent_solution_mem_plus gen hsa φ
  have hψ_eq : gen.op ⟨ψ, hψ_mem⟩ + I • ψ = φ := Resolvent.resolvent_solution_eq_plus gen hsa φ
  have h_Uφ : cayleyTransform gen hsa φ = gen.op ⟨ψ, hψ_mem⟩ - I • ψ :=
    cayleyTransform_apply gen hsa φ
  have h_minus : ‖gen.op ⟨ψ, hψ_mem⟩ - I • ψ‖^2 =
                 ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖ψ‖^2 := by
    have norm_I_smul : ‖I • ψ‖ = ‖ψ‖ := by rw [norm_smul]; simp
    have cross_zero : (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re = 0 := by
      rw [inner_smul_right]
      have h_real : (⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ).im = 0 := by
        have h_sym := gen.symmetric ⟨ψ, hψ_mem⟩ ⟨ψ, hψ_mem⟩
        have h_conj : ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ =
                      (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ := by
          calc ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ
              = ⟪ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ := h_sym
            _ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ := by rw [inner_conj_symm]
        have := Complex.ext_iff.mp h_conj
        simp only [Complex.conj_im] at this
        linarith [this.2]
      have h1 : I * ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ =
                I * (⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ).re := by
        conv_lhs => rw [← Complex.re_add_im ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ, h_real]
        simp
      rw [h1, mul_comm]; simp
    have h_expand : ‖gen.op ⟨ψ, hψ_mem⟩ - I • ψ‖^2 =
        ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖I • ψ‖^2 -
        2 * (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by
      have h1 : ‖gen.op ⟨ψ, hψ_mem⟩ - I • ψ‖ ^ 2 =
                (⟪gen.op ⟨ψ, hψ_mem⟩ - I • ψ, gen.op ⟨ψ, hψ_mem⟩ - I • ψ⟫_ℂ).re := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨ψ, hψ_mem⟩ - I • ψ)
        rw [this]; norm_cast
      have h2 : ‖gen.op ⟨ψ, hψ_mem⟩‖ ^ 2 = (⟪gen.op ⟨ψ, hψ_mem⟩, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨ψ, hψ_mem⟩)
        rw [this]; norm_cast
      have h3 : ‖I • ψ‖ ^ 2 = (⟪I • ψ, I • ψ⟫_ℂ).re := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (I • ψ)
        rw [this]; norm_cast
      have h_cross : (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re + (⟪I • ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re =
                    2 * (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by
        have h_eq : (⟪I • ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re = (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by
          calc (⟪I • ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re
              = ((starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by rw [inner_conj_symm]
            _ = (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by simp only [Complex.conj_re]
        rw [h_eq]; ring
      rw [h1, inner_sub_left, inner_sub_right, inner_sub_right]
      simp only [Complex.sub_re]
      rw [h2, h3, ← h_cross]
      ring
    rw [h_expand, norm_I_smul, cross_zero]
    ring
  have h_plus : ‖gen.op ⟨ψ, hψ_mem⟩ + I • ψ‖^2 =
              ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖ψ‖^2 := by
    have norm_I_smul : ‖I • ψ‖ = ‖ψ‖ := by rw [norm_smul]; simp
    have cross_zero : (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re = 0 := by
      rw [inner_smul_right]
      have h_real : (⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ).im = 0 := by
        have h_sym := gen.symmetric ⟨ψ, hψ_mem⟩ ⟨ψ, hψ_mem⟩
        have h_conj : ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ =
                      (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ := by
          calc ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ
              = ⟪ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ := h_sym
            _ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ := by rw [inner_conj_symm]
        have := Complex.ext_iff.mp h_conj
        simp only [Complex.conj_im] at this
        linarith [this.2]
      have h1 : I * ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ =
                I * (⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ).re := by
        conv_lhs => rw [← Complex.re_add_im ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ, h_real]
        simp
      rw [h1, mul_comm]; simp
    have h_expand : ‖gen.op ⟨ψ, hψ_mem⟩ + I • ψ‖^2 =
        ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖I • ψ‖^2 +
        2 * (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by
      have h1 : ‖gen.op ⟨ψ, hψ_mem⟩ + I • ψ‖ ^ 2 =
                (⟪gen.op ⟨ψ, hψ_mem⟩ + I • ψ, gen.op ⟨ψ, hψ_mem⟩ + I • ψ⟫_ℂ).re := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨ψ, hψ_mem⟩ + I • ψ)
        rw [this]; norm_cast
      have h2 : ‖gen.op ⟨ψ, hψ_mem⟩‖ ^ 2 = (⟪gen.op ⟨ψ, hψ_mem⟩, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨ψ, hψ_mem⟩)
        rw [this]; norm_cast
      have h3 : ‖I • ψ‖ ^ 2 = (⟪I • ψ, I • ψ⟫_ℂ).re := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (I • ψ)
        rw [this]; norm_cast
      have h_cross : (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re + (⟪I • ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re =
                    2 * (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by
        have h_eq : (⟪I • ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re = (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by
          calc (⟪I • ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re
              = ((starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by rw [inner_conj_symm]
            _ = (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by simp only [Complex.conj_re]
        rw [h_eq]; ring
      rw [h1, inner_add_left, inner_add_right, inner_add_right]
      simp only [Complex.add_re]
      rw [h2, h3, ← h_cross]
      ring
    rw [h_expand, norm_I_smul, cross_zero]
    ring
  have h_sq : ‖cayleyTransform gen hsa φ‖^2 = ‖φ‖^2 := by
    calc ‖cayleyTransform gen hsa φ‖^2
        = ‖gen.op ⟨ψ, hψ_mem⟩ - I • ψ‖^2 := by rw [h_Uφ]
      _ = ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖ψ‖^2 := h_minus
      _ = ‖gen.op ⟨ψ, hψ_mem⟩ + I • ψ‖^2 := h_plus.symm
      _ = ‖φ‖^2 := by rw [hψ_eq]
  rw [← Real.sqrt_sq (norm_nonneg (cayleyTransform gen hsa φ)),
      ← Real.sqrt_sq (norm_nonneg φ), h_sq]

/-- The Cayley transform is surjective. -/
theorem cayleyTransform_surjective {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    Function.Surjective (cayleyTransform gen hsa) := by
  intro χ
  obtain ⟨ψ, hψ_dom, hψ_eq⟩ := hsa.2 χ
  let φ := gen.op ⟨ψ, hψ_dom⟩ + I • ψ
  use φ
  have h_Rφ : Resolvent.resolvent_at_neg_i gen hsa φ = ψ := by
    have h_sol : gen.op ⟨ψ, hψ_dom⟩ + I • ψ = φ := rfl
    let ψ' := Resolvent.resolvent_at_neg_i gen hsa φ
    have hψ'_mem := Resolvent.resolvent_solution_mem_plus gen hsa φ
    have hψ'_eq := Resolvent.resolvent_solution_eq_plus gen hsa φ
    exact Resolvent.resolvent_at_neg_i_unique gen hsa φ ψ' ψ hψ'_mem hψ_dom hψ'_eq h_sol
  have h_Uφ := cayleyTransform_apply gen hsa φ
  simp only at h_Uφ
  calc cayleyTransform gen hsa φ
      = gen.op ⟨Resolvent.resolvent_at_neg_i gen hsa φ,
               Resolvent.resolvent_solution_mem_plus gen hsa φ⟩ -
        I • Resolvent.resolvent_at_neg_i gen hsa φ := h_Uφ
    _ = gen.op ⟨ψ, hψ_dom⟩ - I • ψ := by
        subst hψ_eq
        simp_all only [map_add, map_smul, φ]
    _ = χ := hψ_eq

/-- The Cayley transform of a self-adjoint operator is unitary. -/
theorem cayleyTransform_unitary {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    Unitary (cayleyTransform gen hsa) := by
  have h_isometry := cayleyTransform_isometry gen hsa
  have h_star_self : (cayleyTransform gen hsa).adjoint * cayleyTransform gen hsa = 1 := by
    ext φ
    apply ext_inner_left ℂ
    intro ψ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [ContinuousLinearMap.adjoint_inner_right]
    have h_polar : ⟪cayleyTransform gen hsa φ, cayleyTransform gen hsa ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := by
      set U := cayleyTransform gen hsa with hU
      have h_inner_self : ∀ x, ⟪U x, U x⟫_ℂ = ⟪x, x⟫_ℂ := by
        intro x
        have h1 : (⟪U x, U x⟫_ℂ).re = ‖U x‖^2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        have h2 : (⟪x, x⟫_ℂ).re = ‖x‖^2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        have h3 : (⟪U x, U x⟫_ℂ).im = 0 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
        have h4 : (⟪x, x⟫_ℂ).im = 0 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
        apply Complex.ext <;> simp only [h1, h2, h3, h4, h_isometry]
      have h_re_part : ⟪U φ, U ψ⟫_ℂ + ⟪U ψ, U φ⟫_ℂ = ⟪φ, ψ⟫_ℂ + ⟪ψ, φ⟫_ℂ := by
        have h_sum := h_inner_self (φ + ψ)
        rw [U.map_add] at h_sum
        have lhs : ⟪U φ + U ψ, U φ + U ψ⟫_ℂ =
                  ⟪U φ, U φ⟫_ℂ + ⟪U φ, U ψ⟫_ℂ + ⟪U ψ, U φ⟫_ℂ + ⟪U ψ, U ψ⟫_ℂ := by
          rw [inner_add_left, inner_add_right, inner_add_right]; ring
        have rhs : ⟪φ + ψ, φ + ψ⟫_ℂ =
                  ⟪φ, φ⟫_ℂ + ⟪φ, ψ⟫_ℂ + ⟪ψ, φ⟫_ℂ + ⟪ψ, ψ⟫_ℂ := by
          rw [inner_add_left, inner_add_right, inner_add_right]; ring
        have hφ := h_inner_self φ
        have hψ := h_inner_self ψ
        rw [lhs, rhs, hφ, hψ] at h_sum
        calc ⟪U φ, U ψ⟫_ℂ + ⟪U ψ, U φ⟫_ℂ
            = (⟪φ, φ⟫_ℂ + ⟪U φ, U ψ⟫_ℂ + ⟪U ψ, U φ⟫_ℂ + ⟪ψ, ψ⟫_ℂ) - ⟪φ, φ⟫_ℂ - ⟪ψ, ψ⟫_ℂ := by ring
          _ = (⟪φ, φ⟫_ℂ + ⟪φ, ψ⟫_ℂ + ⟪ψ, φ⟫_ℂ + ⟪ψ, ψ⟫_ℂ) - ⟪φ, φ⟫_ℂ - ⟪ψ, ψ⟫_ℂ := by rw [h_sum]
          _ = ⟪φ, ψ⟫_ℂ + ⟪ψ, φ⟫_ℂ := by ring
      have h_im_part : ⟪U φ, I • U ψ⟫_ℂ + ⟪I • U ψ, U φ⟫_ℂ = ⟪φ, I • ψ⟫_ℂ + ⟪I • ψ, φ⟫_ℂ := by
        have h_sum_i := h_inner_self (φ + I • ψ)
        rw [U.map_add, U.map_smul] at h_sum_i
        have lhs : ⟪U φ + I • U ψ, U φ + I • U ψ⟫_ℂ =
                  ⟪U φ, U φ⟫_ℂ + ⟪U φ, I • U ψ⟫_ℂ + ⟪I • U ψ, U φ⟫_ℂ + ⟪I • U ψ, I • U ψ⟫_ℂ := by
          rw [inner_add_left, inner_add_right, inner_add_right]; ring
        have rhs : ⟪φ + I • ψ, φ + I • ψ⟫_ℂ =
                  ⟪φ, φ⟫_ℂ + ⟪φ, I • ψ⟫_ℂ + ⟪I • ψ, φ⟫_ℂ + ⟪I • ψ, I • ψ⟫_ℂ := by
          rw [inner_add_left, inner_add_right, inner_add_right]; ring
        have hIψ : ⟪I • U ψ, I • U ψ⟫_ℂ = ⟪I • ψ, I • ψ⟫_ℂ := by
          rw [inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
          simp only [Complex.conj_I]
          have hψ' := h_inner_self ψ
          ring_nf
          rw [hψ']
        have hφ := h_inner_self φ
        rw [lhs, rhs, hφ, hIψ] at h_sum_i
        calc ⟪U φ, I • U ψ⟫_ℂ + ⟪I • U ψ, U φ⟫_ℂ
            = (⟪φ, φ⟫_ℂ + ⟪U φ, I • U ψ⟫_ℂ + ⟪I • U ψ, U φ⟫_ℂ + ⟪I • ψ, I • ψ⟫_ℂ) -
              ⟪φ, φ⟫_ℂ - ⟪I • ψ, I • ψ⟫_ℂ := by ring
          _ = (⟪φ, φ⟫_ℂ + ⟪φ, I • ψ⟫_ℂ + ⟪I • ψ, φ⟫_ℂ + ⟪I • ψ, I • ψ⟫_ℂ) -
              ⟪φ, φ⟫_ℂ - ⟪I • ψ, I • ψ⟫_ℂ := by rw [h_sum_i]
          _ = ⟪φ, I • ψ⟫_ℂ + ⟪I • ψ, φ⟫_ℂ := by ring
      apply Complex.ext
      · -- Real parts equal
        have h1 : ⟪U ψ, U φ⟫_ℂ = (starRingEnd ℂ) ⟪U φ, U ψ⟫_ℂ := (inner_conj_symm _ _).symm
        have h2 : ⟪ψ, φ⟫_ℂ = (starRingEnd ℂ) ⟪φ, ψ⟫_ℂ := (inner_conj_symm _ _).symm
        have h3 : (⟪U φ, U ψ⟫_ℂ + (starRingEnd ℂ) ⟪U φ, U ψ⟫_ℂ).re = 2 * (⟪U φ, U ψ⟫_ℂ).re := by
          simp only [Complex.add_re, Complex.conj_re]; ring
        have h4 : (⟪φ, ψ⟫_ℂ + (starRingEnd ℂ) ⟪φ, ψ⟫_ℂ).re = 2 * (⟪φ, ψ⟫_ℂ).re := by
          simp only [Complex.add_re, Complex.conj_re]; ring
        rw [h1, h2] at h_re_part
        have := congrArg Complex.re h_re_part
        rw [h3, h4] at this
        linarith
      · -- Imaginary parts equal
        rw [inner_smul_right, inner_smul_left, inner_smul_right, inner_smul_left] at h_im_part
        simp only [Complex.conj_I] at h_im_part
        have h1 : ⟪U ψ, U φ⟫_ℂ = (starRingEnd ℂ) ⟪U φ, U ψ⟫_ℂ := (inner_conj_symm _ _).symm
        have h2 : ⟪ψ, φ⟫_ℂ = (starRingEnd ℂ) ⟪φ, ψ⟫_ℂ := (inner_conj_symm _ _).symm
        have h3 : (I * ⟪U φ, U ψ⟫_ℂ + (-I) * (starRingEnd ℂ) ⟪U φ, U ψ⟫_ℂ).re =
                  -2 * (⟪U φ, U ψ⟫_ℂ).im := by
          simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
                    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
          ring
        have h4 : (I * ⟪φ, ψ⟫_ℂ + (-I) * (starRingEnd ℂ) ⟪φ, ψ⟫_ℂ).re =
                  -2 * (⟪φ, ψ⟫_ℂ).im := by
          simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
                    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
          ring
        rw [h1, h2] at h_im_part
        have := congrArg Complex.re h_im_part
        rw [h3, h4] at this
        linarith
    have h_polar' : ⟪cayleyTransform gen hsa ψ, cayleyTransform gen hsa φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
      have := congrArg (starRingEnd ℂ) h_polar
      simp only [inner_conj_symm] at this
      exact this
    exact h_polar'
  have h_surj := cayleyTransform_surjective gen hsa
  have h_self_star : cayleyTransform gen hsa * (cayleyTransform gen hsa).adjoint = 1 := by
    set U := cayleyTransform gen hsa with hU_def
    ext φ
    obtain ⟨ψ, hψ⟩ := cayleyTransform_surjective gen hsa φ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [← hψ]
    have : U.adjoint (U ψ) = ψ := by
      have h := congrFun (congrArg DFunLike.coe h_star_self) ψ
      simp at h
      exact h
    rw [this, hψ]
  exact ⟨h_star_self, h_self_star⟩

/-- `U U* = I` for the Cayley transform. -/
lemma cayleyTransform_comp_adjoint {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (cayleyTransform gen hsa).comp (cayleyTransform gen hsa).adjoint =
    ContinuousLinearMap.id ℂ H := by
  have hU := cayleyTransform_unitary gen hsa
  exact hU.2

/-- `U* U = I` for the Cayley transform. -/
lemma cayleyTransform_adjoint_comp {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (cayleyTransform gen hsa).adjoint.comp (cayleyTransform gen hsa) =
    ContinuousLinearMap.id ℂ H := by
  have hU := cayleyTransform_unitary gen hsa
  exact hU.1

/-- The Cayley transform is invertible. -/
lemma cayleyTransform_isUnit {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    IsUnit (cayleyTransform gen hsa) := by
  refine ⟨⟨cayleyTransform gen hsa, (cayleyTransform gen hsa).adjoint, ?_, ?_⟩, rfl⟩
  · exact cayleyTransform_comp_adjoint gen hsa
  · exact cayleyTransform_adjoint_comp gen hsa

/-- Variant of `cayleyTransform_adjoint_comp` with explicit calculation. -/
lemma cayleyTransform_adjoint_comp' {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (cayleyTransform gen hsa).adjoint.comp (cayleyTransform gen hsa) =
    ContinuousLinearMap.id ℂ H := by
  have hU := cayleyTransform_unitary gen hsa
  ext ψ
  apply ext_inner_right ℂ
  intro φ
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact ContinuousLinearMap.inner_map_map_of_mem_unitary hU ψ φ

/-- The operator norm of the Cayley transform is 1. -/
theorem cayleyTransform_norm_one {U_grp : OneParameterUnitaryGroup (H := H)} [Nontrivial H]
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    ‖cayleyTransform gen hsa‖ = 1 := by
  set U := cayleyTransform gen hsa
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro ψ
    have hU := cayleyTransform_unitary gen hsa
    have h_inner := hU.1
    have h_norm : ‖U ψ‖ = ‖ψ‖ := by
      have : U.adjoint.comp U = 1 := h_inner
      have h_eq : ⟪U ψ, U ψ⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
        calc ⟪U ψ, U ψ⟫_ℂ
            = ⟪U.adjoint (U ψ), ψ⟫_ℂ := by rw [ContinuousLinearMap.adjoint_inner_left]
          _ = ⟪(U.adjoint.comp U) ψ, ψ⟫_ℂ := rfl
          _ = ⟪ψ, ψ⟫_ℂ := by rw [this]; simp
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h_eq
      have h_sq : ‖U ψ‖^2 = ‖ψ‖^2 := by exact_mod_cast h_eq
      nlinarith [norm_nonneg (U ψ), norm_nonneg ψ, sq_nonneg (‖U ψ‖ - ‖ψ‖)]
    simp only [one_mul, h_norm, le_refl]
  · obtain ⟨ψ, hψ⟩ := exists_ne (0 : H)
    have hU := cayleyTransform_unitary gen hsa
    have h_inner := hU.1
    have h_norm : ‖U ψ‖ = ‖ψ‖ := by
      have : U.adjoint.comp U = 1 := h_inner
      have h_eq : ⟪U ψ, U ψ⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
        calc ⟪U ψ, U ψ⟫_ℂ
            = ⟪U.adjoint (U ψ), ψ⟫_ℂ := by rw [ContinuousLinearMap.adjoint_inner_left]
          _ = ⟪(U.adjoint.comp U) ψ, ψ⟫_ℂ := rfl
          _ = ⟪ψ, ψ⟫_ℂ := by rw [this]; simp
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h_eq
      have h_sq : ‖U ψ‖^2 = ‖ψ‖^2 := by exact_mod_cast h_eq
      nlinarith [norm_nonneg (U ψ), norm_nonneg ψ, sq_nonneg (‖U ψ‖ - ‖ψ‖)]
    calc 1 = ‖U ψ‖ / ‖ψ‖ := by rw [h_norm]; field_simp
      _ ≤ ‖U‖ := by exact ContinuousLinearMap.ratio_le_opNorm U ψ


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- For symmetric operators, `‖Aψ + iψ‖² = ‖Aψ‖² + ‖ψ‖²`. -/
lemma self_adjoint_norm_sq_add {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (_ : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ‖gen.op ⟨ψ, hψ⟩ + I • ψ‖^2 = ‖gen.op ⟨ψ, hψ⟩‖^2 + ‖ψ‖^2 := by
  have norm_I_smul : ‖I • ψ‖ = ‖ψ‖ := by rw [norm_smul]; simp
  have cross_zero : (⟪gen.op ⟨ψ, hψ⟩, I • ψ⟫_ℂ).re = 0 := by
    rw [inner_smul_right]
    have h_real : (⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ).im = 0 := by
      have h_sym := gen.symmetric ⟨ψ, hψ⟩ ⟨ψ, hψ⟩
      have h_conj : ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ := by
        calc ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ
            = ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ := h_sym
          _ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ := by rw [inner_conj_symm]
      have := Complex.ext_iff.mp h_conj
      simp only [Complex.conj_im] at this
      linarith [this.2]
    have h1 : I * ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ = I * (⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ).re := by
      conv_lhs => rw [← Complex.re_add_im ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ, h_real]
      simp
    rw [h1, mul_comm]; simp
  have h_expand : ‖gen.op ⟨ψ, hψ⟩ + I • ψ‖^2 =
      ‖gen.op ⟨ψ, hψ⟩‖^2 + ‖I • ψ‖^2 + 2 * (⟪gen.op ⟨ψ, hψ⟩, I • ψ⟫_ℂ).re := by
    have h1 : ‖gen.op ⟨ψ, hψ⟩ + I • ψ‖^2 =
              (⟪gen.op ⟨ψ, hψ⟩ + I • ψ, gen.op ⟨ψ, hψ⟩ + I • ψ⟫_ℂ).re := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
    have h2 : ‖gen.op ⟨ψ, hψ⟩‖^2 = (⟪gen.op ⟨ψ, hψ⟩, gen.op ⟨ψ, hψ⟩⟫_ℂ).re := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
    have h3 : ‖I • ψ‖^2 = (⟪I • ψ, I • ψ⟫_ℂ).re := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
    have h_cross : (⟪gen.op ⟨ψ, hψ⟩, I • ψ⟫_ℂ).re + (⟪I • ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ).re =
                   2 * (⟪gen.op ⟨ψ, hψ⟩, I • ψ⟫_ℂ).re := by
      have : (⟪I • ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ).re = (⟪gen.op ⟨ψ, hψ⟩, I • ψ⟫_ℂ).re := by
        have h : ⟪I • ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ⟩, I • ψ⟫_ℂ := by
          exact Eq.symm (conj_inner_symm (I • ψ) (gen.op ⟨ψ, hψ⟩))
        simp only [h, Complex.conj_re]
      linarith
    rw [h1, inner_add_left, inner_add_right, inner_add_right]
    simp only [Complex.add_re, h2, h3, ← h_cross]
    ring
  rw [h_expand, norm_I_smul, cross_zero]
  ring


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- The Cayley transform maps `(A + iI)ψ` to `(A - iI)ψ` for domain elements. -/
lemma cayleyTransform_apply_resolvent {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    cayleyTransform gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = gen.op ⟨ψ, hψ⟩ - I • ψ := by
  simp only [cayleyTransform, ContinuousLinearMap.sub_apply,
             ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
  have h_res := Resolvent.resolvent_at_neg_i_left_inverse gen hsa ψ hψ
  rw [h_res]
  module

end QuantumMechanics.Cayley
