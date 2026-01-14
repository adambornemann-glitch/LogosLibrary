/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform.Transform
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform.Mobius

/-!
# Eigenvalue Correspondence for the Cayley Transform

This file proves the eigenvalue correspondence between a self-adjoint operator `A` and
its Cayley transform `U`: real eigenvalues `μ` of `A` correspond to eigenvalues
`(μ - i)/(μ + i)` of `U` on the unit circle.

## Main statements

* `cayley_neg_one_eigenvalue_iff`: `-1` is an eigenvalue of `U` iff `0` is an eigenvalue of `A`
* `cayley_eigenvalue_correspondence`: `μ ∈ ℝ` is an eigenvalue of `A` iff
  `(μ - i)/(μ + i)` is an eigenvalue of `U`
* `cayley_shift_identity`: Key identity relating `(U - w)φ` to `(A - μ)ψ`
-/

namespace QuantumMechanics.Cayley

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `-1` is an eigenvalue of `U` iff `0` is an eigenvalue of `A`. -/
theorem cayley_neg_one_eigenvalue_iff {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    (∃ φ : H, φ ≠ 0 ∧ cayleyTransform gen hsa φ = -φ) ↔
    (∃ ψ : gen.domain, (ψ : H) ≠ 0 ∧ gen.op ψ = 0) := by
  constructor
  · intro ⟨φ, hφ_ne, hUφ⟩
    let ψ := Resolvent.resolvent_at_neg_i gen hsa φ
    have hψ_mem := Resolvent.resolvent_solution_mem_plus gen hsa φ
    have hψ_eq := Resolvent.resolvent_solution_eq_plus gen hsa φ
    have h_Uφ := cayleyTransform_apply gen hsa φ
    have h1 : gen.op ⟨ψ, hψ_mem⟩ - I • ψ = -(gen.op ⟨ψ, hψ_mem⟩ + I • ψ) := by
      calc gen.op ⟨ψ, hψ_mem⟩ - I • ψ
          = cayleyTransform gen hsa φ := h_Uφ.symm
        _ = -φ := hUφ
        _ = -(gen.op ⟨ψ, hψ_mem⟩ + I • ψ) := by rw [← hψ_eq]; rfl
    have h_Aψ_zero : gen.op ⟨ψ, hψ_mem⟩ = 0 := by
      have h2 : gen.op ⟨ψ, hψ_mem⟩ - I • ψ + (gen.op ⟨ψ, hψ_mem⟩ + I • ψ) = 0 := by
        rw [h1]; abel
      have h3 : (2 : ℂ) • gen.op ⟨ψ, hψ_mem⟩ = 0 := by
        calc (2 : ℂ) • gen.op ⟨ψ, hψ_mem⟩
            = gen.op ⟨ψ, hψ_mem⟩ + gen.op ⟨ψ, hψ_mem⟩ := two_smul ℂ _
          _ = (gen.op ⟨ψ, hψ_mem⟩ - I • ψ) + (gen.op ⟨ψ, hψ_mem⟩ + I • ψ) := by abel
          _ = 0 := h2
      exact (smul_eq_zero.mp h3).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
    have hψ_ne : ψ ≠ 0 := by
      intro hψ_eq_zero
      have : φ = 0 := by
        calc φ = gen.op ⟨ψ, hψ_mem⟩ + I • ψ := hψ_eq.symm
          _ = 0 + I • ψ := by rw [h_Aψ_zero]
          _ = 0 + I • 0 := by rw [hψ_eq_zero]
          _ = 0 := by simp
      exact hφ_ne this
    exact ⟨⟨ψ, hψ_mem⟩, hψ_ne, h_Aψ_zero⟩
  · intro ⟨⟨ψ, hψ_mem⟩, hψ_ne, h_Aψ⟩
    let φ := I • ψ
    have hφ_eq : gen.op ⟨ψ, hψ_mem⟩ + I • ψ = φ := by simp [φ, h_Aψ]
    use φ
    constructor
    · intro hφ_zero
      have : ψ = 0 := by
        have h := hφ_zero
        simp only [φ] at h
        exact (smul_eq_zero.mp h).resolve_left I_ne_zero
      exact hψ_ne this
    · have h_Rφ : Resolvent.resolvent_at_neg_i gen hsa φ = ψ := by
        exact Resolvent.resolvent_at_neg_i_unique gen hsa φ
          (Resolvent.resolvent_at_neg_i gen hsa φ) ψ
          (Resolvent.resolvent_solution_mem_plus gen hsa φ) hψ_mem
          (Resolvent.resolvent_solution_eq_plus gen hsa φ) hφ_eq
      calc cayleyTransform gen hsa φ
          = gen.op ⟨Resolvent.resolvent_at_neg_i gen hsa φ,
                   Resolvent.resolvent_solution_mem_plus gen hsa φ⟩ -
            I • Resolvent.resolvent_at_neg_i gen hsa φ := cayleyTransform_apply gen hsa φ
        _ = gen.op ⟨ψ, hψ_mem⟩ - I • ψ := by simp_all only [ne_eq, zero_add, map_smul, zero_sub, φ]
        _ = 0 - I • ψ := by rw [h_Aψ]
        _ = -φ := by simp [φ]

/-- Key identity: `(U - w)φ = (1 - w)(Aψ - μψ)` where `φ = (A + iI)ψ`. -/
lemma cayley_shift_identity {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) (ψ : H) (hψ : ψ ∈ gen.domain) :
    let U := cayleyTransform gen hsa
    let w := (↑μ - I) * (↑μ + I)⁻¹
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    (U - w • ContinuousLinearMap.id ℂ H) φ = ((1 : ℂ) - w) • (gen.op ⟨ψ, hψ⟩ - ↑μ • ψ) := by
  intro U w φ
  have h_Uφ : U φ = gen.op ⟨ψ, hψ⟩ - I • ψ := cayleyTransform_apply_resolvent gen hsa ψ hψ
  have h_coeff := mobius_coeff_identity μ hμ_ne
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.id_apply, φ, h_Uφ]
  calc gen.op ⟨ψ, hψ⟩ - I • ψ - w • (gen.op ⟨ψ, hψ⟩ + I • ψ)
      = (1 - w) • gen.op ⟨ψ, hψ⟩ - (I * (1 + w)) • ψ := by rw [smul_add]; module
    _ = (1 - w) • gen.op ⟨ψ, hψ⟩ - ((1 - w) * ↑μ) • ψ := by rw [h_coeff]
    _ = (1 - w) • gen.op ⟨ψ, hψ⟩ - (1 - w) • (↑μ • ψ) := by rw [@mul_smul]; rfl
    _ = (1 - w) • (gen.op ⟨ψ, hψ⟩ - ↑μ • ψ) := by rw [smul_sub]
  simp only

/-- Real eigenvalues of `A` correspond to eigenvalues of `U` via the Möbius map. -/
theorem cayley_eigenvalue_correspondence {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ) :
    (∃ ψ : H, ∃ hψ : ψ ∈ gen.domain, ψ ≠ 0 ∧ gen.op ⟨ψ, hψ⟩ = μ • ψ) ↔
    (∃ φ : H, φ ≠ 0 ∧ cayleyTransform gen hsa φ = ((↑μ - I) * (↑μ + I)⁻¹) • φ) := by
  set U := cayleyTransform gen hsa
  set w := (↑μ - I) * (↑μ + I)⁻¹ with hw_def
  have hμ_ne : (↑μ : ℂ) + I ≠ 0 := by
    intro h
    have : ((↑μ : ℂ) + I).im = 0 := by rw [h]; simp
    simp at this
  constructor
  · rintro ⟨ψ, hψ, hψ_ne, h_eig⟩
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    have hφ_eq : φ = (↑μ + I) • ψ := by
      simp only [φ, h_eig, add_smul]
      rfl
    have hφ_ne : φ ≠ 0 := by
      rw [hφ_eq]
      intro h
      rw [smul_eq_zero] at h
      cases h with
      | inl h => exact hμ_ne h
      | inr h => exact hψ_ne h
    use φ, hφ_ne
    have h_Uφ : U φ = gen.op ⟨ψ, hψ⟩ - I • ψ := by
      simp only [U, cayleyTransform, ContinuousLinearMap.sub_apply,
                 ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
      have h_res : Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = ψ :=
        Resolvent.resolvent_at_neg_i_left_inverse gen hsa ψ hψ
      rw [h_res]
      module
    calc U φ = gen.op ⟨ψ, hψ⟩ - I • ψ := h_Uφ
      _ = (↑μ - I) • ψ := by rw [h_eig]; exact Eq.symm (sub_smul (↑μ) I ψ)
      _ = w • (↑μ + I) • ψ := by
        simp only [hw_def, smul_smul]
        congr 1
        exact Eq.symm (inv_mul_cancel_right₀ hμ_ne (↑μ - I))
      _ = w • φ := by rw [← hφ_eq]
  · rintro ⟨φ, hφ_ne, h_eig⟩
    set ψ := Resolvent.resolvent_at_neg_i gen hsa φ with hψ_def
    have hψ_mem : ψ ∈ gen.domain := Resolvent.resolvent_solution_mem_plus gen hsa φ
    have hφ_eq : gen.op ⟨ψ, hψ_mem⟩ + I • ψ = φ := Resolvent.resolvent_solution_eq_plus gen hsa φ
    use ψ, hψ_mem
    have hψ_ne : ψ ≠ 0 := by
      intro h
      have hφ_zero : φ = 0 := by
        have h0_mem : (0 : H) ∈ gen.domain := Submodule.zero_mem gen.domain
        have : gen.op ⟨0, h0_mem⟩ + I • (0 : H) = 0 := by
          rw [smul_zero, add_zero]
          exact map_zero gen.op
        rw [← hφ_eq]
        convert this using 2
        · simp_all only [ne_eq, smul_zero, add_zero, w, U, ψ]
        · exact congrArg (HSMul.hSMul I) h
      exact hφ_ne hφ_zero
    constructor
    · exact hψ_ne
    · have h_Uφ : U φ = gen.op ⟨ψ, hψ_mem⟩ - I • ψ := by
        rw [← hφ_eq]
        simp only [U, cayleyTransform, ContinuousLinearMap.sub_apply,
                   ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
        have h_res : Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ_mem⟩ + I • ψ) = ψ :=
          Resolvent.resolvent_at_neg_i_left_inverse gen hsa ψ hψ_mem
        rw [h_res]
        module
      have h_key : gen.op ⟨ψ, hψ_mem⟩ - I • ψ = w • (gen.op ⟨ψ, hψ_mem⟩ + I • ψ) := by
        rw [← h_Uφ, h_eig, hφ_eq]
      have hw_ne_one : w ≠ 1 := by
        simp only [hw_def]
        intro h_eq
        have : (↑μ - I) * (↑μ + I)⁻¹ = 1 := h_eq
        field_simp [hμ_ne] at this
        have h_im : (↑μ - I : ℂ).im = (↑μ + I : ℂ).im := by rw [this]
        simp at h_im
        exact absurd h_im (by norm_num : (-1 : ℝ) ≠ 1)
      have h_one_sub_ne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw_ne_one)
      have h_expand : gen.op ⟨ψ, hψ_mem⟩ - I • ψ = w • gen.op ⟨ψ, hψ_mem⟩ + w • I • ψ := by
        rw [h_key, smul_add]
      have h_collect : (1 - w) • gen.op ⟨ψ, hψ_mem⟩ = (I + w * I) • ψ := by
        calc (1 - w) • gen.op ⟨ψ, hψ_mem⟩
            = gen.op ⟨ψ, hψ_mem⟩ - w • gen.op ⟨ψ, hψ_mem⟩ := by rw [sub_smul, one_smul]
          _ = I • ψ + w • I • ψ := by
              have h1 : gen.op ⟨ψ, hψ_mem⟩ - w • gen.op ⟨ψ, hψ_mem⟩ =
                        (gen.op ⟨ψ, hψ_mem⟩ - I • ψ) - (w • gen.op ⟨ψ, hψ_mem⟩ - I • ψ) := by module
              rw [h1, h_expand]
              module
          _ = (I + w * I) • ψ := by rw [hw_def]; module
      calc gen.op ⟨ψ, hψ_mem⟩
          = (1 - w)⁻¹ • (1 - w) • gen.op ⟨ψ, hψ_mem⟩ := by
              rw [smul_smul]
              simp_all only [ne_eq, not_false_eq_true, inv_mul_cancel₀, one_smul, w, U, ψ]
        _ = (1 - w)⁻¹ • (I + w * I) • ψ := by rw [h_collect]
        _ = ((1 - w)⁻¹ * (I + w * I)) • ψ := by rw [smul_smul]
        _ = ↑μ • ψ := by
            congr 1
            simp only [hw_def]
            field_simp [hμ_ne, h_one_sub_ne]
            simp only [add_add_sub_cancel, add_sub_sub_cancel, RingHom.toMonoidHom_eq_coe,
              OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, coe_algebraMap,
              ZeroHom.coe_mk]
            ring
      rfl

/-- `(U - w)` is injective when `A - μ` is bounded below. -/
lemma cayley_shift_injective {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (μ : ℝ) --(hμ_ne : (↑μ : ℂ) + I ≠ 0)
    (hC : ∃ C > 0, ∀ ψ (hψ : ψ ∈ gen.domain), ‖gen.op ⟨ψ, hψ⟩ - μ • ψ‖ ≥ C * ‖ψ‖) :
    let U := cayleyTransform gen hsa
    let w := (↑μ - I) * (↑μ + I)⁻¹
    Function.Injective (U - w • ContinuousLinearMap.id ℂ H) := by
  intro U w φ₁ φ₂ h_eq
  rw [← sub_eq_zero]
  set φ := φ₁ - φ₂
  have h_zero : (U - w • ContinuousLinearMap.id ℂ H) φ = 0 := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
               ContinuousLinearMap.id_apply, φ, map_sub]
    have := h_eq
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
               ContinuousLinearMap.id_apply] at this
    exact sub_eq_zero_of_eq h_eq
  by_contra hφ_ne
  have h_eig : U φ = w • φ := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
               ContinuousLinearMap.id_apply, sub_eq_zero] at h_zero
    exact h_zero
  have h_exists : ∃ ψ : H, ∃ hψ : ψ ∈ gen.domain, ψ ≠ 0 ∧ gen.op ⟨ψ, hψ⟩ = μ • ψ := by
    rw [cayley_eigenvalue_correspondence gen hsa μ]
    exact ⟨φ, hφ_ne, h_eig⟩
  obtain ⟨ψ, hψ_mem, hψ_ne, h_Aψ⟩ := h_exists
  obtain ⟨C, hC_pos, hC_bound⟩ := hC
  have h_bound := hC_bound ψ hψ_mem
  rw [h_Aψ, sub_self, norm_zero] at h_bound
  have : ‖ψ‖ = 0 := by nlinarith [norm_nonneg ψ]
  exact hψ_ne (norm_eq_zero.mp this)

end QuantumMechanics.Cayley
