/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform.Transform

/-!
# The Inverse Cayley Transform

This file develops the inverse Cayley transform, recovering the generator `A` from the
unitary operator `U`, and proves the fundamental domain characterization `dom(A) = range(I - U)`.

## Main definitions

* `inverseCayleyOp`: The inverse Cayley transform recovering `A` from `U`

## Main statements

* `one_minus_cayley_apply`: Formula for `(I - U)φ` on range elements
* `one_plus_cayley_apply`: Formula for `(I + U)φ` on range elements
* `inverse_cayley_formula`: Both formulas combined
* `inverseCayleyOp_symmetric`: The inverse Cayley transform is symmetric
* `generator_domain_eq_range_one_minus_cayley`: `dom(A) = range(I - U)`
-/

namespace QuantumMechanics.Cayley

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Formula for `(I - U)φ` where `φ = (A + iI)ψ`. -/
lemma one_minus_cayley_apply {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    (ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa) φ = (2 * I) • ψ := by
  simp only [cayleyTransform, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
             ContinuousLinearMap.smul_apply]
  have h_R : Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = ψ := by
    apply Resolvent.resolvent_at_neg_i_unique gen hsa _
      (Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ)) ψ
      (Resolvent.resolvent_solution_mem_plus gen hsa _) hψ
      (Resolvent.resolvent_solution_eq_plus gen hsa _)
    rfl
  calc (gen.op ⟨ψ, hψ⟩ + I • ψ) -
       ((gen.op ⟨ψ, hψ⟩ + I • ψ) - (2 * I) • Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ))
      = (2 * I) • Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) := by abel
    _ = (2 * I) • ψ := by rw [h_R]

/-- Formula for `(I + U)φ` where `φ = (A + iI)ψ`. -/
lemma one_plus_cayley_apply {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    (ContinuousLinearMap.id ℂ H + cayleyTransform gen hsa) φ = (2 : ℂ) • gen.op ⟨ψ, hψ⟩ := by
  simp only [cayleyTransform, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
             ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
  have h_R : Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = ψ := by
    apply Resolvent.resolvent_at_neg_i_unique gen hsa _
      (Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ)) ψ
      (Resolvent.resolvent_solution_mem_plus gen hsa _) hψ
      (Resolvent.resolvent_solution_eq_plus gen hsa _)
    rfl
  calc (gen.op ⟨ψ, hψ⟩ + I • ψ) +
       ((gen.op ⟨ψ, hψ⟩ + I • ψ) - (2 * I) • Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ))
      = (gen.op ⟨ψ, hψ⟩ + I • ψ) + ((gen.op ⟨ψ, hψ⟩ + I • ψ) - (2 * I) • ψ) := by rw [h_R]
    _ = (2 : ℂ) • gen.op ⟨ψ, hψ⟩ := by
      have h1 : I • ψ + I • ψ = (2 * I) • ψ := by rw [← two_smul ℂ (I • ψ), smul_smul]
      calc gen.op ⟨ψ, hψ⟩ + I • ψ + (gen.op ⟨ψ, hψ⟩ + I • ψ - (2 * I) • ψ)
          = gen.op ⟨ψ, hψ⟩ + gen.op ⟨ψ, hψ⟩ + (I • ψ + I • ψ) - (2 * I) • ψ := by abel
        _ = gen.op ⟨ψ, hψ⟩ + gen.op ⟨ψ, hψ⟩ + (2 * I) • ψ - (2 * I) • ψ := by rw [h1]
        _ = gen.op ⟨ψ, hψ⟩ + gen.op ⟨ψ, hψ⟩ := by abel
        _ = (2 : ℂ) • gen.op ⟨ψ, hψ⟩ := by rw [two_smul]

/-- The relation `(2i)Aψ = i(I + U)φ` for `φ = (A + iI)ψ`. -/
theorem inverse_cayley_relation {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    let U := cayleyTransform gen hsa
    (2 * I) • gen.op ⟨ψ, hψ⟩ = I • ((ContinuousLinearMap.id ℂ H + U) φ) := by
  have h_plus := one_plus_cayley_apply gen hsa ψ hψ
  simp only [h_plus, smul_smul]
  ring_nf

/-- Combined formulas for `(I - U)φ` and `(I + U)φ`. -/
theorem inverse_cayley_formula {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    let U := cayleyTransform gen hsa
    (ContinuousLinearMap.id ℂ H - U) φ = (2 * I) • ψ ∧
    (ContinuousLinearMap.id ℂ H + U) φ = (2 : ℂ) • gen.op ⟨ψ, hψ⟩ := by
  exact ⟨one_minus_cayley_apply gen hsa ψ hψ, one_plus_cayley_apply gen hsa ψ hψ⟩

/-- Every domain element is in the range of `I - U` (up to scaling). -/
lemma range_one_minus_cayley {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    ∀ ψ : H, ψ ∈ gen.domain →
      ∃ φ : H, (ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa) φ = (2 * I) • ψ := by
  intro ψ hψ
  use gen.op ⟨ψ, hψ⟩ + I • ψ
  exact one_minus_cayley_apply gen hsa ψ hψ

/-- Recovery formula: `ψ = (-i/2)(I - U)φ`. -/
theorem inverse_cayley_domain {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let U := cayleyTransform gen hsa
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    ψ = ((-I) / 2) • ((ContinuousLinearMap.id ℂ H - U) φ) := by
  have h_minus := one_minus_cayley_apply gen hsa ψ hψ
  have h_inv : ((-I) / 2) • ((2 * I) • ψ) = ψ := by
    rw [smul_smul]
    have : (-I) / 2 * (2 * I) = 1 := by
      field_simp
      simp_all only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
                     Pi.sub_apply, id_eq, map_add, map_smul, I_sq, neg_neg]
    rw [this, one_smul]
  rw [← h_minus] at h_inv
  exact h_inv.symm

/-- Bijection formulas: recovering both `ψ` and `Aψ` from `φ`. -/
theorem cayley_bijection {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    ((-I) / 2) • ((ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa) φ) = ψ ∧
    ((1 : ℂ) / 2) • ((ContinuousLinearMap.id ℂ H + cayleyTransform gen hsa) φ) = gen.op ⟨ψ, hψ⟩ := by
  constructor
  · exact (inverse_cayley_domain gen hsa ψ hψ).symm
  · have h := one_plus_cayley_apply gen hsa ψ hψ
    simp only [h, smul_smul]
    norm_num

/-- The inverse Cayley transform as a linear map on `range(I - U)`. -/
noncomputable def inverseCayleyOp (U : H →L[ℂ] H)
    (_ : ∀ ψ φ, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ)
    (h_one : ∀ ψ, U ψ = ψ → ψ = 0)
    (_ : ∀ ψ, U ψ = -ψ → ψ = 0) :
    LinearMap.range (ContinuousLinearMap.id ℂ H - U) →ₗ[ℂ] H where
  toFun := fun ⟨φ, hφ⟩ =>
    let ψ := Classical.choose hφ
    I • (U ψ + ψ)
  map_add' := by
    intro ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩
    simp only [smul_add]
    set ψ₁ := Classical.choose hφ₁ with hψ₁_def
    set ψ₂ := Classical.choose hφ₂ with hψ₂_def
    have hψ₁ : (ContinuousLinearMap.id ℂ H - U) ψ₁ = φ₁ := Classical.choose_spec hφ₁
    have hψ₂ : (ContinuousLinearMap.id ℂ H - U) ψ₂ = φ₂ := Classical.choose_spec hφ₂
    have hφ₁₂ : ∃ ψ, (ContinuousLinearMap.id ℂ H - U) ψ = φ₁ + φ₂ := ⟨ψ₁ + ψ₂, by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_add]
      rw [← hψ₁, ← hψ₂]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]⟩
    set ψ₁₂ := Classical.choose hφ₁₂ with hψ₁₂_def
    have hψ₁₂ : (ContinuousLinearMap.id ℂ H - U) ψ₁₂ = φ₁ + φ₂ := Classical.choose_spec hφ₁₂
    have h_diff : ψ₁₂ = ψ₁ + ψ₂ := by
      have h_eq : (ContinuousLinearMap.id ℂ H - U) ψ₁₂ =
                  (ContinuousLinearMap.id ℂ H - U) (ψ₁ + ψ₂) := by
        rw [hψ₁₂]
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_add]
        rw [← hψ₁, ← hψ₂]
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      have h_sub : (ContinuousLinearMap.id ℂ H - U) (ψ₁₂ - (ψ₁ + ψ₂)) = 0 := by
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
                   map_sub, map_add]
        rw [sub_eq_zero]
        convert h_eq using 1
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
        rw [map_add]
        abel
      have h_fixed : U (ψ₁₂ - (ψ₁ + ψ₂)) = ψ₁₂ - (ψ₁ + ψ₂) := by
        have : ψ₁₂ - (ψ₁ + ψ₂) - U (ψ₁₂ - (ψ₁ + ψ₂)) = 0 := by
          convert h_sub using 1
        exact (sub_eq_zero.mp this).symm
      exact eq_of_sub_eq_zero (h_one _ h_fixed)
    rw [h_diff, map_add]
    simp only [smul_add]
    abel
  map_smul' := by
    intro c ⟨φ, hφ⟩
    simp only [RingHom.id_apply, smul_add]
    set ψ := Classical.choose hφ with hψ_def
    have hψ : (ContinuousLinearMap.id ℂ H - U) ψ = φ := Classical.choose_spec hφ
    have hcφ : ∃ ψ', (ContinuousLinearMap.id ℂ H - U) ψ' = c • φ := ⟨c • ψ, by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_smul]
      rw [← hψ]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]⟩
    set ψ' := Classical.choose hcφ with hψ'_def
    have hψ' : (ContinuousLinearMap.id ℂ H - U) ψ' = c • φ := Classical.choose_spec hcφ
    have h_diff : ψ' = c • ψ := by
      have h_sub : (ContinuousLinearMap.id ℂ H - U) (ψ' - c • ψ) = 0 := by
        have eq1 : (ContinuousLinearMap.id ℂ H - U) ψ' = c • φ := hψ'
        have eq2 : (ContinuousLinearMap.id ℂ H - U) ψ = φ := hψ
        simp only [map_sub, map_smul, eq1, eq2]
        abel
      have h_fixed : U (ψ' - c • ψ) = ψ' - c • ψ := by
        have : ψ' - c • ψ - U (ψ' - c • ψ) = 0 := by
          convert h_sub using 1
        exact (sub_eq_zero.mp this).symm
      exact eq_of_sub_eq_zero (h_one _ h_fixed)
    rw [h_diff, map_smul, smul_comm c I (U ψ), smul_comm c I ψ]

-- inverseCayleyOp_symmetric doesn't use [CompleteSpace H]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- The inverse Cayley transform is symmetric. -/
theorem inverseCayleyOp_symmetric (U : H →L[ℂ] H)
    (hU : ∀ ψ φ, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ)
    (h_one : ∀ ψ, U ψ = ψ → ψ = 0)
    (h_neg_one : ∀ ψ, U ψ = -ψ → ψ = 0) :
    ∀ ψ φ : LinearMap.range (ContinuousLinearMap.id ℂ H - U),
      ⟪inverseCayleyOp U hU h_one h_neg_one ψ, (φ : H)⟫_ℂ =
      ⟪(ψ : H), inverseCayleyOp U hU h_one h_neg_one φ⟫_ℂ := by
  intro ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩
  set χ₁ := Classical.choose hφ₁ with hχ₁_def
  set χ₂ := Classical.choose hφ₂ with hχ₂_def
  have hχ₁ : (ContinuousLinearMap.id ℂ H - U) χ₁ = φ₁ := Classical.choose_spec hφ₁
  have hχ₂ : (ContinuousLinearMap.id ℂ H - U) χ₂ = φ₂ := Classical.choose_spec hφ₂
  have hφ₁_eq : φ₁ = χ₁ - U χ₁ := by
    rw [← hχ₁]; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  have hφ₂_eq : φ₂ = χ₂ - U χ₂ := by
    rw [← hχ₂]; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  have hcoe₁ : (⟨φ₁, hφ₁⟩ : LinearMap.range (ContinuousLinearMap.id ℂ H - U)).val = φ₁ := rfl
  have hcoe₂ : (⟨φ₂, hφ₂⟩ : LinearMap.range (ContinuousLinearMap.id ℂ H - U)).val = φ₂ := rfl
  show ⟪I • (U χ₁ + χ₁), φ₂⟫_ℂ = ⟪φ₁, I • (U χ₂ + χ₂)⟫_ℂ
  rw [hφ₁_eq, hφ₂_eq]
  rw [inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]
  rw [inner_add_left, inner_sub_right, inner_sub_right]
  rw [inner_sub_left, inner_add_right, inner_add_right]
  rw [hU χ₁ χ₂]
  simp only [RCLike.star_def, conj_I, sub_add_sub_cancel, neg_mul]
  ring


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- The domain of `A` equals the range of `I - U`. -/
theorem generator_domain_eq_range_one_minus_cayley {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (gen.domain : Set H) = LinearMap.range (ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa) := by
  set U := cayleyTransform gen hsa with hU_def
  ext ψ
  constructor
  · intro hψ
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    have h_Uφ : U φ = gen.op ⟨ψ, hψ⟩ - I • ψ := by
      simp only [U, cayleyTransform, ContinuousLinearMap.sub_apply,
                 ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
      have h_res : Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = ψ :=
        Resolvent.resolvent_at_neg_i_left_inverse gen hsa ψ hψ
      rw [h_res]
      module
    have h_diff : (ContinuousLinearMap.id ℂ H - U) φ = (2 * I) • ψ := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, h_Uφ]
      simp only [φ]
      module
    rw [@LinearMap.coe_range]
    use (2 * I)⁻¹ • φ
    simp only [map_smul, h_diff, smul_smul]
    have h_ne : (2 : ℂ) * I ≠ 0 := by simp
    field_simp [h_ne]
    module
  · intro hψ
    rw [LinearMap.coe_range] at hψ
    obtain ⟨χ, hχ⟩ := hψ
    set η := Resolvent.resolvent_at_neg_i gen hsa χ with hη_def
    have hη_mem : η ∈ gen.domain := Resolvent.resolvent_solution_mem_plus gen hsa χ
    have hχ_eq : gen.op ⟨η, hη_mem⟩ + I • η = χ := Resolvent.resolvent_solution_eq_plus gen hsa χ
    have h_Uχ : U χ = gen.op ⟨η, hη_mem⟩ - I • η := by
      rw [← hχ_eq]
      simp only [U, cayleyTransform, ContinuousLinearMap.sub_apply,
                 ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
      have h_res : Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨η, hη_mem⟩ + I • η) = η :=
        Resolvent.resolvent_at_neg_i_left_inverse gen hsa η hη_mem
      rw [h_res]
      module
    have h_diff : (ContinuousLinearMap.id ℂ H - U) χ = (2 * I) • η := by
      calc (ContinuousLinearMap.id ℂ H - U) χ
          = χ - U χ := by simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
        _ = χ - (gen.op ⟨η, hη_mem⟩ - I • η) := by rw [h_Uχ]
        _ = (gen.op ⟨η, hη_mem⟩ + I • η) - (gen.op ⟨η, hη_mem⟩ - I • η) := by rw [← hχ_eq]
        _ = (2 * I) • η := by module
    simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
               Pi.sub_apply, id_eq] at hχ
    rw [← hχ]
    subst hχ
    simp_all only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
                   Pi.sub_apply, id_eq, SetLike.mem_coe, U, η]
    apply SMulMemClass.smul_mem
    exact hη_mem

end QuantumMechanics.Cayley
