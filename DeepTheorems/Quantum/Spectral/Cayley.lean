/-
Author: Adam Bornemann
Created: 12-27-2025

================================================================================
CAYLEY TRANSFORM: Von Neumann's 1932 Approach
================================================================================

The Cayley transform establishes a bijection between self-adjoint operators
and unitary operators (with -1 not an eigenvalue), reducing unbounded spectral
theory to the bounded unitary case.

For self-adjoint A:
  U = (A - iI)(A + iI)⁻¹ = I - 2i·R_{-i}

Key properties:
  1. U is unitary
  2. A = i(I + U)(I - U)⁻¹ (inverse Cayley)
  3. Spectral correspondence: σ(U) = Cayley image of σ(A)

References:
  - Von Neumann, J. "Mathematische Grundlagen der Quantenmechanik" (1932)
  - Reed & Simon, Vol. 1, Section VIII.3
-/

import LogosLibrary.DeepTheorems.Quantum.Evolution.Resolvent
open InnerProductSpace MeasureTheory Complex Filter Topology  StonesTheorem.Bochner Stone.Generators
open scoped BigOperators Topology

namespace StonesTheorem.Cayley



variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
### The Cayley Transform
-/

/--
The Cayley transform of a self-adjoint generator.

**Definition:** U = I - 2i·R_{-i} where R_{-i} = (A + iI)⁻¹

**Equivalent forms:**
- U = (A - iI)(A + iI)⁻¹
- For φ ∈ H with ψ = R_{-i}(φ): Uφ = (A - iI)ψ

**Key insight:** This transforms the unbounded self-adjoint operator A
into a bounded unitary operator U, enabling use of bounded spectral theory.
-/

noncomputable def cayleyTransform {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - (2 * I) • Resolvent.resolvent_at_neg_i gen hsa

/--
Action of Cayley transform: Uφ = (A - iI)ψ where (A + iI)ψ = φ.

This is the fundamental computational lemma connecting U to A.
-/
lemma cayleyTransform_apply {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    let ψ := Resolvent.resolvent_at_neg_i gen hsa φ
    let hψ := Resolvent.resolvent_solution_mem_plus gen hsa φ
    cayleyTransform gen hsa φ = gen.op ⟨ψ, hψ⟩ - I • ψ := by
  simp only [cayleyTransform]
  -- ψ = R_{-i}(φ) satisfies (A + iI)ψ = φ, i.e., Aψ + iψ = φ
  let ψ := Resolvent.resolvent_at_neg_i gen hsa φ
  have hψ_mem := Resolvent.resolvent_solution_mem_plus gen hsa φ
  have hψ_eq : gen.op ⟨ψ, hψ_mem⟩ + I • ψ = φ := Resolvent.resolvent_solution_eq_plus gen hsa φ
  
  -- Uφ = φ - 2i·ψ = (Aψ + iψ) - 2iψ = Aψ - iψ = (A - iI)ψ
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
             ContinuousLinearMap.smul_apply]
  calc φ - (2 * I) • ψ
      = (gen.op ⟨ψ, hψ_mem⟩ + I • ψ) - (2 * I) • ψ := by rw [← hψ_eq]
    _ = gen.op ⟨ψ, hψ_mem⟩ + I • ψ - (2 * I) • ψ := rfl
    _ = gen.op ⟨ψ, hψ_mem⟩ - I • ψ := by
      rw [mul_smul, two_smul ℂ (I • ψ)]
      abel
    _ = gen.op ⟨ψ, hψ_mem⟩ - I • ψ := rfl

/-!
### Isometry Property

The key: ‖(A - iI)ψ‖² = ‖Aψ‖² + ‖ψ‖² = ‖(A + iI)ψ‖²

This identity (already proven in your resolvent file) immediately gives ‖Uφ‖ = ‖φ‖.
-/

/--
The Cayley transform is an isometry: ‖Uφ‖ = ‖φ‖ for all φ ∈ H.

**Proof:**
Let ψ = R_{-i}(φ), so (A + iI)ψ = φ and Uφ = (A - iI)ψ.
Using the fundamental identity ‖(A ± iI)ψ‖² = ‖Aψ‖² + ‖ψ‖²:
  ‖Uφ‖² = ‖(A - iI)ψ‖² = ‖Aψ‖² + ‖ψ‖² = ‖(A + iI)ψ‖² = ‖φ‖²
-/
theorem cayleyTransform_isometry {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    ∀ φ : H, ‖cayleyTransform gen hsa φ‖ = ‖φ‖ := by
  intro φ
  
  let ψ := Resolvent.resolvent_at_neg_i gen hsa φ
  have hψ_mem : ψ ∈ gen.domain := Resolvent.resolvent_solution_mem_plus gen hsa φ
  have hψ_eq : gen.op ⟨ψ, hψ_mem⟩ + I • ψ = φ := Resolvent.resolvent_solution_eq_plus gen hsa φ
  
  -- Uφ = (A - iI)ψ
  have h_Uφ : cayleyTransform gen hsa φ = gen.op ⟨ψ, hψ_mem⟩ - I • ψ := 
    cayleyTransform_apply gen hsa φ
  
  -- Key identity: ‖(A - iI)ψ‖² = ‖Aψ‖² + ‖ψ‖²
  have h_minus : ‖gen.op ⟨ψ, hψ_mem⟩ - I • ψ‖^2 = 
                 ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖ψ‖^2 := by
    -- This is the same calculation from resolvent_at_i continuity proof
    have norm_I_smul : ‖I • ψ‖ = ‖ψ‖ := by rw [norm_smul]; simp
    
    -- Cross term vanishes because ⟨Aψ, ψ⟩ is real
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
    
    -- Expand ‖x - y‖² = ‖x‖² + ‖y‖² - 2Re⟨x,y⟩
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
  
  -- Same identity for (A + iI): ‖(A + iI)ψ‖² = ‖Aψ‖² + ‖ψ‖²
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
  
  -- Chain: ‖Uφ‖² = ‖(A-iI)ψ‖² = ‖Aψ‖² + ‖ψ‖² = ‖(A+iI)ψ‖² = ‖φ‖²
  have h_sq : ‖cayleyTransform gen hsa φ‖^2 = ‖φ‖^2 := by
    calc ‖cayleyTransform gen hsa φ‖^2
        = ‖gen.op ⟨ψ, hψ_mem⟩ - I • ψ‖^2 := by rw [h_Uφ]
      _ = ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖ψ‖^2 := h_minus
      _ = ‖gen.op ⟨ψ, hψ_mem⟩ + I • ψ‖^2 := h_plus.symm
      _ = ‖φ‖^2 := by rw [hψ_eq]
  
  
  rw [← Real.sqrt_sq (norm_nonneg (cayleyTransform gen hsa φ)), 
    ← Real.sqrt_sq (norm_nonneg φ), h_sq]

/-!
### Surjectivity

Range(U) = Range(A - iI) = H by self-adjointness (hsa.2).
-/

/--
The Cayley transform is surjective.

**Proof:** For any χ ∈ H, by hsa.2 there exists ψ ∈ dom(A) with (A - iI)ψ = χ.
Set φ = (A + iI)ψ. Then Uφ = (A - iI)ψ = χ.
-/
theorem cayleyTransform_surjective {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    Function.Surjective (cayleyTransform gen hsa) := by
  intro χ
  -- By hsa.2: Range(A - iI) = H, so ∃ ψ ∈ dom with (A - iI)ψ = χ
  obtain ⟨ψ, hψ_dom, hψ_eq⟩ := hsa.2 χ
  
  -- Set φ = (A + iI)ψ
  let φ := gen.op ⟨ψ, hψ_dom⟩ + I • ψ
  use φ
  
  -- Need: Uφ = χ
  -- φ = (A + iI)ψ, and R_{-i}(φ) = ψ by uniqueness
  have h_Rφ : Resolvent.resolvent_at_neg_i gen hsa φ = ψ := by
    -- ψ solves (A + iI)x = φ, and solution is unique
    have h_sol : gen.op ⟨ψ, hψ_dom⟩ + I • ψ = φ := rfl
    let ψ' := Resolvent.resolvent_at_neg_i gen hsa φ
    have hψ'_mem := Resolvent.resolvent_solution_mem_plus gen hsa φ
    have hψ'_eq := Resolvent.resolvent_solution_eq_plus gen hsa φ
    -- ⊢ (Resolvent.resolvent_at_neg_i gen hsa) φ = ψ
    exact Resolvent.resolvent_at_neg_i_unique gen hsa φ ψ' ψ hψ'_mem hψ_dom hψ'_eq h_sol
  
  -- Uφ = (A - iI)·R_{-i}(φ) = (A - iI)ψ = χ
  have h_Uφ := cayleyTransform_apply gen hsa φ
  simp only at h_Uφ
  -- Need to connect resolvent_solution_mem_plus to hψ_dom via h_Rφ
  calc cayleyTransform gen hsa φ 
      = gen.op ⟨Resolvent.resolvent_at_neg_i gen hsa φ, Resolvent.resolvent_solution_mem_plus gen hsa φ⟩ - 
        I • Resolvent.resolvent_at_neg_i gen hsa φ := h_Uφ
    _ = gen.op ⟨ψ, hψ_dom⟩ - I • ψ := by 
        subst hψ_eq
        simp_all only [map_add, map_smul, φ]
    _ = χ := hψ_eq

/-!
### Unitarity

Isometry + Surjective on Hilbert space = Unitary
-/

/--
The Cayley transform is unitary.

An operator U on a Hilbert space is unitary iff:
1. U is an isometry: ‖Ux‖ = ‖x‖
2. U is surjective

Both conditions are satisfied by the Cayley transform.
-/
theorem cayleyTransform_unitary {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    (cayleyTransform gen hsa).adjoint * cayleyTransform gen hsa = 1 ∧
    cayleyTransform gen hsa * (cayleyTransform gen hsa).adjoint = 1 := by
  -- Isometry implies U*U = I
  have h_isometry := cayleyTransform_isometry gen hsa
  have h_star_self : (cayleyTransform gen hsa).adjoint * cayleyTransform gen hsa = 1 := by
    ext φ
    apply ext_inner_left ℂ
    intro ψ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [ContinuousLinearMap.adjoint_inner_right]
    -- ⟨U*Uφ, ψ⟩ = ⟨Uφ, Uψ⟩
    -- For isometry: ⟨Uφ, Uψ⟩ = ⟨φ, ψ⟩ (polarization identity)
    have h_polar : ⟪cayleyTransform gen hsa φ, cayleyTransform gen hsa ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := by
      set U := cayleyTransform gen hsa with hU
      
      -- From isometry: ‖Ux‖² = ‖x‖², i.e., ⟨Ux, Ux⟩ = ⟨x, x⟩
      have h_inner_self : ∀ x, ⟪U x, U x⟫_ℂ = ⟪x, x⟫_ℂ := by
        intro x
        have h1 : (⟪U x, U x⟫_ℂ).re = ‖U x‖^2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        have h2 : (⟪x, x⟫_ℂ).re = ‖x‖^2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        have h3 : (⟪U x, U x⟫_ℂ).im = 0 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
          norm_cast
        have h4 : (⟪x, x⟫_ℂ).im = 0 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
          norm_cast
        apply Complex.ext <;> simp only [h1, h2, h3, h4, h_isometry]
      
      -- Expand ⟨U(φ+ψ), U(φ+ψ)⟩ = ⟨φ+ψ, φ+ψ⟩
      have h_sum := h_inner_self (φ + ψ)
      rw [U.map_add, inner_add_left, inner_add_right, inner_add_right,
          inner_add_left, inner_add_right, inner_add_right] at h_sum
      
      -- We have: ⟨Uφ,Uφ⟩ + ⟨Uφ,Uψ⟩ + ⟨Uψ,Uφ⟩ + ⟨Uψ,Uψ⟩ = ⟨φ,φ⟩ + ⟨φ,ψ⟩ + ⟨ψ,φ⟩ + ⟨ψ,ψ⟩
      -- Using h_inner_self for φ and ψ:
      have hφ := h_inner_self φ
      have hψ := h_inner_self ψ
      
      -- So: ⟨Uφ,Uψ⟩ + ⟨Uψ,Uφ⟩ = ⟨φ,ψ⟩ + ⟨ψ,φ⟩
      have h_re_part : ⟪U φ, U ψ⟫_ℂ + ⟪U ψ, U φ⟫_ℂ = ⟪φ, ψ⟫_ℂ + ⟪ψ, φ⟫_ℂ := by
        have h_sum := h_inner_self (φ + ψ)
        rw [U.map_add] at h_sum
        have lhs : ⟪U φ + U ψ, U φ + U ψ⟫_ℂ = 
                  ⟪U φ, U φ⟫_ℂ + ⟪U φ, U ψ⟫_ℂ + ⟪U ψ, U φ⟫_ℂ + ⟪U ψ, U ψ⟫_ℂ := by
          rw [inner_add_left, inner_add_right, inner_add_right]; ring
        have rhs : ⟪φ + ψ, φ + ψ⟫_ℂ = 
                  ⟪φ, φ⟫_ℂ + ⟪φ, ψ⟫_ℂ + ⟪ψ, φ⟫_ℂ + ⟪ψ, ψ⟫_ℂ := by
          rw [inner_add_left, inner_add_right, inner_add_right]; ring
        rw [lhs, rhs, hφ, hψ] at h_sum
        calc ⟪U φ, U ψ⟫_ℂ + ⟪U ψ, U φ⟫_ℂ 
            = (⟪φ, φ⟫_ℂ + ⟪U φ, U ψ⟫_ℂ + ⟪U ψ, U φ⟫_ℂ + ⟪ψ, ψ⟫_ℂ) - ⟪φ, φ⟫_ℂ - ⟪ψ, ψ⟫_ℂ := by ring
          _ = (⟪φ, φ⟫_ℂ + ⟪φ, ψ⟫_ℂ + ⟪ψ, φ⟫_ℂ + ⟪ψ, ψ⟫_ℂ) - ⟪φ, φ⟫_ℂ - ⟪ψ, ψ⟫_ℂ := by rw [h_sum]
          _ = ⟪φ, ψ⟫_ℂ + ⟪ψ, φ⟫_ℂ := by ring
      
      -- Now do the same with I • ψ to get imaginary part
      have h_sum_i := h_inner_self (φ + I • ψ)
      rw [U.map_add, U.map_smul, inner_add_left, inner_add_right, inner_add_right,
          inner_add_left, inner_add_right, inner_add_right] at h_sum_i
      
      have hIψ : ⟪U (I • ψ), U (I • ψ)⟫_ℂ = ⟪I • ψ, I • ψ⟫_ℂ := h_inner_self (I • ψ)
      rw [U.map_smul] at hIψ
      
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
        rw [lhs, rhs, hφ, hIψ] at h_sum_i
        calc ⟪U φ, I • U ψ⟫_ℂ + ⟪I • U ψ, U φ⟫_ℂ
            = (⟪φ, φ⟫_ℂ + ⟪U φ, I • U ψ⟫_ℂ + ⟪I • U ψ, U φ⟫_ℂ + ⟪I • ψ, I • ψ⟫_ℂ) - 
              ⟪φ, φ⟫_ℂ - ⟪I • ψ, I • ψ⟫_ℂ := by ring
          _ = (⟪φ, φ⟫_ℂ + ⟪φ, I • ψ⟫_ℂ + ⟪I • ψ, φ⟫_ℂ + ⟪I • ψ, I • ψ⟫_ℂ) - 
              ⟪φ, φ⟫_ℂ - ⟪I • ψ, I • ψ⟫_ℂ := by rw [h_sum_i]
          _ = ⟪φ, I • ψ⟫_ℂ + ⟪I • ψ, φ⟫_ℂ := by ring
      
      -- From h_re_part: ⟨a,b⟩ + ⟨b,a⟩ = ⟨a,b⟩ + conj⟨a,b⟩ = 2 Re⟨a,b⟩
      -- So Re⟨Uφ,Uψ⟩ = Re⟨φ,ψ⟩
      
      -- From h_im_part: ⟨a,ib⟩ + ⟨ib,a⟩ = i⟨a,b⟩ + conj(i)conj⟨a,b⟩ = i⟨a,b⟩ - i·conj⟨a,b⟩
      --                = i(⟨a,b⟩ - conj⟨a,b⟩) = i · 2i · Im⟨a,b⟩ = -2 Im⟨a,b⟩
      -- So Im⟨Uφ,Uψ⟩ = Im⟨φ,ψ⟩
      
      apply Complex.ext
      · -- Real parts equal
        have h1 : ⟪U ψ, U φ⟫_ℂ = (starRingEnd ℂ) ⟪U φ, U ψ⟫_ℂ := (inner_conj_symm _ _).symm
        have h2 : ⟪ψ, φ⟫_ℂ = (starRingEnd ℂ) ⟪φ, ψ⟫_ℂ := (inner_conj_symm _ _).symm
        have h3 : (⟪U φ, U ψ⟫_ℂ + (starRingEnd ℂ) ⟪U φ, U ψ⟫_ℂ).re = 2 * (⟪U φ, U ψ⟫_ℂ).re := by
          simp only [Complex.add_re, Complex.conj_re]
          ring
        have h4 : (⟪φ, ψ⟫_ℂ + (starRingEnd ℂ) ⟪φ, ψ⟫_ℂ).re = 2 * (⟪φ, ψ⟫_ℂ).re := by
          simp only [Complex.add_re, Complex.conj_re]
          ring
        rw [h1, h2] at h_re_part
        have := congrArg Complex.re h_re_part
        rw [h3, h4] at this
        linarith
        
      · -- Imaginary parts equal
        rw [inner_smul_right, inner_smul_left, inner_smul_right, inner_smul_left] at h_im_part
        simp only [Complex.conj_I] at h_im_part
        have h1 : ⟪U ψ, U φ⟫_ℂ = (starRingEnd ℂ) ⟪U φ, U ψ⟫_ℂ := (inner_conj_symm _ _).symm
        have h2 : ⟪ψ, φ⟫_ℂ = (starRingEnd ℂ) ⟪φ, ψ⟫_ℂ := (inner_conj_symm _ _).symm
        -- I * ⟨a,b⟩ + (-I) * conj⟨a,b⟩ = I * (⟨a,b⟩ - conj⟨a,b⟩) = I * 2i * Im⟨a,b⟩ = -2 Im⟨a,b⟩
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
  
  -- Surjectivity + isometry implies UU* = I  
  have h_surj := cayleyTransform_surjective gen hsa
  have h_self_star : cayleyTransform gen hsa * (cayleyTransform gen hsa).adjoint = 1 := by
    set U := cayleyTransform gen hsa with hU
    ext φ
    obtain ⟨ψ, hψ⟩ := cayleyTransform_surjective gen hsa φ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [← hψ]
    -- Goal: U(U*Uψ) = Uψ, and U*U = 1
    have : U.adjoint (U ψ) = ψ := by
      have h := congrFun (congrArg DFunLike.coe h_star_self) ψ
      simp at h
      exact h
    rw [this, hψ]
  
  exact ⟨h_star_self, h_self_star⟩

/-!
### Eigenvalue -1

For self-adjoint A: -1 is an eigenvalue of U iff 0 is an eigenvalue of A.
-/

/--
-1 is an eigenvalue of the Cayley transform iff 0 is an eigenvalue of A.

If Uφ = -φ with φ ≠ 0, then φ = iψ where Aψ = 0 and ψ ≠ 0.
-/
theorem cayley_neg_one_eigenvalue_iff {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    (∃ φ : H, φ ≠ 0 ∧ cayleyTransform gen hsa φ = -φ) ↔
    (∃ ψ : gen.domain, (ψ : H) ≠ 0 ∧ gen.op ψ = 0) := by
  constructor
  · -- (⇒) If Uφ = -φ, find kernel element
    intro ⟨φ, hφ_ne, hUφ⟩
    let ψ := Resolvent.resolvent_at_neg_i gen hsa φ
    have hψ_mem := Resolvent.resolvent_solution_mem_plus gen hsa φ
    have hψ_eq := Resolvent.resolvent_solution_eq_plus gen hsa φ  -- (A + iI)ψ = φ
    
    -- From Uφ = -φ and Uφ = (A - iI)ψ:
    have h_Uφ := cayleyTransform_apply gen hsa φ
    -- (A - iI)ψ = -φ = -(A + iI)ψ
    have h1 : gen.op ⟨ψ, hψ_mem⟩ - I • ψ = -(gen.op ⟨ψ, hψ_mem⟩ + I • ψ) := by
      calc gen.op ⟨ψ, hψ_mem⟩ - I • ψ 
          = cayleyTransform gen hsa φ := h_Uφ.symm
        _ = -φ := hUφ
        _ = -(gen.op ⟨ψ, hψ_mem⟩ + I • ψ) := by rw [← hψ_eq] ; exact rfl
    
    -- Simplify: 2Aψ = 0, so Aψ = 0
    have h_Aψ_zero : gen.op ⟨ψ, hψ_mem⟩ = 0 := by
      have h2 : gen.op ⟨ψ, hψ_mem⟩ - I • ψ + (gen.op ⟨ψ, hψ_mem⟩ + I • ψ) = 0 := by
        rw [h1]; abel
      have h3 : (2 : ℂ) • gen.op ⟨ψ, hψ_mem⟩ = 0 := by
        calc (2 : ℂ) • gen.op ⟨ψ, hψ_mem⟩ 
            = gen.op ⟨ψ, hψ_mem⟩ + gen.op ⟨ψ, hψ_mem⟩ := two_smul ℂ _
          _ = (gen.op ⟨ψ, hψ_mem⟩ - I • ψ) + (gen.op ⟨ψ, hψ_mem⟩ + I • ψ) := by abel
          _ = 0 := h2
      exact (smul_eq_zero.mp h3).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
    
    -- ψ ≠ 0 because φ = iψ and φ ≠ 0
    have hψ_ne : ψ ≠ 0 := by
      intro hψ_eq_zero
      have : φ = 0 := by
        calc φ = gen.op ⟨ψ, hψ_mem⟩ + I • ψ := hψ_eq.symm
          _ = 0 + I • ψ := by rw [h_Aψ_zero]
          _ = 0 + I • 0 := by rw [hψ_eq_zero]
          _ = 0 := by simp
      exact hφ_ne this
    
    exact ⟨⟨ψ, hψ_mem⟩, hψ_ne, h_Aψ_zero⟩
    
  · -- (⇐) If Aψ = 0, construct eigenvector
    intro ⟨⟨ψ, hψ_mem⟩, hψ_ne, h_Aψ⟩
    -- Set φ = (A + iI)ψ = iψ
    let φ := I • ψ
    have hφ_eq : gen.op ⟨ψ, hψ_mem⟩ + I • ψ = φ := by simp [φ, h_Aψ]
    
    use φ
    constructor
    · -- φ ≠ 0
      intro hφ_zero
      have : ψ = 0 := by
        have h := hφ_zero
        simp only [φ] at h
        exact (smul_eq_zero.mp h).resolve_left I_ne_zero
      exact hψ_ne this
    · -- Uφ = -φ
      -- R_{-i}(φ) = ψ by uniqueness
      have h_Rφ : Resolvent.resolvent_at_neg_i gen hsa φ = ψ := by
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


/-!
### Inverse Cayley Transform

For a unitary U with -1 not an eigenvalue:
  A = i(I + U)(I - U)⁻¹

The domain of A is Range(I - U).
-/

/--
(I - U) applied to the resolvent output gives 2i times the domain element.

If φ = (A + iI)ψ, then (I - U)φ = 2i·ψ
-/
lemma one_minus_cayley_apply {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) 
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    (ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa) φ = (2 * I) • ψ := by
  simp only [cayleyTransform, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
             ContinuousLinearMap.smul_apply]
  -- (I - U)φ = φ - Uφ = φ - (φ - 2i·R_{-i}(φ))
  -- But R_{-i}(φ) = ψ since (A + iI)ψ = φ
  have h_R : Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = ψ := by
    apply Resolvent.resolvent_at_neg_i_unique gen hsa _ 
      (Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ)) ψ
      (Resolvent.resolvent_solution_mem_plus gen hsa _) hψ
      (Resolvent.resolvent_solution_eq_plus gen hsa _)
    rfl
  calc (gen.op ⟨ψ, hψ⟩ + I • ψ) - ((gen.op ⟨ψ, hψ⟩ + I • ψ) - (2 * I) • Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ))
      = (2 * I) • Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) := by abel
    _ = (2 * I) • ψ := by rw [h_R]

/--
(I + U) applied gives 2 times the operator output.

If φ = (A + iI)ψ, then (I + U)φ = 2·Aψ
-/
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
  -- (I + U)φ = φ + Uφ = φ + (φ - 2i·ψ) = 2φ - 2iψ = 2(Aψ + iψ) - 2iψ = 2Aψ
  calc (gen.op ⟨ψ, hψ⟩ + I • ψ) + ((gen.op ⟨ψ, hψ⟩ + I • ψ) - (2 * I) • Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ))
      = (gen.op ⟨ψ, hψ⟩ + I • ψ) + ((gen.op ⟨ψ, hψ⟩ + I • ψ) - (2 * I) • ψ) := by rw [h_R]
    _ = (2 : ℂ) • gen.op ⟨ψ, hψ⟩ := by 
      have h1 : I • ψ + I • ψ = (2 * I) • ψ := by rw [← two_smul ℂ (I • ψ), smul_smul];
      calc gen.op ⟨ψ, hψ⟩ + I • ψ + (gen.op ⟨ψ, hψ⟩ + I • ψ - (2 * I) • ψ)
          = gen.op ⟨ψ, hψ⟩ + gen.op ⟨ψ, hψ⟩ + (I • ψ + I • ψ) - (2 * I) • ψ := by abel
        _ = gen.op ⟨ψ, hψ⟩ + gen.op ⟨ψ, hψ⟩ + (2 * I) • ψ - (2 * I) • ψ := by rw [h1]
        _ = gen.op ⟨ψ, hψ⟩ + gen.op ⟨ψ, hψ⟩ := by abel
        _ = (2 : ℂ) • gen.op ⟨ψ, hψ⟩ := by rw [two_smul]


/--
The inverse Cayley formula: on dom(A), we have A = i(I+U)(I-U)⁻¹.

More precisely: (I - U)φ = 2i·ψ and (I + U)φ = 2·Aψ imply Aψ = (i/2)(I+U)·(I-U)⁻¹(2i·ψ)
-/
theorem inverse_cayley_relation {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    let U := cayleyTransform gen hsa
    -- The key relation: multiplying (I-U)φ by the right factor recovers 2·Aψ from (I+U)φ
    (2 * I) • gen.op ⟨ψ, hψ⟩ = I • ((ContinuousLinearMap.id ℂ H + U) φ) := by
  have h_plus := one_plus_cayley_apply gen hsa ψ hψ
  simp only [h_plus, smul_smul]
  ring_nf


/--
The inverse Cayley formula: for ψ ∈ dom(A), the relation between 
(I ± U) applied to φ = (A + iI)ψ gives the inverse Cayley structure.

(I - U)φ = 2i·ψ  and  (I + U)φ = 2·Aψ

Together these give: Aψ = (i/2)·(I + U)·(2i·ψ)/(2i) = i·(I+U)(I-U)⁻¹ψ
-/
theorem inverse_cayley_formula {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    let U := cayleyTransform gen hsa
    -- The two fundamental relations that define the inverse Cayley
    (ContinuousLinearMap.id ℂ H - U) φ = (2 * I) • ψ ∧
    (ContinuousLinearMap.id ℂ H + U) φ = (2 : ℂ) • gen.op ⟨ψ, hψ⟩ := by
  exact ⟨one_minus_cayley_apply gen hsa ψ hψ, one_plus_cayley_apply gen hsa ψ hψ⟩

/--
Range characterization: Range(I - U) contains 2i · dom(A).

Every element of the form 2i·ψ for ψ ∈ dom(A) is in Range(I - U).
-/
lemma range_one_minus_cayley {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    ∀ ψ : H, ψ ∈ gen.domain → 
      ∃ φ : H, (ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa) φ = (2 * I) • ψ := by
  intro ψ hψ
  use gen.op ⟨ψ, hψ⟩ + I • ψ
  exact one_minus_cayley_apply gen hsa ψ hψ



theorem inverse_cayley_domain {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let U := cayleyTransform gen hsa
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    ψ = ((-I) / 2) • ((ContinuousLinearMap.id ℂ H - U) φ) := by
  have h_minus := one_minus_cayley_apply gen hsa ψ hψ
  -- h_minus : (I - U)φ = (2 * I) • ψ
  -- So: ψ = (2 * I)⁻¹ • (I - U)φ = (1/(2i)) • (I - U)φ = (-i/2) • (I - U)φ
  have h_inv : ((-I) / 2) • ((2 * I) • ψ) = ψ := by
    rw [smul_smul]
    have : (-I) / 2 * (2 * I) = 1 := by
      field_simp
      simp_all only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id', Pi.sub_apply, id_eq, map_add, map_smul,
        I_sq, neg_neg]
    rw [this, one_smul]
  rw [← h_minus] at h_inv
  exact h_inv.symm

/--
The bijection characterization: the map ψ ↦ (A + iI)ψ is inverted by
φ ↦ (-i/2)·(I - U)φ on the range.
-/
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

end StonesTheorem.Cayley
