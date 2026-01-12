/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent
/-!
# The Cayley Transform for Self-Adjoint Operators

This file develops the Cayley transform, which establishes a fundamental correspondence
between self-adjoint operators (generators of one-parameter unitary groups) and unitary
operators. Given a self-adjoint operator `A` on a Hilbert space, the Cayley transform
produces the unitary operator `U = (A - iI)(A + iI)⁻¹`.

## Main definitions

* `QuantumMechanics.Cayley.Unitary`: Predicate for an operator satisfying `U* U = U U* = 1`
* `QuantumMechanics.Cayley.cayleyTransform`: The Cayley transform `(A - iI)(A + iI)⁻¹`
  of a self-adjoint generator
* `QuantumMechanics.Cayley.inverseCayleyOp`: Partial inverse recovering `A` from `U`
* `QuantumMechanics.Cayley.cayleyImage`: The Möbius image `{(μ - i)/(μ + i) | μ ∈ B}`
  of a set of reals

## Main statements

* `cayleyTransform_unitary`: The Cayley transform of a self-adjoint operator is unitary
* `cayleyTransform_isometry`: The Cayley transform preserves norms
* `cayley_neg_one_eigenvalue_iff`: `-1` is an eigenvalue of `U` iff `0` is an eigenvalue of `A`
* `cayley_eigenvalue_correspondence`: `μ ∈ ℝ` is an eigenvalue of `A` iff
  `(μ - i)/(μ + i)` is an eigenvalue of `U`
* `cayley_spectrum_correspondence`: Full spectral correspondence: `μ` is in the
  approximate point spectrum of `A` iff `(μ - i)/(μ + i)` is in the spectrum of `U`
* `generator_domain_eq_range_one_minus_cayley`: `dom(A) = range(I - U)`

## Implementation notes

The Cayley transform is defined via the resolvent `(A + iI)⁻¹` rather than directly,
since `A` is unbounded and defined only on a dense domain. The key identity exploited
throughout is:
  `U(Aψ + iψ) = Aψ - iψ`   for `ψ ∈ dom(A)`

The Möbius transformation `μ ↦ (μ - i)/(μ + i)` maps `ℝ` bijectively onto the unit
circle minus `{1}`, which explains why `-1` as an eigenvalue of `U` corresponds to
`0` being an eigenvalue of `A` (the "point at infinity" in the Möbius sense).

## References

* [Reed and Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*]
* [Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*]
* [Rudin, *Functional Analysis*], Chapter 13
-/
namespace QuantumMechanics.Cayley

open InnerProductSpace MeasureTheory Complex Filter Topology  QuantumMechanics.Bochner QuantumMechanics.Generators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


def Unitary (U : H →L[ℂ] H) : Prop :=
  U.adjoint * U = 1 ∧ U * U.adjoint = 1

/-- The Cayley transform preserves inner products. -/
lemma Unitary.inner_map_map {U : H →L[ℂ] H} (hU : Unitary U) (x y : H) :
    ⟪U x, U y⟫_ℂ = ⟪x, y⟫_ℂ := by
  calc ⟪U x, U y⟫_ℂ
      = ⟪U.adjoint (U x), y⟫_ℂ := by rw [ContinuousLinearMap.adjoint_inner_left]
    _ = ⟪(U.adjoint * U) x, y⟫_ℂ := rfl
    _ = ⟪x, y⟫_ℂ := by rw [hU.1]; simp

lemma Unitary.norm_map {U : H →L[ℂ] H} (hU : Unitary U) (x : H) : ‖U x‖ = ‖x‖ := by
  have h := hU.inner_map_map x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h_sq : ‖U x‖^2 = ‖x‖^2 := by exact_mod_cast h
  nlinarith [norm_nonneg (U x), norm_nonneg x, sq_nonneg (‖U x‖ - ‖x‖)]

lemma Unitary.injective {U : H →L[ℂ] H} (hU : Unitary U) : Function.Injective U := by
  intro x y hxy
  have : ‖U x - U y‖ = 0 := by simp [hxy]
  rw [← map_sub, hU.norm_map] at this
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

lemma Unitary.surjective {U : H →L[ℂ] H} (hU : Unitary U) : Function.Surjective U := by
  intro y
  use U.adjoint y
  have := congr_arg (· y) hU.2
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
  exact this

lemma Unitary.isUnit {U : H →L[ℂ] H} (hU : Unitary U) : IsUnit U :=
  ⟨⟨U, U.adjoint, hU.2, hU.1⟩, rfl⟩

/-- The Cayley transform of a self-adjoint generator. -/
noncomputable def cayleyTransform {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - (2 * I) • Resolvent.resolvent_at_neg_i gen hsa

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
    set U := cayleyTransform gen hsa with hU
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
        _ = -(gen.op ⟨ψ, hψ_mem⟩ + I • ψ) := by rw [← hψ_eq]; exact rfl
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

theorem inverse_cayley_relation {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    let U := cayleyTransform gen hsa
    (2 * I) • gen.op ⟨ψ, hψ⟩ = I • ((ContinuousLinearMap.id ℂ H + U) φ) := by

  have h_plus := one_plus_cayley_apply gen hsa ψ hψ
  simp only [h_plus, smul_smul]
  ring_nf


theorem inverse_cayley_formula {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    let U := cayleyTransform gen hsa
    (ContinuousLinearMap.id ℂ H - U) φ = (2 * I) • ψ ∧
    (ContinuousLinearMap.id ℂ H + U) φ = (2 : ℂ) • gen.op ⟨ψ, hψ⟩ := by
  exact ⟨one_minus_cayley_apply gen hsa ψ hψ, one_plus_cayley_apply gen hsa ψ hψ⟩

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
  have h_inv : ((-I) / 2) • ((2 * I) • ψ) = ψ := by
    rw [smul_smul]
    have : (-I) / 2 * (2 * I) = 1 := by
      field_simp
      simp_all only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
                     Pi.sub_apply, id_eq, map_add, map_smul, I_sq, neg_neg]
    rw [this, one_smul]
  rw [← h_minus] at h_inv
  exact h_inv.symm


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



noncomputable def inverseCayleyOp (U : H →L[ℂ] H)
    (_ /-hU-/ : ∀ ψ φ, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ)
    (h_one : ∀ ψ, U ψ = ψ → ψ = 0)
    (_ /-h_neg_one-/ : ∀ ψ, U ψ = -ψ → ψ = 0) :
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


lemma cayleyTransform_comp_adjoint {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (cayleyTransform gen hsa).comp (cayleyTransform gen hsa).adjoint =
    ContinuousLinearMap.id ℂ H := by
  have hU := cayleyTransform_unitary gen hsa
  exact hU.2

lemma cayleyTransform_adjoint_comp {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (cayleyTransform gen hsa).adjoint.comp (cayleyTransform gen hsa) =
    ContinuousLinearMap.id ℂ H := by
  have hU := cayleyTransform_unitary gen hsa
  exact hU.1

lemma cayleyTransform_isUnit {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    IsUnit (cayleyTransform gen hsa) := by
  refine ⟨⟨cayleyTransform gen hsa, (cayleyTransform gen hsa).adjoint, ?_, ?_⟩, rfl⟩
  · exact cayleyTransform_comp_adjoint gen hsa
  · exact cayleyTransform_adjoint_comp gen hsa

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
  · -- Bound on ‖wU*‖
    have h_adj_norm : ‖w • U.adjoint‖ < 1 := by
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
  · -- First, w ≠ 0 (since |w| > 1 > 0)
    have hw_ne : w ≠ 0 := fun h => by
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


lemma dense_range_of_orthogonal_trivial {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : F →L[ℂ] F)
    (h : ∀ y, (∀ x, ⟪T x, y⟫_ℂ = 0) → y = 0) :
    Dense (Set.range T) := by

  have h_orth : (LinearMap.range T.toLinearMap)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    apply h y
    intro x
    rw [Submodule.mem_orthogonal'] at hy
    simp_all only [LinearMap.mem_range, ContinuousLinearMap.coe_coe,
                   forall_exists_index, forall_apply_eq_imp_iff]
    exact inner_eq_zero_symm.mp (hy x)
  have h_double_orth : (LinearMap.range T.toLinearMap)ᗮᗮ = ⊤ := by
    rw [h_orth]
    exact Submodule.bot_orthogonal_eq_top
  have h_closure_top : (LinearMap.range T.toLinearMap).topologicalClosure = ⊤ := by
    rw [h_double_orth.symm]
    rw [@Submodule.orthogonal_orthogonal_eq_closure]
  rw [dense_iff_closure_eq]
  have : closure (Set.range T) = ↑(LinearMap.range T.toLinearMap).topologicalClosure := by
    rw [Submodule.topologicalClosure_coe]
    rfl
  rw [this, h_closure_top]
  rfl

lemma unitary_sub_scalar_isNormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] E) (hU : U.adjoint * U = 1 ∧ U * U.adjoint = 1) (w : ℂ) :
    (U - w • 1).adjoint * (U - w • 1) = (U - w • 1) * (U - w • 1).adjoint := by

  have h_adj : (U - w • 1).adjoint = U.adjoint - (starRingEnd ℂ w) • 1 := by
    ext x
    apply ext_inner_right ℂ
    intro y
    simp only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.sub_apply,
               ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
               inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    simp_all only [RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [h_adj]
  ext x
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
             ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  have h1 : U.adjoint (U x) = x := by
    have := congr_arg (· x) hU.1
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    exact this
  have h2 : U (U.adjoint x) = x := by
    have := congr_arg (· x) hU.2
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    exact this
  simp only [map_sub, map_smul, h1, h2]
  module

lemma surjective_of_isClosed_range_of_dense {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F)
    (hClosed : IsClosed (Set.range T))
    (hDense : Dense (Set.range T)) :
    Function.Surjective T := by
  intro y
  have h_closure : closure (Set.range T) = Set.range T := hClosed.closure_eq
  have h_univ : closure (Set.range T) = Set.univ := hDense.closure_eq
  rw [h_closure] at h_univ
  have hy : y ∈ Set.range T := by rw [h_univ]; trivial
  exact hy

/-- Real eigenvalues of `A` correspond to eigenvalues of `U` via the Möbius map. -/
theorem cayley_eigenvalue_correspondence {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) (μ : ℝ) :
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
      exact rfl

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
      exact rfl



variable (μ : ℝ)

lemma real_add_I_ne_zero : (↑μ : ℂ) + I ≠ 0 := by
  intro h
  have : ((↑μ : ℂ) + I).im = 0 := by rw [h]; simp
  simp at this


lemma mobius_norm_one (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(↑μ - I) * (↑μ + I)⁻¹‖ = 1 := by
  simp only [norm_mul, norm_inv]
  have h1 : ‖(↑μ : ℂ) - I‖ = ‖(↑μ : ℂ) + I‖ := by
    have h : starRingEnd ℂ ((↑μ : ℂ) + I) = (↑μ : ℂ) - I := by simp [Complex.ext_iff]
    rw [← h, RCLike.norm_conj]
  have h2 : ‖(↑μ : ℂ) + I‖ ≠ 0 := norm_ne_zero_iff.mpr hμ_ne
  field_simp [h2, h1]
  exact h1

lemma one_sub_mobius (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹ = 2 * I / (↑μ + I) := by
  field_simp [hμ_ne]
  ring

lemma one_add_mobius (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) + (↑μ - I) * (↑μ + I)⁻¹ = 2 * ↑μ / (↑μ + I) := by
  field_simp [hμ_ne]
  ring

lemma mobius_coeff_identity (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    let w := (↑μ - I) * (↑μ + I)⁻¹
    I * ((1 : ℂ) + w) = ((1 : ℂ) - w) * ↑μ := by
  simp only
  rw [one_sub_mobius μ hμ_ne, one_add_mobius μ hμ_ne]
  field_simp [hμ_ne]

lemma one_sub_mobius_ne_zero (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹ ≠ 0 := by
  rw [one_sub_mobius μ hμ_ne]
  simp [hμ_ne]

lemma one_sub_mobius_norm_pos (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹‖ > 0 :=
  norm_pos_iff.mpr (one_sub_mobius_ne_zero μ hμ_ne)

lemma cayleyTransform_apply_resolvent {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    cayleyTransform gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = gen.op ⟨ψ, hψ⟩ - I • ψ := by
  simp only [cayleyTransform, ContinuousLinearMap.sub_apply,
             ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
  have h_res := Resolvent.resolvent_at_neg_i_left_inverse gen hsa ψ hψ
  rw [h_res]
  module

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


lemma cayley_shift_injective {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0)
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


lemma self_adjoint_norm_sq_add {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (_ /-hsa-/ : Generator.IsSelfAdjoint gen)
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

lemma mobius_norm_eq_one (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(↑μ - I) * (↑μ + I)⁻¹‖ = 1 := by
  exact mobius_norm_one μ hμ_ne


def ContinuousLinearMap.IsNormal (T : H →L[ℂ] H) : Prop :=
  T.adjoint.comp T = T.comp T.adjoint


lemma unitary_sub_scalar_isNormal' {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ) :
    (U - w • 1).adjoint * (U - w • 1) = (U - w • 1) * (U - w • 1).adjoint := by

  have h_adj : (U - w • 1).adjoint = U.adjoint - (starRingEnd ℂ w) • 1 := by
    ext x
    apply ext_inner_right ℂ
    intro y
    simp only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.sub_apply,
               ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
               inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    simp_all only [RingHomCompTriple.comp_apply, RingHom.id_apply]

  rw [h_adj]
  ext x
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
             ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]

  have h1 : U.adjoint (U x) = x := by
    have := congr_arg (· x) hU.1
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    exact this

  have h2 : U (U.adjoint x) = x := by
    have := congr_arg (· x) hU.2
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    exact this

  simp only [map_sub, map_smul, h1, h2]
  module


lemma isUnit_bounded_below [Nontrivial H] {T : H →L[ℂ] H} (hT : IsUnit T) :
    ∃ c > 0, ∀ φ, ‖T φ‖ ≥ c * ‖φ‖ := by
  obtain ⟨⟨T, T_inv, hT_left, hT_right⟩, rfl⟩ := hT
  have hT_inv_ne : T_inv ≠ 0 := by
    intro h
    have h_one_eq : (1 : H →L[ℂ] H) = 0 := by
      calc (1 : H →L[ℂ] H) = T_inv * T := hT_right.symm
        _ = 0 * T := by rw [h]
        _ = 0 := zero_mul T
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have : x = 0 := by simpa using congr_arg (· x) h_one_eq
    exact hx this

  have hT_inv_norm_pos : ‖T_inv‖ > 0 := norm_pos_iff.mpr hT_inv_ne
  use ‖T_inv‖⁻¹, inv_pos.mpr hT_inv_norm_pos

  intro φ
  have h_eq : T_inv (T φ) = φ := by
    have := congr_arg (· φ) hT_right
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    exact this
  have h_bound : ‖φ‖ ≤ ‖T_inv‖ * ‖T φ‖ := by
    calc ‖φ‖ = ‖T_inv (T φ)‖ := by rw [h_eq]
      _ ≤ ‖T_inv‖ * ‖T φ‖ := ContinuousLinearMap.le_opNorm T_inv (T φ)
  exact (inv_mul_le_iff₀ hT_inv_norm_pos).mpr h_bound


lemma normal_bounded_below_surjective {T : H →L[ℂ] H}
    (hT : T.adjoint.comp T = T.comp T.adjoint)
    (c : ℝ) (hc_pos : c > 0) (hc_bound : ∀ φ, ‖T φ‖ ≥ c * ‖φ‖) :
    Function.Surjective T := by

  have h_range_dense : Dense (Set.range T) := by
    apply dense_range_of_orthogonal_trivial
    intro y hy

    have hT_adj_y : T.adjoint y = 0 := by
      apply ext_inner_left ℂ
      intro x
      rw [inner_zero_right, ContinuousLinearMap.adjoint_inner_right]
      exact hy x

    have h_norm_eq : ‖T.adjoint y‖ = ‖T y‖ := by
      have h1 : ⟪T.adjoint (T y), y⟫_ℂ = ⟪T (T.adjoint y), y⟫_ℂ := by
        calc ⟪T.adjoint (T y), y⟫_ℂ
            = ⟪(T.adjoint.comp T) y, y⟫_ℂ := rfl
          _ = ⟪(T.comp T.adjoint) y, y⟫_ℂ := by rw [hT]
          _ = ⟪T (T.adjoint y), y⟫_ℂ := rfl
      have h2 : ‖T.adjoint y‖^2 = (⟪T (T.adjoint y), y⟫_ℂ).re := by
        have h := ContinuousLinearMap.adjoint_inner_right T (T.adjoint y) y
        have h_inner : (⟪T.adjoint y, T.adjoint y⟫_ℂ).re = ‖T.adjoint y‖^2 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
          simp only [coe_algebraMap]
          rw [← ofReal_pow]
          exact Complex.ofReal_re _
        linarith [h_inner, congrArg Complex.re h]
      have h3 : ‖T y‖^2 = (⟪T.adjoint (T y), y⟫_ℂ).re := by
        have h := ContinuousLinearMap.adjoint_inner_left T (T y) y
        have h_inner : (⟪T y, T y⟫_ℂ).re = ‖T y‖^2 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
          simp only [coe_algebraMap]
          rw [← ofReal_pow]
          exact Complex.ofReal_re _
        have h_adj : ⟪T.adjoint (T y), y⟫_ℂ = ⟪T y, T y⟫_ℂ := by
          rw [ContinuousLinearMap.adjoint_inner_left]
        rw [h_adj]
        exact h_inner.symm
      have h_sq : ‖T.adjoint y‖^2 = ‖T y‖^2 := by rw [h2, h3, h1]
      nlinarith [norm_nonneg (T.adjoint y), norm_nonneg (T y),
                 sq_nonneg (‖T.adjoint y‖ - ‖T y‖)]

    rw [hT_adj_y, norm_zero] at h_norm_eq
    have h_Ty_zero : ‖T y‖ = 0 := by rw [← h_norm_eq]

    have h := hc_bound y
    rw [h_Ty_zero] at h
    have hy_norm_zero : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
    exact norm_eq_zero.mp hy_norm_zero

  have h_range_closed : IsClosed (Set.range T) := by
    rw [← isSeqClosed_iff_isClosed]
    intro xseq x hxseq hx_lim
    choose yseq hyseq using hxseq

    have h_cauchy : CauchySeq yseq := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      have hx_cauchy := hx_lim.cauchySeq
      rw [Metric.cauchySeq_iff'] at hx_cauchy
      obtain ⟨N, hN⟩ := hx_cauchy (c * ε) (by positivity)
      use N
      intro n hn
      have h_bound := hc_bound (yseq n - yseq N)
      rw [map_sub] at h_bound
      have h_xdist : ‖xseq n - xseq N‖ < c * ε := by
        rw [← dist_eq_norm]
        exact hN n hn
      have h_ydist : c * ‖yseq n - yseq N‖ ≤ ‖T (yseq n) - T (yseq N)‖ := h_bound
      rw [hyseq n, hyseq N] at h_ydist
      calc dist (yseq n) (yseq N)
          = ‖yseq n - yseq N‖ := dist_eq_norm _ _
        _ ≤ ‖xseq n - xseq N‖ / c := by
            have : c * ‖yseq n - yseq N‖ ≤ ‖xseq n - xseq N‖ := h_ydist
            exact (le_div_iff₀' hc_pos).mpr h_ydist
        _ < (c * ε) / c := by apply div_lt_div_of_pos_right h_xdist hc_pos
        _ = ε := by field_simp

    obtain ⟨y', hy'_lim⟩ := cauchySeq_tendsto_of_complete h_cauchy

    have hTy' : T y' = x := by
      have hT_cont := T.continuous.tendsto y'
      have hTyseq_lim : Tendsto (fun n => T (yseq n)) atTop (𝓝 (T y')) := hT_cont.comp hy'_lim
      have hTyseq_eq : ∀ n, T (yseq n) = xseq n := hyseq
      simp_rw [hTyseq_eq] at hTyseq_lim
      exact tendsto_nhds_unique hTyseq_lim hx_lim

    exact ⟨y', hTy'⟩
  exact surjective_of_isClosed_range_of_dense T h_range_closed h_range_dense

lemma normal_bounded_below_isUnit [Nontrivial H] {T : H →L[ℂ] H}
    (hT : T.adjoint * T = T * T.adjoint)
    (c : ℝ) (hc_pos : c > 0) (hc_bound : ∀ φ, ‖T φ‖ ≥ c * ‖φ‖) :
    IsUnit T := by

  have h_inj : Function.Injective T := by
    intro x y hxy
    have : ‖T (x - y)‖ = 0 := by simp [hxy]
    have h := hc_bound (x - y)
    rw [this] at h
    have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)

  have h_surj := normal_bounded_below_surjective hT c hc_pos hc_bound

  have h_ker : LinearMap.ker T = ⊥ := LinearMap.ker_eq_bot.mpr h_inj
  have h_range : LinearMap.range T = ⊤ := LinearMap.range_eq_top.mpr h_surj
  let e := ContinuousLinearEquiv.ofBijective T h_ker h_range
  exact ⟨⟨T, e.symm.toContinuousLinearMap,
         by ext x;
            simp only [ContinuousLinearMap.coe_mul, ContinuousLinearEquiv.coe_coe,
              Function.comp_apply, ContinuousLinearMap.one_apply]
            exact ContinuousLinearEquiv.ofBijective_apply_symm_apply T h_ker h_range x,
         by ext x;
            simp only [ContinuousLinearMap.coe_mul, ContinuousLinearEquiv.coe_coe,
              Function.comp_apply, ContinuousLinearMap.one_apply]
            exact ContinuousLinearEquiv.ofBijective_symm_apply_apply T h_ker h_range x⟩,
            rfl⟩


lemma unitary_not_isUnit_approx_eigenvalue [Nontrivial H] {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ)
    (h_not : ¬IsUnit (U - w • ContinuousLinearMap.id ℂ H)) :
    ∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧ ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ < ε := by

  by_contra h_neg
  push_neg at h_neg

  obtain ⟨ε, hε_pos, hε_bound⟩ := h_neg

  have h_bounded_below : ∀ φ, ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ ≥ ε * ‖φ‖ := by
    intro φ
    by_cases hφ : φ = 0
    · simp [hφ]
    · have hφ_norm_pos : ‖φ‖ > 0 := norm_pos_iff.mpr hφ
      have h_unit := hε_bound (‖φ‖⁻¹ • φ) (by rw [norm_smul, norm_inv, norm_norm]; field_simp)
      calc ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖
          = ‖φ‖ * (‖φ‖⁻¹ * ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖) := by field_simp
        _ = ‖φ‖ * ‖‖φ‖⁻¹ • (U - w • ContinuousLinearMap.id ℂ H) φ‖ := by
            congr 1; rw [norm_smul, norm_inv, norm_norm]
        _ = ‖φ‖ * ‖(U - w • ContinuousLinearMap.id ℂ H) (‖φ‖⁻¹ • φ)‖ := by
            congr 1; simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_smul',
              ContinuousLinearMap.coe_id', Pi.sub_apply, Pi.smul_apply, id_eq,
              ContinuousLinearMap.map_smul_of_tower]
        _ ≥ ‖φ‖ * ε := mul_le_mul_of_nonneg_left h_unit (norm_nonneg φ)
        _ = ε * ‖φ‖ := mul_comm _ _

  have h_normal := unitary_sub_scalar_isNormal' hU w

  have h_isUnit := normal_bounded_below_isUnit h_normal ε hε_pos h_bounded_below

  exact h_not h_isUnit


lemma unitary_not_approx_eigenvalue_isUnit [Nontrivial H] {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ)
    (h_not : ¬∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧ ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ < ε) :
    IsUnit (U - w • ContinuousLinearMap.id ℂ H) := by
  push_neg at h_not

  obtain ⟨ε, hε_pos, hε_bound⟩ := h_not

  have h_bounded_below : ∀ φ, ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ ≥ ε * ‖φ‖ := by
    intro φ
    by_cases hφ : φ = 0
    · simp [hφ]
    · have hφ_norm_pos : ‖φ‖ > 0 := norm_pos_iff.mpr hφ
      have h_unit := hε_bound (‖φ‖⁻¹ • φ) (by rw [norm_smul, norm_inv, norm_norm]; field_simp)
      calc ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖
          = ‖φ‖ * (‖φ‖⁻¹ * ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖) := by field_simp
        _ = ‖φ‖ * ‖‖φ‖⁻¹ • (U - w • ContinuousLinearMap.id ℂ H) φ‖ := by
            congr 1; rw [norm_smul, norm_inv, norm_norm]
        _ = ‖φ‖ * ‖(U - w • ContinuousLinearMap.id ℂ H) (‖φ‖⁻¹ • φ)‖ := by
            congr 1; simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_smul',
              ContinuousLinearMap.coe_id', Pi.sub_apply, Pi.smul_apply, id_eq,
              ContinuousLinearMap.map_smul_of_tower]
        _ ≥ ‖φ‖ * ε := mul_le_mul_of_nonneg_left h_unit (norm_nonneg φ)
        _ = ε * ‖φ‖ := mul_comm _ _

  have h_normal := unitary_sub_scalar_isNormal' hU w

  exact normal_bounded_below_isUnit h_normal ε hε_pos h_bounded_below


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
      · -- Need: (1 + μ^2) * (x - t_minus) > 0
        apply mul_pos h_coeff_pos
        linarith [htminus_neg]
      · -- Need: x - t_plus < 0
        linarith [h_lt]
    linarith [h_ineq, h_neg]

  calc ‖ψ‖ = x := rfl
    _ ≥ t_plus := h_x_ge_t_plus
    _ = (Real.sqrt (1 + μ^2 - δ^2) - |μ| * δ) / (1 + μ^2) := htplus_def


set_option maxHeartbeats 300000


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
        · -- Case μ = 0: the term is 0 < 1/4
          simp [hμ_zero]
        · -- Case μ ≠ 0
          have hμ_pos : |μ| > 0 := abs_pos.mpr hμ_zero
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
  · -- ‖φ‖ = 1
    rw [hφ_def, norm_smul, norm_inv, norm_norm]
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

/-- Spectral correspondence: bounded below for `A - μ` iff `U - w` is invertible. -/
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

/-- The domain of `A` equals the range of `I - U`. -/
theorem generator_domain_eq_range_one_minus_cayley {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (gen.domain : Set H) = LinearMap.range (ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa) := by
  set U := cayleyTransform gen hsa with hU_def
  ext ψ
  constructor

  · intro hψ
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ

    -- Compute Uφ = (A - iI)ψ
    have h_Uφ : U φ = gen.op ⟨ψ, hψ⟩ - I • ψ := by
      simp only [U, cayleyTransform, ContinuousLinearMap.sub_apply,
                 ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
      have h_res : Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = ψ :=
        Resolvent.resolvent_at_neg_i_left_inverse gen hsa ψ hψ
      rw [h_res]
      module

    -- (I - U)φ = φ - Uφ = (A+iI)ψ - (A-iI)ψ = 2iψ
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

def cayleyImage (B : Set ℝ) : Set ℂ :=
  {w : ℂ | ∃ μ ∈ B, w = (↑μ - I) * (↑μ + I)⁻¹}

noncomputable def spectralMeasure_from_unitary
    (E_U : Set ℂ → (H →L[ℂ] H)) : Set ℝ → (H →L[ℂ] H) :=
  fun B => E_U (cayleyImage B)

def SpectralMeasuresCompatible {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E_A : Set ℝ → (H →L[ℂ] H)) (E_U : Set ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ B : Set ℝ, E_A B = E_U (cayleyImage B)

axiom exists_compatible_spectral_measures {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    ∃ (E_A : Set ℝ → (H →L[ℂ] H)) (E_U : Set ℂ → (H →L[ℂ] H)),
      SpectralMeasuresCompatible gen hsa E_A E_U

theorem spectralMeasure_cayley_correspondence {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E_A : Set ℝ → (H →L[ℂ] H)) (E_U : Set ℂ → (H →L[ℂ] H))
    (hcompat : SpectralMeasuresCompatible gen hsa E_A E_U)
    (B : Set ℝ) :
    E_A B = E_U (cayleyImage B) := hcompat B

end QuantumMechanics.Cayley
