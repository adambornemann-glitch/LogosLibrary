/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Bochner/Resolvent.lean
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner.Basic
import LogosLibrary.QuantumMechanics.UnitaryEvo.Generator

/-!
# Resolvent Integrals for Unitary Groups

This file defines the resolvent integrals used in Stone's theorem:
* `R₊(φ) = (-i) ∫₀^∞ e^{-t} U(t)φ dt`
* `R₋(φ) = i ∫₀^∞ e^{-t} U(-t)φ dt`

These solve `(A + iI)ψ = φ` and `(A - iI)ψ = φ` respectively, which establishes
surjectivity of `A ± iI` and hence self-adjointness of the generator.

## Main definitions

* `resolventIntegralPlus`: the integral `(-i) ∫₀^∞ e^{-t} U(t)φ dt`
* `resolventIntegralMinus`: the integral `i ∫₀^∞ e^{-t} U(-t)φ dt`

## Main results

* `integrable_exp_neg_unitary`: `e^{-t} • U(t)φ` is integrable on `[0, ∞)`
* `norm_resolventIntegralPlus_le`: `‖R₊(φ)‖ ≤ ‖φ‖`
* `norm_resolventIntegralMinus_le`: `‖R₋(φ)‖ ≤ ‖φ‖`

## Tags

resolvent, unitary group, Laplace transform
-/

namespace QuantumMechanics.Bochner

open MeasureTheory Measure Filter Topology Complex QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


section UnitaryGroupIntegration

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

lemma continuous_unitary_apply (φ : H) :
    Continuous (fun t => U_grp.U t φ) :=
  U_grp.strong_continuous φ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

lemma integrable_exp_neg_unitary (φ : H) :
    IntegrableOn (fun t => Real.exp (-t) • U_grp.U t φ) (Set.Ici 0) volume := by
  apply integrable_exp_decay_continuous
    (fun t => U_grp.U t φ)
    (U_grp.strong_continuous φ)
    ‖φ‖
  intro t _ht
  exact le_of_eq (norm_preserving U_grp t φ)

lemma integrable_exp_neg_unitary_neg (φ : H) :
    IntegrableOn (fun t => Real.exp (-t) • U_grp.U (-t) φ) (Set.Ici 0) volume := by
  apply integrable_exp_decay_continuous
    (fun t => U_grp.U (-t) φ)
    ((U_grp.strong_continuous φ).comp continuous_neg)
    ‖φ‖
  intro t _ht
  exact le_of_eq (norm_preserving U_grp (-t) φ)

lemma norm_integral_exp_neg_unitary_le (φ : H) :
    ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ ≤ ‖φ‖ := by
  apply norm_integral_exp_decay_le
    (fun t => U_grp.U t φ)
    (U_grp.strong_continuous φ)
    ‖φ‖
  · intro t _ht
    exact le_of_eq (norm_preserving U_grp t φ)
  · exact norm_nonneg φ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

lemma integrable_unitary_Ioc (φ : H) (h : ℝ) (_ : 0 < h) :
    IntegrableOn (fun t => U_grp.U t φ) (Set.Ioc 0 h) volume := by
  exact (U_grp.strong_continuous φ).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

end UnitaryGroupIntegration

section ResolventIntegrals

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The resolvent integral `R₊(φ) = (-i) ∫₀^∞ e^{-t} U(t)φ dt`.
    This solves `(A + iI)ψ = φ` where `A` is the generator. -/
noncomputable def resolventIntegralPlus (φ : H) : H :=
  (-I) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ

/-- The resolvent integral `R₋(φ) = i ∫₀^∞ e^{-t} U(-t)φ dt`.
    This solves `(A - iI)ψ = φ` where `A` is the generator. -/
noncomputable def resolventIntegralMinus (φ : H) : H :=
  I • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ

lemma resolventIntegralPlus_add (φ₁ φ₂ : H) :
    resolventIntegralPlus U_grp (φ₁ + φ₂) =
    resolventIntegralPlus U_grp φ₁ + resolventIntegralPlus U_grp φ₂ := by
  unfold resolventIntegralPlus
  have h_int₁ := integrable_exp_neg_unitary U_grp φ₁
  have h_int₂ := integrable_exp_neg_unitary U_grp φ₂
  have h_eq : (fun t => Real.exp (-t) • U_grp.U t (φ₁ + φ₂)) =
              (fun t => Real.exp (-t) • U_grp.U t φ₁ + Real.exp (-t) • U_grp.U t φ₂) := by
    ext t
    rw [map_add, smul_add]
  rw [h_eq, integral_add h_int₁ h_int₂, DistribMulAction.smul_add]

lemma norm_resolventIntegralPlus_le (φ : H) :
    ‖resolventIntegralPlus U_grp φ‖ ≤ ‖φ‖ := by
  unfold resolventIntegralPlus
  calc ‖(-I) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖
      = ‖-I‖ * ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ := norm_smul (-I) _
    _ = 1 * ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ := by simp only [norm_neg, norm_I]
    _ = ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ := one_mul _
    _ ≤ ‖φ‖ := norm_integral_exp_neg_unitary_le U_grp φ

lemma norm_resolventIntegralMinus_le (φ : H) :
    ‖resolventIntegralMinus U_grp φ‖ ≤ ‖φ‖ := by
  unfold resolventIntegralMinus
  have h_bound : ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖ ≤ ‖φ‖ := by
    apply norm_integral_exp_decay_le
      (fun t => U_grp.U (-t) φ)
      ((U_grp.strong_continuous φ).comp continuous_neg)
      ‖φ‖
    · intro t _ht
      exact le_of_eq (norm_preserving U_grp (-t) φ)
    · exact norm_nonneg φ
  calc ‖I • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖
      = ‖I‖ * ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖ := norm_smul I _
    _ = 1 * ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖ := by simp only [norm_I, one_mul]
    _ = ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖ := one_mul _
    _ ≤ ‖φ‖ := h_bound

end ResolventIntegrals

end QuantumMechanics.Bochner
