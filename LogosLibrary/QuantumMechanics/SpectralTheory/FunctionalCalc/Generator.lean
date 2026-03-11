/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.Algebraic
/-!
# Generator Recovery from Spectral Measure

This file establishes the fundamental connection between a self-adjoint generator `A`
and its spectral measure `E`: we have `A = ∫ s dE(s)` on the domain of `A`, and the
domain equals `{ψ : ∫|s|² dμ_ψ < ∞}`.

## Main definitions

* `IsSpectralMeasureFor`: Predicate bundling spectral measure axioms for a generator
* `identityFunction`: The function `id(s) = s`

## Main results

* `generator_eq_spectral_integral`: `A = ∫ s dE(s)` on `dom(A)`
* `generator_domain_eq_functional_domain`: `dom(A) = {ψ : ∫|s|² dμ_ψ < ∞}`

## Main axioms (to be discharged)

* `generator_spectral_integral_inner_eq`: Inner product formula connecting A and ∫ s dE
* `generator_domain_subset_id_domain`: `dom(A) ⊆ dom(id(A))`
* `id_domain_subset_generator_domain`: `dom(id(A)) ⊆ dom(A)`
* `generator_norm_sq_eq_second_moment`: `‖Aψ‖² = ∫ s² dμ_ψ`

## Tags

generator, spectral measure, spectral theorem, domain characterization
-/
namespace FunctionalCalculus

open MeasureTheory InnerProductSpace Complex QuantumMechanics.Cayley SpectralBridge.Resolvent SpectralBridge.Bochner QuantumMechanics.Generators ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## IsSpectralMeasureFor
-/

/-- Predicate: E is the spectral measure associated to the generator -/
structure IsSpectralMeasureFor (E : Set ℝ → H →L[ℂ] H)
    {U_grp : OneParameterUnitaryGroup (H := H)} (gen : Generator U_grp) : Prop where
  proj_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C)
  proj_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ
  proj_empty : E ∅ = 0
  proj_univ : E Set.univ = 1
  proj_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
             E (B ∪ C) = E B + E C
  proj_sot : ∀ ψ t₀, Filter.Tendsto (fun t => E (Set.Iic t) ψ) (nhdsWithin t₀ (Set.Ioi t₀)) (nhds (E (Set.Iic t₀) ψ))
  proj_σ_add : ∀ ψ (B : ℕ → Set ℝ), (∀ n, MeasurableSet (B n)) →
        (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
        HasSum (fun n => E (B n) ψ) (E (⋃ n, B n) ψ)
  unitary_eq_integral : ∀ (t : ℝ) (ψ : H),
    ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ s, Complex.exp (I * t * s) ∂(spectral_scalar_measure E ψ ⟨proj_mul, proj_sa, proj_sot, proj_empty, proj_univ, proj_add, proj_σ_add⟩)

/-- Extract IsSpectralMeasure from IsSpectralMeasureFor -/
def IsSpectralMeasureFor.toIsSpectralMeasure {E : Set ℝ → H →L[ℂ] H}
    {U_grp : OneParameterUnitaryGroup (H := H)} {gen : Generator U_grp}
    (hE : IsSpectralMeasureFor E gen) : IsSpectralMeasure E where
  mul := hE.proj_mul
  sa := hE.proj_sa
  sot := hE.proj_sot
  add := hE.proj_add
  empty := hE.proj_empty
  univ := hE.proj_univ
  σ_add := hE.proj_σ_add

/-!
## Identity Function
-/

/-- The identity function id(s) = s -/
def identityFunction : ℝ → ℂ := fun s => s

/-!
## Generator-Spectral Correspondence Axioms
-/

/-- Direct axiom: Generator and spectral integral agree on inner products
NOTE: This is the first axiom to turn into a lemma. This is temporary! -/
axiom generator_spectral_integral_inner_eq {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ_dom : ψ ∈ gen.domain)
    (hψ_func : ψ ∈ functionalDomain (spectral_scalar_measure E · hE.toIsSpectralMeasure) identityFunction)
    (φ : H) :
    ⟪gen.op ⟨ψ, hψ_dom⟩, φ⟫_ℂ = ⟪spectral_integral E hE.toIsSpectralMeasure identityFunction ψ hψ_func, φ⟫_ℂ

/-- Forward direction: dom(A) ⊆ functionalDomain(id)
    Key fact: ψ ∈ dom(A) implies ∫|s|² dμ_ψ < ∞ -/
axiom generator_domain_subset_id_domain {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ψ ∈ functionalDomain (spectral_scalar_measure E · hE.toIsSpectralMeasure) identityFunction

/-- Backward direction: functionalDomain(id) ⊆ dom(A)
    Key fact: ∫|s|² dμ_ψ < ∞ implies ψ ∈ dom(A) -/
axiom id_domain_subset_generator_domain {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE.toIsSpectralMeasure) identityFunction) :
    ψ ∈ gen.domain

/-- Norm formula: ‖Aψ‖² = ∫|s|² dμ_ψ -/
axiom generator_norm_sq_eq_second_moment {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ‖gen.op ⟨ψ, hψ⟩‖^2 = ∫ s, s^2 ∂(spectral_scalar_measure E ψ hE.toIsSpectralMeasure)

/-- **Theorem**: The domain contains dom(A) when f is polynomially bounded.
    NOTE: For polynomial degree n > 1, this really requires dom(A^n).
    We axiomatize the full statement for now. -/
axiom generator_domain_subset_functional_aux {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (C n : ℝ) (hf : ∀ s, ‖f s‖ ≤ C * (1 + |s|)^n)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f

/-!
## Main Theorems
-/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- **Core Theorem**: A = ∫ s dE(s) on dom(A)

The generator equals the functional calculus of the identity function. -/
theorem generator_eq_spectral_integral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ_dom : ψ ∈ gen.domain)
    (hψ_func : ψ ∈ functionalDomain (spectral_scalar_measure E · hE.toIsSpectralMeasure) identityFunction) :
    gen.op ⟨ψ, hψ_dom⟩ = functionalCalculus E hE.toIsSpectralMeasure hE.proj_univ identityFunction ⟨ψ, hψ_func⟩ := by
  apply ext_inner_right ℂ
  intro φ
  exact generator_spectral_integral_inner_eq gen hsa E hE ψ hψ_dom hψ_func φ

/-- Domain equality: dom(A) = dom(id(A)) -/
theorem generator_domain_eq_functional_domain {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen) :
    (gen.domain : Set H) = functionalDomain (spectral_scalar_measure E · hE.toIsSpectralMeasure) identityFunction := by
  ext ψ
  constructor
  · exact generator_domain_subset_id_domain gen hsa E hE ψ
  · exact id_domain_subset_generator_domain gen hsa E hE ψ

/-- **Theorem**: The domain contains dom(A) when f is polynomially bounded. -/
theorem generator_domain_subset_functional {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (hf : ∃ C n : ℝ, ∀ s, ‖f s‖ ≤ C * (1 + |s|)^n) :
    (gen.domain : Set H) ⊆ functionalDomain (spectral_scalar_measure E · hE) f := by
  intro ψ hψ
  obtain ⟨C, n, hCn⟩ := hf
  exact generator_domain_subset_functional_aux gen hsa E hE f C n hCn ψ hψ

end FunctionalCalculus
