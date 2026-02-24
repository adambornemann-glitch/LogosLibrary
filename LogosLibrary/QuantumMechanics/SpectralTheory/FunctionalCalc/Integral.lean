/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.Domain
/-!
# Spectral Integral

This file defines the spectral integral `∫ f(s) dE(s)` and establishes its
fundamental properties.

## Main definitions

* `spectral_integral_bounded`: `f(A)` for bounded Borel functions
* `spectral_integral`: `f(A)` for general measurable functions on domain

## Main axioms (to be discharged)

* `spectral_integral_bounded`: Construction for bounded functions
* `spectral_integral`: Construction for general functions
* `spectral_integral_inner_cross`: Inner product formula
* `spectral_integral_add`: Additivity in f
* `spectral_integral_smul`: Homogeneity in f
* `spectral_integral_mul`: Multiplicativity
* `spectral_integral_conj`: Adjoint property

## Main theorems

* `spectral_integral_indicator`: `Φ(𝟙_B) = E(B)`
* `spectral_integral_one`: `Φ(1) = I`

## Tags

spectral integral, functional calculus
-/

namespace FunctionalCalculus

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory InnerProductSpace Complex QuantumMechanics.Cayley SpectralBridge.Resolvent SpectralBridge.Bochner QuantumMechanics.Generators ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## Spectral Integral Axioms
-/

/-- **Axiom**: The spectral integral exists for bounded Borel functions and
    yields a bounded linear operator `H →L[ℂ] H`. Construction via simple
    function approximation and uniform convergence. -/
axiom spectral_integral_bounded (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) : H →L[ℂ] H

/-- **Axiom**: The spectral integral exists for general measurable functions
    on the functional domain `{ψ : ∫|f|² dμ_ψ < ∞}`. Construction via L²
    approximation and the Riesz representation theorem. -/
axiom spectral_integral (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f) : H

/-- Proper spectral integral inner product formula -/
axiom spectral_integral_inner_cross (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f : ℝ → ℂ) (ψ φ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hf_meas : Measurable f) (hf_bdd : ∃ M, ∀ s, ‖f s‖ ≤ M) :
    ⟪spectral_integral E hE f ψ hψ, φ⟫_ℂ = spectral_cross_integral E hE f ψ φ

/-!
## Linearity Axioms
-/

/-- Linearity in f -/
axiom spectral_integral_add (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f g : ℝ → ℂ)
    (ψ : H)
    (hf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f + g)) :
    spectral_integral E hE (f + g) ψ hfg =
    spectral_integral E hE f ψ hf + spectral_integral E hE g ψ hg

/-- **Axiom**: The spectral integral is homogeneous in the function argument:
    `Φ(c · f) = c · Φ(f)`. -/
axiom spectral_integral_smul (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (c : ℂ) (f : ℝ → ℂ)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hcf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (c • f)) :
    spectral_integral E hE (c • f) ψ hcf = c • spectral_integral E hE f ψ hψ

/-- Multiplicativity: Φ(fg) = Φ(f) ∘ Φ(g) -/
axiom spectral_integral_mul (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f g : ℝ → ℂ)
    (ψ : H)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g)
    (hfg : spectral_integral E hE g ψ hg ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (h_prod : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f * g)) :
    spectral_integral E hE (f * g) ψ h_prod =
    spectral_integral E hE f (spectral_integral E hE g ψ hg) hfg

/-- Adjoint property: Φ(f̄) = Φ(f)* -/
axiom spectral_integral_conj (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (ψ φ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hφ : φ ∈ functionalDomain (spectral_scalar_measure E · hE) (starRingEnd ℂ ∘ f)) :
    ⟪spectral_integral E hE f ψ hψ, φ⟫_ℂ =
    ⟪ψ, spectral_integral E hE (starRingEnd ℂ ∘ f) φ hφ⟫_ℂ

/-- Bounded functions on full domain agree with bounded version -/
axiom spectral_integral_bounded_eq (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) (ψ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    spectral_integral E hE f ψ hψ = spectral_integral_bounded E hE f hf ψ

/-!
## Vector Linearity Axioms
-/

/-- Spectral integral is additive in ψ -/
axiom spectral_integral_add_vector (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (x y : H)
    (hx : x ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hy : y ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hxy : x + y ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    spectral_integral E hE f (x + y) hxy =
    spectral_integral E hE f x hx + spectral_integral E hE f y hy

/-- Spectral integral is homogeneous in ψ -/
axiom spectral_integral_smul_vector (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (c : ℂ) (ψ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hcψ : c • ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    spectral_integral E hE f (c • ψ) hcψ = c • spectral_integral E hE f ψ hψ

/-!
## Main Theorems
-/

/-- Spectral integral of an indicator function equals the spectral projection:
    `Φ(𝟙_B) = E(B)`. Proven via the cross-integral framework and polarization. -/
theorem spectral_integral_indicator (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (B : Set ℝ) (hB : MeasurableSet B) (ψ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (Set.indicator B 1)) :
    spectral_integral E hE (Set.indicator B 1) ψ hψ = E B ψ := by
  apply ext_inner_right ℂ
  intro φ
  rw [spectral_integral_inner_cross E hE hE_univ _ ψ φ hψ
      (Measurable.indicator measurable_const hB) (indicator_bounded B)]
  rw [spectral_cross_integral_indicator E hE hE_univ B hB ψ φ]

/-- Spectral integral of the constant function `1` is the identity: `Φ(1) = I`.
    Follows from `1 = 𝟙_{ℝ}` and `E(ℝ) = I`. -/
theorem spectral_integral_one (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun _ => 1)) :
    spectral_integral E hE (fun _ => 1) ψ hψ = ψ := by
  have h_fun_eq : (fun _ : ℝ => (1 : ℂ)) = Set.indicator Set.univ 1 := by
    funext s; simp only [Set.mem_univ, Set.indicator_of_mem, Pi.one_apply]
  have eq_of_eq : ∀ (f g : ℝ → ℂ) (hfg : f = g)
      (hf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
      (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g),
      spectral_integral E hE f ψ hf = spectral_integral E hE g ψ hg := by
    intro f g hfg hf hg
    subst hfg
    rfl
  have hψ' : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (Set.indicator Set.univ 1) :=
    h_fun_eq ▸ hψ
  rw [eq_of_eq _ _ h_fun_eq hψ hψ']
  rw [spectral_integral_indicator E hE hE_univ Set.univ MeasurableSet.univ ψ hψ']
  rw [hE_univ]
  rfl

/-- Spectral integral respects function equality (with proof irrelevance) -/
lemma spectral_integral_eq_of_eq_fun (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f g : ℝ → ℂ) (hfg : f = g) (ψ : H)
    (hf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g) :
    spectral_integral E hE f ψ hf = spectral_integral E hE g ψ hg := by
  subst hfg
  rfl  -- proof irrelevance: hf and hg now have the same type

end FunctionalCalculus
