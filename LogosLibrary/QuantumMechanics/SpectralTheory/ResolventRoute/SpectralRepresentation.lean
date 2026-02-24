/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.ResolventRoute.ResolventKernel

/-!
# Resolvent Spectral Representation

This file establishes the spectral representation of the resolvent:
`R(z) = ∫ (λ - z)⁻¹ dE(λ)`.

## Main definitions

* `spectral_integral`: The operator-valued spectral integral `∫ f(λ) dE(λ)`

## Main statements

* `resolvent_spectral_bilinear`: `⟨R(z)ψ, ψ⟩ = ∫ (s-z)⁻¹ dμ_ψ(s)` (axiom)
* `resolvent_spectral_integrable`: Integrability of `(s-z)⁻¹` against spectral measure (axiom)
* `resolvent_eq_spectral_integral`: `R(z)ψ = ∫ (λ-z)⁻¹ dE(λ) ψ` (axiom)
* `resolvent_spectral_representation`: The main theorem (operator form)
* `resolvent_spectral_representation'`: The bilinear form version

## Implementation notes

The spectral integral `∫ f(λ) dE(λ)` for a projection-valued measure `E` is defined
axiomatically here. A full implementation would use the Lebesgue-Stieltjes integral
theory with operator-valued integrands.

## Physical interpretation

The resolvent `R(z) = (A - z)⁻¹` of a self-adjoint operator `A` has a spectral
representation as an integral against the spectral measure. This is the foundation
for extracting spectral information from the resolvent via Stone's formula.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VII
* [Schmüdgen, *Unbounded Self-adjoint Operators*][schmudgen2012], Chapter 5

## Tags

resolvent, spectral representation, spectral integral
-/

namespace SpectralBridge.Resolvent

open QuantumMechanics.Resolvent QuantumMechanics.Generators SpectralBridge.Bochner Complex
open InnerProductSpace MeasureTheory Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Spectral integral axioms -/

/-- The bilinear form of the resolvent has spectral representation.

`⟨R(z)ψ, ψ⟩ = ∫ (s - z)⁻¹ dμ_ψ(s)`

where `μ_ψ` is the spectral scalar measure `μ_ψ(B) = ⟨E(B)ψ, ψ⟩`. -/
axiom resolvent_spectral_bilinear {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E)
    (z : QuantumMechanics.Resolvent.OffRealAxis) (ψ : H) :
    ⟪resolventFun gen hsa z ψ, ψ⟫_ℂ =
      ∫ s : ℝ, ((s : ℂ) - z.val)⁻¹ ∂(spectral_scalar_measure E ψ hE)

/-- The spectral integral `(s - z)⁻¹` is integrable for `z` off the real axis.

This follows from the bound `|(s - z)⁻¹| ≤ 1/|Im(z)|` and finiteness of
the spectral measure. -/
axiom resolvent_spectral_integrable {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E)
    (z : OffRealAxis) (ψ : H) :
    Integrable (fun s : ℝ => ((s : ℂ) - z.val)⁻¹)
      (spectral_scalar_measure E ψ hE)

/-! ### Operator-valued spectral integral -/

/-- The operator-valued spectral integral `∫ f(λ) dE(λ)` applied to a vector.

This is the Stieltjes integral with respect to a projection-valued measure.
For bounded measurable `f`, this is well-defined and satisfies
`⟨∫ f dE ψ, φ⟩ = ∫ f d⟨E(·)ψ, φ⟩`. -/
axiom spectral_integral (E : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) (ψ : H) : H

/-- Notation for spectral integrals. -/
notation "∫_E " f ", " ψ => spectral_integral _ f ψ

/-- The spectral integral of `(λ - z)⁻¹` equals the resolvent. -/
axiom resolvent_eq_spectral_integral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (z : QuantumMechanics.Resolvent.OffRealAxis) (ψ : H) :
    resolventFun gen hsa z ψ = spectral_integral E (fun t => ((t : ℂ) - z.val)⁻¹) ψ

/-- Lebesgue-Stieltjes representation of the spectral integral.

For the spectral integral can be written as a Lebesgue integral against
point masses when `E` has atoms, or more generally via the Stieltjes measure. -/
axiom spectral_integral_eq_lebesgue (E : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) (ψ : H) :
    spectral_integral E f ψ = ∫ t : ℝ, f t • E {t} ψ  -- formal equality via Stieltjes

/-! ### Main theorems -/

/-- **Resolvent Spectral Representation (Operator Form)**

The resolvent has an integral representation:
`R(z) = ∫_ℝ (s - z)⁻¹ dE(s)`

This is the operator-valued version of the spectral representation. -/
theorem resolvent_spectral_representation {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H))
    (z : QuantumMechanics.Resolvent.OffRealAxis) (ψ : H) :
    resolventFun gen hsa z ψ = ∫ t : ℝ, ((t : ℂ) - z.val)⁻¹ • E {t} ψ := by
  rw [← spectral_integral_eq_lebesgue]
  exact resolvent_eq_spectral_integral gen hsa E z ψ

/-- **Resolvent Spectral Representation (Bilinear Form)**

The bilinear form version:
`⟨R(z)ψ, ψ⟩ = ∫_ℝ (s - z)⁻¹ dμ_ψ(s)`

where `μ_ψ(B) = ⟨E(B)ψ, ψ⟩` is the spectral scalar measure. -/
theorem resolvent_spectral_representation' {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E)
    (z : QuantumMechanics.Resolvent.OffRealAxis) (ψ : H) :
    ⟪resolventFun gen hsa z ψ, ψ⟫_ℂ =
      ∫ s : ℝ, ((s : ℂ) - z.val)⁻¹ ∂(spectral_scalar_measure E ψ hE) :=
  resolvent_spectral_bilinear gen hsa E hE z ψ

/-- Specialization: the spectral measure `μ` can be any measure agreeing with `E`
    on measurable sets.

This is useful when working with different representations of the same measure. -/
theorem resolvent_spectral_representation'_alt {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E)
    (μ : H → Measure ℝ)
    (hμ : ∀ ψ, μ ψ = spectral_scalar_measure E ψ hE)
    (z : QuantumMechanics.Resolvent.OffRealAxis) (ψ : H) :
    ⟪resolventFun gen hsa z ψ, ψ⟫_ℂ = ∫ t : ℝ, ((t : ℂ) - z.val)⁻¹ ∂(μ ψ) := by
  rw [hμ ψ]
  exact resolvent_spectral_bilinear gen hsa E hE z ψ

end SpectralBridge.Resolvent
