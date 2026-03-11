/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.Generator
/-!
# Three Routes Agreement

This file establishes that the three different constructions of spectral measures
(Bochner, Stieltjes, and Cayley) all produce the same result.

## Main definitions

* `SpectralMeasureAgreement`: Structure asserting all three routes agree

## Main axioms

* `spectralMeasure_from_cayley`: The Cayley-constructed spectral measure
* `bochner_route_agreement`: Bochner route produces same measure
* `stieltjes_route_agreement`: Stieltjes route produces same measure
* `cayley_route_agreement`: Cayley route produces same measure

## Main results

* `three_routes_agree`: All three constructions produce the same spectral measure

## Tags

spectral measure, Bochner, Stieltjes, Cayley transform, three routes
-/
namespace FunctionalCalculus

open MeasureTheory InnerProductSpace Complex QuantumMechanics.Cayley SpectralBridge.Resolvent SpectralBridge.Bochner QuantumMechanics.Generators ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## Cayley Route Axiom
-/

/-- The spectral measure from unitary (Cayley) route - axiomatized -/
axiom spectralMeasure_from_cayley {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) : Set ℝ → H →L[ℂ] H

/-!
## Agreement Structure
-/

/-- The spectral measures from all three routes agree. -/
structure SpectralMeasureAgreement
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen) : Prop where
  /-- E agrees with Bochner measure from U(t) -/
  bochner_agreement : ∀ ψ B, MeasurableSet B →
    (spectral_scalar_measure E ψ hE.toIsSpectralMeasure B).toReal =
    (bochner_measure U_grp ψ B).toReal
  /-- E agrees with Stieltjes inversion from R(z) -/
  stieltjes_agreement : ∀ ψ a b, a < b →
    (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re =
    (bochner_measure U_grp ψ (Set.Ioc a b)).toReal
  /-- E agrees with Cayley-lifted spectral measure -/
  cayley_agreement : ∀ B, MeasurableSet B →
    E B = spectralMeasure_from_cayley gen hsa B

/-!
## Route Agreement Axioms
-/

/-- Bochner route produces same measure as E -/
axiom bochner_route_agreement {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    (spectral_scalar_measure E ψ hE.toIsSpectralMeasure B).toReal =
    (bochner_measure U_grp ψ B).toReal

/-- Stieltjes inversion produces same measure as E -/
axiom stieltjes_route_agreement {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (a b : ℝ) (hab : a < b) :
    (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re =
    (bochner_measure U_grp ψ (Set.Ioc a b)).toReal

/-- Cayley route produces same measure as E -/
axiom cayley_route_agreement {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (B : Set ℝ) (hB : MeasurableSet B) :
    E B = spectralMeasure_from_cayley gen hsa B

/-!
## Main Theorem
-/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- The three routes produce the same spectral measure -/
theorem three_routes_agree {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen) :
    SpectralMeasureAgreement gen hsa E hE where
  bochner_agreement := fun ψ B hB => bochner_route_agreement gen hsa E hE ψ B hB
  stieltjes_agreement := fun ψ a b hab => stieltjes_route_agreement gen hsa E hE ψ a b hab
  cayley_agreement := fun B hB => cayley_route_agreement gen hsa E hE B hB

end FunctionalCalculus
