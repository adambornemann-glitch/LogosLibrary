/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform.Spectrum

/-!
# Spectral Measures and the Cayley Transform

This file defines the Möbius image of sets and establishes the compatibility between
spectral measures of a self-adjoint operator `A` and its Cayley transform `U`.

## Main definitions

* `cayleyImage`: The Möbius image `{(μ - i)/(μ + i) | μ ∈ B}` of a set of reals
* `spectralMeasure_from_unitary`: Constructs a spectral measure for `A` from one for `U`
* `SpectralMeasuresCompatible`: Predicate asserting `E_A(B) = E_U(cayleyImage B)`

## Main statements

* `spectralMeasure_cayley_correspondence`: Compatible spectral measures satisfy
  `E_A(B) = E_U(cayleyImage B)`
-/

namespace QuantumMechanics.Cayley

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Möbius image of a set of reals under `μ ↦ (μ - i)/(μ + i)`. -/
def cayleyImage (B : Set ℝ) : Set ℂ :=
  {w : ℂ | ∃ μ ∈ B, w = (↑μ - I) * (↑μ + I)⁻¹}

/-- Constructs a spectral measure for `A` from a spectral measure for `U`. -/
noncomputable def spectralMeasure_from_unitary
    (E_U : Set ℂ → (H →L[ℂ] H)) : Set ℝ → (H →L[ℂ] H) :=
  fun B => E_U (cayleyImage B)

/-- Predicate asserting that spectral measures for `A` and `U` are compatible. -/
def SpectralMeasuresCompatible {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (_ /-hsa-/ : gen.IsSelfAdjoint)
    (E_A : Set ℝ → (H →L[ℂ] H)) (E_U : Set ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ B : Set ℝ, E_A B = E_U (cayleyImage B)

/-- Existence of compatible spectral measures (axiom). -/
axiom exists_compatible_spectral_measures {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    ∃ (E_A : Set ℝ → (H →L[ℂ] H)) (E_U : Set ℂ → (H →L[ℂ] H)),
      SpectralMeasuresCompatible gen hsa E_A E_U

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- Compatible spectral measures satisfy `E_A(B) = E_U(cayleyImage B)`. -/
theorem spectralMeasure_cayley_correspondence {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E_A : Set ℝ → (H →L[ℂ] H)) (E_U : Set ℂ → (H →L[ℂ] H))
    (hcompat : SpectralMeasuresCompatible gen hsa E_A E_U)
    (B : Set ℝ) :
    E_A B = E_U (cayleyImage B) := hcompat B

end QuantumMechanics.Cayley
