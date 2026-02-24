/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.SpectralProjection
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.ScalarMeasure
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.CrossMeasure
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.Domain
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.Integral
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.Algebraic
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.Generator
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.Agreement
/-!
# Functional Calculus for Self-Adjoint Operators

This file re-exports all components of the Borel functional calculus for self-adjoint
operators via spectral measures.

## File Structure

The functional calculus is developed across several files:

* `SpectralProjection`: Properties of spectral projections E(B)
* `ScalarMeasure`: The spectral scalar measure μ_ψ(B) = ‖E(B)ψ‖²
* `CrossMeasure`: Cross-measure ν_{ψ,φ} and polarization identities
* `Domain`: The functional domain {ψ : ∫|f|² dμ_ψ < ∞}
* `Integral`: Spectral integral axioms and indicator theorem
* `Algebraic`: Functional calculus as a *-homomorphism
* `Generator`: Recovery of A from E via A = ∫ s dE(s)
* `Agreement`: Three routes (Bochner, Stieltjes, Cayley) produce same E

## Overview

The functional calculus is a *-homomorphism from (a suitable algebra of) functions
on `ℝ` to operators on `H`:
- `Φ(f + g) = Φ(f) + Φ(g)` (additive)
- `Φ(fg) = Φ(f) ∘ Φ(g)` (multiplicative)
- `Φ(f̄) = Φ(f)*` (preserves adjoints)
- `Φ(1) = I` (unital)
- `Φ(𝟙_B) = E(B)` (indicator functions give spectral projections)

## Physical interpretation

The functional calculus is the mathematical foundation for quantum observables:
- If `A` is the Hamiltonian with spectrum `σ(A)`, then `f(A)` represents measuring
  the observable `f(energy)`
- The spectral projections `E(B)` represent "the system has energy in `B`"
- The formula `⟨f(A)ψ, ψ⟩ = ∫ f dμ_ψ` is the expectation value of `f(A)` in state `ψ`

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Chapter VII-VIII
* [Schmüdgen, *Unbounded Self-adjoint Operators*][schmudgen2012], Chapters 4-5
* [Rudin, *Functional Analysis*][rudin1991], Chapter 12
* [Hall, *Quantum Theory for Mathematicians*][hall2013], Chapter 7

## Tags

functional calculus, spectral measure, spectral theorem, self-adjoint operator,
*-homomorphism, Borel functional calculus
-/
