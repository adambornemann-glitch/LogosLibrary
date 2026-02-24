/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform.Unitary
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform.Mobius
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform.Transform
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform.Inverse
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform.Eigenvalue
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform.Spectrum
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform.SpectralMeasure
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

## File organization

* `Cayley.Unitary`: General theory of unitary operators on Hilbert spaces
* `Cayley.Mobius`: Complex analysis lemmas for the Möbius map `μ ↦ (μ - i)/(μ + i)`
* `Cayley.Transform`: Core definition and basic properties (isometry, unitarity)
* `Cayley.Inverse`: Inverse transform and domain characterization
* `Cayley.Eigenvalue`: Eigenvalue correspondence between `A` and `U`
* `Cayley.Spectrum`: Full spectral correspondence (approximate point spectrum)
* `Cayley.SpectralMeasure`: Compatibility of spectral measures

## References

* [Reed and Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*]
* [Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*]
* [Rudin, *Functional Analysis*], Chapter 13
-/
