/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner.Basic
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner.Resolvent
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner.Limits
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner.Domain

/-!
# Stone's Theorem: Generators of Unitary Groups

This module provides a complete proof of Stone's theorem (forward direction): every
strongly continuous one-parameter unitary group on a complex Hilbert space has a
unique self-adjoint infinitesimal generator.

## Main results

* `generatorOfUnitaryGroup`: constructs the generator of a unitary group
* `generatorOfUnitaryGroup_isSelfAdjoint`: the generator is self-adjoint
* `generatorDomain_dense`: the domain of the generator is dense

## Module structure

* `Bochner.Basic`: Bochner integration lemmas for exponentially decaying functions
* `Bochner.Resolvent`: resolvent integrals `R±(φ) = ∓i ∫₀^∞ e^{-t} U(±t)φ dt`
* `Bochner.Limits`: generator limits showing `R±(φ)` solve `(A ± iI)ψ = φ`
* `Bochner.Domain`: domain construction, density, and self-adjointness

## Physics context

This establishes that quantum time evolution `U(t) = e^{-itH}` uniquely determines
the Hamiltonian `H`. The resolvent integrals connect time-domain evolution to
energy-domain spectral properties via Laplace transform techniques.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Theorem VIII.8
* [Hall, *Quantum Theory for Mathematicians*][hall2013], Chapter 10

## Tags

Stone's theorem, unitary group, self-adjoint operator, infinitesimal generator,
spectral theory, quantum mechanics
-/
