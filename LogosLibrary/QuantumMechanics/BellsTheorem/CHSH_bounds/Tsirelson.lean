/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your name here]
-/
import LogosLibrary.QuantumMechanics.BellsTheorem.CHSH_Bounds.Tsirelson.Tsirelson

/-!
# Tsirelson's Bound (Classical Formulation)

This module provides a complete proof of Tsirelson's bound for the CHSH inequality
in finite-dimensional quantum mechanics.

## Main Result

`tsirelson_bound`: For any quantum state ρ and CHSH tuple (A₀, A₁, B₀, B₁),
  |⟨A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁⟩| ≤ 2√2

## Module Structure

* `UnitaryBounds`: General theory of unitary operators and Hermitian involutions
* `CommutatorAlgebra`: Commutator bounds for Hermitian involutions
* `Tsirelson`: The main theorem and supporting lemmas

## References

* B.S. Tsirelson, "Quantum generalizations of Bell's inequality", Lett. Math. Phys. 4 (1980)
* J.F. Clauser, M.A. Horne, A. Shimony, R.A. Holt, "Proposed experiment to test local
  hidden-variable theories", Phys. Rev. Lett. 23 (1969)
-/
