/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Range.Orthogonal
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Range.ClosedRange
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Range.Surjectivity
/-!
# Surjectivity of (A - zI) for Self-Adjoint Generators

This module proves that for a self-adjoint generator `A` and any `z` with
`Im(z) ≠ 0`, the operator `(A - zI)` is surjective.

## Main result

* `self_adjoint_range_all_z`: The equation `(A - zI)ψ = φ` has a unique
  solution for every `φ ∈ H`.

## Proof outline

1. **Orthogonal complement is trivial** (`Orthogonal.lean`): `ran(A-zI)⊥ = {0}`
2. **Range is closed** (`ClosedRange.lean`): Uses the lower bound estimate
3. **Closed + dense = everything** (`Surjectivity.lean`): Assembles the result

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3
-/
