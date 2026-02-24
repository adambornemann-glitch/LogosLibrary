/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Basic
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.LowerBound
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.NormExpansion
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.SpecialCases
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Range
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Core
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Identities
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Analytic

/-!
# Resolvent Theory for Self-Adjoint Generators

This module develops the resolvent operator `R(z) = (A - zI)⁻¹` for self-adjoint
generators of one-parameter unitary groups, establishing its key analytic properties.

## Files

* `Basic`: Types for spectral regions and Neumann series machinery
* `LowerBound`: The fundamental estimate `‖(A - zI)ψ‖ ≥ |Im(z)| · ‖ψ‖`
* `SpecialCases`: Resolvent at `±i` constructed directly from self-adjointness
* `Range`: Surjectivity of `(A - zI)` for `Im(z) ≠ 0`
* `Core`: The resolvent definition and basic bound
* `Identities`: Resolvent identity and adjoint relation
* `Analytic`: Power series expansion of the resolvent

## Main results

* `resolvent`: The resolvent `R(z) = (A - zI)⁻¹` for `Im(z) ≠ 0`
* `resolvent_bound`: `‖R(z)‖ ≤ 1/|Im(z)|`
* `resolvent_identity`: `R(z) - R(w) = (z - w) R(z) R(w)`
* `resolvent_adjoint`: `R(z)* = R(z̄)`
* `resolventFun_hasSum`: Power series expansion near any point

## References

* [Kato, *Perturbation Theory for Linear Operators*][kato1995]
* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.6
-/
