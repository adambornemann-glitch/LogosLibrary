/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.Exponential

/-!
# Yosida Approximation and Stone's Theorem (Converse)

This module provides a complete proof of the converse of Stone's theorem:
every self-adjoint operator on a Hilbert space generates a strongly continuous
one-parameter unitary group via the exponential map `U(t) = exp(itA)`.

## Overview

The construction proceeds via Yosida approximation:

1. **Approximate the unbounded `A`** by bounded operators `Aₙ` using resolvents at `z = ±in`
2. **Show `exp(i·Aₙ·t)` is unitary** because `i·Aₙ` is skew-adjoint
3. **Use Duhamel's formula** to relate `U(t) - exp(i·Aₙ·t)` to an integral of `(A - Aₙ)`
4. **Prove `Aₙ → A` pointwise** on the domain, so the Duhamel integral vanishes
5. **Take limits** to obtain `exp(itA)` with all desired properties

## File structure

* `Basic.lean`: Arithmetic lemmas for `I * n`, resolvent specifications
* `Defs.lean`: Core operator definitions (`yosidaApprox`, `yosidaApproxSym`, `yosidaJ`, etc.)
* `Bounds.lean`: Norm bounds on Yosida operators
* `Symmetry.lean`: Self-adjointness of `Aₙˢʸᵐ`, skew-adjointness of `i·Aₙˢʸᵐ`
* `Convergence/`: Pointwise convergence of `Jₙ`, `Jₙ⁻`, and approximants
* `ExpBounded/`: Theory of bounded operator exponentials
* `Duhamel/`: Duhamel's formula and uniform convergence estimates
* `Exponential.lean`: The main construction and Stone's theorem converse

## Main results

* `exponential`: The unitary group `exp(itA)` as a continuous linear map
* `exponential_unitary`: Inner products are preserved
* `exponential_group_law`: `exp(i(s+t)A) = exp(isA) ∘ exp(itA)`
* `exponential_strong_continuous`: `t ↦ exp(itA)ψ` is continuous
* `exponential_generator_eq`: The generator of `exp(itA)` is `iA`

## References

* [Kato, *Perturbation Theory*][kato1995], Section IX.1
* [Reed-Simon, *Methods of Modern Mathematical Physics I*][reed1980], Theorem VIII.7
* [Yosida, *Functional Analysis*][yosida1980], Chapter IX

-/
