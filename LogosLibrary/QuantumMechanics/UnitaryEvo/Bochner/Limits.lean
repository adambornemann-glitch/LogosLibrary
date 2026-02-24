/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner.Limits.Helpers
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner.Limits.Plus
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner.Limits.Minus

/-!
# Generator Limits for Resolvent Integrals

This module proves that the resolvent integrals `R±(φ)` lie in the domain of the
generator and satisfy the key equations for Stone's theorem.

## Module structure

* `Limits.Helpers`: shared analytical lemmas (`tendsto_exp_sub_one_div`, etc.)
* `Limits.Plus`: `R₊(φ)` is in the generator domain with `A(R₊φ) = φ - iR₊φ`
* `Limits.Minus`: `R₋(φ)` is in the generator domain with `A(R₋φ) = φ + iR₋φ`

## Main results

* `generator_limit_resolventIntegralPlus`: the generator limit for `R₊`
* `generator_limit_resolventIntegralMinus`: the generator limit for `R₋`

## Tags

generator, resolvent, limit, Stone's theorem
-/
