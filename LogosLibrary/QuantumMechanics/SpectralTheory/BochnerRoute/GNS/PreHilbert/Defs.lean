/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/GNS/PreHilbert/Defs.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Continuity
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Order

/-!
# The GNS Pre-Hilbert Space for Positive Definite Functions

Given a continuous positive definite function `f : ℝ → ℂ`, we construct a
pre-inner-product space whose completion will carry a strongly continuous
unitary representation of `(ℝ, +)` with a cyclic vector `ξ` satisfying
`f(t) = ⟨ξ, U(t)ξ⟩`.

## The construction

**Vectors.** Formal finite ℂ-linear combinations of point masses `δ_t`,
represented as `ℝ →₀ ℂ` (finitely supported functions ℝ → ℂ). The element
`Finsupp.single t c` represents `c · δ_t`.

**Pre-inner product.** For `α = Σⱼ cⱼ δ_{tⱼ}` and `β = Σₖ dₖ δ_{sₖ}`:

  `⟨α, β⟩_f = Σⱼ Σₖ c̄ⱼ · dₖ · f(sₖ - tⱼ)`

This is conjugate-linear in `α` and linear in `β` (Mathlib/physics convention).

**Translation action.** `U(t)` sends `δ_s ↦ δ_{s+t}`, extended linearly.
Implemented via `Finsupp.mapDomain (· + t)`.

**Cyclic vector.** `ξ = δ_0 = Finsupp.single 0 1`.

**Key identity.** `⟨ξ, U(t)ξ⟩_f = f(t)`.

## Properties established

- Conjugate symmetry: `⟨β, α⟩ = conj ⟨α, β⟩` (from `IsHermitian f`)
- Positive semi-definiteness: `0 ≤ Re⟨α, α⟩` (from `PositiveDefinite f`)
- Translation isometry: `⟨U(t)α, U(t)β⟩ = ⟨α, β⟩`
- Group law: `U(s) ∘ U(t) = U(s + t)`

The null space `N = {α : ⟨α, α⟩ = 0}` and completion to a Hilbert space
are handled in `GNS/Completion.lean`.

## References

* Folland, *A Course in Abstract Harmonic Analysis*, §3.3
* Reed & Simon, *Methods of Modern Mathematical Physics I*, §II.6
* Berg, Christensen & Ressel, *Harmonic Analysis on Semigroups*, Ch. 3

## Tags

GNS construction, positive definite function, pre-Hilbert space,
Bochner's theorem, cyclic representation
-/

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp

-- §1  The pre-inner product

/-- The pre-inner product on formal sums, induced by `f : ℝ → ℂ`.

Convention: conjugate-linear in the first argument, linear in the second,
matching `@inner ℂ` in Mathlib.

Implementation note: we use `Finsupp.sum` (= `∑ over support`) twice.
The definition is independent of how one enlarges the support, because
`Finsupp.sum` ignores indices where the coefficient is zero. -/
noncomputable def pdInner (f : ℝ → ℂ) (α β : ℝ →₀ ℂ) : ℂ :=
  α.sum fun t ct =>
    β.sum fun s ds =>
      starRingEnd ℂ ct * ds * f (s - t)

/-- Translation by `t`: sends `δ_s ↦ δ_{s+t}`, extended linearly.

This is `U(t)` in the unitary representation. Implemented as
`Finsupp.mapDomain (· + t)`, which reindexes the support. -/
noncomputable def translate (t : ℝ) (α : ℝ →₀ ℂ) : ℝ →₀ ℂ :=
  Finsupp.mapDomain (· + t) α


end SpectralBridge.Bochner.GNS
