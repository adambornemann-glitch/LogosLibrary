/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Existence/GNS/PreHilbert.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.GNS.PreHilbert.NormEst
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

/-- Cauchy-Schwarz for the PD pre-inner product:
    `(Re⟨α, β⟩)² ≤ Re⟨α,α⟩ · Re⟨β,β⟩`.
    Proof: the real quadratic `lambda ↦ Re⟨α + lambdaβ, α + lambdaβ⟩ ≥ 0` has non-positive discriminant. -/
lemma pdInner_cauchy_schwarz_re {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (α β : ℝ →₀ ℂ) :
    (pdInner f α β).re ^ 2 ≤ (pdInner f α α).re * (pdInner f β β).re := by
  have hexpand : ∀ lambda : ℝ,
      (pdInner f (α + (↑lambda : ℂ) • β) (α + (↑lambda : ℂ) • β)).re =
      (pdInner f α α).re + 2 * (pdInner f α β).re * lambda +
      (pdInner f β β).re * lambda ^ 2 := by
    intro lambda
    simp only [pdInner_add_left hH, pdInner_add_right,
               pdInner_smul_right, pdInner_smul_left hH, Complex.conj_ofReal]
    rw [pdInner_conj_symm hH α β]
    simp only [Complex.add_re, Complex.mul_re,
               Complex.ofReal_re, Complex.ofReal_im,
               Complex.conj_re, zero_mul, sub_zero]
    ring
  have hq : ∀ lambda : ℝ,
      0 ≤ (pdInner f α α).re + 2 * (pdInner f α β).re * lambda +
      (pdInner f β β).re * lambda ^ 2 := by
    intro lambda; rw [← hexpand]; exact pdInner_self_re_nonneg hPD _
  set A := (pdInner f α α).re
  set B := (pdInner f α β).re
  set C := (pdInner f β β).re
  have hC_nn : 0 ≤ C := pdInner_self_re_nonneg hPD β
  by_cases hC0 : C = 0
  · -- C = 0: quadratic degenerates to linear, forces B = 0
    have hlin : ∀ lambda : ℝ, 0 ≤ A + 2 * B * lambda := by simpa [hC0] using hq
    have hB : B = 0 := by
      by_contra hB
      have h2B : (2 : ℝ) * B ≠ 0 := mul_ne_zero two_ne_zero hB
      linarith [hlin (-(A + 1) / (2 * B)),
        show A + 2 * B * (-(A + 1) / (2 * B)) = -1 from by field_simp; ring]
    simp [hB, hC0]
  · -- C > 0: evaluate at lambda = -B/C, clear denominators
    have hC_pos : 0 < C := lt_of_le_of_ne hC_nn (Ne.symm hC0)
    have h := hq (-B / C)
    have h_simp : A + 2 * B * (-B / C) + C * (-B / C) ^ 2 = A - B ^ 2 / C := by
      field_simp; ring
    rw [h_simp] at h
    rwa [sub_nonneg, div_le_iff₀ hC_pos] at h


end SpectralBridge.Bochner.GNS
