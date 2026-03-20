/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Existence/GNS/PreHilbert.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.GNS.PreHilbert.TransAction

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp

-- §7  The cyclic vector and the key identity

/-- The cyclic vector: `ξ = δ_0 = single 0 1`.

In the completed Hilbert space, this will satisfy:
  `f(t) = ⟨ξ, U(t)ξ⟩`  and  `span(U(t)ξ : t ∈ ℝ)` is dense. -/
noncomputable def cyclicVector : ℝ →₀ ℂ := Finsupp.single 0 1

/-- `U(t)(ξ) = δ_t`. -/
@[simp]
lemma translate_cyclicVector (t : ℝ) :
    translate t cyclicVector = Finsupp.single t 1 := by
  unfold cyclicVector
  rw [translate_single]
  simp

/-- **The key identity**: `f(t) = ⟨ξ, U(t)ξ⟩_f`.

This is the fundamental formula that connects the abstract positive
definite function to the concrete inner product on the GNS space.

Proof: `⟨ξ, U(t)ξ⟩ = ⟨δ₀, δ_t⟩ = conj(1) · 1 · f(t - 0) = f(t)`. -/
theorem pdInner_cyclic (f : ℝ → ℂ) (t : ℝ) :
    pdInner f cyclicVector (translate t cyclicVector) = f t := by
  rw [translate_cyclicVector]
  unfold cyclicVector
  rw [pdInner_single_single, map_one, one_mul, one_mul, sub_zero]

end SpectralBridge.Bochner.GNS
