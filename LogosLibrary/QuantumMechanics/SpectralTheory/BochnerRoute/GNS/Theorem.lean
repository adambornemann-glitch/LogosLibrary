/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/GNS/Theorem.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.GNS.Completion.ToStone

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp Filter Topology

/-- **The GNS theorem for positive definite functions on ℝ.**

Given a continuous positive definite function `f : ℝ → ℂ`, there exists:
1. A Hilbert space H
2. A strongly continuous one-parameter unitary group U(t) on H
3. A vector ξ ∈ H with ‖ξ‖² = f(0).re
4. f(t) = ⟨ξ, U(t)ξ⟩ for all t

Moreover, the translates `{U(t)ξ : t ∈ ℝ}` span a dense subspace of H
(cyclicity).

This is the existence half of the GNS construction. Combined with
Stone's theorem and the spectral theorem, it yields Bochner's theorem. -/
theorem gns_theorem {f : ℝ → ℂ} (hf : IsContinuous f) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H)
      (U : ℝ → H →ₗ[ℂ] H) (ξ : H),
      (∀ t ψ φ, @inner ℂ H ‹InnerProductSpace ℂ H›.toInner (U t ψ) (U t φ) =
                 @inner ℂ H ‹InnerProductSpace ℂ H›.toInner ψ φ) ∧
      (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧
      (∀ ψ, U 0 ψ = ψ) ∧
      (∀ ψ, Continuous (fun t => U t ψ)) ∧
      (∀ t, @inner ℂ H ‹InnerProductSpace ℂ H›.toInner ξ (U t ξ) = f t) := by
  let gns := gnsUnitaryConstruction hf
  exact ⟨gns.H, gns.instNACG, gns.instIPS, gns.instComplete,
    gns.unitaryAction, gns_cyclic gns.toGNSData,
    gns.isometry, gns.group_law, gns.identity, gns.strong_continuous,
    fun t => gns_representation gns t⟩

  end SpectralBridge.Bochner.GNS
