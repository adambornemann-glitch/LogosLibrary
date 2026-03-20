/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/GNS/Completion/UnitaryGroup.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.GNS.Completion.Constructor

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp Filter Topology

/-- Extended translation action on the GNS Hilbert space.

Since `translate t` is an isometry of the pre-inner product:
  `⟨U(t)α, U(t)β⟩ = ⟨α, β⟩`
it descends to an isometry on the quotient, which extends uniquely
to an isometry on the completion. -/
structure GNSUnitaryGroup (f : ℝ → ℂ) extends GNSData f where
  /-- The unitary group action on H. -/
  unitaryAction : ℝ → H →ₗ[ℂ] H
  /-- U(t) is an isometry (hence unitary, since it's surjective). -/
  isometry : ∀ (t : ℝ) (ψ φ : H),
    @inner ℂ H instIPS.toInner (unitaryAction t ψ) (unitaryAction t φ) =
    @inner ℂ H instIPS.toInner ψ φ
  /-- Group law: U(s+t) = U(s) ∘ U(t). -/
  group_law : ∀ (s t : ℝ) (ψ : H),
    unitaryAction (s + t) ψ = unitaryAction s (unitaryAction t ψ)
  /-- Identity: U(0) = id. -/
  identity : ∀ (ψ : H), unitaryAction 0 ψ = ψ
  /-- Strong continuity: t ↦ U(t)ψ is continuous for each ψ. -/
  strong_continuous : ∀ (ψ : H), Continuous (fun t => unitaryAction t ψ)
  /-- Compatibility: U(t) ∘ embed = embed ∘ translate(t). -/
  compat : ∀ (t : ℝ) (α : ℝ →₀ ℂ),
    unitaryAction t (toGNSData.embed α) = toGNSData.embed (translate t α)

end SpectralBridge.Bochner.GNS
