/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Existence/GNS/Completion/Cyclic.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.GNS.Completion.ConstructorII

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp Filter Topology

/-- The cyclic vector in the GNS Hilbert space:
    `ξ = embed(δ₀) = embed(single 0 1)`. -/
noncomputable def gns_cyclic (gns : GNSData f) : gns.H :=
  gns.embed cyclicVector

/-- **THE KEY IDENTITY in H**: `f(t) = ⟨ξ, U(t)ξ⟩_H`.

This is the representation theorem at the Hilbert space level.
It follows directly from PreHilbert's `pdInner_cyclic` composed
with the embedding's inner product preservation.

Proof:
  ⟨ξ, U(t)ξ⟩_H
    = ⟨embed(δ₀), U(t)(embed(δ₀))⟩_H           [definition of ξ]
    = ⟨embed(δ₀), embed(translate t δ₀)⟩_H       [compatibility]
    = pdInner f δ₀ (translate t δ₀)               [embed_inner]
    = f(t)                                         [pdInner_cyclic] -/
theorem gns_representation {f : ℝ → ℂ}
    (gns : GNSUnitaryGroup f) (t : ℝ) :
    @inner ℂ gns.H gns.instIPS.toInner
      (gns_cyclic gns.toGNSData)
      (gns.unitaryAction t (gns_cyclic gns.toGNSData)) = f t := by
  unfold gns_cyclic
  rw [gns.compat t cyclicVector,
      gns.toGNSData.embed_inner cyclicVector (translate t cyclicVector),
      pdInner_cyclic f t]

/-- The norm of the cyclic vector: `‖ξ‖² = f(0).re`.

Proof: ‖ξ‖² = Re⟨ξ,ξ⟩ = Re(pdInner f δ₀ δ₀) = Re(f(0)) = f(0).re. -/
lemma gns_cyclic_norm_sq {f : ℝ → ℂ}
    (_hH : IsHermitian f) (gns : GNSData f) :
    @inner ℂ gns.H gns.instIPS.toInner
      (gns_cyclic gns) (gns_cyclic gns) = f 0 := by
  unfold gns_cyclic
  rw [gns.embed_inner]
  have := pdInner_cyclic f 0
  rw [translate_zero] at this
  exact this

end SpectralBridge.Bochner.GNS
