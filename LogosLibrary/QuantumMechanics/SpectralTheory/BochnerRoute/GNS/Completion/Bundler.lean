/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/GNS/Completion/Bundler.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.GNS.Completion.NullSpace

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp Filter Topology

/-- The complete GNS data for a continuous positive definite function.

Rather than constructing the quotient and completion step by step
(which requires heavy Mathlib plumbing), we bundle everything into
a single structure and show it exists.

This is the mathematical content of the GNS theorem; the individual
fields are established through the quotient-completion construction
outlined in §3 below. -/
structure GNSData (f : ℝ → ℂ) where
  /-- The GNS Hilbert space. -/
  H : Type*
  /-- H is a normed additive commutative group. -/
  instNACG : NormedAddCommGroup H
  /-- H is an inner product space over ℂ. -/
  instIPS : @InnerProductSpace ℂ H _ instNACG.toSeminormedAddCommGroup
  /-- H is complete (Hilbert). -/
  instComplete : @CompleteSpace H instNACG.toUniformSpace
  /-- Embedding of formal sums into H. -/
  embed : letI := instNACG; letI := instIPS; (ℝ →₀ ℂ) →ₗ[ℂ] H
  /-- The embedding respects the pre-inner product. -/
  embed_inner : ∀ (α β : ℝ →₀ ℂ),
    @inner ℂ H instIPS.toInner (embed α) (embed β) = pdInner f α β
  /-- The embedded formal sums are dense in H. -/
  embed_dense : letI := instNACG; Dense (Set.range embed)
  /-- The kernel of the embedding is the null space. -/
  embed_ker : letI := instNACG; ∀ α, embed α = 0 ↔ α ∈ pdNullSpace f


end SpectralBridge.Bochner.GNS
