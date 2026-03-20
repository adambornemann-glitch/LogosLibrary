/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Existence/GNS/Completion/ConstructorII.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.GNS.Completion.ConstructorII.StronglyCont

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp Filter Topology


/-- **Existence of the GNS unitary group.**

Construction:
1. `translate t` preserves `N` (by `pdNullSpace_translate_invariant`),
   so it descends to a map `U₀(t)` on the quotient `V = (ℝ →₀ ℂ)/N`.
2. `U₀(t)` is an isometry of `V` (by `pdInner_translate`).
3. Every isometry of a pre-Hilbert space extends uniquely to an isometry
   of the completion (`UniformSpace.Completion.map` with uniform continuity).
4. Group law and identity follow from `translate_translate` and `translate_zero`.
5. Strong continuity is established in §6 below. -/
noncomputable def gnsUnitaryConstruction {f : ℝ → ℂ}
    (hf : IsContinuous f) :
    GNSUnitaryGroup f := by
  set gns := gnsConstruction hf.pd hf.hermitian
  letI := gns.instNACG
  letI := gns.instIPS
  haveI := gns.instComplete
  exact {
    toGNSData := gns
    unitaryAction := fun t => completionTranslate hf.pd hf.hermitian t
    isometry := fun t ψ φ => completionTranslate_inner hf.pd hf.hermitian t ψ φ
    group_law := fun s t ψ =>
      (completionTranslate_comp hf.pd hf.hermitian s t ψ).symm
    identity := fun ψ => completionTranslate_zero' hf.pd hf.hermitian ψ
    strong_continuous := fun ψ =>
      completionTranslate_strong_continuous hf.pd hf.hermitian hf ψ
    compat := fun t α => completionTranslate_compat hf.pd hf.hermitian t α
  }

end SpectralBridge.Bochner.GNS
