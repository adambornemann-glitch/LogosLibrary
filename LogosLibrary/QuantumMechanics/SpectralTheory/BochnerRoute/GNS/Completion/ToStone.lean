/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/GNS/Completion/ToStone.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.GNS.Completion.StronglyEx
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.GNS.Completion.Cyclic

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp Filter Topology

/-- The GNS unitary group satisfies all the axioms of a
    `OneParameterUnitaryGroup`.

This provides the input to Stone's theorem. The output of Stone
gives a self-adjoint generator A, and the spectral theorem then
produces the representing measure.

Note: the exact packaging depends on the `OneParameterUnitaryGroup`
structure from `UnitaryEvo/Generator.lean`. The map is:
  - `U : ℝ → H →L[ℂ] H`   from   `unitaryAction`
  - `unitary t ψ φ`         from   `isometry t ψ φ`
  - `group_law s t`          from   `group_law s t`
  - `identity`               from   `identity`
  - `strong_continuous`      from   `strong_continuous`
-/
noncomputable def toOneParameterUnitaryGroup {f : ℝ → ℂ}
    (gns : GNSUnitaryGroup f) :
    @QuantumMechanics.Generators.OneParameterUnitaryGroup gns.H
      gns.instNACG gns.instIPS := by
  letI := gns.instNACG
  letI := gns.instIPS
  haveI := gns.instComplete
  -- Each U(t) preserves norms (from inner product isometry)
  have hnorm : ∀ (t : ℝ) (ψ : gns.H), ‖gns.unitaryAction t ψ‖ = ‖ψ‖ := by
    intro t ψ
    have h := gns.isometry t ψ ψ
    rw [@inner_self_eq_norm_sq_to_K ℂ, @inner_self_eq_norm_sq_to_K ℂ] at h
    have h_sq : ‖gns.unitaryAction t ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by exact_mod_cast h
    nlinarith [sq_nonneg (‖gns.unitaryAction t ψ‖ - ‖ψ‖),
               sq_nonneg (‖gns.unitaryAction t ψ‖ + ‖ψ‖),
               norm_nonneg (gns.unitaryAction t ψ), norm_nonneg ψ]
  -- Promote each LinearMap to a ContinuousLinearMap via the norm bound
  set U : ℝ → (gns.H →L[ℂ] gns.H) := fun t =>
    (gns.unitaryAction t).mkContinuous 1 (fun ψ => by rw [hnorm, one_mul])
  exact {
    U := U
    unitary := fun t ψ φ => by
      simp only [U, LinearMap.mkContinuous_apply]
      exact gns.isometry t ψ φ
    group_law := fun s t => ContinuousLinearMap.ext fun ψ => by
      simp only [U, LinearMap.mkContinuous_apply, ContinuousLinearMap.comp_apply]
      exact (gns.group_law s t ψ)
    identity := ContinuousLinearMap.ext fun ψ => by
      simp only [U, LinearMap.mkContinuous_apply, ContinuousLinearMap.id_apply]
      exact gns.identity ψ
    strong_continuous := fun ψ => by
      exact (gns.strong_continuous ψ).congr fun t => by
        simp only [U, LinearMap.mkContinuous_apply]
  }

end SpectralBridge.Bochner.GNS
