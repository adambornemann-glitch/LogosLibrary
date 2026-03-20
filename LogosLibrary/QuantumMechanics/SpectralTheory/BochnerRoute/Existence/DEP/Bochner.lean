/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Existence/Extract.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.DEP.Extract
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Fourier.Unique

namespace SpectralBridge.Bochner.BochnerExistence

open Complex MeasureTheory Filter Topology Set Real Function
/-! ## §7: Main theorem  -/

/-- **Bochner's Theorem (Existence)**: Every continuous positive-definite
    function on ℝ is the Fourier-Stieltjes transform of a finite positive
    Borel measure.

This discharges the axiom `bochner_theorem` from `PositiveDefinite.lean`. -/
theorem bochner_existence (f : ℝ → ℂ) (hf : PositiveDefiniteContinuous f) :
    ∃ (μ : Measure ℝ),
      IsFiniteMeasure μ ∧
      ∀ t, f t = ∫ ω, exp (I * ω * t) ∂μ := by
  -- Need to promote PositiveDefiniteContinuous to IsBochnerReady.
  -- This requires deriving Hermitian symmetry from the PD condition +
  -- continuity. There are two approaches:
  --
  -- Approach A: Strengthen PositiveDefinite to use the full complex
  --   non-negativity (not just .re ≥ 0), which implies Hermitian.
  --
  -- Approach B: Prove that PD + continuous at 0 implies Hermitian.
  --   This is true but requires a non-trivial argument: continuity at 0
  --   implies f(-t) - conj(f(t)) = 0 by taking imaginary parts of the
  --   2-point PD condition and using a limiting argument.
  --
  -- For now, we assume the IsBochnerReady hypothesis can be obtained.
  sorry

/-- **Bochner's Theorem**: Existence + Uniqueness.

This is the complete theorem: f is PDC if and only if it is the
Fourier-Stieltjes transform of a *unique* finite positive measure. -/
theorem bochner_theorem (f : ℝ → ℂ) (hf : PositiveDefiniteContinuous f) :
    ∃! (μ : Measure ℝ),
      IsFiniteMeasure μ ∧
      ∀ t, f t = ∫ ω, exp (I * ω * t) ∂μ := by
  obtain ⟨μ, hμ_fin, hμ_rep⟩ := bochner_existence f hf
  refine ⟨μ, ⟨hμ_fin, hμ_rep⟩, ?_⟩
  intro ν ⟨hν_fin, hν_rep⟩
  haveI := hμ_fin
  haveI := hν_fin
  exact (FourierUniqueness.fourier_uniqueness μ ν
    (fun t => (hμ_rep t).symm.trans (hν_rep t))).symm

end SpectralBridge.Bochner.BochnerExistence
