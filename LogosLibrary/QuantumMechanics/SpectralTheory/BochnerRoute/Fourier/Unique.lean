/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Fourier/Unique.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Fourier.ContPoints

namespace SpectralBridge.Bochner.FourierUniqueness

open Complex MeasureTheory Filter Topology Set


/-! ## §7: The main theorem -/

/-- **Fourier Uniqueness Theorem**: A finite positive Borel measure on ℝ is
    uniquely determined by its characteristic function.

This replaces the axiom `measure_eq_of_fourier_eq` in `PositiveDefinite.lean`. -/
theorem fourier_uniqueness (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, ∫ ω, exp (I * ↑ω * ↑t) ∂μ = ∫ ω, exp (I * ↑ω * ↑t) ∂ν) :
    μ = ν := by
  apply MeasureTheory.Measure.ext_of_Ioc
  intro a b hab
  exact measure_Ioc_eq_of_fourier_eq' μ ν h a b hab


end SpectralBridge.Bochner.FourierUniqueness
