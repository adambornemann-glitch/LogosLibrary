/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Existence/Approx/Defs.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.Fejer
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Continuity

namespace SpectralBridge.Bochner.BochnerExistence

open SpectralBridge.Bochner
open Complex MeasureTheory Filter Topology Set Real Function

variable {f : ℝ → ℂ}


/-! ## §2: The approximate spectral density -/

/-- The approximate spectral density (Bochner–Fejér approximant):

`Λ_T(ω) = (1/2π) ∫_{-T}^{T} (1 - |t|/T) f(t) e^{-iωt} dt`

This is the Fourier transform of the windowed function `w_T · f`.
For positive-definite f, this is a non-negative real-valued function. -/
noncomputable def approxDensity (f : ℝ → ℂ) (T : ℝ) (ω : ℝ) : ℂ :=
  (1 / (2 * ↑Real.pi)) * ∫ t, (↑(fejerWeight T t) : ℂ) * f t * exp (-I * ↑ω * ↑t)


/-! ### Riemann sum machinery for the PD non-negativity argument -/

/-- Riemann sum for a double integral on [0,T]². -/
noncomputable def riemannDoubleSum (F : ℝ → ℝ → ℂ) (T : ℝ) (N : ℕ) : ℂ :=
  (↑T / (↑N : ℂ)) ^ 2 *
    ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
      F (↑j * T / ↑N) (↑k * T / ↑N)


/-- Extract the real-valued version. -/
noncomputable def approxDensityReal (f : ℝ → ℂ) (T : ℝ) (ω : ℝ) : ℝ :=
  (approxDensity f T ω).re


end SpectralBridge.Bochner.BochnerExistence
