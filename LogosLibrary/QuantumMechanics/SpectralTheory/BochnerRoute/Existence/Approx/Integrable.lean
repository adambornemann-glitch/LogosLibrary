/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Existence/Approx/Density.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.Approx.Density

namespace SpectralBridge.Bochner.BochnerExistence

open SpectralBridge.Bochner
open Complex MeasureTheory Filter Topology Set Real Function

variable {f : ℝ → ℂ}


/-- **Integrability of the approximate spectral density** `Λ_T ∈ L¹(ℝ)`.

`Λ_T(ω) = (1/2π) ∫_{-T}^{T} (1 - |t|/T) f(t) e^{-iωt} dt` is the Fourier
transform of the compactly supported function `h(t) = w_T(t) · f(t)`, where
`w_T` is the Fejér weight. Since `h` is continuous with support in `[-T, T]`,
it lies in `L¹(ℝ) ∩ L²(ℝ)`. The integrability of its Fourier transform `Λ_T`
would follow from any of the standard routes below.

### Why this is blocked

Every known proof strategy reduces to Fourier-analytic infrastructure that
Mathlib does not yet possess (as of v4.29):

1. **Plancherel + Riemann-Lebesgue**: `h ∈ L²` implies `Λ_T ∈ L²` by
   Plancherel. Combined with `Λ_T ∈ L^∞` (Riemann-Lebesgue) and
   `Λ_T ≥ 0` (proved in `approxDensity_nonneg`), one obtains
   `Λ_T ∈ L¹` via `‖Λ_T‖₁ ≤ ‖Λ_T‖₂ · ‖Λ_T‖_∞^{1/2}` on compact sets
   plus `L²` tail decay. **Blocked on**: `Mathlib.Analysis.Fourier.Plancherel`.

2. **Integration by parts for decay**: The Fejér-windowed function `h` is
   piecewise `C¹` (with corners at `t = 0, ±T`), so one integration by
   parts gives `|Λ_T(ω)| = O(1/|ω|)` — not integrable. A second
   derivative does not exist classically. Splitting `h` as a convolution
   of rectangles gives `|Λ_T(ω)| = O(1/ω²)` (since `Λ_T` is the squared
   Fejér kernel times a smooth correction), but formalizing this requires
   either the convolution theorem or direct Fourier decay estimates for
   piecewise-smooth functions, neither of which is in Mathlib.

3. **Direct Fubini with regularization**: Insert a convergence factor
   `e^{-ε|ω|}` to make `∫_ω Λ_T(ω) dω` absolutely convergent, compute
   via Fubini + the Poisson kernel machinery from `FourierUniqueness/`,
   then take `ε → 0`. This would give the total mass `∫ Λ_T = f(0).re`
   (hence finiteness), but the limit interchange requires either monotone
   convergence (which needs `Λ_T ≥ 0` — proved — plus measurability of
   the `ε`-regularized integral) or dominated convergence (which needs
   the very integrability we are trying to prove).

### Downstream impact

This lemma is **not required** for the main Bochner existence theorem when
the proof proceeds via the GNS–Stone–Spectral route (see `Existence/GNS/`).
It IS required for the classical Fejér approximation route, which constructs
the representing measure as a weak-* limit of the densities `Λ_T dω`.

The lemma is retained as a natural companion result. It will follow
immediately once Mathlib acquires either Plancherel's theorem or an `L¹`
Fourier inversion theorem.

### See also

* `poissonKernel_fourier` in `Kernel.lean` — a similar infrastructure gap
* `approxDensity_nonneg` — the non-negativity that would combine with
  Plancherel to give this result
* `approxDensity_total_mass` in `Mass.lean` — the total mass computation
  that is similarly blocked

### References

* Rudin, *Real and Complex Analysis*, 3rd ed., §9.12 (Plancherel)
* Katznelson, *An Introduction to Harmonic Analysis*, Ch. VI
* Stein & Shakarchi, *Fourier Analysis*, Ch. 5 -/
lemma approxDensityReal_integrable (hf : IsContinuous f)
    {T : ℝ} (hT : 0 < T) :
    Integrable (approxDensityReal f T) volume := by
  sorry

end SpectralBridge.Bochner.BochnerExistence
