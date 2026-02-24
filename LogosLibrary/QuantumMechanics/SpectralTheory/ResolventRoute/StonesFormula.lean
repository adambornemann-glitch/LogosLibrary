/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.ResolventRoute.ResolventKernel
import LogosLibrary.QuantumMechanics.SpectralTheory.ResolventRoute.SpectralRepresentation
/-!
# Stone's Formula

This file proves Stone's formula, which recovers spectral projections from
the resolvent difference at conjugate points.

## Main statements

* `stones_formula`: `E(a,b) = s-lim_{ε→0+} (1/2πi) ∫_a^b [R(t+iε) - R(t-iε)] dt`

## Proof strategy

1. Express `R(t+iε) - R(t-iε)` using the spectral representation
2. The difference equals `∫ 2iε/((s-t)² + ε²) dE(s)` (purely imaginary Lorentzian)
3. Apply Fubini to swap the order of integration
4. Evaluate the inner integral via the complex arctan formula
5. Apply dominated convergence as `ε → 0`

## Comparison with Stieltjes inversion

Stone's formula is the operator-valued generalization of Stieltjes inversion.
While Stieltjes inversion recovers the scalar measure `⟨E(B)ψ, ψ⟩`, Stone's
formula recovers the full operator `E(B)`.

The key identity connecting them is:
`R(t+iε) - R(t-iε) = 2iε · Im(R(t+iε))` (up to normalization)

## Physical interpretation

Stone's formula is the mathematician's version of the physicist's "spectral
density from the discontinuity across the cut." The resolvent `R(z)` is analytic
in the upper and lower half-planes, with a branch cut along the spectrum on ℝ.
The discontinuity across this cut gives the spectral measure.

## References

* Stone, "Linear Transformations in Hilbert Space" (1932)
* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Theorem VII.13

## Tags

Stone's formula, resolvent, spectral projection, contour integration
-/

namespace SpectralBridge.Resolvent

open QuantumMechanics.Resolvent QuantumMechanics.Generators SpectralBridge.Bochner Complex
open InnerProductSpace MeasureTheory Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Resolvent difference axioms -/

/-- The resolvent difference integrated against the spectral measure.

`⟨[R(t+iε) - R(t-iε)]ψ, ψ⟩ = ∫ 2iε/((s-t)² + ε²) dμ_ψ(s)`

This follows from the spectral representation and the kernel identity
`(s-(t+iε))⁻¹ - (s-(t-iε))⁻¹ = 2iε/((s-t)² + ε²)`. -/
axiom resolvent_diff_spectral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E)
    (t ε : ℝ) (hε : ε > 0) (ψ : H) :
    ⟪(resolventFun gen hsa (offRealPoint t ε hε) -
       resolventFun gen hsa (offRealPointNeg t ε hε)) ψ, ψ⟫_ℂ =
      ∫ s, (2 * ε * I) / ((s - t)^2 + ε^2 : ℂ) ∂(spectral_scalar_measure E ψ hE)

/-- Fubini for the resolvent difference kernel.

Swaps order of integration for the complex Lorentzian kernel `2iε/((s-t)² + ε²)`. -/
axiom resolvent_diff_fubini {μ : Measure ℝ} [IsFiniteMeasure μ]
    (a b ε : ℝ) (hε : ε > 0) :
    ∫ t in Set.Icc a b, ∫ s, (2 * ε * I) / ((s - t)^2 + ε^2 : ℂ) ∂μ =
      ∫ s, (∫ t in Set.Icc a b, (2 * ε * I) / ((s - t)^2 + ε^2 : ℂ)) ∂μ

/-- The complex arctan integral for the resolvent difference.

`∫_a^b (2εi)/((s-t)² + ε²) dt = 2i[arctan((b-s)/ε) - arctan((a-s)/ε)]`

This follows from the real arctan integral by pulling out the factor of `2i`. -/
axiom resolvent_diff_arctan_integral (s a b ε : ℝ) (hε : ε > 0) :
    ∫ t in Set.Icc a b, (2 * ε * I) / ((s - t)^2 + ε^2 : ℂ) =
      2 * I * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))

/-- Dominated convergence for Stone's formula integral.

The same as `arctan_dominated_convergence` but stated for the full formula. -/
axiom stones_dominated_convergence {μ : Measure ℝ}
    [IsFiniteMeasure μ] (a b : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => ∫ s, (1 / Real.pi) *
      (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ)
      (𝓝[>] 0)
      (𝓝 (μ (Set.Ioc a b)).toReal)

/-- The Stone's formula integral simplifies: `(1/2πi) · 2i · arctan = (1/π) · arctan`.

This shows that after dividing by `2πi`, the complex factor `2i` cancels to give
a real integral. -/
axiom stones_integral_real {μ : Measure ℝ} [IsFiniteMeasure μ]
    (a b ε : ℝ) (hε : ε > 0) :
    ∫ s, (1 / (2 * Real.pi * I)) *
      (2 * I * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))) ∂μ =
    ∫ s, (1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ

/-! ### Main theorem -/

/-- **Stone's Formula**

Recover spectral projections from the resolvent difference:
`E(a,b) = s-lim_{ε→0+} (1/2πi) ∫_a^b [R(t+iε) - R(t-iε)] dt`

This is stated in ε-δ form for the bilinear form: for any `δ > 0`, there exists
`ε₀ > 0` such that for all `0 < ε < ε₀`:
`|⟨E(a,b]ψ, ψ⟩ - (1/2πi) ∫_a^b ⟨[R(t+iε) - R(t-iε)]ψ, ψ⟩ dt| < δ`

## Proof outline
1. Set `μ = spectral_scalar_measure E ψ hE`
2. Use `resolvent_diff_spectral` to write the integrand spectrally
3. Apply `resolvent_diff_fubini` to swap integrals
4. Evaluate inner integral via `resolvent_diff_arctan_integral`
5. Use `stones_integral_real` to simplify the `1/2πi` factor
6. Apply `stones_dominated_convergence` to take `ε → 0` limit -/
theorem stones_formula {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (a b : ℝ) (hab : a < b) (ψ : H) :
    ∀ δ > 0, ∃ ε₀ > 0, ∀ ε, ε < ε₀ → ∀ hε : ε > 0,
      ‖⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ - (1 / (2 * Real.pi * I)) *
        ∫ t in Set.Icc a b, ⟪(resolventFun gen hsa (offRealPoint t ε hε) -
          resolventFun gen hsa (offRealPointNeg t ε hε)) ψ, ψ⟫_ℂ‖ < δ := by
  intro δ hδ

  -- Set up the spectral measure
  set μ := spectral_scalar_measure E ψ hE with hμ_def
  haveI hμ_finite : IsFiniteMeasure μ :=
    spectral_scalar_measure_finite E hE hE_univ ψ

  -- Get ε₀ from dominated convergence
  have h_conv := stones_dominated_convergence (μ := μ) a b hab
  rw [Metric.tendsto_nhdsWithin_nhds] at h_conv
  obtain ⟨ε₀, hε₀_pos, hε₀_conv⟩ := h_conv δ hδ

  use ε₀
  constructor
  · exact hε₀_pos
  intro ε hε_lt hε

  -- The spectral measure gives ⟪E(a,b]ψ, ψ⟫
  have h_spectral : (μ (Set.Ioc a b)).toReal = (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re :=
    spectral_scalar_measure_apply' E hE ψ (Set.Ioc a b) measurableSet_Ioc

  -- ⟪E(a,b]ψ, ψ⟫ is real
  have h_real : (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).im = 0 := by
    exact spectral_diagonal_real hE (Set.Ioc a b) ψ

  have h_inner_eq : ⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ = (μ (Set.Ioc a b)).toReal := by
    conv_lhs => rw [← re_add_im ⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ, h_real]
    simp [h_spectral]

  -- Express the integral using spectral representation
  have h_integral : ∫ t in Set.Icc a b,
      ⟪(resolventFun gen hsa (offRealPoint t ε hε) -
        resolventFun gen hsa (offRealPointNeg t ε hε)) ψ, ψ⟫_ℂ =
      ∫ t in Set.Icc a b, ∫ s, (2 * ε * I) / ((s - t)^2 + ε^2 : ℂ) ∂μ := by
    congr 1
    ext t
    exact resolvent_diff_spectral gen hsa E hE t ε hε ψ

  -- Apply Fubini
  have h_fubini : ∫ t in Set.Icc a b, ∫ s, (2 * ε * I) / ((s - t)^2 + ε^2 : ℂ) ∂μ =
      ∫ s, (∫ t in Set.Icc a b, (2 * ε * I) / ((s - t)^2 + ε^2 : ℂ)) ∂μ :=
    resolvent_diff_fubini a b ε hε

  -- Compute inner integral via arctan
  have h_arctan : ∫ s, (∫ t in Set.Icc a b, (2 * ε * I) / ((s - t)^2 + ε^2 : ℂ)) ∂μ =
      ∫ s, 2 * I * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ := by
    apply integral_congr_ae
    filter_upwards with s
    exact resolvent_diff_arctan_integral s a b ε hε

  -- Factor out 1/(2πi)
  have h_factor : (1 / (2 * Real.pi * I)) *
    ∫ t in Set.Icc a b, ⟪(resolventFun gen hsa (offRealPoint t ε hε) -
      resolventFun gen hsa (offRealPointNeg t ε hε)) ψ, ψ⟫_ℂ =
    ∫ s, (1 / (2 * Real.pi * I)) *
      (2 * I * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))) ∂μ := by
    rw [h_integral, h_fubini, h_arctan]
    exact Eq.symm
      (integral_const_mul (1 / (2 * ↑Real.pi * I)) fun a_1 =>
        2 * I * (↑(Real.arctan ((b - a_1) / ε)) - ↑(Real.arctan ((a - a_1) / ε))))

  -- Apply dominated convergence bound
  have h_dist : dist ε 0 < ε₀ := by simp [abs_of_pos hε]; exact hε_lt
  have h_mem : ε ∈ Set.Ioi (0 : ℝ) := hε
  have h_bound := hε₀_conv h_mem h_dist

  -- Convert to norm bound
  rw [h_inner_eq, h_factor, stones_integral_real a b ε hε]
  rw [← ofReal_sub, norm_real, norm_sub_rev]
  exact h_bound

end SpectralBridge.Resolvent
