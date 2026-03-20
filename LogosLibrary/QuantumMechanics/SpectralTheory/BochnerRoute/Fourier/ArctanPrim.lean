/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Fourier/ArctanPrim.lean
-/

import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Fourier.PoissonKernel.Lemmas

namespace SpectralBridge.Bochner.FourierUniqueness

open Complex MeasureTheory Filter Topology Set


/-! ## §2: Arctan primitive — the Poisson integral over an interval -/

/-- The integral of the Poisson kernel over `(a, b]` gives an arctan expression.

`∫_a^b P_ε(x - ω) dx = (1/π) [arctan((b-ω)/ε) - arctan((a-ω)/ε)]`

This is just the antiderivative of `ε/(x² + ε²)` being `arctan(x/ε)/ε`. -/
lemma poissonKernel_integral_Ioc {ε : ℝ} (hε : 0 < ε) (ω a b : ℝ) (hab : a < b) :
    ∫ x in Set.Ioc a b, poissonKernel ε (x - ω) =
    (1 / Real.pi) * (Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε)) := by
  -- Convert Ioc set integral to interval integral (they agree when a ≤ b)
  rw [← intervalIntegral.integral_of_le hab.le]
  -- Antiderivative: F(x) = (1/π) · arctan((x - ω)/ε), F' = poissonKernel ε (· - ω)
  have h_deriv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x => (1 / Real.pi) * Real.arctan ((x - ω) / ε))
                 (poissonKernel ε (x - ω)) x := by
    intro x _
    -- Chain rule: d/dx [(1/π) arctan((x-ω)/ε)] = (1/π) · (1+((x-ω)/ε)²)⁻¹ · (1/ε)
    convert ((Real.hasDerivAt_arctan ((x - ω) / ε)).comp x
      (((hasDerivAt_id x).sub_const ω).div_const ε)).const_mul (1 / Real.pi) using 1
    unfold poissonKernel
    have : 0 < (x - ω) ^ 2 + ε ^ 2 := sq_add_sq_pos hε (x - ω)
    field_simp
    ring
  have h_int : IntervalIntegrable (fun x => poissonKernel ε (x - ω)) volume a b :=
    ContinuousOn.intervalIntegrable
      ((poissonKernel_continuous hε).comp (continuous_id.sub continuous_const)).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int]
  ring

/-- The "arctan recovery function": for fixed ε > 0, the function
    `ω ↦ (1/π)[arctan((b-ω)/ε) - arctan((a-ω)/ε)]`
    is bounded between 0 and 1 and converges to `1_{(a,b]}(ω)` as ε → 0⁺. -/
noncomputable def arctanRecovery (ε : ℝ) (a b : ℝ) (ω : ℝ) : ℝ :=
  (1 / Real.pi) * (Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε))

/-- The arctan recovery function is non-negative. -/
lemma arctanRecovery_nonneg {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (hab : a < b) (ω : ℝ) :
    0 ≤ arctanRecovery ε a b ω := by
  unfold arctanRecovery
  apply mul_nonneg
  · simp only [one_div, inv_nonneg, Real.pi_nonneg]
  · apply sub_nonneg.mpr
    apply Real.arctan_mono
    apply div_le_div_of_nonneg_right
    · linarith
    · exact le_of_lt hε

/-- The arctan recovery function is bounded above by 1. -/
lemma arctanRecovery_le_one {ε : ℝ} (_hε : 0 < ε) {a b : ℝ} (_hab : a < b) (ω : ℝ) :
    arctanRecovery ε a b ω ≤ 1 := by
  unfold arctanRecovery
  have hπ := Real.pi_pos
  -- arctan ∈ (-π/2, π/2), so any difference of two arctans is strictly < π
  have h_diff_le : Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε) ≤ Real.pi :=
    le_of_lt (by linarith [Real.arctan_lt_pi_div_two ((b - ω) / ε),
                            Real.neg_pi_div_two_lt_arctan ((a - ω) / ε)])
  calc (1 / Real.pi) * (Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε))
      ≤ (1 / Real.pi) * Real.pi := by
        exact mul_le_mul_of_nonneg_left h_diff_le (by positivity)
    _ = 1 := one_div_mul_cancel (ne_of_gt hπ)

/-- The arctan recovery function is measurable. -/
lemma arctanRecovery_measurable {ε : ℝ} (_hε : 0 < ε) (a b : ℝ) :
    Measurable (arctanRecovery ε a b) := by
  unfold arctanRecovery
  fun_prop

/-! ### Helpers: division by ε → 0⁺ sends constants to ±∞ -/

/-- If `c > 0`, then `c / ε → +∞` as `ε → 0⁺`. -/
lemma tendsto_pos_div_zero_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ε => c / ε) (𝓝[>] (0 : ℝ)) atTop := by
  have hinv : Tendsto (·⁻¹ : ℝ → ℝ) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
  rw [Filter.tendsto_atTop] at hinv ⊢
  intro M
  filter_upwards [hinv (M / c)] with ε hε
  calc M = c * (M / c) := by field_simp
    _ ≤ c * ε⁻¹ := by apply mul_le_mul_of_nonneg_left hε hc.le
    _ = c / ε := by rw [div_eq_mul_inv]

/-- If `c < 0`, then `c / ε → -∞` as `ε → 0⁺`. -/
lemma tendsto_neg_div_zero_atBot {c : ℝ} (hc : c < 0) :
    Tendsto (fun ε => c / ε) (𝓝[>] (0 : ℝ)) atBot := by
  have key : Tendsto (fun ε => (-c) / ε) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_pos_div_zero_atTop (neg_pos.mpr hc)
  have : Tendsto (fun ε => -((-c) / ε)) (𝓝[>] (0 : ℝ)) atBot :=
    Filter.tendsto_neg_atTop_atBot.comp key
  convert this using 1; ext ε; simp [neg_div]


end SpectralBridge.Bochner.FourierUniqueness
