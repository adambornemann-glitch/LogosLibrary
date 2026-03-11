/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann, with architecture by Claude (Anthropic)
Filename: BochnerRoute/FourierUniqueness.lean
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Integral.Bochner.Set

import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.PositiveDefinite
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.PdProperties

/-!
# Fourier Uniqueness for Finite Measures

A finite positive Borel measure on ℝ is uniquely determined by its
characteristic function (Fourier–Stieltjes transform).

This file discharges the axiom `measure_eq_of_fourier_eq` from
`PositiveDefinite.lean`.

## Main result

* `fourier_uniqueness`: If `∀ t, ∫ e^{iωt} dμ = ∫ e^{iωt} dν`, then `μ = ν`.

## Proof strategy — Poisson regularization

We use the Poisson/Lorentzian kernel `P_ε(x) = (1/π) · ε/(x² + ε²)`,
whose Fourier transform is `e^{-ε|t|}`. This connects the characteristic
function to the distribution function via:

```
∫_a^b (P_ε * μ)(s) ds  =  ∫ [arctan((b-ω)/ε) - arctan((a-ω)/ε)] / π  dμ(ω)
```

The left side depends only on the characteristic function (via Fubini),
and the right side converges to `μ(a,b]` as `ε → 0⁺` (by DCT + arctan limits).

So same characteristic function ⟹ same values on `(a,b]` ⟹ same measure
(via `Measure.ext_of_Ioc`).

## Architecture

```
§1  Lorentzian kernel: definition, properties, Fourier transform
§2  Arctan primitive: ∫_a^b P_ε(x-ω) dx = [arctan]/π
§3  Poisson–Fourier bridge: Poisson integral from characteristic function
§4  Arctan limits: recovery of 1_{(a,b]} as ε → 0
§5  Distribution function agreement at continuity points
§6  Extension to all (a,b] via right-continuity
§7  Main theorem via Measure.ext_of_Ioc
```

## References

* Lévy, P. "Calcul des Probabilités" (1925), §24 (inversion formula)
* Rudin, *Real and Complex Analysis*, 3rd ed., §9.5
* Connects to `lorentzian` already defined in `Routes.lean`

## Tags

Fourier uniqueness, characteristic function, Lévy inversion, Poisson kernel
-/

namespace SpectralBridge.Bochner.FourierUniqueness

open Complex MeasureTheory Filter Topology Set



/-! ## §1: The Lorentzian/Poisson kernel -/

/-- The Poisson kernel (normalized Lorentzian): `P_ε(x) = (1/π) · ε/(x² + ε²)`.
This is a probability density on ℝ for each ε > 0. -/
noncomputable def poissonKernel (ε : ℝ) (x : ℝ) : ℝ :=
  (1 / Real.pi) * (ε / (x ^ 2 + ε ^ 2))

/-- The Poisson kernel is non-negative for ε > 0. -/
lemma poissonKernel_nonneg {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 ≤ poissonKernel ε x := by
  unfold poissonKernel
  apply mul_nonneg
  · simp only [one_div, inv_nonneg, Real.pi_nonneg]
  · apply div_nonneg hε.le
    exact add_nonneg (sq_nonneg x) (sq_nonneg ε)

/-- The denominator `x² + ε²` is strictly positive for ε > 0. -/
lemma sq_add_sq_pos {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 < x ^ 2 + ε ^ 2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos hε)

/-- The Poisson kernel is measurable. -/
lemma poissonKernel_measurable {ε : ℝ} (_hε : 0 < ε) :
    Measurable (poissonKernel ε) := by
  unfold poissonKernel
  fun_prop

/-- The Poisson kernel is continuous. -/
lemma poissonKernel_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (poissonKernel ε) := by
  unfold poissonKernel
  apply Continuous.mul continuous_const
  apply Continuous.div continuous_const
  · exact (continuous_pow 2 |>.add continuous_const)
  · intro x; exact ne_of_gt (sq_add_sq_pos hε x)

/-- `x ↦ (1 + x²)⁻¹` is continuous on ℝ. -/
private lemma continuous_inv_one_add_sq :
    Continuous (fun x : ℝ => (1 + x ^ 2)⁻¹) := by
  apply Continuous.inv₀
  · exact continuous_const.add (continuous_pow 2)
  · intro x; positivity

/-- `x ↦ (1 + x²)⁻¹` is integrable on ℝ.

On `[-1,1]` it's continuous on a compact set. On `|x| > 1` it decays as `x⁻²`. -/
private lemma integrable_inv_one_add_sq :
    Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) volume := by
  -- ∫ |f| ≤ ∫_{[-1,1]} 1 + 2·∫_1^∞ x⁻² < ∞
  -- Clean approach: continuous + dominated by an L¹ function
  rw [← integrableOn_univ]
  rw [show (univ : Set ℝ) = Icc (-1) 1 ∪ (Icc (-1) 1)ᶜ from (union_compl_self _).symm]
  apply IntegrableOn.union
  · -- On [-1, 1]: continuous on compact → integrable
    exact continuous_inv_one_add_sq.continuousOn.integrableOn_compact isCompact_Icc
  · -- On the complement: 0 ≤ (1+x²)⁻¹ ≤ x⁻² and ∫ x⁻² < ∞ on |x|≥1
    sorry
    -- Path to discharge:
    --   • Show (1+x²)⁻¹ ≤ x⁻² for |x| ≥ 1  (since x² ≤ x²+1)
    --   • (Icc (-1) 1)ᶜ = Iio (-1) ∪ Ioi 1
    --   • On Ioi 1: use `integrableOn_Ioi_rpow_of_lt` with p = -2 < -1
    --     or `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto` with F = -1/x
    --   • On Iio (-1): by symmetry (or `integrableOn_Iic_rpow_of_lt`)
    --   • Conclude by IntegrableOn.mono with the bound
#check integrableOn_Ioi_rpow_of_lt
/-integrableOn_Ioi_rpow_of_lt {a c : ℝ} (ha : a < -1) (hc : 0 < c) : IntegrableOn (fun t => t ^ a) (Ioi c) volume-/
#check MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
/-MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto.{u_1} {E : Type u_1} {f f' : ℝ → E} {a : ℝ} {m : E}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (hcont : ContinuousWithinAt f (Ici a) a)
  (hderiv : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Ioi a) volume) (hf : Tendsto f atTop (𝓝 m)) :
  ∫ (x : ℝ) in Ioi a, f' x = m - f a-/

-- Unknown identifier `integrableOn_Iic_rpow_of_lt`

/-- The full-line Bochner integral: `∫ x : ℝ, (1 + x²)⁻¹ = π`.

Proof:
  1. For integrable `f`, `∫ x in -R..R, f x → ∫ x, f x` as `R → ∞`.
  2. By `integral_inv_one_add_sq`, the interval integral = `arctan R - arctan(-R)`.
  3. This tends to `π/2 - (-π/2) = π`.
  4. Uniqueness of limits. -/
private lemma integral_inv_one_add_sq_eq_pi :
    ∫ x : ℝ, (1 + x ^ 2)⁻¹ = Real.pi := by
  -- (1) Bochner integral = limit of symmetric interval integrals
  have h_int := integrable_inv_one_add_sq
  have h_bochner_lim : Tendsto (fun R : ℝ => ∫ x in (-R)..R, (1 + x ^ 2)⁻¹)
      atTop (𝓝 (∫ x, (1 + x ^ 2)⁻¹)) :=
    intervalIntegral_tendsto_integral h_int tendsto_neg_atTop_atBot tendsto_id
  -- (2) Evaluate each interval integral via arctan
  have h_interval : ∀ R : ℝ, ∫ x in (-R)..R, (1 + x ^ 2)⁻¹ =
      Real.arctan R - Real.arctan (-R) :=
    fun R => integral_inv_one_add_sq
  -- (3) arctan R - arctan(-R) → π/2 - (-π/2) = π
  have h_arctan_lim : Tendsto (fun R : ℝ => Real.arctan R - Real.arctan (-R))
      atTop (𝓝 Real.pi) := by
    have := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).sub
      ((Real.tendsto_arctan_atBot.comp tendsto_neg_atTop_atBot).mono_right nhdsWithin_le_nhds)
    rwa [show Real.pi / 2 - -(Real.pi / 2) = Real.pi from by ring] at this
  -- (4) Chain: Bochner integral has limit π
  have h_pi_lim : Tendsto (fun R : ℝ => ∫ x in (-R)..R, (1 + x ^ 2)⁻¹)
      atTop (𝓝 Real.pi) := by
    simp_rw [h_interval]; exact h_arctan_lim
  exact tendsto_nhds_unique h_bochner_lim h_pi_lim

/-- The Poisson kernel is integrable on ℝ. Proved by showing that
    ∫_{-n}^{n} P_ε converges (to 1) via the arctan antiderivative. -/
lemma poissonKernel_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (poissonKernel ε) volume := by
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  -- Antiderivative: d/dx [(1/π) arctan(x/ε)] = P_ε(x)
  have h_deriv : ∀ x : ℝ, HasDerivAt (fun x => (1 / Real.pi) * Real.arctan (x / ε))
      (poissonKernel ε x) x := by
    intro x
    convert ((Real.hasDerivAt_arctan (x / ε)).comp x
      ((hasDerivAt_id x).div_const ε)).const_mul (1 / Real.pi) using 1
    unfold poissonKernel; field_simp; ring
  -- FTC: ∫_{a}^{b} P_ε = (1/π)(arctan(b/ε) - arctan(a/ε))
  have h_FTC : ∀ a b : ℝ, ∫ x in a..b, poissonKernel ε x =
      (1 / Real.pi) * Real.arctan (b / ε) -
      (1 / Real.pi) * Real.arctan (a / ε) :=
    fun a b => intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => h_deriv x)
      (poissonKernel_continuous hε).continuousOn.intervalIntegrable
  -- Filter helper: ↑n / ε → +∞ as n → ∞
  have h_nat_div : Tendsto (fun n : ℕ => (n : ℝ) / ε) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b; exact ⟨⌈b * ε⌉₊ + 1, fun n hn => by
      rw [le_div_iff₀ hε]
      exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (by omega))⟩
  -- Apply the convergent-interval-integrals criterion
  apply integrable_of_intervalIntegral_norm_tendsto (l := atTop) (μ := volume)
    (a := fun n : ℕ => -(n : ℝ)) (b := fun n : ℕ => (n : ℝ))
  · -- hfi: IntervalIntegrable for each n
    intro n
    exact ((poissonKernel_continuous hε).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  · -- ha: -(n : ℝ) → -∞
    exact tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  · -- hb: (n : ℝ) → +∞
    exact tendsto_natCast_atTop_atTop
  · -- h: ∫_{-n}^{n} ‖P_ε‖ → 1
    have h_eq : ∀ n : ℕ,
        ∫ x in (-(n:ℝ))..(n:ℝ), ‖poissonKernel ε x‖ =
        (1 / Real.pi) * Real.arctan ((n:ℝ) / ε) -
        (1 / Real.pi) * Real.arctan (-(n:ℝ) / ε) := by
      intro n
      have h_norm : ∫ x in (-(n:ℝ))..(n:ℝ), ‖poissonKernel ε x‖ =
          ∫ x in (-(n:ℝ))..(n:ℝ), poissonKernel ε x := by
        apply intervalIntegral.integral_congr
        intro x _
        simp only [Real.norm_eq_abs, abs_eq_self]
        exact poissonKernel_nonneg hε x
      rw [h_norm, h_FTC]
    simp_rw [h_eq]
    -- Goal: (1/π) arctan(n/ε) - (1/π) arctan(-n/ε) → 1
    have h_top := (tendsto_const_nhds (x := 1 / Real.pi)).mul
      ((Real.tendsto_arctan_atTop.comp h_nat_div).mono_right nhdsWithin_le_nhds)
    have h_bot := (tendsto_const_nhds (x := 1 / Real.pi)).mul
      ((Real.tendsto_arctan_atBot.comp
        ((tendsto_neg_atTop_atBot.comp h_nat_div).congr
          (fun _ => (neg_div _ _).symm))).mono_right nhdsWithin_le_nhds)
    have h_bot := (tendsto_const_nhds (x := 1 / Real.pi)).mul
      ((Real.tendsto_arctan_atBot.comp
        ((tendsto_neg_atTop_atBot.comp h_nat_div).congr
          (fun _ => (neg_div _ _).symm))).mono_right nhdsWithin_le_nhds)
    convert h_top.sub h_bot using 1

/-- **Poisson kernel integrates to 1**: `∫ P_ε(x) dx = 1`.

Strategy: rewrite `(1/π) · ε/(x²+ε²) = (1/(πε)) · (1+(x/ε)²)⁻¹`,
substitute `u = x/ε`, use `∫ (1+u²)⁻¹ = π`, cancel. -/
lemma poissonKernel_integral_eq_one {ε : ℝ} (hε : 0 < ε) :
    ∫ x, poissonKernel ε x = 1 := by
  -- ── Step 0: Integrability (needed for intervalIntegral_tendsto_integral) ──
  have h_int : Integrable (poissonKernel ε) volume := poissonKernel_integrable hε
  -- ── Step 1: Bochner integral = limit of symmetric interval integrals ──
  have h_lim : Tendsto (fun R : ℝ => ∫ x in (-R)..R, poissonKernel ε x)
      atTop (𝓝 (∫ x, poissonKernel ε x)) :=
    intervalIntegral_tendsto_integral h_int tendsto_neg_atTop_atBot tendsto_id
  -- ── Step 2: Antiderivative of poissonKernel ε is (1/π) · arctan(x/ε) ──
  -- The derivative: d/dx [(1/π) · arctan(x/ε)] = (1/π) · (1/ε) · (1+(x/ε)²)⁻¹
  --   = (1/π) · ε/(x²+ε²) = poissonKernel ε x
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have h_deriv : ∀ x : ℝ, HasDerivAt (fun x => (1 / Real.pi) * Real.arctan (x / ε))
      (poissonKernel ε x) x := by
    intro x
    have h1 : HasDerivAt (· / ε) (1 / ε) x := (hasDerivAt_id x).div_const ε
    have h2 : HasDerivAt Real.arctan ((1 + (x / ε) ^ 2)⁻¹) (x / ε) :=
      Real.hasDerivAt_arctan' (x / ε)
    have h3 := h2.comp x h1
    have h4 : HasDerivAt (fun x => (1 / Real.pi) * Real.arctan (x / ε))
        ((1 / Real.pi) * ((1 + (x / ε) ^ 2)⁻¹ * (1 / ε))) x :=
      h3.const_mul (1 / Real.pi)
    -- Now show the derivatives are equal algebraically
    convert h4 using 1
    unfold poissonKernel
    have h_pos := sq_add_sq_pos hε x
    field_simp; ring
  -- ── Step 3: Evaluate each interval integral via FTC ──
  have h_interval : ∀ R : ℝ, ∫ x in (-R)..R, poissonKernel ε x =
      (1 / Real.pi) * Real.arctan (R / ε) -
      (1 / Real.pi) * Real.arctan (-R / ε) := by
    intro R
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => h_deriv x)
      (poissonKernel_continuous hε).continuousOn.intervalIntegrable
  -- ── Step 4: Take the limit as R → ∞ ──
  have h_val_lim : Tendsto (fun R : ℝ =>
      (1 / Real.pi) * Real.arctan (R / ε) -
      (1 / Real.pi) * Real.arctan (-R / ε))
      atTop (𝓝 1) := by
    have h_div_atTop : Tendsto (fun R : ℝ => R / ε) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b; exact ⟨b * ε, fun x hx => (le_div_iff₀ hε).mpr hx⟩
    have h_div_atBot : Tendsto (fun R : ℝ => -R / ε) atTop atBot :=
      (tendsto_neg_atTop_atBot.comp h_div_atTop).congr (fun R => by grind)
    have h_arctan_top := (Real.tendsto_arctan_atTop.comp h_div_atTop).mono_right
      nhdsWithin_le_nhds
    have h_top : Tendsto (fun R : ℝ => (1 / Real.pi) * Real.arctan (R / ε))
        atTop (𝓝 ((1 / Real.pi) * (Real.pi / 2))) :=
      tendsto_const_nhds.mul h_arctan_top
    have h_arctan_bot := (Real.tendsto_arctan_atBot.comp h_div_atBot).mono_right
      nhdsWithin_le_nhds
    have h_bot : Tendsto (fun R : ℝ => (1 / Real.pi) * Real.arctan (-R / ε))
        atTop (𝓝 ((1 / Real.pi) * -(Real.pi / 2))) :=
      tendsto_const_nhds.mul h_arctan_bot
    have h_sub := h_top.sub h_bot
    rw [show (1 / Real.pi) * (Real.pi / 2) - (1 / Real.pi) * -(Real.pi / 2) = 1 from by
      field_simp; ring] at h_sub; exact tendsto_ofReal_iff'.mp h_sub
  -- ── Step 5: Uniqueness of limits ──
  have h_lim2 : Tendsto (fun R : ℝ => ∫ x in (-R)..R, poissonKernel ε x)
      atTop (𝓝 1) := by
    simp_rw [h_interval]; exact h_val_lim
  exact tendsto_nhds_unique h_lim h_lim2

/-- **Fourier transform of the Poisson kernel**: `∫ P_ε(x) e^{ixt} dx = e^{-ε|t|}`.

This is the key identity connecting the Poisson kernel to characteristic functions.

Proof: compute the bilateral Laplace transform of the Lorentzian, or
use contour integration (residue at x = iε for t > 0). -/
lemma poissonKernel_fourier {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∫ x, (poissonKernel ε x : ℂ) * exp (I * ↑x * ↑t) =
    exp (-(↑ε * ↑|t|) : ℂ) := by
  sorry -- TODO: contour integration or direct computation
         -- Can also be proved via the ODE that the Fourier transform satisfies

/-! ## §2: Arctan primitive — the Poisson integral over an interval -/

/-- The integral of the Poisson kernel over `(a, b]` gives an arctan expression.

`∫_a^b P_ε(x - ω) dx = (1/π) [arctan((b-ω)/ε) - arctan((a-ω)/ε)]`

This is just the antiderivative of `ε/(x² + ε²)` being `arctan(x/ε)/ε`. -/
lemma poissonKernel_integral_Ioc {ε : ℝ} (hε : 0 < ε) (ω a b : ℝ) (hab : a < b) :
    ∫ x in Set.Ioc a b, poissonKernel ε (x - ω) =
    (1 / Real.pi) * (Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε)) := by
  sorry -- TODO: FTC with antiderivative (1/π)·arctan((x-ω)/ε)
         -- Requires HasDerivAt for arctan composition + intervalIntegral.integral_eq_sub
#check intervalIntegral.integral_eq_sub_of_hasDerivAt
/-intervalIntegral.integral_eq_sub_of_hasDerivAt.{u_3} {E : Type u_3} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
  [CompleteSpace E] {f f' : ℝ → E} (hderiv : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
  (hint : IntervalIntegrable f' volume a b) : ∫ (y : ℝ) in a..b, f' y = f b - f a-/

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
private lemma tendsto_pos_div_zero_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ε => c / ε) (𝓝[>] (0 : ℝ)) atTop := by
  have hinv : Tendsto (·⁻¹ : ℝ → ℝ) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
  rw [Filter.tendsto_atTop] at hinv ⊢
  intro M
  filter_upwards [hinv (M / c)] with ε hε
  calc M = c * (M / c) := by field_simp
    _ ≤ c * ε⁻¹ := by apply mul_le_mul_of_nonneg_left hε hc.le
    _ = c / ε := by rw [div_eq_mul_inv]

/-- If `c < 0`, then `c / ε → -∞` as `ε → 0⁺`. -/
private lemma tendsto_neg_div_zero_atBot {c : ℝ} (hc : c < 0) :
    Tendsto (fun ε => c / ε) (𝓝[>] (0 : ℝ)) atBot := by
  have key : Tendsto (fun ε => (-c) / ε) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_pos_div_zero_atTop (neg_pos.mpr hc)
  have : Tendsto (fun ε => -((-c) / ε)) (𝓝[>] (0 : ℝ)) atBot :=
    Filter.tendsto_neg_atTop_atBot.comp key
  convert this using 1; ext ε; simp [neg_div]

/-! ## §3: Poisson–Fourier bridge

The Poisson integral of a measure can be expressed via its characteristic function.
This is the step where Fubini connects the spatial and frequency representations. -/

/-- The Poisson integral of a finite measure equals a Fourier expression.

For a finite measure μ with characteristic function `φ(t) = ∫ e^{iωt} dμ`:

`∫ P_ε(s - ω) dμ(ω) = (1/2π) ∫ e^{ist} · e^{-ε|t|} · φ(t) dt`

This is the key bridge: the LHS depends on μ directly, but the RHS depends
only on the characteristic function φ. -/
lemma poisson_integral_eq_fourier (μ : Measure ℝ) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    ∫ ω, poissonKernel ε (s - ω) ∂μ =
    (1 / (2 * Real.pi)) * (∫ t : ℝ,
      (exp (I * ↑s * ↑t) * exp (-(↑ε * ↑(|t|)) : ℂ) *
       ∫ ω, exp (I * ↑ω * ↑t) ∂μ).re ∂volume) := by
  sorry -- TODO: Fubini to interchange order of integration, then apply poissonKernel_fourier
         -- Integrability: P_ε is in L¹(ℝ), μ is finite, and |e^{iωt}| = 1

/-- Corollary: two measures with the same characteristic function have the
    same Poisson integrals. -/
lemma poisson_integral_eq_of_fourier_eq (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, ∫ ω, exp (I * ↑ω * ↑t) ∂μ = ∫ ω, exp (I * ↑ω * ↑t) ∂ν)
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    ∫ ω, poissonKernel ε (s - ω) ∂μ = ∫ ω, poissonKernel ε (s - ω) ∂ν := by
  rw [poisson_integral_eq_fourier μ hε s, poisson_integral_eq_fourier ν hε s]
  congr 1; congr 1
  ext t; congr 1; congr 1
  exact h t

/-! ## §4: Arctan limits — recovering the indicator function

As `ε → 0⁺`, the arctan recovery function converges to `1_{(a,b]}` pointwise
(except possibly at the endpoints `a` and `b`). -/

/-- For `ω ∈ (a, b)` (strictly interior), `arctanRecovery ε a b ω → 1` as `ε → 0⁺`. -/
lemma arctanRecovery_tendsto_one {a b ω : ℝ} (ha : a < ω) (hb : ω < b) :
    Tendsto (fun ε => arctanRecovery ε a b ω) (𝓝[>] 0) (𝓝 1) := by
  unfold arctanRecovery
  -- As ε → 0⁺: (b-ω)/ε → +∞ so arctan → π/2; (a-ω)/ε → -∞ so arctan → -π/2
  have h_top : Tendsto (fun ε => Real.arctan ((b - ω) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.comp (tendsto_pos_div_zero_atTop (by linarith))).mono_right nhdsWithin_le_nhds

  have h_bot : Tendsto (fun ε => Real.arctan ((a - ω) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (-(Real.pi / 2))) :=
    (Real.tendsto_arctan_atBot.comp (tendsto_neg_div_zero_atBot (by linarith))).mono_right nhdsWithin_le_nhds

  have h_diff : Tendsto (fun ε => Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi / 2 - -(Real.pi / 2))) :=
    h_top.sub h_bot
  rw [show Real.pi / 2 - -(Real.pi / 2) = Real.pi by ring] at h_diff
  have h_mul : Tendsto (fun ε => (1 / Real.pi) *
      (Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 / Real.pi) * Real.pi)) :=
    tendsto_const_nhds.mul h_diff
  rwa [one_div_mul_cancel (ne_of_gt Real.pi_pos)] at h_mul

/-- For `ω < a` (strictly to the left), `arctanRecovery ε a b ω → 0` as `ε → 0⁺`. -/
lemma arctanRecovery_tendsto_zero_of_lt {a b ω : ℝ} (hω : ω < a)
    {b' : ℝ} (hab : a ≤ b') (hbb : b' = b) :
    Tendsto (fun ε => arctanRecovery ε a b ω) (𝓝[>] 0) (𝓝 0) := by
  unfold arctanRecovery
  -- Both (b-ω)/ε and (a-ω)/ε → +∞ since b-ω > a-ω > 0
  have h1 : Tendsto (fun ε => Real.arctan ((b - ω) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.comp (tendsto_pos_div_zero_atTop (by linarith [hab, hbb]))).mono_right
      nhdsWithin_le_nhds

  have h2 : Tendsto (fun ε => Real.arctan ((a - ω) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.comp (tendsto_pos_div_zero_atTop (by linarith))).mono_right nhdsWithin_le_nhds

  have h_diff : Tendsto (fun ε => Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi / 2 - Real.pi / 2)) :=
    h1.sub h2
  rw [sub_self] at h_diff
  have h_mul : Tendsto (fun ε => (1 / Real.pi) *
      (Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 / Real.pi) * 0)) :=
    tendsto_const_nhds.mul h_diff
  rwa [mul_zero] at h_mul

/-- For `ω < a` (original signature without extra params). -/
lemma arctanRecovery_tendsto_zero_of_lt' {a b ω : ℝ} (hω : ω < a) (hab : a < b) :
    Tendsto (fun ε => arctanRecovery ε a b ω) (𝓝[>] 0) (𝓝 0) :=
  arctanRecovery_tendsto_zero_of_lt hω (le_of_lt hab) rfl

/-- For `ω > b` (strictly to the right), `arctanRecovery ε a b ω → 0` as `ε → 0⁺`. -/
lemma arctanRecovery_tendsto_zero_of_gt {a b ω : ℝ} (hab : a < b) (hω : b < ω) :
    Tendsto (fun ε => arctanRecovery ε a b ω) (𝓝[>] 0) (𝓝 0) := by
  unfold arctanRecovery
  -- Both (b-ω)/ε and (a-ω)/ε → -∞ since both numerators are negative
  have h1 : Tendsto (fun ε => Real.arctan ((b - ω) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (-(Real.pi / 2))) :=
    (Real.tendsto_arctan_atBot.comp (tendsto_neg_div_zero_atBot (by linarith))).mono_right nhdsWithin_le_nhds

  have h2 : Tendsto (fun ε => Real.arctan ((a - ω) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (-(Real.pi / 2))) :=
    (Real.tendsto_arctan_atBot.comp (tendsto_neg_div_zero_atBot (by linarith))).mono_right nhdsWithin_le_nhds

  have h_diff : Tendsto (fun ε => Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(Real.pi / 2) - -(Real.pi / 2))) :=
    h1.sub h2
  rw [sub_self] at h_diff
  have h_mul : Tendsto (fun ε => (1 / Real.pi) *
      (Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 / Real.pi) * 0)) :=
    tendsto_const_nhds.mul h_diff
  rwa [mul_zero] at h_mul

/-- At the right endpoint `b`, the arctan recovery converges to `1/2`. -/
lemma arctanRecovery_tendsto_half_at_right {a b : ℝ} (hab : a < b) :
    Tendsto (fun ε => arctanRecovery ε a b b) (𝓝[>] 0) (𝓝 (1/2)) := by
  unfold arctanRecovery
  -- (b-b)/ε = 0 → arctan(0) = 0; (a-b)/ε → -∞ → arctan → -π/2
  simp only [sub_self, zero_div, Real.arctan_zero]
  have h_bot : Tendsto (fun ε => Real.arctan ((a - b) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (-(Real.pi / 2))) :=
    (Real.tendsto_arctan_atBot.comp (tendsto_neg_div_zero_atBot (by linarith))).mono_right nhdsWithin_le_nhds

  have h_diff : Tendsto (fun ε => 0 - Real.arctan ((a - b) / ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 - -(Real.pi / 2))) :=
    tendsto_const_nhds.sub h_bot
  -- Replace the simp + h_mul block with:
  have h_mul : Tendsto (fun ε => (1 / Real.pi) * (0 - Real.arctan ((a - b) / ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 / Real.pi) * (0 - -(Real.pi / 2)))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub h_bot)
  simp only [zero_sub, neg_neg, one_div] at h_mul
  convert h_mul using 1
  simp only [one_div, zero_sub, mul_neg]
  field_simp

/-! ## §5: Distribution function agreement

Integrating the Poisson kernel over `(a, b]` and taking `ε → 0⁺` recovers `μ(a, b]`.
By Fubini + DCT, we show this depends only on the characteristic function. -/

/-- The integrated Poisson kernel equals the arctan recovery integrated against μ.
This is just Fubini: interchange the integral over `(a,b]` with the integral against μ. -/
lemma integrated_poisson_eq_arctan (μ : Measure ℝ) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (hab : a < b) :
    ∫ s in Ioc a b, (∫ ω, poissonKernel ε (s - ω) ∂μ) =
    ∫ ω, arctanRecovery ε a b ω ∂μ := by
  sorry -- TODO: Fubini (Tonelli for non-negative integrands) to swap the integrals
         -- Then apply poissonKernel_integral_Ioc to evaluate the inner integral
         -- Integrability: poissonKernel is continuous bounded, μ is finite

/-- **Key convergence**: the arctan recovery integral converges to `μ(a, b]`.

`∫ arctanRecovery ε a b dμ → μ(a, b]` as `ε → 0⁺`

Proof: the integrand is bounded by 1, and converges pointwise to `1_{(a,b]}`
at all points except possibly `a` (a single point, measure zero for the
limit computation). Apply DCT. -/
lemma arctan_integral_tendsto_measure (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a < b)
    (ha : μ {a} = 0) :
    Tendsto (fun ε => ∫ ω, arctanRecovery ε a b ω ∂μ)
      (𝓝[>] 0) (𝓝 (μ (Ioc a b)).toReal) := by
  sorry -- TODO: DCT via MeasureTheory.tendsto_integral_of_dominated_convergence
         -- Dominating function: constant 1 (integrable since μ is finite)
         -- Bound: arctanRecovery_le_one
         -- Pointwise a.e. convergence: at ω ∈ (a,b) → 1, at ω < a or ω > b → 0,
         --   at ω = a → doesn't matter (μ{a} = 0), at ω = b → 1/2 (correct for Ioc)
         -- The limit function is 1_{(a,b]} μ-a.e., whose integral is μ(a,b]

/-! ## §6: Putting it together — agreement on `(a, b]` -/

/-- Two finite measures with the same characteristic function agree on `(a, b]`,
    provided `μ({a}) = 0` (i.e., `a` is a continuity point of `F_μ`).

This is the core of the uniqueness proof. The argument:
1. Same char. function → same Poisson integrals (§3)
2. Integrate over (a,b] → same arctan integrals (Fubini, §5)
3. Take ε → 0 → μ(a,b] = ν(a,b] (DCT, §5)  -/
lemma measure_Ioc_eq_of_fourier_eq (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, ∫ ω, exp (I * ↑ω * ↑t) ∂μ = ∫ ω, exp (I * ↑ω * ↑t) ∂ν)
    {a b : ℝ} (hab : a < b)
    (ha_μ : μ {a} = 0) (ha_ν : ν {a} = 0) :
    μ (Ioc a b) = ν (Ioc a b) := by
  -- The arctan integrals are equal for all ε > 0
  have h_arctan_eq : ∀ ε : ℝ, 0 < ε →
      ∫ ω, arctanRecovery ε a b ω ∂μ = ∫ ω, arctanRecovery ε a b ω ∂ν := by
    intro ε hε
    have h_poisson := poisson_integral_eq_of_fourier_eq μ ν h hε
    have h_int_μ := integrated_poisson_eq_arctan μ hε hab
    have h_int_ν := integrated_poisson_eq_arctan ν hε hab
    have h_int_eq : ∫ s in Ioc a b, (∫ ω, poissonKernel ε (s - ω) ∂μ) =
                    ∫ s in Ioc a b, (∫ ω, poissonKernel ε (s - ω) ∂ν) := by
      congr 1; ext s; exact h_poisson s
    linarith [h_int_μ, h_int_ν, h_int_eq]
  -- Both sides have the same limit as ε → 0
  have h_lim_μ := arctan_integral_tendsto_measure μ hab ha_μ
  have h_lim_ν := arctan_integral_tendsto_measure ν hab ha_ν
  have h_toReal_eq : (μ (Ioc a b)).toReal = (ν (Ioc a b)).toReal := by
    have h_lim_ν' : Tendsto (fun ε => ∫ ω, arctanRecovery ε a b ω ∂μ)
        (𝓝[>] 0) (𝓝 (ν (Ioc a b)).toReal) := by
      intro s hs
      simp only [mem_map]
      filter_upwards [h_lim_ν hs, self_mem_nhdsWithin] with ε hε_mem hε_pos
      simp only [mem_preimage]
      exact mem_of_eq_of_mem (h_arctan_eq ε hε_pos) hε_mem
    exact tendsto_nhds_unique h_lim_μ h_lim_ν'
  have h_ne_top_μ := measure_ne_top μ (Ioc a b)
  have h_ne_top_ν := measure_ne_top ν (Ioc a b)
  rw [← ENNReal.ofReal_toReal h_ne_top_μ, ← ENNReal.ofReal_toReal h_ne_top_ν, h_toReal_eq]

private lemma finite_of_measure_singleton_ge (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) : Set.Finite {x : ℝ | (1 : ENNReal) / ((n : ENNReal) + 1) ≤ μ {x}} := by
  -- Suppose for contradiction the set is infinite
  by_contra h_inf
  rw [Set.not_finite] at h_inf
  -- We can find a finite subset of size (n+1) · ⌈μ(univ)⌉ + 1
  -- Actually, simpler: if S is any finite subset with k elements,
  -- then k/(n+1) ≤ Σ_{x∈S} μ{x} = μ(⋃_{x∈S} {x}) ≤ μ(univ) < ∞.
  -- So k ≤ (n+1) · μ(univ), bounding the set size.
  -- For any K > (n+1)·μ(univ).toReal, we get a contradiction.
  set M := μ Set.univ with hM_def
  have hM_fin : M < ⊤ := measure_lt_top μ _
  -- Pick a finite subset with more than M·(n+1) elements
  -- Since the set is infinite, we can always do this
  set K := Nat.ceil (M.toReal * (↑n + 1)) + 1 with hK_def
  obtain ⟨S, hS_sub, hS_card⟩ := h_inf.exists_subset_ncard_eq K
  -- S is finite (it has exactly K elements)
  have hS_fin : S.Finite := by
    by_contra h_inf
    have := Set.Infinite.ncard (Set.not_finite.mp h_inf)
    omega
  -- Each point in S has μ{x} ≥ 1/(n+1)
  -- The singletons are pairwise disjoint
  have h_disj : S.PairwiseDisjoint (fun x => ({x} : Set ℝ)) := by
    intro x _ y _ hxy
    exact Set.disjoint_singleton.mpr hxy
  -- Sum of measures: Σ_{x∈S} μ{x} ≥ K · (1/(n+1))
  -- But also ≤ μ(univ) = M
  -- And K > M·(n+1), so K/(n+1) > M. Contradiction.
  sorry -- The ENNReal arithmetic to close this is routine but verbose.
        -- Key steps: convert to ℝ via toReal, use hS_card, hK_def.

/-! ## §6.5: Handling atoms — continuity points are dense

For the full theorem, we need `μ(a,b] = ν(a,b]` for ALL `a < b`, not just
at continuity points. A finite measure has at most countably many atoms,
so continuity points of the distribution function are co-countable (hence dense).
We use right-continuity of the distribution function to extend. -/

/-- A finite measure on ℝ has at most countably many atoms. -/
lemma countable_atoms (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Set.Countable {x : ℝ | μ {x} ≠ 0} := by
  -- {x : μ{x} ≠ 0} = ⋃ n, {x : μ{x} ≥ 1/(n+1)}, each level set finite
  have : {x : ℝ | μ {x} ≠ 0} = ⋃ n : ℕ, {x : ℝ | 1 / ((n : ENNReal) + 1) ≤ μ {x}} := by
    ext x; simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · intro hx
      have hx_pos : 0 < μ {x} := pos_iff_ne_zero.mpr hx
      -- μ{x} > 0, so μ{x} ≥ 1/(n+1) for some n
      by_contra h_none
      push_neg at h_none
      -- ∀ n, μ{x} < 1/(n+1), but 1/(n+1) → 0, so μ{x} ≤ 0, contradiction
      have : μ {x} = 0 := by
        apply le_antisymm _ (zero_le _)
        by_contra h_pos
        push_neg at h_pos
        sorry -- ENNReal Archimedean: find n with 1/(n+1) < μ{x}
      exact hx this
    · intro ⟨n, hn⟩
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hn)
  rw [this]
  apply Set.countable_iUnion
  intro n
  -- {x : 1/(n+1) ≤ μ{x}} is finite: it has at most (n+1)·μ(ℝ) elements
  sorry -- If S is finite subset of this level set with |S| = k,
         -- then k/(n+1) ≤ Σ_{x∈S} μ{x} = μ(⋃_{x∈S} {x}) ≤ μ(univ) < ∞
         -- so k ≤ (n+1)·μ(univ), hence the set is finite.

/-- For any `a : ℝ`, there exist `aₙ < a` with `aₙ → a` and `μ{aₙ} = 0 ∧ ν{aₙ} = 0`.

This is because the set of atoms of `μ` and `ν` is countable, so co-countable
points exist in every interval. -/
lemma exists_continuity_points_below (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (a : ℝ) :
    ∃ (seq : ℕ → ℝ), (∀ n, seq n < a) ∧ (∀ n, μ {seq n} = 0) ∧
    (∀ n, ν {seq n} = 0) ∧ Tendsto seq atTop (𝓝 a) := by
  -- Combined atoms are countable
  have h_countable : Set.Countable ({x | μ {x} ≠ 0} ∪ {x | ν {x} ≠ 0}) :=
    (countable_atoms μ).union (countable_atoms ν)
  have h_exists : ∀ n : ℕ, ∃ x ∈ Ioo (a - 1 / (↑n + 1)) a,
      μ {x} = 0 ∧ ν {x} = 0 := by
    intro n
    -- The interval is uncountable
    have h_uncount : ¬ Set.Countable (Ioo (a - 1 / (↑n + 1)) a) := by
      simp only [one_div, Cardinal.Real.Ioo_countable_iff, le_sub_self_iff, inv_nonpos, not_le]
      exact Nat.cast_add_one_pos n
    have h_diff_nonempty : (Ioo (a - 1 / (↑n + 1)) a \
        ({x | μ {x} ≠ 0} ∪ {x | ν {x} ≠ 0})).Nonempty := by
      by_contra h_empty
      have h_sub : Ioo (a - 1 / (↑n + 1)) a ⊆
          {x | μ {x} ≠ 0} ∪ {x | ν {x} ≠ 0} := by
        intro x hx
        by_contra hx'
        exact h_empty ⟨x, hx, hx'⟩
      exact h_uncount (h_countable.mono h_sub)
    obtain ⟨x, hx_Ioo, hx_not_atom⟩ := h_diff_nonempty
    refine ⟨x, hx_Ioo, ?_, ?_⟩
    · simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hx_not_atom
      exact not_ne_iff.mp hx_not_atom.1
    · simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hx_not_atom
      exact not_ne_iff.mp hx_not_atom.2
  -- Use choice to extract the sequence
  choose seq h_seq using h_exists
  refine ⟨seq, ?_, ?_, ?_, ?_⟩
  · intro n; exact (h_seq n).1.2       -- seq n ∈ Ioo ⊢ seq n < a
  · intro n; exact (h_seq n).2.1       -- μ {seq n} = 0
  · intro n; exact (h_seq n).2.2       -- ν {seq n} = 0
  · -- seq n ∈ (a - 1/(n+1), a), so |seq n - a| < 1/(n+1) → 0
    suffices h : Tendsto (fun n => seq n - a) atTop (𝓝 0) by
      have := h.add (tendsto_const_nhds (x := a))
      simp only [sub_add_cancel, zero_add] at this
      exact this
    apply squeeze_zero_norm
    · intro n
      have h_lo := (h_seq n).1.1   -- a - 1/(n+1) < seq n
      have h_hi := (h_seq n).1.2   -- seq n < a
      rw [Real.norm_eq_abs]
    · have h_bound : ∀ n, ‖|seq n - a|‖ ≤ 1 / ((↑n : ℝ) + 1) := by
        intro n
        rw [Real.norm_eq_abs, abs_abs,
            abs_of_nonpos (by linarith [(h_seq n).1.2] : seq n - a ≤ 0)]
        linarith [(h_seq n).1.1]
      have h_tendsto : Tendsto (fun n : ℕ => 1 / ((↑n : ℝ) + 1)) atTop (𝓝 0) := by
        rw [Metric.tendsto_atTop]
        intro δ hδ
        obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
        refine ⟨N, fun n hn => ?_⟩
        rw [Real.dist_eq, sub_zero,
            abs_of_pos (div_pos one_pos (by positivity : (0 : ℝ) < ↑n + 1))]
        calc (1 : ℝ) / (↑n + 1)
            ≤ 1 / (↑N + 1) := by
              apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < ↑N + 1)
              exact_mod_cast Nat.add_le_add_right hn 1
          _ < δ := by rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ↑N + 1)]
                      rw [← propext (inv_lt_iff_one_lt_mul₀' hδ)]
                      grind only
      exact squeeze_zero_norm h_bound h_tendsto

/-- The distribution function `x ↦ μ(Ioc c x)` for fixed `c` is monotone
    and right-continuous. Two such functions agreeing on a dense set agree everywhere. -/
lemma measure_Ioc_eq_of_fourier_eq' (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, ∫ ω, exp (I * ↑ω * ↑t) ∂μ = ∫ ω, exp (I * ↑ω * ↑t) ∂ν)
    (a b : ℝ) (hab : a < b) :
    μ (Ioc a b) = ν (Ioc a b) := by
  -- Strategy: show the distribution functions F_μ(x) = μ(Iic x) and F_ν(x) = ν(Iic x)
  -- agree everywhere, then μ(a,b] = F_μ(b) - F_μ(a) = F_ν(b) - F_ν(a) = ν(a,b].
  --
  -- Step 1: F_μ and F_ν agree at common continuity points (where both μ{x} = ν{x} = 0).
  -- At such points c < d, we have μ(c,d] = ν(c,d] by measure_Ioc_eq_of_fourier_eq.
  -- Fixing a common continuity point c₀ and letting d vary over common continuity
  -- points gives F_μ(d) - F_μ(c₀) = F_ν(d) - F_ν(c₀).
  -- As c₀ → -∞, F_μ(c₀) → 0 and F_ν(c₀) → 0, so F_μ = F_ν on a dense set.
  --
  -- Step 2: Both F_μ and F_ν are right-continuous monotone functions.
  -- Two right-continuous functions agreeing on a dense set agree everywhere.
  --
  -- Step 3: μ(a,b] = F_μ(b) - F_μ(a) = F_ν(b) - F_ν(a) = ν(a,b].
  sorry

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
