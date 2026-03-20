/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Fourier/PoissonKernel/Lemmas.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.PositiveDefinite
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.PdProperties

/-!
# Fourier Uniqueness for Finite Measures

A finite positive Borel measure on ℝ is uniquely determined by its
characteristic function (Fourier–Stieltjes transform).


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
lemma continuous_inv_one_add_sq :
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
    -- Split complement into two rays
    have compl_eq : (Icc (-1:ℝ) 1)ᶜ = Iio (-1) ∪ Ioi 1 := by
      ext x; simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
    rw [compl_eq]
    -- Hoist the Ioi result for reuse in both branches
    have hIoi : IntegrableOn (fun x : ℝ => (1 + x ^ 2)⁻¹) (Ioi 1) volume := by
      refine Integrable.mono (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) one_pos) ?_ ?_
      · exact continuous_inv_one_add_sq.continuousOn.aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 1 < x)
        have hxp : 0 < x := by linarith
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (by positivity)),
            abs_of_nonneg (Real.rpow_nonneg hxp.le _)]
        calc (1 + x ^ 2)⁻¹
          _ ≤ (x ^ 2)⁻¹ := by gcongr; linarith
          _ = x ^ (-2 : ℝ) := by
              rw [← Real.rpow_natCast x 2, ← Real.rpow_neg hxp.le]; norm_num
    apply IntegrableOn.union
    · -- Iio (-1): by negation symmetry from hIoi
      have h_set : Iio (-(1:ℝ)) = Neg.neg ⁻¹' (Ioi 1) := by ext x; simp
      -- Rewrite integrand as f ∘ neg (since x² = (-x)²)
      rw [show (fun x : ℝ => (1 + x ^ 2)⁻¹) = (fun x : ℝ => (1 + x ^ 2)⁻¹) ∘ Neg.neg
            from by ext x; simp only [Function.comp_apply, even_two, Even.neg_pow]]
      rw [h_set]
      -- Transfer integrability via measure-preserving negation
      exact (MeasurePreserving.integrable_comp_emb
        ⟨measurable_neg, by
          rw [← Measure.restrict_map measurable_neg measurableSet_Ioi]
          rw [Measure.map_neg_eq_self]⟩
        (MeasurableEquiv.neg ℝ).measurableEmbedding).mpr hIoi
    · exact hIoi


/-- The full-line Bochner integral: `∫ x : ℝ, (1 + x²)⁻¹ = π`.

Proof:
  1. For integrable `f`, `∫ x in -R..R, f x → ∫ x, f x` as `R → ∞`.
  2. By `integral_inv_one_add_sq`, the interval integral = `arctan R - arctan(-R)`.
  3. This tends to `π/2 - (-π/2) = π`.
  4. Uniqueness of limits. -/
lemma integral_inv_one_add_sq_eq_pi :
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


/-! ## Phase 1: Half-line exponential integral (engine for Route C) -/

/-- Norm of `cexp(-(a * t))` for real `t`. -/
private lemma norm_cexp_neg_mul_ofReal (a : ℂ) (t : ℝ) :
    ‖cexp (-(a * ↑t))‖ = Real.exp (-a.re * t) := by
  rw [Complex.norm_exp]
  simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- `cexp(-(a * t)) → 0` as `t → +∞` when `0 < a.re`. -/
private lemma tendsto_cexp_neg_mul_ofReal_atTop {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun t : ℝ => cexp (-(a * ↑t))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_cexp_neg_mul_ofReal]
  have h_atBot : Tendsto (fun t : ℝ => -a.re * t) atTop atBot := by
    have h1 : Tendsto (fun t : ℝ => a.re * t) atTop atTop :=
      tendsto_atTop_atTop_of_monotone (fun _ _ h => mul_le_mul_of_nonneg_left h ha.le)
        (fun b => ⟨b / a.re, by rw [mul_div_cancel₀ _ (ne_of_gt ha)]⟩)
    exact (tendsto_neg_atTop_atBot.comp h1).congr (fun t => by ring_nf; rfl)
  exact Real.tendsto_exp_atBot.comp h_atBot

/-- Derivative of the antiderivative `-a⁻¹ * cexp(-(a * t))`. -/
private lemma hasDerivAt_antideriv_cexp {a : ℂ} (ha_ne : a ≠ 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => -a⁻¹ * cexp (-(a * ↑t)))
               (cexp (-(a * ↑t))) t := by
  have h1 : HasDerivAt (fun t : ℝ => (↑t : ℂ)) 1 t := ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => -(a * ↑t)) (-a) t := by
    convert (h1.const_mul a).neg using 1; ring
  convert (h2.cexp).const_mul (-a⁻¹) using 1
  field_simp

/-- Real exponential `exp(-c * t)` is integrable on `(0, ∞)` for `c > 0`.
    Uses FTC: antiderivative `F(t) = -c⁻¹ exp(-ct)` is monotone increasing
    and bounded in `[-c⁻¹, 0]`, so the nonneg derivative is integrable. -/
private lemma integrableOn_exp_neg_mul_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * t)) (Set.Ioi 0) volume := by
  have hcont : ContinuousWithinAt (fun t : ℝ => -c⁻¹ * Real.exp (-c * t)) (Ici 0) 0 := by
    fun_prop
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun t => -c⁻¹ * Real.exp (-c * t)) (Real.exp (-c * t)) t := by
    intro t _
    have h := (((hasDerivAt_id t).const_mul (-c)).exp).const_mul (-c⁻¹)
    simp only [mul_one] at h
    convert h using 1
    field_simp; ring_nf
    exact Real.exp_eq_exp.mpr rfl
  have hnonneg : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ Real.exp (-c * t) := by
    intro t _; exact (Real.exp_pos _).le
  have htendsto : Tendsto (fun t : ℝ => -c⁻¹ * Real.exp (-c * t)) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = -c⁻¹ * 0 from by ring]
    apply Filter.Tendsto.const_mul
    apply Real.tendsto_exp_atBot.comp
    have h1 : Tendsto (fun t : ℝ => c * t) atTop atTop :=
      tendsto_atTop_atTop_of_monotone (fun _ _ h => mul_le_mul_of_nonneg_left h hc.le)
        (fun b => ⟨b / c, by rw [mul_div_cancel₀ _ (ne_of_gt hc)]⟩)
    exact (tendsto_neg_atTop_atBot.comp h1).congr (fun t => by ring_nf; rfl)
  exact integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnonneg htendsto


/-- `cexp(-(a * t))` is integrable on `(0, ∞)` when `0 < a.re`. -/
private lemma integrableOn_cexp_neg_mul_Ioi {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => cexp (-(a * ↑t))) (Set.Ioi 0) volume := by
  -- Dominate: ‖cexp(-(a*t))‖ = exp(-a.re * t), which is integrable
  have h_real := integrableOn_exp_neg_mul_Ioi ha
  exact h_real.mono'
    ((Complex.continuous_exp.comp
      ((continuous_const.mul continuous_ofReal).neg)).aestronglyMeasurable.restrict)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
        exact le_of_eq (norm_cexp_neg_mul_ofReal a t))


/-- **Half-line exponential integral**: `∫ t ∈ (0,∞), cexp(-(a*t)) = a⁻¹` for `Re(a) > 0`.

This is the engine powering Route C of the Poisson–Fourier computation. -/
lemma integral_cexp_neg_mul_Ioi {a : ℂ} (ha : 0 < a.re) :
    ∫ t in Set.Ioi (0 : ℝ), cexp (-(a * ↑t)) = a⁻¹ := by
  have ha_ne : a ≠ 0 := by intro h; simp [h] at ha
  -- F is globally continuous
  have hF_cont : Continuous (fun t : ℝ => -a⁻¹ * cexp (-(a * ↑t))) :=
    continuous_const.mul (Complex.continuous_exp.comp
      ((continuous_const.mul continuous_ofReal).neg))
  -- Apply FTC: ∫₀^∞ F' = lim F - F(0)
  have h_FTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    hF_cont.continuousAt.continuousWithinAt
    (fun t _ht => hasDerivAt_antideriv_cexp ha_ne t)
    (integrableOn_cexp_neg_mul_Ioi ha)
    (show Tendsto (fun (t : ℝ) => -a⁻¹ * cexp (-(a * ↑t))) atTop (𝓝 0) from by
      have := tendsto_cexp_neg_mul_ofReal_atTop ha
      rw [show (0 : ℂ) = -a⁻¹ * 0 from by ring]
      exact tendsto_const_nhds.mul this)
  -- h_FTC : ∫ ... = 0 - (-a⁻¹ * cexp(-(a * 0)))
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
             mul_one, sub_neg_eq_add, zero_add] at h_FTC
  exact h_FTC

/-! ## Phase 2: Fourier transform of the two-sided exponential -/

/-- Algebraic identity: `(ε - ξi)⁻¹ + (ε + ξi)⁻¹ = 2ε/(ξ² + ε²)` in ℂ. -/
private lemma inv_add_conj_inv {ε ξ : ℝ} (hε : 0 < ε) :
    (↑ε - ↑ξ * I)⁻¹ + (↑ε + ↑ξ * I)⁻¹ =
    ((2 * ε / (ξ ^ 2 + ε ^ 2) : ℝ) : ℂ) := by
  have h1 : (↑ε - ↑ξ * I : ℂ) ≠ 0 := by
    intro h; have := congr_arg Complex.re h; simp at this; linarith
  have h2 : (↑ε + ↑ξ * I : ℂ) ≠ 0 := by
    intro h; have := congr_arg Complex.re h; simp at this; linarith
  have h3 : (ξ ^ 2 + ε ^ 2 : ℝ) ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg ξ) (sq_pos_of_pos hε))
  rw [inv_eq_one_div, inv_eq_one_div, div_add_div _ _ h1 h2]
  rw [show (↑ε - ↑ξ * I) * (↑ε + ↑ξ * I) = ↑(ξ ^ 2 + ε ^ 2) from by
    push_cast; ring_nf; simp only [I_sq, mul_neg, mul_one, sub_neg_eq_add]]
  rw [show 1 * (↑ε + ↑ξ * I) + (↑ε - ↑ξ * I) * 1 = ↑(2 * ε) from by push_cast; ring]
  rw [← ofReal_div]


/-- The two-sided exponential integrand `e^{-ε|t|} · e^{iξt}` is integrable on ℝ. -/
lemma integrable_two_sided_exp {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) :
    Integrable (fun t : ℝ => cexp (-(↑ε * ↑|t|)) * cexp (I * ↑ξ * ↑t)) volume := by
  rw [← integrableOn_univ,
      show (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ioi 0 from Set.Iic_union_Ioi.symm]
  refine IntegrableOn.union ?_ ?_
  · -- ── On Iic 0 ──
    -- Split: Iic 0 = Iio 0 ∪ {0}
    rw [show Set.Iic (0:ℝ) = Set.Iio 0 ∪ {0} from by ext; simp [le_iff_lt_or_eq]]
    refine IntegrableOn.union ?_ ?_
    · -- On Iio 0: for t < 0, |t| = -t, so integrand = cexp(-(aPos * (-t)))
      -- Transfer from Ioi 0 via measure-preserving negation
      have haPos : 0 < (↑ε + ↑ξ * I : ℂ).re := by simp; exact hε
      have h_transfer : IntegrableOn ((fun t : ℝ => cexp (-((↑ε + ↑ξ * I) * ↑t))) ∘ Neg.neg)
          (Set.Iio 0) volume :=
        (MeasurePreserving.integrable_comp_emb
          ⟨measurable_neg, by
            conv_lhs =>
              rw [show Set.Iio (0:ℝ) = Neg.neg ⁻¹' Set.Ioi 0 from by
                ext; simp only [mem_Iio,neg_preimage, neg_Ioi, neg_zero]]
            rw [← Measure.restrict_map measurable_neg measurableSet_Ioi,
                Measure.map_neg_eq_self]⟩
          (MeasurableEquiv.neg ℝ).measurableEmbedding).mpr
          (integrableOn_cexp_neg_mul_Ioi haPos)
      -- Integrand = transferred function on Iio 0
      exact h_transfer.congr_fun (fun t ht => by
        simp only [Function.comp, abs_of_neg (Set.mem_Iio.mp ht), ← exp_add]
        congr 1; push_cast; ring) measurableSet_Iio
    · -- On {0}: Lebesgue measure is atomless, so {0} is null
      rw [IntegrableOn, Measure.restrict_eq_zero.mpr (measure_singleton (0 : ℝ))]
      exact integrable_zero_measure
  · -- ── On Ioi 0: for t > 0, |t| = t, integrand = cexp(-(aNeg * t)) ──
    have haNeg : 0 < (↑ε - ↑ξ * I : ℂ).re := by simp; exact hε
    exact (integrableOn_cexp_neg_mul_Ioi haNeg).congr_fun (fun t ht => by
      simp only [abs_of_pos (Set.mem_Ioi.mp ht), ← exp_add]
      congr 1; ring) measurableSet_Ioi

/-- Substitution: `∫_{Iic 0} f(t) dt = ∫_{Ioi 0} f(-u) du` for integrable `f`.
    Uses measure-preserving negation on ℝ. -/
private lemma setIntegral_Iic_comp_neg {f : ℝ → ℂ} (_hf : Integrable f) :
    ∫ t in Set.Iic (0 : ℝ), f t = ∫ u in Set.Ioi (0 : ℝ), f (-u) := by
  have hmp : MeasurePreserving Neg.neg (volume : Measure ℝ) volume :=
    ⟨measurable_neg, Measure.map_neg_eq_self volume⟩
  have hme : MeasurableEmbedding (Neg.neg : ℝ → ℝ) :=
    (MeasurableEquiv.neg ℝ).measurableEmbedding
  rw [← hmp.setIntegral_preimage_emb hme f (Set.Iic 0),
      show Neg.neg ⁻¹' Set.Iic (0:ℝ) = Set.Ici 0 from by ext x; simp]
  exact integral_Ici_eq_integral_Ioi


/-- **Fourier transform of the two-sided exponential**:
    `∫ e^{-ε|t|} · e^{iξt} dt = 2ε/(ξ² + ε²)` for `ε > 0`.

This is the "easy direction" of Route C — exponential integrals via Phase 1. -/
lemma fourier_two_sided_exp {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) :
    ∫ t : ℝ, cexp (-(↑ε * ↑|t|)) * cexp (I * ↑ξ * ↑t) =
    ((2 * ε / (ξ ^ 2 + ε ^ 2) : ℝ) : ℂ) := by

  set f : ℝ → ℂ := fun t => cexp (-(↑ε * ↑|t|)) * cexp (I * ↑ξ * ↑t)
  set aPos : ℂ := ↑ε + ↑ξ * I
  set aNeg : ℂ := ↑ε - ↑ξ * I
  have haPos : 0 < aPos.re := by simp [aPos]; exact hε
  have haNeg : 0 < aNeg.re := by simp [aNeg]; exact hε
  have hf_int := integrable_two_sided_exp hε ξ
  -- ── Split: ∫_ℝ f = ∫_{Ioi 0} f + ∫_{Iic 0} f ──
  have h_split : ∫ t, f t = (∫ t in Set.Ioi 0, f t) + (∫ t in Set.Iic 0, f t) := by
    rw [← integral_add_compl measurableSet_Ioi hf_int]
    congr 1
    rw [Set.compl_Ioi]
  -- ── Positive half: ∫_{Ioi 0} f = aNeg⁻¹ ──
  have h_pos : ∫ t in Set.Ioi 0, f t = aNeg⁻¹ := by
    have h_eq : ∫ t in Set.Ioi 0, f t = ∫ t in Set.Ioi (0 : ℝ), cexp (-(aNeg * ↑t)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      show f t = _
      simp only [f, abs_of_pos (Set.mem_Ioi.mp ht), ← exp_add]
      congr 1; field
    rw [h_eq, integral_cexp_neg_mul_Ioi haNeg]
  -- ── Negative half: ∫_{Iic 0} f = aPos⁻¹ ──
  have h_neg : ∫ t in Set.Iic 0, f t = aPos⁻¹ := by
    -- Substitute u = -t: ∫_{Iic 0} f(t) = ∫_{Ioi 0} f(-u)
    rw [setIntegral_Iic_comp_neg hf_int]
    have h_eq : ∫ u in Set.Ioi 0, f (-u) = ∫ u in Set.Ioi (0 : ℝ), cexp (-(aPos * ↑u)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      show f (-u) = _
      simp only [f, abs_neg, abs_of_pos (Set.mem_Ioi.mp hu), ofReal_neg, mul_neg, ← exp_add]
      congr 1; ring
    rw [h_eq, integral_cexp_neg_mul_Ioi haPos]
  -- ── Combine ──
  rw [h_split, h_pos, h_neg, inv_add_conj_inv hε]



end SpectralBridge.Bochner.FourierUniqueness
