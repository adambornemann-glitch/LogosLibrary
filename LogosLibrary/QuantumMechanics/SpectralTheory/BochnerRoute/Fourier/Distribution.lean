/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Fourier/Distribution.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Fourier.ArctanLim

namespace SpectralBridge.Bochner.FourierUniqueness

open Complex MeasureTheory Filter Topology Set Function

/-! ## §5: Distribution function agreement

Integrating the Poisson kernel over `(a, b]` and taking `ε → 0⁺` recovers `μ(a, b]`.
By Fubini + DCT, we show this depends only on the characteristic function. -/

/-- The integrated Poisson kernel equals the arctan recovery integrated against μ.
This is just Fubini: interchange the integral over `(a,b]` with the integral against μ. -/
lemma integrated_poisson_eq_arctan (μ : Measure ℝ) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (hab : a < b) :
    ∫ s in Ioc a b, (∫ ω, poissonKernel ε (s - ω) ∂μ) =
    ∫ ω, arctanRecovery ε a b ω ∂μ := by
  -- ── Pointwise evaluation: inner set integral = arctanRecovery ──
  have h_eval : ∀ ω, ∫ s in Ioc a b, poissonKernel ε (s - ω) = arctanRecovery ε a b ω :=
    fun ω => poissonKernel_integral_Ioc hε ω a b hab
  -- ── Reduce to swapping the order of integration ──
  suffices h_swap : ∫ s in Ioc a b, (∫ ω, poissonKernel ε (s - ω) ∂μ) =
      ∫ ω, (∫ s in Ioc a b, poissonKernel ε (s - ω)) ∂μ by
    rw [h_swap]; congr 1; ext ω; exact h_eval ω
  -- ── Fubini prerequisites ──
  -- The restricted Lebesgue measure on (a,b] is finite
  haveI : IsFiniteMeasure (volume.restrict (Ioc a b : Set ℝ)) :=
    ⟨by simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter, Real.volume_Ioc,
      ENNReal.ofReal_lt_top]⟩
  -- Joint continuity: (s, ω) ↦ P_ε(s - ω) is continuous
  have h_cont : Continuous (uncurry fun (s : ℝ) (ω : ℝ) => poissonKernel ε (s - ω)) :=
    (poissonKernel_continuous hε).comp (continuous_fst.sub continuous_snd)
  -- ── Joint integrability on product measure ──
  -- Strategy: P_ε(x) ≤ 1/(πε) globally, so dominate by an integrable constant
  have h_int : Integrable (uncurry fun s ω => poissonKernel ε (s - ω))
      ((volume.restrict (Ioc a b)).prod μ) := by
    apply (integrable_const (1 / (Real.pi * ε))).mono h_cont.aestronglyMeasurable
    filter_upwards with ⟨s, ω⟩
    simp only [uncurry_apply_pair, Real.norm_eq_abs,
               abs_of_nonneg (poissonKernel_nonneg hε _),
               abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (Real.pi * ε))]
    -- Goal: poissonKernel ε (s - ω) ≤ 1 / (Real.pi * ε)
    unfold poissonKernel
    calc (1 / Real.pi) * (ε / ((s - ω) ^ 2 + ε ^ 2))
        ≤ (1 / Real.pi) * (1 / ε) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_div_iff₀ (sq_add_sq_pos hε _) hε]
          nlinarith [sq_nonneg (s - ω)]
      _ = 1 / (Real.pi * ε) := by ring
  -- ── Apply Fubini ──
  exact integral_integral_swap h_int


/-- **Key convergence**: the arctan recovery integral converges to `μ(a, b]`.

`∫ arctanRecovery ε a b dμ → μ(a, b]` as `ε → 0⁺`

Proof: the integrand is bounded by 1, and converges pointwise to `1_{(a,b]}`
at all points except possibly `a` (a single point, measure zero for the
limit computation). Apply DCT. -/
lemma arctan_integral_tendsto_measure (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a < b)
    (ha : μ {a} = 0) (hb : μ {b} = 0) :
    Tendsto (fun ε => ∫ ω, arctanRecovery ε a b ω ∂μ)
      (𝓝[>] 0) (𝓝 (μ (Ioc a b)).toReal) := by
  -- ── Limit function: indicator of (a,b] ──
  set F' : ℝ → ℝ := (Ioc a b).indicator (fun _ => 1) with hF'_def
  -- ── ∫ F' dμ = μ(a,b] ──
  have h_int_F' : ∫ ω, F' ω ∂μ = (μ (Ioc a b)).toReal := by
    simp [hF'_def, integral_indicator measurableSet_Ioc]
    exact Measure.real_def μ (Ioc a b)
  -- ── Apply DCT with dominating function g = 1 ──
  rw [← h_int_F']
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · -- Each arctanRecovery ε is AEStronglyMeasurable (eventually for ε > 0)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (arctanRecovery_measurable (mem_Ioi.mp hε) a b).aestronglyMeasurable
  · -- Norm bound: ‖arctanRecovery ε a b ω‖ ≤ 1
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (arctanRecovery_nonneg (mem_Ioi.mp hε) hab ω)]
    exact arctanRecovery_le_one (mem_Ioi.mp hε) hab ω
  · -- Norm bound: ‖arctanRecovery ε a b ω‖ ≤ 1
    simp only [enorm_one, ne_eq, ENNReal.one_ne_top, not_false_eq_true, integrable_const_enorm]
  · -- Pointwise a.e. convergence: arctanRecovery → 𝟙_{(a,b]} except on {a,b}
    have h_ne_a : ∀ᵐ ω ∂μ, ω ≠ a := ae_iff.mpr (by simp [ha])
    have h_ne_b : ∀ᵐ ω ∂μ, ω ≠ b := ae_iff.mpr (by simp [hb])
    filter_upwards [h_ne_a, h_ne_b] with ω hωa hωb
    simp only [F', indicator_apply]
    rcases lt_or_gt_of_ne hωa with hlt_a | hgt_a
    · -- ω < a: arctanRecovery → 0, indicator = 0
      rw [if_neg (fun h : ω ∈ Ioc a b => not_lt.mpr hlt_a.le h.1)]
      exact arctanRecovery_tendsto_zero_of_lt' hlt_a hab
    · rcases lt_or_gt_of_ne hωb with hlt_b | hgt_b
      · -- a < ω < b: arctanRecovery → 1, indicator = 1
        rw [if_pos (mem_Ioc.mpr ⟨hgt_a, hlt_b.le⟩)]
        exact arctanRecovery_tendsto_one hgt_a hlt_b
      · -- ω > b: arctanRecovery → 0, indicator = 0
        rw [if_neg (fun h : ω ∈ Ioc a b => not_le.mpr hgt_b h.2)]
        exact arctanRecovery_tendsto_zero_of_gt hab hgt_b

end SpectralBridge.Bochner.FourierUniqueness
