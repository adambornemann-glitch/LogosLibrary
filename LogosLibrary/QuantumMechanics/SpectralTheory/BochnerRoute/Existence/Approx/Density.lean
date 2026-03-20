/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Existence/Approx/Density.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.Approx.Riemann

namespace SpectralBridge.Bochner.BochnerExistence

open SpectralBridge.Bochner
open Complex MeasureTheory Filter Topology Set Real Function

variable {f : ℝ → ℂ}

/-- Alternative representation: Λ_T(ω) = (1/2πT)|∫₀ᵀ e^{-iωt} dt|²-weighted
    quadratic form.

The key identity is:
  (1 - |t|/T) = (1/T) ∫₀ᵀ⁻|ᵗ| 1 ds = (1/T) ∫∫ 1_{|u-v|=|t|} du dv
  (over [0,T] × [0,T])

So Λ_T(ω) = (1/2πT) ∫∫_{[0,T]²} f(u-v) e^{-iω(u-v)} du dv
            = (1/2πT) ∫∫ f(u-v) e^{-iωu} e^{iωv} du dv

This is manifestly non-negative by positive-definiteness when written
as a Riemann sum limit. -/
lemma approxDensity_alt (f : ℝ → ℂ) (hf_cont : Continuous f)
    (T : ℝ) (hT : 0 < T) (ω : ℝ) :
    approxDensity f T ω =
    (1 / (2 * ↑Real.pi * ↑T)) *
    ∫ u in (0:ℝ)..T, ∫ v in (0:ℝ)..T,
      f (u - v) * exp (-I * ↑ω * ↑u) * exp (I * ↑ω * ↑v) := by
  unfold approxDensity
  have hT_ne : (↑T : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hT)
  set g : ℝ → ℂ := fun t => f t * exp (-I * ↑ω * ↑t)
  have hg_cont : Continuous g :=
    hf_cont.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have h_collapse : ∀ u v : ℝ,
      f (u - v) * exp (-I * ↑ω * ↑u) * exp (I * ↑ω * ↑v) = g (u - v) := by
    intro u v; simp only [g]; rw [mul_assoc, ← Complex.exp_add]; congr 1
    simp only [Complex.ofReal_sub]; congr 1; ring
  simp_rw [h_collapse]
  rw [autocorrelation_eq_fejer_integral hg_cont hT]
  have h_intd : (fun t => (↑(fejerWeight T t) : ℂ) * f t * exp (-I * ↑ω * ↑t)) =
      fun t => ↑(fejerWeight T t) * g t := by
    ext t; simp [g]; ring
  rw [h_intd]
  rw [← mul_assoc,
      show (1 / (2 * ↑Real.pi * ↑T) : ℂ) * ↑T = 1 / (2 * ↑Real.pi) from by field_simp]
  congr 1
  exact integral_fejerWeight_mul_eq_intervalIntegral hg_cont hT


/-- Decompose an interval integral into a sum over equispaced sub-intervals:
    `∫_a^{a+NΔ} g = ∑_{j<N} ∫_{a+jΔ}^{a+(j+1)Δ} g`. -/
private lemma integral_eq_sum_adjacent {g : ℝ → ℂ} (hg : Continuous g) (a Δ : ℝ) :
    ∀ N : ℕ, ∫ t in a..(a + ↑N * Δ), g t =
      ∑ j ∈ Finset.range N, ∫ t in (a + ↑j * Δ)..(a + (↑j + 1) * Δ), g t
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, ← integral_eq_sum_adjacent hg a Δ n,
        show (↑(n + 1) : ℝ) = ↑n + 1 from by push_cast; ring]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)).symm

/-- 1D equispaced left-endpoint Riemann sums converge to the interval integral.

Proof via uniform continuity on the compact interval `[0, T]`:
the error per sub-interval is `O(ε' · Δ)` where `ε'` is the modulus
of continuity at scale `Δ = T/N`, giving total error `T · ε' → 0`. -/
private lemma riemann1d_tendsto {g : ℝ → ℂ} (hg : Continuous g)
    {T : ℝ} (hT : 0 < T) :
    Tendsto (fun M : ℕ => ((↑T : ℂ) / (↑(M + 1) : ℂ)) *
      ∑ j ∈ Finset.range (M + 1), g (↑j * T / ↑(M + 1)))
      atTop (𝓝 (∫ t in (0 : ℝ)..T, g t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- ── Step 1: Uniform continuity on [0, T] gives δ for tolerance ε/(2T) ──
  set ε' := ε / (2 * T) with hε'_def
  have hε' : 0 < ε' := by positivity
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Set.Icc 0 T) hg.continuousOn
  obtain ⟨δ, hδ, hδ_uc⟩ := Metric.uniformContinuousOn_iff.mp huc ε' hε'
  -- ── Step 2: Choose threshold so T/(M+1) < δ ──
  obtain ⟨K, hK⟩ := exists_nat_gt (T / δ)
  refine ⟨K, fun M hM => ?_⟩
  set N := M + 1 with hN_def
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr (Nat.succ_pos M)
  have hN_ne : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos
  set Δ := T / ↑N with hΔ_def
  have hΔ_pos : 0 < Δ := div_pos hT hN_pos
  have hNΔ : ↑N * Δ = T := mul_div_cancel₀ T hN_ne
  have hΔ_lt_δ : Δ < δ := by
    rw [hΔ_def, div_lt_iff₀ hN_pos, mul_comm]
    calc T = T / δ * δ := by rw [div_mul_cancel₀ T (ne_of_gt hδ)]
    _ < ↑K * δ := by exact mul_lt_mul_of_pos_right hK hδ
    _ ≤ ↑M * δ := by exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hM) hδ.le
    _ < ↑N * δ := by rw [hN_def]; push_cast; linarith
  -- ── Step 3: Rewrite Riemann sum as ∑_j ↑Δ * g(jΔ) ──
  have hpts : ∀ j : ℕ, (↑j : ℝ) * T / ↑N = ↑j * Δ := fun j => by
    rw [hΔ_def]; ring
  simp_rw [hpts]
  rw [show (↑T : ℂ) / (↑N : ℂ) = (↑Δ : ℂ) from by
    rw [hΔ_def]; push_cast; rw [hN_def]]
  rw [Finset.mul_sum]
  -- ── Step 4: Decompose integral via sub-intervals ──
  have hdecomp : ∫ t in (0 : ℝ)..T, g t =
      ∑ j ∈ Finset.range N, ∫ t in (↑j * Δ)..(↑j * Δ + 1 * Δ), g t := by
    have h := integral_eq_sum_adjacent hg 0 Δ N
    simp only [zero_add, mul_comm 1 Δ] at h ⊢
    grind only
  rw [hdecomp]
  -- ── Step 5: Bound dist = ‖∑_j (↑Δ·g(jΔ) - ∫_{jΔ}^{(j+1)Δ} g)‖ ──
  rw [dist_eq_norm]
  -- Rewrite as norm of sum of differences
  rw [← Finset.sum_sub_distrib]
  -- ── Step 6: Triangle inequality + per-term bound ──
  calc ‖∑ j ∈ Finset.range N,
        ((↑Δ : ℂ) * g (↑j * Δ) - ∫ t in (↑j * Δ)..(↑j * Δ + 1 * Δ), g t)‖
      ≤ ∑ j ∈ Finset.range N,
          ‖(↑Δ : ℂ) * g (↑j * Δ) - ∫ t in (↑j * Δ)..(↑j * Δ + 1 * Δ), g t‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, ε' * Δ := by
        apply Finset.sum_le_sum; intro j hj
        -- Key: ↑Δ * g(jΔ) = ∫ const, so the difference = ∫ (g(jΔ) - g(t)) dt
        rw [show (↑Δ : ℂ) * g (↑j * Δ) =
            ∫ t in (↑j * Δ)..(↑j * Δ + 1 * Δ), g (↑j * Δ) from by
          rw [intervalIntegral.integral_const]; ring_nf; exact Eq.symm real_smul,
          show (∫ t in (↑j * Δ)..(↑j * Δ + 1 * Δ), g (↑j * Δ)) -
               (∫ t in (↑j * Δ)..(↑j * Δ + 1 * Δ), g t) =
               ∫ t in (↑j * Δ)..(↑j * Δ + 1 * Δ), (g (↑j * Δ) - g t) from
            (intervalIntegral.integral_sub
              intervalIntegrable_const (hg.intervalIntegrable _ _)).symm]
        -- ‖∫ (g(jΔ) - g(t)) dt‖ ≤ ε' * |Δ|
        refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
          fun t ht => ?_) (by
          have : |↑j * Δ + 1 * Δ - ↑j * Δ| = Δ := by
            rw [show ↑j * Δ + 1 * Δ - ↑j * Δ = Δ from by ring]
            exact abs_of_pos hΔ_pos
          nlinarith)
        -- Uniform continuity: ‖g(jΔ) - g(t)‖ < ε' for |jΔ - t| < δ
        rw [Set.uIoc_of_le (by linarith : ↑j * Δ ≤ ↑j * Δ + 1 * Δ)] at ht
        obtain ⟨ht_lo, ht_hi⟩ := Set.mem_Ioc.mp ht
        have hj_mem : ↑j * Δ ∈ Set.Icc 0 T := by
          constructor
          · exact mul_nonneg (Nat.cast_nonneg j) hΔ_pos.le
          · have := Finset.mem_range.mp hj
            calc ↑j * Δ ≤ ↑N * Δ :=
                mul_le_mul_of_nonneg_right
                  (by exact_mod_cast (Finset.mem_range.mp hj).le) hΔ_pos.le
            _ = T := hNΔ
        have ht_mem : t ∈ Set.Icc 0 T := by
          constructor
          · linarith [mul_nonneg (Nat.cast_nonneg j) hΔ_pos.le]
          · have := Finset.mem_range.mp hj
            linarith [show ↑j * Δ + 1 * Δ ≤ T from by
              calc ↑j * Δ + 1 * Δ = (↑j + 1) * Δ := by ring
                _ ≤ ↑N * Δ := by
                    exact mul_le_mul_of_nonneg_right
                      (by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj))
                      hΔ_pos.le
                _ = T := hNΔ]
        have hdist : dist (↑j * Δ) t < δ := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith)]
          linarith
        rw [← dist_eq_norm]
        exact le_of_lt (hδ_uc (↑j * Δ) hj_mem t ht_mem hdist)
    _ = T * ε' := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring_nf; nlinarith [hNΔ]
    _ < ε := by rw [hε'_def]; field_simp; linarith


/-- **The crucial non-negativity**: `Λ_T(ω)` is a non-negative real number.

This is where positive-definiteness does its work. The double integral
representation shows Λ_T(ω) is the limit of finite quadratic forms
∑ᵢⱼ c̄ᵢcⱼf(tᵢ-tⱼ) with cⱼ = (1/√(2πT·N)) e^{-iωtⱼ} · Δt,
each of which is non-negative by PD. The limit preserves non-negativity.

Requires: `IsBochnerReady f` (PD + Hermitian + continuous at 0). -/
lemma approxDensity_nonneg (hf : IsContinuous f)
    {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    0 ≤ (approxDensity f T ω).re := by
  rw [approxDensity_alt f hf.continuity T hT ω]
  set D := ∫ u in (0:ℝ)..T, ∫ v in (0:ℝ)..T,
    f (u - v) * exp (-I * ↑ω * ↑u) * exp (I * ↑ω * ↑v)
  have hpre : (0:ℝ) < 1 / (2 * Real.pi * T) := by positivity
  rw [show (1 / (2 * ↑Real.pi * ↑T) : ℂ) = ↑(1 / (2 * Real.pi * T)) from by push_cast; ring]
  rw [re_ofReal_mul]
  exact mul_nonneg hpre.le (re_nonneg_of_riemann_limit hT ω hf)


/-- The approximate spectral density is actually real-valued (imaginary part = 0).

This follows from Hermitian symmetry: f(-t) = conj(f(t)) implies the integral
is self-conjugate. -/
lemma approxDensity_im_eq_zero (hf : IsContinuous f)
    {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    (approxDensity f T ω).im = 0 := by
  unfold approxDensity
  set g : ℝ → ℂ := fun t => (↑(fejerWeight T t) : ℂ) * f t * exp (-I * ↑ω * ↑t)
  suffices him : (∫ t, g t).im = 0 by
    have hp : (1 / (2 * ↑Real.pi) : ℂ).im = 0 := by
      rw [show (1 / (2 * ↑Real.pi) : ℂ) = ↑((2 * Real.pi)⁻¹) from by push_cast; ring]
      exact Complex.ofReal_im _
    rw [Complex.mul_im, him, hp]; ring
  have hconj : ∀ t, g (-t) = starRingEnd ℂ (g t) := by
    intro t
    simp only [neg_mul, ofReal_neg, mul_neg, neg_neg, map_mul, conj_ofReal, g,
               fejerWeight_neg, hf.hermitian t, map_mul, Complex.conj_ofReal,
               ← Complex.exp_conj, map_neg, conj_I]
  have hodd : ∀ t, (g (-t)).im = -(g t).im := fun t => by
    rw [hconj t, Complex.conj_im]
  have hg_cont : Continuous g := by
    apply Continuous.mul
    · exact (continuous_ofReal.comp (fejerWeight_continuous hT)).mul hf.continuity
    · exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hg_int : Integrable g volume :=
    hg_cont.integrable_of_hasCompactSupport
      (isCompact_Icc.of_isClosed_subset (isClosed_tsupport g)
        (closure_minimal (show support g ⊆ Icc (-T) T from fun t ht => by
          simp only [g, Function.mem_support, ne_eq] at ht
          rw [Set.mem_Icc]
          constructor <;> by_contra h <;> push_neg at h
          · exact ht (by simp [fejerWeight_eq_zero_of_abs_ge hT (by linarith [neg_abs_le t])])
          · exact ht (by simp [fejerWeight_eq_zero_of_abs_ge hT (by linarith [le_abs_self t])]))
        isClosed_Icc))
  have him_comm : (∫ t, g t).im = ∫ t, (g t).im := by
    have := (Complex.imCLM.integral_comp_comm hg_int).symm
    simp only at this
    exact this
  rw [him_comm]
  have h_sub : ∫ t, (g (-t)).im = ∫ t, (g t).im := by
    have := integral_sub_left_eq_self (fun t => (g t).im) volume (0 : ℝ)
    simp only [zero_sub] at this; exact this
  have h_neg : ∫ t, (g (-t)).im = -(∫ t, (g t).im) := by
    simp_rw [hodd]
    exact integral_neg _
  linarith


/-- The real-valued approximate density is non-negative. -/
lemma approxDensityReal_nonneg (hf : IsContinuous f)
    {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    0 ≤ approxDensityReal f T ω :=
  approxDensity_nonneg hf hT ω


/-! ### Helpers for integrability of the approximate spectral density -/

/-- The norm of `exp(-I * ω * t)` is 1 (purely imaginary exponent). -/
private lemma norm_exp_neg_I_mul (ω t : ℝ) :
    ‖exp (-I * ↑ω * ↑t)‖ = 1 := by
  have hre : (-I * ↑ω * ↑t : ℂ).re = 0 := by
    simp [mul_re, neg_re, I_re, I_im, ofReal_re, ofReal_im]
  rw [Complex.norm_exp, hre, Real.exp_zero]


/-- The integrand `w_T(t) · f(t) · e^{-iωt}` is bounded by `(f 0).re`, uniformly in `ω`. -/
private lemma approxDensity_integrand_norm_le (hf : IsContinuous f)
    {T : ℝ} (hT : 0 < T) (ω t : ℝ) :
    ‖(↑(fejerWeight T t) : ℂ) * f t * exp (-I * ↑ω * ↑t)‖ ≤ (f 0).re := by
  rw [norm_mul, norm_exp_neg_I_mul, mul_one, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerWeight_nonneg T t)]
  exact le_trans (mul_le_mul_of_nonneg_right (fejerWeight_le_one hT t) (norm_nonneg _))
    (by rw [one_mul]; exact hf.norm_bound t)


/-- The approximate density is continuous in `ω`.

    The integrand has compact support in `t` (via `w_T`) and is jointly continuous
    in `(ω, t)`, so the parametric integral is continuous. -/
lemma approxDensity_continuous (hf : IsContinuous f) {T : ℝ} (hT : 0 < T) :
    Continuous (fun ω => approxDensity f T ω) := by
  unfold approxDensity
  apply Continuous.const_mul
  have h_eq : ∀ ω, (∫ t, ↑(fejerWeight T t) * f t * exp (-I * ↑ω * ↑t)) =
      ∫ t in (-T)..T, ↑(fejerWeight T t) * f t * exp (-I * ↑ω * ↑t) := by
    intro ω
    rw [show (fun t => ↑(fejerWeight T t) * f t * exp (-I * ↑ω * ↑t)) =
        fun t => ↑(fejerWeight T t) * (f t * exp (-I * ↑ω * ↑t)) from by ext; ring]
    exact integral_fejerWeight_mul_eq_intervalIntegral
      (hf.continuity.mul (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))) hT
  simp_rw [h_eq]
  have hF_cont : Continuous (fun p : ℝ × ℝ =>
      (↑(fejerWeight T p.2) : ℂ) * f p.2 * exp (-I * ↑p.1 * ↑p.2)) := by
    apply Continuous.mul
    · exact (continuous_ofReal.comp ((fejerWeight_continuous hT).comp continuous_snd)).mul
        (hf.continuity.comp continuous_snd)
    · exact Complex.continuous_exp.comp
        ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).mul
          (Complex.continuous_ofReal.comp continuous_snd))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF_cont (-T) T


/-- Since the imaginary part vanishes, `approxDensity` equals `↑(approxDensityReal)`. -/
lemma approxDensity_eq_ofReal (hf : IsContinuous f) {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    approxDensity f T ω = ↑(approxDensityReal f T ω) := by
  apply Complex.ext <;> simp [approxDensityReal, approxDensity_im_eq_zero hf hT ω]


/-- The real approximate density is continuous. -/
lemma approxDensityReal_continuous (hf : IsContinuous f) {T : ℝ} (hT : 0 < T) :
    Continuous (approxDensityReal f T) :=
  Complex.continuous_re.comp (approxDensity_continuous hf hT)


/-- Crude uniform bound: `|Λ_T(ω)| ≤ T · (f 0).re / (2π)`. -/
lemma approxDensityReal_le (hf : IsContinuous f) {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    approxDensityReal f T ω ≤ T * (f 0).re / (2 * Real.pi) := by
  unfold approxDensityReal approxDensity
  -- Integrability first (before hc is in scope)
  have hg_cont : Continuous (fun t => (↑(fejerWeight T t) : ℂ) * f t * exp (-I * ↑ω * ↑t)) :=
    ((continuous_ofReal.comp (fejerWeight_continuous hT)).mul hf.continuity).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hg_int : Integrable (fun t => (↑(fejerWeight T t) : ℂ) * f t * exp (-I * ↑ω * ↑t)) :=
    hg_cont.integrable_of_hasCompactSupport
      (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
        (closure_minimal (fun t ht => by
          simp only [Function.mem_support, ne_eq] at ht
          rw [Set.mem_Icc, ← abs_le]
          by_contra h
          push_neg at h
          exact ht (by
            rw [fejerWeight_eq_zero_of_abs_ge hT h.le,
                ofReal_zero, zero_mul, zero_mul]))
        isClosed_Icc))
  have h_fw_int : Integrable (fejerWeight T) :=
    (fejerWeight_continuous hT).integrable_of_hasCompactSupport
      (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
        (closure_minimal (fun t ht => by
          simp only [Function.mem_support, ne_eq] at ht
          rw [Set.mem_Icc, ← abs_le]
          by_contra h
          push_neg at h
          exact ht (fejerWeight_eq_zero_of_abs_ge hT h.le))
        isClosed_Icc))
  -- Now introduce hc for the calc
  have hc : ‖(1 / (2 * ↑Real.pi) : ℂ)‖ = (2 * Real.pi)⁻¹ := by
    rw [show (1 / (2 * ↑Real.pi) : ℂ) = ↑((2 * Real.pi)⁻¹) from by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc (approxDensity f T ω).re ≤ ‖approxDensity f T ω‖ := Complex.re_le_norm _
    _ = ‖(1 / (2 * ↑Real.pi)) * ∫ t, ↑(fejerWeight T t) * f t * exp (-I * ↑ω * ↑t)‖ := rfl
    _ ≤ (2 * Real.pi)⁻¹ * ‖∫ t, ↑(fejerWeight T t) * f t * exp (-I * ↑ω * ↑t)‖ := by
        rw [norm_mul, hc]
    _ ≤ (2 * Real.pi)⁻¹ * ∫ t, ‖↑(fejerWeight T t) * f t * exp (-I * ↑ω * ↑t)‖ := by
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ (2 * Real.pi)⁻¹ * ∫ t, (fejerWeight T t) * (f 0).re := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact integral_mono hg_int.norm (h_fw_int.mul_const _) (fun t => by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (fejerWeight_nonneg T t), norm_exp_neg_I_mul, mul_one]
          exact mul_le_mul_of_nonneg_left (hf.norm_bound t) (fejerWeight_nonneg T t))
    _ = T * (f 0).re / (2 * Real.pi) := by
        rw [integral_mul_const, fejerWeight_integral hT]; ring


/-- The approximate density is integrable on any compact interval. -/
lemma approxDensityReal_integrableOn_Icc (hf : IsContinuous f)
    {T : ℝ} (hT : 0 < T) (R : ℝ) :
    IntegrableOn (approxDensityReal f T) (Icc (-R) R) volume :=
  (approxDensityReal_continuous hf hT).continuousOn.integrableOn_compact isCompact_Icc

/-- The approximate density is measurable. -/
lemma approxDensityReal_measurable (hf : IsContinuous f) {T : ℝ} (hT : 0 < T) :
    Measurable (approxDensityReal f T) :=
  (approxDensityReal_continuous hf hT).measurable


end SpectralBridge.Bochner.BochnerExistence
