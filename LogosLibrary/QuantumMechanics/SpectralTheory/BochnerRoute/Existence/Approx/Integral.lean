/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Existence/Approx/Integral.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.Approx.Defs

namespace SpectralBridge.Bochner.BochnerExistence

open SpectralBridge.Bochner
open Complex MeasureTheory Filter Topology Set Real Function

variable {f : ℝ → ℂ}


/-! ## §2: The approximate spectral density -/


/-! ### Triangle identities via integration by parts -/

/-- Upper triangle: ∫₀ᵀ (∫₀ᵘ g(t) dt) du = ∫₀ᵀ (T - t) · g(t) dt.
    Proof: F(u) = (T-u)·G(u) has F(0) = F(T) = 0, so ∫ F' = 0
    gives ∫ (T-u)g = ∫ G. -/
lemma integral_cumulative {g : ℝ → ℂ} (hg : Continuous g)
    {T : ℝ} (_hT : 0 < T) :
    ∫ u in (0:ℝ)..T, ∫ t in (0:ℝ)..u, g t =
    ∫ t in (0:ℝ)..T, (↑T - ↑t) * g t := by
  -- ── FTC: derivative of the primitive G(u) = ∫₀ᵘ g ──
  have hG_deriv : ∀ u, HasDerivAt (fun u => ∫ t in (0:ℝ)..u, g t) (g u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 u)
      hg.stronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuousAt
  have hG_cont : Continuous (fun u => ∫ t in (0:ℝ)..u, g t) :=
    continuous_iff_continuousAt.mpr fun u => (hG_deriv u).continuousAt
  -- ── Antiderivative F(u) = (T - u) · G(u), derivative = (T-u)g(u) - G(u) ──
  have hF_deriv : ∀ u ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt (fun u => (↑T - ↑u : ℂ) * ∫ t in (0:ℝ)..u, g t)
                 ((↑T - ↑u) * g u - ∫ t in (0:ℝ)..u, g t) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => (↑T - ↑u : ℂ)) (-1 : ℂ) u := by
      convert (hasDerivAt_const u (↑T : ℂ)).sub Complex.ofRealCLM.hasDerivAt using 1
      simp; rfl
    convert h1.mul (hG_deriv u) using 1; ring
  -- ── FTC: ∫₀ᵀ F' = F(T) - F(0) = 0 - 0 = 0 ──
  have h_ii : IntervalIntegrable (fun x => (↑T - ↑x : ℂ) * g x - ∫ t in (0:ℝ)..x, g t)
        volume 0 T :=
      (((continuous_const.sub Complex.continuous_ofReal).mul hg).sub hG_cont).intervalIntegrable 0 T
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv h_ii
  simp only [sub_self, zero_mul, Complex.ofReal_zero, sub_zero,
             intervalIntegral.integral_same, mul_zero] at h_ftc
  -- ── Split ∫ [(T-u)g - G] = 0 into ∫(T-u)g - ∫G = 0, solve ──
  have hf_ii : IntervalIntegrable (fun x => (↑T - ↑x : ℂ) * g x) volume 0 T :=
    ((continuous_const.sub Complex.continuous_ofReal).mul hg).intervalIntegrable 0 T
  have hg_ii : IntervalIntegrable (fun x => ∫ t in (0:ℝ)..x, g t) volume 0 T :=
    hG_cont.intervalIntegrable 0 T
  have key : (∫ x in (0:ℝ)..T, (↑T - ↑x : ℂ) * g x) -
             (∫ x in (0:ℝ)..T, ∫ t in (0:ℝ)..x, g t) = 0 := by
    rw [← intervalIntegral.integral_sub hf_ii hg_ii]
    exact h_ftc
  exact (sub_eq_zero.mp key).symm


/-- Lower triangle: ∫_{-T}^0 (∫_w^0 g(t) dt) dw = ∫_{-T}^0 (t + T) · g(t) dt.
    Same IBP pattern: F̃(w) = (w+T)·G̃(w) with F̃(-T) = F̃(0) = 0. -/
lemma integral_cumulative_neg {g : ℝ → ℂ} (hg : Continuous g)
    {T : ℝ} (_hT : 0 < T) :
    ∫ w in (-T)..(0:ℝ), ∫ t in w..(0:ℝ), g t =
    ∫ t in (-T)..(0:ℝ), (↑t + ↑T) * g t := by
  -- ── Reversed primitive: G̃(w) = ∫_w^0 g = -(∫_0^w g), so G̃' = -g ──
  have hG_eq : (fun w => ∫ t in w..(0:ℝ), g t) =
               (fun w => -(∫ t in (0:ℝ)..w, g t)) :=
    funext fun w => intervalIntegral.integral_symm 0 w
  have hG_deriv_up : ∀ w, HasDerivAt (fun w => ∫ t in (0:ℝ)..w, g t) (g w) w := fun w =>
    intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 w)
      hg.stronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuousAt
  have hG_deriv : ∀ w, HasDerivAt (fun w => ∫ t in w..(0:ℝ), g t) (-g w) w := by
    intro w; rw [hG_eq]; exact (hG_deriv_up w).neg
  have hG_cont : Continuous (fun w => ∫ t in w..(0:ℝ), g t) :=
    continuous_iff_continuousAt.mpr fun w => (hG_deriv w).continuousAt
  -- ── Antiderivative F̃(w) = (w+T) · G̃(w), derivative = G̃(w) - (w+T)·g(w) ──
  have hF_deriv : ∀ w ∈ Set.uIcc (-T) (0:ℝ),
      HasDerivAt (fun w => (↑w + ↑T : ℂ) * ∫ t in w..(0:ℝ), g t)
                 ((∫ t in w..(0:ℝ), g t) - (↑w + ↑T) * g w) w := by
    intro w _
    have h1 : HasDerivAt (fun w : ℝ => (↑w + ↑T : ℂ)) (1 : ℂ) w := by
      convert Complex.ofRealCLM.hasDerivAt.add (hasDerivAt_const w (↑T : ℂ)) using 1
      simp; rfl
    convert h1.mul (hG_deriv w) using 1; ring
  -- ── FTC: ∫ F̃' = F̃(0) - F̃(-T) = T·0 - 0·G̃(-T) = 0 ──
  have h_ii : IntervalIntegrable (fun x => (∫ t in x..(0:ℝ), g t) - (↑x + ↑T : ℂ) * g x)
        volume (-T) 0 :=
      (hG_cont.sub ((Complex.continuous_ofReal.add continuous_const).mul hg)).intervalIntegrable (-T) 0
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv h_ii
  simp only [Complex.ofReal_zero, zero_add, intervalIntegral.integral_same, mul_zero,
             Complex.ofReal_neg, neg_add_cancel, zero_mul, sub_zero] at h_ftc
  -- ── Split and solve ──
  have hf_ii : IntervalIntegrable (fun x => ∫ t in x..(0:ℝ), g t) volume (-T) 0 :=
    hG_cont.intervalIntegrable (-T) 0
  have hg_ii : IntervalIntegrable (fun x => (↑x + ↑T : ℂ) * g x) volume (-T) 0 :=
    ((Complex.continuous_ofReal.add continuous_const).mul hg).intervalIntegrable (-T) 0
  have key : (∫ x in (-T)..(0:ℝ), ∫ t in x..(0:ℝ), g t) -
             (∫ x in (-T)..(0:ℝ), (↑x + ↑T : ℂ) * g x) = 0 := by
    rw [← intervalIntegral.integral_sub hf_ii hg_ii]
    exact h_ftc
  exact (sub_eq_zero.mp key)


/-- **Autocorrelation identity**: ∫∫_{[0,T]²} g(u-v) du dv = T · ∫_{-T}^T w_T(t) g(t) dt.
    The Fejér weight arises as the "overlap length" of [0,T] with its t-shift. -/
lemma autocorrelation_eq_fejer_integral {g : ℝ → ℂ} (hg : Continuous g)
    {T : ℝ} (hT : 0 < T) :
    ∫ u in (0:ℝ)..T, ∫ v in (0:ℝ)..T, g (u - v) =
    ↑T * ∫ t in (-T)..T, ↑(fejerWeight T t) * g t := by
  have hT_ne : (↑T : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hT)
  have hii : ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    fun a b => hg.intervalIntegrable a b
  -- ── Step 1: Inner substitution v ↦ u - v ──
  have h_sub : ∀ u : ℝ, ∫ v in (0:ℝ)..T, g (u - v) = ∫ t in (u - T)..u, g t := by
    intro u
    have := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := T) g u
    simp only [sub_zero] at this
    exact this
  -- ── Step 2: Split inner integral at 0 ──
  simp_rw [h_sub, show ∀ u : ℝ, ∫ t in (u - T)..u, g t =
    (∫ t in (u - T)..(0:ℝ), g t) + ∫ t in (0:ℝ)..u, g t from
    fun u => (intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)).symm]
  -- ── Step 3: Split outer integral over the sum ──
  have hA_cont : Continuous (fun u => ∫ t in (0:ℝ)..u, g t) :=
    continuous_iff_continuousAt.mpr fun u =>
      (intervalIntegral.integral_hasDerivAt_right (hii 0 u)
        hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).continuousAt
  have hB_cont : Continuous (fun u => ∫ t in (u - T)..(0:ℝ), g t) :=
    -- ∫_{u-T}^0 g = -(∫_0^{u-T} g), and u ↦ ∫_0^{u-T} is continuous
    (hA_cont.comp (continuous_id.sub continuous_const)).neg.congr
      fun u => (intervalIntegral.integral_symm 0 (u - T)).symm
  rw [intervalIntegral.integral_add
    hB_cont.continuousOn.intervalIntegrable
    hA_cont.continuousOn.intervalIntegrable]
  -- ── Step 4: Upper triangle ──
  have h_upper := integral_cumulative hg hT
  -- ── Step 5: Lower triangle — substitute w = u - T in outer integral ──
  have h_outer_sub : ∫ u in (0:ℝ)..T, ∫ t in (u - T)..(0:ℝ), g t =
      ∫ w in (-T)..(0:ℝ), ∫ t in w..(0:ℝ), g t := by
    convert intervalIntegral.integral_comp_sub_right
      (fun w => ∫ t in w..(0:ℝ), g t) T using 2 <;> ring
  have h_lower := h_outer_sub.trans (integral_cumulative_neg hg hT)
  -- ── Step 6: Combine and factor T ──
  rw [h_lower, h_upper]
  -- Goal: ∫_{-T}^0 (t+T)g + ∫_0^T (T-t)g = T · ∫_{-T}^T fejerWeight·g
  -- Split RHS at 0
  have h_fg_cont : Continuous (fun t => (↑(fejerWeight T t) : ℂ) * g t) :=
    (continuous_ofReal.comp (fejerWeight_continuous hT)).mul hg
  rw [show ∫ t in (-T)..T, ↑(fejerWeight T t) * g t =
    (∫ t in (-T)..(0:ℝ), ↑(fejerWeight T t) * g t) +
     ∫ t in (0:ℝ)..T, ↑(fejerWeight T t) * g t from
    (intervalIntegral.integral_add_adjacent_intervals
      (h_fg_cont.intervalIntegrable (-T) 0)
      (h_fg_cont.intervalIntegrable 0 T)).symm,
    mul_add]
  -- Match each half: (t+T) = T · fejerWeight on [-T,0], (T-t) = T · fejerWeight on [0,T]
  congr 1
  · -- Negative half
    trans ∫ t in (-T)..(0:ℝ), ↑T * (↑(fejerWeight T t) * g t)
    · exact intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le (by linarith : -T ≤ (0:ℝ))] at ht
        obtain ⟨h1, h2⟩ := Set.mem_Icc.mp ht
        have hw : fejerWeight T t = (t + T) / T := by
          unfold fejerWeight
          rw [abs_of_nonpos h2, neg_div, sub_neg_eq_add, max_eq_left (by
              rw [one_add_div fun a => hT_ne (congrArg ofReal a)]
              exact div_nonneg (by linarith) hT.le)]
          field_simp
          exact AddCommMagma.add_comm T t
        push_cast [hw]; field_simp
    · exact intervalIntegral.integral_const_mul ↑T fun x => ↑(fejerWeight T x) * g x
  · -- Positive half
    trans ∫ t in (0:ℝ)..T, ↑T * (↑(fejerWeight T t) * g t)
    · exact intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le hT.le] at ht
        obtain ⟨h1, h2⟩ := Set.mem_Icc.mp ht
        have hw : fejerWeight T t = (T - t) / T := by
          unfold fejerWeight
          rw [abs_of_nonneg h1,
              max_eq_left (sub_nonneg.mpr (div_le_one_of_le₀ h2 hT.le))]
          field_simp
        push_cast [hw]; field_simp
    · exact intervalIntegral.integral_const_mul ↑T fun x => ↑(fejerWeight T x) * g x


/-- The full-line integral of fejerWeight * h equals the interval integral on [-T, T],
    since fejerWeight vanishes outside this interval. -/
lemma integral_fejerWeight_mul_eq_intervalIntegral {h : ℝ → ℂ} (hh : Continuous h)
    {T : ℝ} (hT : 0 < T) :
    ∫ t, (↑(fejerWeight T t) : ℂ) * h t =
    ∫ t in (-T)..T, ↑(fejerWeight T t) * h t := by
  set F := fun t => (↑(fejerWeight T t) : ℂ) * h t
  have hF_cont : Continuous F :=
    (continuous_ofReal.comp (fejerWeight_continuous hT)).mul hh
  -- Support of F is contained in [-T, T]
  have h_supp : Function.support F ⊆ Set.Icc (-T) T := by
    intro t ht
    simp only [F, Function.mem_support, ne_eq] at ht
    rw [Set.mem_Icc]
    constructor <;> by_contra h <;> push_neg at h
    · exact ht (by simp [fejerWeight_eq_zero_of_abs_ge hT (by linarith [neg_abs_le t])])
    · exact ht (by simp [fejerWeight_eq_zero_of_abs_ge hT (by linarith [le_abs_self t])])
  have h_int : Integrable F volume :=
    hF_cont.integrable_of_hasCompactSupport
      (isCompact_Icc.of_isClosed_subset (isClosed_tsupport F)
        (closure_minimal h_supp isClosed_Icc))
  -- Full-line = set integral on Icc
  have h_full : ∫ t, F t = ∫ t in Set.Icc (-T) T, F t := by
    rw [← integral_add_compl measurableSet_Icc h_int]
    rw [@add_eq_left]
    exact setIntegral_eq_zero_of_forall_eq_zero fun t ht => by
      simp only [F, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at ht ⊢
      rcases ht with h | h
      · simp [fejerWeight_eq_zero_of_abs_ge hT (by linarith [neg_abs_le t])]
      · simp [fejerWeight_eq_zero_of_abs_ge hT (by linarith [le_abs_self t])]
  -- Set integral on Icc = interval integral (Icc and Ioc differ by null set)
  rw [h_full, intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  exact integral_Icc_eq_integral_Ioc

end SpectralBridge.Bochner.BochnerExistence
