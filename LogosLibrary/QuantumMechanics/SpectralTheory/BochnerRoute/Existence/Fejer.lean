/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Existence/Fejer.lean
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.Basic

import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Fourier

namespace SpectralBridge.Bochner.BochnerExistence

open Complex MeasureTheory Filter Topology Set Real Function

variable {f : ℝ → ℂ}

/-! ## §1: The Fejér weight function -/

/-- The Fejér/triangular weight: `w_T(t) = max(1 - |t|/T, 0)`.

This is the autocorrelation of the rectangular window `1_{[0,T]}`,
normalized by T. Its Fourier transform is non-negative (it is the
Fejér kernel), which is the key to the non-negativity of Λ_T. -/
noncomputable def fejerWeight (T : ℝ) (t : ℝ) : ℝ :=
  max (1 - |t| / T) 0

/-- The Fejér weight is supported on `[-T, T]`. -/
lemma fejerWeight_eq_zero_of_abs_ge {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : T ≤ |t|) :
    fejerWeight T t = 0 := by
  unfold fejerWeight
  simp only [max_eq_right_iff]
  simp only [tsub_le_iff_right, zero_add]
  exact (one_le_div₀ hT).mpr ht

/-- The Fejér weight is non-negative. -/
lemma fejerWeight_nonneg (T : ℝ) (t : ℝ) : 0 ≤ fejerWeight T t := by
  unfold fejerWeight; exact le_max_right _ _

/-- The Fejér weight at 0 is 1. -/
lemma fejerWeight_zero {T : ℝ} (_hT : 0 < T) : fejerWeight T 0 = 1 := by
  unfold fejerWeight; simp [abs_zero]


/-- The Fejér weight is bounded above by 1. -/
lemma fejerWeight_le_one {T : ℝ} (hT : 0 < T) (t : ℝ) : fejerWeight T t ≤ 1 := by
  unfold fejerWeight
  exact max_le (sub_le_self 1 (div_nonneg (abs_nonneg t) hT.le)) zero_le_one

/-- The Fejér weight is measurable. -/
lemma fejerWeight_measurable {T : ℝ} (_hT : 0 < T) : Measurable (fejerWeight T) := by
  unfold fejerWeight; fun_prop

/-- The Fejér weight is continuous. -/
lemma fejerWeight_continuous {T : ℝ} (_hT : 0 < T) : Continuous (fejerWeight T) := by
  unfold fejerWeight
  apply Continuous.max
  · exact continuous_const.sub (continuous_abs.div_const T)
  · exact continuous_const

/-- The Fejér weight is even: `w_T(-t) = w_T(t)`. -/
lemma fejerWeight_neg (T : ℝ) (t : ℝ) : fejerWeight T (-t) = fejerWeight T t := by
  unfold fejerWeight; simp [abs_neg]

private lemma  h_supp {T : ℝ} (hT : 0 < T) : Function.support (fejerWeight T) ⊆ Set.Icc (-T) T := by
    intro t ht; simp only [Function.mem_support] at ht
    rw [Set.mem_Icc]; constructor <;> by_contra h <;> push_neg at h
    · exact ht (fejerWeight_eq_zero_of_abs_ge hT (by linarith [neg_abs_le t]))
    · exact ht (fejerWeight_eq_zero_of_abs_ge hT (by linarith [le_abs_self t]))

private lemma h_pos {T : ℝ} (hT : 0 < T): ∫ t in (0:ℝ)..T, fejerWeight T t = T / 2 := by
    trans ∫ t in (0:ℝ)..T, (1 - t / T)
    · exact intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le hT.le] at ht
        obtain ⟨h0, hle⟩ := Set.mem_Icc.mp ht
        unfold fejerWeight
        rw [abs_of_nonneg h0, max_eq_left (by rw [sub_nonneg, div_le_one hT]; exact hle)]
    · have hd : ∀ t ∈ Set.uIcc (0:ℝ) T,
          HasDerivAt (fun x => x - x ^ 2 / (2 * T)) (1 - t / T) t := fun t _ => by
        have h1 : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
        have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * T)) (t / T) t := by
          convert (hasDerivAt_pow 2 t).div_const (2 * T) using 1; field_simp; ring
        exact h1.sub h2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((continuous_const.sub (continuous_id.div_const T)).continuousOn.intervalIntegrable)]
      field_simp; ring

private lemma h_neg {T : ℝ} (hT : 0 < T): ∫ t in (-T)..(0:ℝ), fejerWeight T t = T / 2 := by
    trans ∫ t in (-T)..(0:ℝ), (1 + t / T)
    · exact intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le (by linarith : -T ≤ 0)] at ht
        obtain ⟨hge, h0⟩ := Set.mem_Icc.mp ht
        unfold fejerWeight
        rw [abs_of_nonpos h0, neg_div, sub_neg_eq_add, max_eq_left (by
          rw [show 1 + t / T = (T + t) / T from by field_simp]
          exact div_nonneg (by linarith) hT.le)]
    · have hd : ∀ t ∈ Set.uIcc (-T) (0:ℝ),
          HasDerivAt (fun x => x + x ^ 2 / (2 * T)) (1 + t / T) t := fun t _ => by
        have h1 : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
        have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * T)) (t / T) t := by
          convert (hasDerivAt_pow 2 t).div_const (2 * T) using 1; field_simp; ring
        exact h1.add h2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((continuous_const.add (continuous_id.div_const T)).continuousOn.intervalIntegrable)]
      field_simp; ring


/-- The integral of the Fejér weight: `∫ w_T(t) dt = T`. -/
lemma fejerWeight_integral {T : ℝ} (hT : 0 < T) :
    ∫ t, fejerWeight T t = T := by
  have hT_ne : T ≠ 0 := ne_of_gt hT
  -- ── Integrability (continuous + compact support) ──
  have h_supp : Function.support (fejerWeight T) ⊆ Set.Icc (-T) T := h_supp hT
  have h_int : Integrable (fejerWeight T) volume :=
    (fejerWeight_continuous hT).integrable_of_hasCompactSupport
      (isCompact_Icc.of_isClosed_subset (isClosed_tsupport (fejerWeight T))
        (closure_minimal h_supp isClosed_Icc))
  -- ── Bochner integral = limit of symmetric interval integrals ──
  have h_lim := intervalIntegral_tendsto_integral h_int tendsto_neg_atTop_atBot tendsto_id
  -- ── For R ≥ T the interval integral stabilizes at T ──
  suffices h_val : ∀ R, T ≤ R → ∫ t in (-R)..R, fejerWeight T t = T by
    exact tendsto_nhds_unique h_lim ((tendsto_congr' <|
      (eventually_ge_atTop T).mono fun R hR => (h_val R hR).symm).mp tendsto_const_nhds)
  intro R hR
  have hii : ∀ a b : ℝ, IntervalIntegrable (fejerWeight T) volume a b :=
    fun a b => (fejerWeight_continuous hT).continuousOn.intervalIntegrable
  -- ── FTC on [0, T]: ∫ (1 - t/T) = T/2 ──
  have h_pos : ∫ t in (0:ℝ)..T, fejerWeight T t = T / 2 := h_pos hT
  -- ── FTC on [-T, 0]: ∫ (1 + t/T) = T/2 ──
  have h_neg : ∫ t in (-T)..(0:ℝ), fejerWeight T t = T / 2 := h_neg hT
  -- ── Tails vanish: fejerWeight = 0 when |t| ≥ T ──
  have h_zr : ∫ t in T..R, fejerWeight T t = 0 := by
    rw [intervalIntegral.integral_congr fun t ht => fejerWeight_eq_zero_of_abs_ge hT (by
          simp only [Set.mem_uIcc] at ht
          rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith [le_abs_self t]),
        intervalIntegral.integral_zero]
  have h_zl : ∫ t in (-R)..(-T), fejerWeight T t = 0 := by
    rw [intervalIntegral.integral_congr fun t ht => fejerWeight_eq_zero_of_abs_ge hT (by
          simp only [Set.mem_uIcc] at ht
          rcases ht with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith [neg_abs_le t]),
        intervalIntegral.integral_zero]
  -- ── Assemble: split (-R,R) at -T, 0, T ──
  calc ∫ t in (-R)..R, fejerWeight T t
    _ = (∫ t in (-R)..(0:ℝ), fejerWeight T t) +
        ∫ t in (0:ℝ)..R, fejerWeight T t :=
        (intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)).symm
    _ = ((∫ t in (-R)..(-T), fejerWeight T t) +
          ∫ t in (-T)..(0:ℝ), fejerWeight T t) +
        ((∫ t in (0:ℝ)..T, fejerWeight T t) +
          ∫ t in T..R, fejerWeight T t) := by
          congr 1
          · exact (intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)).symm
          · exact (intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)).symm
    _ = T := by rw [h_zl, h_neg, h_pos, h_zr]; ring

end SpectralBridge.Bochner.BochnerExistence
