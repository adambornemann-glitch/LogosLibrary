/-
Author: Adam Bornemann
Created: 11-26-2025
Updated: 12-26-2025

================================================================================
STONE'S THEOREM: BOCHNER INTEGRATION MACHINERY
================================================================================

This file provides the Bochner integration infrastructure needed for Stone's theorem:

1. EXISTENCE DIRECTION: Construct the generator's domain via integral formulas
   - ψ₊ = i ∫₀^∞ e^{-t} U(t)φ dt   solves (A + iI)ψ₊ = φ
   - ψ₋ = -i ∫₀^∞ e^{-t} U(-t)φ dt solves (A - iI)ψ₋ = φ

2. DUHAMEL ESTIMATE: The variation of parameters formula
   - U(t)φ - exp(tB)φ = ∫₀ᵗ exp((t-s)B) · (iA - B) · U(s)φ ds

3. DENSITY OF DOMAIN: Show D(A) is dense via averaged vectors
   - ∫₀ʰ U(t)φ dt ∈ D(A) for all φ ∈ H

References:
  - Reed & Simon, "Methods of Modern Mathematical Physics" Vol. 1, Ch. VIII
  - Engel & Nagel, "One-Parameter Semigroups for Linear Evolution Equations"
  - Mathlib Bochner integration: MeasureTheory.Integral.Bochner
-/
/- Bochner Imports -/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
/- Integral Interval Imports -/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
/- Analysis Imports -/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
/- Topology Imports -/
import Mathlib.Topology.MetricSpace.Basic
/- Missing and|or Borken Imports-/
--import Mathlib.MeasureTheory.Integral.Bochner.Dominated
--import Mathlib.MeasureTheory.Function.L1Space
--import Mathlib.Analysis.SpecialFunctions.Integrals

import LogosLibrary.DeepTheorems.Quantum.Evolution.Generator

namespace StonesTheorem.Bochner

open MeasureTheory Measure Filter Topology Complex Stone.Generators
open scoped ENNReal NNReal BigOperators Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
set_option linter.unusedSectionVars false

/-!
================================================================================
SECTION 1: BASIC BOCHNER INTEGRATION FOR HILBERT SPACES
================================================================================

Setup the basic facts about Bochner integrability in Hilbert spaces.
-/
--set_option maxHeartbeats 1000000
section BasicBochner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A continuous function with exponential decay is integrable on [0, ∞). -/
lemma integrable_exp_decay_continuous
    (f : ℝ → E) (hf_cont : Continuous f)
    (C : ℝ) (hC : ∀ t ≥ 0, ‖f t‖ ≤ C) :
    IntegrableOn (fun t => Real.exp (-t) • f t) (Set.Ici 0) volume := by
  -- Use max to ensure positive bound
  set M := max |C| 1 with hM_def
  have hM_pos : 0 < M := lt_max_of_lt_right one_pos
  have hM_ge : |C| ≤ M := le_max_left _ _

  -- Step 1: The bound function M * e^{-t} is integrable on [0, ∞)
  have h_exp_int : IntegrableOn (fun t => Real.exp (-t)) (Set.Ici 0) volume := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (ι := ℕ) (l := atTop)
          (b := fun n => (n : ℝ)) 1 0 ?_ ?_ ?_
    · intro i
      apply Continuous.integrableOn_Ioc
      exact Real.continuous_exp.comp continuous_neg
    · exact tendsto_natCast_atTop_atTop
    · filter_upwards with n
      have h_norm_eq : ∀ x, ‖Real.exp (-x)‖ = Real.exp (-x) := fun x =>
        Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))
      simp_rw [h_norm_eq]
      have h_cont : Continuous (fun t => Real.exp (-t)) := Real.continuous_exp.comp continuous_neg
      have h_antideriv_cont : Continuous (fun t => -Real.exp (-t)) := h_cont.neg
      have h_int : ∫ x in (0 : ℝ)..n, Real.exp (-x) = -Real.exp (-↑n) - -Real.exp 0 := by
        convert intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := 0) (b := n)
                (f := fun t => -Real.exp (-t)) (f' := fun t => Real.exp (-t))
                (by linarith) h_antideriv_cont.continuousOn ?_ (h_cont.intervalIntegrable _ _) using 1
        · simp only [neg_zero, Real.exp_zero]
        · intro x _
          have h1 : HasDerivAt (fun t => -t) (-1) x := hasDerivAt_neg x
          have h2 : HasDerivAt Real.exp (Real.exp (-x)) (-x) := Real.hasDerivAt_exp (-x)
          have h3 := h2.comp x h1
          simp only [mul_neg, mul_one] at h3
          convert h3.neg using 1
          ring
      calc ∫ x in (0 : ℝ)..n, Real.exp (-x)
          = -Real.exp (-↑n) - -Real.exp 0 := h_int
        _ = -Real.exp (-↑n) - -1 := by rw [Real.exp_zero]
        _ = 1 - Real.exp (-↑n) := by ring
        _ ≤ 1 := by linarith [Real.exp_pos (-↑n)]

  have h_bound_int : IntegrableOn (fun t => M * Real.exp (-t)) (Set.Ici 0) volume :=
    h_exp_int.const_mul M

  -- Step 2: Our function is measurable
  have h_meas : AEStronglyMeasurable (fun t => Real.exp (-t) • f t)
                                      (volume.restrict (Set.Ici 0)) := by
    apply AEStronglyMeasurable.smul
    · exact (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable.restrict
    · exact hf_cont.aestronglyMeasurable.restrict

  -- Step 3: Pointwise bound
  have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ici 0)),
                  ‖Real.exp (-t) • f t‖ ≤ M * Real.exp (-t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
    calc Real.exp (-t) * ‖f t‖
        ≤ Real.exp (-t) * |C| := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            calc ‖f t‖ ≤ C := hC t ht
              _ ≤ |C| := le_abs_self C
      _ ≤ Real.exp (-t) * M := mul_le_mul_of_nonneg_left hM_ge (Real.exp_pos _).le
      _ = M * Real.exp (-t) := mul_comm _ _

  -- Step 4: Apply domination
  exact Integrable.mono' h_bound_int h_meas h_bound


/-- The integral ∫₀^∞ e^{-t} dt = 1. -/
lemma integral_exp_neg_eq_one :
    ∫ t in Set.Ici (0 : ℝ), Real.exp (-t) = 1 := by
  rw [integral_Ici_eq_integral_Ioi]

  -- Apply FTC for improper integrals
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
      (f := fun t => -Real.exp (-t)) (m := 0)]
  · simp [Real.exp_zero]
  · intro x _
    have h1 : HasDerivAt (fun t => -t) (-1) x := hasDerivAt_neg x
    have h2 : HasDerivAt Real.exp (Real.exp (-x)) (-x) := Real.hasDerivAt_exp (-x)
    have h3 := h2.comp x h1
    simp only [mul_neg, mul_one] at h3
    convert h3.neg using 1
    ring
  · -- IntegrableOn (fun t => Real.exp (-t)) (Set.Ioi 0) volume
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (ι := ℕ) (l := atTop)
           (b := fun n => (n : ℝ)) 1 0 ?_ ?_ ?_
    · intro i
      apply Continuous.integrableOn_Ioc
      exact Real.continuous_exp.comp continuous_neg
    · exact tendsto_natCast_atTop_atTop
    · filter_upwards with n
      have h_norm_eq : ∀ x, ‖Real.exp (-x)‖ = Real.exp (-x) := fun x =>
        Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))
      simp_rw [h_norm_eq]
      have h_cont : Continuous (fun t => Real.exp (-t)) := Real.continuous_exp.comp continuous_neg
      have h_antideriv_cont : Continuous (fun t => -Real.exp (-t)) := h_cont.neg
      have h_int : ∫ x in (0 : ℝ)..n, Real.exp (-x) = -Real.exp (-↑n) - -Real.exp 0 := by
        convert intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := 0) (b := n)
                (f := fun t => -Real.exp (-t)) (f' := fun t => Real.exp (-t))
                (by linarith) h_antideriv_cont.continuousOn ?_ (h_cont.integrableOn_Icc.intervalIntegrable) using 1
        · simp only [neg_zero, Real.exp_zero]
        · intro x _
          have h1 : HasDerivAt (fun t => -t) (-1) x := hasDerivAt_neg x
          have h2 : HasDerivAt Real.exp (Real.exp (-x)) (-x) := Real.hasDerivAt_exp (-x)
          have h3 := h2.comp x h1
          simp only [mul_neg, mul_one] at h3
          convert h3.neg using 1
          ring
      calc ∫ x in (0 : ℝ)..n, Real.exp (-x)
          = -Real.exp (-↑n) - -Real.exp 0 := h_int
        _ = -Real.exp (-↑n) - -1 := by rw [Real.exp_zero]
        _ = 1 - Real.exp (-↑n) := by ring
        _ ≤ 1 := by linarith [Real.exp_pos (-↑n)]
  -- ⊢ Tendsto (fun t => -Real.exp (-t)) atTop (𝓝 0)
  · convert (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).neg using 1
    simp


/-- Integral bound for exponentially decaying functions. -/
lemma norm_integral_exp_decay_le
    (f : ℝ → E) (hf_cont : Continuous f)
    (C : ℝ) (hC : ∀ t ≥ 0, ‖f t‖ ≤ C) (_ /-hC_pos-/ : 0 ≤ C) :
    ‖∫ t in Set.Ici 0, Real.exp (-t) • f t‖ ≤ C := by
  -- Get integrability from previous lemma
  have h_integrand_int : IntegrableOn (fun t => Real.exp (-t) • f t) (Set.Ici 0) volume :=
    integrable_exp_decay_continuous f hf_cont C hC

  -- Integrability of exp(-t)
  have h_exp_int : IntegrableOn (fun t => Real.exp (-t)) (Set.Ici 0) volume := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (ι := ℕ) (l := atTop)
           (b := fun n => (n : ℝ)) 1 0 ?_ ?_ ?_
    · intro i
      apply Continuous.integrableOn_Ioc
      exact Real.continuous_exp.comp continuous_neg
    · exact tendsto_natCast_atTop_atTop
    · filter_upwards with n
      have h_norm_eq : ∀ x, ‖Real.exp (-x)‖ = Real.exp (-x) := fun x =>
        Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))
      simp_rw [h_norm_eq]
      have h_cont : Continuous (fun t => Real.exp (-t)) := Real.continuous_exp.comp continuous_neg
      have h_antideriv_cont : Continuous (fun t => -Real.exp (-t)) := h_cont.neg
      have h_int : ∫ x in (0 : ℝ)..n, Real.exp (-x) = -Real.exp (-↑n) - -Real.exp 0 := by
        convert intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := 0) (b := n)
                (f := fun t => -Real.exp (-t)) (f' := fun t => Real.exp (-t))
                (by linarith) h_antideriv_cont.continuousOn ?_ (h_cont.intervalIntegrable _ _) using 1
        · simp only [neg_zero, Real.exp_zero]
        · intro x _
          have h1 : HasDerivAt (fun t => -t) (-1) x := hasDerivAt_neg x
          have h2 : HasDerivAt Real.exp (Real.exp (-x)) (-x) := Real.hasDerivAt_exp (-x)
          have h3 := h2.comp x h1
          simp only [mul_neg, mul_one] at h3
          convert h3.neg using 1
          ring
      calc ∫ x in (0 : ℝ)..n, Real.exp (-x)
          = -Real.exp (-↑n) - -Real.exp 0 := h_int
        _ = -Real.exp (-↑n) - -1 := by rw [Real.exp_zero]
        _ = 1 - Real.exp (-↑n) := by ring
        _ ≤ 1 := by linarith [Real.exp_pos (-↑n)]

  calc ‖∫ t in Set.Ici 0, Real.exp (-t) • f t‖
      ≤ ∫ t in Set.Ici 0, ‖Real.exp (-t) • f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ici 0, C * Real.exp (-t) := by
        apply setIntegral_mono_on h_integrand_int.norm (h_exp_int.const_mul C) measurableSet_Ici
        intro t ht
        rw [norm_smul, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
        calc Real.exp (-t) * ‖f t‖
            ≤ Real.exp (-t) * C := mul_le_mul_of_nonneg_left (hC t ht) (Real.exp_pos _).le
          _ = C * Real.exp (-t) := mul_comm _ _
    _ = C * ∫ t in Set.Ici 0, Real.exp (-t) := by exact MeasureTheory.integral_const_mul C fun a => Real.exp (-a)
    _ = C * 1 := by rw [integral_exp_neg_eq_one]
    _ = C := mul_one C



/-- Truncated integrals converge to the improper integral. -/
lemma tendsto_integral_Ioc_exp_decay
    (f : ℝ → E) (hf_cont : Continuous f)
    (C : ℝ) (hC : ∀ t ≥ 0, ‖f t‖ ≤ C) :
    Tendsto (fun T => ∫ t in Set.Ioc 0 T, Real.exp (-t) • f t)
            atTop
            (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • f t)) := by
  rw [integral_Ici_eq_integral_Ioi]

  have h_int : IntegrableOn (fun t => Real.exp (-t) • f t) (Set.Ioi 0) volume :=
    (integrable_exp_decay_continuous f hf_cont C hC).mono_set Set.Ioi_subset_Ici_self

  rw [Metric.tendsto_atTop]
  intro ε hε

  -- Use that ∫_{Ioi n} ‖g‖ → 0 for integrable g
  set M := max C 0 with hM_def
  have hM_nonneg : 0 ≤ M := le_max_right _ _

  -- Bound: ‖e^{-t} • f t‖ ≤ M * e^{-t}
  have h_norm_int : IntegrableOn (fun t => M * Real.exp (-t)) (Set.Ioi 0) volume := by
    have h_exp : IntegrableOn (fun t => Real.exp (-t)) (Set.Ioi 0) volume := by
      refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (ι := ℕ) (l := atTop)
             (b := fun n => (n : ℝ)) 1 0 ?_ ?_ ?_
      · intro i
        apply Continuous.integrableOn_Ioc
        exact Real.continuous_exp.comp continuous_neg
      · exact tendsto_natCast_atTop_atTop
      · filter_upwards with n
        have h_norm_eq : ∀ x, ‖Real.exp (-x)‖ = Real.exp (-x) := fun x =>
          Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))
        simp_rw [h_norm_eq]
        have h_cont : Continuous (fun t => Real.exp (-t)) := Real.continuous_exp.comp continuous_neg
        have h_antideriv_cont : Continuous (fun t => -Real.exp (-t)) := h_cont.neg
        have h_int : ∫ x in (0 : ℝ)..n, Real.exp (-x) = -Real.exp (-↑n) - -Real.exp 0 := by
          convert intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := 0) (b := n)
                  (f := fun t => -Real.exp (-t)) (f' := fun t => Real.exp (-t))
                  (by linarith) h_antideriv_cont.continuousOn ?_
                  (h_cont.integrableOn_Icc.intervalIntegrable) using 1
          · simp only [neg_zero, Real.exp_zero]
          · intro x _
            have h1 : HasDerivAt (fun t => -t) (-1) x := hasDerivAt_neg x
            have h2 : HasDerivAt Real.exp (Real.exp (-x)) (-x) := Real.hasDerivAt_exp (-x)
            have h3 := h2.comp x h1
            simp only [mul_neg, mul_one] at h3
            convert h3.neg using 1
            ring
        calc ∫ x in (0 : ℝ)..n, Real.exp (-x)
            = -Real.exp (-↑n) - -Real.exp 0 := h_int
          _ = -Real.exp (-↑n) - -1 := by rw [Real.exp_zero]
          _ = 1 - Real.exp (-↑n) := by ring
          _ ≤ 1 := by linarith [Real.exp_pos (-↑n)]
    exact h_exp.const_mul M

  -- The tail ∫_{Ioi T} M * e^{-t} dt = M * e^{-T} → 0
  have h_tail_bound : ∀ T ≥ 0, ∫ t in Set.Ioi T, M * Real.exp (-t) = M * Real.exp (-T) := by
    intro T hT
    have h_deriv : ∀ x ∈ Set.Ici T, HasDerivAt (fun t => -M * Real.exp (-t)) (M * Real.exp (-x)) x := by
      intro x _
      have h1 : HasDerivAt (fun t => -t) (-1) x := hasDerivAt_neg x
      have h2 : HasDerivAt Real.exp (Real.exp (-x)) (-x) := Real.hasDerivAt_exp (-x)
      have h3 := h2.comp x h1
      have h4 : HasDerivAt (fun t => M * Real.exp (-t)) (M * (Real.exp (-x) * -1)) x :=
        h3.const_mul M
      have h5 := h4.neg
      -- h5 : HasDerivAt (fun t => -(M * Real.exp (-t))) (-(M * (Real.exp (-x) * -1))) x
      convert h5 using 1 <;> ring_nf ; exact rfl

    have h_int : IntegrableOn (fun t => M * Real.exp (-t)) (Set.Ioi T) volume :=
      h_norm_int.mono_set (Set.Ioi_subset_Ioi hT)
    have h_tend : Tendsto (fun t => -M * Real.exp (-t)) atTop (𝓝 0) := by
      have : Tendsto (fun t => -M * Real.exp (-t)) atTop (𝓝 (-M * 0)) := by
        apply Tendsto.const_mul
        exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
      simp only [mul_zero] at this -- neg_zero is unused
      exact this
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (a := T) (f := fun t => -M * Real.exp (-t)) (m := 0)
        h_deriv h_int h_tend]
    ring


  -- Choose T large enough that M * e^{-T} < ε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M * Real.exp (-(N : ℝ)) < ε := by
    by_cases hM_zero : M = 0
    · exact ⟨0, by simp [hM_zero, hε]⟩
    · have hM_pos : 0 < M := lt_of_le_of_ne hM_nonneg (Ne.symm hM_zero)
      have : Tendsto (fun n : ℕ => M * Real.exp (-(n : ℝ))) atTop (𝓝 (M * 0)) := by
        apply Tendsto.const_mul
        exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      simp at this
      exact (this.eventually (gt_mem_nhds hε)).exists

  use max 1 N
  intro T hT
  have hT_pos : 0 < T := by
    have : (1 : ℝ) ≤ max 1 (N : ℝ) := le_max_left 1 (N : ℝ)
    linarith

  -- Split the integral
  have h_split : ∫ t in Set.Ioi 0, Real.exp (-t) • f t ∂volume =
                 (∫ t in Set.Ioc 0 T, Real.exp (-t) • f t ∂volume) +
                 (∫ t in Set.Ioi T, Real.exp (-t) • f t ∂volume) := by
    have h_union : Set.Ioc 0 T ∪ Set.Ioi T = Set.Ioi 0 := by
      ext x
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · intro h; cases h with
        | inl h => exact h.1
        | inr h => exact lt_trans hT_pos h
      · intro hx
        by_cases hxT : x ≤ T
        · left; exact ⟨hx, hxT⟩
        · right; exact lt_of_not_ge hxT
    rw [← h_union, setIntegral_union (Set.Ioc_disjoint_Ioi (le_refl T)) measurableSet_Ioi
          (h_int.mono_set Set.Ioc_subset_Ioi_self) (h_int.mono_set (Set.Ioi_subset_Ioi hT_pos.le))]

  rw [h_split, dist_eq_norm]
  have h_simp : (∫ t in Set.Ioc 0 T, Real.exp (-t) • f t) -
                ((∫ t in Set.Ioc 0 T, Real.exp (-t) • f t) + ∫ t in Set.Ioi T, Real.exp (-t) • f t) =
                -(∫ t in Set.Ioi T, Real.exp (-t) • f t) := by abel
  rw [h_simp, norm_neg]
  -- Bound: ‖∫_{Ioi T} g‖ ≤ ∫_{Ioi T} ‖g‖ ≤ ∫_{Ioi T} M * e^{-t}
  calc ‖∫ t in Set.Ioi T, Real.exp (-t) • f t‖
      ≤ ∫ t in Set.Ioi T, ‖Real.exp (-t) • f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi T, M * Real.exp (-t) := by
        apply setIntegral_mono_on (h_int.mono_set (Set.Ioi_subset_Ioi hT_pos.le)).norm
              (h_norm_int.mono_set (Set.Ioi_subset_Ioi hT_pos.le)) measurableSet_Ioi
        intro t ht
        rw [norm_smul, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        calc ‖f t‖ ≤ C := hC t (le_of_lt (lt_trans hT_pos ht))
          _ ≤ M := le_max_left _ _
    _ = M * Real.exp (-T) := h_tail_bound T hT_pos.le
    _ ≤ M * Real.exp (-(N : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hM_nonneg
        apply Real.exp_le_exp.mpr
        have h1 : (N : ℝ) ≤ max 1 N := Nat.cast_le.mpr (le_max_right 1 N)
        simp_all only [ge_iff_le, gt_iff_lt, le_sup_right, sup_le_iff, sub_add_cancel_left, Nat.cast_max, Nat.cast_one,
          neg_le_neg_iff, M]
    _ < ε := hN



/-- Differentiation under the integral sign for parameter-dependent integrals. -/
lemma hasDerivAt_integral_of_exp_decay
    (f : ℝ → ℝ → E)
    (hf_cont : Continuous (Function.uncurry f))
    (hf_deriv : ∀ t s, HasDerivAt (f · s) (deriv (f · s) t) t)
    (hf'_cont : ∀ t, Continuous (fun s => deriv (f · s) t))  -- NEW
    (C : ℝ) (hC : ∀ t s, s ≥ 0 → ‖f t s‖ ≤ C)
    (hC' : ∀ t s, s ≥ 0 → ‖deriv (f · s) t‖ ≤ C)
    (t : ℝ) :
    HasDerivAt (fun τ => ∫ s in Set.Ici 0, Real.exp (-s) • f τ s)
               (∫ s in Set.Ici 0, Real.exp (-s) • deriv (f · s) t)
               t := by
  let μ := volume.restrict (Set.Ici (0 : ℝ))
  let M := max |C| 1
  have hM_pos : 0 < M := lt_max_of_lt_right one_pos
  have hC_le_M : |C| ≤ M := le_max_left _ _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (ε := 1) (x₀ := t)
    (F := fun τ s => Real.exp (-s) • f τ s)
    (F' := fun τ s => Real.exp (-s) • deriv (f · s) τ)
    (bound := fun s => M * Real.exp (-s))
    one_pos ?hF_meas ?hF_int ?hF'_meas ?hF'_bound ?hbound_int ?hF_deriv
  exact h.2
  case hF_meas =>
    filter_upwards with τ
    apply AEStronglyMeasurable.smul
    · exact (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable
    · exact (hf_cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  case hF_int =>
    have hf_t_cont : Continuous (fun s => f t s) :=
      hf_cont.comp (continuous_const.prodMk continuous_id)
    have hf_t_bound : ∀ s ≥ 0, ‖f t s‖ ≤ |C| := fun s hs => (hC t s hs).trans (le_abs_self C)
    exact integrable_exp_decay_continuous (fun s => f t s) hf_t_cont |C| hf_t_bound
  case hF'_meas =>
    apply AEStronglyMeasurable.smul
    · exact (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable
    · exact (hf'_cont t).aestronglyMeasurable
  case hF'_bound =>
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs τ _
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
    have h1 : ‖deriv (f · s) τ‖ ≤ C := hC' τ s hs
    calc Real.exp (-s) * ‖deriv (f · s) τ‖
        ≤ Real.exp (-s) * M := by
          apply mul_le_mul_of_nonneg_left
          exact h1.trans ((le_abs_self C).trans hC_le_M)
          exact le_of_lt (Real.exp_pos _)
      _ = M * Real.exp (-s) := mul_comm _ _
  case hbound_int =>
    -- M * exp(-s) integrable on [0,∞)
    have h_exp_int : IntegrableOn (fun s => Real.exp (-s)) (Set.Ici 0) volume := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (ι := ℕ) (l := atTop)
            (b := fun n => (n : ℝ)) 1 0 ?_ ?_ ?_
      · -- IntegrableOn on finite intervals
        intro i
        exact (Real.continuous_exp.comp continuous_neg).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      · -- Tendsto
        exact tendsto_natCast_atTop_atTop
      · -- Bounded integrals
        filter_upwards with n
        -- First simplify ‖exp(-x)‖ = exp(-x) inside the integral
        have h_norm_eq : ∫ x in (0:ℝ)..n, ‖Real.exp (-x)‖ = ∫ x in (0:ℝ)..n, Real.exp (-x) := by
          congr 1
          ext x
          exact Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))
        rw [h_norm_eq]
        have h_eq : ∫ t in (0:ℝ)..n, Real.exp (-t) = 1 - Real.exp (-(n:ℝ)) := by
          by_cases hn : (n : ℝ) ≤ 0
          · have hn' : n = 0 := by
              have h1 : (n : ℝ) = 0 := le_antisymm hn (Nat.cast_nonneg n)
              exact Nat.cast_eq_zero.mp h1
            simp [hn', intervalIntegral.integral_same]
          · push_neg at hn
            have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) n, HasDerivAt (fun t => -Real.exp (-t)) (Real.exp (-x)) x := by
              intro x _
              have h1 : HasDerivAt (fun t => -t) (-1) x := hasDerivAt_neg x
              have h2 : HasDerivAt Real.exp (Real.exp (-x)) (-x) := Real.hasDerivAt_exp (-x)
              have h3 : HasDerivAt (fun t => Real.exp (-t)) (Real.exp (-x) * -1) x := h2.comp x h1
              have h4 : HasDerivAt (fun t => -Real.exp (-t)) (-(Real.exp (-x) * -1)) x := h3.neg
              simp only [mul_neg_one, neg_neg] at h4
              exact h4
            convert intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hn)
                    (a := 0) (b := n) (f := fun t => -Real.exp (-t)) (f' := fun t => Real.exp (-t))
                    ((Real.continuous_exp.comp continuous_neg).continuousOn.neg)
                    (fun x hx => hderiv x hx)
                    ((Real.continuous_exp.comp continuous_neg).intervalIntegrable 0 n) using 1
            simp only [neg_zero, Real.exp_zero]; ring
        rw [h_eq]
        have hexp_pos : 0 < Real.exp (-(n:ℝ)) := Real.exp_pos _
        linarith
    exact h_exp_int.const_mul M
  case hF_deriv =>
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s _ τ _
    exact (hf_deriv τ s).const_smul (Real.exp (-s))

end BasicBochner

/-!
================================================================================
SECTION 2: UNITARY GROUP INTEGRATION
================================================================================

Integration of strongly continuous unitary groups.
-/

section UnitaryGroupIntegration

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The function t ↦ U(t)φ is continuous (strong continuity). -/
lemma continuous_unitary_apply (φ : H) :
    Continuous (fun t => U_grp.U t φ) :=
  U_grp.strong_continuous φ

/-- The function t ↦ e^{-t} U(t)φ is integrable on [0, ∞). -/
lemma integrable_exp_neg_unitary (φ : H) :
    IntegrableOn (fun t => Real.exp (-t) • U_grp.U t φ) (Set.Ici 0) volume := by
  apply integrable_exp_decay_continuous
    (fun t => U_grp.U t φ)
    (U_grp.strong_continuous φ)
    ‖φ‖
  intro t _ht
  exact le_of_eq (norm_preserving U_grp t φ)

/-- The function t ↦ e^{-t} U(-t)φ is integrable on [0, ∞). -/
lemma integrable_exp_neg_unitary_neg (φ : H) :
    IntegrableOn (fun t => Real.exp (-t) • U_grp.U (-t) φ) (Set.Ici 0) volume := by
  apply integrable_exp_decay_continuous
    (fun t => U_grp.U (-t) φ)
    ((U_grp.strong_continuous φ).comp continuous_neg)
    ‖φ‖
  intro t _ht
  exact le_of_eq (norm_preserving U_grp (-t) φ)

/-- Bound on the integral of e^{-t} U(t)φ. -/
lemma norm_integral_exp_neg_unitary_le (φ : H) :
    ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ ≤ ‖φ‖ := by
  apply norm_integral_exp_decay_le
    (fun t => U_grp.U t φ)
    (U_grp.strong_continuous φ)
    ‖φ‖
  · intro t _ht
    exact le_of_eq (norm_preserving U_grp t φ)
  · exact norm_nonneg φ

/-- The averaged vector ∫₀ʰ U(t)φ dt exists for any h > 0. -/
lemma integrable_unitary_Ioc (φ : H) (h : ℝ) (_ : 0 < h) :
    IntegrableOn (fun t => U_grp.U t φ) (Set.Ioc 0 h) volume := by
  exact (U_grp.strong_continuous φ).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

end UnitaryGroupIntegration

/-!
================================================================================
SECTION 3: THE RESOLVENT INTEGRALS
================================================================================

Define the integral formulas that solve (A ± iI)ψ = φ.
-/


section ResolventIntegrals

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The integral ψ₊ = i ∫₀^∞ e^{-t} U(t)φ dt, which will solve (A + iI)ψ₊ = φ. -/
noncomputable def resolventIntegralPlus (φ : H) : H :=
  (-I) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ

/-- The integral ψ₋ = -i ∫₀^∞ e^{-t} U(-t)φ dt, which will solve (A - iI)ψ₋ = φ. -/
noncomputable def resolventIntegralMinus (φ : H) : H :=
  I • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ

/-- The resolvent integral ψ₊ is linear in φ. -/
lemma resolventIntegralPlus_add (φ₁ φ₂ : H) :
    resolventIntegralPlus U_grp (φ₁ + φ₂) =
    resolventIntegralPlus U_grp φ₁ + resolventIntegralPlus U_grp φ₂ := by
  unfold resolventIntegralPlus
  have h_int₁ := integrable_exp_neg_unitary U_grp φ₁
  have h_int₂ := integrable_exp_neg_unitary U_grp φ₂
  have h_eq : (fun t => Real.exp (-t) • U_grp.U t (φ₁ + φ₂)) =
              (fun t => Real.exp (-t) • U_grp.U t φ₁ + Real.exp (-t) • U_grp.U t φ₂) := by
    ext t
    rw [map_add, smul_add]
  rw [h_eq, integral_add h_int₁ h_int₂, DistribMulAction.smul_add]


/-- The resolvent integral ψ₊ is bounded: ‖ψ₊‖ ≤ ‖φ‖. -/
lemma norm_resolventIntegralPlus_le (φ : H) :
    ‖resolventIntegralPlus U_grp φ‖ ≤ ‖φ‖ := by
  unfold resolventIntegralPlus
  calc ‖(-I) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖
      = ‖-I‖ * ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ := norm_smul (-I) _
    _ = 1 * ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ := by simp only [norm_neg, norm_I]
    _ = ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ := one_mul _
    _ ≤ ‖φ‖ := norm_integral_exp_neg_unitary_le U_grp φ


/-- The resolvent integral ψ₋ is bounded: ‖ψ₋‖ ≤ ‖φ‖. -/
lemma norm_resolventIntegralMinus_le (φ : H) :
    ‖resolventIntegralMinus U_grp φ‖ ≤ ‖φ‖ := by
  unfold resolventIntegralMinus
  have h_bound : ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖ ≤ ‖φ‖ := by
    apply norm_integral_exp_decay_le
      (fun t => U_grp.U (-t) φ)
      ((U_grp.strong_continuous φ).comp continuous_neg)
      ‖φ‖
    · intro t _ht
      exact le_of_eq (norm_preserving U_grp (-t) φ)
    · exact norm_nonneg φ
  calc ‖I • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖
      = ‖I‖ * ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖ := norm_smul I _
    _ = 1 * ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖ := by simp only [norm_I, one_mul]
    _ = ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖ := one_mul _
    _ ≤ ‖φ‖ := h_bound

end ResolventIntegrals

/-!
================================================================================
SECTION 4: THE GENERATOR LIMIT FOR RESOLVENT INTEGRALS
================================================================================

Show that ψ₊ and ψ₋ are in the domain of the generator, i.e., the limit
defining Aψ exists.
-/

section GeneratorLimit

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- Key computation: (U(h) - I)ψ₊ in terms of integrals.

For ψ₊ = i ∫₀^∞ e^{-t} U(t)φ dt, we have:
  U(h)ψ₊ - ψ₊ = i ∫₀^∞ e^{-t} (U(t+h) - U(t))φ dt
              = i ∫₀^∞ e^{-t} U(t+h)φ dt - i ∫₀^∞ e^{-t} U(t)φ dt

Using substitution s = t + h in the first integral:
  = i ∫ₕ^∞ e^{-(s-h)} U(s)φ ds - i ∫₀^∞ e^{-t} U(t)φ dt
  = i·e^h ∫ₕ^∞ e^{-s} U(s)φ ds - i ∫₀^∞ e^{-t} U(t)φ dt

Splitting the second integral:
  = i·e^h ∫ₕ^∞ e^{-s} U(s)φ ds - i ∫₀^h e^{-t} U(t)φ dt - i ∫ₕ^∞ e^{-t} U(t)φ dt
  = i(e^h - 1) ∫ₕ^∞ e^{-s} U(s)φ ds - i ∫₀^h e^{-t} U(t)φ dt
-/
lemma unitary_shift_resolventIntegralPlus (φ : H) (h : ℝ) (hh : h > 0) :
    U_grp.U h (resolventIntegralPlus U_grp φ) - resolventIntegralPlus U_grp φ =
    (-I) • ((Real.exp h - 1) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) -
    (-I) • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ := by
  unfold resolventIntegralPlus
  -- U(h)(I • x) = I • U(h)(x)
  rw [ContinuousLinearMap.map_smul]

  have h_int := integrable_exp_neg_unitary U_grp φ
  -- Push U(h) inside the integral
  have h_comm : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) =
              ∫ t in Set.Ici 0, U_grp.U h (Real.exp (-t) • U_grp.U t φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  rw [h_comm]

  -- U(h)(e^{-t} • U(t)φ) = e^{-t} • U(h)(U(t)φ) = e^{-t} • U(t+h)φ
  have h_shift : ∀ t, U_grp.U h (Real.exp (-t) • U_grp.U t φ) =
                      Real.exp (-t) • U_grp.U (t + h) φ := by
    intro t
    have := U_grp.group_law h t
    rw [add_comm] at this
    rw [this]
    exact ContinuousLinearMap.map_smul_of_tower (U_grp.U h) (Real.exp (-t)) ((U_grp.U t) φ)
  simp_rw [h_shift]

  -- Rewrite e^{-t} • U(t+h)φ = e^h • (e^{-(t+h)} • U(t+h)φ)
  have h_exp : ∀ t, Real.exp (-t) • U_grp.U (t + h) φ =
                  Real.exp h • (Real.exp (-(t + h)) • U_grp.U (t + h) φ) := by
    intro t
    rw [← smul_assoc]
    congr 1
    rw [smul_eq_mul, ← Real.exp_add]
    congr 1
    ring
  simp_rw [h_exp]

  -- Pull out e^h
  rw [integral_smul]

  -- Substitution: ∫₀^∞ e^{-(t+h)} U(t+h)φ dt = ∫ₕ^∞ e^{-s} U(s)φ ds
  have h_subst : ∫ t in Set.Ici 0, Real.exp (-(t + h)) • U_grp.U (t + h) φ =
               ∫ s in Set.Ici h, Real.exp (-s) • U_grp.U s φ := by
    have h_preimage : (· + h) ⁻¹' (Set.Ici h) = Set.Ici 0 := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ici]
      constructor
      · intro ht; linarith
      · intro ht; linarith
    have h_map : Measure.map (· + h) volume = (volume : Measure ℝ) :=
      (measurePreserving_add_right volume h).map_eq
    have h_meas_set : MeasurableSet (Set.Ici h) := measurableSet_Ici
    have h_f_meas : AEStronglyMeasurable (fun s => Real.exp (-s) • U_grp.U s φ)
                      (Measure.map (· + h) volume) := by
      rw [h_map]
      exact ((Real.continuous_exp.comp continuous_neg).smul
         (U_grp.strong_continuous φ)).aestronglyMeasurable
    have h_g_meas : AEMeasurable (· + h) volume := measurable_add_const h |>.aemeasurable
    rw [← h_map, MeasureTheory.setIntegral_map h_meas_set h_f_meas h_g_meas, h_preimage]
    congr 1
    ext t
    exact congrFun (congrArg DFunLike.coe (congrFun (congrArg restrict h_map) (Set.Ici 0))) t

  rw [h_subst]

  -- Split [0,∞) = (0,h] ∪ [h,∞)
  have h_split : ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ =
               (∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ) +
               (∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) := by
    rw [integral_Ici_eq_integral_Ioi]
    have h_union : Set.Ioi (0 : ℝ) = Set.Ioc 0 h ∪ Set.Ioi h := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro hx
        by_cases hxh : x ≤ h
        · left; exact ⟨hx, hxh⟩
        · right; exact lt_of_not_ge hxh
      · intro hx
        cases hx with
        | inl hx => exact hx.1
        | inr hx => exact lt_trans hh hx
    rw [h_union, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (h_int.mono_set (Set.Ioc_subset_Icc_self.trans Set.Icc_subset_Ici_self))
      (h_int.mono_set (Set.Ioi_subset_Ici hh.le))]
    congr 1
    exact Eq.symm integral_Ici_eq_integral_Ioi
  rw [h_split]

  -- Algebra: I • (e^h • X) - I • (Y + X) = I • ((e^h - 1) • X) - I • Y
  -- where X = ∫ on Ici h, Y = ∫ on Ioc 0 h
  set X := ∫ s in Set.Ici h, Real.exp (-s) • U_grp.U s φ with hX_def
  set Y := ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ with hY_def
  rw [smul_add]
  calc -I • Real.exp h • X - (-I • Y + -I • X)
      = -I • Real.exp h • X - -I • X - -I • Y := by abel
    _ = -I • (Real.exp h • X - X) - -I • Y := by rw [← smul_sub]
    _ = -I • ((Real.exp h - 1) • X) - -I • Y := by rw [sub_smul, one_smul]
    _ = -I • (Real.exp h - 1) • X - -I • Y := by rw [← h_subst]





/-- The limit (U(h)ψ₊ - ψ₊)/(ih) as h → 0 exists and equals -ψ₊ + φ.

This is the key calculation showing ψ₊ ∈ D(A) with Aψ₊ = -ψ₊ + φ,
i.e., (A + iI)ψ₊ = Aψ₊ + iψ₊ = (-ψ₊ + φ) + iψ₊ = φ + i(ψ₊ - ψ₊) = φ.

Wait, that's not quite right. Let me recalculate...

Actually: Aψ₊ + iψ₊ = φ means Aψ₊ = φ - iψ₊.
The generator formula gives: Aψ = lim_{h→0} (U(h)ψ - ψ)/(ih)

So we need: lim_{h→0} (U(h)ψ₊ - ψ₊)/(ih) = φ - iψ₊

Hmm, let's be more careful. Define A via (U(h)ψ - ψ)/(ih) → Aψ.
Then (A + iI)ψ = Aψ + iψ.

For ψ₊, we need to show this limit exists and (A + iI)ψ₊ = φ.
-/
/- Helper 1 -/
lemma tendsto_exp_sub_one_div :
    Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[≠] 0) (𝓝 1) := by
  have h : HasDerivAt Real.exp 1 0 := by
    convert Real.hasDerivAt_exp 0 using 1
    exact Real.exp_zero.symm
  rw [hasDerivAt_iff_tendsto_slope] at h
  convert h using 1
  ext y
  simp only [slope, Real.exp_zero, sub_zero, vsub_eq_sub, smul_eq_mul]
  exact div_eq_inv_mul (Real.exp y - 1) y

/- Helper 2 -/
lemma tendsto_integral_Ici_exp_unitary (φ : H) :
    Tendsto (fun h : ℝ => ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ)
            (𝓝 0)
            (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) := by
  have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U t φ) :=
    (Real.continuous_exp.comp continuous_neg).smul (U_grp.strong_continuous φ)
  have h_int := integrable_exp_neg_unitary U_grp φ

  have h_prim_cont : Continuous (fun h => ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ) :=
    intervalIntegral.continuous_primitive (fun a b => h_cont.intervalIntegrable a b) 0

  have h_prim_zero : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U t φ = 0 :=
    intervalIntegral.integral_same

  have h_prim_tendsto : Tendsto (fun h => ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
                                (𝓝 0) (𝓝 0) := by
    rw [← h_prim_zero]
    exact h_prim_cont.tendsto 0

  convert tendsto_const_nhds.sub h_prim_tendsto using 1
  · ext h
    by_cases hh : h ≥ 0
    · -- Case h ≥ 0: Ici 0 =ᵐ Ioc 0 h ∪ Ici h
      have h_ae_eq : ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ =
                     ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U t φ :=
        setIntegral_congr_set Ioi_ae_eq_Ici.symm
      have h_union : Set.Ioi (0 : ℝ) = Set.Ioc 0 h ∪ Set.Ioi h := by
        ext x
        simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
        constructor
        · intro hx
          by_cases hxh : x ≤ h
          · left; exact ⟨hx, hxh⟩
          · right; exact lt_of_not_ge hxh
        · intro hx
          cases hx with
          | inl hx => exact hx.1
          | inr hx => linarith [hh, hx]
      have h_disj : Disjoint (Set.Ioc 0 h) (Set.Ioi h) := Set.Ioc_disjoint_Ioi le_rfl
      have h_ae_eq2 : ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ =
                      ∫ t in Set.Ioi h, Real.exp (-t) • U_grp.U t φ :=
        setIntegral_congr_set Ioi_ae_eq_Ici.symm
      have h_eq1 : ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U t φ =
                   (∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ) +
                   ∫ t in Set.Ioi h, Real.exp (-t) • U_grp.U t φ := by
        rw [h_union, setIntegral_union h_disj measurableSet_Ioi
            (h_int.mono_set (Set.Ioc_subset_Icc_self.trans Set.Icc_subset_Ici_self))
            (h_int.mono_set (Set.Ioi_subset_Ici hh))]
      have h_eq2 : ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ =
                   ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ := by
        rw [intervalIntegral.integral_of_le hh]
      -- ∫ Ioi h = ∫ Ioi 0 - ∫ Ioc 0 h
      have h_eq3 : ∫ t in Set.Ioi h, Real.exp (-t) • U_grp.U t φ =
                   (∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U t φ) -
                   ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ := by
        exact Eq.symm (sub_eq_of_eq_add' h_eq1)
      rw [h_ae_eq2, h_eq3, h_ae_eq.symm, h_eq2]
    · -- Case h < 0: Ici h = Ico h 0 ∪ Ici 0
      push_neg at hh
      have h_union : Set.Ici h = Set.Ico h 0 ∪ Set.Ici 0 := by
        ext x
        simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ico]
        constructor
        · intro hx
          by_cases hx0 : x < 0
          · left; exact ⟨hx, hx0⟩
          · right; linarith
        · intro hx
          cases hx with
          | inl hx => exact hx.1
          | inr hx => linarith [hh, hx]
      have h_disj : Disjoint (Set.Ico h 0) (Set.Ici 0) := by
        rw [Set.disjoint_iff]
        intro x ⟨hx1, hx2⟩
        simp only [Set.mem_Ico] at hx1
        simp only [Set.mem_Ici] at hx2
        linarith [hx1.2, hx2]
      have h_eq1 : ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ =
                   (∫ t in Set.Ico h 0, Real.exp (-t) • U_grp.U t φ) +
                   ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ := by
        rw [h_union, setIntegral_union h_disj measurableSet_Ici
            (h_cont.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)
            h_int]
      have h_eq2 : ∫ t in Set.Ico h 0, Real.exp (-t) • U_grp.U t φ =
                   -(∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ) := by
        rw [← intervalIntegral.integral_symm]
        rw [intervalIntegral.integral_of_le (le_of_lt hh)]
        rw [@restrict_Ico_eq_restrict_Ioc]
      rw [h_eq1, h_eq2]
      ring_nf
      exact
        neg_add_eq_sub (∫ (t : ℝ) in 0..h, Real.exp (-t) • (U_grp.U t) φ)
          (∫ (t : ℝ) in Set.Ici 0, Real.exp (-t) • (U_grp.U t) φ)
  · simp only [sub_zero]

/- Helper 3 -/
lemma tendsto_average_integral_unitary (φ : H) :
    Tendsto (fun h : ℝ => (h⁻¹ : ℂ) • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ)
            (𝓝[>] 0)
            (𝓝 φ) := by
  have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U t φ) :=
    (Real.continuous_exp.comp continuous_neg).smul (U_grp.strong_continuous φ)

  have h_f0 : Real.exp (-(0 : ℝ)) • U_grp.U 0 φ = φ := by
    simp only [neg_zero, Real.exp_zero, one_smul]
    rw [U_grp.identity]
    simp only [ContinuousLinearMap.id_apply]

  -- Convert to interval integral
  have h_eq : ∀ h > 0, ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ =
                       ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ := by
    intro h hh
    rw [intervalIntegral.integral_of_le (le_of_lt hh)]

  -- The primitive F(h) = ∫₀ʰ f has F'(0) = f(0)
  have h_deriv : HasDerivAt (fun h => ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
                            (Real.exp (-(0 : ℝ)) • U_grp.U 0 φ) 0 := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact h_cont.intervalIntegrable 0 0
    · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
    · exact h_cont.continuousAt

  rw [h_f0] at h_deriv

  -- F(0) = 0
  have h_F0 : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U t φ = 0 :=
    intervalIntegral.integral_same

  -- HasDerivAt gives: (F(h) - F(0))/h → F'(0), i.e., F(h)/h → φ
  have h_tendsto_real : Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
                                (𝓝[≠] 0) (𝓝 φ) := by
    have := h_deriv.hasDerivWithinAt (s := Set.univ \ {0})
    rw [hasDerivWithinAt_iff_tendsto_slope] at this
    simp only [Set.diff_diff, Set.union_self] at this
    convert this using 1
    ext h
    unfold slope
    simp only [sub_zero, h_F0, vsub_eq_sub]
    · congr 1
      exact Set.compl_eq_univ_diff {(0 : ℝ)}


  -- Restrict to 𝓝[>] 0
  have h_restrict := h_tendsto_real.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))

  -- Convert ℝ scalar to ℂ scalar
  apply Tendsto.congr' _ h_restrict
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [h_eq h hh, ← ofReal_inv, @Complex.coe_smul]

/- Helper 4 -/
lemma unitary_shift_resolventIntegralPlus_neg (φ : H) (h : ℝ) (hh : h < 0) :
    U_grp.U h (resolventIntegralPlus U_grp φ) - resolventIntegralPlus U_grp φ =
    (-I) • (Real.exp h • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ) +
    (-I) • ((Real.exp h - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) := by
  unfold resolventIntegralPlus
  have h_int := integrable_exp_neg_unitary U_grp φ

  -- U(h) commutes with (-I) • and the integral
  rw [ContinuousLinearMap.map_smul]
  have h_comm : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) =
                ∫ t in Set.Ici 0, U_grp.U h (Real.exp (-t) • U_grp.U t φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  rw [h_comm]

  -- U(h)(e^{-t} • U(t)φ) = e^{-t} • U(t+h)φ
  have h_shift : ∀ t, U_grp.U h (Real.exp (-t) • U_grp.U t φ) =
                      Real.exp (-t) • U_grp.U (t + h) φ := by
    intro t
    rw [ContinuousLinearMap.map_smul_of_tower]
    congr 1
    have := U_grp.group_law h t
    rw [add_comm] at this
    exact congrFun (congrArg DFunLike.coe this).symm φ
  simp_rw [h_shift]

  -- Rewrite e^{-t} • U(t+h)φ = e^h • (e^{-(t+h)} • U(t+h)φ)
  have h_exp : ∀ t, Real.exp (-t) • U_grp.U (t + h) φ =
                    Real.exp h • (Real.exp (-(t + h)) • U_grp.U (t + h) φ) := by
    intro t
    rw [← smul_assoc, smul_eq_mul, ← Real.exp_add]
    congr 1
    ring_nf
  simp_rw [h_exp]

-- Pull out e^h
  have h_smul_comm : ∫ t in Set.Ici 0, Real.exp h • (Real.exp (-(t + h)) • U_grp.U (t + h) φ) =
                     Real.exp h • ∫ t in Set.Ici 0, Real.exp (-(t + h)) • U_grp.U (t + h) φ := by
    rw [@integral_smul]
  rw [h_smul_comm]

  -- Substitution: ∫₀^∞ e^{-(t+h)} U(t+h)φ dt = ∫ₕ^∞ e^{-s} U(s)φ ds
  have h_subst : ∫ t in Set.Ici 0, Real.exp (-(t + h)) • U_grp.U (t + h) φ =
                 ∫ s in Set.Ici h, Real.exp (-s) • U_grp.U s φ := by
    have h_preimage : (· + h) ⁻¹' (Set.Ici h) = Set.Ici 0 := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ici]
      constructor
      · intro ht; linarith
      · intro ht; linarith
    have h_map : Measure.map (· + h) volume = (volume : Measure ℝ) :=
      (measurePreserving_add_right volume h).map_eq
    have h_meas_set : MeasurableSet (Set.Ici h) := measurableSet_Ici
    have h_f_meas : AEStronglyMeasurable (fun s => Real.exp (-s) • U_grp.U s φ)
                      (Measure.map (· + h) volume) := by
      rw [h_map]
      exact ((Real.continuous_exp.comp continuous_neg).smul
             (U_grp.strong_continuous φ)).aestronglyMeasurable
    have h_g_meas : AEMeasurable (· + h) volume := measurable_add_const h |>.aemeasurable
    rw [← h_map, MeasureTheory.setIntegral_map h_meas_set h_f_meas h_g_meas, h_preimage]
    congr 1
    ext t
    exact congrFun (congrArg DFunLike.coe (congrFun (congrArg restrict h_map) (Set.Ici 0))) t
  rw [h_subst]

  -- Define X and Y
  set X := ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ with hX_def
  set Y := ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ with hY_def

  -- Split [h, ∞) = (h, 0] ∪ [0, ∞) for h < 0
  have h_split : ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ = X + Y := by
    have h_ae_eq1 : ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ =
                    ∫ t in Set.Ioi h, Real.exp (-t) • U_grp.U t φ :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_ae_eq2 : Y = ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U t φ :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_union : Set.Ioi h = Set.Ioc h 0 ∪ Set.Ioi 0 := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro hx
        by_cases hx0 : x ≤ 0
        · left; exact ⟨hx, hx0⟩
        · right; linarith
      · intro hx
        cases hx with
        | inl hx => exact hx.1
        | inr hx => linarith [hh, hx]
    have h_disj : Disjoint (Set.Ioc h 0) (Set.Ioi 0) := Set.Ioc_disjoint_Ioi le_rfl
    have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U t φ) :=
      (Real.continuous_exp.comp continuous_neg).smul (U_grp.strong_continuous φ)
    rw [h_ae_eq1, h_union, setIntegral_union h_disj measurableSet_Ioi
        (h_cont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (h_int.mono_set Set.Ioi_subset_Ici_self), h_ae_eq2.symm]

  rw [h_split, smul_add]

  -- Algebra
  calc -I • (Real.exp h • X + Real.exp h • Y) - -I • Y
      = -I • Real.exp h • X + -I • Real.exp h • Y - -I • Y := by rw [smul_add]
    _ = -I • Real.exp h • X + (-I • Real.exp h • Y - -I • Y) := by abel
    _ = -I • Real.exp h • X + -I • (Real.exp h • Y - Y) := by rw [← smul_sub]
    _ = -I • Real.exp h • X + -I • ((Real.exp h - 1) • Y) := by rw [sub_smul, one_smul]
    _ = -I • (Real.exp h • X) + -I • ((Real.exp h - 1) • Y) := by rw [hX_def]

/- Helper 5 -/
lemma tendsto_average_integral_unitary_neg (φ : H) :
    Tendsto (fun h : ℝ => ((-h)⁻¹ : ℂ) • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ)
            (𝓝[<] 0)
            (𝓝 φ) := by
  have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U t φ) :=
    (Real.continuous_exp.comp continuous_neg).smul (U_grp.strong_continuous φ)
  have h_f0 : Real.exp (-(0 : ℝ)) • U_grp.U 0 φ = φ := by
    simp only [neg_zero, Real.exp_zero, one_smul]
    rw [U_grp.identity]
    simp only [ContinuousLinearMap.id_apply]
  -- Convert to interval integral
  have h_eq : ∀ h < 0, ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ =
                       ∫ t in h..0, Real.exp (-t) • U_grp.U t φ := by
    intro h hh
    rw [intervalIntegral.integral_of_le (le_of_lt hh)]
  -- ∫_h^0 = -∫_0^h, and -h > 0 for h < 0
  have h_eq' : ∀ h < 0, ∫ t in h..0, Real.exp (-t) • U_grp.U t φ =
                        -∫ t in 0..h, Real.exp (-t) • U_grp.U t φ := by
    intro h _
    rw [intervalIntegral.integral_symm]
  -- The primitive F(h) = ∫₀ʰ f has F'(0) = f(0)
  have h_deriv : HasDerivAt (fun h => ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
                            (Real.exp (-(0 : ℝ)) • U_grp.U 0 φ) 0 := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact h_cont.intervalIntegrable 0 0
    · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
    · exact h_cont.continuousAt
  rw [h_f0] at h_deriv
  have h_F0 : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U t φ = 0 :=
    intervalIntegral.integral_same
  have h_tendsto_real : Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
                                (𝓝[≠] 0) (𝓝 φ) := by
    have := h_deriv.hasDerivWithinAt (s := Set.univ \ {0})
    rw [hasDerivWithinAt_iff_tendsto_slope] at this
    simp only [Set.diff_diff, Set.union_self] at this
    convert this using 1
    · ext h
      unfold slope
      simp only [sub_zero, h_F0, vsub_eq_sub]
    · congr 1
      exact Set.compl_eq_univ_diff {(0 : ℝ)}
  have h_restrict := h_tendsto_real.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))
  -- For h < 0: (-h)⁻¹ • ∫_{(h,0]} = (-h)⁻¹ • (-∫_0^h) = h⁻¹ • ∫_0^h
  apply Tendsto.congr' _ h_restrict
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [h_eq h hh, h_eq' h hh]
  rw [smul_neg]
  -- Goal: h⁻¹ • ∫_0^h = -((-↑h)⁻¹ • ∫_0^h)
  rw [← neg_smul]
  -- Goal: h⁻¹ • ∫_0^h = -(-↑h)⁻¹ • ∫_0^h
  -- Convert real smul to complex smul on LHS
  rw [(Complex.coe_smul h⁻¹ _).symm, ofReal_inv]
  congr 1
  rw [@neg_inv]
  simp_all only [neg_zero, Real.exp_zero, one_smul, intervalIntegral.integral_same, neg_neg]



lemma generator_limit_resolventIntegralPlus (φ : H) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
                                              resolventIntegralPlus U_grp φ))
            (𝓝[≠] 0)
            (𝓝 (φ - I • resolventIntegralPlus U_grp φ)) := by
  -- Simplify target: φ - I • (I • ∫) = φ + ∫
  have h_target : φ - I • resolventIntegralPlus U_grp φ =
                  φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ := by
    unfold resolventIntegralPlus
    rw [smul_smul, mul_neg, I_mul_I, neg_neg, one_smul]

  rw [h_target]

  -- Key scalar identity: (I * h)⁻¹ * I = h⁻¹
  have h_scalar : ∀ h : ℝ, h ≠ 0 → ((I * (h : ℂ))⁻¹ * (-I) : ℂ) = -(h : ℂ)⁻¹ := by
    intro h _
    calc ((I * (h : ℂ))⁻¹ * (-I) : ℂ)
        = (h : ℂ)⁻¹ * I⁻¹ * (-I) := by rw [mul_inv_rev]
      _ = (h : ℂ)⁻¹ * (I⁻¹ * (-I)) := by rw [mul_assoc]
      _ = (h : ℂ)⁻¹ * (-(I⁻¹ * I)) := by rw [mul_neg]
      _ = (h : ℂ)⁻¹ * (-1) := by rw [inv_mul_cancel₀ I_ne_zero]
      _ = -(h : ℂ)⁻¹ := by rw [mul_neg_one]


  -- It suffices to prove on 𝓝[>] 0 (use symmetry for 𝓝[<] 0)
  have h_compl : ({0} : Set ℝ)ᶜ = Set.Ioi 0 ∪ Set.Iio 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · intro hx
      by_cases h : x > 0
      · left; exact h
      · right; push_neg at h; exact lt_of_le_of_ne h hx
    · intro hx
      cases hx with
      | inl h => linarith
      | inr h => linarith
  rw [show (𝓝[≠] (0 : ℝ)) = 𝓝[Set.Ioi 0 ∪ Set.Iio 0] 0 from by rw [← h_compl]]
  rw [nhdsWithin_union]
  apply Tendsto.sup

  · -- Case h > 0: use unitary_shift_resolventIntegralPlus
    have h_eq : ∀ h : ℝ, h > 0 → ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
                                                   resolventIntegralPlus U_grp φ) =
                         (-(h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) -
                         (-(h : ℂ)⁻¹ • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ) := by
      intro h hh
      rw [unitary_shift_resolventIntegralPlus U_grp φ h hh]
      rw [smul_sub, smul_smul, smul_smul, h_scalar h (ne_of_gt hh)]

    -- Rewrite as: -h⁻¹(e^h-1)∫_{≥h} + h⁻¹∫_{(0,h]}
    have h_eq' : ∀ h : ℝ, h > 0 → ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
                                                   resolventIntegralPlus U_grp φ) =
                         -((h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) +
                         ((h : ℂ)⁻¹ • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ) := by
      intro h hh
      rw [h_eq h hh]
      rw [neg_smul, neg_smul, sub_neg_eq_add]

    apply Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact (h_eq' h hh).symm

    -- Target: φ - ∫ = -∫ + φ
    rw [show φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ =
            -(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) + φ by abel]

    apply Tendsto.add

    · -- First term: -h⁻¹(e^h-1)∫_{≥h} → -∫
      apply Tendsto.neg
      have he : Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[>] 0) (𝓝 1) :=
        tendsto_exp_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
      have hi : Tendsto (fun h : ℝ => ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ)
                        (𝓝[>] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) :=
        (tendsto_integral_Ici_exp_unitary U_grp φ).mono_left nhdsWithin_le_nhds
      -- h⁻¹(e^h-1) → 1 and ∫_{≥h} → ∫_{≥0}
      have he_cplx : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ)) (𝓝[>] 0) (𝓝 1) := by
        convert Tendsto.comp (continuous_ofReal.tendsto 1) he using 1
        ext h
        simp only [Function.comp_apply, ofReal_div, ofReal_sub, ofReal_one]
      have h_prod : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ)
                            (𝓝[>] 0) (𝓝 ((1 : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) :=
        Tendsto.smul he_cplx hi
      simp only [one_smul] at h_prod
      -- Convert (e^h-1)/h to h⁻¹(e^h-1)
      apply Tendsto.congr' _ h_prod
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [div_eq_inv_mul]
      conv_lhs =>
        rw [show (↑(Real.exp h) : ℂ) - 1 = ↑(Real.exp h - 1) from by rw [ofReal_sub, ofReal_one]]
        rw [← smul_smul]
      exact rfl

    · -- Second term: h⁻¹∫_{(0,h]} → φ
      exact tendsto_average_integral_unitary U_grp φ
  · -- Case h < 0: use unitary_shift_resolventIntegralPlus_neg
    have h_eq : ∀ h : ℝ, h < 0 → ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
                                                   resolventIntegralPlus U_grp φ) =
                         (-(h : ℂ)⁻¹ • Real.exp h • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ) +
                         (-(h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) := by
      intro h hh
      rw [unitary_shift_resolventIntegralPlus_neg U_grp φ h hh]
      rw [smul_add, smul_smul, smul_smul, h_scalar h (ne_of_lt hh)]

    -- Rewrite as: -h⁻¹ e^h ∫_{(h,0]} + -h⁻¹(e^h-1)∫_{≥0}
    -- As h → 0⁻: first term → φ, second term → -∫
    -- Total: φ - ∫ ✓

    apply Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact (h_eq h hh).symm

    -- Target: φ - ∫ = φ + (-∫)
    rw [show φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ =
            φ + (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) by abel]

    apply Tendsto.add

    · -- First term: -h⁻¹ e^h ∫_{(h,0]} → φ
      -- Note: for h < 0, ∫_{(h,0]} is over an interval going from h to 0
      -- and -h⁻¹ = |h|⁻¹, so this is like averaging over [h,0]
      have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U t φ) :=
        (Real.continuous_exp.comp continuous_neg).smul (U_grp.strong_continuous φ)
      have h_f0 : Real.exp (-(0 : ℝ)) • U_grp.U 0 φ = φ := by
        simp only [neg_zero, Real.exp_zero, one_smul]
        rw [U_grp.identity]
        simp only [ContinuousLinearMap.id_apply]

      -- ∫_{(h,0]} = ∫_{h..0} for h < 0
      have h_eq_int : ∀ h < 0, ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ =
                               ∫ t in h..0, Real.exp (-t) • U_grp.U t φ := by
        intro h hh
        rw [intervalIntegral.integral_of_le (le_of_lt hh)]

      -- -h⁻¹ • e^h • ∫_{h..0} → 1 • φ = φ as h → 0⁻
      -- Note: -h⁻¹ = (-h)⁻¹ for h < 0, and -h > 0
      -- Also e^h → 1
      have he : Tendsto (fun h : ℝ => Real.exp h) (𝓝[<] 0) (𝓝 1) := by
        rw [← Real.exp_zero]
        exact Real.continuous_exp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

      -- Key: (-h)⁻¹ • ∫_{h..0} = (-h)⁻¹ • ∫_{0..(-h)} ∘ (- ·) ... this is getting complicated
      -- Simpler approach: use that -h⁻¹ ∫_h^0 = h⁻¹ ∫_0^h via sign flip
      have h_flip : ∀ h : ℝ, h < 0 → -(h : ℂ)⁻¹ • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ =
                             ((-h) : ℂ)⁻¹ • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ := by
        intro h hh
        congr 1
        exact neg_inv

      -- First term: -h⁻¹ e^h ∫_{(h,0]} → φ
      have he : Tendsto (fun h : ℝ => Real.exp h) (𝓝[<] 0) (𝓝 1) := by
        rw [← Real.exp_zero]
        exact Real.continuous_exp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h_avg := tendsto_average_integral_unitary_neg U_grp φ
      -- e^h • (avg) → 1 • φ = φ
      have h_comb : Tendsto (fun h : ℝ => Real.exp h • (((-h)⁻¹ : ℂ) • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ))
                            (𝓝[<] 0) (𝓝 ((1 : ℝ) • φ)) := by
        have he' : Tendsto (fun h : ℝ => Real.exp h) (𝓝[<] 0) (𝓝 (1 : ℝ)) := by
          rw [← Real.exp_zero]
          exact Real.continuous_exp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        exact Tendsto.smul he' h_avg
      simp only [one_smul] at h_comb
      apply Tendsto.congr' _ h_comb
      filter_upwards [self_mem_nhdsWithin] with h hh
      rw [h_eq_int h hh]
      rw [smul_comm, @inv_neg]

    · -- Second term: -h⁻¹(e^h-1)∫_{≥0} → -∫
      have he : Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[<] 0) (𝓝 1) :=
        tendsto_exp_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))
      have he_cplx : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ)) (𝓝[<] 0) (𝓝 1) := by
        convert Tendsto.comp (continuous_ofReal.tendsto 1) he using 1
        ext h
        simp only [Function.comp_apply, ofReal_div, ofReal_sub, ofReal_one]
      have h_prod : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)
                            (𝓝[<] 0) (𝓝 ((1 : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) :=
        Tendsto.smul he_cplx tendsto_const_nhds
      simp only [one_smul] at h_prod
      -- h⁻¹ • (e^h - 1) • ∫ = ((e^h - 1)/h) • ∫
      have h_inner : Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)
                             (𝓝[<] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) := by
        apply Tendsto.congr' _ h_prod
        filter_upwards [self_mem_nhdsWithin] with h hh
        simp only [div_eq_inv_mul]
        conv_lhs =>
          rw [show (↑(Real.exp h) : ℂ) - 1 = ↑(Real.exp h - 1) from by rw [ofReal_sub, ofReal_one]]
          rw [← smul_smul]
        rw [@Complex.coe_smul]
      -- -h⁻¹ • X = -(h⁻¹ • X), so use Tendsto.neg
      apply Tendsto.congr' _ h_inner.neg
      filter_upwards with h
      rw [neg_smul]

/- Helper 1 -/
lemma unitary_shift_resolventIntegralMinus (φ : H) (h : ℝ) (hh : h > 0) :
    U_grp.U h (resolventIntegralMinus U_grp φ) - resolventIntegralMinus U_grp φ =
    I • (Real.exp (-h) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) +
    I • ((Real.exp (-h) - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) := by
  unfold resolventIntegralMinus
  have h_int := integrable_exp_neg_unitary_neg U_grp φ

  -- U(h) commutes with I • and the integral
  rw [ContinuousLinearMap.map_smul]
  have h_comm : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) =
                ∫ t in Set.Ici 0, U_grp.U h (Real.exp (-t) • U_grp.U (-t) φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  rw [h_comm]

  -- U(h)(e^{-t} • U(-t)φ) = e^{-t} • U(h-t)φ
  have h_shift : ∀ t, U_grp.U h (Real.exp (-t) • U_grp.U (-t) φ) =
                      Real.exp (-t) • U_grp.U (h - t) φ := by
    intro t
    rw [ContinuousLinearMap.map_smul_of_tower]
    congr 1
    have := U_grp.group_law h (-t)
    simp only at this
    exact congrFun (congrArg DFunLike.coe this).symm φ
  simp_rw [h_shift]

  -- Rewrite e^{-t} • U(h-t)φ = e^{-h} • (e^{-(t-h)} • U(-(-(h-t)))φ)
  -- Note: h - t = -(t - h), so U(h-t) = U(-(t-h))
  have h_exp : ∀ t, Real.exp (-t) • U_grp.U (h - t) φ =
                    Real.exp (-h) • (Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ) := by
    intro t
    rw [← smul_assoc, smul_eq_mul, ← Real.exp_add]
    congr 1
    · ring_nf
    · ring_nf
  simp_rw [h_exp]

  -- Pull out e^{-h}
  have h_smul_comm : ∫ t in Set.Ici 0, Real.exp (-h) • (Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ) =
                     Real.exp (-h) • ∫ t in Set.Ici 0, Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ := by
    exact integral_smul (Real.exp (-h)) fun a => Real.exp (-(a - h)) • (U_grp.U (-(a - h))) φ
  rw [h_smul_comm]

  -- Substitution: ∫₀^∞ e^{-(t-h)} U(-(t-h))φ dt = ∫_{-h}^∞ e^{-s} U(-s)φ ds
  have h_subst : ∫ t in Set.Ici 0, Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ =
                 ∫ s in Set.Ici (-h), Real.exp (-s) • U_grp.U (-s) φ := by
    have h_preimage : (· - h) ⁻¹' (Set.Ici (-h)) = Set.Ici 0 := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ici]
      constructor
      · intro ht; linarith
      · intro ht; linarith
    have h_map : Measure.map (· - h) volume = (volume : Measure ℝ) :=
      (measurePreserving_sub_right volume h).map_eq
    have h_meas_set : MeasurableSet (Set.Ici (-h)) := measurableSet_Ici
    have h_cont : Continuous (fun s => Real.exp (-s) • U_grp.U (-s) φ) :=
      ((Real.continuous_exp.comp continuous_neg).smul
       ((U_grp.strong_continuous φ).comp continuous_neg))
    have h_f_meas : AEStronglyMeasurable (fun s => Real.exp (-s) • U_grp.U (-s) φ)
                      (Measure.map (· - h) volume) := by
      rw [h_map]
      exact h_cont.aestronglyMeasurable
    have h_g_meas : AEMeasurable (· - h) volume := (measurable_sub_const h).aemeasurable
    rw [← h_map, MeasureTheory.setIntegral_map h_meas_set h_f_meas h_g_meas, h_preimage]
    congr 1
    ext t
    exact congrFun (congrArg DFunLike.coe (congrFun (congrArg restrict h_map) (Set.Ici 0))) t
  rw [h_subst]

  -- Split [-h, ∞) = (-h, 0] ∪ [0, ∞) for h > 0
  have h_split : ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ =
                 (∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) +
                 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) := by
    have h_ae_eq1 : ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ =
                    ∫ t in Set.Ioi (-h), Real.exp (-t) • U_grp.U (-t) φ :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_ae_eq2 : ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ =
                    ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U (-t) φ :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_union : Set.Ioi (-h) = Set.Ioc (-h) 0 ∪ Set.Ioi 0 := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro hx
        by_cases hx0 : x ≤ 0
        · left; exact ⟨hx, hx0⟩
        · right; linarith
      · intro hx
        cases hx with
        | inl hx => exact hx.1
        | inr hx => linarith [hh, hx]
    have h_disj : Disjoint (Set.Ioc (-h) 0) (Set.Ioi 0) := Set.Ioc_disjoint_Ioi le_rfl
    have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U (-t) φ) :=
      ((Real.continuous_exp.comp continuous_neg).smul
       ((U_grp.strong_continuous φ).comp continuous_neg))
    rw [h_ae_eq1, h_union, setIntegral_union h_disj measurableSet_Ioi
        (h_cont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (h_int.mono_set Set.Ioi_subset_Ici_self), h_ae_eq2.symm]
  rw [h_split, smul_add]

  -- Algebra
  set X := ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ with hX_def
  set Y := ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ with hY_def

  calc I • (Real.exp (-h) • X + Real.exp (-h) • Y) - I • Y
      = I • Real.exp (-h) • X + I • Real.exp (-h) • Y - I • Y := by rw [smul_add]
    _ = I • Real.exp (-h) • X + (I • Real.exp (-h) • Y - I • Y) := by abel
    _ = I • Real.exp (-h) • X + I • (Real.exp (-h) • Y - Y) := by rw [← smul_sub]
    _ = I • Real.exp (-h) • X + I • ((Real.exp (-h) - 1) • Y) := by rw [sub_smul, one_smul]
    _ = I • (Real.exp (-h) • X) + I • ((Real.exp (-h) - 1) • Y) := by rw [hX_def]


/- Helper 2 -/
lemma unitary_shift_resolventIntegralMinus_neg (φ : H) (h : ℝ) (hh : h < 0) :
    U_grp.U h (resolventIntegralMinus U_grp φ) - resolventIntegralMinus U_grp φ =
    I • ((Real.exp (-h) - 1) • ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ) -
    I • ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ := by
  unfold resolventIntegralMinus
  have h_int := integrable_exp_neg_unitary_neg U_grp φ

  -- U(h) commutes with I • and the integral
  rw [ContinuousLinearMap.map_smul]
  have h_comm : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) =
                ∫ t in Set.Ici 0, U_grp.U h (Real.exp (-t) • U_grp.U (-t) φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  rw [h_comm]

  -- U(h)(e^{-t} • U(-t)φ) = e^{-t} • U(h-t)φ
  have h_shift : ∀ t, U_grp.U h (Real.exp (-t) • U_grp.U (-t) φ) =
                      Real.exp (-t) • U_grp.U (h - t) φ := by
    intro t
    rw [ContinuousLinearMap.map_smul_of_tower]
    congr 1
    have := U_grp.group_law h (-t)
    simp only at this
    exact congrFun (congrArg DFunLike.coe (id (Eq.symm this))) φ
  simp_rw [h_shift]

  -- Rewrite e^{-t} • U(h-t)φ = e^{-h} • (e^{-(t-h)} • U(-(-(h-t)))φ)
  have h_exp : ∀ t, Real.exp (-t) • U_grp.U (h - t) φ =
                    Real.exp (-h) • (Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ) := by
    intro t
    rw [← smul_assoc, smul_eq_mul, ← Real.exp_add]
    congr 1
    · ring_nf
    · ring_nf
  simp_rw [h_exp]

  -- Pull out e^{-h}
  have h_smul_comm : ∫ t in Set.Ici 0, Real.exp (-h) • (Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ) =
                     Real.exp (-h) • ∫ t in Set.Ici 0, Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ := by
    exact integral_smul (Real.exp (-h)) fun a => Real.exp (-(a - h)) • (U_grp.U (-(a - h))) φ
  rw [h_smul_comm]

  -- Substitution: ∫₀^∞ e^{-(t-h)} U(-(t-h))φ dt = ∫_{-h}^∞ e^{-s} U(-s)φ ds
  have h_subst : ∫ t in Set.Ici 0, Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ =
                 ∫ s in Set.Ici (-h), Real.exp (-s) • U_grp.U (-s) φ := by
    have h_preimage : (· - h) ⁻¹' (Set.Ici (-h)) = Set.Ici 0 := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ici]
      constructor
      · intro ht; linarith
      · intro ht; linarith
    have h_map : Measure.map (· - h) volume = (volume : Measure ℝ) :=
      (measurePreserving_sub_right volume h).map_eq
    have h_meas_set : MeasurableSet (Set.Ici (-h)) := measurableSet_Ici
    have h_cont : Continuous (fun s => Real.exp (-s) • U_grp.U (-s) φ) :=
      ((Real.continuous_exp.comp continuous_neg).smul
       ((U_grp.strong_continuous φ).comp continuous_neg))
    have h_f_meas : AEStronglyMeasurable (fun s => Real.exp (-s) • U_grp.U (-s) φ)
                      (Measure.map (· - h) volume) := by
      rw [h_map]
      exact h_cont.aestronglyMeasurable
    have h_g_meas : AEMeasurable (· - h) volume := (measurable_sub_const h).aemeasurable
    rw [← h_map, MeasureTheory.setIntegral_map h_meas_set h_f_meas h_g_meas, h_preimage]
    congr 1
    ext t
    exact congrFun (congrArg DFunLike.coe (congrFun (congrArg restrict h_map) (Set.Ici 0))) t
  rw [h_subst]

  -- Split [0, ∞) = (0, -h] ∪ [-h, ∞) for h < 0 (so -h > 0)
  have h_neg_pos : -h > 0 := neg_pos.mpr hh
  have h_split : ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ =
                 (∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ) +
                 (∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ) := by
    have h_ae_eq1 : ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ =
                    ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U (-t) φ :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_ae_eq2 : ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ =
                    ∫ t in Set.Ioi (-h), Real.exp (-t) • U_grp.U (-t) φ :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_union : Set.Ioi 0 = Set.Ioc 0 (-h) ∪ Set.Ioi (-h) := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro hx
        by_cases hxh : x ≤ -h
        · left; exact ⟨hx, hxh⟩
        · right; linarith
      · intro hx
        cases hx with
        | inl hx => exact hx.1
        | inr hx => linarith [h_neg_pos, hx]
    have h_disj : Disjoint (Set.Ioc 0 (-h)) (Set.Ioi (-h)) := Set.Ioc_disjoint_Ioi le_rfl
    have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U (-t) φ) :=
      ((Real.continuous_exp.comp continuous_neg).smul
       ((U_grp.strong_continuous φ).comp continuous_neg))
    rw [h_ae_eq1, h_union, setIntegral_union h_disj measurableSet_Ioi
        (h_cont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (h_int.mono_set (Set.Ioi_subset_Ici h_neg_pos.le)), h_ae_eq2.symm]
  rw [h_split]

  -- Algebra
  set X := ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ with hX_def
  set Y := ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ with hY_def
  rw [smul_add]

  calc  I • Real.exp (-h) • Y - (I • X + I • Y)
      = I • Real.exp (-h) • Y - I • X - I • Y := by exact sub_add_eq_sub_sub (I • Real.exp (-h) • Y) (I • X) (I • Y)
    _ = I • Real.exp (-h) • Y - I • Y - I • X := by abel
    _ = I • (Real.exp (-h) • Y - Y) - I • X := by rw [← smul_sub]
    _ = I • ((Real.exp (-h) - 1) • Y) - I • X := by rw [sub_smul, one_smul]
    _ = I • (Real.exp (-h) - 1) • Y - I • X := by exact rfl


/-- The limit for ψ₋ exists and gives (A - iI)ψ₋ = φ. -/
lemma generator_limit_resolventIntegralMinus (φ : H) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) -
                                              resolventIntegralMinus U_grp φ))
            (𝓝[≠] 0)
            (𝓝 (φ + I • resolventIntegralMinus U_grp φ)) := by
  -- Simplify target: φ + I • (I • ∫) = φ - ∫
  have h_target : φ + I • resolventIntegralMinus U_grp φ =
                  φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ := by
    unfold resolventIntegralMinus
    rw [smul_smul, I_mul_I, neg_one_smul, sub_eq_add_neg]
  rw [h_target]

  -- Key scalar identity: (I * h)⁻¹ * I = h⁻¹
  have h_scalar : ∀ h : ℝ, h ≠ 0 → ((I * (h : ℂ))⁻¹ * I : ℂ) = (h : ℂ)⁻¹ := by
    intro h _
    calc ((I * (h : ℂ))⁻¹ * I : ℂ)
        = (h : ℂ)⁻¹ * I⁻¹ * I := by rw [mul_inv_rev]
      _ = (h : ℂ)⁻¹ * (I⁻¹ * I) := by rw [mul_assoc]
      _ = (h : ℂ)⁻¹ * 1 := by rw [inv_mul_cancel₀ I_ne_zero]
      _ = (h : ℂ)⁻¹ := by rw [mul_one]

  -- Split into h > 0 and h < 0 cases
  have h_compl : ({0} : Set ℝ)ᶜ = Set.Ioi 0 ∪ Set.Iio 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · intro hx
      by_cases h : x > 0
      · left; exact h
      · right; push_neg at h; exact lt_of_le_of_ne h hx
    · intro hx
      cases hx with
      | inl h => linarith
      | inr h => linarith
  rw [show (𝓝[≠] (0 : ℝ)) = 𝓝[Set.Ioi 0 ∪ Set.Iio 0] 0 from by rw [← h_compl]]
  rw [nhdsWithin_union]
  apply Tendsto.sup

  · -- Case h > 0: use unitary_shift_resolventIntegralMinus
    have h_eq : ∀ h : ℝ, h > 0 → ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) -
                                                   resolventIntegralMinus U_grp φ) =
                         ((h : ℂ)⁻¹ • Real.exp (-h) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) +
                         ((h : ℂ)⁻¹ • (Real.exp (-h) - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) := by
      intro h hh
      rw [unitary_shift_resolventIntegralMinus U_grp φ h hh]
      rw [smul_add, smul_smul, smul_smul, h_scalar h (ne_of_gt hh)]

    apply Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact (h_eq h hh).symm

    -- Target: φ - ∫ = φ + (-∫)
    rw [show φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ =
            φ + (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) by abel]

    apply Tendsto.add

    · -- First term: h⁻¹ e^{-h} ∫_{(-h,0]} → φ
      have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U (-t) φ) :=
        ((Real.continuous_exp.comp continuous_neg).smul
         ((U_grp.strong_continuous φ).comp continuous_neg))
      have h_f0 : Real.exp (-(0 : ℝ)) • U_grp.U (-(0 : ℝ)) φ = φ := by
        simp only [neg_zero, Real.exp_zero, one_smul]
        rw [U_grp.identity]
        simp only [ContinuousLinearMap.id_apply]

      have he : Tendsto (fun h : ℝ => Real.exp (-h)) (𝓝[>] 0) (𝓝 1) := by
        have h1 : Tendsto (fun h : ℝ => -h) (𝓝 (0 : ℝ)) (𝓝 0) := by
          convert (continuous_neg (G := ℝ)).tendsto 0 using 1
          simp
        have h2 : Tendsto Real.exp (𝓝 0) (𝓝 1) := by
          rw [← Real.exp_zero]
          exact Real.continuous_exp.tendsto 0
        exact (h2.comp h1).mono_left nhdsWithin_le_nhds

      -- For h > 0, ∫_{(-h,0]} e^{-t} U(-t)φ dt, averaged by h⁻¹, → φ
      have h_avg : Tendsto (fun h : ℝ => (h⁻¹ : ℂ) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ)
                           (𝓝[>] 0) (𝓝 φ) := by
        have h_eq_int : ∀ h > 0, ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ =
                                 ∫ t in (-h)..0, Real.exp (-t) • U_grp.U (-t) φ := by
          intro h hh
          rw [intervalIntegral.integral_of_le (by linarith : -h ≤ 0)]
        have h_deriv : HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, Real.exp (-t) • U_grp.U (-t) φ)
                                  (Real.exp (-(0 : ℝ)) • U_grp.U (-(0 : ℝ)) φ) 0 := by
          apply intervalIntegral.integral_hasDerivAt_right
          · exact h_cont.intervalIntegrable 0 0
          · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
          · exact h_cont.continuousAt
        rw [h_f0] at h_deriv
        have h_F0 : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U (-t) φ = 0 :=
          intervalIntegral.integral_same
        have h_tendsto_real : Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U (-t) φ)
                                      (𝓝[≠] 0) (𝓝 φ) := by
          have := h_deriv.hasDerivWithinAt (s := Set.univ \ {0})
          rw [hasDerivWithinAt_iff_tendsto_slope] at this
          simp only [Set.diff_diff, Set.union_self] at this
          convert this using 1
          · ext h
            unfold slope
            simp only [sub_zero, h_F0, vsub_eq_sub]
          · congr 1
            exact Set.compl_eq_univ_diff {(0 : ℝ)}
        -- Use tendsto at -h as h → 0⁺, so -h → 0⁻
        have tendsto_neg_Ioi : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
          rw [tendsto_nhdsWithin_iff]
          constructor
          · have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
              convert (continuous_neg (G := ℝ)).tendsto 0 using 1
              simp
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with h hh
            simp only [Set.mem_Iio, Left.neg_neg_iff]
            exact hh
        have h_neg_tendsto := h_tendsto_real.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx)) |>.comp tendsto_neg_Ioi
        apply Tendsto.congr' _ h_neg_tendsto
        filter_upwards [self_mem_nhdsWithin] with h hh
        rw [h_eq_int h hh]
        simp only [Function.comp_apply]
        rw [intervalIntegral.integral_symm (-h) 0]
        rw [smul_neg]
        rw [neg_eq_iff_eq_neg, ← neg_smul]
        -- Goal: (-h)⁻¹ • ∫ = -(↑h)⁻¹ • ∫
        -- Convert LHS real scalar to complex
        rw [(Complex.coe_smul (-h)⁻¹ _).symm]
        congr 1
        simp only [ofReal_inv, ofReal_neg, neg_inv]

      have h_comb : Tendsto (fun h : ℝ => Real.exp (-h) • ((h⁻¹ : ℂ) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ))
                            (𝓝[>] 0) (𝓝 ((1 : ℝ) • φ)) := by
        exact Tendsto.smul he h_avg
      simp only [one_smul] at h_comb
      apply Tendsto.congr' _ h_comb
      filter_upwards [self_mem_nhdsWithin] with h hh
      rw [smul_comm]

    · -- Second term: h⁻¹(e^{-h}-1)∫_{≥0} → -∫
      have he : Tendsto (fun h : ℝ => (Real.exp (-h) - 1) / h) (𝓝[>] 0) (𝓝 (-1)) := by
        have tendsto_neg_Ioi : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
          rw [tendsto_nhdsWithin_iff]
          constructor
          · have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
              convert (continuous_neg (G := ℝ)).tendsto 0 using 1
              simp
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with h hh
            simp only [Set.mem_Iio, Left.neg_neg_iff]
            exact hh
        have h1 : Tendsto (fun h : ℝ => (Real.exp (-h) - 1) / (-h) * (-1)) (𝓝[>] 0) (𝓝 (1 * (-1))) := by
          apply Tendsto.mul
          · have := (tendsto_exp_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))).comp tendsto_neg_Ioi
            simp only at this
            convert this using 1
          · exact tendsto_const_nhds
        simp only [mul_neg_one] at h1
        convert h1 using 1
        ext h
        by_cases hh : h = 0
        · simp [hh]
        · field_simp
      have he_cplx : Tendsto (fun h : ℝ => ((Real.exp (-h) - 1) / h : ℂ)) (𝓝[>] 0) (𝓝 (-1)) := by
        convert Tendsto.comp (continuous_ofReal.tendsto (-1)) he using 1
        ext h
        simp only [Function.comp_apply, ofReal_div, ofReal_sub, ofReal_one]
        simp_all only [ne_eq, mul_inv_rev, inv_I, mul_neg, neg_mul, gt_iff_lt, neg_smul, ofReal_neg, ofReal_one]
      have h_prod : Tendsto (fun h : ℝ => ((Real.exp (-h) - 1) / h : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)
                            (𝓝[>] 0) (𝓝 ((-1 : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) :=
        Tendsto.smul he_cplx tendsto_const_nhds
      simp only [neg_one_smul] at h_prod
      apply Tendsto.congr' _ h_prod
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [div_eq_inv_mul]
      conv_lhs =>
        rw [show (↑(Real.exp (-h)) : ℂ) - 1 = ↑(Real.exp (-h) - 1) from by rw [ofReal_sub, ofReal_one]]
        rw [← smul_smul]
      rw [@Complex.coe_smul]

  · -- Case h < 0: use unitary_shift_resolventIntegralMinus_neg
    have h_eq : ∀ h : ℝ, h < 0 → ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) -
                                                   resolventIntegralMinus U_grp φ) =
                         ((h : ℂ)⁻¹ • (Real.exp (-h) - 1) • ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ) +
                         (-(h : ℂ)⁻¹ • ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ) := by
      intro h hh
      rw [unitary_shift_resolventIntegralMinus_neg U_grp φ h hh]
      rw [smul_sub, smul_smul, smul_smul, h_scalar h (ne_of_lt hh)]
      rw [sub_eq_add_neg, neg_smul]

    apply Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact (h_eq h hh).symm

    -- Target: φ - ∫ = (-∫) + φ (reorder for Tendsto.add)
    rw [show φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ =
            (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) + φ by abel]

    apply Tendsto.add

    · -- First term: h⁻¹(e^{-h}-1)∫_{≥-h} → -∫ as h → 0⁻
      -- Note: as h → 0⁻, -h → 0⁺, so ∫_{≥-h} → ∫_{≥0}
      -- And (e^{-h}-1)/h → -1 (since (e^x-1)/x → 1 as x → 0, and here x = -h → 0⁺)
      have he : Tendsto (fun h : ℝ => (Real.exp (-h) - 1) / h) (𝓝[<] 0) (𝓝 (-1)) := by
        have tendsto_neg_Iio : Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝[>] 0) := by
          rw [tendsto_nhdsWithin_iff]
          constructor
          · have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
              convert (continuous_neg (G := ℝ)).tendsto 0 using 1
              simp
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with h hh
            simp only [Set.mem_Ioi, Left.neg_pos_iff]
            exact hh
        have h1 : Tendsto (fun h : ℝ => (Real.exp (-h) - 1) / (-h) * (-1)) (𝓝[<] 0) (𝓝 (1 * (-1))) := by
          apply Tendsto.mul
          · have := (tendsto_exp_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))).comp tendsto_neg_Iio
            simp only at this
            convert this using 1
          · exact tendsto_const_nhds
        simp only [mul_neg_one] at h1
        convert h1 using 1
        ext h
        by_cases hh : h = 0
        · simp [hh]
        · field_simp
      have he_cplx : Tendsto (fun h : ℝ => ((Real.exp (-h) - 1) / h : ℂ)) (𝓝[<] 0) (𝓝 (-1)) := by
        convert Tendsto.comp (continuous_ofReal.tendsto (-1)) he using 1
        ext h
        simp only [Function.comp_apply, ofReal_div, ofReal_sub, ofReal_one]
        rw [ofReal_neg]
        exact rfl
      -- ∫_{≥-h} → ∫_{≥0} as h → 0⁻ (i.e., -h → 0⁺)
      have hi : Tendsto (fun h : ℝ => ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ)
                        (𝓝[<] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) := by
        have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U (-t) φ) :=
          ((Real.continuous_exp.comp continuous_neg).smul
           ((U_grp.strong_continuous φ).comp continuous_neg))
        have h_int := integrable_exp_neg_unitary_neg U_grp φ
        have h_prim_cont : Continuous (fun a => ∫ t in (0 : ℝ)..a, Real.exp (-t) • U_grp.U (-t) φ) :=
          intervalIntegral.continuous_primitive (fun a b => h_cont.intervalIntegrable a b) 0
        have h_prim_zero : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U (-t) φ = 0 :=
          intervalIntegral.integral_same
        have h_prim_tendsto : Tendsto (fun a => ∫ t in (0 : ℝ)..a, Real.exp (-t) • U_grp.U (-t) φ)
                                      (𝓝 0) (𝓝 0) := by
          rw [← h_prim_zero]
          exact h_prim_cont.tendsto 0
        -- ∫_{≥-h} = ∫_{≥0} - ∫_{(0,-h]} for h < 0
        have h_split : ∀ h < 0, ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ =
                                (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) -
                                ∫ t in (0 : ℝ)..(-h), Real.exp (-t) • U_grp.U (-t) φ := by
          intro h hh
          have h_neg_pos : -h > 0 := neg_pos.mpr hh
          have h_ae_eq1 : ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ =
                          ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U (-t) φ :=
            setIntegral_congr_set Ioi_ae_eq_Ici.symm
          have h_ae_eq2 : ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ =
                          ∫ t in Set.Ioi (-h), Real.exp (-t) • U_grp.U (-t) φ :=
            setIntegral_congr_set Ioi_ae_eq_Ici.symm
          have h_union : Set.Ioi 0 = Set.Ioc 0 (-h) ∪ Set.Ioi (-h) := by
            ext x
            simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
            constructor
            · intro hx
              by_cases hxh : x ≤ -h
              · left; exact ⟨hx, hxh⟩
              · right; linarith
            · intro hx
              cases hx with
              | inl hx => exact hx.1
              | inr hx => linarith [h_neg_pos, hx]
          have h_disj : Disjoint (Set.Ioc 0 (-h)) (Set.Ioi (-h)) := Set.Ioc_disjoint_Ioi le_rfl
          have h_eq1 : ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U (-t) φ =
                       (∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ) +
                       ∫ t in Set.Ioi (-h), Real.exp (-t) • U_grp.U (-t) φ := by
            rw [h_union, setIntegral_union h_disj measurableSet_Ioi
                (h_cont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
                (h_int.mono_set (Set.Ioi_subset_Ici h_neg_pos.le))]
          have h_eq2 : ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ =
                       ∫ t in (0 : ℝ)..(-h), Real.exp (-t) • U_grp.U (-t) φ := by
            rw [intervalIntegral.integral_of_le h_neg_pos.le]
          rw [h_ae_eq1, h_eq1, h_ae_eq2.symm, h_eq2]
          ring_nf
          exact
            Eq.symm
              (add_sub_cancel_left (∫ (t : ℝ) in 0..-h, Real.exp (-t) • (U_grp.U (-t)) φ)
                (∫ (t : ℝ) in Set.Ici (-h), Real.exp (-t) • (U_grp.U (-t)) φ))
        -- Tendsto: ∫_{0..-h} → 0 as h → 0⁻ (since -h → 0⁺)
        have h_int_tendsto : Tendsto (fun h : ℝ => ∫ t in (0 : ℝ)..(-h), Real.exp (-t) • U_grp.U (-t) φ)
                                     (𝓝[<] 0) (𝓝 0) := by
          have h_neg_tendsto : Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝 0) := by
            have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
              convert (continuous_neg (G := ℝ)).tendsto 0 using 1
              simp
            exact this.mono_left nhdsWithin_le_nhds
          have := h_prim_tendsto.comp h_neg_tendsto
          simp only at this
          convert this using 1
        have h_combined : Tendsto (fun h : ℝ => (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) -
                                                 ∫ t in (0 : ℝ)..(-h), Real.exp (-t) • U_grp.U (-t) φ)
                                  (𝓝[<] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) := by
          convert tendsto_const_nhds.sub h_int_tendsto using 1
          simp only [sub_zero]
        apply Tendsto.congr' _ h_combined
        filter_upwards [self_mem_nhdsWithin] with h hh
        exact (h_split h hh).symm
      have h_prod : Tendsto (fun h : ℝ => ((Real.exp (-h) - 1) / h : ℂ) • ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ)
                            (𝓝[<] 0) (𝓝 ((-1 : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) :=
        Tendsto.smul he_cplx hi
      simp only [neg_one_smul] at h_prod
      apply Tendsto.congr' _ h_prod
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [div_eq_inv_mul]
      conv_lhs =>
        rw [show (↑(Real.exp (-h)) : ℂ) - 1 = ↑(Real.exp (-h) - 1) from by rw [ofReal_sub, ofReal_one]]
        rw [← smul_smul]
      rw [@Complex.coe_smul]

    · -- Second term: -h⁻¹ • ∫_{(0,-h]} → φ as h → 0⁻
      -- Note: h⁻¹ is negative, and -(h⁻¹) = (-h)⁻¹
      -- So -h⁻¹ • ∫_{(0,-h]} = (-h)⁻¹ • ∫_{(0,-h]} → φ by FTC
      have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U (-t) φ) :=
        ((Real.continuous_exp.comp continuous_neg).smul
         ((U_grp.strong_continuous φ).comp continuous_neg))
      have h_f0 : Real.exp (-(0 : ℝ)) • U_grp.U (-(0 : ℝ)) φ = φ := by
        simp only [neg_zero, Real.exp_zero, one_smul]
        rw [U_grp.identity]
        simp only [ContinuousLinearMap.id_apply]
      -- Use tendsto_average_integral_unitary for the negative version
      have h_avg : Tendsto (fun h : ℝ => (h⁻¹ : ℂ) • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U (-t) φ)
                           (𝓝[>] 0) (𝓝 φ) := by
        have h_eq_int : ∀ h > 0, ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U (-t) φ =
                                 ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U (-t) φ := by
          intro h hh
          rw [intervalIntegral.integral_of_le (le_of_lt hh)]
        have h_deriv : HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, Real.exp (-t) • U_grp.U (-t) φ)
                                  (Real.exp (-(0 : ℝ)) • U_grp.U (-(0 : ℝ)) φ) 0 := by
          apply intervalIntegral.integral_hasDerivAt_right
          · exact h_cont.intervalIntegrable 0 0
          · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
          · exact h_cont.continuousAt
        rw [h_f0] at h_deriv
        have h_F0 : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U (-t) φ = 0 :=
          intervalIntegral.integral_same
        have h_tendsto_real : Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U (-t) φ)
                                      (𝓝[≠] 0) (𝓝 φ) := by
          have := h_deriv.hasDerivWithinAt (s := Set.univ \ {0})
          rw [hasDerivWithinAt_iff_tendsto_slope] at this
          simp only [Set.diff_diff, Set.union_self] at this
          convert this using 1
          · ext h
            unfold slope
            simp only [sub_zero, h_F0, vsub_eq_sub]
          · congr 1
            exact Set.compl_eq_univ_diff {(0 : ℝ)}
        have h_restrict := h_tendsto_real.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
        apply Tendsto.congr' _ h_restrict
        filter_upwards [self_mem_nhdsWithin] with h hh
        rw [h_eq_int h hh, (Complex.coe_smul h⁻¹ _).symm, ofReal_inv]
      -- Now compose with negation: h → -h maps 𝓝[<] 0 to 𝓝[>] 0
      have tendsto_neg_Iio : Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝[>] 0) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
            convert (continuous_neg (G := ℝ)).tendsto 0 using 1
            simp
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with h hh
          simp only [Set.mem_Ioi, Left.neg_pos_iff]
          exact hh
      have h_comp := h_avg.comp tendsto_neg_Iio
      -- h_comp: Tendsto (fun h => (-h)⁻¹ • ∫_{(0,-h]}) (𝓝[<] 0) (𝓝 φ)
      apply Tendsto.congr' _ h_comp
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [Function.comp_apply]
      -- Goal: -h⁻¹ • ∫_{(0,-h]} = (-h)⁻¹ • ∫_{(0,-h]}
      -- Since h < 0, we have h⁻¹ < 0 and -h⁻¹ = (-h)⁻¹
      rw [show -(h : ℂ)⁻¹ = ((-h) : ℂ)⁻¹ from by rw [@neg_inv]]
      simp only [ofReal_neg, inv_neg, neg_smul]



end GeneratorLimit

/-!
================================================================================
SECTION 5: CONSTRUCTION OF THE GENERATOR
================================================================================

Define the generator and prove it's self-adjoint.
-/

section GeneratorConstruction

open Classical
open InnerProductSpace
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The domain of the generator: vectors where the limit exists.

This is characterized as:
D(A) = {ψ ∈ H | lim_{h→0} (U(h)ψ - ψ)/(ih) exists}

We construct this as a submodule.
-/
noncomputable def generatorDomain : Submodule ℂ H where
  carrier := {ψ : H | ∃ (η : H), Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ - ψ))
                                         (𝓝[≠] 0) (𝓝 η)}
  add_mem' := by
    intro ψ₁ ψ₂ ⟨η₁, hη₁⟩ ⟨η₂, hη₂⟩
    refine ⟨η₁ + η₂, ?_⟩
    have h_add : ∀ h : ℝ, ((I * h)⁻¹ : ℂ) • (U_grp.U h (ψ₁ + ψ₂) - (ψ₁ + ψ₂)) =
                         ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₁ - ψ₁) +
                         ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₂ - ψ₂) := by
      intro h
      rw [map_add]
      ring_nf
      -- ⊢ (I⁻¹ * (↑h)⁻¹) • ((U_grp.U h) ψ₁ + (U_grp.U h) ψ₂ - (ψ₁ + ψ₂)) = (I⁻¹ * (↑h)⁻¹) • ((U_grp.U h) ψ₁ - ψ₁) + (I⁻¹ * (↑h)⁻¹) • ((U_grp.U h) ψ₂ - ψ₂)
      rw [← smul_add]
      congr 1
      abel
    simp_rw [h_add]
    exact hη₁.add hη₂
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp only [map_zero, sub_zero, smul_zero]
    exact tendsto_const_nhds
  smul_mem' := by
    intro c ψ ⟨η, hη⟩
    refine ⟨c • η, ?_⟩
    have h_smul : ∀ h : ℝ, ((I * h)⁻¹ : ℂ) • (U_grp.U h (c • ψ) - c • ψ) =
                          c • (((I * h)⁻¹ : ℂ) • (U_grp.U h ψ - ψ)) := by
      intro h
      rw [ContinuousLinearMap.map_smul, smul_sub, smul_comm]
      -- ⊢ c • (I * ↑h)⁻¹ • (U_grp.U h) ψ - (I * ↑h)⁻¹ • c • ψ = c • (I * ↑h)⁻¹ • ((U_grp.U h) ψ - ψ)
      rw [smul_comm ((I * (h : ℂ))⁻¹) c ψ, ← smul_sub, ← smul_sub]
    simp_rw [h_smul]
    exact hη.const_smul c

/-- Helper to extract the limit value for vectors in the domain. -/
noncomputable def generatorLimitValue (ψ : H)
    (hψ : ψ ∈ generatorDomain U_grp) : H :=
  Classical.choose hψ

lemma generatorLimitValue_spec (ψ : H) (hψ : ψ ∈ generatorDomain U_grp) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ - ψ))
            (𝓝[≠] 0) (𝓝 (generatorLimitValue U_grp ψ hψ)) :=
  Classical.choose_spec hψ

/-- The generator operator on the domain.

For ψ ∈ D(A), we define Aψ = lim_{h→0} (U(h)ψ - ψ)/(ih).
Outside the domain, we define it to be 0 (arbitrary choice).
-/
noncomputable def generatorOp : (generatorDomain U_grp) →ₗ[ℂ] H where
  toFun := fun ⟨ψ, hψ⟩ => generatorLimitValue U_grp ψ hψ
  map_add' := by
    intro ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩
    have hψ_sum : ψ₁ + ψ₂ ∈ generatorDomain U_grp := (generatorDomain U_grp).add_mem hψ₁ hψ₂
    simp
    -- Show generatorLimitValue (ψ₁ + ψ₂) = generatorLimitValue ψ₁ + generatorLimitValue ψ₂
    have h₁ := generatorLimitValue_spec U_grp ψ₁ hψ₁
    have h₂ := generatorLimitValue_spec U_grp ψ₂ hψ₂
    have h_sum := generatorLimitValue_spec U_grp (ψ₁ + ψ₂) hψ_sum
    have h_add_lim : Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (ψ₁ + ψ₂) - (ψ₁ + ψ₂)))
                             (𝓝[≠] 0)
                             (𝓝 (generatorLimitValue U_grp ψ₁ hψ₁ + generatorLimitValue U_grp ψ₂ hψ₂)) := by
      have h_eq : ∀ h : ℝ, ((I * h)⁻¹ : ℂ) • (U_grp.U h (ψ₁ + ψ₂) - (ψ₁ + ψ₂)) =
                          ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₁ - ψ₁) +
                          ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₂ - ψ₂) := by
        intro h
        rw [map_add, ← smul_add]
        congr 1
        abel
      simp_rw [h_eq]
      exact h₁.add h₂
    exact tendsto_nhds_unique h_sum h_add_lim
  map_smul' := by
    intro c ⟨ψ, hψ⟩
    have hcψ : c • ψ ∈ generatorDomain U_grp := (generatorDomain U_grp).smul_mem c hψ
    simp only [RingHom.id_apply]
    have h := generatorLimitValue_spec U_grp ψ hψ
    have hc := generatorLimitValue_spec U_grp (c • ψ) hcψ
    have h_smul_lim : Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (c • ψ) - c • ψ))
                              (𝓝[≠] 0)
                              (𝓝 (c • generatorLimitValue U_grp ψ hψ)) := by
      have h_eq : ∀ h : ℝ, ((I * h)⁻¹ : ℂ) • (U_grp.U h (c • ψ) - c • ψ) =
                          c • (((I * h)⁻¹ : ℂ) • (U_grp.U h ψ - ψ)) := by
        intro h
        rw [ContinuousLinearMap.map_smul, smul_sub, smul_comm]
        rw [smul_comm ((I * (h : ℂ))⁻¹) c ψ, ← smul_sub]
        congr 1
        rw [← smul_sub]
      simp_rw [h_eq]
      exact h.const_smul c
    exact tendsto_nhds_unique hc h_smul_lim



/-- The generator formula holds by construction. -/
theorem generator_formula_holds (ψ : generatorDomain U_grp) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (ψ : H) - (ψ : H)))
            (𝓝[≠] 0)
            (𝓝 (generatorOp U_grp ψ)) := by
  exact generatorLimitValue_spec U_grp ψ.val ψ.property

/-- The domain is invariant under U(t). -/
theorem generatorDomain_invariant (t : ℝ) (ψ : H) (hψ : ψ ∈ generatorDomain U_grp) :
    U_grp.U t ψ ∈ generatorDomain U_grp := by
  -- ψ ∈ domain means the limit exists
  obtain ⟨η, hη⟩ := hψ
  -- The limit for U(t)ψ will be U(t)η
  refine ⟨U_grp.U t η, ?_⟩
  -- Key: (U(h)(U(t)ψ) - U(t)ψ)/(ih) = U(t)((U(h)ψ - ψ)/(ih))
  have h_eq : ∀ h : ℝ, ((I * h)⁻¹ : ℂ) • (U_grp.U h (U_grp.U t ψ) - U_grp.U t ψ) =
                       U_grp.U t (((I * h)⁻¹ : ℂ) • (U_grp.U h ψ - ψ)) := by
    intro h
    -- U(h)(U(t)ψ) = U(t)(U(h)ψ) by commutativity
    have h_comm : U_grp.U h (U_grp.U t ψ) = U_grp.U t (U_grp.U h ψ) := by
      calc U_grp.U h (U_grp.U t ψ)
          = (U_grp.U h).comp (U_grp.U t) ψ := rfl
        _ = U_grp.U (h + t) ψ := by rw [← U_grp.group_law]
        _ = U_grp.U (t + h) ψ := by rw [add_comm]
        _ = (U_grp.U t).comp (U_grp.U h) ψ := by rw [U_grp.group_law]
        _ = U_grp.U t (U_grp.U h ψ) := rfl
    rw [h_comm, ← ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul]
  simp_rw [h_eq]
  -- U(t) is continuous, so it preserves limits
  exact (U_grp.U t).continuous.tendsto _ |>.comp hη

/-- The generator is symmetric. -/
theorem generator_symmetric (ψ₁ ψ₂ : generatorDomain U_grp) :
    ⟪generatorOp U_grp ψ₁, (ψ₂ : H)⟫_ℂ = ⟪(ψ₁ : H), generatorOp U_grp ψ₂⟫_ℂ := by
  -- Get the limit characterizations
  have h₁ := generatorLimitValue_spec U_grp ψ₁.val ψ₁.property
  have h₂ := generatorLimitValue_spec U_grp ψ₂.val ψ₂.property

  -- Inner product is continuous in first argument
  have h_lhs : Tendsto (fun h : ℝ => ⟪((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₁ - ψ₁), (ψ₂ : H)⟫_ℂ)
                       (𝓝[≠] 0) (𝓝 ⟪generatorOp U_grp ψ₁, (ψ₂ : H)⟫_ℂ) :=
    Tendsto.inner h₁ tendsto_const_nhds

  have h_rhs : Tendsto (fun h : ℝ => ⟪(ψ₁ : H), ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₂ - ψ₂)⟫_ℂ)
                       (𝓝[≠] 0) (𝓝 ⟪(ψ₁ : H), generatorOp U_grp ψ₂⟫_ℂ) :=
    Tendsto.inner tendsto_const_nhds h₂

  -- Key: show ⟨(U(h)ψ₁ - ψ₁)/(ih), ψ₂⟩ = ⟨ψ₁, (U(-h)ψ₂ - ψ₂)/(i(-h))⟩
  have h_eq : ∀ h : ℝ, h ≠ 0 →
      ⟪((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₁ - ψ₁), (ψ₂ : H)⟫_ℂ =
      ⟪(ψ₁ : H), ((I * (-h))⁻¹ : ℂ) • (U_grp.U (-h) ψ₂ - ψ₂)⟫_ℂ := by
    intro h hh
    -- Expand inner product with scalar on left
    rw [inner_smul_left]
    -- Use unitarity: ⟨U(h)x, y⟩ = ⟨x, U(-h)y⟩
    have h_unitary : ⟪U_grp.U h ψ₁, (ψ₂ : H)⟫_ℂ = ⟪(ψ₁ : H), U_grp.U (-h) ψ₂⟫_ℂ := by
      calc ⟪U_grp.U h ψ₁, (ψ₂ : H)⟫_ℂ
          = ⟪U_grp.U (-h) (U_grp.U h ψ₁), U_grp.U (-h) ψ₂⟫_ℂ := by rw [U_grp.unitary (-h)]
        _ = ⟪(U_grp.U (-h)).comp (U_grp.U h) ψ₁, U_grp.U (-h) ψ₂⟫_ℂ := rfl
        _ = ⟪U_grp.U ((-h) + h) ψ₁, U_grp.U (-h) ψ₂⟫_ℂ := by rw [← U_grp.group_law]
        _ = ⟪U_grp.U 0 ψ₁, U_grp.U (-h) ψ₂⟫_ℂ := by ring_nf
        _ = ⟪(ψ₁ : H), U_grp.U (-h) ψ₂⟫_ℂ := by rw [U_grp.identity]; rfl
    rw [inner_sub_left, h_unitary, ← inner_sub_right]
    -- Now deal with scalars
    rw [inner_smul_right]
    congr 1
    -- Show conj((ih)⁻¹) = (i(-h))⁻¹
    simp only [map_inv₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring

  -- Use filter convergence with the equality
  have h_rhs' : Tendsto (fun h : ℝ => ⟪(ψ₁ : H), ((I * (-h))⁻¹ : ℂ) • (U_grp.U (-h) ψ₂ - ψ₂)⟫_ℂ)
                        (𝓝[≠] 0) (𝓝 ⟪(ψ₁ : H), generatorOp U_grp ψ₂⟫_ℂ) := by
    have h_neg : Tendsto (fun h : ℝ => -h) (𝓝[≠] 0) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
          convert (continuous_neg (G := ℝ)).tendsto 0 using 1
          simp
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, neg_eq_zero]
        exact hh
    have h_comp := h_rhs.comp h_neg
    apply Tendsto.congr _ h_comp
    intro h
    simp only [Function.comp_apply, ofReal_neg]

  -- Both limits are equal
  refine tendsto_nhds_unique ?_ h_rhs'
  apply Tendsto.congr' _ h_lhs
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact h_eq h hh

/-- The resolvent integrals are in the domain. -/
theorem resolventIntegralPlus_in_domain (φ : H) :
    resolventIntegralPlus U_grp φ ∈ generatorDomain U_grp := by
  exact ⟨φ - I • resolventIntegralPlus U_grp φ, generator_limit_resolventIntegralPlus U_grp φ⟩

theorem resolventIntegralMinus_in_domain (φ : H) :
    resolventIntegralMinus U_grp φ ∈ generatorDomain U_grp := by
  exact ⟨φ + I • resolventIntegralMinus U_grp φ, generator_limit_resolventIntegralMinus U_grp φ⟩

/-- (A + iI)ψ₊ = φ -/
theorem resolventIntegralPlus_solves (φ : H) :
    generatorOp U_grp ⟨resolventIntegralPlus U_grp φ, resolventIntegralPlus_in_domain U_grp φ⟩ +
    I • resolventIntegralPlus U_grp φ = φ := by
      classical
  have hψ := resolventIntegralPlus_in_domain U_grp φ
  simp only [generatorOp] -- unused dif_pos hψ
  have h_lim := generatorLimitValue_spec U_grp (resolventIntegralPlus U_grp φ) hψ
  have h_target := generator_limit_resolventIntegralPlus U_grp φ
  have h_eq := tendsto_nhds_unique h_lim h_target
  -- h_eq : generatorLimitValue = φ - I • ψ₊
  -- Goal: (φ - I • ψ₊) + I • ψ₊ = φ
  /-
  ⊢ { toFun := fun ψ => if hψ : ψ ∈ generatorDomain U_grp then generatorLimitValue U_grp ψ hψ else 0, map_add' := ⋯, map_smul' := ⋯ }
      (resolventIntegralPlus U_grp φ) + I • resolventIntegralPlus U_grp φ = φ
  -/
  --rw [h_eq]
  -- Tactic `rewrite` failed: Did not find an occurrence of the pattern
  -- generatorLimitValue U_grp (resolventIntegralPlus U_grp φ) hψ
  abel_nf
  rw [@LinearMap.coe_mk]
  simp_all only [mul_inv_rev, inv_I, mul_neg, neg_smul, AddHom.coe_mk, sub_add_cancel]


/-- (A - iI)ψ₋ = φ -/
theorem resolventIntegralMinus_solves (φ : H) :
    generatorOp U_grp ⟨resolventIntegralMinus U_grp φ, resolventIntegralMinus_in_domain U_grp φ⟩ -
    I • resolventIntegralMinus U_grp φ = φ := by
  classical
  have hψ := resolventIntegralMinus_in_domain U_grp φ
  simp only [generatorOp] -- unused dif_pos hψ
  have h_lim := generatorLimitValue_spec U_grp (resolventIntegralMinus U_grp φ) hψ
  have h_target := generator_limit_resolventIntegralMinus U_grp φ
  have h_eq := tendsto_nhds_unique h_lim h_target
  -- h_eq : generatorLimitValue = φ + I • ψ₋
  -- Goal: (φ + I • ψ₋) - I • ψ₋ = φ
  --rw [h_eq]
  -- Tactic `rewrite` failed: Did not find an occurrence of the pattern
  -- generatorLimitValue U_grp (resolventIntegralPlus U_grp φ) hψ
  abel_nf
  simp_all only [mul_inv_rev, inv_I, mul_neg, neg_smul, LinearMap.coe_mk, AddHom.coe_mk, Int.reduceNeg,
    one_smul, add_neg_cancel_right]

/-- Range(A + iI) = H -/
theorem range_plus_i_eq_top :
    ∀ φ : H, ∃ ψ : generatorDomain U_grp,
      generatorOp U_grp ψ + I • (ψ : H) = φ := by
  intro φ
  exact ⟨⟨resolventIntegralPlus U_grp φ, resolventIntegralPlus_in_domain U_grp φ⟩,
         resolventIntegralPlus_solves U_grp φ⟩

/-- Range(A - iI) = H -/
theorem range_minus_i_eq_top :
    ∀ φ : H, ∃ ψ : generatorDomain U_grp,
      generatorOp U_grp ψ - I • (ψ : H) = φ := by
  intro φ
  exact ⟨⟨resolventIntegralMinus U_grp φ, resolventIntegralMinus_in_domain U_grp φ⟩,
         resolventIntegralMinus_solves U_grp φ⟩






end GeneratorConstruction

/-!
================================================================================
SECTION 6: AVERAGED VECTORS AND DOMAIN DENSITY
================================================================================

Alternative proof of domain density via averaged vectors.
-/

section AveragedVectors

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The averaged vector ψₕ = (1/h) ∫₀ʰ U(t)φ dt. -/
noncomputable def averagedVector (h : ℝ) (_ /-hh-/ : h ≠ 0) (φ : H) : H :=
  (h⁻¹ : ℂ) • ∫ t in Set.Ioc 0 h, U_grp.U t φ

/-- The averaged vector converges to φ as h → 0. -/
lemma averagedVector_tendsto (φ : H) :
    Tendsto (fun h : ℝ => if hh : h ≠ 0 then averagedVector U_grp h hh φ else φ)
            (𝓝[>] 0) (𝓝 φ) := by
  unfold averagedVector
  have h_cont : Continuous (fun t => U_grp.U t φ) := U_grp.strong_continuous φ
  have h_f0 : U_grp.U 0 φ = φ := by rw [U_grp.identity]; rfl
  -- FTC: derivative of ∫_0^x f(t) dt at x=0 is f(0)
  have h_deriv : HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, U_grp.U t φ) (U_grp.U 0 φ) 0 := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact h_cont.intervalIntegrable 0 0
    · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
    · exact h_cont.continuousAt
  rw [h_f0] at h_deriv
  have h_F0 : ∫ t in (0 : ℝ)..0, U_grp.U t φ = 0 := intervalIntegral.integral_same
  -- The slope (F(h) - F(0))/h = F(h)/h → φ
  have h_tendsto_real : Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, U_grp.U t φ)
                                (𝓝[≠] 0) (𝓝 φ) := by
    have := h_deriv.hasDerivWithinAt (s := Set.univ \ {0})
    rw [hasDerivWithinAt_iff_tendsto_slope] at this
    simp only [Set.diff_diff, Set.union_self] at this
    convert this using 1
    · ext h
      unfold slope
      simp only [sub_zero, h_F0, vsub_eq_sub]
    · congr 1
      exact Set.compl_eq_univ_diff {(0 : ℝ)}
  -- Restrict to h > 0
  have h_restrict := h_tendsto_real.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
  apply Tendsto.congr' _ h_restrict
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [dif_pos (ne_of_gt hh)]
  rw [intervalIntegral.integral_of_le (le_of_lt hh)]
  -- Goal: (↑h⁻¹ : ℂ) • ∫ t in Set.Ioc 0 h, U_grp.U t φ = h⁻¹ • ∫ t in Set.Ioc 0 h, U_grp.U t φ
  rw [(Complex.coe_smul h⁻¹ _).symm, ofReal_inv]

/-- The averaged vector is in the domain of the generator.
The point is ψₕ ∈ D(A), and as h → 0, ψₕ → φ, proving density.
-/
lemma averagedVector_in_domain (h : ℝ) (hh : h ≠ 0) (φ : H) :
    averagedVector U_grp h hh φ ∈ generatorDomain U_grp := by
  -- Handle h < 0 separately: Ioc 0 h is empty, so averagedVector = 0
  by_cases hpos : h > 0
  · -- Case h > 0: the main calculation
    refine ⟨((I * h)⁻¹ : ℂ) • (U_grp.U h φ - φ), ?_⟩

    have h_cont : Continuous (fun t => U_grp.U t φ) := U_grp.strong_continuous φ
    set ψ := averagedVector U_grp h hh φ with hψ_def

    -- Step 1: FTC limits
    have h_FTC1 : Tendsto (fun s : ℝ => (s⁻¹ : ℂ) • ∫ t in (0 : ℝ)..s, U_grp.U t φ) (𝓝[≠] 0) (𝓝 φ) := by
      have h_deriv : HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, U_grp.U t φ) φ 0 := by
        have := intervalIntegral.integral_hasDerivAt_right (h_cont.intervalIntegrable 0 0)
                  (h_cont.stronglyMeasurableAtFilter volume (𝓝 0)) h_cont.continuousAt
        simp only [U_grp.identity, ContinuousLinearMap.id_apply] at this
        exact this
      have h_F0 : ∫ t in (0 : ℝ)..0, U_grp.U t φ = 0 := intervalIntegral.integral_same
      rw [hasDerivAt_iff_tendsto_slope] at h_deriv
      apply h_deriv.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      unfold slope
      simp only [vsub_eq_sub, sub_zero, h_F0, sub_zero]
      rw [(Complex.coe_smul s⁻¹ _).symm, ofReal_inv]

    have h_FTC2 : Tendsto (fun s : ℝ => (s⁻¹ : ℂ) • ∫ t in (h : ℝ)..(h + s), U_grp.U t φ) (𝓝[≠] 0) (𝓝 (U_grp.U h φ)) := by
      have h_deriv : HasDerivAt (fun x => ∫ t in (h : ℝ)..x, U_grp.U t φ) (U_grp.U h φ) h := by
        exact intervalIntegral.integral_hasDerivAt_right (h_cont.intervalIntegrable h h)
                (h_cont.stronglyMeasurableAtFilter volume (𝓝 h)) h_cont.continuousAt
      have h_Fh : ∫ t in (h : ℝ)..h, U_grp.U t φ = 0 := intervalIntegral.integral_same
      rw [hasDerivAt_iff_tendsto_slope] at h_deriv
      have h_shift : Tendsto (fun s : ℝ => h + s) (𝓝[≠] 0) (𝓝[≠] h) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · have : Tendsto (fun s : ℝ => h + s) (𝓝 0) (𝓝 h) := by
            have h1 : Tendsto (fun _ : ℝ => h) (𝓝 0) (𝓝 h) := tendsto_const_nhds
            have h2 : Tendsto (fun s : ℝ => s) (𝓝 0) (𝓝 0) := tendsto_id
            convert h1.add h2 using 1
            simp only [add_zero]
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left]
          exact hs
      have := h_deriv.comp h_shift
      simp only at this
      apply this.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      unfold slope
      simp only [vsub_eq_sub, h_Fh, sub_zero, Function.comp_apply, add_sub_cancel_left]
      rw [(Complex.coe_smul s⁻¹ _).symm, ofReal_inv]

    -- Step 2: Show the expression equals (1/(ih)) • (average at h+s - average at s)
    have h_key : ∀ s : ℝ, s ≠ 0 →
        ((I * s)⁻¹ : ℂ) • (U_grp.U s ψ - ψ) =
        ((I * h)⁻¹ : ℂ) • (((s⁻¹ : ℂ) • ∫ t in (h : ℝ)..(h + s), U_grp.U t φ) -
                           ((s⁻¹ : ℂ) • ∫ t in (0 : ℝ)..s, U_grp.U t φ)) := by
      intro s hs
      rw [hψ_def]
      unfold averagedVector
      rw [ContinuousLinearMap.map_smul]
      have h_shift_int : U_grp.U s (∫ t in Set.Ioc 0 h, U_grp.U t φ) =
                         ∫ t in Set.Ioc s (s + h), U_grp.U t φ := by
        rw [← (U_grp.U s).integral_comp_comm h_cont.integrableOn_Ioc]
        have h_subst : ∫ t in Set.Ioc 0 h, U_grp.U s (U_grp.U t φ) =
                       ∫ t in Set.Ioc 0 h, U_grp.U (s + t) φ := by
          congr 1; ext t
          rw [@OneParameterUnitaryGroup.group_law]
          exact rfl
        rw [h_subst]
        have h_preimage : (fun t => t - s) ⁻¹' (Set.Ioc 0 h) = Set.Ioc s (s + h) := by
          ext t; simp only [Set.mem_preimage, Set.mem_Ioc]; constructor <;> intro ⟨a, b⟩ <;> constructor <;> linarith
        have h_meas : Measure.map (fun t => t - s) volume = volume :=
          (measurePreserving_sub_right volume s).map_eq
        rw [← h_meas, MeasureTheory.setIntegral_map measurableSet_Ioc]
        · simp only [h_preimage]; congr 1
          exact congrFun (congrArg restrict (id (Eq.symm h_meas))) (Set.Ioc s (s + h))
          simp only [add_sub_cancel]
        · exact h_cont.aestronglyMeasurable.comp_measurable (measurable_const_add s)
        · exact (measurable_sub_const s).aemeasurable
      rw [h_shift_int]
      rw [← smul_sub, smul_smul]
      have h_Ioc_eq_interval : ∀ a b : ℝ, a ≤ b → ∫ t in Set.Ioc a b, U_grp.U t φ =
                                                    ∫ t in a..b, U_grp.U t φ := by
        intro a b hab
        rw [intervalIntegral.integral_of_le hab]
      rw [h_Ioc_eq_interval s (s + h) (by linarith), h_Ioc_eq_interval 0 h (le_of_lt hpos)]
      have h_arith : (∫ t in s..(s + h), U_grp.U t φ) - ∫ t in (0 : ℝ)..h, U_grp.U t φ =
               (∫ t in (h : ℝ)..(h + s), U_grp.U t φ) - ∫ t in (0 : ℝ)..s, U_grp.U t φ := by
        have hint : ∀ a b : ℝ, IntervalIntegrable (fun t => U_grp.U t φ) volume a b :=
          fun a b => h_cont.intervalIntegrable a b
        have h3 : s + h = h + s := add_comm s h
        have key : (∫ t in s..(s + h), U_grp.U t φ) + ∫ t in (0 : ℝ)..s, U_grp.U t φ =
                  (∫ t in h..(h + s), U_grp.U t φ) + ∫ t in (0 : ℝ)..h, U_grp.U t φ := by
          have eq1 := intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s (s + h))
          have eq2 := intervalIntegral.integral_add_adjacent_intervals (hint 0 h) (hint h (h + s))
          calc (∫ t in s..(s + h), U_grp.U t φ) + ∫ t in (0 : ℝ)..s, U_grp.U t φ
              = (∫ t in (0 : ℝ)..s, U_grp.U t φ) + ∫ t in s..(s + h), U_grp.U t φ := by abel
            _ = ∫ t in (0 : ℝ)..(s + h), U_grp.U t φ := eq1
            _ = ∫ t in (0 : ℝ)..(h + s), U_grp.U t φ := by rw [h3]
            _ = (∫ t in (0 : ℝ)..h, U_grp.U t φ) + ∫ t in h..(h + s), U_grp.U t φ := eq2.symm
            _ = (∫ t in h..(h + s), U_grp.U t φ) + ∫ t in (0 : ℝ)..h, U_grp.U t φ := by abel
        have h_sub : ∀ a b c d : H, a + b = c + d → a - d = c - b := by
          intros a b c d heq
          have h1 : a = c + d - b := by rw [← heq]; abel
          rw [h1]; abel
        exact h_sub _ _ _ _ key
      rw [h_arith]
      have h_scalar : ((I * s)⁻¹ : ℂ) * (h⁻¹ : ℂ) = ((I * h)⁻¹ : ℂ) * (s⁻¹ : ℂ) := by
        field_simp
      rw [h_scalar, ← smul_smul, smul_sub]

    -- Step 3: Take the limit
    apply Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact (h_key s hs).symm
    · exact Tendsto.smul tendsto_const_nhds (h_FTC2.sub h_FTC1)

  · -- Case h < 0: averagedVector = 0 which is in domain
    push_neg at hpos
    have hneg : h < 0 := lt_of_le_of_ne hpos (Ne.symm hh.symm)
    have h_empty : Set.Ioc 0 h = ∅ := Set.Ioc_eq_empty (not_lt.mpr (le_of_lt hneg))
    unfold averagedVector
    rw [h_empty, setIntegral_empty, smul_zero]
    exact (generatorDomain U_grp).zero_mem


/-- Alternative proof that the domain is dense: averaged vectors span H. -/
theorem generatorDomain_dense_via_average :
    Dense (generatorDomain U_grp : Set H) := by
  rw [Metric.dense_iff]
  intro φ ε hε
  -- averagedVector h φ → φ as h → 0⁺
  have h_tendsto := averagedVector_tendsto U_grp φ
  rw [Metric.tendsto_nhds] at h_tendsto
  specialize h_tendsto ε hε
  rw [Filter.eventually_iff_exists_mem] at h_tendsto
  obtain ⟨S, hS_mem, hS_ball⟩ := h_tendsto
  rw [mem_nhdsWithin] at hS_mem
  obtain ⟨U, hU_open, hU_zero, hU_sub⟩ := hS_mem
  rw [Metric.isOpen_iff] at hU_open
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := hU_open 0 hU_zero
  -- Pick h = δ / 2
  have hh : δ / 2 ≠ 0 := by linarith
  have hh_pos : δ / 2 > 0 := by linarith
  refine ⟨averagedVector U_grp (δ / 2) hh φ, ?_, ?_⟩
  · -- dist φ (averagedVector ...) < ε, i.e., in Metric.ball
    have h_in_ball : δ / 2 ∈ Metric.ball 0 δ := by
      rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_of_pos hh_pos]
      linarith
    have h_in_U : δ / 2 ∈ U := hδ_ball h_in_ball
    have h_in_S : δ / 2 ∈ S := hU_sub ⟨h_in_U, hh_pos⟩
    have := hS_ball (δ / 2) h_in_S
    rw [dif_pos hh] at this
    exact this
  · -- membership in generatorDomain
    exact averagedVector_in_domain U_grp (δ / 2) hh φ

/-- The generator domain is dense in H.

Proof strategy: Show that "averaged vectors" ∫₀ʰ U(t)φ dt are in D(A) for all φ,
and that these vectors span a dense subset as h → 0.
-/
theorem generatorDomain_dense : Dense (generatorDomain U_grp : Set H) :=
  generatorDomain_dense_via_average U_grp


lemma generatorDomain_maximal (ψ : H)
    (h : ∃ η : H, Tendsto (fun t : ℝ => ((I : ℂ) * t)⁻¹ • (U_grp.U t ψ - ψ)) (𝓝[≠] 0) (𝓝 η)) :
    ψ ∈ generatorDomain U_grp := h


/-- **Main Theorem: Construction of Self-Adjoint Generator**

Every strongly continuous one-parameter unitary group has a self-adjoint generator.
-/
noncomputable def generatorOfUnitaryGroup : Generator U_grp where
  op := generatorOp U_grp
  domain := generatorDomain U_grp
  dense_domain := generatorDomain_dense U_grp
  generator_formula := generator_formula_holds U_grp
  domain_invariant := generatorDomain_invariant U_grp
  symmetric := generator_symmetric U_grp
  domain_maximal := generatorDomain_maximal U_grp

theorem generatorOfUnitaryGroup_isSelfAdjoint :
    (generatorOfUnitaryGroup U_grp).IsSelfAdjoint := by
  constructor
  · -- Range(A + iI) = H
    intro φ
    obtain ⟨ψ, hψ_eq⟩ := range_plus_i_eq_top U_grp φ
    exact ⟨ψ.val, ψ.property, hψ_eq⟩
  · -- Range(A - iI) = H
    intro φ
    obtain ⟨ψ, hψ_eq⟩ := range_minus_i_eq_top U_grp φ
    exact ⟨ψ.val, ψ.property, hψ_eq⟩

end AveragedVectors

/-!
================================================================================
SECTION 7: CONNECTING TO STONE'S THEOREM
================================================================================

Bridge lemmas connecting this file to the main theorem files.
-/

section Bridge

variable (U_grp : OneParameterUnitaryGroup (H := H))


/-- **Construction of Generator from Unitary Group**

Given a strongly continuous one-parameter unitary group U(t), we construct
its self-adjoint generator A via:

  D(A) = {ψ ∈ H | lim_{t→0} (U(t)ψ - ψ)/(it) exists}
  Aψ = lim_{t→0} (U(t)ψ - ψ)/(it)

The proof that this is self-adjoint (i.e., Range(A ± iI) = H) uses the
integral formulas:
  ψ₊ = i ∫₀^∞ e^{-t} U(t)φ dt   satisfies (A + iI)ψ₊ = φ
  ψ₋ = -i ∫₀^∞ e^{-t} U(-t)φ dt satisfies (A - iI)ψ₋ = φ

These integrals converge because ‖U(t)‖ = 1 (unitarity) and e^{-t} decays.
-/
noncomputable def Generator.ofUnitaryGroup
    (U_grp : OneParameterUnitaryGroup (H := H)) :
    Generator U_grp :=
  generatorOfUnitaryGroup U_grp

theorem Generator.ofUnitaryGroup_isSelfAdjoint
    (U_grp : OneParameterUnitaryGroup (H := H)) :
    (Generator.ofUnitaryGroup U_grp).IsSelfAdjoint :=
  generatorOfUnitaryGroup_isSelfAdjoint U_grp

/-- The constructed generator matches the one in Resolvent.lean. -/
theorem generatorOfUnitaryGroup_eq_ofUnitaryGroup :
    generatorOfUnitaryGroup U_grp = Generator.ofUnitaryGroup U_grp := by
  -- Both are constructed the same way
  unfold generatorOfUnitaryGroup Generator.ofUnitaryGroup
  rfl

/-- Self-adjointness transfers. -/
theorem isSelfAdjoint_transfer :
    (Generator.ofUnitaryGroup U_grp).IsSelfAdjoint := by
  rw [← generatorOfUnitaryGroup_eq_ofUnitaryGroup]
  exact generatorOfUnitaryGroup_isSelfAdjoint U_grp

end Bridge


/-!
================================================================================
APPENDIX: HELPER LEMMAS FOR BOCHNER INTEGRATION
================================================================================

Technical lemmas about Bochner integrals that may be useful.
-/

section Appendix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Fubini for finite intervals. -/
lemma fubini_Ioc (f : ℝ → ℝ → E) (a b c d : ℝ)
    (hf : Integrable (Function.uncurry f) ((volume.restrict (Set.Ioc a b)).prod
                                           (volume.restrict (Set.Ioc c d)))) :
    ∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d, f x y =
    ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, f x y := by
  exact MeasureTheory.integral_integral_swap hf

/-- Dominated convergence for Bochner integrals. -/
lemma tendsto_integral_of_dominated_convergence
    (f : ℕ → ℝ → E) (g : ℝ → E) (bound : ℝ → ℝ)
    (S : Set ℝ)
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict S))
    (hbound : ∀ n, ∀ᵐ x ∂(volume.restrict S), ‖f n x‖ ≤ bound x)
    (hbound_int : Integrable bound (volume.restrict S))
    (hf_tendsto : ∀ᵐ x ∂(volume.restrict S), Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x in S, f n x) atTop (𝓝 (∫ x in S, g x)) := by
  exact MeasureTheory.tendsto_integral_of_dominated_convergence bound hf_meas hbound_int hbound hf_tendsto


end Appendix

end StonesTheorem.Bochner
