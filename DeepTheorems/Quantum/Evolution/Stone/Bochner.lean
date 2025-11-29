/-
Author: Adam Bornemann
Created: 11-26-2025

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

import LogosLibrary.DeepTheorems.Quantum.Evolution.Stone.Resolvent

namespace StonesTheorem.Bochner

open MeasureTheory Measure Filter Topology Complex Resolvent.Generator
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

open StonesTheorem.Resolvent

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The function t ↦ U(t)φ is continuous (strong continuity). -/
lemma continuous_unitary_apply (φ : H) :
    Continuous (fun t => U_grp.U t φ) :=
  U_grp.strong_continuous φ

/-- The function t ↦ e^{-t} U(t)φ is integrable on [0, ∞). -/
lemma integrable_exp_neg_unitary (φ : H) :
    IntegrableOn (fun t => Real.exp (-t) • U_grp.U t φ) (Set.Ici 0) volume := by
  sorry

/-- The function t ↦ e^{-t} U(-t)φ is integrable on [0, ∞). -/
lemma integrable_exp_neg_unitary_neg (φ : H) :
    IntegrableOn (fun t => Real.exp (-t) • U_grp.U (-t) φ) (Set.Ici 0) volume := by
  sorry

/-- Bound on the integral of e^{-t} U(t)φ. -/
lemma norm_integral_exp_neg_unitary_le (φ : H) :
    ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ ≤ ‖φ‖ := by
  sorry

/-- The averaged vector ∫₀ʰ U(t)φ dt exists for any h > 0. -/
lemma integrable_unitary_Ioc (φ : H) (h : ℝ) (hh : 0 < h) :
    IntegrableOn (fun t => U_grp.U t φ) (Set.Ioc 0 h) volume := by
  sorry

end UnitaryGroupIntegration

/-!
================================================================================
SECTION 3: THE RESOLVENT INTEGRALS
================================================================================

Define the integral formulas that solve (A ± iI)ψ = φ.
-/

section ResolventIntegrals

open StonesTheorem.Resolvent

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The integral ψ₊ = i ∫₀^∞ e^{-t} U(t)φ dt, which will solve (A + iI)ψ₊ = φ. -/
noncomputable def resolventIntegralPlus (φ : H) : H :=
  I • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ

/-- The integral ψ₋ = -i ∫₀^∞ e^{-t} U(-t)φ dt, which will solve (A - iI)ψ₋ = φ. -/
noncomputable def resolventIntegralMinus (φ : H) : H :=
  (-I) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ

/-- The resolvent integral ψ₊ is linear in φ. -/
lemma resolventIntegralPlus_add (φ₁ φ₂ : H) :
    resolventIntegralPlus U_grp (φ₁ + φ₂) =
    resolventIntegralPlus U_grp φ₁ + resolventIntegralPlus U_grp φ₂ := by
  sorry

/-- The resolvent integral ψ₊ is bounded: ‖ψ₊‖ ≤ ‖φ‖. -/
lemma norm_resolventIntegralPlus_le (φ : H) :
    ‖resolventIntegralPlus U_grp φ‖ ≤ ‖φ‖ := by
  sorry

/-- The resolvent integral ψ₋ is bounded: ‖ψ₋‖ ≤ ‖φ‖. -/
lemma norm_resolventIntegralMinus_le (φ : H) :
    ‖resolventIntegralMinus U_grp φ‖ ≤ ‖φ‖ := by
  sorry

end ResolventIntegrals

/-!
================================================================================
SECTION 4: THE GENERATOR LIMIT FOR RESOLVENT INTEGRALS
================================================================================

Show that ψ₊ and ψ₋ are in the domain of the generator, i.e., the limit
defining Aψ exists.
-/

section GeneratorLimit

open StonesTheorem.Resolvent

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
    I • ((Real.exp h - 1) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) -
    I • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ := by
  sorry

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
lemma generator_limit_resolventIntegralPlus (φ : H) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
                                              resolventIntegralPlus U_grp φ))
            (𝓝[≠] 0)
            (𝓝 (φ - I • resolventIntegralPlus U_grp φ)) := by
  sorry

/-- The limit for ψ₋ exists and gives (A - iI)ψ₋ = φ. -/
lemma generator_limit_resolventIntegralMinus (φ : H) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) -
                                              resolventIntegralMinus U_grp φ))
            (𝓝[≠] 0)
            (𝓝 (φ + I • resolventIntegralMinus U_grp φ)) := by
  sorry

end GeneratorLimit

/-!
================================================================================
SECTION 5: CONSTRUCTION OF THE GENERATOR
================================================================================

Define the generator and prove it's self-adjoint.
-/

section GeneratorConstruction

open StonesTheorem.Resolvent
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
      sorry
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
      sorry
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
noncomputable def generatorOp : H →ₗ[ℂ] H where
  toFun := fun ψ =>
    if hψ : ψ ∈ generatorDomain U_grp then
      generatorLimitValue U_grp ψ hψ
    else 0
  map_add' := by
    intro ψ₁ ψ₂
    classical
    by_cases hψ₁ : ψ₁ ∈ generatorDomain U_grp <;>
    by_cases hψ₂ : ψ₂ ∈ generatorDomain U_grp
    · -- Both in domain
      have hψ_sum : ψ₁ + ψ₂ ∈ generatorDomain U_grp :=
        (generatorDomain U_grp).add_mem hψ₁ hψ₂
      simp only [dif_pos hψ₁, dif_pos hψ₂, dif_pos hψ_sum]
      -- Both sides are limits of the same expression, so they're equal
      have h₁ := generatorLimitValue_spec U_grp ψ₁ hψ₁
      have h₂ := generatorLimitValue_spec U_grp ψ₂ hψ₂
      have h_sum := generatorLimitValue_spec U_grp (ψ₁ + ψ₂) hψ_sum
      -- The limit of the sum equals the sum of the limits
      have h_add_lim : Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (ψ₁ + ψ₂) - (ψ₁ + ψ₂)))
                               (𝓝[≠] 0)
                               (𝓝 (generatorLimitValue U_grp ψ₁ hψ₁ + generatorLimitValue U_grp ψ₂ hψ₂)) := by
        have h_eq : ∀ h : ℝ, ((I * h)⁻¹ : ℂ) • (U_grp.U h (ψ₁ + ψ₂) - (ψ₁ + ψ₂)) =
                            ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₁ - ψ₁) +
                            ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₂ - ψ₂) := by
          intro h
          rw [map_add]
          rw [← smul_add]
          congr 1
          abel
        simp_rw [h_eq]
        exact h₁.add h₂
      exact tendsto_nhds_unique h_sum h_add_lim
    · -- ψ₁ in domain, ψ₂ not in domain
      -- This case shouldn't happen if we're only evaluating on domain elements
      -- But we need to handle it for linearity
      /-
      ⊢ (if hψ : ψ₁ + ψ₂ ∈ generatorDomain U_grp then generatorLimitValue U_grp (ψ₁ + ψ₂) hψ else 0) =
        (if hψ : ψ₁ ∈ generatorDomain U_grp then generatorLimitValue U_grp ψ₁ hψ else 0) +
        if hψ : ψ₂ ∈ generatorDomain U_grp then generatorLimitValue U_grp ψ₂ hψ else 0
      -/
      sorry
    · -- ψ₁ not in domain, ψ₂ in domain
      /-
      ⊢ (if hψ : ψ₁ + ψ₂ ∈ generatorDomain U_grp then generatorLimitValue U_grp (ψ₁ + ψ₂) hψ else 0) =
      (if hψ : ψ₁ ∈ generatorDomain U_grp then generatorLimitValue U_grp ψ₁ hψ else 0) +
      if hψ : ψ₂ ∈ generatorDomain U_grp then generatorLimitValue U_grp ψ₂ hψ else 0
      -/
      sorry
    · -- Neither in domain
      simp only [dif_neg hψ₁, dif_neg hψ₂]
      by_cases hψ_sum : ψ₁ + ψ₂ ∈ generatorDomain U_grp
      · -- Sum is in domain but neither summand is - contradiction with submodule
        -- Actually this can't happen: if ψ₁ + ψ₂ ∈ D(A) and ψ₂ ∉ D(A),
        -- then ψ₁ = (ψ₁ + ψ₂) - ψ₂ should be... wait, we need ψ₂ ∈ D(A) for that
        -- This case is actually possible! If neither is in domain but sum is.
        -- ⊢ (if hψ : ψ₁ + ψ₂ ∈ generatorDomain U_grp then generatorLimitValue U_grp (ψ₁ + ψ₂) hψ else 0) = 0 + 0
        sorry
      · simp only [dif_neg hψ_sum]
        norm_num
  map_smul' := by
    intro c ψ
    classical
    by_cases hψ : ψ ∈ generatorDomain U_grp
    · have hcψ : c • ψ ∈ generatorDomain U_grp := (generatorDomain U_grp).smul_mem c hψ
      simp only [dif_pos hψ, dif_pos hcψ, RingHom.id_apply]
      have h := generatorLimitValue_spec U_grp ψ hψ
      have hc := generatorLimitValue_spec U_grp (c • ψ) hcψ
      have h_smul_lim : Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (c • ψ) - c • ψ))
                                (𝓝[≠] 0)
                                (𝓝 (c • generatorLimitValue U_grp ψ hψ)) := by
        have h_eq : ∀ h : ℝ, ((I * h)⁻¹ : ℂ) • (U_grp.U h (c • ψ) - c • ψ) =
                            c • (((I * h)⁻¹ : ℂ) • (U_grp.U h ψ - ψ)) := by
          intro h
          rw [ContinuousLinearMap.map_smul, smul_sub, smul_comm]
          -- ⊢ c • (I * ↑h)⁻¹ • (U_grp.U h) ψ - (I * ↑h)⁻¹ • c • ψ = c • (I * ↑h)⁻¹ • ((U_grp.U h) ψ - ψ)
          sorry
        simp_rw [h_eq]
        exact h.const_smul c
      exact tendsto_nhds_unique hc h_smul_lim
    · by_cases hcψ : c • ψ ∈ generatorDomain U_grp
      · -- c • ψ in domain but ψ not - can happen if c = 0
        by_cases hc : c = 0
        · simp only [hc, zero_smul, dif_neg hψ, smul_zero]
          -- Need to show generatorLimitValue (0) = 0
          have h0 : (0 : H) ∈ generatorDomain U_grp := (generatorDomain U_grp).zero_mem
          have h_eq : c • ψ = 0 := by simp [hc]
          sorry -- generatorLimitValue 0 = 0
        · -- c ≠ 0 and c • ψ ∈ domain but ψ ∉ domain
          -- Then ψ = c⁻¹ • (c • ψ) should be in domain - contradiction
          exfalso
          have : ψ = c⁻¹ • (c • ψ) := by simp_all only [ne_eq, not_false_eq_true, inv_smul_smul₀]
          rw [this] at hψ
          exact hψ ((generatorDomain U_grp).smul_mem c⁻¹ hcψ)
      · simp only [dif_neg hψ, dif_neg hcψ, RingHom.id_apply, smul_zero]

/-- The generator domain is dense in H.

Proof strategy: Show that "averaged vectors" ∫₀ʰ U(t)φ dt are in D(A) for all φ,
and that these vectors span a dense subset as h → 0.
-/
theorem generatorDomain_dense : Dense (generatorDomain U_grp : Set H) := by
  sorry

/-- The generator formula holds by construction. -/
theorem generator_formula_holds (ψ : H) (hψ : ψ ∈ generatorDomain U_grp) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ - ψ))
            (𝓝[≠] 0)
            (𝓝 (generatorOp U_grp ψ)) := by
  classical
  simp only [generatorOp]-- unused dif_pos hψ
  --exact generatorLimitValue_spec U_grp ψ hψ
  /-
  oof strategy: Show that "averaged vectors" ∫₀ʰ U(t)φ dt are in D(A) for all φ,
def exponential
Type mismatch
  generatorLimitValue_spec U_grp ψ hψ
has type
  Tendsto (fun h => (I * ↑h)⁻¹ • ((U_grp.U h) ψ - ψ)) (𝓝[≠] 0) (𝓝 (generatorLimitValue U_grp ψ hψ))
but is expected to have type
  Tendsto (fun h => (I * ↑h)⁻¹ • ((U_grp.U h) ψ - ψ)) (𝓝[≠] 0)
    (𝓝
      ({ toFun := fun ψ => if hψ : ψ ∈ generatorDomain U_grp then generatorLimitValue U_grp ψ hψ else 0, map_add' := ⋯,
          map_smul' := ⋯ }
        ψ))
        -/
  sorry

/-- The domain is invariant under U(t). -/
theorem generatorDomain_invariant (t : ℝ) (ψ : H) (hψ : ψ ∈ generatorDomain U_grp) :
    U_grp.U t ψ ∈ generatorDomain U_grp := by
  sorry

/-- The generator is symmetric. -/
theorem generator_symmetric (ψ₁ ψ₂ : H)
    (hψ₁ : ψ₁ ∈ generatorDomain U_grp) (hψ₂ : ψ₂ ∈ generatorDomain U_grp) :
    ⟪generatorOp U_grp ψ₁, ψ₂⟫_ℂ = ⟪ψ₁, generatorOp U_grp ψ₂⟫_ℂ := by -- expected token
  sorry

/-- The resolvent integrals are in the domain. -/
theorem resolventIntegralPlus_in_domain (φ : H) :
    resolventIntegralPlus U_grp φ ∈ generatorDomain U_grp := by
  exact ⟨φ - I • resolventIntegralPlus U_grp φ, generator_limit_resolventIntegralPlus U_grp φ⟩

theorem resolventIntegralMinus_in_domain (φ : H) :
    resolventIntegralMinus U_grp φ ∈ generatorDomain U_grp := by
  exact ⟨φ + I • resolventIntegralMinus U_grp φ, generator_limit_resolventIntegralMinus U_grp φ⟩

/-- (A + iI)ψ₊ = φ -/
theorem resolventIntegralPlus_solves (φ : H) :
    generatorOp U_grp (resolventIntegralPlus U_grp φ) +
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
  sorry


/-- (A - iI)ψ₋ = φ -/
theorem resolventIntegralMinus_solves (φ : H) :
    generatorOp U_grp (resolventIntegralMinus U_grp φ) -
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
  sorry

/-- Range(A + iI) = H -/
theorem range_plus_i_eq_top :
    ∀ φ : H, ∃ ψ ∈ generatorDomain U_grp,
      generatorOp U_grp ψ + I • ψ = φ := by
  intro φ
  exact ⟨resolventIntegralPlus U_grp φ,
         resolventIntegralPlus_in_domain U_grp φ,
         resolventIntegralPlus_solves U_grp φ⟩

/-- Range(A - iI) = H -/
theorem range_minus_i_eq_top :
    ∀ φ : H, ∃ ψ ∈ generatorDomain U_grp,
      generatorOp U_grp ψ - I • ψ = φ := by
  intro φ
  exact ⟨resolventIntegralMinus U_grp φ,
         resolventIntegralMinus_in_domain U_grp φ,
         resolventIntegralMinus_solves U_grp φ⟩

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

theorem generatorOfUnitaryGroup_isSelfAdjoint :
    (generatorOfUnitaryGroup U_grp).IsSelfAdjoint := by
  constructor
  · -- Range(A + iI) = H
    intro φ
    obtain ⟨ψ, hψ_mem, hψ_eq⟩ := range_plus_i_eq_top U_grp φ
    exact ⟨ψ, hψ_mem, hψ_eq⟩
  · -- Range(A - iI) = H
    intro φ
    obtain ⟨ψ, hψ_mem, hψ_eq⟩ := range_minus_i_eq_top U_grp φ
    exact ⟨ψ, hψ_mem, hψ_eq⟩

end GeneratorConstruction

/-!
================================================================================
SECTION 6: AVERAGED VECTORS AND DOMAIN DENSITY
================================================================================

Alternative proof of domain density via averaged vectors.
-/

section AveragedVectors

open StonesTheorem.Resolvent

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The averaged vector ψₕ = (1/h) ∫₀ʰ U(t)φ dt. -/
noncomputable def averagedVector (h : ℝ) (hh : h ≠ 0) (φ : H) : H :=
  (h⁻¹ : ℂ) • ∫ t in Set.Ioc 0 h, U_grp.U t φ

/-- The averaged vector converges to φ as h → 0. -/
lemma averagedVector_tendsto (φ : H) :
    Tendsto (fun h : ℝ => if hh : h ≠ 0 then averagedVector U_grp h hh φ else φ)
            (𝓝[≠] 0) (𝓝 φ) := by
  sorry

/-- The averaged vector is in the domain of the generator.

Key calculation:
  (U(s) - I)(ψₕ) = (1/h) ∫₀ʰ (U(t+s) - U(t))φ dt
                 = (1/h) [∫ₛʰ⁺ˢ U(r)φ dr - ∫₀ʰ U(t)φ dt]
                 = (1/h) [∫ₕʰ⁺ˢ U(r)φ dr - ∫₀ˢ U(t)φ dt]

So (U(s)ψₕ - ψₕ)/(is) → (1/h)[U(h)φ - U(0)φ]/i = (U(h) - I)φ/(ih) as s → 0
Wait, that's not quite right either...

Actually: (U(s)ψₕ - ψₕ)/(is) = (1/(ih·s)) [∫ₕʰ⁺ˢ U(r)φ dr - ∫₀ˢ U(t)φ dt]

As s → 0: This → (1/(ih)) [U(h)φ - φ] = (U(h) - I)φ/(ih)

So Aψₕ exists and equals (U(h) - I)φ/(ih)... but that depends on h.

The point is ψₕ ∈ D(A), and as h → 0, ψₕ → φ, proving density.
-/
lemma averagedVector_in_domain (h : ℝ) (hh : h ≠ 0) (φ : H) :
    averagedVector U_grp h hh φ ∈ generatorDomain U_grp := by
  sorry

/-- Alternative proof that the domain is dense: averaged vectors span H. -/
theorem generatorDomain_dense_via_average :
    Dense (generatorDomain U_grp : Set H) := by
  rw [Metric.dense_iff]
  intro φ ε hε
  -- For small enough h, averagedVector h φ is within ε of φ
  have h_tendsto := averagedVector_tendsto U_grp φ
  rw [Metric.tendsto_nhds] at h_tendsto
  -- ... this is getting complicated. The idea is:
  -- 1. averagedVector h φ → φ as h → 0
  -- 2. Each averagedVector h φ ∈ D(A)
  -- 3. Therefore D(A) is dense
  sorry

end AveragedVectors

/-!
================================================================================
SECTION 7: CONNECTING TO STONE'S THEOREM
================================================================================

Bridge lemmas connecting this file to the main theorem files.
-/

section Bridge

open StonesTheorem.Resolvent

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The constructed generator matches the one in Resolvent.lean. -/
theorem generatorOfUnitaryGroup_eq_ofUnitaryGroup :
    generatorOfUnitaryGroup U_grp = Generator.ofUnitaryGroup U_grp := by
  -- Both are constructed the same way
  sorry

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
  sorry

/-- Integration by parts for Bochner integrals. -/
lemma integration_by_parts_Ioc
    (f : ℝ → ℂ) (g : ℝ → E) (a b : ℝ) (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (deriv f x) x)
    (hg : ∀ x ∈ Set.Icc a b, HasDerivAt g (deriv g x) x)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hf'_int : IntegrableOn (deriv f) (Set.Ioc a b))
    (hg'_int : IntegrableOn (deriv g) (Set.Ioc a b)) :
    ∫ x in Set.Ioc a b, deriv f x • g x + f x • deriv g x =
    f b • g b - f a • g a := by
  sorry

/-- Dominated convergence for Bochner integrals. -/
lemma tendsto_integral_of_dominated_convergence
    (f : ℕ → ℝ → E) (g : ℝ → E) (bound : ℝ → ℝ)
    (S : Set ℝ)
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict S))
    (hbound : ∀ n, ∀ᵐ x ∂(volume.restrict S), ‖f n x‖ ≤ bound x)
    (hbound_int : Integrable bound (volume.restrict S))
    (hf_tendsto : ∀ᵐ x ∂(volume.restrict S), Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x in S, f n x) atTop (𝓝 (∫ x in S, g x)) := by
  sorry

/-- Continuity of the integral with respect to a parameter. -/
lemma continuous_integral_of_continuous
    (f : ℝ → ℝ → E) (S : Set ℝ)
    (hf_cont : Continuous (Function.uncurry f))
    (hf_int : ∀ t, IntegrableOn (f t) S) :
    Continuous (fun t => ∫ s in S, f t s) := by
  sorry

/-- The fundamental theorem of calculus for Bochner integrals. -/
lemma ftc_Ioc (f : ℝ → E) (a b : ℝ) (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b)) :
    HasDerivAt (fun x => ∫ t in Set.Ioc a x, f t) (f b) b := by
  sorry

end Appendix

end StonesTheorem.Bochner
