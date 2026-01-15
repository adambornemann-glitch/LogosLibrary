/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Bochner Integration for Exponentially Decaying Functions

This file provides foundational lemmas for Bochner integration of exponentially
decaying functions. These are the analytical tools needed for the resolvent
integral construction in Stone's theorem.

## Main results

* `integrableOn_exp_neg`: `e^{-t}` is integrable on `[0, ∞)`
* `integral_exp_neg_eq_one`: `∫₀^∞ e^{-t} dt = 1`
* `integrable_exp_decay_continuous`: `e^{-t} • f(t)` is integrable if `f` is bounded
* `norm_integral_exp_decay_le`: `‖∫₀^∞ e^{-t} • f(t) dt‖ ≤ C` if `‖f(t)‖ ≤ C`
* `tendsto_integral_Ioc_exp_decay`: monotone convergence for exponentially decaying integrands
* `hasDerivAt_integral_of_exp_decay`: differentiation under the integral sign

## Implementation notes

The exponential weight `e^{-t}` ensures integrability. The parameter `λ = 1` is
arbitrary; any `λ > 0` works. This corresponds to evaluating resolvents at `z = ±i`.

## Tags

Bochner integral, exponential decay, improper integral
-/

namespace QuantumMechanics.Bochner

open MeasureTheory Measure Filter Topology Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


section BasicBochner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]


lemma integral_exp_neg_Ioc (n : ℕ) : ∫ x in (0 : ℝ)..n, Real.exp (-x) = 1 - Real.exp (-n) := by
  by_cases hn : (n : ℝ) ≤ 0
  · have hn' : n = 0 := Nat.cast_eq_zero.mp (le_antisymm hn (Nat.cast_nonneg n))
    simp [hn', intervalIntegral.integral_same]
  · push_neg at hn
    have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) n, HasDerivAt (fun t => -Real.exp (-t)) (Real.exp (-x)) x := by
      intro x _
      have h1 : HasDerivAt (fun t => -t) (-1) x := hasDerivAt_neg x
      have h2 : HasDerivAt Real.exp (Real.exp (-x)) (-x) := Real.hasDerivAt_exp (-x)
      convert (h2.comp x h1).neg using 1
      ring
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hn)
            ((Real.continuous_exp.comp continuous_neg).continuousOn.neg)
            (fun x hx => hderiv x hx)
            ((Real.continuous_exp.comp continuous_neg).intervalIntegrable 0 n) using 1
    simp [Real.exp_zero]; ring


lemma integrableOn_exp_neg : IntegrableOn (fun t => Real.exp (-t)) (Set.Ici 0) volume := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (ι := ℕ) (l := atTop)
        (b := fun n => (n : ℝ)) 1 0 ?_ ?_ ?_
  · intro i
    exact (Real.continuous_exp.comp continuous_neg).integrableOn_Ioc
  · exact tendsto_natCast_atTop_atTop
  · filter_upwards with n
    simp_rw [fun x => Real.norm_of_nonneg (le_of_lt (Real.exp_pos (-x)))]
    calc ∫ x in (0 : ℝ)..n, Real.exp (-x)
        = 1 - Real.exp (-n) := integral_exp_neg_Ioc n
      _ ≤ 1 := by linarith [Real.exp_pos (-n : ℝ)]


lemma integral_exp_neg_eq_one : ∫ t in Set.Ici (0 : ℝ), Real.exp (-t) = 1 := by
  rw [integral_Ici_eq_integral_Ioi]
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
      (f := fun t => -Real.exp (-t)) (m := 0)]
  · simp [Real.exp_zero]
  · intro x _
    have h1 : HasDerivAt (fun t => -t) (-1) x := hasDerivAt_neg x
    have h2 : HasDerivAt Real.exp (Real.exp (-x)) (-x) := Real.hasDerivAt_exp (-x)
    convert (h2.comp x h1).neg using 1; ring
  · exact integrableOn_exp_neg.mono_set Set.Ioi_subset_Ici_self
  · convert (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).neg using 1; simp


lemma integrableOn_exp_neg_Ioi : IntegrableOn (fun t => Real.exp (-t)) (Set.Ioi 0) volume :=
  integrableOn_exp_neg.mono_set Set.Ioi_subset_Ici_self

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma integrable_exp_decay_continuous
    (f : ℝ → E) (hf_cont : Continuous f)
    (C : ℝ) (hC : ∀ t ≥ 0, ‖f t‖ ≤ C) :
    IntegrableOn (fun t => Real.exp (-t) • f t) (Set.Ici 0) volume := by
  set M := max |C| 1 with hM_def
  have hM_pos : 0 < M := lt_max_of_lt_right one_pos
  have hM_ge : |C| ≤ M := le_max_left _ _
  have h_exp_int : IntegrableOn (fun t => Real.exp (-t)) (Set.Ici 0) volume :=
  integrableOn_exp_neg

  have h_bound_int : IntegrableOn (fun t => M * Real.exp (-t)) (Set.Ici 0) volume :=
    h_exp_int.const_mul M
  have h_meas : AEStronglyMeasurable (fun t => Real.exp (-t) • f t)
                                      (volume.restrict (Set.Ici 0)) := by
    apply AEStronglyMeasurable.smul
    · exact (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable.restrict
    · exact hf_cont.aestronglyMeasurable.restrict
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
  exact Integrable.mono' h_bound_int h_meas h_bound


lemma norm_integral_exp_decay_le
    (f : ℝ → E) (hf_cont : Continuous f)
    (C : ℝ) (hC : ∀ t ≥ 0, ‖f t‖ ≤ C) (_ : 0 ≤ C) :
    ‖∫ t in Set.Ici 0, Real.exp (-t) • f t‖ ≤ C := by
  have h_integrand_int : IntegrableOn (fun t => Real.exp (-t) • f t) (Set.Ici 0) volume :=
    integrable_exp_decay_continuous f hf_cont C hC
  have h_exp_int : IntegrableOn (fun t => Real.exp (-t)) (Set.Ici 0) volume :=
    integrableOn_exp_neg
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
  set M := max C 0 with hM_def
  have hM_nonneg : 0 ≤ M := le_max_right _ _
  have h_norm_int : IntegrableOn (fun t => M * Real.exp (-t)) (Set.Ioi 0) volume := by
    have h_exp : IntegrableOn (fun t => Real.exp (-t)) (Set.Ioi 0) volume :=
      integrableOn_exp_neg_Ioi
    exact h_exp.const_mul M
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
      convert h5 using 1 <;> ring_nf ; rfl
    have h_int : IntegrableOn (fun t => M * Real.exp (-t)) (Set.Ioi T) volume :=
      h_norm_int.mono_set (Set.Ioi_subset_Ioi hT)
    have h_tend : Tendsto (fun t => -M * Real.exp (-t)) atTop (𝓝 0) := by
      have : Tendsto (fun t => -M * Real.exp (-t)) atTop (𝓝 (-M * 0)) := by
        apply Tendsto.const_mul
        exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
      simp only [mul_zero] at this
      exact this
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (a := T) (f := fun t => -M * Real.exp (-t)) (m := 0)
        h_deriv h_int h_tend]
    ring
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

lemma hasDerivAt_integral_of_exp_decay
    (f : ℝ → ℝ → E)
    (hf_cont : Continuous (Function.uncurry f))
    (hf_deriv : ∀ t s, HasDerivAt (f · s) (deriv (f · s) t) t)
    (hf'_cont : ∀ t, Continuous (fun s => deriv (f · s) t))
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
    exact integrableOn_exp_neg.const_mul M
  case hF_deriv =>
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s _ τ _
    exact (hf_deriv τ s).const_smul (Real.exp (-s))

end BasicBochner

section Appendix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma fubini_Ioc (f : ℝ → ℝ → E) (a b c d : ℝ)
    (hf : Integrable (Function.uncurry f) ((volume.restrict (Set.Ioc a b)).prod
                                           (volume.restrict (Set.Ioc c d)))) :
    ∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d, f x y =
    ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, f x y := by
  exact MeasureTheory.integral_integral_swap hf

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

end QuantumMechanics.Bochner
