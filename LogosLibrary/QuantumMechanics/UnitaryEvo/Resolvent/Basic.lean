/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner

/-!
# Basic Definitions for Resolvent Theory

This file provides foundational definitions and tools for resolvent theory:
* Types for spectral regions (`OffRealAxis`, `UpperHalfPlane`, `LowerHalfPlane`)
* Neumann series machinery for inverting `(1 - T)` when `‖T‖ < 1`

## Main definitions

* `OffRealAxis`: Complex numbers with nonzero imaginary part
* `UpperHalfPlane`: Complex numbers with positive imaginary part
* `LowerHalfPlane`: Complex numbers with negative imaginary part
* `neumannPartialSum`: Partial sums `∑_{k<n} Tᵏ`
* `neumannSeries`: The limit `∑_{k=0}^∞ Tᵏ` for `‖T‖ < 1`

## Main statements

* `neumannSeries_mul_left`: `(1 - T) * neumannSeries T = 1`
* `neumannSeries_mul_right`: `neumannSeries T * (1 - T) = 1`
* `isUnit_one_sub`: `(1 - T)` is a unit when `‖T‖ < 1`
* `neumannSeries_hasSum`: The series `∑ Tⁿ` converges to `neumannSeries T`

## References

* [Kato, *Perturbation Theory for Linear Operators*][kato1995], Section IV.1
-/

namespace QuantumMechanics.Resolvent

open InnerProductSpace MeasureTheory Complex Filter Topology

/-! ## Spectral Region Types -/

/-- Complex numbers with nonzero imaginary part (complement of the real axis). -/
def OffRealAxis : Type := {z : ℂ // z.im ≠ 0}

/-- Complex numbers with positive imaginary part. -/
def UpperHalfPlane : Type := {z : ℂ // 0 < z.im}

/-- Complex numbers with negative imaginary part. -/
def LowerHalfPlane : Type := {z : ℂ // z.im < 0}

instance : Coe UpperHalfPlane OffRealAxis where
  coe z := ⟨z.val, ne_of_gt z.property⟩

instance : Coe LowerHalfPlane OffRealAxis where
  coe z := ⟨z.val, ne_of_lt z.property⟩

/-! ## Neumann Series -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma opNorm_pow_le (T : E →L[ℂ] E) (n : ℕ) : ‖T^n‖ ≤ ‖T‖^n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    calc ‖T^(n+1)‖
        = ‖T^n * T‖ := by rw [pow_succ]
      _ ≤ ‖T^n‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖T‖^n * ‖T‖ := by
          apply mul_le_mul_of_nonneg_right ih (norm_nonneg _)
      _ = ‖T‖^(n+1) := by rw [pow_succ]



lemma opNorm_pow_tendsto_zero (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    Tendsto (fun n => ‖T^n‖) atTop (𝓝 0) := by
  have h_geom : Tendsto (fun n => ‖T‖^n) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    rw [norm_norm]
    exact hT
  have h_bound : ∀ n, ‖T^n‖ ≤ ‖T‖^n := fun n => opNorm_pow_le T n
  have h_nonneg : ∀ n, 0 ≤ ‖T^n‖ := fun n => norm_nonneg _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_geom h_nonneg h_bound

/-- Partial sums of the Neumann series `∑_{k<n} Tᵏ`. -/
noncomputable def neumannPartialSum (T : E →L[ℂ] E) (n : ℕ) : E →L[ℂ] E :=
  Finset.sum (Finset.range n) (fun k => T^k)

lemma neumannPartialSum_mul (T : E →L[ℂ] E) (n : ℕ) :
    (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n =
    ContinuousLinearMap.id ℂ E - T^n := by
  induction n with
  | zero =>
    simp only [neumannPartialSum, Finset.range_zero, Finset.sum_empty, pow_zero]
    simp only [mul_zero]
    ext x : 1
    simp_all only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_sub',
      ContinuousLinearMap.coe_id', Pi.sub_apply, id_eq, ContinuousLinearMap.one_apply, sub_self]
  | succ n ih =>
    simp only [neumannPartialSum] at ih ⊢
    rw [Finset.sum_range_succ]
    rw [mul_add]
    rw [ih]
    have h_id_eq : ContinuousLinearMap.id ℂ E = (1 : E →L[ℂ] E) := rfl
    rw [h_id_eq]
    rw [sub_mul, one_mul]
    rw [← pow_succ']
    abel

lemma neumannPartialSum_cauchy (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    CauchySeq (neumannPartialSum T) := by
  apply cauchySeq_of_summable_dist
  have h_bound : ∀ n, dist (neumannPartialSum T n) (neumannPartialSum T (n + 1)) ≤ ‖T‖^n := by
    intro n
    simp only [neumannPartialSum, dist_eq_norm, Finset.sum_range_succ]
    rw [← norm_neg, neg_sub, add_sub_cancel_left]
    exact opNorm_pow_le T n
  apply Summable.of_nonneg_of_le
  · intro n; exact dist_nonneg
  · exact h_bound
  · exact summable_geometric_of_lt_one (norm_nonneg _) hT

/-- The Neumann series `∑_{k=0}^∞ Tᵏ` for `‖T‖ < 1`. -/
noncomputable def neumannSeries (T : E →L[ℂ] E) (_ : ‖T‖ < 1) : E →L[ℂ] E :=
  limUnder atTop (neumannPartialSum T)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma neumannSeries_mul_left (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    (ContinuousLinearMap.id ℂ E - T) * neumannSeries T hT = ContinuousLinearMap.id ℂ E := by
  have h_lim : Tendsto (neumannPartialSum T) atTop (𝓝 (neumannSeries T hT)) := by
    exact (neumannPartialSum_cauchy T hT).tendsto_limUnder
  have h_mul_lim : Tendsto (fun n => (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n)
      atTop (𝓝 ((ContinuousLinearMap.id ℂ E - T) * neumannSeries T hT)) := by
    exact Tendsto.const_mul (ContinuousLinearMap.id ℂ E - T) h_lim
  have h_eq : ∀ n, (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n =
      ContinuousLinearMap.id ℂ E - T^n := neumannPartialSum_mul T
  have h_pow_lim : Tendsto (fun n => T^n) atTop (𝓝 0) := by
    have h := opNorm_pow_tendsto_zero T hT
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h
  have h_sub_lim : Tendsto (fun n => ContinuousLinearMap.id ℂ E - T^n) atTop
      (𝓝 (ContinuousLinearMap.id ℂ E - 0)) := by
    exact Tendsto.const_sub (ContinuousLinearMap.id ℂ E) h_pow_lim
  simp only [sub_zero] at h_sub_lim
  have h_eq_lim : Tendsto (fun n => (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n)
      atTop (𝓝 (ContinuousLinearMap.id ℂ E)) := by
    simp only [h_eq]
    exact h_sub_lim
  exact tendsto_nhds_unique h_mul_lim h_eq_lim

lemma neumannSeries_mul_right (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    neumannSeries T hT * (ContinuousLinearMap.id ℂ E - T) = ContinuousLinearMap.id ℂ E := by
  have h_telescope : ∀ n, neumannPartialSum T n * (ContinuousLinearMap.id ℂ E - T) =
      ContinuousLinearMap.id ℂ E - T^n := by
    intro n
    induction n with
    | zero =>
      simp only [neumannPartialSum, Finset.range_zero, Finset.sum_empty, pow_zero]
      simp only [zero_mul]
      ext x : 1
      simp_all only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_sub',
        ContinuousLinearMap.coe_id', Pi.sub_apply, id_eq, ContinuousLinearMap.one_apply, sub_self]
    | succ n ih =>
      simp only [neumannPartialSum] at ih ⊢
      rw [Finset.sum_range_succ]
      rw [add_mul]
      rw [ih]
      have h_id_eq : ContinuousLinearMap.id ℂ E = (1 : E →L[ℂ] E) := rfl
      rw [h_id_eq]
      rw [mul_sub, mul_one]
      rw [← pow_succ]
      abel
  have h_lim : Tendsto (neumannPartialSum T) atTop (𝓝 (neumannSeries T hT)) :=
    (neumannPartialSum_cauchy T hT).tendsto_limUnder
  have h_mul_lim : Tendsto (fun n => neumannPartialSum T n * (ContinuousLinearMap.id ℂ E - T))
      atTop (𝓝 (neumannSeries T hT * (ContinuousLinearMap.id ℂ E - T))) := by
    exact Tendsto.mul_const (ContinuousLinearMap.id ℂ E - T) h_lim
  have h_pow_lim : Tendsto (fun n => T^n) atTop (𝓝 0) := by
    have h := opNorm_pow_tendsto_zero T hT
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h
  have h_sub_lim : Tendsto (fun n => ContinuousLinearMap.id ℂ E - T^n) atTop
      (𝓝 (ContinuousLinearMap.id ℂ E)) := by
    have := Tendsto.const_sub (ContinuousLinearMap.id ℂ E) h_pow_lim
    simp only [sub_zero] at this
    exact this
  have h_eq_lim : Tendsto (fun n => neumannPartialSum T n * (ContinuousLinearMap.id ℂ E - T))
      atTop (𝓝 (ContinuousLinearMap.id ℂ E)) := by
    simp only [h_telescope]
    exact h_sub_lim
  exact tendsto_nhds_unique h_mul_lim h_eq_lim

lemma isUnit_one_sub (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    IsUnit (ContinuousLinearMap.id ℂ E - T) := by
  refine ⟨⟨ContinuousLinearMap.id ℂ E - T, neumannSeries T hT, ?_, ?_⟩, rfl⟩
  · exact neumannSeries_mul_left T hT
  · exact neumannSeries_mul_right T hT

theorem neumannSeries_summable (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    Summable (fun n => T^n) := by
  have h_geom : Summable (fun n => ‖T‖^n) := summable_geometric_of_lt_one (norm_nonneg _) hT
  apply Summable.of_norm_bounded_eventually
  · exact h_geom
  · filter_upwards with n
    exact opNorm_pow_le T n

theorem tsum_eq_neumannSeries (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    ∑' n, T^n = neumannSeries T hT := by
  have h_summable := neumannSeries_summable T hT
  have h_cauchy := neumannPartialSum_cauchy T hT
  have h_tendsto_neumann : Tendsto (neumannPartialSum T) atTop (𝓝 (neumannSeries T hT)) :=
    h_cauchy.tendsto_limUnder
  have h_tendsto_tsum : Tendsto (fun n => ∑ i ∈ Finset.range n, T^i) atTop (𝓝 (∑' n, T^n)) :=
    h_summable.hasSum.tendsto_sum_nat
  have h_eq_partial : (fun n => ∑ i ∈ Finset.range n, T^i) = neumannPartialSum T := by
    ext n
    simp only [neumannPartialSum]
  rw [h_eq_partial] at h_tendsto_tsum
  exact tendsto_nhds_unique h_tendsto_tsum h_tendsto_neumann

theorem neumannSeries_hasSum (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    HasSum (fun n => T^n) (neumannSeries T hT) := by
  rw [← tsum_eq_neumannSeries T hT]
  exact (neumannSeries_summable T hT).hasSum

/-! ## Auxiliary Lemmas -/

lemma im_ne_zero_of_near {z₀ : ℂ} (_ : z₀.im ≠ 0) {z : ℂ}
    (hz : ‖z - z₀‖ < |z₀.im|) : z.im ≠ 0 := by
  have h_im_diff : |z.im - z₀.im| ≤ ‖z - z₀‖ := abs_im_le_norm (z - z₀)
  have h_im_close : |z.im - z₀.im| < |z₀.im| := lt_of_le_of_lt h_im_diff hz
  intro hz_eq
  rw [hz_eq, zero_sub, abs_neg] at h_im_close
  exact lt_irrefl _ h_im_close

end QuantumMechanics.Resolvent
