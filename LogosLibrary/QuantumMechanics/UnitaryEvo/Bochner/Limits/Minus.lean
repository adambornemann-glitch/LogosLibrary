/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Bochner/Limits/Minus.lean
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner.Limits.Helpers

/-!
# Generator Limit for R₋

This file proves that the resolvent integral `R₋(φ) = i ∫₀^∞ e^{-t} U(-t)φ dt`
lies in the generator domain and satisfies `A(R₋φ) = φ + iR₋φ`.

## Main results

* `unitary_shift_resolventIntegralMinus`: formula for `U(h)R₋(φ) - R₋(φ)` when `h > 0`
* `unitary_shift_resolventIntegralMinus_neg`: formula when `h < 0`
* `generator_limit_resolventIntegralMinus`: the limit exists and equals `φ + iR₋φ`

## Tags

generator, resolvent, limit
-/

namespace QuantumMechanics.Bochner

open MeasureTheory Measure Filter Topology Complex QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section GeneratorLimitMinus

variable (U_grp : OneParameterUnitaryGroup (H := H))

lemma unitary_shift_resolventIntegralMinus (φ : H) (h : ℝ) (hh : h > 0) :
    U_grp.U h (resolventIntegralMinus U_grp φ) - resolventIntegralMinus U_grp φ =
    I • (Real.exp (-h) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) +
    I • ((Real.exp (-h) - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) := by
  unfold resolventIntegralMinus
  have h_int := integrable_exp_neg_unitary_neg U_grp φ
  rw [ContinuousLinearMap.map_smul]
  have h_comm : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) =
                ∫ t in Set.Ici 0, U_grp.U h (Real.exp (-t) • U_grp.U (-t) φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  rw [h_comm]
  have h_shift : ∀ t, U_grp.U h (Real.exp (-t) • U_grp.U (-t) φ) =
                      Real.exp (-t) • U_grp.U (h - t) φ := by
    intro t
    have hlaw' : U_grp.U h ∘L U_grp.U (-t) = U_grp.U (h - t) := by
      rw [show h - t = h + (-t) from sub_eq_add_neg h t]; exact Eq.symm (U_grp.group_law h (-t))
    rw [← hlaw', ContinuousLinearMap.comp_apply]
    exact map_smul (U_grp.U h) _ _
  simp_rw [h_shift]
  have h_exp : ∀ t, Real.exp (-t) • U_grp.U (h - t) φ =
                    Real.exp (-h) • (Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ) := by
    intro t
    rw [← smul_assoc, smul_eq_mul, ← Real.exp_add]
    congr 1
    · ring_nf
    · · congr 1; abel_nf
  simp_rw [h_exp]
  have h_smul_comm : ∫ t in Set.Ici 0, Real.exp (-h) • (Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ) =
                     Real.exp (-h) • ∫ t in Set.Ici 0, Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ := by
    exact integral_smul (Real.exp (-h)) fun a => Real.exp (-(a - h)) • (U_grp.U (-(a - h))) φ
  rw [h_smul_comm]
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
  set X := ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ with hX_def
  set Y := ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ with hY_def
  calc I • (Real.exp (-h) • X + Real.exp (-h) • Y) - I • Y
      = I • Real.exp (-h) • X + I • Real.exp (-h) • Y - I • Y := by rw [smul_add]
    _ = I • Real.exp (-h) • X + (I • Real.exp (-h) • Y - I • Y) := by abel
    _ = I • Real.exp (-h) • X + I • (Real.exp (-h) • Y - Y) := by rw [← smul_sub]
    _ = I • Real.exp (-h) • X + I • ((Real.exp (-h) - 1) • Y) := by rw [sub_smul, one_smul]
    _ = I • (Real.exp (-h) • X) + I • ((Real.exp (-h) - 1) • Y) := by rw [hX_def]

lemma unitary_shift_resolventIntegralMinus_neg (φ : H) (h : ℝ) (hh : h < 0) :
    U_grp.U h (resolventIntegralMinus U_grp φ) - resolventIntegralMinus U_grp φ =
    I • ((Real.exp (-h) - 1) • ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ) -
    I • ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ := by
  unfold resolventIntegralMinus
  have h_int := integrable_exp_neg_unitary_neg U_grp φ
  rw [ContinuousLinearMap.map_smul]
  have h_comm : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) =
                ∫ t in Set.Ici 0, U_grp.U h (Real.exp (-t) • U_grp.U (-t) φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  rw [h_comm]
  have h_shift : ∀ t, U_grp.U h (Real.exp (-t) • U_grp.U (-t) φ) =
                      Real.exp (-t) • U_grp.U (h - t) φ := by
    intro t
    have hlaw : U_grp.U h ∘L U_grp.U (-t) = U_grp.U (h - t) := by
      rw [show h - t = h + (-t) from sub_eq_add_neg h t]; exact Eq.symm (U_grp.group_law h (-t))
    rw [← hlaw, ContinuousLinearMap.comp_apply]
    exact map_smul (U_grp.U h) _ _
  simp_rw [h_shift]
  have h_exp : ∀ t, Real.exp (-t) • U_grp.U (h - t) φ =
                    Real.exp (-h) • (Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ) := by
    intro t
    rw [← smul_assoc, smul_eq_mul, ← Real.exp_add]
    congr 1
    · ring_nf
    · congr 1; abel_nf
  simp_rw [h_exp]
  have h_smul_comm : ∫ t in Set.Ici 0, Real.exp (-h) • (Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ) =
                     Real.exp (-h) • ∫ t in Set.Ici 0, Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ := by
    exact integral_smul (Real.exp (-h)) fun a => Real.exp (-(a - h)) • (U_grp.U (-(a - h))) φ
  rw [h_smul_comm]
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
  set X := ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ with hX_def
  set Y := ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ with hY_def
  rw [smul_add]
  calc  I • Real.exp (-h) • Y - (I • X + I • Y)
      = I • Real.exp (-h) • Y - I • X - I • Y := by exact sub_add_eq_sub_sub (I • Real.exp (-h) • Y) (I • X) (I • Y)
    _ = I • Real.exp (-h) • Y - I • Y - I • X := by abel
    _ = I • (Real.exp (-h) • Y - Y) - I • X := by rw [← smul_sub]
    _ = I • ((Real.exp (-h) - 1) • Y) - I • X := by rw [sub_smul, one_smul]
    _ = I • (Real.exp (-h) - 1) • Y - I • X := by rfl

lemma generator_limit_resolventIntegralMinus (φ : H) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) -
                                              resolventIntegralMinus U_grp φ))
            (𝓝[≠] 0)
            (𝓝 (φ + I • resolventIntegralMinus U_grp φ)) := by
  have h_target : φ + I • resolventIntegralMinus U_grp φ =
                  φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ := by
    unfold resolventIntegralMinus
    rw [smul_smul, I_mul_I, neg_one_smul, sub_eq_add_neg]
  rw [h_target]
  have h_scalar : ∀ h : ℝ, h ≠ 0 → ((I * (h : ℂ))⁻¹ * I : ℂ) = (h : ℂ)⁻¹ := by
    intro h _
    calc ((I * (h : ℂ))⁻¹ * I : ℂ)
        = (h : ℂ)⁻¹ * I⁻¹ * I := by rw [mul_inv_rev]
      _ = (h : ℂ)⁻¹ * (I⁻¹ * I) := by rw [mul_assoc]
      _ = (h : ℂ)⁻¹ * 1 := by rw [inv_mul_cancel₀ I_ne_zero]
      _ = (h : ℂ)⁻¹ := by rw [mul_one]
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
  · have h_eq : ∀ h : ℝ, h > 0 → ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) -
                                                   resolventIntegralMinus U_grp φ) =
                         ((h : ℂ)⁻¹ • Real.exp (-h) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) +
                         ((h : ℂ)⁻¹ • (Real.exp (-h) - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) := by
      intro h hh
      rw [unitary_shift_resolventIntegralMinus U_grp φ h hh]
      rw [smul_add, smul_smul, smul_smul, h_scalar h (ne_of_gt hh)]
    apply Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact (h_eq h hh).symm
    rw [show φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ =
            φ + (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) by abel]
    apply Tendsto.add
    · have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U (-t) φ) :=
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
    · have he : Tendsto (fun h : ℝ => (Real.exp (-h) - 1) / h) (𝓝[>] 0) (𝓝 (-1)) := by
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
  · have h_eq : ∀ h : ℝ, h < 0 → ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) -
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
    rw [show φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ =
            (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) + φ by abel]
    apply Tendsto.add
    · have he : Tendsto (fun h : ℝ => (Real.exp (-h) - 1) / h) (𝓝[<] 0) (𝓝 (-1)) := by
        have tendsto_neg_Iio : Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝[>] 0) := by
          rw [tendsto_nhdsWithin_iff]
          constructor
          · have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
              convert (continuous_neg (G := ℝ)).tendsto 0 using 1
              simp
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with h hh
            simp only [Set.mem_Ioi]
            exact Left.neg_pos_iff.mpr hh
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
        rfl
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
    · have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U (-t) φ) :=
        ((Real.continuous_exp.comp continuous_neg).smul
         ((U_grp.strong_continuous φ).comp continuous_neg))
      have h_f0 : Real.exp (-(0 : ℝ)) • U_grp.U (-(0 : ℝ)) φ = φ := by
        simp only [neg_zero, Real.exp_zero, one_smul]
        rw [U_grp.identity]
        simp only [ContinuousLinearMap.id_apply]
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
      have tendsto_neg_Iio : Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝[>] 0) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
            convert (continuous_neg (G := ℝ)).tendsto 0 using 1
            simp
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with h hh
          simp only [Set.mem_Ioi]
          exact Left.neg_pos_iff.mpr hh
      have h_comp := h_avg.comp tendsto_neg_Iio
      apply Tendsto.congr' _ h_comp
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [Function.comp_apply]
      rw [show -(h : ℂ)⁻¹ = ((-h) : ℂ)⁻¹ from by rw [@neg_inv]]
      simp only [ofReal_neg, inv_neg, neg_smul]

end GeneratorLimitMinus

end QuantumMechanics.Bochner
