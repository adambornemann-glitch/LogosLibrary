/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner.Limits.Helpers

/-!
# Generator Limit for R₊

This file proves that the resolvent integral `R₊(φ) = (-i) ∫₀^∞ e^{-t} U(t)φ dt`
lies in the generator domain and satisfies `A(R₊φ) = φ - iR₊φ`.

## Main results

* `unitary_shift_resolventIntegralPlus`: formula for `U(h)R₊(φ) - R₊(φ)` when `h > 0`
* `unitary_shift_resolventIntegralPlus_neg`: formula when `h < 0`
* `generator_limit_resolventIntegralPlus`: the limit exists and equals `φ - iR₊φ`

## Tags

generator, resolvent, limit
-/

namespace QuantumMechanics.Bochner

open MeasureTheory Measure Filter Topology Complex QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section GeneratorLimitPlus

variable (U_grp : OneParameterUnitaryGroup (H := H))

lemma unitary_shift_resolventIntegralPlus (φ : H) (h : ℝ) (hh : h > 0) :
    U_grp.U h (resolventIntegralPlus U_grp φ) - resolventIntegralPlus U_grp φ =
    (-I) • ((Real.exp h - 1) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) -
    (-I) • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ := by
  unfold resolventIntegralPlus
  rw [ContinuousLinearMap.map_smul]
  have h_int := integrable_exp_neg_unitary U_grp φ
  have h_comm : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) =
              ∫ t in Set.Ici 0, U_grp.U h (Real.exp (-t) • U_grp.U t φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  rw [h_comm]
  have h_shift : ∀ t, U_grp.U h (Real.exp (-t) • U_grp.U t φ) =
                      Real.exp (-t) • U_grp.U (t + h) φ := by
    intro t
    have := U_grp.group_law h t
    rw [add_comm] at this
    rw [this]
    exact ContinuousLinearMap.map_smul_of_tower (U_grp.U h) (Real.exp (-t)) ((U_grp.U t) φ)
  simp_rw [h_shift]
  have h_exp : ∀ t, Real.exp (-t) • U_grp.U (t + h) φ =
                  Real.exp h • (Real.exp (-(t + h)) • U_grp.U (t + h) φ) := by
    intro t
    rw [← smul_assoc]
    congr 1
    rw [smul_eq_mul, ← Real.exp_add]
    congr 1
    ring
  simp_rw [h_exp]
  rw [integral_smul]
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
  set X := ∫ s in Set.Ici h, Real.exp (-s) • U_grp.U s φ with hX_def
  set Y := ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ with hY_def
  rw [smul_add]
  calc -I • Real.exp h • X - (-I • Y + -I • X)
      = -I • Real.exp h • X - -I • X - -I • Y := by abel
    _ = -I • (Real.exp h • X - X) - -I • Y := by rw [← smul_sub]
    _ = -I • ((Real.exp h - 1) • X) - -I • Y := by rw [sub_smul, one_smul]
    _ = -I • (Real.exp h - 1) • X - -I • Y := by rw [← h_subst]

lemma unitary_shift_resolventIntegralPlus_neg (φ : H) (h : ℝ) (hh : h < 0) :
    U_grp.U h (resolventIntegralPlus U_grp φ) - resolventIntegralPlus U_grp φ =
    (-I) • (Real.exp h • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ) +
    (-I) • ((Real.exp h - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) := by
  unfold resolventIntegralPlus
  have h_int := integrable_exp_neg_unitary U_grp φ
  rw [ContinuousLinearMap.map_smul]
  have h_comm : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) =
                ∫ t in Set.Ici 0, U_grp.U h (Real.exp (-t) • U_grp.U t φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  rw [h_comm]
  have h_shift : ∀ t, U_grp.U h (Real.exp (-t) • U_grp.U t φ) =
                      Real.exp (-t) • U_grp.U (t + h) φ := by
    intro t
    rw [ContinuousLinearMap.map_smul_of_tower]
    congr 1
    have := U_grp.group_law h t
    rw [add_comm] at this
    exact congrFun (congrArg DFunLike.coe this).symm φ
  simp_rw [h_shift]
  have h_exp : ∀ t, Real.exp (-t) • U_grp.U (t + h) φ =
                    Real.exp h • (Real.exp (-(t + h)) • U_grp.U (t + h) φ) := by
    intro t
    rw [← smul_assoc, smul_eq_mul, ← Real.exp_add]
    congr 1
    ring_nf
  simp_rw [h_exp]
  have h_smul_comm : ∫ t in Set.Ici 0, Real.exp h • (Real.exp (-(t + h)) • U_grp.U (t + h) φ) =
                     Real.exp h • ∫ t in Set.Ici 0, Real.exp (-(t + h)) • U_grp.U (t + h) φ := by
    rw [@integral_smul]
  rw [h_smul_comm]
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
  set X := ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ with hX_def
  set Y := ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ with hY_def
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
  calc -I • (Real.exp h • X + Real.exp h • Y) - -I • Y
      = -I • Real.exp h • X + -I • Real.exp h • Y - -I • Y := by rw [smul_add]
    _ = -I • Real.exp h • X + (-I • Real.exp h • Y - -I • Y) := by abel
    _ = -I • Real.exp h • X + -I • (Real.exp h • Y - Y) := by rw [← smul_sub]
    _ = -I • Real.exp h • X + -I • ((Real.exp h - 1) • Y) := by rw [sub_smul, one_smul]
    _ = -I • (Real.exp h • X) + -I • ((Real.exp h - 1) • Y) := by rw [hX_def]

lemma generator_limit_resolventIntegralPlus (φ : H) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
                                              resolventIntegralPlus U_grp φ))
            (𝓝[≠] 0)
            (𝓝 (φ - I • resolventIntegralPlus U_grp φ)) := by
  have h_target : φ - I • resolventIntegralPlus U_grp φ =
                  φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ := by
    unfold resolventIntegralPlus
    rw [smul_smul, mul_neg, I_mul_I, neg_neg, one_smul]
  rw [h_target]
  have h_scalar : ∀ h : ℝ, h ≠ 0 → ((I * (h : ℂ))⁻¹ * (-I) : ℂ) = -(h : ℂ)⁻¹ := by
    intro h _
    calc ((I * (h : ℂ))⁻¹ * (-I) : ℂ)
        = (h : ℂ)⁻¹ * I⁻¹ * (-I) := by rw [mul_inv_rev]
      _ = (h : ℂ)⁻¹ * (I⁻¹ * (-I)) := by rw [mul_assoc]
      _ = (h : ℂ)⁻¹ * (-(I⁻¹ * I)) := by rw [mul_neg]
      _ = (h : ℂ)⁻¹ * (-1) := by rw [inv_mul_cancel₀ I_ne_zero]
      _ = -(h : ℂ)⁻¹ := by rw [mul_neg_one]
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
  · have h_eq : ∀ h : ℝ, h > 0 → ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
                                                   resolventIntegralPlus U_grp φ) =
                         (-(h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) -
                         (-(h : ℂ)⁻¹ • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ) := by
      intro h hh
      rw [unitary_shift_resolventIntegralPlus U_grp φ h hh]
      rw [smul_sub, smul_smul, smul_smul, h_scalar h (ne_of_gt hh)]
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
    rw [show φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ =
            -(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) + φ by abel]
    apply Tendsto.add
    · apply Tendsto.neg
      have he : Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[>] 0) (𝓝 1) :=
        tendsto_exp_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
      have hi : Tendsto (fun h : ℝ => ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ)
                        (𝓝[>] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) :=
        (tendsto_integral_Ici_exp_unitary U_grp φ).mono_left nhdsWithin_le_nhds
      have he_cplx : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ)) (𝓝[>] 0) (𝓝 1) := by
        convert Tendsto.comp (continuous_ofReal.tendsto 1) he using 1
        ext h
        simp only [Function.comp_apply, ofReal_div, ofReal_sub, ofReal_one]
      have h_prod : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ)
                            (𝓝[>] 0) (𝓝 ((1 : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) :=
        Tendsto.smul he_cplx hi
      simp only [one_smul] at h_prod
      apply Tendsto.congr' _ h_prod
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [div_eq_inv_mul]
      conv_lhs =>
        rw [show (↑(Real.exp h) : ℂ) - 1 = ↑(Real.exp h - 1) from by rw [ofReal_sub, ofReal_one]]
        rw [← smul_smul]
      rfl
    · exact tendsto_average_integral_unitary U_grp φ
  · have h_eq : ∀ h : ℝ, h < 0 → ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
                                                   resolventIntegralPlus U_grp φ) =
                         (-(h : ℂ)⁻¹ • Real.exp h • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ) +
                         (-(h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) := by
      intro h hh
      rw [unitary_shift_resolventIntegralPlus_neg U_grp φ h hh]
      rw [smul_add, smul_smul, smul_smul, h_scalar h (ne_of_lt hh)]
    apply Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact (h_eq h hh).symm
    rw [show φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ =
            φ + (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) by abel]
    apply Tendsto.add
    · have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U t φ) :=
        (Real.continuous_exp.comp continuous_neg).smul (U_grp.strong_continuous φ)
      have h_f0 : Real.exp (-(0 : ℝ)) • U_grp.U 0 φ = φ := by
        simp only [neg_zero, Real.exp_zero, one_smul]
        rw [U_grp.identity]
        simp only [ContinuousLinearMap.id_apply]
      have he : Tendsto (fun h : ℝ => Real.exp h) (𝓝[<] 0) (𝓝 1) := by
        rw [← Real.exp_zero]
        exact Real.continuous_exp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h_flip : ∀ h : ℝ, h < 0 → -(h : ℂ)⁻¹ • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ =
                             ((-h) : ℂ)⁻¹ • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ := by
        intro h hh
        congr 1
        exact neg_inv
      have he : Tendsto (fun h : ℝ => Real.exp h) (𝓝[<] 0) (𝓝 1) := by
        rw [← Real.exp_zero]
        exact Real.continuous_exp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h_avg := tendsto_average_integral_unitary_neg U_grp φ
      have h_comb : Tendsto (fun h : ℝ => Real.exp h • (((-h)⁻¹ : ℂ) • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ))
                            (𝓝[<] 0) (𝓝 ((1 : ℝ) • φ)) := by
        have he' : Tendsto (fun h : ℝ => Real.exp h) (𝓝[<] 0) (𝓝 (1 : ℝ)) := by
          rw [← Real.exp_zero]
          exact Real.continuous_exp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        exact Tendsto.smul he' h_avg
      simp only [one_smul] at h_comb
      apply Tendsto.congr' _ h_comb
      filter_upwards [self_mem_nhdsWithin] with h hh
      rw [smul_comm, @inv_neg]
    · have he : Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[<] 0) (𝓝 1) :=
        tendsto_exp_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))
      have he_cplx : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ)) (𝓝[<] 0) (𝓝 1) := by
        convert Tendsto.comp (continuous_ofReal.tendsto 1) he using 1
        ext h
        simp only [Function.comp_apply, ofReal_div, ofReal_sub, ofReal_one]
      have h_prod : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)
                            (𝓝[<] 0) (𝓝 ((1 : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) :=
        Tendsto.smul he_cplx tendsto_const_nhds
      simp only [one_smul] at h_prod
      have h_inner : Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)
                             (𝓝[<] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) := by
        apply Tendsto.congr' _ h_prod
        filter_upwards [self_mem_nhdsWithin] with h hh
        simp only [div_eq_inv_mul]
        conv_lhs =>
          rw [show (↑(Real.exp h) : ℂ) - 1 = ↑(Real.exp h - 1) from by rw [ofReal_sub, ofReal_one]]
          rw [← smul_smul]
        rw [@Complex.coe_smul]
      apply Tendsto.congr' _ h_inner.neg
      filter_upwards with h
      rw [neg_smul]

end GeneratorLimitPlus

end QuantumMechanics.Bochner
