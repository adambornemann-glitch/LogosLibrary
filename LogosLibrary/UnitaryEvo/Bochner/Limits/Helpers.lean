/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Bochner/Limits/Helpers.lean
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner.Resolvent

/-!
# Helper Lemmas for Generator Limits

This file contains shared analytical lemmas used in proving that the resolvent
integrals `R±(φ)` lie in the generator domain.

## Main results

* `tendsto_exp_sub_one_div`: `(e^h - 1)/h → 1` as `h → 0`
* `tendsto_integral_Ici_exp_unitary`: continuity of `∫_{[h,∞)} e^{-t} U(t)φ dt` at `h = 0`
* `tendsto_average_integral_unitary`: `h⁻¹ ∫_{(0,h]} e^{-t} U(t)φ dt → φ` as `h → 0⁺`
* `tendsto_average_integral_unitary_neg`: analogous limit as `h → 0⁻`

## Tags

generator, limit, exponential, average
-/

namespace QuantumMechanics.Bochner

open MeasureTheory Measure Filter Topology Complex QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Helpers

variable (U_grp : OneParameterUnitaryGroup (H := H))

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
    · have h_ae_eq : ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ =
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
      have h_eq3 : ∫ t in Set.Ioi h, Real.exp (-t) • U_grp.U t φ =
                   (∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U t φ) -
                   ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ := by
        exact Eq.symm (sub_eq_of_eq_add' h_eq1)
      rw [h_ae_eq2, h_eq3, h_ae_eq.symm, h_eq2]
    · push_neg at hh
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
        grind only [= Set.disjoint_left, = Set.mem_Ico, = Set.mem_Ici]
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
  have h_eq : ∀ h > 0, ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ =
                       ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ := by
    intro h hh
    rw [intervalIntegral.integral_of_le (le_of_lt hh)]
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
    ext h
    unfold slope
    simp only [sub_zero, h_F0, vsub_eq_sub]
    · congr 1
      exact Set.compl_eq_univ_diff {(0 : ℝ)}
  have h_restrict := h_tendsto_real.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
  apply Tendsto.congr' _ h_restrict
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [h_eq h hh, ← ofReal_inv, @Complex.coe_smul]

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
  have h_eq : ∀ h < 0, ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ =
                       ∫ t in h..0, Real.exp (-t) • U_grp.U t φ := by
    intro h hh
    rw [intervalIntegral.integral_of_le (le_of_lt hh)]
  have h_eq' : ∀ h < 0, ∫ t in h..0, Real.exp (-t) • U_grp.U t φ =
                        -∫ t in 0..h, Real.exp (-t) • U_grp.U t φ := by
    intro h _
    rw [intervalIntegral.integral_symm]
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
  apply Tendsto.congr' _ h_restrict
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [h_eq h hh, h_eq' h hh]
  rw [smul_neg]
  rw [← neg_smul]
  rw [(Complex.coe_smul h⁻¹ _).symm, ofReal_inv]
  congr 1
  rw [@neg_inv]
  simp_all only [neg_zero, Real.exp_zero, one_smul, intervalIntegral.integral_same, neg_neg]

end Helpers

end QuantumMechanics.Bochner
