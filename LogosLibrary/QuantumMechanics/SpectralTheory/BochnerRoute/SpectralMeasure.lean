/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/SpectralMeasure.lean
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.MeasureSpace
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent

/-!
# Spectral Measures and Projection-Valued Measures

This file develops the theory of projection-valued spectral measures on Hilbert spaces.
Given a spectral measure `E : Set ℝ → H →L[ℂ] H`, we construct the associated scalar
measures and prove their basic properties.

## Main definitions

* `IsSpectralMeasure`: Structure bundling the axioms for a projection-valued measure
* `spectralDistribution`: The Stieltjes function `t ↦ ⟨E(-∞,t]ψ, ψ⟩`
* `spectral_inner_measure`: The measure `μ_ψ(B) = ⟨E(B)ψ, ψ⟩` defined directly
* `spectral_scalar_measure`: The same measure obtained from the Stieltjes construction

## Main statements

* `spectral_projection_norm_le`: `‖E(B)ψ‖ ≤ ‖ψ‖` (projections are contractions)
* `spectral_projection_norm_sq`: `‖E(B)ψ‖² = ⟨E(B)ψ, ψ⟩.re`
* `spectral_inner_measure_eq`: The two constructions of the scalar measure agree
* `spectral_scalar_measure_apply`: `μ_ψ(B) = ⟨E(B)ψ, ψ⟩.re` (as ENNReal)

## Implementation notes

The spectral measure is axiomatized via `IsSpectralMeasure` which requires:
- Multiplicativity: `E(B)E(C) = E(B ∩ C)`
- Self-adjointness: `⟨E(B)ψ, φ⟩ = ⟨ψ, E(B)φ⟩`
- Strong operator continuity (right-continuity of `t ↦ E(-∞,t]ψ`)
- Measure axioms: `E(∅) = 0`, `E(ℝ) = 1`, σ-additivity

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Chapter VII
* [Schmüdgen, *Unbounded Self-adjoint Operators*][schmudgen2012], Chapter 4

## Tags

spectral measure, projection-valued measure, Stieltjes function, scalar spectral measure
-/

namespace SpectralBridge.Bochner

open InnerProductSpace MeasureTheory Complex Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Projection norm estimates -/

/-- Spectral projections are contractions: `‖E(B)ψ‖ ≤ ‖ψ‖`.
    This follows from idempotence and self-adjointness. -/
lemma spectral_projection_norm_le (E : Set ℝ → H →L[ℂ] H)
    (hE_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C))
    (hE_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    ‖E B ψ‖ ≤ ‖ψ‖ := by
  -- E(B) is idempotent
  have h_idem : E B * E B = E B := by rw [hE_mul B B hB hB, Set.inter_self]
  -- ‖E(B)ψ‖² = ⟨E(B)ψ, E(B)ψ⟩ = ⟨E(B)²ψ, ψ⟩ = ⟨E(B)ψ, ψ⟩
  have h1 : ‖E B ψ‖^2 = (⟪E B ψ, ψ⟫_ℂ).re := by
    calc ‖E B ψ‖^2
        = (⟪E B ψ, E B ψ⟫_ℂ).re := by
          rw [inner_self_eq_norm_sq_to_K]
          rw [← @RCLike.ofReal_pow]
          exact rfl
      _ = (⟪E B (E B ψ), ψ⟫_ℂ).re := by rw [hE_sa B (E B ψ) ψ]
      _ = (⟪(E B * E B) ψ, ψ⟫_ℂ).re := by rw [ContinuousLinearMap.mul_apply]
      _ = (⟪E B ψ, ψ⟫_ℂ).re := by rw [h_idem]
  -- By Cauchy-Schwarz: |⟨E(B)ψ, ψ⟩| ≤ ‖E(B)ψ‖·‖ψ‖
  have h2 : |(⟪E B ψ, ψ⟫_ℂ).re| ≤ ‖E B ψ‖ * ‖ψ‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  -- Since (⟨E(B)ψ, ψ⟩).re = ‖E(B)ψ‖² ≥ 0
  have h3 : (⟪E B ψ, ψ⟫_ℂ).re ≥ 0 := by rw [← h1]; exact sq_nonneg _
  -- So ‖E(B)ψ‖² ≤ ‖E(B)ψ‖·‖ψ‖
  have h4 : ‖E B ψ‖^2 ≤ ‖E B ψ‖ * ‖ψ‖ := h1 ▸ (abs_of_nonneg h3 ▸ h2)
  -- If ‖E(B)ψ‖ = 0, done. Otherwise divide by ‖E(B)ψ‖.
  by_cases hE : ‖E B ψ‖ = 0
  · simp [hE]
  · have hE_pos : 0 < ‖E B ψ‖ := (norm_nonneg _).lt_of_ne' hE
    calc ‖E B ψ‖ = ‖E B ψ‖^2 / ‖E B ψ‖ := by field_simp
      _ ≤ (‖E B ψ‖ * ‖ψ‖) / ‖E B ψ‖ := by exact
        (div_le_div_iff_of_pos_right hE_pos).mpr h4
      _ = ‖ψ‖ := by exact mul_div_cancel_left₀ ‖ψ‖ hE

/-- Spectral projections have operator norm at most 1. -/
lemma spectral_projection_opNorm_le_one (E : Set ℝ → H →L[ℂ] H)
    (hE_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C))
    (hE_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ‖E B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  simp only [one_mul]
  exact spectral_projection_norm_le E hE_mul hE_sa B hB ψ

/-! ### The spectral measure structure -/

/-- A projection-valued spectral measure on ℝ.

This bundles all the axioms that a spectral measure must satisfy:
- Multiplicativity (projections onto intersections)
- Self-adjointness
- Strong operator continuity
- Measure axioms (empty set, full space, additivity, σ-additivity) -/
structure IsSpectralMeasure (E : Set ℝ → H →L[ℂ] H) : Prop where
  /-- E(B ∩ C) = E(B)E(C) -/
  mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C)
  /-- E(B) is self-adjoint -/
  sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ
  /-- t ↦ E(-∞,t]ψ is right-continuous in SOT -/
  sot : ∀ ψ t₀, Filter.Tendsto (fun t => E (Set.Iic t) ψ) (nhdsWithin t₀ (Set.Ioi t₀)) (nhds (E (Set.Iic t₀) ψ))
  /-- E(∅) = 0 -/
  empty : E ∅ = 0
  /-- E(ℝ) = 1 -/
  univ : E Set.univ = 1
  /-- E(B ∪ C) = E(B) + E(C) for disjoint B, C -/
  add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C → E (B ∪ C) = E B + E C
  /-- σ-additivity in SOT -/
  σ_add : ∀ ψ (B : ℕ → Set ℝ), (∀ n, MeasurableSet (B n)) →
        (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
        HasSum (fun n => E (B n) ψ) (E (⋃ n, B n) ψ)

/-! ### The Stieltjes distribution function -/

/-- The spectral distribution function: `F(t) = ⟨E(-∞,t]ψ, ψ⟩.re`.

This is a right-continuous monotone function, hence defines a Stieltjes measure.
The monotonicity follows from `E(Iic s) ≤ E(Iic t)` for `s ≤ t` (as projections). -/
noncomputable def spectralDistribution (E : Set ℝ → H →L[ℂ] H) (ψ : H)
    (hE_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C))
    (hE_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ)
    (hE_sot : ∀ t₀, Tendsto (fun t => E (Set.Iic t) ψ) (𝓝[>] t₀) (𝓝 (E (Set.Iic t₀) ψ))) :
    StieltjesFunction ℝ where
  toFun := fun t => (⟪E (Set.Iic t) ψ, ψ⟫_ℂ).re

  mono' := fun s t hst => by
    -- E(Iic s) = E(Iic s) * E(Iic t) since Iic s ⊆ Iic t
    have h_subset : Set.Iic s ∩ Set.Iic t = Set.Iic s := by
      simp only [Set.Iic_inter_Iic]
      rw [inf_of_le_left hst]
    have h_factor : E (Set.Iic s) = E (Set.Iic s) * E (Set.Iic t) := by
      rw [hE_mul _ _ measurableSet_Iic measurableSet_Iic, h_subset]

    -- ⟨E(B)ψ, ψ⟩ = ‖E(B)ψ‖² for self-adjoint idempotent E(B)
    have h_norm_sq : ∀ B, MeasurableSet B → (⟪E B ψ, ψ⟫_ℂ).re = ‖E B ψ‖^2 := by
      intro B hB
      have h_idem : E B * E B = E B := by rw [hE_mul B B hB hB, Set.inter_self]
      calc (⟪E B ψ, ψ⟫_ℂ).re
          = (⟪E B (E B ψ), ψ⟫_ℂ).re := by rw [← ContinuousLinearMap.mul_apply, h_idem]
        _ = (⟪E B ψ, E B ψ⟫_ℂ).re := by rw [hE_sa B (E B ψ) ψ]
        _ = ‖E B ψ‖^2 := by rw [inner_self_eq_norm_sq_to_K]; rw [← @RCLike.ofReal_pow]; exact rfl

    -- E(Iic s)ψ = E(Iic s)(E(Iic t)ψ), so ‖E(Iic s)ψ‖ ≤ ‖E(Iic t)ψ‖
    show (⟪E (Set.Iic s) ψ, ψ⟫_ℂ).re ≤ (⟪E (Set.Iic t) ψ, ψ⟫_ℂ).re
    rw [h_norm_sq _ measurableSet_Iic, h_norm_sq _ measurableSet_Iic]
    have h_contract : ‖E (Set.Iic s) ψ‖ ≤ ‖E (Set.Iic t) ψ‖ := by
      calc ‖E (Set.Iic s) ψ‖
          = ‖(E (Set.Iic s) * E (Set.Iic t)) ψ‖ := by rw [← h_factor]
        _ = ‖E (Set.Iic s) (E (Set.Iic t) ψ)‖ := by rw [ContinuousLinearMap.mul_apply]
        _ ≤ ‖E (Set.Iic s)‖ * ‖E (Set.Iic t) ψ‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖E (Set.Iic t) ψ‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              exact spectral_projection_opNorm_le_one E hE_mul hE_sa (Set.Iic s) measurableSet_Iic
        _ = ‖E (Set.Iic t) ψ‖ := one_mul _
    exact sq_le_sq' (by linarith [norm_nonneg (E (Set.Iic s) ψ)]) h_contract

  right_continuous' := fun t₀ => by
    have h := hE_sot t₀
    have h_inner : Tendsto (fun t => ⟪E (Set.Iic t) ψ, ψ⟫_ℂ) (𝓝[>] t₀)
                          (𝓝 ⟪E (Set.Iic t₀) ψ, ψ⟫_ℂ) :=
      Filter.Tendsto.inner h tendsto_const_nhds
    have h_re : Tendsto (fun t => (⟪E (Set.Iic t) ψ, ψ⟫_ℂ).re) (𝓝[>] t₀)
                        (𝓝 (⟪E (Set.Iic t₀) ψ, ψ⟫_ℂ).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp h_inner
    exact continuousWithinAt_Ioi_iff_Ici.mp h_re

/-! ### σ-additivity of the inner product spectral function -/

/-- The inner product spectral function is σ-additive. -/
lemma spectral_inner_hasSum (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (ψ : H) (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hB_disj : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    HasSum (fun n => (⟪E (B n) ψ, ψ⟫_ℂ).re) (⟪E (⋃ n, B n) ψ, ψ⟫_ℂ).re := by
  have hσ := hE.σ_add ψ B hB hB_disj
  -- Step 1: Inner product with ψ preserves HasSum
  have h_inner : HasSum (fun n => ⟪E (B n) ψ, ψ⟫_ℂ) ⟪E (⋃ n, B n) ψ, ψ⟫_ℂ := by
    rw [HasSum] at hσ ⊢
    have h_sum_inner : ∀ s : Finset ℕ,
        s.sum (fun i => ⟪E (B i) ψ, ψ⟫_ℂ) = ⟪s.sum (fun i => E (B i) ψ), ψ⟫_ℂ := by
      intro s
      rw [sum_inner]
    simp_rw [h_sum_inner]
    exact Tendsto.inner hσ tendsto_const_nhds
  -- Step 2: Real part preserves HasSum
  rw [HasSum] at h_inner ⊢
  have h_sum_re : ∀ s : Finset ℕ,
      s.sum (fun i => (⟪E (B i) ψ, ψ⟫_ℂ).re) = (s.sum (fun i => ⟪E (B i) ψ, ψ⟫_ℂ)).re := by
    intro s
    simp only [Complex.re_sum]
  simp_rw [h_sum_re]
  exact Complex.continuous_re.continuousAt.tendsto.comp h_inner

/-- ‖E(B)ψ‖² = ⟪E(B)ψ, ψ⟫.re -/
lemma spectral_projection_norm_sq (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    ‖E B ψ‖^2 = (⟪E B ψ, ψ⟫_ℂ).re := by
  have h_idem : E B * E B = E B := by rw [hE.mul B B hB hB, Set.inter_self]
  calc ‖E B ψ‖^2
      = (⟪E B ψ, E B ψ⟫_ℂ).re := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; rw [← @RCLike.ofReal_pow]; rfl
    _ = (⟪E B (E B ψ), ψ⟫_ℂ).re := by rw [hE.sa B (E B ψ) ψ]
    _ = (⟪(E B * E B) ψ, ψ⟫_ℂ).re := by rw [ContinuousLinearMap.mul_apply]
    _ = (⟪E B ψ, ψ⟫_ℂ).re := by rw [h_idem]

/-! ### Construction of the scalar spectral measure -/

/-- The spectral inner measure, defined directly from the inner product.
    `μ_ψ(B) = ⟨E(B)ψ, ψ⟩.re` -/
noncomputable def spectral_inner_measure (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (ψ : H) : Measure ℝ := by
  refine Measure.ofMeasurable
    (fun B _ => ENNReal.ofReal (⟪E B ψ, ψ⟫_ℂ).re) ?_ ?_
  · -- Empty set: E(∅) = 0
    simp only [hE.empty, ContinuousLinearMap.zero_apply, inner_zero_left, Complex.zero_re,
               ENNReal.ofReal_zero]
  · -- σ-additivity
    intro B hB_meas hB_disj
    have h_sum := spectral_inner_hasSum E hE ψ B hB_meas hB_disj
    have h_nonneg : ∀ n, 0 ≤ (⟪E (B n) ψ, ψ⟫_ℂ).re := fun n => by
      rw [← spectral_projection_norm_sq E hE (B n) (hB_meas n) ψ]
      exact sq_nonneg _
    have h_nonneg_union : 0 ≤ (⟪E (⋃ n, B n) ψ, ψ⟫_ℂ).re := by
      rw [← spectral_projection_norm_sq E hE (⋃ n, B n) (MeasurableSet.iUnion hB_meas) ψ]
      exact sq_nonneg _
    -- HasSum implies tsum equality
    have h_tsum : ∑' n, (⟪E (B n) ψ, ψ⟫_ℂ).re = (⟪E (⋃ n, B n) ψ, ψ⟫_ℂ).re := h_sum.tsum_eq
    -- For non-negative reals, ofReal commutes with tsum
    simp only
    rw [← h_tsum]
    rw [ENNReal.ofReal_tsum_of_nonneg h_nonneg h_sum.summable]

/-- The spectral scalar measure obtained from the Stieltjes construction. -/
noncomputable def spectral_scalar_measure (E : Set ℝ → H →L[ℂ] H) (ψ : H)
    (hE : IsSpectralMeasure E) : Measure ℝ :=
  (spectralDistribution E ψ hE.mul hE.sa (hE.sot ψ)).measure

/-- The spectral scalar measure of `(a, b]` equals `⟪E(a,b] ψ, ψ⟫.re`. -/
lemma spectral_scalar_measure_apply_Ioc (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (ψ : H) (a b : ℝ) (hab : a < b) :
    spectral_scalar_measure E ψ hE (Set.Ioc a b) = ENNReal.ofReal (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re := by
  unfold spectral_scalar_measure
  rw [StieltjesFunction.measure_Ioc]
  simp only [spectralDistribution]
  have h_decomp : Set.Iic b = Set.Iic a ∪ Set.Ioc a b :=
    (Set.Iic_union_Ioc_eq_Iic (le_of_lt hab)).symm
  have h_disj : Disjoint (Set.Iic a) (Set.Ioc a b) := by
    simp only [le_refl, Set.Iic_disjoint_Ioc]
  have h_add := hE.add (Set.Iic a) (Set.Ioc a b) measurableSet_Iic measurableSet_Ioc h_disj
  have h_inner : (⟪E (Set.Iic b) ψ, ψ⟫_ℂ).re - (⟪E (Set.Iic a) ψ, ψ⟫_ℂ).re =
                 (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re := by
    rw [h_decomp, h_add]
    simp [inner_add_left, Complex.add_re]
  rw [h_inner]

/-- The two constructions agree on intervals (a, b]. -/
lemma spectral_inner_measure_eq_Ioc (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (ψ : H) (a b : ℝ) (hab : a < b) :
    spectral_inner_measure E hE ψ (Set.Ioc a b) = spectral_scalar_measure E ψ hE (Set.Ioc a b) := by
  rw [spectral_scalar_measure_apply_Ioc E hE ψ a b hab]
  unfold spectral_inner_measure
  rw [Measure.ofMeasurable_apply _ measurableSet_Ioc]

/-- spectral_inner_measure is a finite measure. -/
instance spectral_inner_measure_finite (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (ψ : H) :
    IsFiniteMeasure (spectral_inner_measure E hE ψ) := by
  constructor
  unfold spectral_inner_measure
  rw [Measure.ofMeasurable_apply _ MeasurableSet.univ]
  rw [hE.univ]
  simp only [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, coe_algebraMap]
  exact ENNReal.ofReal_lt_top

/-- **Main theorem**: The two constructions of the scalar measure are equal.

This is proved using the uniqueness of measures on ℝ determined by their values on (a,b]. -/
lemma spectral_inner_measure_eq (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (ψ : H) :
    spectral_inner_measure E hE ψ = spectral_scalar_measure E ψ hE := by
  haveI h_inner_finite : IsFiniteMeasure (spectral_inner_measure E hE ψ) :=
    spectral_inner_measure_finite E hE ψ
  haveI : IsLocallyFiniteMeasure (spectral_inner_measure E hE ψ) := by
    exact isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : IsLocallyFiniteMeasure (spectral_scalar_measure E ψ hE) := by
    apply StieltjesFunction.instIsLocallyFiniteMeasure
  apply MeasureTheory.Measure.ext_of_Ioc
  intro a b hab
  rw [spectral_scalar_measure_apply_Ioc E hE ψ a b hab]
  unfold spectral_inner_measure
  rw [Measure.ofMeasurable_apply _ measurableSet_Ioc]

/-! ### Main API for the scalar spectral measure -/

/-- The scalar spectral measure of any measurable set B equals ⟨E(B)ψ, ψ⟩.re (as ENNReal). -/
lemma spectral_scalar_measure_apply (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E) (ψ : H)
    (B : Set ℝ) (hB : MeasurableSet B) :
    spectral_scalar_measure E ψ hE B = ENNReal.ofReal (⟪E B ψ, ψ⟫_ℂ).re := by
  rw [← spectral_inner_measure_eq E hE ψ]
  unfold spectral_inner_measure
  rw [Measure.ofMeasurable_apply _ hB]

/-- The scalar spectral measure of B equals ⟨E(B)ψ, ψ⟩.re (as ℝ). -/
lemma spectral_scalar_measure_apply' (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E) (ψ : H)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (spectral_scalar_measure E ψ hE B).toReal = (⟪E B ψ, ψ⟫_ℂ).re := by
  rw [spectral_scalar_measure_apply E hE ψ B hB]
  rw [ENNReal.toReal_ofReal]
  rw [← spectral_projection_norm_sq E hE B hB ψ]
  exact sq_nonneg _

/-- The spectral scalar measure is finite (bounded by ‖ψ‖²). -/
lemma spectral_scalar_measure_finite (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (ψ : H) :
    IsFiniteMeasure (spectral_scalar_measure E ψ hE) := by
  constructor
  rw [spectral_scalar_measure_apply E hE ψ Set.univ MeasurableSet.univ]
  rw [hE_univ]
  simp only [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, coe_algebraMap]
  exact ENNReal.ofReal_lt_top

/-- Diagonal spectral values are real (imaginary part is zero). -/
lemma spectral_diagonal_real (hE : IsSpectralMeasure E) (B : Set ℝ) (ψ : H) :
    (⟪E B ψ, ψ⟫_ℂ).im = 0 := by
  have h := hE.sa B ψ ψ
  have key : ⟪E B ψ, ψ⟫_ℂ = starRingEnd ℂ ⟪E B ψ, ψ⟫_ℂ :=
    calc ⟪E B ψ, ψ⟫_ℂ
        = ⟪ψ, E B ψ⟫_ℂ := h
      _ = starRingEnd ℂ ⟪E B ψ, ψ⟫_ℂ := by
        exact Eq.symm (conj_inner_symm ψ ((E B) ψ))
  exact Complex.conj_eq_iff_im.mp key.symm

/-! ### Additional spectral measure lemmas -/

/-- E(B) is idempotent: E(B)² = E(B). -/
lemma spectral_projection_idempotent (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) :
    E B * E B = E B := by
  rw [hE.mul B B hB hB, Set.inter_self]

/-- E(B) + E(Bᶜ) = 1. -/
lemma spectral_projection_compl_add (E : Set ℝ → H →L[ℂ] H) (_ : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (hE_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C → E (B ∪ C) = E B + E C)
    (B : Set ℝ) (hB : MeasurableSet B) :
    E B + E Bᶜ = 1 := by
  have h : B ∪ Bᶜ = Set.univ := by exact Set.union_compl_self B
  have h_disj : Disjoint B Bᶜ := by exact Set.disjoint_compl_right_iff_subset.mpr fun ⦃a⦄ a => a
  rw [← hE_add B Bᶜ hB hB.compl h_disj, h, hE_univ]

/-- Spectral measure of union of disjoint sets. -/
lemma spectral_scalar_measure_union (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B C : Set ℝ) (hC : MeasurableSet C) (hBC : Disjoint B C) (ψ : H) :
    spectral_scalar_measure E ψ hE (B ∪ C) =
    spectral_scalar_measure E ψ hE B + spectral_scalar_measure E ψ hE C := by
  exact MeasureTheory.measure_union hBC hC

/-- Spectral measure of set difference. -/
lemma spectral_scalar_measure_diff (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (B C : Set ℝ) (hC : MeasurableSet C) (hCB : C ⊆ B) (ψ : H) :
    spectral_scalar_measure E ψ hE (B \ C) =
    spectral_scalar_measure E ψ hE B - spectral_scalar_measure E ψ hE C := by
  haveI := spectral_scalar_measure_finite E hE hE_univ ψ
  exact MeasureTheory.measure_diff hCB hC.nullMeasurableSet (measure_lt_top _ _).ne

/-- Projection onto intersection. -/
lemma spectral_projection_inter (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    E (B ∩ C) = E B * E C := by
  rw [hE.mul B C hB hC]

/-- Spectral projections commute. -/
lemma spectral_projection_mul_comm (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    E B * E C = E C * E B := by
  rw [hE.mul B C hB hC, hE.mul C B hC hB, Set.inter_comm]

/-- Spectral measure is subadditive. -/
lemma spectral_scalar_measure_subadditive (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B C : Set ℝ) (ψ : H) :
    spectral_scalar_measure E ψ hE (B ∪ C) ≤
    spectral_scalar_measure E ψ hE B + spectral_scalar_measure E ψ hE C := by
  exact MeasureTheory.measure_union_le B C

/-- E(B)ψ is in the range of E(B). -/
lemma spectral_projection_range (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    E B (E B ψ) = E B ψ := by
  have h := spectral_projection_idempotent E hE B hB
  calc E B (E B ψ) = (E B * E B) ψ := rfl
    _ = E B ψ := by rw [h]

/-- Norm of projection is at most norm of vector (variant using IsSpectralMeasure). -/
lemma spectral_projection_norm_le' (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    ‖E B ψ‖ ≤ ‖ψ‖ :=
  spectral_projection_norm_le E hE.mul hE.sa B hB ψ

-- Helper to import from PositiveDefinite.lean
open SpectralBridge.Bochner in
lemma tendsto_nhdsWithin_Ici_of_tendsto_nhdsWithin_Ioi' {f : ℝ → ℝ} {x : ℝ}
    (h : Tendsto f (𝓝[>] x) (𝓝 (f x))) : ContinuousWithinAt f (Set.Ici x) x := by
  exact continuousWithinAt_Ioi_iff_Ici.mp h

end SpectralBridge.Bochner
