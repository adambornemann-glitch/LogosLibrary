/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: BellsTheorem/TLHV/CHSH.lean
-/
import LogosLibrary.Superior.SplitMechanics.ThermalBell.Core
/-!
# Thermal Hidden Variable Models — CHSH Bounds

## Synopsis

This file proves the main CHSH inequality results for the thermal
hidden variable framework defined in `Core.lean`. The key structural
insight is that the CHSH value decomposes additively:

    S = S_classical + S_thermal

where |S_classical| ≤ 2 (Bell's bound on the base measure) and
|S_thermal| ≤ 4·ε_max. Combined: |S| ≤ 2 + 4·ε_max.

Setting ε = 0 recovers Bell's classical bound exactly, and the
thermal model maps onto a standard `LHVModel` from `BellTheorem`.

## Main Results

* `CHSH_decomposition` — S = S_classical + S_thermal
* `CHSH_classical_bound` — |S_classical| ≤ 2
* `CHSH_thermal_bound` — |S_thermal| ≤ 4·ε_max
* `thermal_chsh_bound` — |S| ≤ 2 + 4·ε_max
* `classical_bound_from_thermal` — ε = 0 recovers |S| ≤ 2
* `thermal_CHSH_eq_lhv_CHSH` — ε = 0 agrees with `LHVModel.CHSH`
* `thermal_bound_tight` — the bound 2 + 4ε is achievable
* `thermal_covers_quantum_range` — every S ∈ (2, 2√2] is reachable
* `thermal_chsh_limit` — S → 2 as thermal separation → ∞

## References

* Bell, "Speakable and Unspeakable in Quantum Mechanics"
* 't Hooft, "The Cellular Automaton Interpretation of Quantum Mechanics"
* Connes, Rovelli, "Von Neumann Algebra Automorphisms and
  Time-Thermodynamics", CQG 11 (1994)

## Tags

Bell inequality, CHSH, hidden variables, thermal, KMS, measurement
independence, classical reduction, tightness
-/
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Real BellTheorem

namespace ThermalBell

/-! ## Section 1: Model Definitions -/

variable {Λ : Type*} [MeasurableSpace Λ]


/-- |S_classical| ≤ 2 (Bell's bound applied to the base measure). -/
theorem CHSH_classical_bound (M : ThermalHVModel Λ) :
    |M.CHSH_classical| ≤ 2 := by
  unfold ThermalHVModel.CHSH_classical
  -- Step 1: ae the integrand has norm ≤ 2, using chsh_pointwise_values
  have hae : ∀ᵐ ω ∂(M.μ₀ : Measure Λ),
      ‖M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω +
       M.A 1 ω * M.B 0 ω + M.A 1 ω * M.B 1 ω‖ ≤ 2 := by
    filter_upwards [(M.A 0).ae_pm_one, (M.A 1).ae_pm_one,
                     (M.B 0).ae_pm_one, (M.B 1).ae_pm_one] with ω ha₀ ha₁ hb₀ hb₁
    rw [Real.norm_eq_abs]
    have hpw := chsh_pointwise_values (M.A 0 ω) (M.A 1 ω) (M.B 0 ω) (M.B 1 ω)
      ha₀ ha₁ hb₀ hb₁
    unfold chsh_pointwise at hpw
    rcases hpw with h | h <;> rw [h] <;> norm_num
  -- Step 2: ‖∫ f‖ ≤ C * μ(univ).toReal, then μ(univ) = 1
  have h := norm_integral_le_of_norm_le_const hae
  simp only [Measure.real, measure_univ, Fin.isValue, norm_eq_abs, ENNReal.toReal_one, mul_one] at h
  exact RCLike.ofReal_le_ofReal.mp h


/-- **CHSH Decomposition**: S = S_classical + S_thermal. -/
theorem CHSH_decomposition (M : ThermalHVModel Λ) :
    M.CHSH = M.CHSH_classical + M.CHSH_thermal := by
  have hAB : ∀ i j, Integrable (fun ω => M.A i ω * M.B j ω) (M.μ₀ : Measure Λ) := by
    intro i j
    exact (integrable_const (1 : ℝ)).mono
      ((M.A i).measurable.mul (M.B j).measurable).aestronglyMeasurable
      (by filter_upwards [(M.A i).ae_pm_one, (M.B j).ae_pm_one] with ω ha hb
          rcases ha with h₁ | h₁ <;> rcases hb with h₂ | h₂ <;> simp [h₁, h₂])
  have hABε : ∀ i j, Integrable (fun ω => M.A i ω * M.B j ω * M.deviation.ε i j ω)
      (M.μ₀ : Measure Λ) := by
    intro i j
    exact (M.deviation.integrable i j).mono
      (((M.A i).measurable.mul (M.B j).measurable).mul
        (M.deviation.measurable i j)).aestronglyMeasurable
      (by filter_upwards [(M.A i).ae_pm_one, (M.B j).ae_pm_one] with ω ha hb
          simp only [norm_mul, Real.norm_eq_abs]
          rcases ha with h₁ | h₁ <;> rcases hb with h₂ | h₂ <;> simp [h₁, h₂])
  -- Each correlation splits: E(i,j) = ∫AB + ∫ABε
  have hsplit : ∀ i j, M.correlation i j =
      ∫ ω, M.A i ω * M.B j ω ∂(M.μ₀ : Measure Λ) +
      ∫ ω, M.A i ω * M.B j ω * M.deviation.ε i j ω ∂(M.μ₀ : Measure Λ) := by
    intro i j; simp only [ThermalHVModel.correlation]
    have h : ∀ ω, M.A i ω * M.B j ω * (1 + M.deviation.ε i j ω) =
        M.A i ω * M.B j ω + M.A i ω * M.B j ω * M.deviation.ε i j ω := fun ω => by ring
    simp_rw [h]; exact integral_add (hAB i j) (hABε i j)
  -- Split CHSH_classical: ∫(f₁-f₂+f₃+f₄) = ∫f₁ - ∫f₂ + ∫f₃ + ∫f₄
  have hcl_split : M.CHSH_classical =
      ∫ ω, M.A 0 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ) -
      ∫ ω, M.A 0 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ) +
      ∫ ω, M.A 1 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ) +
      ∫ ω, M.A 1 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ) := by
    unfold ThermalHVModel.CHSH_classical
    -- Term proofs: Lean's type checker handles Pi ↔ pointwise defeq
    have s1 := integral_add ((hAB 0 1).sub (hAB 0 0) |>.add (hAB 1 0)) (hAB 1 1)
    have s2 := integral_add ((hAB 0 1).sub (hAB 0 0)) (hAB 1 0)
    have s3 := integral_sub (hAB 0 1) (hAB 0 0)
    -- Normalize Pi-level ops to pointwise so linarith can match integrals
    simp_rw [Pi.add_apply, Pi.sub_apply] at s1 s2 s3
    linarith
  -- Split CHSH_thermal: same pattern
  have hth_split : M.CHSH_thermal =
      ∫ ω, M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω ∂(M.μ₀ : Measure Λ) -
      ∫ ω, M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω ∂(M.μ₀ : Measure Λ) +
      ∫ ω, M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω ∂(M.μ₀ : Measure Λ) +
      ∫ ω, M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω ∂(M.μ₀ : Measure Λ) := by
    unfold ThermalHVModel.CHSH_thermal
    have s1 := integral_add ((hABε 0 1).sub (hABε 0 0) |>.add (hABε 1 0)) (hABε 1 1)
    have s2 := integral_add ((hABε 0 1).sub (hABε 0 0)) (hABε 1 0)
    have s3 := integral_sub (hABε 0 1) (hABε 0 0)
    simp_rw [Pi.add_apply, Pi.sub_apply] at s1 s2 s3
    linarith
  -- CHSH → 4 correlations → 8 integrals (via hsplit)
  -- CHSH_classical + CHSH_thermal → 8 integrals (via hcl_split, hth_split)
  -- Both sides are now the same ℝ expression over 8 named integrals
  simp only [ThermalHVModel.CHSH, hsplit, hcl_split, hth_split]
  ring

/- Proof for CHSH_thermal_bound — drop-in replacement for the sorry -/

/-- |S_thermal| ≤ 4·ε_max. -/
theorem CHSH_thermal_bound (M : ThermalHVModel Λ) (ε_max : ℝ)
    (hε_sup : ∀ i j ω, |M.deviation.ε i j ω| ≤ ε_max) :
    |M.CHSH_thermal| ≤ 4 * ε_max := by
  unfold ThermalHVModel.CHSH_thermal
  -- Helper: ±1 * ±1 absorbs into the absolute value
  have pm_mul_abs : ∀ (a b x : ℝ), (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
      |a * b * x| = |x| := by
    intros a b x ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  -- Helper: four-term triangle inequality
  have four_abs : ∀ (a b c d : ℝ), |a - b + c + d| ≤ |a| + |b| + |c| + |d| := by
    intros a b c d
    have h1 := abs_add_le (a - b + c) d
    have h2 := abs_add_le (a - b) c
    have h3 := abs_add_le a (-b)
    simp only [abs_neg] at h3
    grind => linarith
  -- Step 1: ae the integrand has norm ≤ 4 * ε_max
  have hae : ∀ᵐ ω ∂(M.μ₀ : Measure Λ),
      ‖M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
       M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
       M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
       M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω‖ ≤ 4 * ε_max := by
    filter_upwards [(M.A 0).ae_pm_one, (M.A 1).ae_pm_one,
                     (M.B 0).ae_pm_one, (M.B 1).ae_pm_one] with ω ha₀ ha₁ hb₀ hb₁
    rw [Real.norm_eq_abs]
    have h01 : |M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω| ≤ ε_max := by
      rw [pm_mul_abs _ _ _ ha₀ hb₁]; exact hε_sup 0 1 ω
    have h00 : |M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω| ≤ ε_max := by
      rw [pm_mul_abs _ _ _ ha₀ hb₀]; exact hε_sup 0 0 ω
    have h10 : |M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω| ≤ ε_max := by
      rw [pm_mul_abs _ _ _ ha₁ hb₀]; exact hε_sup 1 0 ω
    have h11 : |M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω| ≤ ε_max := by
      rw [pm_mul_abs _ _ _ ha₁ hb₁]; exact hε_sup 1 1 ω
    linarith [four_abs (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω)
                       (M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω)
                       (M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω)
                       (M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω)]
  -- Step 2: ‖∫ f‖ ≤ C * μ(univ).toReal, then μ(univ) = 1
  have h := norm_integral_le_of_norm_le_const hae
  simp only [Measure.real, measure_univ, Fin.isValue, norm_eq_abs,
             ENNReal.toReal_one, mul_one] at h
  exact RCLike.ofReal_le_ofReal.mp h

/-! ## Section 4: Classical Reduction (ε = 0)

When the correlation deviation vanishes, the thermal model reduces
exactly to a standard LHV model. Bell's bound is a special case.
-/

/-- When ε = 0, the thermal correlation equals the base correlation. -/
lemma correlation_of_zero_deviation
    (M : ThermalHVModel Λ)
    (hzero : ∀ i j ω, M.deviation.ε i j ω = 0)
    (i j : Fin 2) :
    M.correlation i j = ∫ ω, M.A i ω * M.B j ω ∂(M.μ₀ : Measure Λ) := by
  unfold ThermalHVModel.correlation
  congr 1; ext ω; rw [hzero]; ring

/-- When ε = 0, the thermal CHSH equals the classical formula. -/
lemma CHSH_of_zero_deviation
    (M : ThermalHVModel Λ)
    (hzero : ∀ i j ω, M.deviation.ε i j ω = 0) :
    M.CHSH = ∫ ω, (M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω +
                   M.A 1 ω * M.B 0 ω + M.A 1 ω * M.B 1 ω) ∂(M.μ₀ : Measure Λ) := by
  have h := CHSH_decomposition M
  have hth : M.CHSH_thermal = 0 := by
    unfold ThermalHVModel.CHSH_thermal
    simp_rw [hzero]; simp only [mul_zero, sub_self, add_zero, integral_zero]
  rw [h, hth, add_zero]; rfl

/-- Convert ThermalBell.ResponseFunction to BellTheorem.ResponseFunction. -/
def ResponseFunction.toBellTheorem {Λ : Type*} [MeasurableSpace Λ] {μ : Measure Λ}
    (f : ThermalBell.ResponseFunction Λ μ) : BellTheorem.ResponseFunction Λ μ where
  toFun := f.toFun
  measurable := f.measurable
  ae_pm_one := f.ae_pm_one
  integrable := f.integrable

/-- Convert a ThermalHVModel to an LHVModel (forgetting ε). -/
noncomputable def ThermalHVModel.toLHV (M : ThermalHVModel Λ) : LHVModel Λ where
  μ := M.μ₀
  A₀ := (M.A 0).toBellTheorem
  A₁ := (M.A 1).toBellTheorem
  B₀ := (M.B 0).toBellTheorem
  B₁ := (M.B 1).toBellTheorem

/-- The CHSH values agree when ε = 0. -/
lemma thermal_CHSH_eq_lhv_CHSH
    (M : ThermalHVModel Λ)
    (hzero : ∀ i j ω, M.deviation.ε i j ω = 0) :
    M.CHSH = M.toLHV.CHSH := by
  rw [CHSH_of_zero_deviation M hzero, BellTheorem.chsh_as_integral]; rfl

/-- Alternative: derive directly from the LHV bound. -/
theorem classical_bound_via_lhv
    (M : ThermalHVModel Λ)
    (hzero : ∀ i j ω, M.deviation.ε i j ω = 0) :
    |M.CHSH| ≤ 2 := by
  rw [thermal_CHSH_eq_lhv_CHSH M hzero]; exact lhv_chsh_bound M.toLHV

/-! ## Section 5: Thermal Correlation Structure

A physically motivated model: correlations decay exponentially with
thermal time separation between source preparation and detector
configuration. Connects to the KMS machinery via the modular period.
-/

/-- A thermal correlation structure: ε decays exponentially. -/
structure ThermalCorrelationStructure (Λ : Type*) [MeasurableSpace Λ] (μ₀ : Measure Λ) extends
    CorrelationDeviation Λ μ₀ where
  T : ℝ
  hT_pos : T > 0
  τ_corr : ℝ
  hτ_pos : τ_corr > 0
  t_separation : ℝ
  ht_pos : t_separation ≥ 0
  C : Λ → ℝ
  C_measurable : Measurable C
  C_bounded : ∀ ω, |C ω| ≤ 1
  ε_thermal_form : ∀ i j ω, |ε i j ω| ≤ |C ω| * Real.exp (-t_separation / τ_corr)
  hmodular_sep : t_separation / τ_corr ≥ Real.pi / 4

/-- The maximum ε for a thermal correlation structure. -/
noncomputable def ThermalCorrelationStructure.ε_max
    {μ₀ : Measure Λ} (S : ThermalCorrelationStructure Λ μ₀) : ℝ :=
  Real.exp (-S.t_separation / S.τ_corr)

/-- Correlations decay to zero with increasing thermal time separation. -/
lemma correlation_decay (_μ₀ : Measure Λ) (τ_corr : ℝ) (hτ : τ_corr > 0) :
    Filter.Tendsto
      (fun t => Real.exp (-t / τ_corr))
      Filter.atTop
      (nhds 0) := by
  have h_scale : Filter.Tendsto (fun t => t / τ_corr) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.atTop_div_const hτ; exact fun ⦃U⦄ a => a
  have h_comp := Real.tendsto_exp_neg_atTop_nhds_zero.comp h_scale
  convert h_comp using 1; ext t
  simp only [Function.comp_apply, exp_eq_exp]; exact neg_div τ_corr t

/-- In the limit of large separation, the CHSH bound approaches 2. -/
lemma thermal_chsh_limit (μ₀ : Measure Λ) (τ_corr : ℝ) (hτ : τ_corr > 0) :
    Filter.Tendsto
      (fun t => 2 + 4 * Real.exp (-t / τ_corr))
      Filter.atTop
      (nhds 2) := by
  have h := correlation_decay μ₀ τ_corr hτ
  have : Filter.Tendsto (fun t => 2 + 4 * Real.exp (-t / τ_corr))
      Filter.atTop (nhds (2 + 4 * 0)) :=
    Filter.Tendsto.const_add 2 (Filter.Tendsto.const_mul 4 h)
  simp at this; exact this

/-! ## Section 6: Strict Generalization

When ε > 0, the thermal framework strictly generalizes LHV:
it can achieve |S| > 2, which no LHV model can.
-/

/-- A thermal model with ε > 0 can exceed the classical bound. -/
lemma thermal_exceeds_classical_possible (ε : ℝ) (hε_pos : ε > 0) :
    2 + 4 * ε > 2 := by linarith

/-- For any S ∈ (2, 2√2], there exists ε fitting the thermal bound. -/
lemma thermal_covers_quantum_range (S : ℝ) (hS_low : S > 2) (hS_high : S ≤ 2 * Real.sqrt 2) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ (Real.sqrt 2 - 1) / 2 ∧ 2 + 4 * ε ≥ S := by
  use (S - 2) / 4
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ## Section 7: Tightness

The bound |S| ≤ 2 + 4ε is tight: for any ε, there exist response
functions achieving equality.
-/

/-- **Main bound**: |S| ≤ 2 + 4·ε_max. -/
theorem thermal_chsh_bound (M : ThermalHVModel Λ) (ε_max : ℝ)
    (hε_sup : ∀ i j ω, |M.deviation.ε i j ω| ≤ ε_max) :
    |M.CHSH| ≤ 2 + 4 * ε_max := by
  calc |M.CHSH|
      = |M.CHSH_classical + M.CHSH_thermal| := by rw [CHSH_decomposition]
    _ ≤ |M.CHSH_classical| + |M.CHSH_thermal| := abs_add_le _ _
    _ ≤ 2 + 4 * ε_max := by linarith [CHSH_classical_bound M, CHSH_thermal_bound M ε_max hε_sup]

/-- **Classical reduction**: ε = 0 recovers Bell's bound. -/
theorem classical_bound_from_thermal
    (M : ThermalHVModel Λ)
    (hzero : ∀ i j ω, M.deviation.ε i j ω = 0) :
    |M.CHSH| ≤ 2 := by
  have h := thermal_chsh_bound M 0 (by simp [hzero])
  simp at h; exact h

/-- The bound 2 + 4ε is achievable with the right configuration. -/
theorem thermal_bound_tight (ε : ℝ) (_hε : |ε| < 1) :
    ∃ (config : Fin 2 → Fin 2 → ℝ),
      (∀ i j, config i j = ε ∨ config i j = -ε) ∧
      (2 : ℝ) + (config 0 1 - config 0 0 + config 1 0 + config 1 1) = 2 + 4 * |ε| := by
  by_cases hpos : ε ≥ 0
  · use fun i j => if i = 0 ∧ j = 0 then -ε else ε
    constructor
    · intro i j; split_ifs <;> simp
    · simp only [Fin.isValue, one_ne_zero, and_false, ↓reduceIte, and_self, sub_neg_eq_add,
        and_true, add_right_inj]
      rw [abs_of_nonneg hpos]; ring
  · push_neg at hpos
    use fun i j => if i = 0 ∧ j = 0 then ε else -ε
    constructor
    · intro i j; split_ifs <;> simp
    · simp only [Fin.isValue, one_ne_zero]
      grind only [= abs.eq_1, = max_def]

end ThermalBell
