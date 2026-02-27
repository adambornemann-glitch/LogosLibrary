/-
Copyright (c) 2025 Bell Theorem Thermodynamic Analysis
Released under Apache 2.0 license.

# Thermal Hidden Variable Models

This file investigates what happens to Bell's lemma when we relax
the statistical independence assumption using thermodynamic considerations.

## The Core Insight

Bell's LHV model assumes: ρ(ω|a,b) = ρ(ω)
This requires I(ω; a,b) = 0 — zero mutual information.

In a universe with:
- Common causal origin (Big Bang)
- Unscreenable gravity
- Finite-temperature thermal baths
- KMS structure on observables

Perfect independence is unphysical. Everything shares a backward light cone.

## The Program

1. Define ThermalHVModel with setting-dependent measures
2. Show CHSH bound becomes |S| ≤ 2 + f(ε) where ε encodes correlations
3. Connect ε to thermal time and KMS periodicity
4. Investigate whether Tsirelson's bound emerges from modular geometry

## References

- Bell, "Speakable and Unspeakable in Quantum Mechanics"
- 't Hooft, "The Cellular Automaton Interpretation of Quantum Mechanics"
- Connes & Rovelli, "Von Neumann Algebra Automorphisms and Time-Thermodynamics"
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

-- Import the existing Bell machinery
import LogosLibrary.QuantumMechanics.BellsTheorem.LHV
import LogosLibrary.Relativity.Thermodynamics.Ott

open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Real BellTheorem

namespace ThermalBell

/-! ## Part 1: The Setting-Dependent Measure

The key modification: instead of one fixed measure μ on hidden variables,
we allow the measure to depend (weakly) on the measurement settings.

This is NOT superdeterminism in the conspiratorial sense — it's just
acknowledging that in a thermal universe, perfect screening is impossible.
-/

variable {Λ : Type*} [MeasurableSpace Λ]

/-- A response function for thermal models.
    Same as Bell's: maps hidden variable to ±1 outcome. -/
structure ResponseFunction (Λ : Type*) [MeasurableSpace Λ] (μ : Measure Λ) where
  toFun : Λ → ℝ
  measurable : Measurable toFun
  ae_pm_one : ∀ᵐ ω ∂μ, toFun ω = 1 ∨ toFun ω = -1
  integrable : Integrable toFun μ

instance : CoeFun (ResponseFunction Λ μ) (fun _ => Λ → ℝ) where
  coe f := f.toFun

/-- The correlation deviation function.

    ε(i,j,ω) measures how much the effective probability distribution
    deviates from the "base" distribution when settings (i,j) are chosen.-/
structure CorrelationDeviation (Λ : Type*) [MeasurableSpace Λ] (μ₀ : Measure Λ) where
  /-- The deviation function: ε(setting_A, setting_B, ω) -/
  ε : Fin 2 → Fin 2 → Λ → ℝ
  /-- ε is measurable in ω for each setting pair -/
  measurable : ∀ i j, Measurable (ε i j)
  /-- ε is bounded: |ε| < 1 to keep probabilities positive -/
  bounded : ∀ i j ω, |ε i j ω| < 1
  /-- ε integrates to zero (normalization): ∫ ε dμ₀ = 0 -/
  normalized : ∀ i j, ∫ ω, ε i j ω ∂μ₀ = 0
  /-- ε is integrable -/
  integrable : ∀ i j, Integrable (ε i j) μ₀

/-- A Thermal Hidden Variable Model -/
structure ThermalHVModel (Λ : Type*) [MeasurableSpace Λ] where
  /-- The base probability measure (the "would-be-independent" distribution) -/
  μ₀ : ProbabilityMeasure Λ
  /-- The correlation deviation from independence -/
  deviation : CorrelationDeviation Λ μ₀
  /-- Alice's response functions -/
  A : Fin 2 → ResponseFunction Λ μ₀
  /-- Bob's response functions -/
  B : Fin 2 → ResponseFunction Λ μ₀

variable (M : ThermalHVModel Λ)

/-- The effective measure for settings (i,j):
    dμᵢⱼ(ω) = (1 + ε(i,j,ω)) dμ₀(ω)-/
noncomputable def ThermalHVModel.effectiveMeasure
    (M : ThermalHVModel Λ) (i j : Fin 2) : Measure Λ :=
  (M.μ₀ : Measure Λ).withDensity (fun ω => ENNReal.ofReal (1 + M.deviation.ε i j ω))

/-- The effective measure is a probability measure -/
lemma ThermalHVModel.effectiveMeasure_isProbability
    (M : ThermalHVModel Λ) (i j : Fin 2) :
    IsProbabilityMeasure (M.effectiveMeasure i j) := by
  constructor
  simp only [effectiveMeasure]
  -- Key facts
  have hε_bounded := M.deviation.bounded i j
  have hε_normalized := M.deviation.normalized i j
  have hε_integrable := M.deviation.integrable i j
  have hμ₀_prob : IsProbabilityMeasure (M.μ₀ : Measure Λ) :=
    ProbabilityMeasure.instIsProbabilityMeasureToMeasure M.μ₀
  -- 1 + ε ≥ 0 since |ε| < 1
  have h_nonneg : ∀ ω, 0 ≤ 1 + M.deviation.ε i j ω := fun ω => by
    have := hε_bounded ω
    linarith [abs_lt.mp this]
  -- Convert to real integral
  have h_meas : Measurable (fun ω => (1 : ℝ) + M.deviation.ε i j ω) :=
    measurable_const.add (M.deviation.measurable i j)
  simp only [MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · -- Compute the integral
    rw [integral_add (integrable_const 1) hε_integrable]
    rw [integral_const, hε_normalized]
    simp only [measureReal_univ_eq_one, smul_eq_mul, mul_one, add_zero, ENNReal.ofReal_one]
  · -- Integrability
    exact (integrable_const 1).add hε_integrable
  · -- Almost everywhere nonnegativity
    exact Filter.Eventually.of_forall h_nonneg

/-- The correlation E(i,j) under the thermal model -/
noncomputable def ThermalHVModel.correlation
    (M : ThermalHVModel Λ) (i j : Fin 2) : ℝ :=
  ∫ ω, M.A i ω * M.B j ω * (1 + M.deviation.ε i j ω) ∂(M.μ₀ : Measure Λ)

/-- The CHSH value under the thermal model -/
noncomputable def ThermalHVModel.CHSH (M : ThermalHVModel Λ) : ℝ :=
  M.correlation 0 1 - M.correlation 0 0 + M.correlation 1 0 + M.correlation 1 1

end ThermalBell
