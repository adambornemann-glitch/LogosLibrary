/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: BellsTheorem/TLHV/Core.lean
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import LogosLibrary.QuantumMechanics.BellsTheorem.LHV
import LogosLibrary.QuantumMechanics.ModularTheory.KMS.Condition
import LogosLibrary.QuantumMechanics.ModularTheory.ThermalTime
/-!
# Thermal Hidden Variable Models — Core

## Synopsis

Bell's LHV model assumes statistical independence: ρ(λ|a,b) = ρ(λ).
In a universe with common causal origin, unscreenable gravity, and
finite-temperature thermal baths carrying KMS structure, perfect
independence is unphysical. This file formalizes the minimal relaxation.

## Architecture

We introduce a single parameter ε that controls the deviation from
independence. The CHSH value decomposes cleanly:

    S = S_classical + S_thermal

where |S_classical| ≤ 2 (Bell's bound) and |S_thermal| ≤ 4·ε_max.
Setting ε = 0 recovers the standard LHV framework exactly.

## Main Results

* `ThermalHVModel` — the model with setting-dependent measures
* `effectiveMeasure_isProbability` — the deformed measure is normalized

## References

* Bell, "Speakable and Unspeakable in Quantum Mechanics"
* 't Hooft, "The Cellular Automaton Interpretation of Quantum Mechanics"
* Connes, Rovelli, "Von Neumann Algebra Automorphisms and
  Time-Thermodynamics", CQG 11 (1994)

## Tags

Bell inequality, CHSH, hidden variables, thermal, KMS, measurement
independence
-/

open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Real BellTheorem

namespace ThermalBell

/-! ## Section 1: Model Definitions -/

variable {Λ : Type*} [MeasurableSpace Λ]

/-- A response function: maps hidden variable to ±1 outcome. -/
structure ResponseFunction (Λ : Type*) [MeasurableSpace Λ] (μ : Measure Λ) where
  toFun : Λ → ℝ
  measurable : Measurable toFun
  ae_pm_one : ∀ᵐ ω ∂μ, toFun ω = 1 ∨ toFun ω = -1
  integrable : Integrable toFun μ

instance : CoeFun (ResponseFunction Λ μ) (fun _ => Λ → ℝ) where
  coe f := f.toFun

/-- The correlation deviation from statistical independence.
    ε(i,j,ω) measures how much the effective distribution deviates
    from the base distribution when settings (i,j) are chosen. -/
structure CorrelationDeviation (Λ : Type*) [MeasurableSpace Λ] (μ₀ : Measure Λ) where
  ε : Fin 2 → Fin 2 → Λ → ℝ
  measurable : ∀ i j, Measurable (ε i j)
  bounded : ∀ i j ω, |ε i j ω| < 1
  normalized : ∀ i j, ∫ ω, ε i j ω ∂μ₀ = 0
  integrable : ∀ i j, Integrable (ε i j) μ₀

/-- A Thermal Hidden Variable Model: Bell + setting-dependent measure. -/
structure ThermalHVModel (Λ : Type*) [MeasurableSpace Λ] where
  μ₀ : ProbabilityMeasure Λ
  deviation : CorrelationDeviation Λ μ₀
  A : Fin 2 → ResponseFunction Λ μ₀
  B : Fin 2 → ResponseFunction Λ μ₀

variable (M : ThermalHVModel Λ)

/-! ## Section 2: Effective Measure and Correlations -/

/-- The effective measure for settings (i,j):
    dμ_{ij}(ω) = (1 + ε(i,j,ω)) dμ₀(ω). -/
noncomputable def ThermalHVModel.effectiveMeasure
    (M : ThermalHVModel Λ) (i j : Fin 2) : Measure Λ :=
  (M.μ₀ : Measure Λ).withDensity (fun ω => ENNReal.ofReal (1 + M.deviation.ε i j ω))

/-- The effective measure is a probability measure. -/
lemma ThermalHVModel.effectiveMeasure_isProbability
    (M : ThermalHVModel Λ) (i j : Fin 2) :
    IsProbabilityMeasure (M.effectiveMeasure i j) := by
  constructor
  simp only [effectiveMeasure]
  have hε_bounded := M.deviation.bounded i j
  have hε_normalized := M.deviation.normalized i j
  have hε_integrable := M.deviation.integrable i j
  have hμ₀_prob : IsProbabilityMeasure (M.μ₀ : Measure Λ) :=
    ProbabilityMeasure.instIsProbabilityMeasureToMeasure M.μ₀
  have h_nonneg : ∀ ω, 0 ≤ 1 + M.deviation.ε i j ω := fun ω => by
    have := hε_bounded ω; linarith [abs_lt.mp this]
  have h_meas : Measurable (fun ω => (1 : ℝ) + M.deviation.ε i j ω) :=
    measurable_const.add (M.deviation.measurable i j)
  simp only [MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_add (integrable_const 1) hε_integrable]
    rw [integral_const, hε_normalized]
    simp only [MeasureTheory.probReal_univ, smul_eq_mul, mul_one, add_zero, ENNReal.ofReal_one]
  · exact (integrable_const 1).add hε_integrable
  · exact Filter.Eventually.of_forall h_nonneg

/-- The correlation E(i,j) under the thermal model. -/
noncomputable def ThermalHVModel.correlation
    (M : ThermalHVModel Λ) (i j : Fin 2) : ℝ :=
  ∫ ω, M.A i ω * M.B j ω * (1 + M.deviation.ε i j ω) ∂(M.μ₀ : Measure Λ)

/-- The CHSH value: S = E₀₁ - E₀₀ + E₁₀ + E₁₁. -/
noncomputable def ThermalHVModel.CHSH (M : ThermalHVModel Λ) : ℝ :=
  M.correlation 0 1 - M.correlation 0 0 + M.correlation 1 0 + M.correlation 1 1

/-! ## Section 3: CHSH Decomposition

The key structural result: CHSH decomposes into a classical part
(which is bounded by Bell's theorem) and a thermal correction
(which is bounded by ε_max).
-/

/-- The pointwise CHSH value. -/
def chsh_pointwise (a₀ a₁ b₀ b₁ : ℝ) : ℝ :=
  a₀ * b₁ - a₀ * b₀ + a₁ * b₀ + a₁ * b₁

/-- All achievable pointwise CHSH values for dichotomic inputs. -/
lemma chsh_pointwise_values (a₀ a₁ b₀ b₁ : ℝ)
    (ha₀ : a₀ = 1 ∨ a₀ = -1) (ha₁ : a₁ = 1 ∨ a₁ = -1)
    (hb₀ : b₀ = 1 ∨ b₀ = -1) (hb₁ : b₁ = 1 ∨ b₁ = -1) :
    chsh_pointwise a₀ a₁ b₀ b₁ = 2 ∨ chsh_pointwise a₀ a₁ b₀ b₁ = -2 := by
  unfold chsh_pointwise
  rcases ha₀ with rfl | rfl <;> rcases ha₁ with rfl | rfl <;>
  rcases hb₀ with rfl | rfl <;> rcases hb₁ with rfl | rfl <;>
  simp <;> ring_nf <;> simp

/-- The classical part of CHSH: what you get ignoring ε. -/
noncomputable def ThermalHVModel.CHSH_classical (M : ThermalHVModel Λ) : ℝ :=
  ∫ ω, (M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω +
         M.A 1 ω * M.B 0 ω + M.A 1 ω * M.B 1 ω) ∂(M.μ₀ : Measure Λ)

/-- The thermal correction to CHSH: the contribution from ε. -/
noncomputable def ThermalHVModel.CHSH_thermal (M : ThermalHVModel Λ) : ℝ :=
  ∫ ω, (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
         M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
         M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
         M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ)


end ThermalBell
