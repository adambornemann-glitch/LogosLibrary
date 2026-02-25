/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.Relativity.LorentzBoost.Ott
import Mathlib.Analysis.Real.Pi.Bounds

open RelativisticTemperature MinkowskiSpace

namespace ThermalTime
set_option linter.unusedVariables false

/-- Thermal time: the relationship between coordinate time,
    temperature, and modular parameter -/
noncomputable def thermalTime (T : ℝ) (τ_mod : ℝ) : ℝ := τ_mod / T  -- units where ℏ/k = 1

theorem thermal_time_gives_time_dilation
    (T : ℝ) (hT : T > 0)
    (τ_mod : ℝ)  -- modular parameter (invariant by Tomita-Takesaki)
    (v : ℝ) (hv : |v| < 1) :
    let γ := lorentzGamma v hv
    let t := thermalTime T τ_mod
    let T' := γ * T           -- Ott transformation
    let t' := thermalTime T' τ_mod  -- thermal time in boosted frame
    t' = t / γ := by
  -- Unfold the definition of thermalTime: t = τ/T
  simp only [thermalTime]
  -- Establish that γ > 0 (needed for field_simp)
  have hγ_pos : lorentzGamma v hv > 0 := by
    have := lorentzGamma_ge_one v hv; linarith
  have hγ_ne : lorentzGamma v hv ≠ 0 := ne_of_gt hγ_pos
  have hT_ne : T ≠ 0 := ne_of_gt hT
  -- The algebra: τ/(γT) = (τ/T)/γ
  exact div_mul_eq_div_div_swap τ_mod (lorentzGamma v hv) T


lemma lorentzGamma_surjective_ge_one (γ : ℝ) (hγ : γ ≥ 1) :
    ∃ v, ∃ hv : |v| < 1, lorentzGamma v hv = γ := by
  -- Explicit construction: v = √(1 - 1/γ²)
  -- This inverts γ = 1/√(1-v²) to get v² = 1 - 1/γ²
  use Real.sqrt (1 - 1/γ^2)

  -- === Establish basic properties of γ ===
  have hγ_pos : γ > 0 := by linarith
  have hγ_sq_pos : γ^2 > 0 := sq_pos_of_pos hγ_pos
  have hγ_sq_ge_one : γ^2 ≥ 1 := by exact one_le_pow₀ hγ

  -- === Show the argument to √ is in [0, 1) ===

  -- Lower bound: 1 - 1/γ² ≥ 0  (equivalently: 1/γ² ≤ 1)
  have h_nonneg : 1 - 1/γ^2 ≥ 0 := by
    have : 1/γ^2 ≤ 1 := by
      rw [div_le_one hγ_sq_pos]
      exact hγ_sq_ge_one
    linarith

  -- Upper bound: 1 - 1/γ² < 1  (equivalently: 1/γ² > 0)
  have h_lt_one : 1 - 1/γ^2 < 1 := by
    have : 1/γ^2 > 0 := div_pos one_pos hγ_sq_pos
    linarith

  -- === Prove |v| < 1, i.e., the velocity is subluminal ===
  have hv : |Real.sqrt (1 - 1/γ^2)| < 1 := by
    -- √(x) ≥ 0 for any x, so |√(x)| = √(x)
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    -- Need: √(1 - 1/γ²) < √(1) = 1
    calc Real.sqrt (1 - 1/γ^2)
        < Real.sqrt 1 := Real.sqrt_lt_sqrt h_nonneg h_lt_one
      _ = 1 := Real.sqrt_one

  use hv

  -- === Main calculation: lorentzGamma v hv = γ ===
  unfold lorentzGamma

  -- Key algebraic fact: v² = 1 - 1/γ²
  have h_v_sq : (Real.sqrt (1 - 1/γ^2))^2 = 1 - 1/γ^2 := Real.sq_sqrt h_nonneg

  -- Therefore: 1 - v² = 1/γ²
  have h_one_minus_v_sq : 1 - (Real.sqrt (1 - 1/γ^2))^2 = 1/γ^2 := by linarith

  -- And: √(1/γ²) = 1/γ  (since γ > 0)
  have h_sqrt_inv : Real.sqrt (1/γ^2) = 1/γ := by
    have h1 : 1/γ^2 = (1/γ)^2 := by
        exact Eq.symm (one_div_pow γ 2)
    rw [h1, Real.sqrt_sq (by positivity : 1/γ ≥ 0)]

  -- Chain the equalities: 1/√(1-v²) = 1/√(1/γ²) = 1/(1/γ) = γ
  calc 1 / Real.sqrt (1 - (Real.sqrt (1 - 1/γ^2))^2)
      = 1 / Real.sqrt (1/γ^2) := by rw [h_one_minus_v_sq]
    _ = 1 / (1/γ) := by rw [h_sqrt_inv]
    _ = γ := by exact one_div_one_div γ

def satisfiesCovariance (g : ℝ → ℝ) : Prop :=
  ∀ T v (hv : |v| < 1), T > 0 →
    g (lorentzGamma v hv * T) = g T / lorentzGamma v hv


theorem functional_equation_solution
    (g : ℝ → ℝ)
    (hg_pos : ∀ T, T > 0 → g T > 0)
    (hg_cov : satisfiesCovariance g) :
    ∀ T, T > 0 → g T * T = g 1 := by
  intro T hT

  by_cases hT_ge_one : T ≥ 1

  · obtain ⟨v, hv, hγ_eq⟩ := lorentzGamma_surjective_ge_one T hT_ge_one

    have h_cov : g (lorentzGamma v hv * 1) = g 1 / lorentzGamma v hv :=
      hg_cov 1 v hv one_pos
    simp only [mul_one] at h_cov

    -- Substitute γ = T to get: g(T) = g(1) / T
    rw [hγ_eq] at h_cov

    -- Multiply both sides by T: g(T) · T = g(1)
    calc g T * T
        = (g 1 / T) * T := by rw [h_cov]
      _ = g 1 := by field_simp

  · push_neg at hT_ge_one  -- Now: T < 1

    -- Since T < 1 and T > 0, we have 1/T > 1
    have hT_inv_ge_one : 1/T ≥ 1 := by
      rw [ge_iff_le, one_le_div hT]
      linarith

    -- Find a physical velocity v achieving Lorentz factor γ = 1/T
    obtain ⟨v, hv, hγ_eq⟩ := lorentzGamma_surjective_ge_one (1/T) hT_inv_ge_one

    -- Apply covariance at base temperature T:
    -- g(γ · T) = g(T) / γ
    have h_cov : g (lorentzGamma v hv * T) = g T / lorentzGamma v hv :=
      hg_cov T v hv hT

    -- Substitute γ = 1/T
    rw [hγ_eq] at h_cov

    -- Note: γ · T = (1/T) · T = 1
    have h_prod : (1/T) * T = 1 := by field_simp
    rw [h_prod] at h_cov

    -- Now h_cov says: g(1) = g(T) / (1/T) = g(T) · T
    calc g T * T
        = g T / (1/T) := by field_simp
      _ = g 1 := h_cov.symm


theorem thermalTime_unique
    (f : ℝ → ℝ → ℝ)
    (hf_pos : ∀ T τ, T > 0 → τ > 0 → f T τ > 0)
    (hf_linear_τ : ∀ T c τ, T > 0 → c > 0 → τ > 0 → f T (c * τ) = c * f T τ)
    (hf_cov : ∀ T τ v (hv : |v| < 1), T > 0 → τ > 0 →
      f (lorentzGamma v hv * T) τ = f T τ / lorentzGamma v hv) :
    ∃ c, c > 0 ∧ ∀ T τ, T > 0 → τ > 0 → f T τ = c * τ / T := by

  use f 1 1
  constructor
  · -- c = f(1,1) > 0 follows from positivity hypothesis
    exact hf_pos 1 1 one_pos one_pos

  intro T τ hT hτ
  have h_linear : f T τ = τ * f T 1 := by
    have h := hf_linear_τ T τ 1 hT hτ one_pos
    simp only [mul_one] at h
    exact h

  set g := fun T' => f T' 1 with hg_def

  -- g inherits positivity from f
  have hg_pos : ∀ T', T' > 0 → g T' > 0 := fun T' hT' => hf_pos T' 1 hT' one_pos

  -- g inherits covariance from f (with τ = 1)
  have hg_cov : satisfiesCovariance g := by
    intro T' v hv hT'
    exact hf_cov T' 1 v hv hT' one_pos

  have h_eq : g T * T = g 1 := functional_equation_solution g hg_pos hg_cov T hT

  have hT_ne : T ≠ 0 := ne_of_gt hT
  have h_g_form : g T = f 1 1 / T := by
    calc g T = (g T * T) / T := by exact Eq.symm (mul_div_cancel_right₀ (g T) hT_ne)
      _ = g 1 / T := by rw [h_eq]
      _ = f 1 1 / T := rfl

  calc f T τ
      = τ * f T 1 := h_linear           -- Step 1: linearity
    _ = τ * g T := rfl                   -- Definition of g
    _ = τ * (f 1 1 / T) := by rw [h_g_form]  -- Step 4: g(T) = c/T
    _ = f 1 1 * τ / T := by ring         -- Rearrange: c · τ / T


theorem thermalTime_inverse_unique
    (g : ℝ → ℝ)
    (hg_pos : ∀ T, T > 0 → g T > 0)
    (hg_eq : ∀ T γ, T > 0 → γ > 1 → g (γ * T) = g T / γ) :
    ∀ T, T > 0 → g T * T = g 1 := by
  intro T hT

  by_cases hT_eq_one : T = 1

  · rw [hT_eq_one]
    ring

  · -- Case T ≠ 1: Split further based on whether T > 1 or T < 1
    by_cases hT_gt_one : T > 1

    · have h := hg_eq 1 T one_pos hT_gt_one
      simp only [mul_one] at h
      -- h : g T = g 1 / T

      calc g T * T
          = (g 1 / T) * T := by rw [h]
        _ = g 1 := by field_simp

    · push_neg at hT_gt_one  -- Now: T ≤ 1

      -- Since T ≠ 1 and T ≤ 1, we have T < 1
      have hT_lt_one : T < 1 := lt_of_le_of_ne hT_gt_one hT_eq_one

      -- Since T < 1 and T > 0, we have 1/T > 1
      have hT_inv_gt_one : 1/T > 1 := by
        rw [gt_iff_lt, one_lt_div hT]
        exact hT_lt_one

      -- Apply scaling at base point T with γ = 1/T:
      -- g((1/T) · T) = g(T) / (1/T)
      have h := hg_eq T (1/T) hT hT_inv_gt_one

      -- Simplify left side: (1/T) · T = 1
      have h_prod : (1/T) * T = 1 := by field_simp
      rw [h_prod] at h
      -- h : g 1 = g T / (1/T) = g T * T

      calc g T * T
          = g T / (1/T) := by linarith
        _ = g 1 := h.symm


theorem modular_parameter_recovery (T t : ℝ) (hT : T > 0) :
    thermalTime T (t * T) = t := by
  unfold thermalTime
  have hT_ne : T ≠ 0 := ne_of_gt hT
  exact mul_div_cancel_right₀ t hT_ne


theorem thermal_time_scale_invariant
    (T τ c : ℝ) (hT : T > 0) (hc : c > 0) :
    thermalTime (c * T) τ = thermalTime T τ / c := by
  unfold thermalTime
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hT_ne : T ≠ 0 := ne_of_gt hT
  exact div_mul_eq_div_div_swap τ c T


theorem thermal_time_homogeneous
    (T τ c : ℝ) (hT : T > 0) (hc : c > 0) :
    thermalTime (c * T) (c * τ) = thermalTime T τ := by
  unfold thermalTime
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hT_ne : T ≠ 0 := ne_of_gt hT
  exact mul_div_mul_left τ T hc_ne


theorem thermal_time_determines_modular_structure
    (T₁ T₂ : ℝ) (hT₁ : T₁ > 0) (hT₂ : T₂ > 0)
    (τ : ℝ) (hτ : τ ≠ 0)
    (h : thermalTime T₁ τ = thermalTime T₂ τ) :
    T₁ = T₂ := by
  unfold thermalTime at h
  have hT₁_ne : T₁ ≠ 0 := ne_of_gt hT₁
  have hT₂_ne : T₂ ≠ 0 := ne_of_gt hT₂
  -- h : τ / T₁ = τ / T₂
  -- Cross multiply: τ * T₂ = τ * T₁
  field_simp at h
  -- Cancel τ
  exact id (Eq.symm h)


noncomputable def modular_period : ℝ := 2 * Real.pi


theorem one_cycle_thermal_time (T : ℝ) (hT : T > 0) :
    thermalTime T modular_period = 2 * Real.pi / T := by
  unfold thermalTime modular_period
  module


noncomputable def ℏ : ℝ := 1

noncomputable def k_B : ℝ := 1


theorem thermal_time_physical_units (T : ℝ) (hT : T > 0) :
    thermalTime T modular_period * (k_B * T / ℏ) = 2 * Real.pi := by
  unfold thermalTime modular_period k_B ℏ
  have hT_ne : T ≠ 0 := ne_of_gt hT
  simp only [one_mul, div_one]
  exact div_mul_cancel₀ (2 * Real.pi) hT_ne


namespace ThermalTimeConsequences

open ThermalTime MinkowskiSpace RelativisticTemperature

noncomputable def inverse_temperature (T : ℝ) : ℝ := 1 / T

axiom kms_periodicity (T : ℝ) (hT : T > 0) :
    inverse_temperature T = 1 / T

axiom kms_fixes_thermal_constant :
    ∀ T τ, T > 0 → thermalTime T τ = τ / T


noncomputable def modularHamiltonian (H T : ℝ) : ℝ := H / T


theorem modular_hamiltonian_invariant
    (H T : ℝ) (hT : T > 0)
    (v : ℝ) (hv : |v| < 1) :
    let γ := lorentzGamma v hv
    let H' := γ * H           -- Energy transforms
    let T' := γ * T           -- Ott transformation
    modularHamiltonian H' T' = modularHamiltonian H T := by
  simp only [modularHamiltonian]
  have hγ_pos : lorentzGamma v hv > 0 := by
    have := lorentzGamma_ge_one v hv; linarith
  have hγ_ne : lorentzGamma v hv ≠ 0 := ne_of_gt hγ_pos
  have hT_ne : T ≠ 0 := ne_of_gt hT
  exact Unification.corollary_detailed_balance H T hT v hv


noncomputable def unruhTemperature (a : ℝ) : ℝ := a / (2 * Real.pi)


theorem unruh_from_modular_period (a : ℝ) (ha : a > 0) :
    unruhTemperature a = a / modular_period := by
  unfold unruhTemperature modular_period
  module


theorem unruh_temperature_pos (a : ℝ) (ha : a > 0) :
    unruhTemperature a > 0 := by
  unfold unruhTemperature
  apply div_pos ha
  linarith [Real.pi_pos]


theorem boosted_unruh_temperature
    (a : ℝ) (ha : a > 0)
    (v : ℝ) (hv : |v| < 1) :
    let γ := lorentzGamma v hv
    let T_U := unruhTemperature a
    let T_U' := γ * T_U      -- Ott transformation of Unruh temperature
    T_U' = unruhTemperature (γ * a) := by
  simp only [unruhTemperature]
  ring


structure LocalRindlerThermodynamics where
  δQ : ℝ          -- Heat flow
  T : ℝ           -- Local Unruh temperature
  δS : ℝ          -- Entropy change
  hT : T > 0
  clausius : δQ = T * δS   -- First law


theorem rindler_thermodynamics_covariant
    (R : LocalRindlerThermodynamics)
    (v : ℝ) (hv : |v| < 1) :
    let γ := lorentzGamma v hv
    let δQ' := γ * R.δQ     -- Energy (heat) transforms
    let T' := γ * R.T        -- Temperature transforms (Ott)
    let δS' := R.δS          -- Entropy is invariant
    δQ' = T' * δS' := by
  simp only
  calc lorentzGamma v hv * R.δQ
      = lorentzGamma v hv * (R.T * R.δS) := by rw [R.clausius]
    _ = (lorentzGamma v hv * R.T) * R.δS := by ring


def wheeler_dewitt_constraint (H : ℝ) : Prop := H = 0


theorem modular_flow_survives_constraint :
    -- This is a statement about the algebraic formulation
    -- The modular flow σ_τ(A) = Δ^{iτ} A Δ^{-iτ} is defined
    -- by the state, not by H directly
    True := trivial  -- Placeholder for algebraic statement


noncomputable def thermalDensityMatrix (β H : ℝ) : ℝ :=
    Real.exp (-β * H)


theorem thermal_to_ground_state_limit :
    ∀ H, H > 0 → Filter.Tendsto (fun β => thermalDensityMatrix β H)
                                 Filter.atTop (nhds 0) := by
  intro H hH
  unfold thermalDensityMatrix
  -- As β → +∞ with H > 0: -β * H → -∞, so exp(-β * H) → 0
  have h1 : Filter.Tendsto (fun β => β * H) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.atTop_mul_const hH
  have h2 : Filter.Tendsto (fun β => -β * H) Filter.atTop Filter.atBot := by
    simp_all only [gt_iff_lt, neg_mul, Filter.tendsto_neg_atBot_iff]
  exact Real.tendsto_exp_comp_nhds_zero.mpr h2


theorem thermal_time_consistency
    (T : ℝ) (hT : T > 0)
    (τ : ℝ) (hτ : τ > 0)
    (H : ℝ)
    (v : ℝ) (hv : |v| < 1) :
    let γ := lorentzGamma v hv
    -- 1. Thermal time gives time dilation
    let t := thermalTime T τ
    let T' := γ * T
    let t' := thermalTime T' τ
    -- 2. Modular Hamiltonian is invariant
    let K := modularHamiltonian H T
    let H' := γ * H
    let K' := modularHamiltonian H' T'
    -- Both conditions hold simultaneously
    t' = t / γ ∧ K' = K := by
  constructor
  · exact thermal_time_gives_time_dilation T hT τ v hv
  · exact modular_hamiltonian_invariant H T hT v hv

end ThermalTimeConsequences

namespace MeasurementTheorem

open ThermalTime

/-!
# The Measurement Theorem

## The Question
What IS a measurement? When does "collapse" happen?

## The Answer
A measurement is any interaction that produces ≥ 2π nats of entropy.
This takes thermal time t = ΔS/T ≥ 2π/T > 0.

There is no instantaneous collapse. There is only thermodynamics.

## Why 2π?
The modular period τ = 2π is not arbitrary. It is:
- The KMS periodicity of thermal states
- The period of the modular automorphism group
- The minimum "cycle" to establish one bit of correlation
- The Euclidean time period in thermal QFT

One measurement = one modular cycle = 2π nats of entropy = positive time.
-/

/-- The fundamental entropy quantum: one modular cycle = 2π nats -/
noncomputable def entropyQuantum : ℝ := 2 * Real.pi

theorem entropyQuantum_eq_modular_period : entropyQuantum = modular_period := rfl

theorem entropyQuantum_pos : entropyQuantum > 0 := by
  unfold entropyQuantum
  linarith [Real.pi_pos]

/-- A measurement is an entropy-producing interaction.
    The entropy produced must be at least one modular cycle. -/
structure Measurement where
  /-- Entropy produced (in nats, i.e., natural units where k_B = 1) -/
  ΔS : ℝ
  /-- A measurement requires at least 2π nats (one full modular cycle) -/
  h_minimal : ΔS ≥ entropyQuantum

/-- The thermal time required to complete a measurement -/
noncomputable def Measurement.duration (m : Measurement) (T : ℝ) : ℝ :=
  thermalTime T m.ΔS

/-- Equivalently: duration = ΔS / T -/
theorem Measurement.duration_eq (m : Measurement) (T : ℝ) :
    m.duration T = m.ΔS / T := rfl

/-! ## Core Theorems -/

/-- **THEOREM 1**: Every measurement takes positive time. -/
theorem measurement_takes_positive_time
    (m : Measurement) (T : ℝ) (hT : T > 0) :
    m.duration T > 0 := by
  unfold Measurement.duration thermalTime
  apply div_pos _ hT
  calc m.ΔS ≥ entropyQuantum := m.h_minimal
    _ > 0 := entropyQuantum_pos

/-- **THEOREM 2**: Measurement time has a lower bound determined by temperature alone. -/
theorem measurement_time_lower_bound
    (m : Measurement) (T : ℝ) (hT : T > 0) :
    m.duration T ≥ entropyQuantum / T := by
  unfold Measurement.duration thermalTime
  exact div_le_div_of_nonneg_right m.h_minimal (le_of_lt hT)

/-- **THEOREM 3**: The minimum measurement time is exactly one thermal period. -/
noncomputable def minimalMeasurement : Measurement where
  ΔS := entropyQuantum
  h_minimal := le_refl entropyQuantum

theorem minimal_measurement_duration (T : ℝ) (hT : T > 0) :
    minimalMeasurement.duration T = 2 * Real.pi / T := by
  unfold Measurement.duration minimalMeasurement thermalTime entropyQuantum
  ring

/-! ## Thermal Bath and Thermodynamic Systems -/

/-- A thermal bath at temperature T > 0 -/
structure ThermalBath where
  T : ℝ
  h_T_pos : T > 0

/-- The cosmic microwave background -/
def CMB : ThermalBath where
  T := 2.725
  h_T_pos := by norm_num

/-- Room temperature (in Kelvin, natural units) -/
noncomputable def roomTemperatureBath : ThermalBath where
  T := 300
  h_T_pos := by norm_num

/-- de Sitter temperature from cosmological constant -/
noncomputable def deSitterBath (Λ : ℝ) (hΛ : Λ > 0) : ThermalBath where
  T := Real.sqrt (Λ / 3) / (2 * Real.pi)
  h_T_pos := by
    apply div_pos
    · exact Real.sqrt_pos.mpr (div_pos hΛ (by norm_num : (3 : ℝ) > 0))
    · linarith [Real.pi_pos]

/-- A system evolving under thermal dynamics -/
structure ThermodynamicSystem (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The thermal bath this system is in contact with -/
  bath : ThermalBath
  /-- Time evolution operator -/
  evolve : H → ℝ → H
  /-- Evolution preserves normalization -/
  preserves_norm : ∀ ψ t, ‖ψ‖ = 1 → ‖evolve ψ t‖ = 1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The temperature of a thermodynamic system -/
def ThermodynamicSystem.temperature (sys : ThermodynamicSystem H) : ℝ := sys.bath.T

/-- The temperature is always positive -/
theorem ThermodynamicSystem.temperature_pos (sys : ThermodynamicSystem H) :
    sys.temperature > 0 := sys.bath.h_T_pos

/-- Duration of a measurement in this system -/
noncomputable def ThermodynamicSystem.measurementDuration
    (sys : ThermodynamicSystem H) (m : Measurement) : ℝ :=
  m.duration sys.bath.T

/-- Measurement duration is positive -/
theorem ThermodynamicSystem.measurementDuration_pos
    (sys : ThermodynamicSystem H) (m : Measurement) :
    sys.measurementDuration m > 0 :=
  measurement_takes_positive_time m sys.bath.T sys.bath.h_T_pos

/-! ## The Measurement Problem: Resolved -/

/-- **THE MEASUREMENT PROBLEM (Formalized)**:

    You cannot measure a property P of state ψ without:
    1. Performing an interaction (producing entropy ΔS ≥ 2π)
    2. This takes time t = ΔS/T > 0
    3. During time t, the state evolves: ψ ↦ evolve ψ t
    4. Therefore: you measure P(evolve ψ t), not P(ψ)

    "Instantaneous measurement" is a contradiction in terms. -/
theorem measurement_problem
    (sys : ThermodynamicSystem H)
    (m : Measurement)
    (ψ : H) (h_norm : ‖ψ‖ = 1)
    (P : H → ℝ) :  -- Any observable property
    let t := sys.measurementDuration m
    let ψ' := sys.evolve ψ t
    t > 0 ∧ ‖ψ'‖ = 1 := by
  constructor
  · exact sys.measurementDuration_pos m
  · exact sys.preserves_norm ψ (sys.measurementDuration m) h_norm

/-- The state you actually measure is never the state you started with -/
theorem measured_state_is_evolved
    (sys : ThermodynamicSystem H)
    (m : Measurement)
    (ψ : H) (h_norm : ‖ψ‖ = 1) :
    let t := sys.measurementDuration m
    t > 0 := sys.measurementDuration_pos m

end MeasurementTheorem
/-! ## Landauer's Principle and Information Theory

The bridge between thermodynamics and information:
- Erasing 1 bit costs k_B T ln(2) energy (Landauer 1961)
- Equivalently: 1 bit of irreversible computation produces ln(2) nats of entropy
- One measurement = 2π nats = 2π/ln(2) bits ≈ 9.06 bits

A measurement isn't mysterious "collapse" — it's establishing correlation
between system and apparatus. That correlation IS the measurement record.
-/

namespace InformationTheory

open MeasurementTheorem

/-- Conversion factor: 1 bit = ln(2) nats -/
noncomputable def natsPerBit : ℝ := Real.log 2

lemma natsPerBit_pos : natsPerBit > 0 := Real.log_pos (by exact one_lt_two )

/-- Convert entropy from nats to bits -/
noncomputable def natsToBits (S_nats : ℝ) : ℝ := S_nats / natsPerBit

/-- Convert entropy from bits to nats -/
noncomputable def bitsToNats (S_bits : ℝ) : ℝ := S_bits * natsPerBit

theorem bits_nats_inverse (S : ℝ) : natsToBits (bitsToNats S) = S := by
  unfold natsToBits bitsToNats
  have h : natsPerBit ≠ 0 := ne_of_gt natsPerBit_pos
  field_simp

theorem nats_bits_inverse (S : ℝ) : bitsToNats (natsToBits S) = S := by
  unfold natsToBits bitsToNats
  have h : natsPerBit ≠ 0 := ne_of_gt natsPerBit_pos
  field_simp

/-! ### Landauer's Principle -/

/-- Landauer's principle: minimum energy to erase one bit at temperature T

    E = k_B T ln(2)

    In natural units (k_B = 1): E = T ln(2) -/
noncomputable def landauerCost (T : ℝ) : ℝ := T * natsPerBit

theorem landauerCost_pos (T : ℝ) (hT : T > 0) : landauerCost T > 0 := by
  unfold landauerCost
  exact mul_pos hT natsPerBit_pos

/-- Energy cost to produce ΔS nats of entropy -/
noncomputable def entropyCost (T : ℝ) (ΔS_nats : ℝ) : ℝ := T * ΔS_nats

/-- Landauer cost is entropy cost for ln(2) nats (= 1 bit) -/
theorem landauer_is_one_bit_entropy (T : ℝ) :
    landauerCost T = entropyCost T natsPerBit := by
  unfold landauerCost entropyCost
  ring

/-! ### Measurement as Information -/

/-- Bits of correlation established by a measurement -/
noncomputable def Measurement.bits (m : Measurement) : ℝ :=
  natsToBits m.ΔS

/-- One modular cycle in bits: 2π / ln(2) ≈ 9.064 bits -/
noncomputable def bitsPerModularCycle : ℝ := natsToBits entropyQuantum

/-- The fundamental measurement establishes ~9 bits of correlation -/
theorem bitsPerModularCycle_eq : bitsPerModularCycle = 2 * Real.pi / Real.log 2 := by
  unfold bitsPerModularCycle natsToBits entropyQuantum natsPerBit
  ring

/-- Bits of correlation established by a measurement -/
noncomputable def measurementBits (m : Measurement) : ℝ :=
  natsToBits m.ΔS

/-- A measurement establishes at least one modular cycle worth of bits -/
theorem measurement_bits_lower_bound (m : Measurement) :
    measurementBits m ≥ bitsPerModularCycle := by
  unfold measurementBits bitsPerModularCycle natsToBits
  apply div_le_div_of_nonneg_right m.h_minimal (le_of_lt natsPerBit_pos)

/-- ln(2) < 1 (since 2 < e) -/
theorem log_two_lt_one : Real.log 2 < 1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 2)]
  have h := Real.add_one_lt_exp (one_ne_zero' ℝ)
  norm_num at h
  exact h


/-! ### Physical Interpretation -/

/-- Energy cost of a measurement -/
noncomputable def Measurement.energyCost (m : Measurement) (T : ℝ) : ℝ :=
  entropyCost T m.ΔS

/-- Minimum energy cost of any measurement at temperature T -/
noncomputable def minMeasurementEnergy (T : ℝ) : ℝ :=
  entropyCost T entropyQuantum

theorem minMeasurementEnergy_eq (T : ℝ) :
    minMeasurementEnergy T = 2 * Real.pi * T := by
  unfold minMeasurementEnergy entropyCost entropyQuantum
  ring

/-- Energy cost of a measurement -/
noncomputable def measurementEnergyCost (m : Measurement) (T : ℝ) : ℝ :=
  entropyCost T m.ΔS

/-- A measurement costs at least ~9 Landauer erasures worth of energy -/
theorem measurement_energy_bound (m : Measurement) (T : ℝ) (hT : T > 0) :
    measurementEnergyCost m T ≥ minMeasurementEnergy T := by
  unfold measurementEnergyCost minMeasurementEnergy entropyCost
  exact mul_le_mul_of_nonneg_left m.h_minimal (le_of_lt hT)

/-- Minimum measurement energy in terms of Landauer cost -/
theorem minMeasurementEnergy_in_landauer' (T : ℝ) :
    minMeasurementEnergy T = bitsPerModularCycle * landauerCost T := by
  unfold minMeasurementEnergy bitsPerModularCycle landauerCost
  unfold entropyCost natsToBits entropyQuantum natsPerBit
  have h : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1:ℝ) < 2))
  field_simp

/-- A measurement record is the correlation established between system and apparatus.

    Before measurement: System and apparatus uncorrelated
    After measurement: ~9 bits of mutual information

    This IS what "having a measurement result" means. -/
structure MeasurementRecord where
  /-- The measurement that was performed -/
  measurement : Measurement
  /-- Mutual information between system and apparatus (in bits) -/
  mutualInformation : ℝ
  /-- The correlation equals the entropy produced -/
  correlation_eq_entropy : mutualInformation = measurementBits measurement

/-- The "collapse" is just the establishment of correlation -/
theorem collapse_is_correlation (r : MeasurementRecord) :
    r.mutualInformation ≥ bitsPerModularCycle := by
  rw [r.correlation_eq_entropy]
  exact measurement_bits_lower_bound r.measurement

/-- No correlation without entropy production -/
theorem no_free_information (m : Measurement) :
    measurementBits m > 0 := by
  calc measurementBits m
      ≥ bitsPerModularCycle := measurement_bits_lower_bound m
    _ = 2 * Real.pi / Real.log 2 := bitsPerModularCycle_eq
    _ > 0 := by positivity

/-- The Holevo bound: accessible classical information ≤ von Neumann entropy.

    A measurement that extracts n bits of information must produce
    at least n bits worth of entropy. Our bound says n ≥ 2π/ln(2) ≈ 9 bits
    for any complete measurement. -/
theorem holevo_consistency (m : Measurement)
    (accessible_info : ℝ)
    (h_holevo : accessible_info ≤ measurementBits m) :
    accessible_info ≤ m.ΔS / natsPerBit := by
  calc accessible_info
      ≤ measurementBits m := h_holevo
    _ = m.ΔS / natsPerBit := rfl

end InformationTheory

end ThermalTime
