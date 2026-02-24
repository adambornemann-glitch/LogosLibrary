/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.Relativity.LorentzBoost.Ott
import Mathlib.Analysis.Real.Pi.Bounds

open RelativisticTemperature MinkowskiSpace

namespace ThermalTime.Basic
set_option linter.unusedVariables false

/-- Thermal time: the relationship between coordinate time,
    temperature, and modular parameter -/
noncomputable def thermalTime (T : ℝ) (τ_mod : ℝ) : ℝ := τ_mod / T  -- units where ℏ/k = 1
noncomputable def modular_period : ℝ := 2 * Real.pi
noncomputable def ℏ : ℝ := 1
noncomputable def k_B : ℝ := 1

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

theorem one_cycle_thermal_time (T : ℝ) (hT : T > 0) :
    thermalTime T modular_period = 2 * Real.pi / T := by
  unfold thermalTime modular_period
  module

theorem thermal_time_physical_units (T : ℝ) (hT : T > 0) :
    thermalTime T modular_period * (k_B * T / ℏ) = 2 * Real.pi := by
  unfold thermalTime modular_period k_B ℏ
  have hT_ne : T ≠ 0 := ne_of_gt hT
  simp only [one_mul, div_one]
  exact div_mul_cancel₀ (2 * Real.pi) hT_ne

end ThermalTime.Basic
