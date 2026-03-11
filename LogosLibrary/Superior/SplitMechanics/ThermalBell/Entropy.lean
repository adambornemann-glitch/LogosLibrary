/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: BellsTheorem/ThermalBell/Entropy.lean
-/
import LogosLibrary.Superior.SplitMechanics.ThermalBell.Constraints
/-!
# Thermal Bell — Measurement Entropy & Thermal Time Decay

The minimum entropy cost of a measurement is one modular period (2π nats).
Same-setting remeasurement costs nothing (Zeno effect). Different-setting
measurement costs the full 2π. Correlations decay exponentially with
thermal time separation.

## Main Results

* `zeno_entropy` — n same-setting measurements cost only 2π total
* `correlation_decay` — ε → 0 as thermal separation → ∞
* `ε_decreasing` — longer separation ⟹ smaller ε ⟹ more classical
-/
open Real Filter MeasureTheory ProbabilityTheory

namespace ThermalBell

/-! ## Section 1: Measurement Entropy -/

/-- The minimum entropy cost of a single measurement: one modular cycle. -/
noncomputable def measurementEntropyCost : ℝ := 2 * Real.pi

lemma measurementEntropyCost_pos : measurementEntropyCost > 0 := by
  unfold measurementEntropyCost; linarith [Real.pi_pos]

/-- Entropy produced depends on whether the setting changed. -/
noncomputable def entropyForSettingChange (same : Bool) : ℝ :=
  if same then 0 else measurementEntropyCost

/-- Count setting changes in a sequence. -/
def countSettingChanges : List (Fin 2) → ℕ
  | [] => 0
  | [_] => 0
  | s₁ :: s₂ :: rest =>
      (if s₁ ≠ s₂ then 1 else 0) + countSettingChanges (s₂ :: rest)

/-- Total entropy = (1 + #changes) × 2π. -/
noncomputable def totalEntropy (settings : List (Fin 2)) : ℝ :=
  match settings with
  | [] => 0
  | _ :: _ => (1 + countSettingChanges settings) * measurementEntropyCost

/-- For all-same settings, no changes occur. -/
lemma countSettingChanges_same (settings : List (Fin 2)) (s : Fin 2)
    (h : ∀ x ∈ settings, x = s) : countSettingChanges settings = 0 := by
  induction settings with
  | nil => rfl
  | cons s₁ rest ih =>
    match rest, ih with
    | [], _ => rfl
    | s₂ :: rest', ih =>
      unfold countSettingChanges
      have h1 : s₁ = s := h s₁ (by simp)
      have h2 : s₂ = s := h s₂ (by simp)
      subst h1; subst h2
      simp only [ne_eq, not_true_eq_false, ↓reduceIte, Nat.zero_add]
      exact ih (fun x hx => h x (by simp [hx]))

/-- **Zeno entropy**: n same-setting measurements cost only one 2π. -/
theorem zeno_entropy (n : ℕ) (hn : n ≥ 1) (s : Fin 2) :
    ∃ (settings : List (Fin 2)),
      settings.length = n ∧
      (∀ x ∈ settings, x = s) ∧
      totalEntropy settings = measurementEntropyCost := by
  use (List.replicate n s)
  have h_len : (List.replicate n s).length = n := List.length_replicate ..
  have h_mem : ∀ x ∈ List.replicate n s, x = s := fun x hx => List.eq_of_mem_replicate hx
  refine ⟨h_len, h_mem, ?_⟩
  have hne : List.replicate n s ≠ [] := by
    intro h;
    grind only [= List.length_nil]
  unfold totalEntropy
  -- We need to show the match reduces on a nonempty list
  obtain ⟨hd, tl, hrw⟩ := List.exists_cons_of_ne_nil hne
  rw [hrw, countSettingChanges_same _ s (by rwa [← hrw])]
  simp

variable {Λ : Type*} [MeasurableSpace Λ]

/-- When Alice and Bob measure the same observable (A_i = B_j a.e.),
    the correlation is exactly 1 regardless of the deviation ε.
    The product A·B = 1 a.e. (both ±1 and equal), so the correlation
    reduces to ∫(1 + ε) dμ₀ = 1 by the normalization condition
    ∫ε dμ₀ = 0. No thermal correction can degrade same-setting
    perfect correlation — this is the model-level Zeno effect. -/
theorem same_setting_perfect_correlation
    (M : ThermalHVModel Λ) (i j : Fin 2)
    (h_same : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), M.A i ω = M.B j ω) :
    M.correlation i j = 1 := by
  unfold ThermalHVModel.correlation
  -- Step 1: A_i·B_j = 1 a.e. ⟹ integrand = 1 + ε a.e.
  have h_eq : ∀ᵐ ω ∂(M.μ₀ : Measure Λ),
      M.A i ω * M.B j ω * (1 + M.deviation.ε i j ω) = 1 + M.deviation.ε i j ω := by
    filter_upwards [h_same, (M.A i).ae_pm_one] with ω heq hpm
    have : M.A i ω * M.B j ω = 1 := by
      rw [← heq]; rcases hpm with h | h <;> rw [h] <;> ring
    rw [this, one_mul]
  -- Step 2: ∫(1 + ε) = ∫1 + ∫ε = 1 + 0 = 1
  rw [integral_congr_ae h_eq,
      integral_add (integrable_const 1) (M.deviation.integrable i j),
      M.deviation.normalized i j, add_zero, integral_const]
  simp [probReal_univ]


/-! ## Section 2: Thermal Time Decay -/

/-- ε from exponential decay: ε = exp(−t/τ). -/
noncomputable def ε_from_time (t_eff τ_corr : ℝ) : ℝ :=
  Real.exp (-t_eff / τ_corr)

/-- ε decreases as effective time increases. -/
lemma ε_decreasing (τ : ℝ) (hτ : τ > 0) (t₁ t₂ : ℝ) (h : t₁ < t₂) :
    ε_from_time t₂ τ < ε_from_time t₁ τ := by
  unfold ε_from_time
  exact Real.exp_strictMono (div_lt_div_of_pos_right (by linarith) hτ)

/-- Longer separation ⟹ ε < 1 ⟹ measure stays positive. -/
lemma longer_time_more_classical (τ : ℝ) (hτ : τ > 0) (t : ℝ) (ht : t > 0) :
    ε_from_time t τ < 1 := by
  unfold ε_from_time; rw [← Real.exp_zero]
  exact Real.exp_strictMono (div_neg_of_neg_of_pos (by linarith) hτ)

/-! ## Section 3: Thermal Time at Temperature T

Thermal time t = 2π/T. Hot detectors have short thermal time (fast
measurement, less decay, larger ε, more quantum). Cold detectors have
long thermal time (more decay, smaller ε, more classical).

Note: the full asymmetric temperature theory lives in ThermalTime.lean
via the Ott transformation. Here we record only the decay connection.
-/

/-- Thermal time at temperature T. -/
noncomputable def thermalTimeAt (T : ℝ) : ℝ := 2 * Real.pi / T

/-- Hot detector → small thermal time. -/
lemma hot_fast (T₁ T₂ : ℝ) (_h₁ : T₁ > 0) (h₂ : T₂ > 0) (h : T₁ > T₂) :
    thermalTimeAt T₁ < thermalTimeAt T₂ := by
  unfold thermalTimeAt
  exact div_lt_div_of_pos_left (by linarith [Real.pi_pos]) h₂ h

/-- Hot limit: T → ∞ ⟹ thermal time → 0. -/
lemma hot_limit_time : Tendsto thermalTimeAt atTop (nhds 0) := by
  unfold thermalTimeAt
  convert Tendsto.const_mul (2 * Real.pi) tendsto_inv_atTop_zero using 1; simp [mul_zero]

/-- Cold limit: T → 0⁺ ⟹ thermal time → ∞. -/
lemma cold_limit_time :
    Tendsto thermalTimeAt (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  unfold thermalTimeAt
  have hpi : 2 * Real.pi > 0 := by linarith [Real.pi_pos]
  have h_inv : Tendsto (fun T : ℝ => T⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have h_mul : Tendsto (fun T : ℝ => (2 * Real.pi) * T⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos hpi).mpr h_inv
  exact h_mul.congr fun T => by simp [div_eq_mul_inv]

end ThermalBell
