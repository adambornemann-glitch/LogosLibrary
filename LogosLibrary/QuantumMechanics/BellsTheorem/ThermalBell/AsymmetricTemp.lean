import LogosLibrary.QuantumMechanics.BellsTheorem.TLHV

open ThermalBell BellTheorem

namespace ThermalBell



/-! ## Part 11: Asymmetric Temperatures

What happens when Alice's detector is at temperature T_A and Bob's at T_B?

The thermal times differ: t_A = 2π/T_A, t_B = 2π/T_B.

Key question: how does ε_max depend on T_A and T_B?
-/

/-- Thermal time at temperature T -/
noncomputable def thermalTimeAt (T : ℝ) : ℝ := 2 * Real.pi / T

/-- An asymmetric thermal configuration -/
structure AsymmetricThermalConfig where
  /-- Alice's detector temperature -/
  T_A : ℝ
  /-- Bob's detector temperature -/
  T_B : ℝ
  /-- Temperatures are positive -/
  hT_A : T_A > 0
  hT_B : T_B > 0
  /-- Correlation decay time -/
  τ_corr : ℝ
  hτ : τ_corr > 0

/-- Alice's thermal time -/
noncomputable def AsymmetricThermalConfig.t_A (C : AsymmetricThermalConfig) : ℝ :=
  thermalTimeAt C.T_A

/-- Bob's thermal time -/
noncomputable def AsymmetricThermalConfig.t_B (C : AsymmetricThermalConfig) : ℝ :=
  thermalTimeAt C.T_B

/-- The relevant time scale for correlations: when do Alice and Bob "meet"?

    Hypothesis 1: Use the MINIMUM time (faster detector dominates)
    Hypothesis 2: Use the MAXIMUM time (slower detector is bottleneck)
    Hypothesis 3: Use geometric mean (symmetric in exchange)
    Hypothesis 4: Use arithmetic mean
-/

noncomputable def AsymmetricThermalConfig.t_min (C : AsymmetricThermalConfig) : ℝ :=
  min C.t_A C.t_B

noncomputable def AsymmetricThermalConfig.t_max (C : AsymmetricThermalConfig) : ℝ :=
  max C.t_A C.t_B

noncomputable def AsymmetricThermalConfig.t_geometric (C : AsymmetricThermalConfig) : ℝ :=
  Real.sqrt (C.t_A * C.t_B)

noncomputable def AsymmetricThermalConfig.t_arithmetic (C : AsymmetricThermalConfig) : ℝ :=
  (C.t_A + C.t_B) / 2

/-- The geometric mean of thermal times equals thermal time at geometric mean temperature -/
lemma geometric_mean_temps (C : AsymmetricThermalConfig) :
    C.t_geometric = Real.sqrt (thermalTimeAt C.T_A * thermalTimeAt C.T_B) := rfl

/-- Alternative form using temperatures -/
lemma geometric_time_from_temps (C : AsymmetricThermalConfig) :
    C.t_geometric = 2 * Real.pi / Real.sqrt (C.T_A * C.T_B) := by
  unfold AsymmetricThermalConfig.t_geometric AsymmetricThermalConfig.t_A
         AsymmetricThermalConfig.t_B thermalTimeAt
  have hA := C.hT_A
  have hB := C.hT_B
  have h_prod_pos : C.T_A * C.T_B > 0 := mul_pos hA hB
  have hpi : 2 * Real.pi > 0 := by linarith [Real.pi_pos]
  -- √((2π/T_A) * (2π/T_B)) = √((2π)² / (T_A * T_B)) = 2π / √(T_A * T_B)
  have h1 : (2 * Real.pi / C.T_A) * (2 * Real.pi / C.T_B) = (2 * Real.pi)^2 / (C.T_A * C.T_B) := by
    field_simp
  rw [h1]
  rw [Real.sqrt_div (sq_nonneg _)]
  rw [Real.sqrt_sq (le_of_lt hpi)]

/-- The ε_max as a function of effective time separation -/
noncomputable def ε_from_time (t_eff τ_corr : ℝ) : ℝ :=
  Real.exp (-t_eff / τ_corr)

/-- ε decreases as effective time increases -/
lemma ε_decreasing (τ_corr : ℝ) (hτ : τ_corr > 0) (t₁ t₂ : ℝ) (h : t₁ < t₂) :
    ε_from_time t₂ τ_corr < ε_from_time t₁ τ_corr := by
  unfold ε_from_time
  apply Real.exp_lt_exp_of_lt
  have : -t₂ / τ_corr < -t₁ / τ_corr := by
    apply div_lt_div_of_pos_right _ hτ
    linarith
  exact this

/-- Longer time → smaller ε → closer to classical -/
lemma longer_time_more_classical (τ_corr : ℝ) (hτ : τ_corr > 0) (t : ℝ) (ht : t > 0) :
    ε_from_time t τ_corr < 1 := by
  unfold ε_from_time
  rw [← Real.exp_zero]
  apply Real.exp_lt_exp_of_lt
  apply div_neg_of_neg_of_pos
  · linarith
  · exact hτ

/-- The asymmetric CHSH bound using minimum time (conservative) -/
noncomputable def CHSH_bound_min (C : AsymmetricThermalConfig) : ℝ :=
  2 + 4 * ε_from_time C.t_min C.τ_corr

/-- The asymmetric CHSH bound using geometric mean time -/
noncomputable def CHSH_bound_geometric (C : AsymmetricThermalConfig) : ℝ :=
  2 + 4 * ε_from_time C.t_geometric C.τ_corr

/-- For positive reals, min ≤ geometric mean -/
lemma min_le_geometric_mean (a b : ℝ) (ha : a > 0) (hb : b > 0) :
    min a b ≤ Real.sqrt (a * b) := by
  rcases le_or_gt a b with hab | hab
  · -- a ≤ b case: min = a, need a ≤ √(ab)
    rw [min_eq_left hab]
    have h1 : a ^ 2 ≤ a * b := by nlinarith
    have h2 : Real.sqrt (a ^ 2) = a := Real.sqrt_sq (le_of_lt ha)
    calc a = Real.sqrt (a ^ 2) := h2.symm
      _ ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt h1
  · -- b < a case: min = b, need b ≤ √(ab)
    rw [min_eq_right (le_of_lt hab)]
    have h1 : b ^ 2 ≤ a * b := by nlinarith
    have h2 : Real.sqrt (b ^ 2) = b := Real.sqrt_sq (le_of_lt hb)
    calc b = Real.sqrt (b ^ 2) := h2.symm
      _ ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt h1

/-- Minimum time gives the largest ε (most quantum) -/
lemma min_time_largest_ε (C : AsymmetricThermalConfig) :
    ε_from_time C.t_min C.τ_corr ≥ ε_from_time C.t_geometric C.τ_corr := by
  unfold ε_from_time
  apply Real.exp_le_exp_of_le
  apply div_le_div_of_nonneg_right _ (le_of_lt C.hτ)
  apply neg_le_neg
  unfold AsymmetricThermalConfig.t_min AsymmetricThermalConfig.t_geometric
  have ht_A_pos : C.t_A > 0 := by
    unfold AsymmetricThermalConfig.t_A thermalTimeAt
    exact div_pos (by linarith [Real.pi_pos] : 2 * Real.pi > 0) C.hT_A
  have ht_B_pos : C.t_B > 0 := by
    unfold AsymmetricThermalConfig.t_B thermalTimeAt
    exact div_pos (by linarith [Real.pi_pos] : 2 * Real.pi > 0) C.hT_B
  exact min_le_geometric_mean C.t_A C.t_B ht_A_pos ht_B_pos

/-- Symmetric case: when T_A = T_B, all time scales agree -/
lemma symmetric_temps_agree (C : AsymmetricThermalConfig) (h : C.T_A = C.T_B) :
    C.t_A = C.t_B ∧ C.t_min = C.t_A ∧ C.t_max = C.t_A ∧
    C.t_geometric = C.t_A ∧ C.t_arithmetic = C.t_A := by
  have ht_eq : C.t_A = C.t_B := by
    unfold AsymmetricThermalConfig.t_A AsymmetricThermalConfig.t_B thermalTimeAt
    rw [h]
  constructor
  · exact ht_eq
  constructor
  · unfold AsymmetricThermalConfig.t_min
    rw [ht_eq, min_self]
  constructor
  · unfold AsymmetricThermalConfig.t_max
    rw [ht_eq, max_self]
  constructor
  · unfold AsymmetricThermalConfig.t_geometric
    rw [ht_eq]
    have ht_pos : C.t_B > 0 := by
      unfold AsymmetricThermalConfig.t_B thermalTimeAt
      exact div_pos (by linarith [Real.pi_pos] : 2 * Real.pi > 0) C.hT_B
    rw [← Real.sqrt_sq (le_of_lt ht_pos)]
    congr 1
    ring_nf
    rw [Real.sqrt_sq_eq_abs]
    exact sq_abs C.t_B
  · unfold AsymmetricThermalConfig.t_arithmetic
    rw [ht_eq]
    ring


/-- Hot detector (large T) has small thermal time -/
lemma hot_fast (T₁ T₂ : ℝ) (_h₁ : T₁ > 0) (h₂ : T₂ > 0) (h : T₁ > T₂) :
    thermalTimeAt T₁ < thermalTimeAt T₂ := by
  unfold thermalTimeAt
  have hpi : 2 * Real.pi > 0 := by linarith [Real.pi_pos]
  apply div_lt_div_of_pos_left hpi h₂ h

/-- Cold detector (small T) has large thermal time -/
lemma cold_slow (T₁ T₂ : ℝ) (h₁ : T₁ > 0) (h₂ : T₂ > 0) (h : T₁ < T₂) :
    thermalTimeAt T₁ > thermalTimeAt T₂ := by
  exact hot_fast T₂ T₁ h₂ h₁ h

/- The extreme asymmetric limits -/

/-- When T_A → ∞ (Alice's detector very hot), t_A → 0 -/
lemma hot_limit_time : Filter.Tendsto thermalTimeAt Filter.atTop (nhds 0) := by
  unfold thermalTimeAt
  have hpi : 2 * Real.pi > 0 := by linarith [Real.pi_pos]
  have : Filter.Tendsto (fun T : ℝ => T⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have h := Filter.Tendsto.const_mul (2 * Real.pi) this
  simp only [mul_zero] at h
  convert h using 1

/-- When T_A → 0⁺ (Alice's detector very cold), t_A → ∞ -/
lemma cold_limit_time : Filter.Tendsto thermalTimeAt (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  unfold thermalTimeAt
  have hpi : 2 * Real.pi > 0 := by linarith [Real.pi_pos]
  have h : Filter.Tendsto (fun T : ℝ => T⁻¹) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  have h2 : Filter.Tendsto (fun T : ℝ => (2 * Real.pi) * T⁻¹) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    rw [propext (Filter.tendsto_const_mul_atTop_of_pos hpi)]
    exact h
  convert h2 using 1

/- Physical interpretation:
    - Hot detector → fast measurement → less time for correlations → more classical
    - Cold detector → slow measurement → more time for correlations → more quantum

    Wait, that's backwards from intuition! Let me reconsider...

    Actually: t is the SEPARATION time, not measurement time.
    Larger t → correlations have decayed more → smaller ε → more classical.

    So: hot detector → small t_A → less decay → larger ε → more quantum.
    This matches: high temperature systems are more "quantum" in some sense.
-/

/-- Corrected interpretation: hot = more quantum (larger ε) -/
lemma hot_more_quantum (C : AsymmetricThermalConfig) (C' : AsymmetricThermalConfig)
    (hτ : C.τ_corr = C'.τ_corr)
    (_hB : C.T_B = C'.T_B)
    (hA : C.T_A > C'.T_A) :
    ε_from_time C.t_A C.τ_corr > ε_from_time C'.t_A C'.τ_corr := by
  unfold ε_from_time
  apply Real.exp_lt_exp_of_lt
  rw [hτ]
  apply div_lt_div_of_pos_right _ C'.hτ
  apply neg_lt_neg
  unfold AsymmetricThermalConfig.t_A
  exact hot_fast C.T_A C'.T_A C.hT_A C'.hT_A hA

end ThermalBell
