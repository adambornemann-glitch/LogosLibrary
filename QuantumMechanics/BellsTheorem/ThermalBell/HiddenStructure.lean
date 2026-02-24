import LogosLibrary.QuantumMechanics.BellsTheorem.TLHV
import LogosLibrary.QuantumMechanics.BellsTheorem.ThermalBell.QuantumCompatible
import LogosLibrary.QuantumMechanics.BellsTheorem.ThermalBell.OriginOfEight
import LogosLibrary.QuantumMechanics.BellsTheorem.ThermalBell.PRBox

open MeasureTheory ProbabilityTheory Set Real BellTheorem
namespace ThermalBell


/-! ## Part 14: Hidden Structure in the Bounds

Several non-obvious relationships emerge from the formalization.
-/

/-- Observation 1: The quantum/classical ratio is 1/cos(period/8) -/

lemma quantum_classical_ratio : CHSH_quantum / CHSH_classical = Real.sqrt 2 := by
  unfold CHSH_quantum CHSH_classical
  norm_num

lemma ratio_from_cosine : 1 / Real.cos (2 * Real.pi / 8) = Real.sqrt 2 := by
  have h : (2 : ℝ) * Real.pi / 8 = Real.pi / 4 := by ring
  rw [h, Real.cos_pi_div_four]
  have hsqrt : Real.sqrt 2 ≠ 0 := by simp only [ne_eq, Nat.ofNat_nonneg, sqrt_eq_zero,
    OfNat.ofNat_ne_zero, not_false_eq_true]
  field_simp
  simp only [Nat.ofNat_nonneg, sq_sqrt]

theorem quantum_from_classical_and_geometry :
    CHSH_quantum = CHSH_classical / Real.cos (modularPeriod' / chsh_angle_slots) := by
  unfold CHSH_quantum CHSH_classical modularPeriod' chsh_angle_slots
  simp only [Nat.cast_ofNat]
  have h : (2 : ℝ) * Real.pi / 8 = Real.pi / 4 := by ring
  rw [h, Real.cos_pi_div_four]
  have hsqrt : Real.sqrt 2 ≠ 0 := by simp only [ne_eq, Nat.ofNat_nonneg, sqrt_eq_zero,
    OfNat.ofNat_ne_zero, not_false_eq_true]
  field_simp
  simp only [Nat.ofNat_nonneg, sq_sqrt]

/-- Observation 2: Tsirelson = (# correlations) × cos(period / # configs) -/

lemma tsirelson_as_correlations_times_cosine :
    CHSH_quantum = n_correlations * Real.cos (modularPeriod' / total_phase_space) := by
  unfold CHSH_quantum n_correlations modularPeriod' total_phase_space
  unfold config_space_dim orientations_per_config alice_dof bob_dof n_settings dichotomic_dim
  simp only [Nat.reduceMul, Nat.cast_ofNat]
  have h : (2 : ℝ) * Real.pi / 8 = Real.pi / 4 := by ring
  rw [h, Real.cos_pi_div_four]
  ring

/-- Alternative form: the "4 cosines" interpretation -/
lemma tsirelson_four_cosines :
    CHSH_quantum = 4 * Real.cos (Real.pi / 4) := by
  unfold CHSH_quantum
  rw [Real.cos_pi_div_four]
  ring

/-- Each correlation term contributes cos(π/4) = √2/2 at optimal angles -/
lemma per_term_contribution : CHSH_quantum / 4 = Real.cos (Real.pi / 4) := by
  unfold CHSH_quantum
  rw [Real.cos_pi_div_four]
  ring

/-- Observation 3: The ratio ε_tsirelson / ε_PR = √2 - 1 -/

lemma epsilon_ratio : ε_tsirelson / ε_PR = Real.sqrt 2 - 1 := by
  unfold ε_tsirelson ε_PR
  simp only [one_div, div_inv_eq_mul, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, IsUnit.div_mul_cancel]


/-- This is the same as the "quantum deficit" -/
noncomputable def quantum_deficit : ℝ := Real.sqrt 2 - 1

lemma quantum_deficit_eq_ratio : quantum_deficit = ε_tsirelson / ε_PR := by
  unfold quantum_deficit
  rw [epsilon_ratio]

/-- The deficit also appears as: (1 - cos(π/4)) scaled by √2 -/
lemma deficit_from_cosine : quantum_deficit = (1 - Real.cos (Real.pi / 4)) * Real.sqrt 2 := by
  unfold quantum_deficit
  rw [Real.cos_pi_div_four]
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  ring_nf
  simp only [Nat.ofNat_nonneg, sq_sqrt]
  linarith

/-- Alternative: the deficit times √2 gives 2(1 - cos(π/4)) -/
lemma deficit_times_sqrt_two : quantum_deficit * Real.sqrt 2 = 2 - Real.sqrt 2 := by
  unfold quantum_deficit
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  ring_nf
  linear_combination h

/-- And 2 - √2 = 2(1 - cos(π/4)) -/
lemma two_minus_sqrt_two : 2 - Real.sqrt 2 = 2 * (1 - Real.cos (Real.pi / 4)) := by
  rw [Real.cos_pi_div_four]
  ring

/-- Half-angle formula: sin²(θ/2) = (1 - cos(θ))/2 -/
lemma sin_sq_half (θ : ℝ) : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
  have h := Real.cos_sq_add_sin_sq (θ / 2)
  have h2 := Real.cos_two_mul (θ / 2)
  -- cos(2 * (θ/2)) = 2 * cos²(θ/2) - 1
  -- cos(θ) = 2 * cos²(θ/2) - 1
  -- cos²(θ/2) = (1 + cos(θ))/2
  -- sin²(θ/2) = 1 - cos²(θ/2) = 1 - (1 + cos(θ))/2 = (1 - cos(θ))/2
  have h3 : θ / 2 * 2 = θ := by ring
  rw [mul_comm, h3] at h2
  -- h2 : cos θ = 2 * cos(θ/2)² - 1
  have cos_sq : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by linarith
  linarith

/-- Half-angle formula: cos²(θ/2) = (1 + cos(θ))/2 -/
lemma cos_sq_half (θ : ℝ) : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
  have h2 := Real.cos_two_mul (θ / 2)
  have h3 : θ / 2 * 2 = θ := by ring
  rw [mul_comm, h3] at h2
  linarith

/-- The correct sine relationship: quantum_deficit = 2√2 * sin²(π/8) -/
lemma deficit_from_sine_sq : quantum_deficit = 2 * Real.sqrt 2 * Real.sin (Real.pi / 8) ^ 2 := by
  unfold quantum_deficit
  have h : Real.pi / 4 / 2 = Real.pi / 8 := by ring
  have sin_sq := sin_sq_half (Real.pi / 4)
  rw [h] at sin_sq
  rw [sin_sq, Real.cos_pi_div_four]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  field_simp
  ring_nf
  linear_combination hsq

/-- Alternative: the simpler relation between deficit and half-angle -/
lemma deficit_half_angle : quantum_deficit = Real.sqrt 2 * (1 - Real.cos (Real.pi / 4)) := by
  unfold quantum_deficit
  rw [Real.cos_pi_div_four]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  ring_nf
  linarith

/-- Check: 2 * sin²(π/8) = 1 - √2/2, not √2 - 1 -/
lemma two_sin_sq_pi_eight : 2 * Real.sin (Real.pi / 8) ^ 2 = 1 - Real.sqrt 2 / 2 := by
  have h : Real.pi / 4 / 2 = Real.pi / 8 := by ring
  have sin_sq := sin_sq_half (Real.pi / 4)
  rw [h] at sin_sq
  rw [sin_sq, Real.cos_pi_div_four]
  ring


/- Observation 4: Quantum-compatible models require E_C ≠ 0 at |E_Q| = 1 -/

/-- When |f| < 1 everywhere and μ is a probability measure, ∫|f| < 1 -/
lemma integral_abs_lt_one_of_bound {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ]
    (f : Λ → ℝ) (hf_int : Integrable f μ)
    (hf_bound : ∀ ω, |f ω| < 1) :
    ∫ ω, |f ω| ∂μ < 1 := by
  have h_gap : ∀ ω, 1 - |f ω| > 0 := fun ω => by linarith [hf_bound ω]
  have h_gap_nonneg : ∀ ω, 0 ≤ 1 - |f ω| := fun ω => le_of_lt (h_gap ω)
  have h_gap_int : Integrable (fun ω => 1 - |f ω|) μ := (integrable_const 1).sub hf_int.abs
  -- The support of (1 - |f|) is all of Λ since 1 - |f ω| > 0 everywhere
  have h_support : Function.support (fun ω => 1 - |f ω|) = Set.univ := by
    ext ω
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    linarith [h_gap ω]
  have h_int_gap_pos : 0 < ∫ ω, (1 - |f ω|) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg h_gap_nonneg h_gap_int]
    rw [h_support]
    simp only [measure_univ, zero_lt_one]
  have h_expand : ∫ ω, (1 - |f ω|) ∂μ = ∫ ω, (1 : ℝ) ∂μ - ∫ ω, |f ω| ∂μ :=
    integral_sub (integrable_const 1) hf_int.abs
  have h_prob : ∫ ω, (1 : ℝ) ∂μ = 1 := by
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_univ_eq_one]
  linarith

/-- Product of dichotomic functions has absolute value 1 -/
lemma abs_mul_dichotomic {a b : ℝ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    |a * b| = 1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

/-- |A B ε| = |ε| when A, B are dichotomic -/
lemma abs_dichotomic_mul_eq {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ)
    (A B ε : Λ → ℝ)
    (hA : ∀ᵐ ω ∂μ, A ω = 1 ∨ A ω = -1)
    (hB : ∀ᵐ ω ∂μ, B ω = 1 ∨ B ω = -1) :
    ∀ᵐ ω ∂μ, |A ω * B ω * ε ω| = |ε ω| := by
  filter_upwards [hA, hB] with ω ha hb
  rw [abs_mul, abs_mul_dichotomic ha hb, one_mul]

/-- Main application: |∫ A B ε| < 1 when A, B dichotomic and |ε| < 1 -/
lemma abs_integral_ABε_lt_one {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A B ε : Λ → ℝ)
    (hA : ∀ᵐ ω ∂μ, A ω = 1 ∨ A ω = -1)
    (hB : ∀ᵐ ω ∂μ, B ω = 1 ∨ B ω = -1)
    (hε_bound : ∀ ω, |ε ω| < 1)
    (hA_int : Integrable A μ) (hB_int : Integrable B μ) (hε_int : Integrable ε μ) :
    |∫ ω, A ω * B ω * ε ω ∂μ| < 1 := by
  have h_int : Integrable (fun ω => A ω * B ω * ε ω) μ := by
    apply Integrable.mono' (integrable_const 1)
    · exact ((hA_int.aestronglyMeasurable.mul hB_int.aestronglyMeasurable).mul
             hε_int.aestronglyMeasurable)
    · have h_ae := abs_dichotomic_mul_eq μ A B ε hA hB
      filter_upwards [h_ae] with ω hω
      simp only [Real.norm_eq_abs, hω]
      exact le_of_lt (hε_bound ω)
  calc |∫ ω, A ω * B ω * ε ω ∂μ|
      ≤ ∫ ω, |A ω * B ω * ε ω| ∂μ := abs_integral_le_integral_abs
    _ = ∫ ω, |ε ω| ∂μ := integral_congr_ae (abs_dichotomic_mul_eq μ A B ε hA hB)
    _ < 1 := integral_abs_lt_one_of_bound μ ε hε_int hε_bound

/-- If |E_Q(θ)| = 1 and E_C = 0, we'd need |ε_thermal| = 1, violating |ε| < 1 -/
theorem quantum_compatible_constraint {Λ : Type*} [MeasurableSpace Λ]
    (μ₀ : Measure Λ) [IsProbabilityMeasure μ₀]
    (A B : Λ → ℝ) (ε : Λ → ℝ)
    (hε_bounded : ∀ ω, |ε ω| < 1)
    (hA : ∀ᵐ ω ∂μ₀, A ω = 1 ∨ A ω = -1)
    (hB : ∀ᵐ ω ∂μ₀, B ω = 1 ∨ B ω = -1)
    (hA_int : Integrable A μ₀) (hB_int : Integrable B μ₀)
    (hε_int : Integrable ε μ₀)
    (h_E_C_zero : E_C μ₀ A B = 0)
    (θ : ℝ) (h_E_Q_one : |E_Q θ| = 1) :
    ¬ quantum_compatible μ₀ A B ε θ := by
  intro h_compat
  unfold quantum_compatible E_full at h_compat
  rw [h_E_C_zero, zero_add] at h_compat
  -- So E_thermal = E_Q θ, with |E_Q θ| = 1
  unfold E_thermal at h_compat
  -- We need |∫ A B ε dμ₀| = 1
  have h_thermal_eq : |∫ ω, A ω * B ω * ε ω ∂μ₀| = 1 := by
    rw [h_compat]; exact h_E_Q_one
  -- But |∫ A B ε| < 1 by our lemma
  have h_lt := abs_integral_ABε_lt_one μ₀ A B ε hA hB hε_bounded hA_int hB_int hε_int
  linarith

/-- Corollary: At θ = 0 (E_Q = -1) or θ = π (E_Q = 1), E_C cannot be 0 -/
theorem E_C_nonzero_at_extremes {Λ : Type*} [MeasurableSpace Λ]
    (μ₀ : Measure Λ) [IsProbabilityMeasure μ₀]
    (A B : Λ → ℝ) (ε : Λ → ℝ)
    (hε_bounded : ∀ ω, |ε ω| < 1)
    (hA : ∀ᵐ ω ∂μ₀, A ω = 1 ∨ A ω = -1)
    (hB : ∀ᵐ ω ∂μ₀, B ω = 1 ∨ B ω = -1)
    (hA_int : Integrable A μ₀) (hB_int : Integrable B μ₀)
    (hε_int : Integrable ε μ₀)
    (h_compat_zero : quantum_compatible μ₀ A B ε 0) :
    E_C μ₀ A B ≠ 0 := by
  intro h_zero
  have h_E_Q_abs : |E_Q 0| = 1 := by
    unfold E_Q; simp [Real.cos_zero]
  exact quantum_compatible_constraint μ₀ A B ε hε_bounded hA hB hA_int hB_int hε_int
        h_zero 0 h_E_Q_abs h_compat_zero

/- The physical interpretation: quantum correlations REQUIRE classical correlations
    at the extreme angles. The hidden variables must already be correlated;
    ε just "tweaks" them to match the quantum curve. -/

/-- How much classical correlation is needed? At θ = 0, if |ε| ≤ ε_max < 1:
    E_Q(0) = -1, so E_C + E_thermal = -1
    |E_thermal| ≤ ε_max (roughly), so |E_C| ≥ 1 - ε_max -/
lemma classical_correlation_lower_bound (ε_max : ℝ) (_hε : 0 ≤ ε_max) (hε' : ε_max < 1) :
    ∀ E_C E_th : ℝ, E_C + E_th = -1 → |E_th| ≤ ε_max → |E_C| ≥ 1 - ε_max := by
  intro E_C E_th h_sum h_th
  have h1 : E_C = -1 - E_th := by linarith
  -- From |E_th| ≤ ε_max we get -ε_max ≤ E_th ≤ ε_max
  have h_th_bounds : -ε_max ≤ E_th ∧ E_th ≤ ε_max := abs_le.mp h_th
  -- So E_C = -1 - E_th is in [-1 - ε_max, -1 + ε_max], both negative since ε_max < 1
  have h_E_C_neg : E_C < 0 := by linarith [h_th_bounds.2]
  rw [h1, abs_of_neg (by linarith [h_th_bounds.2] : -1 - E_th < 0)]
  -- Now we need to show: -(-1 - E_th) ≥ 1 - ε_max, i.e., 1 + E_th ≥ 1 - ε_max
  linarith [h_th_bounds.1]

/-- For ε_max = ε_tsirelson, the minimum |E_C| at θ = 0 -/
lemma min_classical_at_tsirelson : 1 - ε_tsirelson = (3 - Real.sqrt 2) / 2 := by
  unfold ε_tsirelson
  ring

/-- Numerical check: (3 - √2)/2 ≈ (3 - 1.414)/2 ≈ 0.793 -/
lemma min_classical_positive : 1 - ε_tsirelson > 0 := by
  unfold ε_tsirelson
  have h : Real.sqrt 2 < 2 := sqrt_two_lt_two
  linarith
namespace ThermalBell
