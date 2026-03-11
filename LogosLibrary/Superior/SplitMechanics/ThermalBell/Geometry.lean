/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: BellsTheorem/ThermalBell/Geometry.lean
-/
import LogosLibrary.Superior.SplitMechanics.ThermalBell.Core
import LogosLibrary.Superior.SplitMechanics.ThermalBell.DecayGap
/-!
# Thermal Bell — Algebraic & Geometric Structure

This file contains the pure algebra and trigonometry of the thermal Bell
framework: the duality structure, the origin of 8, the PR box hierarchy,
and the three equivalent characterizations of ε_tsirelson. No measure
theory appears here — everything is `ℝ`-valued identities.

## Main Results

* `quantum_is_sum_of_conjugates` — 2√2 = β + 1/β
* `classical_is_diff_of_conjugates` — 2 = 1/β − β
* `ε_from_bounds` — ε = 1/(S_quantum + S_classical)
* `ε_tsirelson_three_faces` — algebraic, from-bounds, and sin²(π/8) forms
* `epsilon_hierarchy` — 0 < ε_tsirelson < ε_PR < 1
* `eight_is_configs_per_chsh_value` — why 8 angle slots

## References

* Tsirelson, "Quantum generalizations of Bell's inequality" (1980)
* Popescu, Rohrlich, "Quantum nonlocality as an axiom" (1994)
-/

open Real ThermalBell

namespace ThermalBell

/-! ## Section 1: The Duality Structure

Define β = 2ε_tsirelson = √2 − 1 and its conjugate 1/β = √2 + 1.
The CHSH bounds are symmetric/antisymmetric combinations:
  β + 1/β = 2√2 = S_quantum
  1/β − β = 2   = S_classical
-/

/-- The fundamental thermal parameter: β = 2ε_tsirelson = √2 − 1. -/
noncomputable def β_thermal : ℝ := 2 * ε_tsirelson

lemma β_thermal_value : β_thermal = Real.sqrt 2 - 1 := by
  unfold β_thermal ε_tsirelson; ring

lemma β_thermal_pos : β_thermal > 0 := by
  rw [β_thermal_value]; linarith [Real.one_lt_sqrt_two]

lemma β_thermal_lt_one : β_thermal < 1 := by
  rw [β_thermal_value]; linarith [sqrt_two_lt_two]

/-- The conjugate parameter: 1/β = √2 + 1. -/
noncomputable def β_conjugate : ℝ := 1 / β_thermal

lemma β_conjugate_value : β_conjugate = Real.sqrt 2 + 1 := by
  unfold β_conjugate; rw [β_thermal_value]
  have h : Real.sqrt 2 - 1 ≠ 0 := by linarith [Real.one_lt_sqrt_two]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  field_simp; linarith

lemma β_conjugate_inverse : β_thermal * β_conjugate = 1 := by
  unfold β_conjugate; field_simp [ne_of_gt β_thermal_pos]

/-- (√2 − 1)(√2 + 1) = 1: the difference-of-squares identity. -/
lemma conjugate_product : (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) = 1 := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  nlinarith

/-- **S_quantum = β + 1/β** (symmetric combination). -/
theorem quantum_is_sum_of_conjugates :
    CHSH_quantum = β_thermal + β_conjugate := by
  rw [β_thermal_value, β_conjugate_value]; unfold CHSH_quantum; ring

/-- The classical CHSH bound (unified definition). -/
def CHSH_classical : ℝ := 2

/-- **S_classical = 1/β − β** (antisymmetric combination). -/
theorem classical_is_diff_of_conjugates :
    CHSH_classical = β_conjugate - β_thermal := by
  rw [β_thermal_value, β_conjugate_value]; unfold CHSH_classical; ring

/-- The quantum/classical gap is 2β. -/
theorem quantum_classical_gap :
    CHSH_quantum - CHSH_classical = 2 * β_thermal := by
  rw [quantum_is_sum_of_conjugates, classical_is_diff_of_conjugates]; ring

/-- S_quantum / S_classical = √2. -/
theorem quantum_classical_ratio_sqrt_two :
    CHSH_quantum / CHSH_classical = Real.sqrt 2 := by
  unfold CHSH_quantum CHSH_classical; field_simp

/-! ## Section 2: ε_tsirelson from Bounds -/

/-- 1/ε_tsirelson = S_quantum + S_classical. -/
theorem one_over_ε_is_total_bounds :
    1 / ε_tsirelson = CHSH_quantum + CHSH_classical := by
  unfold ε_tsirelson CHSH_quantum CHSH_classical
  have h : Real.sqrt 2 - 1 ≠ 0 := by linarith [Real.one_lt_sqrt_two]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  field_simp; linarith

/-- **ε = 1/(S_quantum + S_classical)**. -/
theorem ε_from_bounds :
    ε_tsirelson = 1 / (CHSH_quantum + CHSH_classical) := by
  have h : CHSH_quantum + CHSH_classical ≠ 0 := by
    unfold CHSH_quantum CHSH_classical
    linarith [Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num)]
  have hε : ε_tsirelson ≠ 0 := ne_of_gt ε_tsirelson_pos
  rw [← one_over_ε_is_total_bounds]; field_simp

/-! ## Section 3: Half-Angle Identities & sin²(π/8) -/

/-- sin²(θ/2) = (1 − cos θ)/2. -/
lemma sin_sq_half (θ : ℝ) : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
  have h2 := Real.cos_two_mul (θ / 2)
  have h3 : θ / 2 * 2 = θ := by ring
  rw [mul_comm, h3] at h2
  have h := Real.cos_sq_add_sin_sq (θ / 2)
  linarith

/-- cos²(θ/2) = (1 + cos θ)/2. -/
lemma cos_sq_half (θ : ℝ) : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
  have h2 := Real.cos_two_mul (θ / 2)
  have h3 : θ / 2 * 2 = θ := by ring
  rw [mul_comm, h3] at h2; linarith

/-- The quantum deficit: √2 − 1. -/
noncomputable def quantum_deficit : ℝ := Real.sqrt 2 - 1

/-- quantum_deficit = 2√2 · sin²(π/8). -/
lemma deficit_from_sine_sq :
    quantum_deficit = 2 * Real.sqrt 2 * Real.sin (Real.pi / 8) ^ 2 := by
  unfold quantum_deficit
  have h : Real.pi / 4 / 2 = Real.pi / 8 := by ring
  have sin_sq := sin_sq_half (Real.pi / 4)
  rw [h] at sin_sq; rw [sin_sq, Real.cos_pi_div_four]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  field_simp; ring_nf; linear_combination hsq

/-- **ε_tsirelson = √2 · sin²(π/8)**. -/
theorem ε_tsirelson_from_sine_squared :
    ε_tsirelson = Real.sqrt 2 * Real.sin (Real.pi / 8) ^ 2 := by
  have h_deficit : quantum_deficit = 2 * Real.sqrt 2 * Real.sin (Real.pi / 8) ^ 2 :=
    deficit_from_sine_sq
  have h_ε_def : ε_tsirelson = quantum_deficit / 2 := by unfold ε_tsirelson quantum_deficit; ring
  rw [h_ε_def, h_deficit]; ring

/-- **The three equivalent characterizations of ε_tsirelson.** -/
theorem ε_tsirelson_three_faces :
    ε_tsirelson = (Real.sqrt 2 - 1) / 2 ∧
    ε_tsirelson = 1 / (CHSH_quantum + CHSH_classical) ∧
    ε_tsirelson = Real.sqrt 2 * Real.sin (Real.pi / 8) ^ 2 :=
  ⟨rfl, ε_from_bounds, ε_tsirelson_from_sine_squared⟩

/-! ## Section 4: The PR Box & ε Hierarchy -/

/-- The ε value for a PR box (S = 4). -/
noncomputable def ε_PR : ℝ := 1/2

lemma pr_box_epsilon : 2 + 4 * ε_PR = 4 := by unfold ε_PR; ring

/-- **ε hierarchy**: 0 < ε_tsirelson < ε_PR < 1. -/
theorem epsilon_hierarchy :
    (0 : ℝ) < ε_tsirelson ∧ ε_tsirelson < ε_PR ∧ ε_PR < 1 := by
  unfold ε_tsirelson ε_PR
  exact ⟨by linarith [Real.one_lt_sqrt_two],
         by linarith [sqrt_two_lt_two],
         by norm_num⟩

/-- **Bounds hierarchy**: 2 < 2√2 < 4. -/
theorem bounds_hierarchy : 2 < 2 * Real.sqrt 2 ∧ 2 * Real.sqrt 2 < 4 :=
  ⟨by linarith [Real.one_lt_sqrt_two], by linarith [sqrt_two_lt_two]⟩

/-- ε_tsirelson / ε_PR = √2 − 1 (the quantum deficit). -/
lemma epsilon_ratio : ε_tsirelson / ε_PR = Real.sqrt 2 - 1 := by
  unfold ε_tsirelson ε_PR; field_simp

/-! ## Section 5: The Origin of 8

16 = 2⁴ total dichotomic configurations.
2 = number of CHSH values (±2).
8 = 16/2 configurations per CHSH value.
2π/8 = π/4 = the optimal quantum angle.
-/

/-- Number of settings per party. -/
def n_settings : ℕ := 2

/-- Dimension of a dichotomic observable's eigenspace. -/
def dichotomic_dim : ℕ := 2

/-- Number of correlation terms: n_settings². -/
def n_correlations : ℕ := n_settings * n_settings

/-- Degrees of freedom per party. -/
def alice_dof : ℕ := n_settings

def bob_dof : ℕ := n_settings

/-- Configuration space dimension. -/
def config_space_dim : ℕ := alice_dof * bob_dof

/-- Orientations per configuration. -/
def orientations_per_config : ℕ := dichotomic_dim

/-- Total phase space: 4 × 2 = 8. -/
def total_phase_space : ℕ := config_space_dim * orientations_per_config

lemma total_phase_space_is_eight : total_phase_space = 8 := rfl

/-- Total sign configurations: 2⁴ = 16. -/
def total_sign_configs : ℕ := 2^4

/-- **8 = 16/2 = configs per CHSH value = angle slots.** -/
theorem eight_is_configs_per_chsh_value :
    total_sign_configs / 2 = chsh_angle_slots := rfl

/-- 2π / 8 = π/4. -/
lemma angle_per_slot : (2 * Real.pi) / total_phase_space = Real.pi / 4 := by
  unfold total_phase_space config_space_dim orientations_per_config
  unfold alice_dof bob_dof n_settings dichotomic_dim; norm_num; ring

/-- Bob's combinations in the CHSH factorization. -/
def bob_combinations (b₀ b₁ : ℝ) : ℝ × ℝ := (b₁ - b₀, b₀ + b₁)

/-- For dichotomic B, exactly one combination is ±2, the other is 0. -/
lemma bob_combinations_complementary (b₀ b₁ : ℝ)
    (hb₀ : b₀ = 1 ∨ b₀ = -1) (hb₁ : b₁ = 1 ∨ b₁ = -1) :
    (bob_combinations b₀ b₁).1 = 0 ∧ |((bob_combinations b₀ b₁).2)| = 2 ∨
    |((bob_combinations b₀ b₁).1)| = 2 ∧ (bob_combinations b₀ b₁).2 = 0 := by
  unfold bob_combinations
  rcases hb₀ with rfl | rfl <;> rcases hb₁ with rfl | rfl <;> simp <;> norm_num

/-- This complementarity is WHY the classical bound is 2. -/
lemma classical_bound_from_complementarity (a₀ a₁ b₀ b₁ : ℝ)
    (ha₀ : a₀ = 1 ∨ a₀ = -1) (ha₁ : a₁ = 1 ∨ a₁ = -1)
    (hb₀ : b₀ = 1 ∨ b₀ = -1) (hb₁ : b₁ = 1 ∨ b₁ = -1) :
    |a₀ * (b₁ - b₀) + a₁ * (b₀ + b₁)| ≤ 2 := by
  have h := bob_combinations_complementary b₀ b₁ hb₀ hb₁
  rcases h with ⟨hz, ht⟩ | ⟨ht, hz⟩ <;> simp only [bob_combinations] at hz ht
  · rw [hz, mul_zero, zero_add]
    rcases ha₁ with rfl | rfl <;> simp <;> grind
  · rw [hz, mul_zero, add_zero]
    rcases ha₀ with rfl | rfl <;> simp <;> grind

/-- S_quantum = 4 · cos(π/4): the "four cosines" form. -/
lemma tsirelson_four_cosines :
    CHSH_quantum = 4 * Real.cos (Real.pi / 4) := by
  unfold CHSH_quantum; rw [Real.cos_pi_div_four]; ring

/-- S_quantum = (# correlations) × cos(2π / total_phase_space). -/
lemma tsirelson_as_correlations_times_cosine :
    CHSH_quantum = n_correlations * Real.cos (modularPeriod / total_phase_space) := by
  unfold CHSH_quantum n_correlations modularPeriod total_phase_space
  unfold config_space_dim orientations_per_config alice_dof bob_dof n_settings dichotomic_dim
  simp only [Nat.reduceMul, Nat.cast_ofNat]
  rw [show (2 : ℝ) * Real.pi / 8 = Real.pi / 4 by ring, Real.cos_pi_div_four]; ring

end ThermalBell
