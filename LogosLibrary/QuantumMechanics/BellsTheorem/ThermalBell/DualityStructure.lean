import LogosLibrary.QuantumMechanics.BellsTheorem.TLHV
import LogosLibrary.QuantumMechanics.BellsTheorem.ThermalBell

open ThermalBell BellTheorem ProbabilityTheory MeasureTheory

namespace ThermalBell

/-! ## The Duality Structure of CHSH Bounds

A remarkable algebraic structure emerges: the classical and quantum CHSH bounds
are the antisymmetric and symmetric combinations of a fundamental parameter
and its reciprocal.

Define β = 2 * ε_tsirelson = √2 - 1.

Then:
- β * (1/β) = 1  (β and 1/β are conjugate)
- β + 1/β = 2√2 = CHSH_quantum
- 1/β - β = 2   = CHSH_classical

The quantum bound is the SUM of conjugates.
The classical bound is the DIFFERENCE of conjugates.

This suggests ε_tsirelson isn't arbitrary — it's the fundamental unit
from which BOTH bounds are constructed.
-/

/-- The fundamental thermal parameter: twice the Tsirelson epsilon -/
noncomputable def β_thermal : ℝ := 2 * ε_tsirelson

/-- β = √2 - 1 -/
lemma β_thermal_value : β_thermal = Real.sqrt 2 - 1 := by
  unfold β_thermal ε_tsirelson
  ring

/-- β is positive -/
lemma β_thermal_pos : β_thermal > 0 := by
  rw [β_thermal_value]
  have h : Real.sqrt 2 > 1 := Real.one_lt_sqrt_two
  linarith

/-- β is less than 1 -/
lemma β_thermal_lt_one : β_thermal < 1 := by
  rw [β_thermal_value]
  have h : Real.sqrt 2 < 2 := sqrt_two_lt_two
  linarith

/-- The conjugate parameter: 1/β = √2 + 1 -/
noncomputable def β_conjugate : ℝ := 1 / β_thermal

/-- 1/β = √2 + 1 (rationalization of 1/(√2 - 1)) -/
lemma β_conjugate_value : β_conjugate = Real.sqrt 2 + 1 := by
  unfold β_conjugate
  rw [β_thermal_value]
  have h : Real.sqrt 2 - 1 ≠ 0 := by
    have : Real.sqrt 2 > 1 := Real.one_lt_sqrt_two
    linarith
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  field_simp
  linarith

/-- β and 1/β are genuine inverses -/
lemma β_conjugate_inverse : β_thermal * β_conjugate = 1 := by
  unfold β_conjugate
  have h : β_thermal ≠ 0 := ne_of_gt β_thermal_pos
  field_simp [h]

/-- Alternative form: (√2 - 1)(√2 + 1) = 1 -/
lemma conjugate_product : (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) = 1 := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  ring_nf
  linarith

/-! ### The Main Duality Theorems -/

/-- CHSH_quantum = β + 1/β (symmetric combination) -/
theorem quantum_is_sum_of_conjugates :
    CHSH_quantum = β_thermal + β_conjugate := by
  rw [β_thermal_value, β_conjugate_value]
  unfold CHSH_quantum
  ring

/-- CHSH_classical = 1/β - β (antisymmetric combination) -/
theorem classical_is_diff_of_conjugates :
    CHSH_classical = β_conjugate - β_thermal := by
  rw [β_thermal_value, β_conjugate_value]
  unfold CHSH_classical
  ring

/-- The quantum bound exceeds classical by 2β -/
theorem quantum_classical_gap : CHSH_quantum - CHSH_classical = 2 * β_thermal := by
  rw [quantum_is_sum_of_conjugates, classical_is_diff_of_conjugates]
  ring

/-- Alternatively: quantum - classical = 2(√2 - 1) -/
theorem quantum_classical_gap_explicit :
    CHSH_quantum - CHSH_classical = 2 * Real.sqrt 2 - 2 := by
  rw [quantum_classical_gap, β_thermal_value]
  ring

/-- The ratio quantum/classical = (β + 1/β)/(1/β - β) -/
theorem quantum_classical_ratio_conjugate :
    CHSH_quantum / CHSH_classical = (β_thermal + β_conjugate) / (β_conjugate - β_thermal) := by
  rw [quantum_is_sum_of_conjugates, classical_is_diff_of_conjugates]

/-- This ratio simplifies to √2 -/
theorem quantum_classical_ratio_sqrt_two :
    CHSH_quantum / CHSH_classical = Real.sqrt 2 := by
  unfold CHSH_quantum CHSH_classical
  have h : (2 : ℝ) ≠ 0 := by norm_num
  field_simp

/-! ### Connecting to ε_tsirelson -/

/-- ε_tsirelson = β/2 -/
lemma ε_from_β : ε_tsirelson = β_thermal / 2 := by
  unfold β_thermal
  ring

/-- 1/ε_tsirelson = 2/β = 2(√2 + 1)/(something)... let's compute directly -/
lemma one_over_ε_value : 1 / ε_tsirelson = 2 * Real.sqrt 2 + 2 := by
  unfold ε_tsirelson
  have h : Real.sqrt 2 - 1 ≠ 0 := by
    have : Real.sqrt 2 > 1 := Real.one_lt_sqrt_two
    linarith
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  field_simp
  linarith

/-- The beautiful identity: 1/ε = quantum + classical -/
theorem one_over_ε_is_total_bounds :
    1 / ε_tsirelson = CHSH_quantum + CHSH_classical := by
  rw [one_over_ε_value]
  unfold CHSH_quantum CHSH_classical
  ring

/-- Equivalently: ε = 1/(quantum + classical) -/
theorem ε_from_bounds :
    ε_tsirelson = 1 / (CHSH_quantum + CHSH_classical) := by
  have h : CHSH_quantum + CHSH_classical ≠ 0 := by
    unfold CHSH_quantum CHSH_classical
    have : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (2:ℝ) > 0)
    linarith
  field_simp
  rw [← one_over_ε_is_total_bounds]
  field_simp
  have hε : ε_tsirelson ≠ 0 := by
    unfold ε_tsirelson
    have : Real.sqrt 2 > 1 := Real.one_lt_sqrt_two
    linarith
  exact (div_eq_one_iff_eq hε).mpr rfl

/-! ### The Geometric Connection: ε and sin²(π/8) -/

/-- The optimal CHSH angle -/
noncomputable def optimal_angle : ℝ := Real.pi / 4

/-- Half the optimal angle -/
noncomputable def half_optimal_angle : ℝ := Real.pi / 8

/-- The relationship: optimal_angle / 2 = half_optimal_angle -/
lemma half_angle_relation : optimal_angle / 2 = half_optimal_angle := by
  unfold optimal_angle half_optimal_angle
  ring

/-- ε_tsirelson = √2 * sin²(π/8) -/
theorem ε_tsirelson_from_sine_squared :
    ε_tsirelson = Real.sqrt 2 * Real.sin (Real.pi / 8) ^ 2 := by
  -- From deficit_from_sine_sq: quantum_deficit = 2 * √2 * sin²(π/8)
  -- And quantum_deficit = √2 - 1 = 2 * ε_tsirelson
  -- So ε_tsirelson = √2 * sin²(π/8)
  have h_deficit : quantum_deficit = 2 * Real.sqrt 2 * Real.sin (Real.pi / 8) ^ 2 :=
    deficit_from_sine_sq
  have h_deficit_val : quantum_deficit = Real.sqrt 2 - 1 := by
    unfold quantum_deficit; rfl
  have h_ε_def : ε_tsirelson = (Real.sqrt 2 - 1) / 2 := by
    unfold ε_tsirelson; rfl
  -- From h_deficit and h_deficit_val:
  -- √2 - 1 = 2 * √2 * sin²(π/8)
  -- So sin²(π/8) = (√2 - 1) / (2√2)
  -- And ε_tsirelson = (√2 - 1)/2 = √2 * (√2 - 1)/(2√2) = √2 * sin²(π/8)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  have h_sqrt_pos : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (2:ℝ) > 0)
  have h_sin_sq : Real.sin (Real.pi / 8) ^ 2 = (Real.sqrt 2 - 1) / (2 * Real.sqrt 2) := by
    have h1 : Real.sqrt 2 - 1 = 2 * Real.sqrt 2 * Real.sin (Real.pi / 8) ^ 2 := by
      rw [← h_deficit_val, h_deficit]
    field_simp at h1 ⊢
    linarith
  rw [h_sin_sq]
  field_simp
  linarith

/-- The geometric meaning: ε is determined by half the optimal measurement angle -/
theorem ε_from_half_optimal_angle :
    ε_tsirelson = Real.sqrt 2 * Real.sin half_optimal_angle ^ 2 := by
  unfold half_optimal_angle
  exact ε_tsirelson_from_sine_squared

/-! ### Physical Interpretation

The duality structure reveals deep meaning:

1. β_thermal = √2 - 1 is the "thermal coupling" — how much measurement
   dependence is thermodynamically permitted.

2. Its conjugate 1/β = √2 + 1 represents the "inverse coupling" —
   perhaps related to the observer's perspective.

3. The CLASSICAL bound (2) is their DIFFERENCE: what you get when the
   couplings work AGAINST each other.

4. The QUANTUM bound (2√2) is their SUM: what you get when the couplings
   work TOGETHER coherently.

5. ε_tsirelson = β/2 is half the thermal coupling, because the deviation
   affects BOTH sides of the correlation.

6. The sin²(π/8) connection ties the thermal parameter directly to the
   GEOMETRY of optimal measurements — the half-angle of the π/4 that
   maximizes violation.

This is not numerology. This is structure.
-/

/-- Summary: The three equivalent characterizations of ε_tsirelson -/
theorem ε_tsirelson_three_faces :
    ε_tsirelson = (Real.sqrt 2 - 1) / 2 ∧
    ε_tsirelson = 1 / (CHSH_quantum + CHSH_classical) ∧
    ε_tsirelson = Real.sqrt 2 * Real.sin (Real.pi / 8) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · exact ε_from_bounds
  · exact ε_tsirelson_from_sine_squared

end ThermalBell
