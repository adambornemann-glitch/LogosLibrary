import LogosLibrary.Superior.SplitMechanics.BellsTheorem.TLHV.Measurement
open MeasureTheory Real

namespace ThermalBell
/-! ## The Quantum-Thermal Dictionary

The quantum CHSH excess beyond classical = 2√2 - 2 = 2(√2 - 1)
The thermal CHSH excess beyond classical = 4·ε_max

Setting these equal gives ε_max = (√2 - 1)/2 = ε_tsirelson.

This section makes the dictionary precise.
-/

/-- The quantum CHSH value -/
noncomputable def CHSH_quantum : ℝ := 2 * Real.sqrt 2

/-- The classical (LHV) CHSH bound -/
def CHSH_classical : ℝ := 2

/-- The quantum excess beyond classical -/
noncomputable def CHSH_quantum_excess : ℝ := CHSH_quantum - CHSH_classical

lemma quantum_excess_value : CHSH_quantum_excess = 2 * (Real.sqrt 2 - 1) := by
  unfold CHSH_quantum_excess CHSH_quantum CHSH_classical
  ring

/-- The thermal excess is 4·ε -/
noncomputable def CHSH_thermal_excess (ε : ℝ) : ℝ := 4 * ε

/-- Matching quantum and thermal excess determines ε -/
lemma thermal_matches_quantum_excess :
    CHSH_thermal_excess ε_tsirelson = CHSH_quantum_excess := by
  unfold CHSH_thermal_excess ε_tsirelson CHSH_quantum_excess CHSH_quantum CHSH_classical
  ring

/-- The per-correlation-term excess.

    CHSH has 4 terms: E₀₁, E₀₀, E₁₀, E₁₁
    Classical: each |E| ≤ 1, and the combination gives |S| ≤ 2
    Quantum: each E = -cos(θ), optimal angles give |S| = 2√2

    The excess per term is (2√2 - 2)/4 = (√2 - 1)/2 = ε_tsirelson -/
lemma per_term_excess : (CHSH_quantum - CHSH_classical) / 4 = ε_tsirelson := by
  unfold CHSH_quantum CHSH_classical ε_tsirelson
  ring

/-- The structure of the correspondence -/
structure QuantumThermalCorrespondence where
  /-- Quantum state (singlet) gives correlations E(θ) = -cos(θ) -/
  quantum_correlation : ℝ → ℝ := singletCorrelation
  /-- The quantum CHSH value -/
  S_quantum : ℝ := CHSH_quantum
  /-- Thermal model gives S = S_classical + 4ε -/
  S_thermal : ℝ → ℝ := fun ε => CHSH_classical + 4 * ε
  /-- The unique ε matching quantum -/
  ε_match : ℝ := ε_tsirelson
  /-- Proof that they match -/
  correspondence : S_thermal ε_match = S_quantum := by
    simp only [CHSH_classical, CHSH_quantum, ε_tsirelson]
    ring

/-- The quantum correlation at optimal angle π/4 -/
lemma quantum_correlation_at_optimal :
    singletCorrelation (Real.pi / 4) = -Real.sqrt 2 / 2 := by
  unfold singletCorrelation
  rw [Real.cos_pi_div_four]
  ring

/-- Helper for quantum_between_classical -/
lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h1 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  have h2 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
  nlinarith

/-- The "missing" correlation from classical.

    Classical expectation for uncorrelated: E = 0
    Classical maximum for perfectly correlated: |E| = 1
    Quantum at π/4: E = -√2/2 ≈ -0.707

    The quantum correlation is "between" the classical extremes,
    but in a way that allows CHSH to exceed 2. -/
lemma quantum_between_classical :
    -1 < singletCorrelation (Real.pi / 4) ∧ singletCorrelation (Real.pi / 4) < 0 := by
  rw [quantum_correlation_at_optimal]
  constructor
  · have h : Real.sqrt 2 < 2 := sqrt_two_lt_two
    linarith
  · have h : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (2:ℝ) > 0)
    linarith


/-! ## The π/4 Mystery

Why π/4? This is the deep question.

In QM: The optimal angle is π/4 because it maximizes |S| given the
constraint that observables are dichotomic (A² = I).

In the thermal picture: The optimal "correlation angle" should emerge
from KMS periodicity 2π and the constraint |ε| < 1.

KEY OBSERVATION: π/4 = 2π/8 = (modular period)/8

The "eighth" appears because:
- CHSH has 4 correlation terms
- Each involves a PAIR of angles (Alice's and Bob's)
- 4 × 2 = 8 "angle slots"
- Distributing 2π evenly gives 2π/8 = π/4 per slot
-/



/-- The optimal angle is 1/8 of the modular period -/
lemma optimal_angle_is_eighth : Real.pi / 4 = modularPeriod' / 8 := by
  unfold modularPeriod'
  ring

/-- The number of "angle slots" in CHSH -/
def chsh_angle_slots : ℕ := 8

/-- Distributing the modular period evenly -/
lemma even_distribution : modularPeriod' / chsh_angle_slots = Real.pi / 4 := by
  unfold modularPeriod' chsh_angle_slots
  simp only [Nat.cast_ofNat]
  ring

/-- The cosine of the evenly-distributed angle gives √2/2 -/
lemma cos_even_distribution : Real.cos (modularPeriod' / chsh_angle_slots) = Real.sqrt 2 / 2 := by
  rw [even_distribution]
  exact Real.cos_pi_div_four

/-- Four such cosines sum to 2√2 -/
lemma four_cosines_sum : 4 * (Real.sqrt 2 / 2) = 2 * Real.sqrt 2 := by
  ring

/-- The Tsirelson bound emerges from evenly distributing the modular period -/
theorem tsirelson_from_modular_geometry :
    4 * Real.cos (modularPeriod' / chsh_angle_slots) = CHSH_quantum := by
  rw [cos_even_distribution]
  unfold CHSH_quantum
  ring

/-- Connection to ε_tsirelson via trigonometry.

    ε_tsirelson = (√2 - 1)/2

    Note that: 1 - cos(π/4) = 1 - √2/2 = (2 - √2)/2
    And: cos(π/4) - cos(π/2) = √2/2 - 0 = √2/2

    The ε measures "how far" the thermal correlation deviates from
    the "base" (classical) configuration. -/
lemma epsilon_from_trig :
    ε_tsirelson = (1 - Real.cos (Real.pi / 4)) / Real.sqrt 2 := by
  unfold ε_tsirelson
  rw [Real.cos_pi_div_four]
  have h : Real.sqrt 2 ≠ 0 := by simp only [ne_eq, Nat.ofNat_nonneg, sqrt_eq_zero,
    OfNat.ofNat_ne_zero, not_false_eq_true]
  field_simp
  ring_nf
  rw [@neg_add_eq_sub]
  simp only [Nat.ofNat_nonneg, sq_sqrt]

/-- Alternative form: ε in terms of sine -/
lemma epsilon_from_sine :
    ε_tsirelson = Real.sin (Real.pi / 8) ^ 2 / (Real.sqrt 2 / 2) := by
  unfold ε_tsirelson
  field_simp
  simp only [Real.sin_pi_div_eight]
  -- Goal: √2 * (√2 - 1) = 2 ^ 2 * (√(2 - √2) / 2) ^ 2
  have h1 : Real.sqrt 2 * (Real.sqrt 2 - 1) = 2 - Real.sqrt 2 := by
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
    linarith
  have h2 : (2 : ℝ) ^ 2 * (Real.sqrt (2 - Real.sqrt 2) / 2) ^ 2 = 2 - Real.sqrt 2 := by
    have h_nonneg : 2 - Real.sqrt 2 ≥ 0 := by
      have : Real.sqrt 2 ≤ 2 := le_of_lt sqrt_two_lt_two
      linarith
    rw [div_pow, sq_sqrt h_nonneg]
    ring
  rw [h1, h2]


/-- The "correlation deficit" from classical maximum.

    Classical: maximum |E| = 1 (perfect correlation/anticorrelation)
    Quantum at π/4: |E| = √2/2 ≈ 0.707

    Deficit = 1 - √2/2 = (2 - √2)/2 -/
noncomputable def correlationDeficit : ℝ := 1 - Real.sqrt 2 / 2

lemma deficit_value : correlationDeficit = (2 - Real.sqrt 2) / 2 := by
  unfold correlationDeficit
  ring

/-- The deficit relates to ε_tsirelson -/
lemma deficit_epsilon_relation :
    correlationDeficit = ε_tsirelson * Real.sqrt 2 := by
  unfold correlationDeficit ε_tsirelson
  have h : Real.sqrt 2 ≠ 0 := by simp only [ne_eq, Nat.ofNat_nonneg, sqrt_eq_zero,
    OfNat.ofNat_ne_zero, not_false_eq_true]
  field_simp
  rw [@mul_sub_one]
  simp only [Nat.ofNat_nonneg, mul_self_sqrt]

end ThermalBell
