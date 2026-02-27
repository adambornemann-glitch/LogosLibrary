import LogosLibrary.Superior.SplitMechanics.BellsTheorem.TLHV

open ThermalBell BellTheorem ProbabilityTheory MeasureTheory

namespace ThermalBell

/-! ## Part 12: Characterizing Quantum-Compatible ε

Quantum mechanics gives E(θ) = -cos(θ) for the singlet.
The thermal model gives E(i,j) = ∫ A_i B_j (1 + ε_{ij}) dμ₀.

Question: What constraints on ε are needed to reproduce -cos(θ)?
-/

/-- The quantum correlation function -/
noncomputable def E_Q (θ : ℝ) : ℝ := -Real.cos θ

variable {Λ : Type*} [MeasurableSpace Λ]

/-- The classical (LHV) correlation: ∫ A B dμ₀ for dichotomic A, B -/
noncomputable def E_C {Λ : Type*} [MeasurableSpace Λ] (μ₀ : Measure Λ)
    [IsProbabilityMeasure μ₀]
    (A B : Λ → ℝ) : ℝ := ∫ ω, A ω * B ω ∂μ₀

/-- The thermal correction: ∫ A B ε dμ₀ -/
noncomputable def E_thermal {Λ : Type*} [MeasurableSpace Λ] (μ₀ : Measure Λ)
    (A B ε : Λ → ℝ) : ℝ := ∫ ω, A ω * B ω * ε ω ∂μ₀

/-- The full thermal correlation -/
noncomputable def E_full {Λ : Type*} [MeasurableSpace Λ] (μ₀ : Measure Λ)
    [IsProbabilityMeasure μ₀]
    (A B ε : Λ → ℝ) : ℝ := E_C μ₀ A B + E_thermal μ₀ A B ε

/-- For thermal model to match quantum, we need E_full = E_Q -/
def quantum_compatible {Λ : Type*} [MeasurableSpace Λ] (μ₀ : Measure Λ)
    [IsProbabilityMeasure μ₀]
    (A B ε : Λ → ℝ) (θ : ℝ) : Prop :=
  E_full μ₀ A B ε = E_Q θ

/-- The required thermal correction to match quantum -/
noncomputable def required_thermal_correction {Λ : Type*} [MeasurableSpace Λ]
    (μ₀ : Measure Λ) [IsProbabilityMeasure μ₀]
    (A B : Λ → ℝ) (θ : ℝ) : ℝ :=
  E_Q θ - E_C μ₀ A B

/-- If E_C is fixed, the required thermal correction determines ε -/
lemma thermal_correction_determines (Λ : Type*) [MeasurableSpace Λ] (μ₀ : Measure Λ)
    [IsProbabilityMeasure μ₀] (A B ε : Λ → ℝ) (θ : ℝ) :
    quantum_compatible μ₀ A B ε θ ↔
    E_thermal μ₀ A B ε = required_thermal_correction μ₀ A B θ := by
  unfold quantum_compatible E_full required_thermal_correction
  constructor
  · intro h
    linarith
  · intro h
    linarith

/- For the optimal CHSH angles, what are the required corrections? -/

/-- At θ = 0: E_Q = -1 (perfect anticorrelation) -/
lemma E_Q_zero : E_Q 0 = -1 := by
  unfold E_Q
  simp [Real.cos_zero]

/-- At θ = π: E_Q = 1 (perfect correlation) -/
lemma E_Q_pi : E_Q Real.pi = 1 := by
  unfold E_Q
  simp [Real.cos_pi]

/-- At θ = π/2: E_Q = 0 (no correlation) -/
lemma E_Q_pi_div_two : E_Q (Real.pi / 2) = 0 := by
  unfold E_Q
  simp [Real.cos_pi_div_two]

/-- At θ = π/4: E_Q = -√2/2 -/
lemma E_Q_pi_div_four : E_Q (Real.pi / 4) = -Real.sqrt 2 / 2 := by
  unfold E_Q
  rw [Real.cos_pi_div_four]
  ring

/-- At θ = 3π/4: E_Q = √2/2 -/
lemma E_Q_three_pi_div_four : E_Q (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
  unfold E_Q
  rw [cos_three_pi_div_four]
  ring

/-- The "gap" between classical maximum and quantum at π/4 -/
noncomputable def correlation_gap_pi_four : ℝ := |E_Q (Real.pi / 4)| - 1

/-- This gap is negative: quantum |E| < 1 at π/4 -/
lemma correlation_gap_negative : correlation_gap_pi_four < 0 := by
  unfold correlation_gap_pi_four
  rw [E_Q_pi_div_four]
  simp only [sub_neg]
  have h : Real.sqrt 2 / 2 < 1 := by
    have : Real.sqrt 2 < 2 := sqrt_two_lt_two
    linarith
  have h_pos : Real.sqrt 2 / 2 > 0 := by
    have : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (2:ℝ) > 0)
    linarith
  rw [abs_of_neg (by linarith : -Real.sqrt 2 / 2 < 0)]
  linarith

/-- Classical dichotomic correlation is bounded -/
lemma E_C_bounded {Λ : Type*} [MeasurableSpace Λ] (μ₀ : Measure Λ)
    [IsProbabilityMeasure μ₀]
    (A B : Λ → ℝ)
    (hA : ∀ᵐ ω ∂μ₀, A ω = 1 ∨ A ω = -1)
    (hB : ∀ᵐ ω ∂μ₀, B ω = 1 ∨ B ω = -1)
    (hA_int : Integrable A μ₀) (hB_int : Integrable B μ₀) :
    -1 ≤ E_C μ₀ A B ∧ E_C μ₀ A B ≤ 1 := by
  unfold E_C
  have h_pm : ∀ᵐ ω ∂μ₀, A ω * B ω = 1 ∨ A ω * B ω = -1 := by
    filter_upwards [hA, hB] with ω ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
  have h_abs : ∀ᵐ ω ∂μ₀, |A ω * B ω| = 1 := by
    filter_upwards [h_pm] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have h_int : Integrable (fun ω => A ω * B ω) μ₀ := by
    apply Integrable.mono' (integrable_const 1)
    · exact (hA_int.aestronglyMeasurable.mul hB_int.aestronglyMeasurable)
    · filter_upwards [h_abs] with ω hω
      simp only [norm_mul, Real.norm_eq_abs]
      rw [← @abs_mul]
      simp [hω]
  have h_bound : |∫ ω, A ω * B ω ∂μ₀| ≤ 1 := by
    calc |∫ ω, A ω * B ω ∂μ₀|
        ≤ ∫ ω, |A ω * B ω| ∂μ₀ := abs_integral_le_integral_abs
      _ = ∫ ω, (1 : ℝ) ∂μ₀ := by
          apply integral_congr_ae
          filter_upwards [h_abs] with ω hω
          exact hω
      _ = 1 := by simp
  exact abs_le.mp h_bound

/-- The structure of a quantum-compatible thermal model -/
structure QuantumCompatibleModel (Λ : Type*) [MeasurableSpace Λ] where
  /-- Base measure -/
  μ₀ : ProbabilityMeasure Λ
  /-- Response functions for each angle -/
  A : ℝ → Λ → ℝ  -- A(θ, ω)
  B : ℝ → Λ → ℝ  -- B(θ, ω)
  /-- Deviation function -/
  ε : ℝ → Λ → ℝ  -- ε(θ, ω), where θ is the angle between settings
  /-- Dichotomic outputs -/
  A_dichotomic : ∀ θ, ∀ᵐ ω ∂(μ₀ : Measure Λ), A θ ω = 1 ∨ A θ ω = -1
  B_dichotomic : ∀ θ, ∀ᵐ ω ∂(μ₀ : Measure Λ), B θ ω = 1 ∨ B θ ω = -1
  /-- Bounded deviation -/
  ε_bounded : ∀ θ ω, |ε θ ω| < 1
  /-- Quantum compatible at all angles -/
  compatible : ∀ θ, E_full (μ₀ : Measure Λ) (A θ) (B θ) (ε θ) = E_Q θ

/-- For a quantum compatible model, ε at θ = 0 must compensate for E_C ≠ -1 -/
lemma ε_at_zero (Λ : Type*) [MeasurableSpace Λ] (M : QuantumCompatibleModel Λ) :
    E_thermal (M.μ₀ : Measure Λ) (M.A 0) (M.B 0) (M.ε 0) = -1 - E_C M.μ₀ (M.A 0) (M.B 0) := by
  have h := M.compatible 0
  unfold E_full at h
  rw [E_Q_zero] at h
  linarith

/-- For a quantum compatible model, if E_C = -1 at θ = 0, then ε contribution is 0 -/
lemma ε_zero_when_classical_matches (Λ : Type*) [MeasurableSpace Λ] (M : QuantumCompatibleModel Λ)
    (h_classical : E_C M.μ₀ (M.A 0) (M.B 0) = -1) :
    E_thermal (M.μ₀ : Measure Λ) (M.A 0) (M.B 0) (M.ε 0) = 0 := by
  have h := ε_at_zero Λ M
  rw [h_classical] at h
  linarith

/-- The ε contribution at π/4 -/
lemma ε_at_pi_four (Λ : Type*) [MeasurableSpace Λ] (M : QuantumCompatibleModel Λ) :
    E_thermal (M.μ₀ : Measure Λ) (M.A (Real.pi/4)) (M.B (Real.pi/4)) (M.ε (Real.pi/4)) =
    -Real.sqrt 2 / 2 - E_C M.μ₀ (M.A (Real.pi/4)) (M.B (Real.pi/4)) := by
  have h := M.compatible (Real.pi / 4)
  unfold E_full at h
  rw [E_Q_pi_div_four] at h
  linarith

/-- If E_C = 0 at π/4 (uncorrelated classically), ε must provide -√2/2 -/
lemma ε_provides_quantum (Λ : Type*) [MeasurableSpace Λ] (M : QuantumCompatibleModel Λ)
    (h_uncorr : E_C M.μ₀ (M.A (Real.pi/4)) (M.B (Real.pi/4)) = 0) :
    E_thermal (M.μ₀ : Measure Λ) (M.A (Real.pi/4)) (M.B (Real.pi/4)) (M.ε (Real.pi/4)) =
    -Real.sqrt 2 / 2 := by
  have h := ε_at_pi_four Λ M
  rw [h_uncorr] at h
  linarith

/-- The maximum |ε| needed across all angles -/
noncomputable def max_ε_needed (E_C_val : ℝ) : ℝ → ℝ := fun θ =>
  |E_Q θ - E_C_val|

/-- If E_C = 0 everywhere (uniform random base), the ε must do all the work -/
lemma ε_does_all_work (θ : ℝ) : max_ε_needed 0 θ = |E_Q θ| := by
  unfold max_ε_needed
  simp

/-- The maximum ε needed for uniform base is at θ = 0 or θ = π -/
lemma max_ε_at_extremes : max_ε_needed 0 0 = 1 ∧ max_ε_needed 0 Real.pi = 1 := by
  constructor
  · unfold max_ε_needed E_Q
    simp [Real.cos_zero]
  · unfold max_ε_needed E_Q
    simp [Real.cos_pi]

end ThermalBell
