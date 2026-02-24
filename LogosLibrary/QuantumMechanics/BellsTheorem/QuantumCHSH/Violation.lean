import LogosLibrary.QuantumMechanics.BellsTheorem.QuantumCHSH.Correlations

open Matrix Complex MatrixGroups
namespace QuantumCHSH

/-! ## The Main Result -/

/-- The CHSH operator for quantum observables -/
noncomputable def CHSH_quantum : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  A₀ * B₁ - A₀ * B₀ + A₁ * B₀ + A₁ * B₁

/-- The CHSH expectation value -/
noncomputable def CHSH_value : ℂ :=
  expectation CHSH_quantum ρ_Ψ_minus

/-- **Quantum CHSH Violation**: The Bell state achieves S = 2√2.

This is the maximum quantum violation, known as the Tsirelson bound. -/
theorem quantum_chsh_value : CHSH_value = 2 * Real.sqrt 2 := by
  unfold CHSH_value expectation CHSH_quantum
  calc ((A₀ * B₁ - A₀ * B₀ + A₁ * B₀ + A₁ * B₁) * ρ_Ψ_minus).trace
      = (A₀ * B₁ * ρ_Ψ_minus).trace - (A₀ * B₀ * ρ_Ψ_minus).trace +
        (A₁ * B₀ * ρ_Ψ_minus).trace + (A₁ * B₁ * ρ_Ψ_minus).trace := by
          simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.trace_sub, Matrix.trace_add]
      _ = correlation A₀ B₁ ρ_Ψ_minus - correlation A₀ B₀ ρ_Ψ_minus +
          correlation A₁ B₀ ρ_Ψ_minus + correlation A₁ B₁ ρ_Ψ_minus := by
          unfold correlation
          simp only [mul_assoc]
      _ = 1/Real.sqrt 2 - (-1/Real.sqrt 2) + 1/Real.sqrt 2 + 1/Real.sqrt 2 := by
          rw [E_A₀_B₁, E_A₀_B₀, E_A₁_B₀, E_A₁_B₁]
      _ = 4/Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by
          have sqrt2_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
            rw [sq, ← Complex.ofReal_mul]
            norm_num
          have sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
            simp [Real.sqrt_ne_zero'.mpr (by norm_num : (2:ℝ) > 0)]
          calc (4 : ℂ) / Real.sqrt 2
              = 4 / Real.sqrt 2 * (Real.sqrt 2 / Real.sqrt 2) := by rw [div_self sqrt2_ne, mul_one]
            _ = (4 * Real.sqrt 2) / (Real.sqrt 2 * Real.sqrt 2) := by ring
            _ = (4 * Real.sqrt 2) / 2 := by rw [← sq, sqrt2_sq]
            _ = 2 * Real.sqrt 2 := by ring

/-- The quantum violation exceeds the LHV bound -/
theorem quantum_exceeds_lhv : (2 : ℝ) * Real.sqrt 2 > 2 := by
  have h : Real.sqrt 2 > 1 := Real.one_lt_sqrt_two
  linarith
