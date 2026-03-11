/-
Copyright (c) 2025 Bell Theorem Formalization Project
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla
Ported by: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.BellsTheorem.CHSH_bounds.CHSH_Basic
import LogosLibrary.QuantumMechanics.BellsTheorem.CHSH_bounds.Separable
import LogosLibrary.QuantumMechanics.BellsTheorem.CHSH_bounds.Op_square

open MeasureTheory ProbabilityTheory Matrix Complex

/-! ## Quantum State Foundations -/

namespace QuantumInfo



/-- Commuting observables cannot violate CHSH -/
lemma CHSH_commuting_bound {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hT : IsCHSHTuple A₀ A₁ B₀ B₁)
    (hcomm : (A₀ * A₁ = A₁ * A₀) ∨ (B₀ * B₁ = B₁ * B₀))
    (ρ : DensityMatrix n) :
    ‖(CHSH_expect A₀ A₁ B₀ B₁ ρ.toMatrix)‖ ≤ 2 := by
  -- When [A₀,A₁]=0 or [B₀,B₁]=0, the commutator product vanishes
  have h_comm_zero : ⟦A₀, A₁⟧ * ⟦B₀, B₁⟧ = 0 := by
    rcases hcomm with hA | hB
    · -- [A₀, A₁] = 0
      unfold comm
      simp only [hA, sub_self, Matrix.zero_mul]
    · -- [B₀, B₁] = 0
      unfold comm
      simp only [hB, sub_self, Matrix.mul_zero]
  -- So S² = 4I
  have h_sq : CHSH_op A₀ A₁ B₀ B₁ * CHSH_op A₀ A₁ B₀ B₁ = 4 • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [CHSH_op_square A₀ A₁ B₀ B₁ hT, h_comm_zero, sub_zero]
  -- Let S' = S/2, then S'² = I
  let S := CHSH_op A₀ A₁ B₀ B₁
  let S' := (1/2 : ℂ) • S
  have h_S'_sq : S' * S' = 1 := by
    simp only [S', Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [h_sq]
    module
  -- S' is Hermitian (CHSH operator is Hermitian)
  have h_S_herm : S.IsHermitian := by
    show (CHSH_op A₀ A₁ B₀ B₁).IsHermitian
    simp only [CHSH_op]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_sub]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    rw [hT.A₀_herm.eq, hT.A₁_herm.eq, hT.B₀_herm.eq, hT.B₁_herm.eq]
    rw [hT.comm_A₀_B₁, hT.comm_A₀_B₀, hT.comm_A₁_B₀, hT.comm_A₁_B₁]
  have h_S'_herm : S'.IsHermitian := by
    simp only [S', Matrix.IsHermitian]
    rw [Matrix.conjTranspose_smul, h_S_herm.eq]
    congr 1
    simp only [one_div, star_inv₀, star_ofNat]
  -- Apply dichotomic bound to S'
  have h_bound := dichotomic_expectation_bound S' h_S'_herm h_S'_sq ρ
  -- Relate back to S
  simp only [CHSH_expect]
  calc ‖(S * ρ.toMatrix).trace‖
      = ‖((2 : ℂ) • S' * ρ.toMatrix).trace‖ := by simp [S']
    _ = ‖(2 : ℂ) • (S' * ρ.toMatrix).trace‖ := by rw [Matrix.smul_mul, Matrix.trace_smul]
    _ = ‖(2 : ℂ)‖ * ‖(S' * ρ.toMatrix).trace‖ := norm_smul _ _
    _ ≤ 2 * 1 := by
        apply mul_le_mul _ h_bound (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
        simp only [norm_ofNat, le_refl]
    _ = 2 := by ring



end QuantumInfo
