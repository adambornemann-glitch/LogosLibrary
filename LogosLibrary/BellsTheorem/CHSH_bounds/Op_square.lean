/-
Copyright (c) 2025 Bell Theorem Formalization Project
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla
Ported by: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.BellsTheorem.Basic

open MeasureTheory ProbabilityTheory Matrix Complex

/-! ## Quantum State Foundations -/

namespace QuantumInfo

/-! ## Key Algebraic Identity for CHSH² -/

/-- The commutator of two matrices -/
noncomputable def comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A * B - B * A

-- Use ⟦A, B⟧ notation to avoid conflict with list literal [A, B]
notation "⟦" A ", " B "⟧" => comm A B

/-- For involutions A² = B² = I: (A + B)² = 2I + AB + BA -/
lemma add_sq_involution {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A * A = 1) (hB : B * B = 1) :
    (A + B) * (A + B) = 2 • (1 : Matrix _ _ ℂ) + A * B + B * A := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  rw [hA, hB]
  module

/-- For involutions A² = B² = I: (A - B)² = 2I - AB - BA -/
lemma sub_sq_involution {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A * A = 1) (hB : B * B = 1) :
    (A - B) * (A - B) = 2 • (1 : Matrix _ _ ℂ) - A * B - B * A := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [hA, hB]
  module

/-- For involutions: (A - B)(A + B) = [A, B] -/
lemma sub_mul_add_involution {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A * A = 1) (hB : B * B = 1) :
    (A - B) * (A + B) = comm A B := by
  unfold comm
  rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add]
  rw [hA, hB]
  module

/-- For involutions: (A + B)(A - B) = -[A, B] -/
lemma add_mul_sub_involution {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A * A = 1) (hB : B * B = 1) :
    (A + B) * (A - B) = -comm A B := by
  unfold comm
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [hA, hB]
  module

/-- CHSH operator can be factored as (B₁ - B₀)A₀ + (B₀ + B₁)A₁ when Aᵢ commutes with Bⱼ -/
lemma CHSH_op_factor {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hc00 : A₀ * B₀ = B₀ * A₀) (hc01 : A₀ * B₁ = B₁ * A₀)
    (hc10 : A₁ * B₀ = B₀ * A₁) (hc11 : A₁ * B₁ = B₁ * A₁) :
    CHSH_op A₀ A₁ B₀ B₁ = (B₁ - B₀) * A₀ + (B₀ + B₁) * A₁ := by
  unfold CHSH_op
  rw [hc00, hc01, hc10, hc11]
  rw [Matrix.sub_mul, Matrix.add_mul]
  module

/-- For involutions: (A - B)² + (A + B)² = 4I -/
lemma sub_sq_add_add_sq_involution {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A * A = 1) (hB : B * B = 1) :
    (A - B) * (A - B) + (A + B) * (A + B) = 4 • (1 : Matrix _ _ ℂ) := by
  rw [sub_sq_involution A B hA hB, add_sq_involution A B hA hB]
  module

/-- A₀ commutes with B₁ - B₀ -/
lemma comm_A_sub_B {n : ℕ} [NeZero n]
    (A B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hc0 : A * B₀ = B₀ * A) (hc1 : A * B₁ = B₁ * A) :
    A * (B₁ - B₀) = (B₁ - B₀) * A := by
  rw [Matrix.mul_sub, Matrix.sub_mul, hc0, hc1]

/-- A₀ commutes with B₀ + B₁ -/
lemma comm_A_add_B {n : ℕ} [NeZero n]
    (A B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hc0 : A * B₀ = B₀ * A) (hc1 : A * B₁ = B₁ * A) :
    A * (B₀ + B₁) = (B₀ + B₁) * A := by
  rw [Matrix.mul_add, Matrix.add_mul, hc0, hc1]

/-- (B₁ - B₀)(B₀ + B₁) = -[B₀, B₁] for involutions -/
lemma sub_mul_add_comm {n : ℕ} [NeZero n]
    (B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hB₀ : B₀ * B₀ = 1) (hB₁ : B₁ * B₁ = 1) :
    (B₁ - B₀) * (B₀ + B₁) = -comm B₀ B₁ := by
  unfold comm
  rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add]
  rw [hB₀, hB₁]
  module

/-- (B₀ + B₁)(B₁ - B₀) = [B₀, B₁] for involutions -/
lemma add_mul_sub_comm {n : ℕ} [NeZero n]
    (B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hB₀ : B₀ * B₀ = 1) (hB₁ : B₁ * B₁ = 1) :
    (B₀ + B₁) * (B₁ - B₀) = comm B₀ B₁ := by
  unfold comm
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [hB₀, hB₁]
  module

/-- Square of sum XA₀ + YA₁ when Aᵢ commutes with X, Y and Aᵢ² = I -/
lemma sq_sum_factor {n : ℕ} [NeZero n]
    (A₀ A₁ X Y : Matrix (Fin n) (Fin n) ℂ)
    (hA₀sq : A₀ * A₀ = 1) (hA₁sq : A₁ * A₁ = 1)
    (hcX0 : A₀ * X = X * A₀) (hcX1 : A₁ * X = X * A₁)
    (hcY0 : A₀ * Y = Y * A₀) (hcY1 : A₁ * Y = Y * A₁) :
    (X * A₀ + Y * A₁) * (X * A₀ + Y * A₁) =
    X * X + Y * Y + X * Y * A₀ * A₁ + Y * X * A₁ * A₀ := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  have h1 : X * A₀ * (X * A₀) = X * X := by
    calc X * A₀ * (X * A₀)
        = X * (A₀ * X) * A₀ := by
          rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc];
      _ = X * (X * A₀) * A₀ := by rw [hcX0]
      _ = X * X * A₀ * A₀ := by rw [Matrix.mul_assoc X X A₀]
      _ = X * X * (A₀ * A₀) := by rw [Matrix.mul_assoc (X * X)]
      _ = X * X * 1 := by rw [hA₀sq]
      _ = X * X := Matrix.mul_one _
  have h2 : Y * A₁ * (Y * A₁) = Y * Y := by
    calc Y * A₁ * (Y * A₁)
        = Y * (A₁ * Y) * A₁ := by
          rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc];
      _ = Y * (Y * A₁) * A₁ := by rw [hcY1]
      _ = Y * Y * A₁ * A₁ := by rw [Matrix.mul_assoc Y Y A₁]
      _ = Y * Y * (A₁ * A₁) := by rw [Matrix.mul_assoc (Y * Y)]
      _ = Y * Y * 1 := by rw [hA₁sq]
      _ = Y * Y := Matrix.mul_one _
  have h3 : X * A₀ * (Y * A₁) = X * Y * A₀ * A₁ := by
    calc X * A₀ * (Y * A₁)
        = X * (A₀ * Y) * A₁ := by
          rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc];
      _ = X * (Y * A₀) * A₁ := by rw [hcY0]
      _ = X * Y * A₀ * A₁ := by rw [Matrix.mul_assoc X Y A₀]
  have h4 : Y * A₁ * (X * A₀) = Y * X * A₁ * A₀ := by
    calc Y * A₁ * (X * A₀)
        = Y * (A₁ * X) * A₀ := by
          rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc];
      _ = Y * (X * A₁) * A₀ := by rw [hcX1]
      _ = Y * X * A₁ * A₀ := by rw [Matrix.mul_assoc Y X A₁]
  rw [h1, h2, h3, h4]
  module


/-- Commutators [A₀,A₁] and [B₀,B₁] commute when all Aᵢ commute with all Bⱼ -/
lemma comm_comm_comm {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hc00 : A₀ * B₀ = B₀ * A₀) (hc01 : A₀ * B₁ = B₁ * A₀)
    (hc10 : A₁ * B₀ = B₀ * A₁) (hc11 : A₁ * B₁ = B₁ * A₁) :
    comm A₀ A₁ * comm B₀ B₁ = comm B₀ B₁ * comm A₀ A₁ := by
  unfold comm
  simp only [Matrix.sub_mul, Matrix.mul_sub]
  -- Need to show products like A₀A₁B₀B₁ = B₀B₁A₀A₁
  have h1 : A₀ * A₁ * (B₀ * B₁) = B₀ * B₁ * (A₀ * A₁) := by
    calc A₀ * A₁ * (B₀ * B₁)
        = A₀ * (A₁ * B₀) * B₁ := by rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]
      _ = A₀ * (B₀ * A₁) * B₁ := by rw [hc10]
      _ = (A₀ * B₀) * A₁ * B₁ := by rw [← Matrix.mul_assoc A₀ B₀]
      _ = (B₀ * A₀) * A₁ * B₁ := by rw [hc00]
      _ = B₀ * (A₀ * A₁) * B₁ := by rw [Matrix.mul_assoc B₀]
      _ = B₀ * (A₀ * (A₁ * B₁)) := by rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]
      _ = B₀ * (A₀ * (B₁ * A₁)) := by rw [hc11]
      _ = B₀ * ((A₀ * B₁) * A₁) := by rw [← Matrix.mul_assoc A₀]
      _ = B₀ * ((B₁ * A₀) * A₁) := by rw [hc01]
      _ = B₀ * (B₁ * (A₀ * A₁)) := by rw [Matrix.mul_assoc B₁]
      _ = B₀ * B₁ * (A₀ * A₁) := by rw [← Matrix.mul_assoc B₀]
  have h2 : A₀ * A₁ * (B₁ * B₀) = B₁ * B₀ * (A₀ * A₁) := by
    calc A₀ * A₁ * (B₁ * B₀)
        = A₀ * (A₁ * B₁) * B₀ := by rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]
      _ = A₀ * (B₁ * A₁) * B₀ := by rw [hc11]
      _ = (A₀ * B₁) * A₁ * B₀ := by rw [← Matrix.mul_assoc A₀ B₁]
      _ = (B₁ * A₀) * A₁ * B₀ := by rw [hc01]
      _ = B₁ * (A₀ * A₁) * B₀ := by rw [Matrix.mul_assoc B₁]
      _ = B₁ * (A₀ * (A₁ * B₀)) := by rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]
      _ = B₁ * (A₀ * (B₀ * A₁)) := by rw [hc10]
      _ = B₁ * ((A₀ * B₀) * A₁) := by rw [← Matrix.mul_assoc A₀]
      _ = B₁ * ((B₀ * A₀) * A₁) := by rw [hc00]
      _ = B₁ * (B₀ * (A₀ * A₁)) := by rw [Matrix.mul_assoc B₀]
      _ = B₁ * B₀ * (A₀ * A₁) := by rw [← Matrix.mul_assoc B₁]
  have h3 : A₁ * A₀ * (B₀ * B₁) = B₀ * B₁ * (A₁ * A₀) := by
    calc A₁ * A₀ * (B₀ * B₁)
        = A₁ * (A₀ * B₀) * B₁ := by rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]
      _ = A₁ * (B₀ * A₀) * B₁ := by rw [hc00]
      _ = (A₁ * B₀) * A₀ * B₁ := by rw [← Matrix.mul_assoc A₁ B₀]
      _ = (B₀ * A₁) * A₀ * B₁ := by rw [hc10]
      _ = B₀ * (A₁ * A₀) * B₁ := by rw [Matrix.mul_assoc B₀]
      _ = B₀ * (A₁ * (A₀ * B₁)) := by rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]
      _ = B₀ * (A₁ * (B₁ * A₀)) := by rw [hc01]
      _ = B₀ * ((A₁ * B₁) * A₀) := by rw [← Matrix.mul_assoc A₁]
      _ = B₀ * ((B₁ * A₁) * A₀) := by rw [hc11]
      _ = B₀ * (B₁ * (A₁ * A₀)) := by rw [Matrix.mul_assoc B₁]
      _ = B₀ * B₁ * (A₁ * A₀) := by rw [← Matrix.mul_assoc B₀]
  have h4 : A₁ * A₀ * (B₁ * B₀) = B₁ * B₀ * (A₁ * A₀) := by
    calc A₁ * A₀ * (B₁ * B₀)
        = A₁ * (A₀ * B₁) * B₀ := by rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]
      _ = A₁ * (B₁ * A₀) * B₀ := by rw [hc01]
      _ = (A₁ * B₁) * A₀ * B₀ := by rw [← Matrix.mul_assoc A₁ B₁]
      _ = (B₁ * A₁) * A₀ * B₀ := by rw [hc11]
      _ = B₁ * (A₁ * A₀) * B₀ := by rw [Matrix.mul_assoc B₁]
      _ = B₁ * (A₁ * (A₀ * B₀)) := by rw [@Matrix.mul_assoc]; rw [@Matrix.mul_assoc]
      _ = B₁ * (A₁ * (B₀ * A₀)) := by rw [hc00]
      _ = B₁ * ((A₁ * B₀) * A₀) := by rw [← Matrix.mul_assoc A₁]
      _ = B₁ * ((B₀ * A₁) * A₀) := by rw [hc10]
      _ = B₁ * (B₀ * (A₁ * A₀)) := by rw [Matrix.mul_assoc B₀]
      _ = B₁ * B₀ * (A₁ * A₀) := by rw [← Matrix.mul_assoc B₁]
  rw [h1, h2, h3, h4]
  module

/-- The CHSH operator squared: S² = 4I - [A₀,A₁]·[B₀,B₁]

This is the key identity for deriving Tsirelson's bound. -/
theorem CHSH_op_square {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hT : IsCHSHTuple A₀ A₁ B₀ B₁) :
    CHSH_op A₀ A₁ B₀ B₁ * CHSH_op A₀ A₁ B₀ B₁ =
    4 • (1 : Matrix (Fin n) (Fin n) ℂ) - ⟦A₀, A₁⟧ * ⟦B₀, B₁⟧ := by
  -- Extract hypotheses
  have hA₀sq := hT.A₀_sq
  have hA₁sq := hT.A₁_sq
  have hB₀sq := hT.B₀_sq
  have hB₁sq := hT.B₁_sq
  have hc00 := hT.comm_A₀_B₀
  have hc01 := hT.comm_A₀_B₁
  have hc10 := hT.comm_A₁_B₀
  have hc11 := hT.comm_A₁_B₁
  -- Define X = B₁ - B₀, Y = B₀ + B₁
  let X := B₁ - B₀
  let Y := B₀ + B₁
  -- Commutativity lemmas for X, Y
  have hcX0 : A₀ * X = X * A₀ := comm_A_sub_B A₀ B₀ B₁ hc00 hc01
  have hcX1 : A₁ * X = X * A₁ := comm_A_sub_B A₁ B₀ B₁ hc10 hc11
  have hcY0 : A₀ * Y = Y * A₀ := comm_A_add_B A₀ B₀ B₁ hc00 hc01
  have hcY1 : A₁ * Y = Y * A₁ := comm_A_add_B A₁ B₀ B₁ hc10 hc11
  -- Factor CHSH operator
  have h_factor : CHSH_op A₀ A₁ B₀ B₁ = X * A₀ + Y * A₁ :=
    CHSH_op_factor A₀ A₁ B₀ B₁ hc00 hc01 hc10 hc11
  -- Square of factored form
  have h_sq := sq_sum_factor A₀ A₁ X Y hA₀sq hA₁sq hcX0 hcX1 hcY0 hcY1
  -- X*X + Y*Y = 4I
  have h_sum_sq : X * X + Y * Y = 4 • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have := sub_sq_add_add_sq_involution B₁ B₀ hB₁sq hB₀sq
    simp only [X, Y, add_comm B₀ B₁]
    exact this
  -- X*Y = -[B₀, B₁]
  have h_XY : X * Y = -comm B₀ B₁ := sub_mul_add_comm B₀ B₁ hB₀sq hB₁sq
  -- Y*X = [B₀, B₁]
  have h_YX : Y * X = comm B₀ B₁ := add_mul_sub_comm B₀ B₁ hB₀sq hB₁sq
  -- Commutators commute
  have h_comm := comm_comm_comm A₀ A₁ B₀ B₁ hc00 hc01 hc10 hc11
  -- Put it together
  rw [h_factor, h_sq, h_sum_sq, h_XY, h_YX]
  -- S² = 4I + (-[B₀,B₁])*A₀*A₁ + [B₀,B₁]*A₁*A₀
  --    = 4I - [B₀,B₁]*(A₀*A₁ - A₁*A₀)
  --    = 4I - [B₀,B₁]*[A₀,A₁]
  --    = 4I - [A₀,A₁]*[B₀,B₁]  (by commutativity)
  unfold comm at *
  rw [h_comm]
  rw [Matrix.mul_sub, Matrix.neg_mul, Matrix.neg_mul]
  simp only [Matrix.mul_assoc]
  module

end QuantumInfo
