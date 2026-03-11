/-
Copyright (c) 2025 Bell Theorem Formalization Project
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla
Ported by: Adam Bornemann
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Matrix.Normed
import LogosLibrary.QuantumMechanics.BellsTheorem.Basic

open Matrix Complex MatrixGroups

namespace QuantumCHSH

/-! ## Pauli Matrices -/

/-- Pauli X matrix: σₓ = |0⟩⟨1| + |1⟩⟨0| -/
def σₓ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Pauli Y matrix: σᵧ = -i|0⟩⟨1| + i|1⟩⟨0| -/
def σᵧ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

/-- Pauli Z matrix: σ_z = |0⟩⟨0| - |1⟩⟨1| -/
def σ_z : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- The 2×2 identity matrix -/
def I₂ : Matrix (Fin 2) (Fin 2) ℂ := 1

/-! ## Properties of Pauli Matrices -/

lemma σₓ_hermitian : σₓ.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σₓ, conjTranspose, of_apply, star] <;> rfl

lemma σᵧ_hermitian : σᵧ.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp only [Fin.zero_eta, Fin.isValue, conjTranspose_apply, RCLike.star_def]
  simp only [σᵧ, of_apply, Fin.isValue,
    cons_val', cons_val_zero, empty_val', cons_val_fin_one]
  · simp only [map_zero]
  · simp only [Fin.mk_one, Fin.isValue]
    simp only [σᵧ, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    simp only [Complex.conj_I]
  · simp only [Fin.isValue, Fin.mk_one]
    simp only [σᵧ, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    exact conj_neg_I
  · simp only [Fin.mk_one, Fin.isValue]; exact conj_eq_iff_re.mpr rfl

lemma σ_z_hermitian : σ_z.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp only [σ_z, conjTranspose_apply, of_apply, star, Fin.zero_eta, Fin.isValue,
    cons_val', cons_val_zero, empty_val', cons_val_fin_one]
  · simp only [one_re, one_im, neg_zero]; rfl
  · simp only [Fin.mk_one, Fin.isValue, cons_val_one, zero_re, zero_im, neg_zero, cons_val_fin_one]; rfl
  · simp only [Fin.mk_one, Fin.isValue, cons_val_one, cons_val_fin_one, zero_re, zero_im, neg_zero]; rfl
  · simp only [Fin.mk_one, Fin.isValue, cons_val_one, cons_val_fin_one, neg_re, one_re, neg_im,
    one_im, neg_zero]
    exact Complex.ext rfl (by simp [Complex.neg_im, Complex.one_im])

lemma σₓ_sq : σₓ * σₓ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σₓ, Matrix.mul_apply, Fin.sum_univ_two]

lemma σᵧ_sq : σᵧ * σᵧ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [σᵧ, Matrix.mul_apply, Fin.sum_univ_two]

lemma σ_z_sq : σ_z * σ_z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ_z, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli matrices anticommute: σₓσ_z = -σ_zσₓ -/
lemma σₓ_σ_z_anticomm : σₓ * σ_z = -σ_z * σₓ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [σₓ, σ_z, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## The Bell State -/

/-- The singlet (Bell) state |Ψ⁻⟩ = (|01⟩ - |10⟩)/√2 as a ket vector -/
noncomputable def ket_Ψ_minus : Fin 4 → ℂ := ![0, 1/Real.sqrt 2, -1/Real.sqrt 2, 0]

/-- The Bell state |Ψ⁻⟩ = (1/√2)(|01⟩ - |10⟩) as a density matrix -/
noncomputable def ρ_Ψ_minus : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j =>
    match i, j with
    | (0, 1), (0, 1) =>  (1/2 : ℂ)
    | (0, 1), (1, 0) => -(1/2 : ℂ)
    | (1, 0), (0, 1) => -(1/2 : ℂ)
    | (1, 0), (1, 0) =>  (1/2 : ℂ)
    | _, _ => 0

lemma ρ_Ψ_minus_trace : ρ_Ψ_minus.trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, ρ_Ψ_minus, Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fin.isValue]
  norm_num

end QuantumCHSH
