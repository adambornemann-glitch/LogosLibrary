/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Pauli Matrices

The Pauli matrices σₓ, σᵧ, σᵤ form the fundamental representation of the
spin-1/2 angular momentum algebra su(2). They satisfy:

  σᵢ² = I           (involutions)
  {σᵢ, σⱼ} = 0      for i ≠ j (anticommutation)
  [σᵢ, σⱼ] = 2iεᵢⱼₖσₖ  (Lie algebra)

## Main definitions

* `pauliX`, `pauliY`, `pauliZ`: The three Pauli matrices

## Main results

* `pauliX_sq`, `pauliY_sq`, `pauliZ_sq`: Each Pauli matrix squares to I
* `pauliX_hermitian`, `pauliY_hermitian`, `pauliZ_hermitian`: All are Hermitian
* `pauliXY_anticommute`, `pauliXZ_anticommute`, `pauliYZ_anticommute`: Anticommutation relations

## Physical interpretation

The Pauli matrices represent spin-1/2 angular momentum operators:
- σₓ: spin measurement along x-axis, eigenstates |→⟩, |←⟩
- σᵧ: spin measurement along y-axis, eigenstates |↻⟩, |↺⟩
- σᵤ: spin measurement along z-axis, eigenstates |↑⟩, |↓⟩

The eigenvalues ±1 correspond to spin ±ℏ/2 in units where ℏ = 1.
-/

namespace PaulDirac

open Complex

/-- Pauli-X (σₓ): spin flip operator. Real symmetric.

      ┌     ┐
σₓ =  │ 0 1 │
      │ 1 0 │
      └     ┘

Eigenvectors: |+⟩ = (1,1)/√2, |-⟩ = (1,-1)/√2 with eigenvalues ±1. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli-Y (σᵧ): spin flip with phase. Imaginary antisymmetric, but still Hermitian.

      ┌      ┐
σᵧ =  │ 0 -i │
      │ i  0 │
      └      ┘

The only Pauli matrix with imaginary entries. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- Pauli-Z (σᵤ): spin measurement in z-direction. Real diagonal.

      ┌      ┐
σᵤ =  │ 1  0 │
      │ 0 -1 │
      └      ┘

Eigenvectors: |↑⟩ = (1,0), |↓⟩ = (0,1) with eigenvalues +1, -1. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]


/-! ### Hermiticity

All Pauli matrices are Hermitian (self-adjoint), which is required for them
to represent physical observables. -/

/-- σₓ is Hermitian: real symmetric matrix. -/
lemma pauliX_hermitian : pauliX.conjTranspose = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose, Matrix.of_apply]

/-- σᵧ is Hermitian: the ±I entries are in conjugate positions.

Despite having imaginary entries, σᵧ is Hermitian because:
  (σᵧ)†ᵢⱼ = conj((σᵧ)ⱼᵢ) = conj(±I) = ∓I = (σᵧ)ᵢⱼ -/
lemma pauliY_hermitian : pauliY.conjTranspose = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, Matrix.conjTranspose, Matrix.of_apply, conj_I]

/-- σᵤ is Hermitian: real diagonal matrix. -/
lemma pauliZ_hermitian : pauliZ.conjTranspose = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose, Matrix.of_apply]


/-! ### Involution property

Each Pauli matrix squares to the identity, so eigenvalues are ±1. -/

/-- σₓ² = I: eigenvalues are ±1, corresponding to spin-right and spin-left states. -/
lemma pauliX_sq : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- σᵧ² = I: the product (-I)(I) = 1 on the off-diagonal. -/
lemma pauliY_sq : pauliY * pauliY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

/-- σᵤ² = I: diagonal entries (±1)² = 1. -/
lemma pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]


/-! ### Anticommutation relations

Distinct Pauli matrices anticommute: {σᵢ, σⱼ} = σᵢσⱼ + σⱼσᵢ = 0 for i ≠ j.

This is the Clifford algebra Cl(3) relation that makes spin non-commutative
and underlies the uncertainty principle for spin measurements along different axes. -/

/-- σₓ and σᵧ anticommute: {σₓ, σᵧ} = 0.

This is the Clifford algebra relation that makes spin non-commutative. -/
lemma pauliXY_anticommute : pauliX * pauliY + pauliY * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, pauliY, Matrix.add_apply]

/-- σₓ and σᵤ anticommute: {σₓ, σᵤ} = 0. -/
lemma pauliXZ_anticommute : pauliX * pauliZ + pauliZ * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, pauliZ, Matrix.add_apply]

/-- σᵧ and σᵤ anticommute: {σᵧ, σᵤ} = 0. -/
lemma pauliYZ_anticommute : pauliY * pauliZ + pauliZ * pauliY = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliY, pauliZ, Matrix.add_apply]

end PaulDirac
