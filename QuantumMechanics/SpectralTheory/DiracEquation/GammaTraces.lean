/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.CliffordAlgebra
import Mathlib.Analysis.Complex.Basic

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap


/-!
# Gamma Matrix Trace Identities

This file develops the trace identities for products of gamma matrices, which are
the workhorse formulas for computing Feynman diagrams in quantum electrodynamics
and quantum chromodynamics.

## Main definitions

* `gammaAt`: Helper to access gamma matrices by index μ ∈ {0,1,2,3}
* `minkowskiMetric`: The Minkowski metric tensor η^μν = diag(1,-1,-1,-1)

## Main results

### Single gamma traces
* `gamma_trace_zero`: Tr(γ^μ) = 0

### Two-gamma traces
* `gamma_trace_two`: Tr(γ^μ γ^ν) = 4η^μν

### Three-gamma traces (odd number)
* `gamma_trace_three`: Tr(γ^μ γ^ν γ^ρ) = 0

### Gamma squares (derived from Clifford relations)
* `gamma0_sq_eq_one`: (γ⁰)² = I
* `gamma1_sq_eq_neg_one`: (γ¹)² = -I
* `gamma2_sq_eq_neg_one`: (γ²)² = -I
* `gamma3_sq_eq_neg_one`: (γ³)² = -I

## Implementation notes

The two-gamma trace formula Tr(γ^μ γ^ν) = 4η^μν is proved by case analysis on
all 16 pairs (μ,ν). Diagonal cases use the gamma square lemmas; off-diagonal
cases use anticommutation to show the trace vanishes.

The three-gamma trace formula uses a clever trick: insert γ⁵γ⁵ = I, use
anticommutation to move γ⁵ through, and observe that Tr(A) = -Tr(A) implies Tr(A) = 0.

## References

* [Peskin, Schroeder, *An Introduction to Quantum Field Theory*][peskin1995], Appendix A
* [Srednicki, *Quantum Field Theory*][srednicki2007], Chapter 36

## Tags

gamma matrices, trace identities, Feynman diagrams, QED, Clifford algebra
-/

namespace Dirac.Matrices

open Complex Matrix

/-! ## Minkowski Metric -/

/-- The Minkowski metric tensor η^μν = diag(1, -1, -1, -1).

This is the "mostly minus" convention standard in particle physics.
The "mostly plus" convention diag(-1,1,1,1) is used in general relativity. -/
def minkowskiMetric (μ ν : Fin 4) : ℂ :=
  if μ = ν then
    if μ = 0 then 1 else -1
  else 0

/-- The chirality matrix γ⁵ = iγ⁰γ¹γ²γ³-/
def gamma5 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]


/-! ## Gamma Matrix Access -/

/-- Helper to get gamma matrix by index.

Provides uniform access: gammaAt 0 = γ⁰, gammaAt 1 = γ¹, etc.
Useful for stating general identities that hold for all μ. -/
def gammaAt (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  match μ with
  | 0 => gamma0
  | 1 => gamma1
  | 2 => gamma2
  | 3 => gamma3


/-! ## Single Gamma Traces -/

/-- Tr(γ⁰) = 0: The timelike gamma matrix is traceless.

**Proof**: γ⁰ = diag(1, 1, -1, -1), so Tr = 1 + 1 + (-1) + (-1) = 0. -/
lemma gamma0_trace_zero : Matrix.trace gamma0 = 0 := by
  unfold gamma0 Matrix.trace Matrix.diag
  simp only [Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.cons_val_one,
    Matrix.cons_val_zero, add_neg_cancel_right, add_neg_cancel]

/-- Tr(γ¹) = 0: Off-diagonal structure gives zero trace.

**Proof**: γ¹ has zeros on the diagonal (it's purely off-diagonal). -/
lemma gamma1_trace_zero : Matrix.trace gamma1 = 0 := by
  unfold gamma1 Matrix.trace Matrix.diag
  simp only [Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    add_zero, Fin.isValue, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.cons_val_zero]

/-- Tr(γ²) = 0: Despite imaginary entries, the diagonal is zero. -/
lemma gamma2_trace_zero : Matrix.trace gamma2 = 0 := by
  unfold gamma2 Matrix.trace Matrix.diag
  simp only [Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    add_zero, Fin.isValue, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.cons_val_zero]

/-- Tr(γ³) = 0: Same off-diagonal structure as γ¹. -/
lemma gamma3_trace_zero : Matrix.trace gamma3 = 0 := by
  unfold gamma3 Matrix.trace Matrix.diag
  simp only [Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    add_zero, Fin.isValue, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.cons_val_zero]

/-- Tr(γ^μ) = 0 for all μ ∈ {0,1,2,3}.

Unified statement of the single-gamma trace identity. -/
lemma gamma_trace_zero (μ : Fin 4) : Matrix.trace (gammaAt μ) = 0 := by
  fin_cases μ <;> simp only [gammaAt]
  · exact gamma0_trace_zero
  · exact gamma1_trace_zero
  · exact gamma2_trace_zero
  · exact gamma3_trace_zero


/-! ## Gamma Squares

These are derived from the Clifford relations {γ^μ, γ^ν} = 2η^μν I.
The diagonal case μ = ν gives 2(γ^μ)² = 2η^μμ I, so (γ^μ)² = η^μμ I. -/

/-- (γ⁰)² = I: The timelike gamma matrix squares to the identity.

Derived from clifford_00: γ⁰γ⁰ + γ⁰γ⁰ = 2I. -/
lemma gamma0_sq_eq_one : gamma0 * gamma0 = 1 := by
  have h := clifford_00
  have h2 : (2 : ℂ) • (gamma0 * gamma0) = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    calc (2 : ℂ) • (gamma0 * gamma0)
        = gamma0 * gamma0 + gamma0 * gamma0 := by rw [two_smul]
      _ = 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) := h
      _ = (2 : ℂ) • 1 := by exact Eq.symm (ofNat_smul_eq_nsmul ℂ 2 1)
  exact smul_right_injective (Matrix (Fin 4) (Fin 4) ℂ) (two_ne_zero) h2

/-- (γ¹)² = -I: The first spacelike gamma matrix squares to minus identity.

Derived from clifford_11: γ¹γ¹ + γ¹γ¹ = -2I. -/
lemma gamma1_sq_eq_neg_one : gamma1 * gamma1 = -1 := by
  have h := clifford_11
  have h2 : (2 : ℂ) • (gamma1 * gamma1) = (2 : ℂ) • (-(1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
    calc (2 : ℂ) • (gamma1 * gamma1)
        = gamma1 * gamma1 + gamma1 * gamma1 := by rw [two_smul]
      _ = (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := h
      _ = (2 : ℂ) • (-(1 : Matrix (Fin 4) (Fin 4) ℂ)) := by rw [← gamma0_sq_eq_one]; simp only [neg_smul,
        smul_neg]
  have h3 := smul_right_injective (Matrix (Fin 4) (Fin 4) ℂ) (two_ne_zero) h2
  simp only at h3 ⊢
  exact h3

/-- (γ²)² = -I: The second spacelike gamma matrix squares to minus identity. -/
lemma gamma2_sq_eq_neg_one : gamma2 * gamma2 = -1 := by
  have h := clifford_22
  have h2 : (2 : ℂ) • (gamma2 * gamma2) = (2 : ℂ) • (-(1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
    calc (2 : ℂ) • (gamma2 * gamma2)
        = gamma2 * gamma2 + gamma2 * gamma2 := by rw [two_smul]
      _ = (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := h
      _ = (2 : ℂ) • (-(1 : Matrix (Fin 4) (Fin 4) ℂ)) := by rw [← gamma0_sq_eq_one]; simp only [neg_smul,
        smul_neg]
  have h3 := smul_right_injective (Matrix (Fin 4) (Fin 4) ℂ) (two_ne_zero) h2
  simp only at h3 ⊢
  exact h3

/-- (γ³)² = -I: The third spacelike gamma matrix squares to minus identity. -/
lemma gamma3_sq_eq_neg_one : gamma3 * gamma3 = -1 := by
  have h := clifford_33
  have h2 : (2 : ℂ) • (gamma3 * gamma3) = (2 : ℂ) • (-(1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
    calc (2 : ℂ) • (gamma3 * gamma3)
        = gamma3 * gamma3 + gamma3 * gamma3 := by rw [two_smul]
      _ = (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := h
      _ = (2 : ℂ) • (-(1 : Matrix (Fin 4) (Fin 4) ℂ)) := by rw [← gamma0_sq_eq_one]; simp only [neg_smul,
        smul_neg]
  have h3 := smul_right_injective (Matrix (Fin 4) (Fin 4) ℂ) (two_ne_zero) h2
  simp only at h3 ⊢
  exact h3


/-! ## Trace Helper Lemmas -/

/-- Tr(I₄) = 4: The trace of the 4×4 identity matrix. -/
lemma trace_one_fin4 : Matrix.trace (1 : Matrix (Fin 4) (Fin 4) ℂ) = 4 := by
  unfold Matrix.trace Matrix.diag
  simp only [Fin.sum_univ_four, Matrix.one_apply_eq]
  norm_num

/-- Tr(-I₄) = -4: The trace of minus the identity. -/
lemma trace_neg_one_fin4 : Matrix.trace (-(1 : Matrix (Fin 4) (Fin 4) ℂ)) = -4 := by
  rw [Matrix.trace_neg, trace_one_fin4]

/-- Tr(AB) = Tr(BA): Cyclic property of trace. -/
lemma trace_mul_comm (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.trace (A * B) = Matrix.trace (B * A) := by
  unfold Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  ring

/-- For anticommuting matrices, the trace of the product vanishes.

If AB + BA = 0, then Tr(AB) = Tr(BA) = -Tr(AB), so Tr(AB) = 0. -/
lemma trace_zero_of_anticommute (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (h : A * B + B * A = 0) : Matrix.trace (A * B) = 0 := by
  have hab : A * B = -(B * A) := by
    have h' := congrArg (· - B * A) h
    simp only [add_sub_cancel_right, zero_sub] at h'
    exact h'
  have h_neg_self : Matrix.trace (A * B) = -Matrix.trace (A * B) := by
    calc Matrix.trace (A * B)
        = Matrix.trace (-(B * A)) := by rw [hab]
      _ = -Matrix.trace (B * A) := Matrix.trace_neg (B * A)
      _ = -Matrix.trace (A * B) := by rw [trace_mul_comm B A]
  have h_double : Matrix.trace (A * B) + Matrix.trace (A * B) = 0 := by
    rw [h_neg_self]
    exact neg_add_eq_zero.mpr h_neg_self
  have h_two : (2 : ℂ) * Matrix.trace (A * B) = 0 := by
    rw [two_mul]
    exact h_double
  exact (mul_eq_zero.mp h_two).resolve_left two_ne_zero


/-! ## Two-Gamma Trace: Tr(γ^μ γ^ν) = 4η^μν

This is the workhorse identity for computing Feynman diagrams in QED/QCD.
The proof splits into 16 cases:
- 4 diagonal cases (μ = ν): Use gamma squares and trace of ±I
- 12 off-diagonal cases (μ ≠ ν): Use anticommutation ⟹ trace = 0 -/

/-- Tr(γ^μ γ^ν) = 4η^μν: The fundamental two-gamma trace identity. -/
lemma gamma_trace_two (μ ν : Fin 4) :
    Matrix.trace (gammaAt μ * gammaAt ν) = 4 * minkowskiMetric μ ν := by
  fin_cases μ <;> fin_cases ν <;> simp only [gammaAt, minkowskiMetric]

  -- Case (0, 0): Tr(γ⁰ γ⁰) = Tr(I) = 4 = 4 · η⁰⁰
  · simp only [Fin.isValue, ↓reduceIte]
    rw [gamma0_sq_eq_one, trace_one_fin4]
    norm_num

  -- Case (0, 1): Tr(γ⁰ γ¹) = 0 = 4 · η⁰¹
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, zero_ne_one, ↓reduceIte, mul_zero]
    exact trace_zero_of_anticommute gamma0 gamma1 clifford_01

  -- Case (0, 2): Tr(γ⁰ γ²) = 0 = 4 · η⁰²
  · simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, mul_zero]
    exact trace_zero_of_anticommute gamma0 gamma2 clifford_02

  -- Case (0, 3): Tr(γ⁰ γ³) = 0 = 4 · η⁰³
  · simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, mul_zero]
    exact trace_zero_of_anticommute gamma0 gamma3 clifford_03

  -- Case (1, 0): Tr(γ¹ γ⁰) = 0 = 4 · η¹⁰
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, one_ne_zero, ↓reduceIte, mul_zero]
    exact trace_zero_of_anticommute gamma1 gamma0 clifford_10

  -- Case (1, 1): Tr(γ¹ γ¹) = Tr(-I) = -4 = 4 · η¹¹
  · simp only [Fin.isValue, ↓reduceIte]
    rw [gamma1_sq_eq_neg_one, trace_neg_one_fin4]
    norm_num

  -- Case (1, 2): Tr(γ¹ γ²) = 0 = 4 · η¹²
  · simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, mul_zero]
    exact trace_zero_of_anticommute gamma1 gamma2 clifford_12

  -- Case (1, 3): Tr(γ¹ γ³) = 0 = 4 · η¹³
  · simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, mul_zero]
    exact trace_zero_of_anticommute gamma1 gamma3 clifford_13

  -- Case (2, 0): Tr(γ² γ⁰) = 0 = 4 · η²⁰
  · simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_zero]
    exact trace_zero_of_anticommute gamma2 gamma0 clifford_20

  -- Case (2, 1): Tr(γ² γ¹) = 0 = 4 · η²¹
  · simp only [Fin.reduceFinMk, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_zero]
    exact trace_zero_of_anticommute gamma2 gamma1 clifford_21

  -- Case (2, 2): Tr(γ² γ²) = Tr(-I) = -4 = 4 · η²²
  · simp only [Fin.isValue, ↓reduceIte]
    rw [gamma2_sq_eq_neg_one, trace_neg_one_fin4]
    norm_num

  -- Case (2, 3): Tr(γ² γ³) = 0 = 4 · η²³
  · simp only [Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, mul_zero]
    exact trace_zero_of_anticommute gamma2 gamma3 clifford_23

  -- Case (3, 0): Tr(γ³ γ⁰) = 0 = 4 · η³⁰
  · simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_zero]
    exact trace_zero_of_anticommute gamma3 gamma0 clifford_30

  -- Case (3, 1): Tr(γ³ γ¹) = 0 = 4 · η³¹
  · simp only [Fin.reduceFinMk, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_zero]
    exact trace_zero_of_anticommute gamma3 gamma1 clifford_31

  -- Case (3, 2): Tr(γ³ γ²) = 0 = 4 · η³²
  · simp only [Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, mul_zero]
    exact trace_zero_of_anticommute gamma3 gamma2 clifford_32

  -- Case (3, 3): Tr(γ³ γ³) = Tr(-I) = -4 = 4 · η³³
  · simp only [Fin.isValue, ↓reduceIte]
    rw [gamma3_sq_eq_neg_one, trace_neg_one_fin4]
    norm_num

/-- (γ⁵)² = I: The chirality matrix is an involution.

**Physical meaning**: The eigenvalues of γ⁵ are ±1, corresponding to
right-handed (+1) and left-handed (-1) chirality states.

**Consequence**: P_L = (1-γ⁵)/2 and P_R = (1+γ⁵)/2 are projectors:
P_L² = P_L, P_R² = P_R, P_L P_R = 0, P_L + P_R = 1. -/
lemma gamma5_sq : gamma5 * gamma5 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma5, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply,
             Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one,
             Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add, ↓reduceIte, Fin.isValue, Fin.reduceEq, ↓reduceIte]

/-- γ⁵ is Hermitian: (γ⁵)† = γ⁵.

**Physical meaning**: Chirality is an observable (self-adjoint operator).
You can measure whether a fermion is left-handed or right-handed.

**Note**: Chirality ≠ helicity for massive particles. Helicity (spin along
momentum) is frame-dependent; chirality (γ⁵ eigenvalue) is Lorentz-invariant.
For massless particles, they coincide. -/
lemma gamma5_hermitian : gamma5.conjTranspose = gamma5 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma5, Matrix.conjTranspose, Matrix.of_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_one]
set_option maxHeartbeats 100000
/-- γ⁵ anticommutes with γ⁰: {γ⁵, γ⁰} = γ⁵γ⁰ + γ⁰γ⁵ = 0.

**Physical meaning**: Under parity (space inversion), γ⁰ is invariant
but γ⁵ → -γ⁵. This means left-handed ↔ right-handed under parity.
The weak force violates parity maximally because it couples only to
left-handed particles. -/
lemma gamma5_anticommutes_0 : gamma5 * gamma0 = -gamma0 * gamma5 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma5, gamma0, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one,
             Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, mul_neg, add_zero, zero_add, neg_zero, neg_neg]

/-- γ⁵ anticommutes with γ¹. -/
lemma gamma5_anticommutes_1 : gamma5 * gamma1 = -gamma1 * gamma5 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma5, gamma1, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one,
             Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, mul_neg, add_zero, zero_add, neg_zero, neg_neg]

/-- γ⁵ anticommutes with γ². -/
lemma gamma5_anticommutes_2 : gamma5 * gamma2 = -gamma2 * gamma5 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma5, gamma2, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one,
             Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, mul_neg, add_zero, zero_add, neg_zero, neg_neg, zero_mul]
  all_goals try ring

/-- γ⁵ anticommutes with γ³. -/
lemma gamma5_anticommutes_3 : gamma5 * gamma3 = -gamma3 * gamma5 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma5, gamma3, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one,
             Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, mul_neg, add_zero, zero_add, neg_zero, neg_neg]

/-- γ⁵ anticommutes with all γ^μ: {γ⁵, γ^μ} = 0.

**Unified statement**: For any spacetime index μ, γ⁵γ^μ = -γ^μγ⁵.

**Consequence**: γ⁵ commutes with Lorentz generators S^μν = (i/4)[γ^μ, γ^ν],
so chirality is Lorentz-invariant. -/
lemma gamma5_anticommutes (μ : Fin 4) :
    gamma5 * gammaAt μ = -gammaAt μ * gamma5 := by
  fin_cases μ <;> simp only [gammaAt]
  · exact gamma5_anticommutes_0
  · exact gamma5_anticommutes_1
  · exact gamma5_anticommutes_2
  · exact gamma5_anticommutes_3

/-- Tr(γ⁵) = 0: The chirality matrix is traceless.

**Proof**: Direct computation, or note that γ⁵ is off-diagonal in the
standard representation. -/
lemma gamma5_trace_zero : Matrix.trace gamma5 = 0 := by
  unfold gamma5 Matrix.trace Matrix.diag
  simp only [Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    add_zero, Fin.isValue, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.cons_val_zero]

/-! ## Three-Gamma Trace: Tr(γ^μ γ^ν γ^ρ) = 0

The trace of an odd number of gamma matrices vanishes. The proof uses γ⁵:
1. Insert γ⁵γ⁵ = I
2. Move γ⁵ through the three gammas, picking up (-1)³ = -1
3. Use cyclicity of trace to get Tr(X) = -Tr(X), hence Tr(X) = 0 -/

/-- Moving γ⁵ through three gamma matrices picks up a factor of (-1)³ = -1.

  γ⁵ · γ^μ · γ^ν · γ^ρ = -γ^μ · γ^ν · γ^ρ · γ⁵

Each anticommutation γ⁵ γ^α = -γ^α γ⁵ contributes a factor of -1. -/
lemma gamma5_move_through_three (μ ν ρ : Fin 4) :
    gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ =
    -(gammaAt μ * gammaAt ν * gammaAt ρ * gamma5) := by
  have step1 : gamma5 * gammaAt μ = -(gammaAt μ * gamma5) := by
    rw [gamma5_anticommutes μ]
    exact Matrix.neg_mul (gammaAt μ) gamma5
  have step2 : gamma5 * gammaAt ν = -(gammaAt ν * gamma5) := by
    rw [gamma5_anticommutes ν]
    exact Matrix.neg_mul (gammaAt ν) gamma5
  have step3 : gamma5 * gammaAt ρ = -(gammaAt ρ * gamma5) := by
    rw [gamma5_anticommutes ρ]
    exact Matrix.neg_mul (gammaAt ρ) gamma5
  calc gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ
      = (gamma5 * gammaAt μ) * gammaAt ν * gammaAt ρ := by noncomm_ring
    _ = (-(gammaAt μ * gamma5)) * gammaAt ν * gammaAt ρ := by rw [step1]
    _ = -(gammaAt μ * gamma5 * gammaAt ν * gammaAt ρ) := by noncomm_ring
    _ = -(gammaAt μ * (gamma5 * gammaAt ν) * gammaAt ρ) := by noncomm_ring
    _ = -(gammaAt μ * (-(gammaAt ν * gamma5)) * gammaAt ρ) := by rw [step2]
    _ = gammaAt μ * gammaAt ν * gamma5 * gammaAt ρ := by noncomm_ring
    _ = gammaAt μ * gammaAt ν * (gamma5 * gammaAt ρ) := by noncomm_ring
    _ = gammaAt μ * gammaAt ν * (-(gammaAt ρ * gamma5)) := by rw [step3]
    _ = -(gammaAt μ * gammaAt ν * gammaAt ρ * gamma5) := by noncomm_ring

/-- Tr(γ^μ γ^ν γ^ρ) = 0: The trace of an odd number of gamma matrices vanishes.

**Proof sketch**:
1. T = Tr(γ⁵γ⁵ · X) since γ⁵² = I
2. T = Tr(γ⁵ · X · γ⁵) by cyclicity
3. T = Tr(-X) by moving γ⁵ through X
4. T = -T, so T = 0 -/
lemma gamma_trace_three (μ ν ρ : Fin 4) :
    Matrix.trace (gammaAt μ * gammaAt ν * gammaAt ρ) = 0 := by
  set T := Matrix.trace (gammaAt μ * gammaAt ν * gammaAt ρ) with hT_def

  have h_insert : gammaAt μ * gammaAt ν * gammaAt ρ =
                  gamma5 * gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ := by
    rw [gamma5_sq]
    noncomm_ring

  have h_cyclic : Matrix.trace (gamma5 * gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ) =
                  Matrix.trace (gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ * gamma5) := by
    have h_assoc : gamma5 * gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ =
                   gamma5 * (gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ) := by noncomm_ring
    rw [h_assoc, trace_mul_comm]

  have h_anticomm : gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ * gamma5 =
                    -(gammaAt μ * gammaAt ν * gammaAt ρ) := by
    rw [gamma5_move_through_three]
    have h_assoc : -(gammaAt μ * gammaAt ν * gammaAt ρ * gamma5) * gamma5 =
                   -(gammaAt μ * gammaAt ν * gammaAt ρ * (gamma5 * gamma5)) := by noncomm_ring
    rw [h_assoc, gamma5_sq]
    noncomm_ring

  have h_neg_self : T = -T := by
    calc T
        = Matrix.trace (gammaAt μ * gammaAt ν * gammaAt ρ) := rfl
      _ = Matrix.trace (gamma5 * gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ) := by rw [h_insert]
      _ = Matrix.trace (gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ * gamma5) := h_cyclic
      _ = Matrix.trace (-(gammaAt μ * gammaAt ν * gammaAt ρ)) := by rw [h_anticomm]
      _ = -Matrix.trace (gammaAt μ * gammaAt ν * gammaAt ρ) := Matrix.trace_neg _
      _ = -T := rfl

  have h_double : T + T = 0 := by
    rw [h_neg_self]
    exact neg_add_eq_zero.mpr h_neg_self
  have h_two : (2 : ℂ) * T = 0 := by
    rw [two_mul]
    exact h_double
  exact (mul_eq_zero.mp h_two).resolve_left two_ne_zero


/-! ## Additional Gamma5 Trace Identities -/

/-- The anticommutator {γ⁵, γ^μ} vanishes: γ⁵ γ^μ + γ^μ γ⁵ = 0 -/
lemma gamma5_gammaAt_anticommute (μ : Fin 4) :
    gamma5 * gammaAt μ + gammaAt μ * gamma5 = 0 := by
  rw [gamma5_anticommutes μ, neg_mul]
  exact neg_add_cancel (gammaAt μ * gamma5)

/-- Tr(γ⁵ γ^μ) = 0: Mixed trace with single gamma vanishes. -/
lemma gamma5_gamma_trace_zero (μ : Fin 4) :
    Matrix.trace (gamma5 * gammaAt μ) = 0 := by
  exact trace_zero_of_anticommute gamma5 (gammaAt μ) (gamma5_gammaAt_anticommute μ)


set_option maxHeartbeats 400000

/-- Alternative definition: γ⁵ = iγ⁰γ¹γ²γ³

This is the standard definition in terms of the four gamma matrices.
The factor of i ensures (γ⁵)² = +I rather than -I. -/
lemma gamma5_eq_product : gamma5 = I • (gamma0 * gamma1 * gamma2 * gamma3) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma5, gamma0, gamma1, gamma2, gamma3,
             Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one,
             Fin.isValue, Fin.mk_one, Fin.reduceFinMk, smul_eq_mul]
  all_goals try simp only [mul_zero, mul_one, zero_mul, one_mul,
                           add_zero, zero_add, mul_neg, neg_mul,
                           neg_neg, neg_zero, mul_comm I]
  all_goals try ring_nf
  all_goals try simp only [neg_neg, I_sq, neg_neg]

end Dirac.Matrices
