/-
Author: Adam Bornemann

================================================================================
QUANTUM MECHANICS FOUNDATIONS FOR ROBERTSON'S UNCERTAINTY RELATION
================================================================================

This file establishes the mathematical foundations needed to prove Robertson's
generalized uncertainty relation:

  σ_A σ_B ≥ (1/2)|⟨[Â,B̂]⟩|

where:
  - σ_A, σ_B are standard deviations (uncertainties) of observables A, B
  - [Â,B̂] is the commutator of operators Â and B̂
  - ⟨·⟩ denotes expectation value in a quantum state

The proof follows from the Cauchy-Schwarz inequality applied to the inner
product structure of quantum states, showing that non-commuting observables
have a fundamental lower bound on their joint uncertainties.

Organization:
  1. Imports and namespace setup
  2. Core quantum structures (Hilbert spaces, states, observables)
  3. Type-safe statistical quantities (expectation, variance, std dev)
  4. Quantum systems (molecules, quantum numbers, spin)
  5. Physical constants
  6. Algebraic operations (commutators, anticommutators)
  7. Finite-dimensional matrix formulation
  8. Standard quantum states and operators
  9. Tensor products and entanglement
  10. Measurement and Born rule
  11. Unitary evolution
  12. Canonical commutation relations
  13. Fundamental Axiom
  14. Basic theorems
  15. Key helper lemmas

References:
  - Robertson, H.P. (1929). "The Uncertainty Principle". Phys. Rev. 34, 163
  - Sakurai & Napolitano, "Modern Quantum Mechanics" Ch. 1
  - Nielsen & Chuang, "Quantum Computation and Quantum Information" Ch. 2
-/

/-============================================================================
  SECTION 1: IMPORTS AND NAMESPACE SETUP
============================================================================-/

/- Core mathematical structures -/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fin.Basic

/- Hilbert space machinery -/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/- Calculus for position/momentum operators -/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/- Measure theory for L² spaces -/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Measure.MeasureSpace

/- Linear algebra -/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/- Operator theory -/
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/- Other -/
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace Robertson.Core

open InnerProductSpace MeasureTheory Complex
open scoped BigOperators

/-============================================================================
  SECTION 2: CORE QUANTUM STRUCTURES
============================================================================-/

/-
In quantum mechanics, physical systems are described by:
  1. States: Unit vectors in a Hilbert space H
  2. Observables: Self-adjoint operators on H
  3. Evolution: Unitary operators on H

We provide both infinite-dimensional (general Hilbert space) and
finite-dimensional (matrix) formulations.
-/

/--
A normalized quantum state in a Hilbert space.

Mathematical structure: A unit vector |ψ⟩ in a complex Hilbert space H.
The normalization ‖ψ‖ = 1 ensures Born rule probabilities sum to 1.

Type safety: By encoding normalization in the type, we ensure all quantum
states are properly normalized at compile time, preventing a common source
of errors in quantum calculations.
-/
structure NormalizedState (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  vec : H
  normalized : ‖vec‖ = 1

/--
An observable in infinite-dimensional Hilbert space (bounded case).

Mathematical requirements:
  - Self-adjoint: A† = A (ensures real eigenvalues)
  - Bounded: ‖A‖ < ∞ (ensures A is defined everywhere)

Examples: Spin operators, bounded potentials, projection operators
-/
structure Observable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  op : H →L[ℂ] H
  SymmetricOperator : IsSelfAdjoint op

/--
An unbounded observable (for position, momentum operators).

Many fundamental observables are unbounded:
  - Position: X̂ψ(x) = xψ(x)
  - Momentum: P̂ψ(x) = -iℏ(d/dx)ψ(x)
  - Hamiltonian: Ĥ = P̂²/(2m) + V(X̂)

Mathematical subtlety: For unbounded operators, symmetric ≠ self-adjoint.
Self-adjointness requires careful domain specification... which I'm skipping.

Why?  Because Robertson can be proven with symmetry.  Let me show you how it's done.
-/
structure UnboundedObservable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  op : H →ₗ[ℂ] H  -- Linear but not necessarily bounded
  domain : Submodule ℂ H  -- Dense domain where operator is defined
  dense : Dense (domain : Set H)
  SymmetricOperator : ∀ (ψ φ : H), ψ ∈ domain → φ ∈ domain →
    ⟪op ψ, φ⟫_ℂ = ⟪ψ, op φ⟫_ℂ

/-============================================================================
  SECTION 3: TYPE-SAFE STATISTICAL QUANTITIES
============================================================================-/

/-
Rather than using raw real numbers for statistical quantities, we define
type-safe wrappers that encode invariants (like non-negativity) directly
in the type system. This prevents errors and makes the code more self-documenting.
-/

/--
Expectation value of an observable.

Mathematical definition: ⟨A⟩ = ⟨ψ|A|ψ⟩

Physical meaning: Average measurement outcome over many identical preparations.
Note: Can be any real number (positive, negative, or zero).
-/
structure ExpectationValue where
  val : ℝ

/--
Variance of an observable, with built-in non-negativity.

Mathematical definition: Var(A) = ⟨A²⟩ - ⟨A⟩²

The non-negativity proof is required at construction time, ensuring
type safety. This comes from Var(A) = ‖(A - ⟨A⟩I)ψ‖² ≥ 0.
-/
structure Variance where
  val : ℝ
  nonneg : 0 ≤ val

/--
Standard deviation (uncertainty) with built-in non-negativity.

Mathematical definition: σ_A = √Var(A)

This is the key quantity in Robertson's relation. The type ensures
we can only construct valid (non-negative) standard deviations.
-/
structure StandardDeviation where
  val : ℝ
  nonneg : 0 ≤ val

/--
Expectation value of a commutator (always purely imaginary for self-adjoint operators).

For self-adjoint A, B: ⟨[A,B]⟩ is purely imaginary.
This structure could enforce val.re = 0 for additional type safety.
-/
structure CommutatorExpectation where
  val : ℂ

/-============================================================================
  SECTION 4: QUANTUM SYSTEMS AND PARTICLES
============================================================================-/

/-
Structures for describing quantum mechanical systems, from single electrons
to multi-electron molecules. These are used in quantum chemistry applications.
-/

/-- Spin quantum number (spin-1/2 particles) -/
inductive Spin
  | up : Spin
  | down : Spin
  deriving Repr, BEq

/--
Complete set of quantum numbers for an electron in an atom.

These arise from solving the hydrogen atom Schrödinger equation:
  - n: Principal quantum number (energy level)
  - l: Azimuthal/orbital angular momentum quantum number
  - m: Magnetic quantum number (z-component of angular momentum)
  - s: Spin quantum number

Constraints enforced by type:
  - l < n (orbital angular momentum bounded by energy level)
  - |m| ≤ l (magnetic quantum number bounded by total angular momentum)
-/
structure QuantumNumbers where
  n : ℕ  -- Principal (n ≥ 1)
  l : ℕ  -- Azimuthal (0 ≤ l < n)
  m : ℤ  -- Magnetic (-l ≤ m ≤ l)
  s : Spin
  h_valid : l < n ∧ |m| ≤ l

/--
Molecular system structure for quantum chemistry.

Represents a molecule with:
  - Multiple electrons (subject to Pauli exclusion)
  - Multiple nuclei (Born-Oppenheimer approximation)
  - Nuclear charges and masses for Coulomb interactions
-/
structure Molecule where
  n_electrons : ℕ
  n_nuclei : ℕ
  nuclear_charges : Fin n_nuclei → ℝ
  nuclear_masses : Fin n_nuclei → ℝ

/-- Type alias for 3D space -/
abbrev ℝ3 := Fin 3 → ℝ

/-- Nuclear configuration in 3D space -/
def NuclearConfiguration (mol : Molecule) := Fin mol.n_nuclei → ℝ3

/-- Multi-electron wavefunction type -/
def Wavefunction (n : ℕ) := (Fin n → ℝ3) → (Fin n → Spin) → ℂ

/-- Electronic state (alias for clarity) -/
def ElectronicState (n : ℕ) := Wavefunction n

/-============================================================================
  SECTION 5: PHYSICAL CONSTANTS
============================================================================-/

/-
Physical constants in SI units.
Note: Often we work in natural units where ℏ = 1 for simplicity.
-/

/-- Reduced Planck constant ℏ = h/(2π) in J·s -/
def ℏ : ℝ := 1.054571817e-34

/-- Electron mass in kg -/
def m_electron : ℝ := 9.1093837015e-31

/-- Proton mass in kg -/
def m_proton : ℝ := 1.67262192369e-27

/-- Boltzmann constant in J/K -/
def k_B : ℝ := 1.380649e-23

/-============================================================================
  SECTION 6: STATISTICAL FUNCTIONS
============================================================================-/

/-
Functions for computing statistical quantities from quantum states.
These are central to the uncertainty principle.
-/

/--
Expectation value of a bounded observable in a normalized state.

Mathematical definition: ⟨A⟩_ψ = ⟨ψ, Aψ⟩

Note: We take the real part since observables have real expectation values.
-/
def expectationValue {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : Observable H) (ψ : H) (_ /- h_norm -/ : ‖ψ‖ = 1) : ℝ :=
  (⟪ψ, A.op ψ⟫_ℂ).re

/--
Variance of an observable in a state.

Mathematical definition: Var(A) = ⟨A²⟩ - ⟨A⟩²

Physical meaning: Spread of measurement outcomes around the mean.
-/
def variance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : Observable H) (ψ : H) (h_norm : ‖ψ‖ = 1) : ℝ :=
  let μ := expectationValue A ψ h_norm
  (⟪ψ, A.op (A.op ψ)⟫_ℂ).re - μ^2

/--
Standard deviation (uncertainty) of an observable.

Mathematical definition: σ_A = √Var(A)

This is the key quantity in Robertson's uncertainty relation.
-/
noncomputable def uncertainty {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : Observable H) (ψ : H) (h_norm : ‖ψ‖ = 1) : ℝ :=
  Real.sqrt (variance A ψ h_norm)

/-- Alternative name for pedagogical clarity -/
noncomputable def standardDeviation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : Observable H) (ψ : H) (h_norm : ‖ψ‖ = 1) : ℝ :=
  uncertainty A ψ h_norm

/-- Expectation value for unbounded observables -/
noncomputable def unboundedExpectationValue {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) (_ /- h_norm -/ : ‖ψ‖ = 1)
    (_ /- h_dom -/ : ψ ∈ A.domain) : ℝ :=
  (⟪ψ, A.op ψ⟫_ℂ).re

/-- Variance of an unbounded observable -/
noncomputable def unboundedVariance {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) (h_norm : ‖ψ‖ = 1)
    (hψ : ψ ∈ A.domain) : ℝ :=
  let A_exp := unboundedExpectationValue A ψ h_norm hψ
  let A' := A.op - A_exp • (1 : H →ₗ[ℂ] H)
  ‖A' ψ‖^2

/-- Standard deviation for unbounded observables -/
noncomputable def unboundedStandardDeviation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) (h_norm : ‖ψ‖ = 1)
    (hψ : ψ ∈ A.domain) : ℝ :=
  Real.sqrt (unboundedVariance A ψ h_norm hψ)

/-============================================================================
  SECTION 7: ALGEBRAIC OPERATIONS
============================================================================-/

/-
The commutator is central to quantum mechanics, appearing in:
  - Uncertainty relations: σ_A σ_B ≥ |⟨[A,B]⟩|/2
  - Time evolution: dA/dt = (i/ℏ)[H,A]
  - Canonical relations: [x̂,p̂] = iℏ
-/

/--
Commutator of two bounded operators.

Mathematical definition: [A,B] = AB - BA

Physical meaning: Measures incompatibility of observables.
Non-zero commutator ⟹ observables cannot be simultaneously measured precisely.
-/
def commutator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →L[ℂ] H) : H →L[ℂ] H :=
  A ∘L B - B ∘L A

/--
Anticommutator {A,B} = AB + BA.

Less common in basic QM but important for:
  - Fermionic operators in QFT
  - Jordan algebras
  - Decomposing inner products
-/
def anticommutator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →L[ℂ] H) : H →L[ℂ] H :=
  A ∘L B + B ∘L A

/-============================================================================
  SECTION 8: FINITE-DIMENSIONAL MATRIX FORMULATION
============================================================================-/

/-
For concrete calculations and quantum computing applications, we use
finite-dimensional matrix representations.
-/

/--
A quantum state in n-dimensional Hilbert space.

Represents a pure state as a normalized vector in ℂⁿ.
Used for qubits (n=2), qutrits (n=3), and finite-level systems.
-/
structure QuantumState (n : ℕ) where
  ψ : Fin n → ℂ
  normalized : ∑ i, Complex.normSq (ψ i) = 1

/-- An observable as a Hermitian matrix -/
structure MatrixObservable (n : ℕ) where
  M : Matrix (Fin n) (Fin n) ℂ
  hermitian : M.IsHermitian

/-- Matrix commutator -/
noncomputable def matrix_commutator {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A * B - B * A

notation "[" A "," B "]" => matrix_commutator A B

/-- Apply an observable to a quantum state -/
noncomputable def apply {n : ℕ} (O : MatrixObservable n) (ψ : QuantumState n) : Fin n → ℂ :=
  fun i => ∑ j, O.M i j * ψ.ψ j

/-- Inner product of quantum states -/
noncomputable def innerProduct {n : ℕ} (φ ψ : QuantumState n) : ℂ :=
  ∑ i, (star (φ.ψ i)) * (ψ.ψ i)

notation "⟨" φ "|" ψ "⟩" => innerProduct φ ψ

/-- Expectation value in matrix formulation -/
noncomputable def expectation {n : ℕ} (ψ : QuantumState n) (O : MatrixObservable n) : ℂ :=
  ∑ i, (star (ψ.ψ i)) * ((apply O ψ) i)

/-- General expectation value for any matrix -/
noncomputable def expectation_matrix {n : ℕ} (ψ : QuantumState n)
    (M : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ i, ∑ j, star (ψ.ψ i) * M i j * (ψ.ψ j)

/-============================================================================
  SECTION 9: STANDARD QUANTUM STATES AND OPERATORS
============================================================================-/

/-- A qubit (2-dimensional quantum state) -/
abbrev Qubit := QuantumState 2

/-- Computational basis state |0⟩ -/
def ket0 : Qubit where
  ψ := ![1, 0]
  normalized := by simp [Complex.normSq]

/-- Computational basis state |1⟩ -/
def ket1 : Qubit where
  ψ := ![0, 1]
  normalized := by simp [Complex.normSq]

/-- Hadamard basis state |+⟩ = (|0⟩ + |1⟩)/√2 -/
noncomputable def ketPlus : Qubit where
  ψ := fun i => Complex.mk (1 / Real.sqrt 2) 0
  normalized := by
  {simp_all!; ring_nf!; simp}


/-- Hadamard basis state |−⟩ = (|0⟩ - |1⟩)/√2 -/
noncomputable def ketMinus : Qubit where
  ψ := fun i => if i = 0 then Complex.mk (1 / Real.sqrt 2) 0
                else Complex.mk (-1 / Real.sqrt 2) 0
  normalized := by
    simp only [Fin.sum_univ_two, Fin.isValue]
    simp only [↓reduceIte, Complex.normSq_mk]
    -- (1/√2)² + (-1/√2)² = 1/2 + 1/2 = 1
    have h : (-1 / Real.sqrt 2) ^ 2 = (1 / Real.sqrt 2) ^ 2 := by ring
    rw [← normSq_mk]
    have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    rw [← hsqrt]
    ring_nf
    simp_all only [one_div, inv_pow, Nat.ofNat_nonneg, Real.sq_sqrt, normSq_mk, mul_zero, add_zero, Fin.isValue,
    one_ne_zero, ↓reduceIte, mul_neg, neg_mul, neg_neg]
    rw [← two_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num

/-
PAULI MATRICES: Fundamental observables for spin-1/2 systems.
-/

/-- Pauli-X (bit flip): σₓ = |0⟩⟨1| + |1⟩⟨0| -/
def σₓ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli-Y: σᵧ = -i|0⟩⟨1| + i|1⟩⟨0| -/
def σᵧ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Pauli-Z (phase flip): σᵤ = |0⟩⟨0| - |1⟩⟨1| -/
def σᵤ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- 2×2 Identity matrix -/
def I₂ : Matrix (Fin 2) (Fin 2) ℂ := 1

/-============================================================================
  SECTION 10: TENSOR PRODUCTS AND ENTANGLEMENT
============================================================================-/

/--
Tensor product of quantum states.

For systems A and B: |ψ_AB⟩ = |ψ_A⟩ ⊗ |ψ_B⟩

noncomputable def tensorProduct {m n} (φ : QuantumState m) (ψ : QuantumState n) :
    QuantumState (m * n) where
  ψ := fun idx =>
    let i := idx / n
    let j := idx % n
    φ.ψ ⟨i, by sorry⟩ * ψ.ψ ⟨j, by sorry⟩
  normalized := by sorry

notation φ " ⊗ " ψ => tensorProduct φ ψ

/-- Test if a two-qubit state is entangled -/
def isEntangled (ψ : QuantumState 4) : Prop :=
  ¬∃ (φ₁ φ₂ : Qubit), ψ = φ₁ ⊗ φ₂
-/

noncomputable def bell_Φ_plus : QuantumState 4 where
  ψ := fun i => if i = 0 ∨ i = 3 then Complex.mk (1 / Real.sqrt 2) 0 else 0
  normalized := by
    simp only [Fin.sum_univ_four, Fin.isValue]
    -- Only i=0 and i=3 are nonzero
    norm_num
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, normSq_zero, add_zero, or_self]
    have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    rw [hsqrt]
    ring_nf

noncomputable def GHZ : QuantumState 8 where
  ψ := fun i => if i = 0 ∨ i = 7 then Complex.mk (1 / Real.sqrt 2) 0 else 0
  normalized := by
    simp only [Fin.sum_univ_eight, Fin.isValue]  -- May need Fin.sum_univ_succ iterations
    norm_num
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, normSq_zero, add_zero, or_self]
    have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    rw [hsqrt]
    ring

/-============================================================================
  SECTION 11: MEASUREMENT AND BORN RULE
============================================================================-/

/--
Born rule: probability of measuring |i⟩.

P(i) = |⟨i|ψ⟩|² = |ψᵢ|²
-/
noncomputable def prob_measure {n : ℕ} (ψ : QuantumState n) (i : Fin n) : ℝ :=
  Complex.normSq (ψ.ψ i)

/-- State collapse after measurement -/
noncomputable def collapse {n : ℕ} (ψ : QuantumState n) (i : Fin n)
    (_ : prob_measure ψ i ≠ 0) : QuantumState n where -- h
  ψ := fun j => if j = i then 1 else 0
  normalized := by simp

/-
============================================================================
  SECTION 12: UNITARY EVOLUTION
============================================================================
-/

/--
Unitary operators preserve norms and probabilities.

Time evolution: |ψ(t)⟩ = U(t)|ψ(0)⟩ where U(t) = exp(-iHt/ℏ)
-/
structure Unitary (n : ℕ) where
  U : Matrix (Fin n) (Fin n) ℂ
  unitary : U * star U = 1 ∧ star U * U = 1

/-
============================================================================
  SECTION 13: FUNDAMENTAL AXIOMS
============================================================================
-/

/--
The Gaussian integral - fundamental for quantum mechanics.

Used for normalizing Gaussian wave packets and computing
partition functions in quantum statistical mechanics.
-/
theorem integral_gaussian_unit : ∫ x : ℝ, Real.exp (-x^2) = Real.sqrt Real.pi := by
  simpa using integral_gaussian 1

/-
============================================================================
  SECTION 14: BASIC THEOREMS
============================================================================
-/

/-- Physical constants are positive -/
theorem ℏ_pos : 0 < ℏ := by norm_num [ℏ]
theorem k_B_pos : 0 < k_B := by norm_num [k_B]
theorem m_electron_pos : 0 < m_electron := by norm_num [m_electron]
theorem m_proton_pos : 0 < m_proton := by norm_num [m_proton]

/-- Pauli matrices are Hermitian -/
lemma pauli_x_hermitian : σₓ.IsHermitian := by
  simp [Matrix.IsHermitian, σₓ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma pauli_z_hermitian : σᵤ.IsHermitian := by
  simp [Matrix.IsHermitian, σᵤ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Pauli matrices square to identity -/
lemma pauli_x_squared : σₓ * σₓ = I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σₓ, I₂, Matrix.mul_apply]

/-- Basis states are orthonormal -/
theorem ket0_ket1_orthogonal : ⟨ket0|ket1⟩ = 0 := by
  simp [innerProduct, ket0, ket1]

/-- Variance for unbounded observables is non-negative -/
theorem unboundedVariance_nonneg {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) (h_norm : ‖ψ‖ = 1)
    (hψ : ψ ∈ A.domain) : 0 ≤ unboundedVariance A ψ h_norm hψ := by
  unfold unboundedVariance
  exact sq_nonneg _

/-- Standard deviation for unbounded observables is non-negative -/
theorem unboundedStandardDeviation_nonneg {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) (h_norm : ‖ψ‖ = 1)
    (hψ : ψ ∈ A.domain) : 0 ≤ unboundedStandardDeviation A ψ h_norm hψ := by
  unfold unboundedStandardDeviation
  exact Real.sqrt_nonneg _


/-
================================================================================
Section 15: KEY HELPER LEMMAS FOR ROBERTSON'S UNCERTAINTY RELATION
================================================================================

This file contains the mathematical machinery needed to prove Robertson's
generalized uncertainty principle. The key insight is decomposing the
complex inner product ⟨Aψ, Bψ⟩ into symmetric and antisymmetric parts:

  ⟨Aψ, Bψ⟩ = (1/2)⟨ψ, {A,B}ψ⟩ + (1/2)⟨ψ, [A,B]ψ⟩
           = Real part      + i(Imaginary part)

where {A,B} = AB + BA is the anticommutator and [A,B] = AB - BA is the commutator.

The lemmas establish:
  1. Algebraic properties of complex numbers and real functions
  2. Self-adjointness is preserved under affine transformations
  3. Commutators have purely imaginary expectation values
  4. Anticommutators have purely real expectation values

These combine with Cauchy-Schwarz to yield the uncertainty bound.

References:
  - Robertson, H.P. (1929). "The Uncertainty Principle". Phys. Rev. 34, 163
  - Griffiths, D.J. "Introduction to Quantum Mechanics" Section 3.5
  - Hall, B.C. "Quantum Theory for Mathematicians" Chapter 9
-/
namespace Robertson.Lemmas



/-============================================================================
  SECTION 1: ALGEBRAIC FOUNDATIONS
============================================================================-/

/-
These lemmas establish basic algebraic properties needed throughout the proof.
They may seem elementary, but having them explicitly proven ensures our
uncertainty derivation is completely rigorous.
-/

/--
A complex number is purely imaginary if and only if its real part is zero.

Mathematical significance: A complex number z is purely imaginary when z = -z*.
This characterization is crucial for understanding commutator expectation values,
which are always purely imaginary for self-adjoint operators.

Application in Robertson's proof: We use this to show that ⟨ψ, [A,B]ψ⟩ is
purely imaginary, which means |⟨ψ, [A,B]ψ⟩| = |Im⟨ψ, [A,B]ψ⟩|.
-/
lemma star_eq_neg_iff_re_eq_zero (z : ℂ) : star z = -z ↔ z.re = 0 := by
  -- Expand the complex conjugate: if z = a + bi, then z* = a - bi
  -- So z* = -z means (a - bi) = -(a + bi) = -a - bi
  -- This gives us a = -a, which implies a = 0
  simp [Complex.ext_iff]
  constructor
  · intro h
    -- From z.re = -z.re, we get 2·z.re = 0, thus z.re = 0
    linarith
  · intro h
    -- If z.re = 0, then clearly 0 = -0
    rw [h]
    simp

/--
Monotonicity of squaring for non-negative real numbers.

Mathematical note: This is only true for non-negative numbers!
For negative numbers, the inequality reverses: if x < y < 0, then x² > y².

Application in Robertson's proof: Used when establishing that
variance (which involves squares) preserves certain inequalities.
This is particularly important when applying Cauchy-Schwarz and
needing to take square roots while preserving the inequality direction.
-/
lemma pow_le_pow_of_le_left {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x^2 ≤ y^2 := by
  -- We prove x² ≤ y² by factoring through x² ≤ xy ≤ y²
  -- This leverages the fact that multiplication by non-negative numbers preserves inequalities
  calc
    x^2 = x * x       := by rw [pow_two]
    _   ≤ x * y       := by
                          -- Since 0 ≤ x and x ≤ y, we have x·x ≤ x·y
                          apply mul_le_mul_of_nonneg_left
                          · exact hxy  -- The inequality x ≤ y
                          · exact hx   -- The non-negativity x ≥ 0
    _   ≤ y * y       := by
                          -- Since x ≤ y and 0 ≤ y (by transitivity), we have x·y ≤ y·y
                          apply mul_le_mul_of_nonneg_right
                          · exact hxy  -- The inequality x ≤ y
                          · exact le_trans hx hxy  -- y ≥ x ≥ 0, so y ≥ 0
    _   = y^2         := by rw [pow_two]

/-============================================================================
  SECTION 2: SELF-ADJOINTNESS PRESERVATION
============================================================================-/

/-
Self-adjoint operators are central to quantum mechanics as they represent
observables. These lemmas show that self-adjointness is preserved under
certain transformations, which is crucial when we shift operators by their
expectation values in the uncertainty proof.
-/

/--
Self-adjointness is preserved under affine transformations by real scalars.

Mathematical statement: If A is self-adjoint and λ ∈ ℝ, then A - λI is self-adjoint.

Physical interpretation: Shifting an observable by a real constant (like
subtracting its expectation value) gives another observable. This is why
we can work with Ã = A - ⟨A⟩I in the uncertainty proof.

Technical note: The domain D must be preserved under both A and scalar
multiplication. In practice, this is usually a dense subspace of the
Hilbert space.
-/
lemma isSymmetric_sub_smul_of_real {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [IsScalarTower ℝ ℂ H] (A : H →ₗ[ℂ] H) (lambda : ℝ) (D : Submodule ℂ H)
    (hA_sym : ∀ v w, v ∈ D → w ∈ D → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ) :
    ∀ v w, v ∈ D → w ∈ D → ⟪(A - lambda • 1) v, w⟫_ℂ = ⟪v, (A - lambda • 1) w⟫_ℂ := by
  intros v w hv hw
  -- Expand (A - λI) as pointwise operations
  show ⟪A v - lambda • v, w⟫_ℂ = ⟪v, A w - lambda • w⟫_ℂ

  -- Use linearity of inner product
  simp only [inner_sub_left, inner_sub_right]

  -- Use self-adjointness of A
  rw [hA_sym v w hv hw]

  -- The scalar terms need careful handling due to complex scalars
  ring_nf
  have h1 : ⟪lambda • v, w⟫_ℂ = ⟪(lambda : ℂ) • v, w⟫_ℂ := by congr 1
  have h2 : ⟪v, lambda • w⟫_ℂ = ⟪v, (lambda : ℂ) • w⟫_ℂ := by congr 1
  rw [h1, h2, inner_smul_left, inner_smul_right]

  -- For real λ, we have conj(λ) = λ
  simp only [Complex.conj_ofReal]

/-============================================================================
  SECTION 3: COMMUTATOR AND ANTICOMMUTATOR PROPERTIES
============================================================================-/

/-
The heart of Robertson's proof lies in decomposing the inner product
⟨Aψ, Bψ⟩ using commutators and anticommutators. These lemmas establish
the crucial properties that:
  - Commutator expectation values are purely imaginary
  - Anticommutator expectation values are purely real

This decomposition, combined with Cauchy-Schwarz, yields the uncertainty bound.
-/

/--
The expectation value of a commutator of self-adjoint operators is purely imaginary.

Mathematical insight: For self-adjoint A and B,
  ⟨ψ, [A,B]ψ⟩ = ⟨ψ, ABψ⟩ - ⟨ψ, BAψ⟩
              = ⟨Aψ, Bψ⟩ - ⟨Bψ, Aψ⟩
              = ⟨Aψ, Bψ⟩ - ⟨Aψ, Bψ⟩*

This difference of a complex number and its conjugate is purely imaginary.

Physical interpretation: The commutator [A,B] measures the "incompatibility"
of observables A and B. Its imaginary expectation value directly leads to
the uncertainty relation's lower bound.

Application in Robertson's proof: This shows that the uncertainty bound
|⟨[A,B]⟩|/2 comes from the imaginary part of ⟨Aψ, Bψ⟩.
-/
lemma expectation_commutator_re_eq_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ[ℂ] H) (ψ : H) (D_A D_B : Submodule ℂ H)
    (hA_sa : ∀ v w, v ∈ D_A → w ∈ D_A → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ)
    (hB_sa : ∀ v w, v ∈ D_B → w ∈ D_B → ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ)
    (hdomain_ψ_A : ψ ∈ D_A)
    (hdomain_ψ_B : ψ ∈ D_B)
    (hdomain_Bψ_A : B ψ ∈ D_A)
    (hdomain_Aψ_B : A ψ ∈ D_B) :
    (⟪ψ, (A ∘ₗ B - B ∘ₗ A) ψ⟫_ℂ).re = 0 := by
  -- Expand the commutator [A,B] = AB - BA
  simp_rw [LinearMap.sub_apply, inner_sub_right, LinearMap.comp_apply]

  -- Use self-adjointness to move operators between sides of inner product
  -- ⟨ψ, ABψ⟩ = ⟨Aψ, Bψ⟩ and ⟨ψ, BAψ⟩ = ⟨Bψ, Aψ⟩
  rw [← hA_sa ψ (B ψ) hdomain_ψ_A hdomain_Bψ_A]
  rw [← hB_sa ψ (A ψ) hdomain_ψ_B hdomain_Aψ_B]

  -- Now we have ⟨Aψ, Bψ⟩ - ⟨Bψ, Aψ⟩ = ⟨Aψ, Bψ⟩ - ⟨Aψ, Bψ⟩*
  rw [← inner_conj_symm]
  rw [Complex.sub_re, Complex.conj_re]

  -- The real part of (z - z*) is Re(z) - Re(z*) = Re(z) - Re(z) = 0
  ring

/--
The expectation value of an anticommutator of self-adjoint operators is purely real.

Mathematical insight: For self-adjoint A and B,
  ⟨ψ, {A,B}ψ⟩ = ⟨ψ, ABψ⟩ + ⟨ψ, BAψ⟩
              = ⟨Aψ, Bψ⟩ + ⟨Bψ, Aψ⟩
              = ⟨Aψ, Bψ⟩ + ⟨Aψ, Bψ⟩*

This sum of a complex number and its conjugate is purely real.

Physical interpretation: The anticommutator {A,B} = AB + BA represents
the "compatible" part of the operators' composition. Unlike the commutator,
it doesn't directly contribute to the uncertainty bound.

Application in Robertson's proof: This separates the real and imaginary
parts of ⟨Aψ, Bψ⟩, allowing us to isolate the commutator contribution
that creates the uncertainty bound.
-/
lemma expectation_anticommutator_im_eq_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ[ℂ] H) (ψ : H) (D_A D_B : Submodule ℂ H)
    (hA_sa : ∀ v w, v ∈ D_A → w ∈ D_A → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ)
    (hB_sa : ∀ v w, v ∈ D_B → w ∈ D_B → ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ)
    (hdomain_ψ_A : ψ ∈ D_A)
    (hdomain_ψ_B : ψ ∈ D_B)
    (hdomain_Bψ_A : B ψ ∈ D_A)
    (hdomain_Aψ_B : A ψ ∈ D_B) :
    (⟪ψ, (A ∘ₗ B + B ∘ₗ A) ψ⟫_ℂ).im = 0 := by
  -- Expand the anticommutator {A,B} = AB + BA
  simp_rw [LinearMap.add_apply, inner_add_right, LinearMap.comp_apply]

  -- Use self-adjointness to move operators
  rw [← hA_sa ψ (B ψ) hdomain_ψ_A hdomain_Bψ_A]
  rw [← hB_sa ψ (A ψ) hdomain_ψ_B hdomain_Aψ_B]

  -- Now we have ⟨Aψ, Bψ⟩ + ⟨Bψ, Aψ⟩ = ⟨Aψ, Bψ⟩ + ⟨Aψ, Bψ⟩*
  rw [← inner_conj_symm]
  rw [Complex.add_im, Complex.conj_im]

  -- The imaginary part of (z + z*) is Im(z) + Im(z*) = Im(z) - Im(z) = 0
  ring


/-============================================================================
  SECTION 4: KEY DECOMPOSITION THEOREM
============================================================================-/

/-
This section contains the main decomposition theorem that combines
the above lemmas to show:

  ⟨Aψ, Bψ⟩ = (1/2)⟨ψ, {A,B}ψ⟩ + (i/2)⟨ψ, i[A,B]ψ⟩

where the first term is real and the second provides the uncertainty bound.
-/

/--
The fundamental decomposition of inner products for self-adjoint operators.

This is the key identity that enables Robertson's proof:
  2⟨Aψ, Bψ⟩ = ⟨ψ, {A,B}ψ⟩ + ⟨ψ, [A,B]ψ⟩
            = (real part) + (imaginary part)

From Cauchy-Schwarz: |⟨Aψ, Bψ⟩|² ≤ ‖Aψ‖² · ‖Bψ‖² = Var(A) · Var(B)

The imaginary part gives: |Im⟨Aψ, Bψ⟩| = (1/2)|⟨[A,B]⟩|

Therefore: Var(A) · Var(B) ≥ (1/4)|⟨[A,B]⟩|²

Taking square roots: σ_A · σ_B ≥ (1/2)|⟨[A,B]⟩|

This is Robertson's uncertainty relation!
-/
theorem inner_product_decomposition {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ[ℂ] H) (ψ : H) (D : Submodule ℂ H)
    (hA_sa : ∀ v w, v ∈ D → w ∈ D → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ)
    (_ /-hB_sa-/ : ∀ v w, v ∈ D → w ∈ D → ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ)
    (hdomain : ψ ∈ D ∧ A ψ ∈ D ∧ B ψ ∈ D) :
    2 * ⟪A ψ, B ψ⟫_ℂ = ⟪ψ, (A ∘ₗ B + B ∘ₗ A) ψ⟫_ℂ + ⟪ψ, (A ∘ₗ B - B ∘ₗ A) ψ⟫_ℂ := by
  -- This follows from the algebraic identity: AB + BA + (AB - BA) = 2AB
  -- First, let's establish the algebraic fact
  have h_alg : ∀ (x y : ℂ), x + y + (x - y) = 2 * x := by
    intros x y
    ring

  -- Now apply this to our inner products
  -- Note that (A ∘ₗ B) ψ = A (B ψ) and similarly for B ∘ₗ A
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, inner_add_right, inner_sub_right]

  -- We have: ⟪ψ, A (B ψ) + B (A ψ)⟫_ℂ + ⟪ψ, A (B ψ) - B (A ψ)⟫_ℂ
  -- = ⟪ψ, A (B ψ)⟫_ℂ + ⟪ψ, B (A ψ)⟫_ℂ + ⟪ψ, A (B ψ)⟫_ℂ - ⟪ψ, B (A ψ)⟫_ℂ
  -- = 2 * ⟪ψ, A (B ψ)⟫_ℂ

  ring_nf

  -- Now we need to show ⟪ψ, A (B ψ)⟫_ℂ = ⟪A ψ, B ψ⟫_ℂ
  -- This follows from self-adjointness of A
  have h_adj : ⟪ψ, A (B ψ)⟫_ℂ = ⟪A ψ, B ψ⟫_ℂ := by
    rw [hA_sa ψ (B ψ) hdomain.1 hdomain.2.2]

  rw [← h_adj]

/-============================================================================
  HELPER LEMMAS FOR CAUCHY-SCHWARZ APPLICATION
============================================================================-/

/-
Variance is non-negative for self-adjoint operators.

This seems obvious but needs proof: Var(A) = ⟨(A - ⟨A⟩I)²⟩ ≥ 0

The proof uses the fact that for self-adjoint operators,
⟨ψ, A²ψ⟩ = ⟨Aψ, Aψ⟩ = ‖Aψ‖² ≥ 0

lemma variance_nonneg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ[ℂ] H) (ψ : H) (D : Submodule ℂ H)
    (hA_sa : ∀ v w, v ∈ D → w ∈ D → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ)
    (hdomain : ψ ∈ D ∧ A ψ ∈ D) (hnorm : ‖ψ‖ = 1) :
    0 ≤ (⟪ψ, A (A ψ)⟫_ℂ - (⟪ψ, A ψ⟫_ℂ).re ^ 2).re := by

-/

/-============================================================================
  SECTION 5: DOMAIN PRESERVATION LEMMAS
============================================================================-/

/-
For unbounded operators (like position and momentum), we need to carefully
track domains. These lemmas ensure that the necessary operations preserve
the domain structure required for self-adjointness.
-/

/--
If ψ is in the domain of both A and B, and their commutator is defined,
then the shifted operators (A - ⟨A⟩I) preserve the domain structure
needed for the uncertainty relation.

Note: This is a simplified version. The actual statement would depend on
the specific domain conditions, which can be quite technical for unbounded
operators. In the bounded case, this is trivial since the domain is the
entire Hilbert space.
-/
lemma shifted_operator_domain_preservation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ[ℂ] H) (ψ : H) (D : Submodule ℂ H) (μ : ℝ)
    (hdomain : ψ ∈ D) :
    (A - μ • (1 : H →ₗ[ℂ] H)) ψ ∈ D → A ψ ∈ D := by
  intro h_shifted

  -- We have (A - μI)ψ ∈ D
  -- This means Aψ - μψ ∈ D
  -- Since D is a submodule, ψ ∈ D implies μψ ∈ D
  have h_scaled : μ • ψ ∈ D := by
    -- D is closed under scalar multiplication
    have : (μ : ℂ) • ψ ∈ D := D.smul_mem (μ : ℂ) hdomain
    convert this
    -- μ as a real number coerced to ℂ acts the same as μ •
    --simp only [Complex.ofReal_eq_coe] <-- not needed, no goals to be solved

  -- Since D is closed under addition and (Aψ - μψ) ∈ D and μψ ∈ D
  -- we have Aψ = (Aψ - μψ) + μψ ∈ D
  have h_sum : (A - μ • (1 : H →ₗ[ℂ] H)) ψ + μ • ψ ∈ D := by
    exact D.add_mem h_shifted h_scaled

  -- Now we need to show that (A - μ • 1) ψ + μ • ψ = A ψ
  -- First, expand (A - μ • 1) ψ
  have h_expand : (A - μ • (1 : H →ₗ[ℂ] H)) ψ = A ψ - μ • ψ := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply]
    simp

  -- Rewrite h_sum using this expansion
  rw [h_expand] at h_sum

  -- Now h_sum states: (A ψ - μ • ψ) + μ • ψ ∈ D
  -- This simplifies to A ψ ∈ D by cancellation
  have h_cancel : A ψ - μ • ψ + μ • ψ = A ψ := by
    abel  -- or use: simp only [sub_add_cancel]

  rw [← h_cancel]
  exact h_sum

/-============================================================================
  ADDITIONAL HELPER LEMMAS
============================================================================-/

/--
Helper lemma: The commutator of self-adjoint operators has purely imaginary
expectation values. This is a key ingredient in Robertson's proof.
-/
lemma commutator_expectation_imaginary {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ[ℂ] H) (ψ : H) (D : Submodule ℂ H)
    (hA_sa : ∀ v w, v ∈ D → w ∈ D → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ)
    (hB_sa : ∀ v w, v ∈ D → w ∈ D → ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ)
    (hdomain : ψ ∈ D ∧ A ψ ∈ D ∧ B ψ ∈ D ∧ A (B ψ) ∈ D ∧ B (A ψ) ∈ D) :
    (⟪ψ, (A ∘ₗ B - B ∘ₗ A) ψ⟫_ℂ).re = 0 := by
  -- This follows from the fact that [A,B]† = -[A,B] for self-adjoint A,B
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_right]

  -- Use self-adjointness to rewrite
  have h1 : ⟪ψ, A (B ψ)⟫_ℂ = ⟪A ψ, B ψ⟫_ℂ := by
    rw [hA_sa ψ (B ψ) hdomain.1 hdomain.2.2.1]

  have h2 : ⟪ψ, B (A ψ)⟫_ℂ = ⟪B ψ, A ψ⟫_ℂ := by
    rw [hB_sa ψ (A ψ) hdomain.1 hdomain.2.1]

  rw [h1, h2]

  -- Now we have ⟪Aψ, Bψ⟫ - ⟪Bψ, Aψ⟫ = ⟪Aψ, Bψ⟫ - ⟪Aψ, Bψ⟫*
  rw [← inner_conj_symm (B ψ) (A ψ)]

  -- The real part of z - z* is 0
  simp only [Complex.sub_re, Complex.conj_re]
  ring

/--
The anticommutator of self-adjoint operators has real expectation values.
-/
lemma anticommutator_expectation_real {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ[ℂ] H) (ψ : H) (D : Submodule ℂ H)
    (hA_sa : ∀ v w, v ∈ D → w ∈ D → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ)
    (hB_sa : ∀ v w, v ∈ D → w ∈ D → ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ)
    (hdomain : ψ ∈ D ∧ A ψ ∈ D ∧ B ψ ∈ D ∧ A (B ψ) ∈ D ∧ B (A ψ) ∈ D) :
    (⟪ψ, (A ∘ₗ B + B ∘ₗ A) ψ⟫_ℂ).im = 0 := by
  -- The anticommutator {A,B} = AB + BA is self-adjoint when A and B are
  simp only [LinearMap.add_apply, LinearMap.comp_apply, inner_add_right]

  -- Use self-adjointness
  have h1 : ⟪ψ, A (B ψ)⟫_ℂ = ⟪A ψ, B ψ⟫_ℂ := by
    rw [hA_sa ψ (B ψ) hdomain.1 hdomain.2.2.1]

  have h2 : ⟪ψ, B (A ψ)⟫_ℂ = ⟪B ψ, A ψ⟫_ℂ := by
    rw [hB_sa ψ (A ψ) hdomain.1 hdomain.2.1]

  rw [h1, h2]

  -- Now we have ⟪Aψ, Bψ⟫ + ⟪Bψ, Aψ⟫ = ⟪Aψ, Bψ⟫ + ⟪Aψ, Bψ⟫*
  rw [← inner_conj_symm (B ψ) (A ψ)]

  -- The imaginary part of z + z* is 0
  simp only [Complex.add_im, Complex.conj_im]
  ring


end Robertson.Lemmas
end Robertson.Core
