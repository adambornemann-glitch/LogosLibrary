/-
Author: Adam Bornemann
Created: 9/16/2025
Updated: 11/15/2025

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
  13. Basic theorems

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
  self_adjoint : IsSelfAdjoint op

/--
An unbounded observable (for position, momentum operators).

Many fundamental observables are unbounded:
  - Position: X̂ψ(x) = xψ(x)
  - Momentum: P̂ψ(x) = -iℏ(d/dx)ψ(x)
  - Hamiltonian: Ĥ = P̂²/(2m) + V(X̂)

Mathematical subtlety: For unbounded operators, symmetric ≠ self-adjoint.
Self-adjointness requires careful domain specification.
-/
structure UnboundedObservable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  op : H →ₗ[ℂ] H  -- Linear but not necessarily bounded
  domain : Submodule ℂ H  -- Dense domain where operator is defined
  dense : Dense (domain : Set H)
  self_adjoint : ∀ (ψ φ : H), ψ ∈ domain → φ ∈ domain →
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
  {simp_all!; ring_nf!; sorry}


/-- Hadamard basis state |−⟩ = (|0⟩ - |1⟩)/√2 -/
noncomputable def ketMinus : Qubit where
  ψ := fun i => if i = 0 then Complex.mk (1 / Real.sqrt 2) 0
                else Complex.mk (-1 / Real.sqrt 2) 0
  normalized := by sorry

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
-/
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

/-- Bell state |Φ⁺⟩ = (|00⟩ + |11⟩)/√2 -/
noncomputable def bell_Φ_plus : QuantumState 4 where
  ψ := fun i => if i = 0 ∨ i = 3 then Complex.mk (1 / Real.sqrt 2) 0 else 0
  normalized := by sorry

/-- GHZ state: |GHZ⟩ = (|000⟩ + |111⟩)/√2 -/
noncomputable def GHZ : QuantumState 8 where
  ψ := fun i => if i = 0 ∨ i = 7 then Complex.mk (1 / Real.sqrt 2) 0 else 0
  normalized := by sorry

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

/-============================================================================
  SECTION 12: UNITARY EVOLUTION
============================================================================-/

/--
Unitary operators preserve norms and probabilities.

Time evolution: |ψ(t)⟩ = U(t)|ψ(0)⟩ where U(t) = exp(-iHt/ℏ)
-/
structure Unitary (n : ℕ) where
  U : Matrix (Fin n) (Fin n) ℂ
  unitary : U * star U = 1 ∧ star U * U = 1

/-- Apply unitary evolution -/
noncomputable def evolve {n : ℕ} (U : Unitary n) (ψ : QuantumState n) : QuantumState n where
  ψ := fun i => ∑ j, U.U i j * ψ.ψ j
  normalized := by sorry

/-============================================================================
  SECTION 13: CANONICAL COMMUTATION RELATIONS
============================================================================-/

/--
The canonical commutation relation [X̂,P̂] = iℏ.

Foundation of Heisenberg's uncertainty principle: ΔxΔp ≥ ℏ/2
-/
structure CanonicalPair (n : ℕ) where
  X : MatrixObservable n  -- Position
  P : MatrixObservable n  -- Momentum
  commutation : X.M * P.M - P.M * X.M =
    Complex.I • (ℏ • (1 : Matrix (Fin n) (Fin n) ℂ))

/-============================================================================
  SECTION 14: ROBERTSON'S UNCERTAINTY RELATION
============================================================================-/

/--
Robertson's Uncertainty Principle.

For any two observables A and B with non-zero commutator,
their standard deviations satisfy:

  σ_A · σ_B ≥ (1/2)|⟨[A,B]⟩|

This is the fundamental limit on simultaneous knowledge of
non-commuting observables.
-/
theorem robertson_uncertainty {n : ℕ} (ψ : QuantumState n) (A B : MatrixObservable n)
    (h_nonzero : expectation_matrix ψ [A.M, B.M] ≠ 0) :
    ∃ (bound : ℝ), bound > 0 ∧
    -- σ_A² · σ_B² ≥ bound²
    -- where bound = |⟨[A,B]⟩|/2
    sorry := by sorry

/-============================================================================
  SECTION 15: FUNDAMENTAL AXIOMS
============================================================================-/

/--
The Gaussian integral - fundamental for quantum mechanics.

Used for normalizing Gaussian wave packets and computing
partition functions in quantum statistical mechanics.
-/
axiom integral_gaussian : ∫ x : ℝ, Real.exp (-x^2) = Real.sqrt Real.pi

/-============================================================================
  SECTION 16: BASIC THEOREMS
============================================================================-/

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



end Robertson.Core
