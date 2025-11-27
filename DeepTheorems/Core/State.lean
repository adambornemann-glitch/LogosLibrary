/-
=============================================================================================================
QUANTUM STATES: DENSITY OPERATORS ON ℂⁿ
=============================================================================================================

This file develops the density operator formalism for quantum states on
finite-dimensional Hilbert spaces ℂⁿ.

PHYSICAL MOTIVATION:
  Pure state |ψ⟩: Complete quantum information, represented by ρ = |ψ⟩⟨ψ|
  Mixed state ρ:  Incomplete information OR entangled subsystem

  Mixed states arise from:
    1. Classical ignorance: Statistical mixture of pure states
    2. Entanglement: Reduced state of entangled bipartite system
    3. Decoherence: Interaction with environment

MATHEMATICAL CONTENT:
  §1 Density operator structure
  §2 Pure state construction
  §3 Purity and mixedness measures
  §4 Maximally mixed state
  §5 Spectral properties (TODO)
  §6 Von Neumann entropy (TODO)

CONVENTIONS:
  - n denotes dimension of Hilbert space
  - ρ denotes density operator
  - Tr(·) denotes trace
  - γ = Tr(ρ²) is purity

Built on: QHilbert (Hilbert.lean)
  - trace n A : Trace of bounded operator
  - |ψ⟩⟨φ| : Outer product notation
  - HermitianOp : Self-adjoint operators

References:
  [1] von Neumann, "Mathematical Foundations of QM" (1932)
  [2] Nielsen & Chuang, "Quantum Computation and Quantum Information" Ch. 2
  [3] Wilde, "Quantum Information Theory" (2013)
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
-- Import our Hilbert space foundation
import LogosLibrary.DeepTheorems.Core.Hilbert.Basic

namespace QState

open scoped InnerProductSpace TensorProduct ComplexConjugate
open Complex QHilbert



/-
Helper lemmas
-/
/-- Composition of outer products: |ψ⟩⟨φ| ∘ |χ⟩⟨ξ| = ⟨φ|χ⟩ |ψ⟩⟨ξ| -/
lemma outerProduct_comp (ψ φ χ ξ : ℂ^n) :
    (|ψ⟩⟨φ|).comp (|χ⟩⟨ξ|) = ⟪φ, χ⟫_ℂ • |ψ⟩⟨ξ| := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
  simp only [outerProduct_apply]
  -- LHS: |ψ⟩⟨φ| (⟪ξ, v⟫_ℂ • χ) = ⟪φ, ⟪ξ, v⟫_ℂ • χ⟫_ℂ • ψ
  -- RHS: ⟪φ, χ⟫_ℂ • (⟪ξ, v⟫_ℂ • ψ)
  rw [inner_smul_right (𝕜 := ℂ)]
  rw [smul_smul]
  ring_nf




/-!
=============================================================================================================
## Section 1: Density Operator Structure
=============================================================================================================

A density operator ρ on ℂⁿ is characterized by three properties:

  1. **Hermitian**: ρ† = ρ
     - Ensures real expectation values
     - Guarantees real eigenvalues

  2. **Positive semidefinite**: ⟨ψ|ρ|ψ⟩ ≥ 0 for all |ψ⟩
     - Ensures non-negative probabilities
     - Guarantees non-negative eigenvalues

  3. **Trace one**: Tr(ρ) = 1
     - Normalization condition
     - Eigenvalues form probability distribution

Physical interpretation:
  ρ = Σᵢ pᵢ |ψᵢ⟩⟨ψᵢ| (ensemble interpretation)
  where pᵢ ≥ 0 and Σᵢ pᵢ = 1

Note: The ensemble decomposition is NOT unique. Many different ensembles
can give the same density operator. Only ρ itself is physically observable.
-/

/-- A density operator on the n-dimensional complex Hilbert space ℂⁿ.

A density operator represents the most general quantum state, encompassing
both pure states (complete information) and mixed states (incomplete
information or entanglement with another system).

Fields:
  - `op`: The underlying bounded linear operator on ℂⁿ
  - `hermitian`: Self-adjointness ρ† = ρ
  - `positive`: Positive semidefiniteness ⟨ψ|ρ|ψ⟩ ≥ 0
  - `trace_one`: Normalization Tr(ρ) = 1
-/
structure DensityOp (n : ℕ) where
  /-- The underlying bounded linear operator -/
  op : BoundedOp (ℂ^n)
  /-- Hermitian property: ρ† = ρ -/
  hermitian : ContinuousLinearMap.adjoint op = op
  /-- Positive semidefinite: ⟨ψ|ρ|ψ⟩ ≥ 0 for all ψ -/
  positive : ∀ ψ : ℂ^n, 0 ≤ (⟪ψ, op ψ⟫_ℂ).re
  /-- Trace normalization: Tr(ρ) = 1 -/
  trace_one : trace n op = 1

namespace DensityOp

variable {n : ℕ}

/-- Coercion allowing a DensityOp to be used as a BoundedOp directly. -/
instance : Coe (DensityOp n) (BoundedOp (ℂ^n)) := ⟨DensityOp.op⟩

/-- Apply a density operator to a vector.

For ρ a density operator and ψ a state vector, `ρ.apply ψ` computes ρ|ψ⟩.
-/
def apply (ρ : DensityOp n) (ψ : ℂ^n) : ℂ^n := ρ.op ψ

/-- Expectation values ⟨ψ|ρ|ψ⟩ of density operators are real.

This is a consequence of the Hermitian property: for self-adjoint operators,
all diagonal matrix elements are real.

Proof: ⟨ψ|ρ|ψ⟩ = ⟨ρψ|ψ⟩ = ⟨ψ|ρ†ψ⟩* = ⟨ψ|ρψ⟩*, so ⟨ψ|ρ|ψ⟩ ∈ ℝ.
-/
theorem expectation_real (ρ : DensityOp n) (ψ : ℂ^n) :
    (⟪ψ, ρ.op ψ⟫_ℂ).im = 0 := by
  have h : ⟪ρ.op ψ, ψ⟫_ℂ = ⟪ψ, ρ.op ψ⟫_ℂ := by
    calc ⟪ρ.op ψ, ψ⟫_ℂ
        = ⟪ψ, (ContinuousLinearMap.adjoint ρ.op) ψ⟫_ℂ :=
          (ContinuousLinearMap.adjoint_inner_right ρ.op ψ ψ).symm
      _ = ⟪ψ, ρ.op ψ⟫_ℂ := by rw [ρ.hermitian]
  have hconj : ⟪ψ, ρ.op ψ⟫_ℂ = conj ⟪ψ, ρ.op ψ⟫_ℂ := by
    calc ⟪ψ, ρ.op ψ⟫_ℂ
        = ⟪ρ.op ψ, ψ⟫_ℂ := h.symm
      _ = conj ⟪ψ, ρ.op ψ⟫_ℂ := (inner_conj_symm (ρ.op ψ) ψ).symm
  exact Complex.conj_eq_iff_im.mp hconj.symm
/-!
## Section 1 Addition: Convex Combinations

Density operators form a convex set: if ρ₁ and ρ₂ are density operators
and 0 ≤ p ≤ 1, then pρ₁ + (1-p)ρ₂ is also a density operator.

This reflects the physical operation of probabilistic mixing:
  "Prepare ρ₁ with probability p, otherwise prepare ρ₂"

The convex structure is essential for:
  - Defining mixed states as convex combinations of pure states
  - Proving concavity of von Neumann entropy
  - Characterizing pure states as extreme points
-/

/-- Convex combination of two density operators.

Given density operators ρ₁, ρ₂ and probability p ∈ [0,1], constructs
the mixed state ρ = p·ρ₁ + (1-p)·ρ₂.

Physical interpretation: Prepare ρ₁ with probability p, prepare ρ₂
with probability (1-p). The resulting ensemble is described by ρ.
-/
noncomputable def mix (ρ₁ ρ₂ : DensityOp n) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : DensityOp n where
  op := (p : ℂ) • ρ₁.op + ((1 - p) : ℂ) • ρ₂.op

  hermitian := by
    have h1 : (p : ℂ) = conj (p : ℂ) := by simp
    have h2 : ((1 - p) : ℂ) = conj ((1 - p) : ℂ) := by simp
    have adj1 : ContinuousLinearMap.adjoint ((p : ℂ) • ρ₁.op) =
                conj (p : ℂ) • ContinuousLinearMap.adjoint ρ₁.op := adjoint_smul _ _
    have adj2 : ContinuousLinearMap.adjoint (((1 - p) : ℂ) • ρ₂.op) =
                conj ((1 - p) : ℂ) • ContinuousLinearMap.adjoint ρ₂.op := adjoint_smul _ _
    calc ContinuousLinearMap.adjoint ((p : ℂ) • ρ₁.op + ((1 - p) : ℂ) • ρ₂.op)
        = ContinuousLinearMap.adjoint ((p : ℂ) • ρ₁.op) +
          ContinuousLinearMap.adjoint (((1 - p) : ℂ) • ρ₂.op) := by
          rw [map_add]
      _ = conj (p : ℂ) • ContinuousLinearMap.adjoint ρ₁.op +
          conj ((1 - p) : ℂ) • ContinuousLinearMap.adjoint ρ₂.op := by
          rw [adj1, adj2]
      _ = conj (p : ℂ) • ρ₁.op + conj ((1 - p) : ℂ) • ρ₂.op := by
          rw [ρ₁.hermitian, ρ₂.hermitian]
      _ = (p : ℂ) • ρ₁.op + ((1 - p) : ℂ) • ρ₂.op := by
          rw [← h1, ← h2]

  positive := fun ψ => by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    rw [inner_add_right (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ)]
    have hr1 : (⟪ψ, ρ₁.op ψ⟫_ℂ).im = 0 := expectation_real ρ₁ ψ
    have hr2 : (⟪ψ, ρ₂.op ψ⟫_ℂ).im = 0 := expectation_real ρ₂ ψ
    have hp1 : 0 ≤ (⟪ψ, ρ₁.op ψ⟫_ℂ).re := ρ₁.positive ψ
    have hp2 : 0 ≤ (⟪ψ, ρ₂.op ψ⟫_ℂ).re := ρ₂.positive ψ
    -- Inner products are real and non-negative
    have hre1 : ⟪ψ, ρ₁.op ψ⟫_ℂ = (⟪ψ, ρ₁.op ψ⟫_ℂ).re := by
      rw [Complex.ext_iff]
      simp [hr1]
    have hre2 : ⟪ψ, ρ₂.op ψ⟫_ℂ = (⟪ψ, ρ₂.op ψ⟫_ℂ).re := by
      rw [Complex.ext_iff]
      simp [hr2]
    rw [hre1, hre2]
    -- Now just real arithmetic
    have h1p : 0 ≤ 1 - p := by linarith
    show 0 ≤ ((p : ℂ) * (⟪ψ, ρ₁.op ψ⟫_ℂ).re + ((1 - p) : ℂ) * (⟪ψ, ρ₂.op ψ⟫_ℂ).re).re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
               Complex.ofReal_im, mul_zero, sub_zero] -- unused Complex.ofReal_mul
    calc p * (⟪ψ, ρ₁.op ψ⟫_ℂ).re + (1 - p) * (⟪ψ, ρ₂.op ψ⟫_ℂ).re
        ≥ p * 0 + (1 - p) * 0 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hp1 hp₀
          · exact mul_le_mul_of_nonneg_left hp2 h1p
      _ = 0 := by ring

  trace_one := by
    rw [trace_add, trace_smul, trace_smul]
    rw [ρ₁.trace_one, ρ₂.trace_one]
    simp only [mul_one]
    ring

/-- Mixing with p=1 returns the first state. -/
theorem mix_one (ρ₁ ρ₂ : DensityOp n) (h₀ : (0:ℝ) ≤ 1) (h₁ : (1:ℝ) ≤ 1) :
    (mix ρ₁ ρ₂ 1 h₀ h₁).op = ρ₁.op := by
  simp only [mix]
  ext ψ
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  simp only [sub_self, zero_smul, add_zero,
             Complex.ofReal_one, one_smul]

/-- Mixing with p=0 returns the second state. -/
theorem mix_zero (ρ₁ ρ₂ : DensityOp n) (h₀ : (0:ℝ) ≤ 0) (h₁ : (0:ℝ) ≤ 1) :
    (mix ρ₁ ρ₂ 0 h₀ h₁).op = ρ₂.op := by
  simp only [mix]
  ext ψ
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  simp only [Complex.ofReal_zero, zero_smul, zero_add, sub_zero, one_smul]

/-- Mixing is symmetric under p ↔ (1-p). -/
theorem mix_symm (ρ₁ ρ₂ : DensityOp n) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (mix ρ₁ ρ₂ p hp₀ hp₁).op = (mix ρ₂ ρ₁ (1 - p) (by linarith) (by linarith)).op := by
  simp only [mix]
  ext ψ
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  ring_nf
  rw [ofReal_sub]
  rw [coe_smul]
  rw [← ContinuousLinearMap.map_smul]
  simp
  expose_names
  exact AddCommMagma.add_comm (↑p * ρ₁.op ψ i) ((1 - ↑p) * ρ₂.op ψ i)

/-!
=============================================================================================================
## Section 2: Pure State Construction
=============================================================================================================

A pure state is one with complete quantum information, represented by a
single state vector |ψ⟩. The corresponding density operator is the
projector ρ = |ψ⟩⟨ψ|.

Properties of pure state density operators:
  - Rank 1 (single non-zero eigenvalue)
  - ρ² = ρ (idempotent)
  - Tr(ρ²) = 1 (purity equals 1)
  - Single eigenvalue λ = 1, all others 0
-/

/-- Construct a density operator from a pure quantum state.

Given a normalized state vector |ψ⟩ with ‖ψ‖ = 1, constructs the
density operator ρ = |ψ⟩⟨ψ|.

The resulting operator satisfies:
  - Hermitian: (|ψ⟩⟨ψ|)† = |ψ⟩⟨ψ|
  - Positive: ⟨φ|ψ⟩⟨ψ|φ⟩ = |⟨ψ|φ⟩|² ≥ 0
  - Trace one: Tr(|ψ⟩⟨ψ|) = ⟨ψ|ψ⟩ = 1
-/
noncomputable def fromPure (ψ : QuantumState (ℂ^n)) : DensityOp n where
  op := |ψ.vec⟩⟨ψ.vec|

  hermitian := outerProduct_self_hermitian ψ.vec

  positive := fun φ => by
    simp only [outerProduct_apply]
    rw [inner_smul_right (𝕜 := ℂ)]
    rw [(inner_conj_symm ψ.vec φ).symm]
    rw [mul_comm]
    rw [mul_conj]
    simp [Complex.normSq_nonneg]

  trace_one := by
    rw [trace_outerProduct]
    rw [inner_self_eq_norm_sq_to_K, ψ.normalized]
    simp

/-!
=============================================================================================================
## Section 3: Purity and Mixedness Measures
=============================================================================================================

How "mixed" is a quantum state? Several measures quantify this:

**Purity**: γ = Tr(ρ²) ∈ [1/n, 1]
  - γ = 1: Pure state (complete information)
  - γ = 1/n: Maximally mixed (minimal information)
  - Interpretation: γ = Σᵢ λᵢ² where λᵢ are eigenvalues

**Linear Entropy**: S_L = 1 - Tr(ρ²) = 1 - γ ∈ [0, 1-1/n]
  - S_L = 0: Pure state
  - S_L = 1 - 1/n: Maximally mixed
  - Quick approximation to von Neumann entropy

**Von Neumann Entropy** (TODO): S = -Tr(ρ ln ρ) ∈ [0, ln n]
  - THE canonical measure of quantum mixedness
  - S = 0: Pure state
  - S = ln n: Maximally mixed

Relation: S ≥ S_L with equality only for pure states.
-/

/-- Purity of a density operator: γ = Tr(ρ²).

The purity measures how "pure" or "mixed" a quantum state is.

Range: 1/n ≤ γ ≤ 1
  - γ = 1 iff ρ is a pure state
  - γ = 1/n iff ρ is maximally mixed

In terms of eigenvalues: γ = Σᵢ λᵢ²
-/
noncomputable def purity (ρ : DensityOp n) : ℝ :=
  (trace n (ρ.op.comp ρ.op)).re

/-- A density operator represents a pure state iff its purity equals 1.

Equivalent characterizations of pure states:
  - Tr(ρ²) = 1
  - ρ² = ρ (idempotent)
  - Rank(ρ) = 1
  - Unique non-zero eigenvalue (equal to 1)
-/
def isPure (ρ : DensityOp n) : Prop :=
  ρ.purity = 1

/-- Pure states constructed via fromPure have purity 1.

Proof sketch: For ρ = |ψ⟩⟨ψ|,
  ρ² = |ψ⟩⟨ψ|ψ⟩⟨ψ| = ⟨ψ|ψ⟩ |ψ⟩⟨ψ| = |ψ⟩⟨ψ| = ρ

Therefore Tr(ρ²) = Tr(ρ) = 1.
-/
/- Pure states from fromPure have purity 1 -/
theorem fromPure_isPure (ψ : QuantumState (ℂ^n)) :
    (fromPure ψ).isPure := by
  simp only [isPure, purity, fromPure]
  rw [outerProduct_comp]
  rw [inner_self_eq_norm_sq_to_K, ψ.normalized]
  -- Goal: (trace n ((1 : ℝ)^2 • |ψ.vec⟩⟨ψ.vec|)).re = 1
  norm_num
  -- Goal: (trace n |ψ.vec⟩⟨ψ.vec|).re = 1
  rw [trace_outerProduct]
  rw [inner_self_eq_norm_sq_to_K, ψ.normalized]
  norm_num

/-- Linear entropy: S_L = 1 - Tr(ρ²).

A simple measure of mixedness that approximates von Neumann entropy.

Range: 0 ≤ S_L ≤ 1 - 1/n
  - S_L = 0 iff ρ is pure
  - S_L = 1 - 1/n iff ρ is maximally mixed

Relation to von Neumann entropy: S ≥ S_L always.
-/
noncomputable def linearEntropy (ρ : DensityOp n) : ℝ :=
  1 - ρ.purity

/-- Pure states have zero linear entropy.

This follows immediately from purity = 1 for pure states.
-/
theorem fromPure_linearEntropy (ψ : QuantumState (ℂ^n)) :
    (fromPure ψ).linearEntropy = 0 := by
  simp only [linearEntropy]
  have h : (fromPure ψ).purity = 1 := fromPure_isPure ψ
  rw [h]
  ring

/-!
=============================================================================================================
## Section 4: Maximally Mixed State
=============================================================================================================

The maximally mixed state ρ = I/n represents complete ignorance about
the quantum system. It is the unique state with:

  - Maximum von Neumann entropy: S = ln n
  - Minimum purity: γ = 1/n
  - Equal probability for all outcomes in any measurement basis
  - Invariance under all unitary transformations

Physical interpretations:
  - Thermal equilibrium at infinite temperature
  - Reduced state of maximally entangled bipartite state
  - Uniform classical mixture of any orthonormal basis
-/

/-- The maximally mixed state ρ = I/n on ℂⁿ.

This state represents complete ignorance about the quantum system.
All eigenvalues equal 1/n, giving:
  - Purity: γ = n · (1/n)² = 1/n (minimum possible)
  - Linear entropy: S_L = 1 - 1/n (maximum possible)
  - Von Neumann entropy: S = ln n (maximum possible)

Requires n ≠ 0 for the state to be well-defined.
-/
noncomputable def maximallyMixed (n : ℕ) (hn : n ≠ 0) : DensityOp n where
  op := (1 / n : ℂ) • ContinuousLinearMap.id ℂ (ℂ^n)

  hermitian := by
    have h1 : ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℂ (ℂ^n)) =
              ContinuousLinearMap.id ℂ (ℂ^n) := ContinuousLinearMap.adjoint_id
    have h2 : (1 / n : ℂ) = conj (1 / n : ℂ) := by simp
    calc ContinuousLinearMap.adjoint ((1 / n : ℂ) • ContinuousLinearMap.id ℂ (ℂ^n))
        = conj (1 / n : ℂ) • ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℂ (ℂ^n)) :=
          adjoint_smul (1 / n : ℂ) (ContinuousLinearMap.id ℂ (ℂ^n))
      _ = conj (1 / n : ℂ) • ContinuousLinearMap.id ℂ (ℂ^n) := by rw [h1]
      _ = (1 / n : ℂ) • ContinuousLinearMap.id ℂ (ℂ^n) := by rw [← h2]

  positive := fun ψ => by
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    rw [inner_smul_right (𝕜 := ℂ)]
    rw [inner_self_eq_norm_sq_to_K]
    show 0 ≤ ((1 / n : ℂ) * (‖ψ‖ : ℂ) ^ 2).re
    have h1 : (1 / n : ℂ) = (1 / n : ℝ) := by norm_num
    rw [h1]
    have h2 : ((1 / n : ℝ) : ℂ) * (‖ψ‖ : ℂ) ^ 2 = ((1 / n : ℝ) * ‖ψ‖ ^ 2 : ℝ) := by
      push_cast
      ring
    rw [h2]
    simp only [Complex.ofReal_re]
    apply mul_nonneg
    · apply div_nonneg
      · norm_num
      · exact Nat.cast_nonneg n
    · exact sq_nonneg _

  trace_one := by
    rw [trace_smul, trace_id]
    rw [one_div, inv_mul_cancel₀]
    exact Nat.cast_ne_zero.mpr hn

/-- The maximally mixed state has purity 1/n.

This is the minimum possible purity for an n-dimensional system.

Proof: Tr((I/n)²) = Tr(I/n²) = n/n² = 1/n.
-/
theorem maximallyMixed_purity (n : ℕ) (hn : n ≠ 0) :
    (maximallyMixed n hn).purity = 1 / n := by
  simp only [purity, maximallyMixed]
  have h1 : ((1 / n : ℂ) • ContinuousLinearMap.id ℂ (ℂ^n)).comp
            ((1 / n : ℂ) • ContinuousLinearMap.id ℂ (ℂ^n)) =
            (1 / n : ℂ)^2 • ContinuousLinearMap.id ℂ (ℂ^n) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
               ContinuousLinearMap.id_apply, smul_smul, sq]
  rw [h1]
  rw [trace_smul, trace_id]
  simp only [sq, one_div]
  have h2 : ((n : ℂ)⁻¹ * (n : ℂ)⁻¹ * n).re = (1 / n : ℝ) := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    norm_num
    simp_all only [ne_eq, one_div, ContinuousLinearMap.comp_smulₛₗ, map_inv₀,
                   map_natCast, ContinuousLinearMap.comp_id, inv_pow,
                   Nat.cast_eq_zero, not_false_eq_true, inv_mul_cancel_right₀]
  rw [h2]
  norm_num

/-- The maximally mixed state has linear entropy (n-1)/n.

This is the maximum possible linear entropy for an n-dimensional system.
-/
theorem maximallyMixed_linearEntropy (n : ℕ) (hn : n ≠ 0) :
    (maximallyMixed n hn).linearEntropy = (n - 1) / n := by
  simp only [linearEntropy, maximallyMixed_purity]
  field_simp

/-- Axiom: Eigenvalues exist for density operators with the expected properties.

This packages the spectral theorem for density operators into a single
existence statement. The eigenvalues form a probability distribution
(non-negative, sum to 1) and determine the purity.

AXIOMATIZED: Derivable from Matrix.IsHermitian.eigenvalues + bridging
-/
axiom eigenvalues_exist (ρ : DensityOp n) :
    ∃ (lambda_s : Fin n → ℝ),
      (∀ i, 0 ≤ lambda_s i) ∧
      (∀ i, lambda_s i ≤ 1) ∧
      (∑ i, lambda_s i = 1) ∧
      (ρ.purity = ∑ i, (lambda_s i)^2)

/-- Eigenvalues of a density operator.

Extracted from the existence axiom via Classical.choose.
-/
noncomputable def eigenvalues (ρ : DensityOp n) : Fin n → ℝ :=
  Classical.choose (eigenvalues_exist ρ)

/-- Eigenvalues are non-negative. -/
theorem eigenvalues_nonneg (ρ : DensityOp n) : ∀ i, 0 ≤ ρ.eigenvalues i :=
  (Classical.choose_spec (eigenvalues_exist ρ)).1

/-- Eigenvalues are at most 1. -/
theorem eigenvalues_le_one (ρ : DensityOp n) : ∀ i, ρ.eigenvalues i ≤ 1 :=
  (Classical.choose_spec (eigenvalues_exist ρ)).2.1

/-- Eigenvalues sum to 1. -/
theorem eigenvalues_sum_one (ρ : DensityOp n) : ∑ i : Fin n, ρ.eigenvalues i = 1 :=
  (Classical.choose_spec (eigenvalues_exist ρ)).2.2.1

/-- Purity equals sum of squared eigenvalues. -/
theorem purity_eq_sum_sq (ρ : DensityOp n) : ρ.purity = ∑ i : Fin n, (ρ.eigenvalues i)^2 :=
  (Classical.choose_spec (eigenvalues_exist ρ)).2.2.2

/-!
=============================================================================================================
## Section 5 Additions: Eigenvalues of Specific States
=============================================================================================================

To prove entropy bounds (S = 0 for pure, S = ln n for maximally mixed),
we need to know the eigenvalue structure of specific density operators.
-/

/-- A pure state |ψ⟩⟨ψ| has exactly one non-zero eigenvalue equal to 1.

Intuition: The projector |ψ⟩⟨ψ| maps everything onto span{|ψ⟩}, giving
eigenvalue 1 for |ψ⟩ and eigenvalue 0 for any orthogonal vector.

Consequences:
  - Purity = 1² + 0² + ... + 0² = 1 ✓
  - Entropy = -1·ln(1) - 0·ln(0) - ... = 0

AXIOMATIZED: Derivable from rank-1 projector spectral analysis
-/
axiom fromPure_eigenvalues (ψ : QuantumState (ℂ^n)) (hn : 0 < n) :
    ∃ i₀ : Fin n, (fromPure ψ).eigenvalues i₀ = 1 ∧
                  ∀ i, i ≠ i₀ → (fromPure ψ).eigenvalues i = 0

/-- The maximally mixed state I/n has all eigenvalues equal to 1/n.

Intuition: The identity matrix has all eigenvalues equal to 1, so
I/n has all eigenvalues equal to 1/n.

Consequences:
  - Purity = n · (1/n)² = 1/n ✓
  - Entropy = -n · (1/n)·ln(1/n) = ln(n)

AXIOMATIZED: Derivable from identity matrix spectral decomposition
-/
axiom maximallyMixed_eigenvalues (n : ℕ) (hn : n ≠ 0) :
    ∀ i : Fin n, (maximallyMixed n hn).eigenvalues i = 1 / n

/-- Sum of squared pure state eigenvalues equals 1.

Sanity check that fromPure_eigenvalues is consistent with purity_eq_sum_sq.
-/
theorem fromPure_eigenvalues_sq_sum (ψ : QuantumState (ℂ^n)) (hn : 0 < n) :
    ∑ i : Fin n, ((fromPure ψ).eigenvalues i)^2 = 1 := by
  obtain ⟨i₀, hi₀_one, hi₀_rest⟩ := fromPure_eigenvalues ψ hn
  calc ∑ i : Fin n, ((fromPure ψ).eigenvalues i)^2
      = (fromPure ψ).eigenvalues i₀ ^ 2 + ∑ i ∈ Finset.univ.erase i₀, ((fromPure ψ).eigenvalues i)^2 := by
        rw [← Finset.add_sum_erase Finset.univ (fun i => ((fromPure ψ).eigenvalues i)^2) (Finset.mem_univ i₀)]
    _ = 1^2 + ∑ i ∈ Finset.univ.erase i₀, 0^2 := by
        congr 1
        · rw [hi₀_one]
        · apply Finset.sum_congr rfl
          intro i hi
          rw [hi₀_rest i (Finset.ne_of_mem_erase hi)]
    _ = 1 := by norm_num

/-- Sum of squared maximally mixed eigenvalues equals 1/n.

Sanity check that maximallyMixed_eigenvalues is consistent with purity.
-/
theorem maximallyMixed_eigenvalues_sq_sum (n : ℕ) (hn : n ≠ 0) :
    ∑ i : Fin n, ((maximallyMixed n hn).eigenvalues i)^2 = 1 / n := by
  have h : ∀ i : Fin n, (maximallyMixed n hn).eigenvalues i = 1 / n :=
    maximallyMixed_eigenvalues n hn
  calc ∑ i : Fin n, ((maximallyMixed n hn).eigenvalues i)^2
      = ∑ i : Fin n, (1 / n : ℝ)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [h i]
    _ = Fintype.card (Fin n) • (1 / n : ℝ)^2 := by
        rw [Finset.sum_const, Finset.card_univ]
    _ = n • (1 / n : ℝ)^2 := by rw [Fintype.card_fin]
    _ = n * (1 / n)^2 := by rw [nsmul_eq_mul]
    _ = 1 / n := by
        field_simp



end DensityOp
end QState
