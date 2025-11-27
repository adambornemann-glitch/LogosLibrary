/-
Author: Adam Bornemann
Created: [10/24/2025]
Updates: [11/26/2025]
=============================================================================================================
HILBERT SPACES: MATHEMATICAL FOUNDATION FOR QUANTUM MECHANICS
=============================================================================================================

This file establishes the Hilbert space formalism as the mathematical arena
for quantum mechanics. We build on Mathlib's inner product space infrastructure
but add quantum-specific structures and conventions.

PHYSICAL MOTIVATION:
  Quantum states live in complex Hilbert spaces. The inner product gives:
    - Probability amplitudes: ⟨φ|ψ⟩
    - Transition probabilities: |⟨φ|ψ⟩|²
    - Observables as Hermitian operators
    - Dynamics via unitary evolution

  The Hilbert space axioms encode the superposition principle: if |ψ⟩ and |φ⟩
  are possible states, so is α|ψ⟩ + β|φ⟩. Complex coefficients allow interference.

HISTORICAL DEVELOPMENT:
  von Neumann (1927): Rigorous Hilbert space formulation of QM
  Dirac (1930): Bra-ket notation, delta functions
  Stone (1930): Spectral theorem for unbounded operators
  Gleason (1957): Derived Born rule from Hilbert space structure

CONNECTION TO OTHER WORK:
  - Feeds into: State.lean (density operators)
  - Feeds into: VonNeumann.lean (entropy)
  - Feeds into: Evolution/ (unitary dynamics)
  - Requires: Mathlib inner product spaces, functional analysis

MATHEMATICAL CONTENT:
  §1 Basic Hilbert space structure
  §2 Physics inner product convention
  §3 Quantum states (normalized vectors)
  §4 Orthonormal bases and Parseval
  §5 Finite-dimensional structure
  §6 Linear operators and adjoints
  §7 Hermitian operators (observables)
  §8 Unitary operators (dynamics)
  §9 Standard quantum systems (qubits, Pauli matrices)
  §10 Trace and outer products

CONVENTIONS:
  - Inner product CONJUGATE-LINEAR in first argument (physics convention)
  - Natural units: ℏ = 1
  - Finite-dimensional unless otherwise stated

Built on:
  - Mathlib.Analysis.InnerProductSpace (inner products, adjoints)
  - Mathlib.LinearAlgebra (finite-dimensional structure)

References:
  [1] von Neumann, "Mathematical Foundations of Quantum Mechanics" (1932)
  [2] Reed & Simon, "Functional Analysis" Vol I (1980)
  [3] Hall, "Quantum Theory for Mathematicians" (2013)
  [4] Nielsen & Chuang, "Quantum Computation and Quantum Information" (2000)
-/
/- Basic Imports -/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
/- Projection Imports -/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
/- Complex Imports-/
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.AbsMax

namespace QHilbert

open scoped InnerProductSpace TensorProduct ComplexConjugate
open Complex

/-!
================================================================================
SECTION 1: BASIC HILBERT SPACE STRUCTURE
================================================================================

A Hilbert space is a complete inner product space. For quantum mechanics:
  - Always over ℂ (complex numbers)
  - Inner product gives probability amplitudes
  - Completeness ensures limits of Cauchy sequences exist

We work primarily with FINITE-DIMENSIONAL spaces in this file.
Infinite-dimensional requires careful functional analysis (future work).
-/

/-- Type class for a quantum Hilbert space: complex inner product space -/
class QuantumHilbert (H : Type*) extends
    NormedAddCommGroup H,
    InnerProductSpace ℂ H where
  /-- For quantum mechanics, we typically want finite dimension or separability -/
  -- Additional structure can be added as needed

/- Any complex inner product space is a quantum Hilbert space -/
instance (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    QuantumHilbert H := {}

/-!
================================================================================
SECTION 2: PHYSICS INNER PRODUCT CONVENTION
================================================================================

CRITICAL: Mathlib vs Physics convention

Mathlib: ⟪x, y⟫_ℂ is LINEAR in x, CONJUGATE-LINEAR in y
Physics: ⟨x|y⟩ is CONJUGATE-LINEAR in x (bra), LINEAR in y (ket)

### Physics vs Mathlib Inner Product Convention

We define the physics bracket as:
  `⟨ψ|φ⟩ := ⟪φ, ψ⟫_ℂ`

This swaps the arguments from Mathlib's convention. The resulting linearity is:

| Argument | Mathlib `⟪x, y⟫` | Physics `⟨ψ\|φ⟩` |
|----------|------------------|------------------|
| First    | conj-linear      | linear           |
| Second   | linear           | conj-linear      |

Note: This differs from standard Dirac notation where the bra `⟨ψ|` acts as a
conjugate-linear functional. Here `⟨ψ|φ⟩` is linear in `ψ` and conjugate-linear
in `φ`. This choice simplifies compatibility with Mathlib's inner product space
infrastructure while preserving the essential structure:
  - `⟨ψ|ψ⟩ ≥ 0` (real, non-negative)
  - `⟨ψ|φ⟩ = conj ⟨φ|ψ⟩` (conjugate symmetry)
  - Cauchy-Schwarz: `‖⟨ψ|φ⟩‖ ≤ ‖ψ‖ * ‖φ‖`

A future refactor may introduce a separate bra type to recover standard Dirac
conjugate-linearity conventions.
-/


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Physics inner product: ⟨ψ|φ⟩ in Dirac notation.

Defined as ⟨ψ|φ⟩ := ⟪φ, ψ⟫_ℂ, swapping arguments from Mathlib's convention.

**Convention translation:**

| Property          | Mathlib ⟪x, y⟫    | Physics ⟨ψ|φ⟩     |
|-------------------|-------------------|-------------------|
| First argument    | linear            | linear            |
| Second argument   | conjugate-linear  | conjugate-linear  |

Note: Our definition makes ⟨ψ|φ⟩ linear in ψ and conjugate-linear in φ.
This differs from standard Dirac notation where ⟨ψ| is conjugate-linear.
The choice prioritizes compatibility with Mathlib while preserving the
essential structure (conjugate symmetry, positivity).

**Physical meaning:**

The inner product ⟨φ|ψ⟩ is the probability amplitude for finding state |φ⟩
when the system is in state |ψ⟩. The transition probability is |⟨φ|ψ⟩|².

**Key properties (proven below):**
  - ⟨ψ|ψ⟩ ≥ 0 with equality iff ψ = 0
  - ⟨ψ|φ⟩ = conj ⟨φ|ψ⟩ (conjugate symmetry)
  - ‖ψ‖² = Re⟨ψ|ψ⟩
  - |⟨ψ|φ⟩| ≤ ‖ψ‖‖φ‖ (Cauchy-Schwarz)
-/
noncomputable def braket (ψ φ : H) : ℂ := ⟪φ, ψ⟫_ℂ

/-- Notation: we use ⟨ψ|φ⟩ for physics inner product -/
notation "⟨" ψ "|" φ "⟩" => braket ψ φ

/-- Physics inner product is linear in the first argument.

For scalar α ∈ ℂ:
  ⟨αψ|φ⟩ = α⟨ψ|φ⟩

**Derivation:**

Since ⟨ψ|φ⟩ := ⟪φ, ψ⟫_ℂ and Mathlib's inner product is linear in the
second argument:
  ⟨αψ|φ⟩ = ⟪φ, αψ⟫_ℂ = α⟪φ, ψ⟫_ℂ = α⟨ψ|φ⟩

**Physical interpretation:**

Scaling a state |ψ⟩ → α|ψ⟩ scales all probability amplitudes by α.
For normalized states, |α| = 1 (pure phase), so probabilities |⟨φ|αψ⟩|²
are unchanged—confirming that global phase is unobservable.
-/
theorem braket_linear_left (α : ℂ) (ψ φ : H) :
    ⟨α • ψ|φ⟩ = α * ⟨ψ|φ⟩ := by
  simp only [braket]
  rw [inner_smul_right]


/-- Physics inner product is conjugate-linear in the second argument.

For scalar α ∈ ℂ:
  ⟨ψ|αφ⟩ = ᾱ⟨ψ|φ⟩

**Derivation:**

Since ⟨ψ|φ⟩ := ⟪φ, ψ⟫_ℂ and Mathlib's inner product is conjugate-linear
in the first argument:
  ⟨ψ|αφ⟩ = ⟪αφ, ψ⟫_ℂ = conj(α)⟪φ, ψ⟫_ℂ = ᾱ⟨ψ|φ⟩

**Physical interpretation:**

This ensures ⟨ψ|ψ⟩ is real: conjugate-linearity in one argument combined
with linearity in the other forces ⟨ψ|ψ⟩ = conj⟨ψ|ψ⟩, hence Im⟨ψ|ψ⟩ = 0.
Real self-inner-products are essential for interpreting ‖ψ‖² as probability.
-/
theorem braket_conj_linear_right (α : ℂ) (ψ φ : H) :
    ⟨ψ|α • φ⟩ = conj α * ⟨ψ|φ⟩ := by
  simp only [braket, inner_smul_left]


/-- Conjugate symmetry: ⟨ψ|φ⟩ = conj⟨φ|ψ⟩.

Swapping arguments conjugates the inner product.

**Proof:**

Direct from Mathlib's `inner_conj_symm` and the definition ⟨ψ|φ⟩ := ⟪φ, ψ⟫_ℂ.

**Physical meaning:**

Probability amplitudes satisfy |⟨ψ|φ⟩|² = |⟨φ|ψ⟩|². The transition probability
from |ψ⟩ to |φ⟩ equals the transition probability from |φ⟩ to |ψ⟩.

This is microscopic reversibility at the amplitude level—a reflection of
time-reversal symmetry in quantum mechanics.

**Algebraic consequence:**

Setting φ = ψ: ⟨ψ|ψ⟩ = conj⟨ψ|ψ⟩, forcing ⟨ψ|ψ⟩ ∈ ℝ.
Combined with positivity, this gives ⟨ψ|ψ⟩ ≥ 0.
-/
theorem braket_conj_symm (ψ φ : H) : ⟨ψ|φ⟩ = conj ⟨φ|ψ⟩ := by
  simp only [braket, inner_conj_symm]

/-- Self inner product has zero imaginary part.

For any vector ψ:
  Im⟨ψ|ψ⟩ = 0

**Proof:**

From conjugate symmetry: ⟨ψ|ψ⟩ = conj⟨ψ|ψ⟩. A complex number equal to
its conjugate has zero imaginary part.

**Physical necessity:**

The norm ‖ψ‖² = Re⟨ψ|ψ⟩ must be real to serve as a probability (or sum
of probabilities in the Born rule). If ⟨ψ|ψ⟩ had nonzero imaginary part,
the interpretation of |amplitude|² as probability would fail.

This is not a convention—it follows from the axioms of inner product spaces.
-/
theorem braket_self_real (ψ : H) : (⟨ψ|ψ⟩).im = 0 := by
  simp only [braket]
  exact @inner_self_im ℂ H _ _ _ ψ

/-- Self inner product is non-negative.

For any vector ψ:
  Re⟨ψ|ψ⟩ ≥ 0

**Proof:**

This is the positive-definiteness axiom of inner product spaces, inherited
from Mathlib's `inner_self_nonneg`.

**Physical meaning:**

Since ‖ψ‖² = Re⟨ψ|ψ⟩, non-negativity ensures norms (and hence probabilities)
are non-negative. This is the mathematical foundation for the probabilistic
interpretation of quantum mechanics.

**Stronger statement:**

Re⟨ψ|ψ⟩ = 0 iff ψ = 0 (proven in `braket_self_eq_zero`). Nonzero vectors
have strictly positive norm—there are no "null vectors" in a Hilbert space
(unlike indefinite inner product spaces in relativity).
-/
theorem braket_self_nonneg (ψ : H) : 0 ≤ (⟨ψ|ψ⟩).re := by
  simp only [braket]
  exact @inner_self_nonneg ℂ H _ _ _ (x := ψ)


/-- Self inner product vanishes iff the vector is zero.

  ⟨ψ|ψ⟩ = 0  ↔  ψ = 0

**Proof:**

(→) Positive-definiteness: ⟨ψ|ψ⟩ = 0 with ⟨ψ|ψ⟩ ≥ 0 forces ψ = 0.
(←) Direct calculation: ⟨0|0⟩ = 0.

**Physical interpretation:**

This is non-degeneracy of the inner product. Every nonzero vector has
positive norm, so every nonzero state is physically distinguishable from
the zero vector (which is not a valid quantum state).

**Contrast with pseudo-Hilbert spaces:**

In special relativity, the Minkowski inner product can give ⟨v|v⟩ = 0
for nonzero "null vectors." Quantum mechanics requires a positive-definite
inner product, excluding such degeneracies.
-/
theorem braket_self_eq_zero (ψ : H) : ⟨ψ|ψ⟩ = 0 ↔ ψ = 0 := by
  simp only [braket]
  constructor
  · intro h
    exact inner_self_eq_zero.mp h
  · intro h
    simp [h]



/-- Norm squared equals the real part of self inner product.

  ‖ψ‖² = Re⟨ψ|ψ⟩

**Proof:**

The norm in an inner product space is defined by ‖ψ‖² = Re⟪ψ, ψ⟫.
Since ⟨ψ|ψ⟩ = ⟪ψ, ψ⟫_ℂ (self inner products are symmetric under swap),
we have ‖ψ‖² = Re⟨ψ|ψ⟩.

**Why Re and not just ⟨ψ|ψ⟩?**

Although ⟨ψ|ψ⟩ is real (proven in `braket_self_real`), it's a complex
number with zero imaginary part. The explicit Re extracts the real
component for type consistency with ‖ψ‖² : ℝ.

**Physical content:**

This connects the algebraic inner product to the geometric norm:
  - ‖ψ‖ measures "length" of the state vector
  - For normalized states, ‖ψ‖ = 1
  - Born rule: probability = |⟨φ|ψ⟩|² = ‖projection‖²
-/
theorem norm_sq_eq_braket (ψ : H) : ‖ψ‖^2 = (⟨ψ|ψ⟩).re := by
  simp only [braket]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast



/-- Cauchy-Schwarz inequality in physics notation.

For any vectors ψ, φ:
  |⟨ψ|φ⟩| ≤ ‖ψ‖ · ‖φ‖

**Proof:**

Direct from Mathlib's `norm_inner_le_norm`, with argument order adjusted
for our convention.

**Physical meaning:**

The transition amplitude is bounded by the product of norms. For normalized
states (‖ψ‖ = ‖φ‖ = 1):
  |⟨ψ|φ⟩| ≤ 1

This ensures transition probabilities |⟨ψ|φ⟩|² ≤ 1, as required for
a valid probability interpretation.

**Equality condition:**

|⟨ψ|φ⟩| = ‖ψ‖ · ‖φ‖ iff ψ and φ are linearly dependent (parallel).
For normalized states, equality holds iff |ψ⟩ = e^{iθ}|φ⟩ for some phase θ.
Maximum overlap occurs for identical states (up to phase).

**Geometric interpretation:**

Cauchy-Schwarz says |cos θ| ≤ 1 where θ is the "angle" between vectors.
The inner product generalizes the dot product, and the inequality
reflects that projections cannot exceed the original length.
-/
theorem cauchy_schwarz (ψ φ : H) : ‖⟨ψ|φ⟩‖ ≤ ‖ψ‖ * ‖φ‖ := by
  simp only [braket]
  rw [mul_comm]
  exact norm_inner_le_norm (𝕜 := ℂ) φ ψ


/-!
================================================================================
SECTION 3: QUANTUM STATES
================================================================================

A quantum state is a normalized vector: ‖ψ‖ = 1

Physical interpretation:
  - |ψ⟩ and e^{iθ}|ψ⟩ represent the SAME physical state (global phase)
  - Probability to find state |φ⟩: P = |⟨φ|ψ⟩|²
  - Normalization ensures Σ P = 1
-/

/-- A quantum state is a unit vector in Hilbert space.

**Physical interpretation:**

A quantum state |ψ⟩ represents a complete description of a quantum system.
The normalization ‖ψ‖ = 1 ensures:
  - Total probability sums to 1: Σᵢ |⟨eᵢ|ψ⟩|² = 1
  - Transition probabilities are bounded: |⟨φ|ψ⟩|² ≤ 1

**Global phase ambiguity:**

The states |ψ⟩ and e^{iθ}|ψ⟩ are physically indistinguishable—they give
identical probabilities |⟨φ|e^{iθ}ψ⟩|² = |⟨φ|ψ⟩|². The true state space
is projective Hilbert space ℙH = (H \ {0})/~, where ψ ~ φ iff ψ = λφ.

We work with representatives (unit vectors) for computational convenience,
keeping in mind that physics lives in the quotient.

**Structure fields:**
  - `vec`: The underlying Hilbert space vector
  - `normalized`: Proof that ‖vec‖ = 1
-/
structure QuantumState (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  vec : H
  normalized : ‖vec‖ = 1


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Coercion to underlying vector -/
instance : Coe (QuantumState H) H := ⟨QuantumState.vec⟩


/-- A quantum state vector is nonzero.

For any quantum state ψ:
  ψ.vec ≠ 0

**Proof:**

If ψ.vec = 0, then ‖ψ.vec‖ = 0 ≠ 1, contradicting normalization.

**Physical meaning:**

The zero vector is not a valid quantum state. It would give zero probability
for every measurement outcome, violating probability normalization.

This is why quantum states live in projective space ℙH = (H \ {0})/~,
explicitly excluding the origin.
-/
theorem vec_ne_zero (ψ : QuantumState H) : ψ.vec ≠ 0 := by
  intro h
  have hn := ψ.normalized
  rw [h] at hn
  simp at hn



/-- Self inner product of a quantum state is 1.

For any quantum state ψ:
  ⟨ψ|ψ⟩ = 1

**Proof:**

Since ‖ψ‖ = 1 and ‖ψ‖² = Re⟨ψ|ψ⟩, we have Re⟨ψ|ψ⟩ = 1.
Since Im⟨ψ|ψ⟩ = 0 (from `braket_self_real`), we get ⟨ψ|ψ⟩ = 1 + 0i = 1.

**Physical meaning:**

This is the normalization condition. In any orthonormal basis {|eᵢ⟩}:
  ⟨ψ|ψ⟩ = Σᵢ |⟨eᵢ|ψ⟩|² = 1

The probabilities |⟨eᵢ|ψ⟩|² sum to 1, as required for a valid
probability distribution over measurement outcomes.
-/
theorem braket_self_one (ψ : QuantumState H) : ⟨ψ.vec|ψ.vec⟩ = 1 := by
  simp only [braket]
  rw [inner_self_eq_norm_sq_to_K]
  simp [ψ.normalized]



/-- Transition probability between quantum states.

For states ψ, φ:
  P(ψ → φ) = |⟨ψ|φ⟩|²

**Physical interpretation:**

This is the Born rule: the probability of finding state |φ⟩ when
measuring a system in state |ψ⟩ (in an appropriate basis containing |φ⟩).

Equivalently: if we prepare |ψ⟩ and perform a projective measurement
with |φ⟩ as one outcome, P(ψ → φ) is the probability of that outcome.

**Properties (proven below):**
  - 0 ≤ P(ψ → φ) ≤ 1
  - P(ψ → φ) = P(φ → ψ) (symmetry)
  - P(ψ → ψ) = 1 (certainty for identical states)
  - P(ψ → φ) = 0 iff ψ ⊥ φ (orthogonal states)
-/
noncomputable def transition_prob (ψ φ : QuantumState H) : ℝ :=
  Complex.normSq ⟨ψ.vec|φ.vec⟩



/-- Transition probability lies in [0, 1].

For any quantum states ψ, φ:
  0 ≤ P(ψ → φ) ≤ 1

**Proof:**

Lower bound: |z|² ≥ 0 for any complex z.

Upper bound: By Cauchy-Schwarz, |⟨ψ|φ⟩| ≤ ‖ψ‖ · ‖φ‖ = 1 · 1 = 1.
Squaring: |⟨ψ|φ⟩|² ≤ 1.

**Physical necessity:**

Probabilities must lie in [0, 1]. This theorem confirms that the Born
rule |⟨φ|ψ⟩|² produces valid probabilities, not arbitrary real numbers.

The bound is tight:
  - P = 0 for orthogonal states (|⟨ψ|φ⟩| = 0)
  - P = 1 for identical states up to phase (|⟨ψ|φ⟩| = 1)
-/
theorem transition_prob_range (ψ φ : QuantumState H) :
    0 ≤ transition_prob ψ φ ∧ transition_prob ψ φ ≤ 1 := by
  constructor
  · exact Complex.normSq_nonneg _
  · simp only [transition_prob]
    calc Complex.normSq ⟨ψ.vec|φ.vec⟩
        = ‖⟨ψ.vec|φ.vec⟩‖^2 := by rw [Complex.normSq_eq_norm_sq]
      _ ≤ (‖ψ.vec‖ * ‖φ.vec‖)^2 := by {
          apply sq_le_sq'
          · linarith [norm_nonneg ⟨ψ.vec|φ.vec⟩,
                      mul_nonneg (norm_nonneg ψ.vec) (norm_nonneg φ.vec)]
          · exact cauchy_schwarz ψ.vec φ.vec
        }
      _ = 1 := by rw [ψ.normalized, φ.normalized]; ring




/-- Transition probability is symmetric.

For any quantum states ψ, φ:
  P(ψ → φ) = P(φ → ψ)

**Proof:**

P(ψ → φ) = |⟨ψ|φ⟩|² = |conj⟨φ|ψ⟩|² = |⟨φ|ψ⟩|² = P(φ → ψ)

using conjugate symmetry and |conj z| = |z|.

**Physical meaning:**

The probability of transition from |ψ⟩ to |φ⟩ equals the reverse.
This is microscopic reversibility—a consequence of unitarity.

In scattering theory, this becomes detailed balance: the rate of
A → B equals the rate of B → A (at equal energies, summed over
internal degrees of freedom).

**Contrast with classical physics:**

Classical transition rates need not be symmetric (e.g., friction
converts kinetic energy to heat, but not vice versa). Quantum
mechanical reversibility is more fundamental.
-/
theorem transition_prob_symm (ψ φ : QuantumState H) :
    transition_prob ψ φ = transition_prob φ ψ := by
  simp only [transition_prob, braket]
  rw [← Complex.normSq_conj ⟪ψ.vec, φ.vec⟫_ℂ, ← inner_conj_symm (𝕜 := ℂ)]



/-- Construct a quantum state from a nonzero vector by normalizing.

Given ψ ≠ 0, produces the normalized state ψ/‖ψ‖.

**Mathematical content:**

  normalize(ψ) = (1/‖ψ‖) · ψ

with ‖normalize(ψ)‖ = 1 by construction.

**Physical interpretation:**

Any nonzero vector can be promoted to a valid quantum state by
normalization. The direction matters; the length doesn't.

This reflects the projective nature of quantum state space: |ψ⟩ and
λ|ψ⟩ (for λ ≠ 0) represent the same physical state. Normalization
picks a canonical representative with ‖ψ‖ = 1.

**Usage:**

When constructing states from linear combinations or operator actions,
normalize to obtain a valid quantum state:
  |ψ'⟩ = A|ψ⟩/‖A|ψ⟩‖
-/
noncomputable def normalize (ψ : H) (hψ : ψ ≠ 0) : QuantumState H where
  vec := (‖ψ‖⁻¹ : ℝ) • ψ
  normalized := by
    rw [norm_smul]
    simp only [norm_inv, Real.norm_eq_abs, abs_norm]
    rw [inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr hψ



/-- Two states represent the same physical state iff they differ by a phase.

  same_physical_state ψ φ  ↔  ∃ θ : ℝ, φ = e^{iθ} ψ

**Physical meaning:**

Global phase is unobservable. The states |ψ⟩ and e^{iθ}|ψ⟩ give identical:
  - Expectation values: ⟨e^{iθ}ψ|A|e^{iθ}ψ⟩ = ⟨ψ|A|ψ⟩
  - Transition probabilities: |⟨φ|e^{iθ}ψ⟩|² = |⟨φ|ψ⟩|²
  - Measurement statistics

The true state space is projective Hilbert space ℙH = H/~, where
this equivalence relation identifies phase-related vectors.

**Relative phase matters:**

For superpositions α|0⟩ + β|1⟩, the relative phase arg(β/α) is
observable through interference. Only the overall phase is arbitrary.

**Topological consequence:**

For a qubit, ℙH ≅ S² (Bloch sphere). The phase ambiguity quotients
out the U(1) fiber, leaving the physical 2-sphere of pure states.
-/
def same_physical_state (ψ φ : QuantumState H) : Prop :=
  ∃ θ : ℝ, φ.vec = Complex.exp (I * θ) • ψ.vec

/-- same_physical_state is an equivalence relation -/
theorem same_physical_state_refl (ψ : QuantumState H) :
    same_physical_state ψ ψ := ⟨0, by simp⟩

theorem same_physical_state_symm {ψ φ : QuantumState H} :
    same_physical_state ψ φ → same_physical_state φ ψ := by
  intro ⟨θ, h⟩
  use -θ
  rw [h]
  rw [smul_smul]
  simp
  -- ⊢ ψ.vec = (cexp (-(I * ↑θ)) * cexp (I * ↑θ)) • ψ.vec
  rw [← Complex.exp_add]
  simp

/-!
================================================================================
SECTION 4: ORTHONORMAL BASES
================================================================================

An orthonormal basis {|eᵢ⟩} satisfies:
  - Orthonormality: ⟨eᵢ|eⱼ⟩ = δᵢⱼ
  - Completeness: Σᵢ |eᵢ⟩⟨eᵢ| = I (resolution of identity)

For finite-dimensional H of dimension n:
  - Any state: |ψ⟩ = Σᵢ cᵢ|eᵢ⟩ where cᵢ = ⟨eᵢ|ψ⟩
  - Normalization: Σᵢ |cᵢ|² = 1
-/

variable {n : ℕ}

/-- Type alias for standard n-dimensional complex Hilbert space -/
scoped notation "ℂ^" n => EuclideanSpace ℂ (Fin n)

/-- The standard basis vector eᵢ for ℂⁿ.

The i-th standard basis vector has 1 in position i and 0 elsewhere:
  (eᵢ)ⱼ = δᵢⱼ

**Mathematical content:**

Uses Mathlib's `EuclideanSpace.single i 1`, which constructs the vector
with value 1 at index i and 0 elsewhere.

**Physical interpretation:**

For a quantum system with n distinguishable states (e.g., n energy levels),
the standard basis {|0⟩, |1⟩, ..., |n-1⟩} represents the computational or
energy eigenbasis.

Examples:
  - Qubit (n=2): |0⟩ = (1,0), |1⟩ = (0,1)
  - Qutrit (n=3): |0⟩ = (1,0,0), |1⟩ = (0,1,0), |2⟩ = (0,0,1)

**Role in the theory:**

Standard bases provide:
  - Concrete representation for abstract states
  - Matrix elements of operators: Aᵢⱼ = ⟨eᵢ|A|eⱼ⟩
  - Trace computation: Tr(A) = Σᵢ ⟨eᵢ|A|eᵢ⟩
  - Completeness relation: Σᵢ |eᵢ⟩⟨eᵢ| = I
-/
noncomputable def std_basis (n : ℕ) (i : Fin n) : ℂ^n := EuclideanSpace.single i 1



/-- The standard basis is orthonormal: ⟨eᵢ|eⱼ⟩ = δᵢⱼ.

For the standard basis vectors of ℂⁿ:
  ⟨eᵢ|eⱼ⟩ = 1 if i = j
  ⟨eᵢ|eⱼ⟩ = 0 if i ≠ j

**Proof:**

Direct calculation using `EuclideanSpace.inner_single_left` and the
definition of the single-entry vector.

**Physical meaning:**

Orthonormality encodes two properties:
  
1. *Orthogonality* (⟨eᵢ|eⱼ⟩ = 0 for i ≠ j): Distinct basis states are
   perfectly distinguishable. Measuring |eᵢ⟩ in the standard basis
   gives outcome i with certainty, never outcome j ≠ i.

2. *Normalization* (⟨eᵢ|eᵢ⟩ = 1): Each basis state is a valid quantum
   state with unit norm.

**Kronecker delta:**

The result ⟨eᵢ|eⱼ⟩ = δᵢⱼ is the defining property of an orthonormal basis.
Any orthonormal basis satisfies this; the standard basis is the canonical
choice aligned with coordinate indices.
-/
theorem std_basis_orthonormal (n : ℕ) :
    ∀ i j : Fin n, ⟨std_basis n i|std_basis n j⟩ = if i = j then 1 else 0 := by
  intro i j
  simp only [braket, std_basis]
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  simp only [map_one, one_mul, eq_comm (a := j)]



/-- Every vector expands in the standard basis.

For any ψ ∈ ℂⁿ:
  ψ = Σᵢ ⟨ψ|eᵢ⟩ · eᵢ

**Proof:**

The coefficient ⟨ψ|eᵢ⟩ equals ψᵢ (the i-th component of ψ). The sum
Σᵢ ψᵢ · eᵢ reconstructs ψ component by component.

**Physical interpretation:**

Any quantum state decomposes into a superposition of basis states:
  |ψ⟩ = Σᵢ cᵢ |eᵢ⟩  where cᵢ = ⟨ψ|eᵢ⟩

The coefficients cᵢ are probability amplitudes:
  - |cᵢ|² = probability of measuring outcome i
  - Σᵢ |cᵢ|² = 1 (normalization)

**Completeness relation:**

This expansion is equivalent to the resolution of identity:
  Σᵢ |eᵢ⟩⟨eᵢ| = I

Applying both sides to |ψ⟩: I|ψ⟩ = Σᵢ |eᵢ⟩⟨eᵢ|ψ⟩ = Σᵢ ⟨eᵢ|ψ⟩* |eᵢ⟩

Note: Our convention gives ⟨ψ|eᵢ⟩ rather than ⟨eᵢ|ψ⟩ as coefficients,
which differs from standard Dirac notation by conjugation.

**Uniqueness:**

The expansion is unique: if ψ = Σᵢ aᵢ eᵢ = Σᵢ bᵢ eᵢ, then aᵢ = bᵢ
for all i. This follows from orthonormality: apply ⟨eⱼ|· to both sides.
-/
theorem expand_std_basis (n : ℕ) (ψ : ℂ^n) :
    ψ = ∑ i : Fin n, ⟨ψ|std_basis n i⟩ • std_basis n i := by
  have h : ∀ i, ⟨ψ|std_basis n i⟩ = ψ i := fun i => by
    simp only [braket, std_basis]
    rw [EuclideanSpace.inner_single_left]
    simp
  simp_rw [h, std_basis]
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp [EuclideanSpace.single_apply]
  · intro i _ hij
    simp [EuclideanSpace.single_apply]
    intro hiej
    exact (hij hiej.symm).elim
  · intro hj
    exact (hj (Finset.mem_univ j)).elim



/-- Parseval's identity: ‖ψ‖² = Σᵢ |⟨eᵢ|ψ⟩|².

The squared norm equals the sum of squared amplitudes over any
orthonormal basis.

**Proof:**

‖ψ‖² = ⟨ψ|ψ⟩ = ⟨Σᵢ cᵢeᵢ | Σⱼ cⱼeⱼ⟩ = Σᵢⱼ c̄ᵢcⱼ⟨eᵢ|eⱼ⟩ = Σᵢⱼ c̄ᵢcⱼδᵢⱼ = Σᵢ |cᵢ|²

using orthonormality ⟨eᵢ|eⱼ⟩ = δᵢⱼ.

**Physical interpretation:**

For a normalized state (‖ψ‖ = 1):
  Σᵢ |⟨eᵢ|ψ⟩|² = 1

This is probability conservation: the probabilities of all measurement
outcomes sum to 1. Parseval's identity is the mathematical statement
underlying the Born rule's consistency.

**Generalization:**

Parseval holds for any orthonormal basis, not just the standard one.
The squared norm is basis-independent, even though individual
amplitudes ⟨eᵢ|ψ⟩ depend on the choice of basis.

**Connection to Fourier analysis:**

In L²(ℝ), Parseval becomes ∫|f(x)|²dx = Σₙ|f̂ₙ|² (Fourier coefficients).
The finite-dimensional version here is the discrete analogue.

**Energy interpretation:**

If {|eᵢ⟩} are energy eigenstates with energies Eᵢ, then |⟨eᵢ|ψ⟩|² is
the probability of measuring energy Eᵢ. Parseval ensures these
probabilities are properly normalized.
-/
theorem parseval (n : ℕ) (ψ : ℂ^n) :
    ‖ψ‖^2 = ∑ i : Fin n, Complex.normSq ⟨std_basis n i|ψ⟩ := by
  have h : ∀ i, ⟨std_basis n i|ψ⟩ = conj (ψ i) := fun i => by
    simp only [braket, std_basis]
    rw [EuclideanSpace.inner_single_right]
    simp
  simp_rw [h, Complex.normSq_conj]
  have hn : ‖ψ‖^2 = ∑ i : Fin n, ‖ψ i‖^2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  rw [hn]
  congr 1
  ext i
  rw [Complex.normSq_eq_norm_sq]

/-!
================================================================================
SECTION 5: FINITE-DIMENSIONAL STRUCTURE
================================================================================

For finite-dimensional quantum systems:
  - Dimension = number of distinguishable states
  - dim(H_A ⊗ H_B) = dim(H_A) × dim(H_B)
  - All operators are bounded

Examples:
  - Qubit: dim = 2 (spin-1/2, two-level atom, polarization)
  - Qutrit: dim = 3
  - n qubits: dim = 2ⁿ
-/

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Type class for finite-dimensional quantum systems.

A finite-dimensional quantum system has a Hilbert space with finite
dimension over ℂ.

**Physical examples:**

  - Qubit: dim = 2 (spin-1/2, photon polarization, two-level atom)
  - Qutrit: dim = 3 (spin-1, three-level system)
  - n qubits: dim = 2ⁿ (exponential growth → quantum advantage)
  - Spin-j particle: dim = 2j + 1

**Why finite dimension matters:**

  1. *All operators are bounded*: No domain issues, complete spectral theorem
  2. *Matrices suffice*: Operators ↔ n×n complex matrices
  3. *Compactness*: State space is compact (important for optimization)
  4. *Computability*: Algorithms can manipulate states explicitly

**Infinite-dimensional systems:**

Position/momentum of a particle require L²(ℝ), which is infinite-dimensional.
Unbounded operators (like position x̂) require careful domain specifications.
This file focuses on finite dimensions; infinite-dimensional extension is
future work.
-/
class FiniteDimQuantum (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  finite_dim : FiniteDimensional ℂ H

/-- Dimension of a finite-dimensional quantum Hilbert space.

Returns the dimension n = dim_ℂ(H) as a natural number.

**Mathematical content:**

Uses Mathlib's `Module.finrank`, which computes the dimension of a
finite-dimensional vector space over its base field.

**Physical interpretation:**

The dimension counts the maximum number of perfectly distinguishable
states. For dimension n:
  - n orthonormal states {|0⟩, ..., |n-1⟩} can be perfectly distinguished
  - Any n+1 states must have overlaps (cannot all be orthogonal)

**Information content:**

A system of dimension n can encode log₂(n) bits of classical information
(Holevo bound). Quantum mechanically, it can participate in log₂(n)
qubits worth of entanglement.

**Dimensional scaling:**

  - Single qubit: n = 2
  - k qubits: n = 2ᵏ
  - Composite systems: dim(H_A ⊗ H_B) = dim(H_A) × dim(H_B)
-/
noncomputable def qdim [FiniteDimensional ℂ H] : ℕ :=
  Module.finrank ℂ H


/-- Standard Hilbert spaces ℂⁿ are finite-dimensional.

The Euclidean space ℂⁿ = EuclideanSpace ℂ (Fin n) has finite dimension.

**Proof:**

Mathlib's `EuclideanSpace` is constructed to be finite-dimensional
over its base field, with dimension equal to the cardinality of the
index type (here Fin n, which has cardinality n).

**Role in the theory:**

This instance allows us to use all finite-dimensional machinery
(spectral theorem, trace, determinant) for the standard spaces ℂⁿ
that represent n-level quantum systems.
-/
instance (n : ℕ) : FiniteDimQuantum (ℂ^n) where
  finite_dim := inferInstance



/-- The dimension of ℂⁿ is n.

  qdim (ℂ^n) = n

**Proof:**

Direct from Mathlib's `finrank_euclideanSpace`, which computes the
dimension as the cardinality of the index type Fin n.

**Verification:**

This confirms our notation is consistent:
  - ℂ^2 (qubit) has dimension 2
  - ℂ^n (n-level system) has dimension n

**Physical meaning:**

An n-dimensional Hilbert space supports exactly n orthonormal basis
states. This is the "size" of the quantum system—how many classical
bits it takes to specify a basis state.
-/
theorem qdim_euclidean (n : ℕ) : qdim (ℂ^n) = n := by
  simp only [qdim, finrank_euclideanSpace, Fintype.card_fin]

/-!
================================================================================
SECTION 6: LINEAR OPERATORS
================================================================================

Observables and dynamics are represented by operators on H.

Key types:
  - Linear operators: A(α|ψ⟩ + β|φ⟩) = αA|ψ⟩ + βA|φ⟩
  - Bounded operators: ‖Aψ‖ ≤ C‖ψ‖ (automatic in finite dim)
  - Adjoint: ⟨ψ|A†φ⟩ = ⟨Aψ|φ⟩

For finite dimension, we can use matrices.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
         [FiniteDimensional ℂ H]


/-- Linear operator on a Hilbert space.

A linear operator A : H → H satisfies:
  A(αψ + βφ) = αA(ψ) + βA(φ)

**Physical role:**

Linear operators represent:
  - Observables (Hermitian operators): position, momentum, energy
  - Dynamics (unitary operators): time evolution, quantum gates
  - Measurements (projectors): state collapse
  - General transformations: quantum channels (via Kraus operators)

**Mathematical content:**

This is an abbreviation for `H →ₗ[ℂ] H`, Mathlib's type of ℂ-linear
maps from H to itself.

**Finite vs infinite dimension:**

In finite dimensions, all linear operators are automatically bounded
(continuous). In infinite dimensions, unbounded operators like
position and momentum require careful domain specifications.
-/
abbrev LinOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  H →ₗ[ℂ] H



/-- Bounded (continuous) linear operator on a Hilbert space.

A bounded operator A satisfies ‖Aψ‖ ≤ C‖ψ‖ for some constant C.

**Mathematical content:**

This is an abbreviation for `H →L[ℂ] H`, Mathlib's type of continuous
ℂ-linear maps. The `L` indicates continuity (bounded = continuous for
linear operators on normed spaces).

**Why boundedness matters:**

1. *Continuity*: Small changes in input → small changes in output
2. *Operator norm*: ‖A‖ = sup{‖Aψ‖ : ‖ψ‖ = 1} is finite
3. *Adjoint exists*: Bounded operators have bounded adjoints
4. *Composition*: Bounded operators form an algebra under composition

**Finite-dimensional automatic:**

For finite-dimensional H, every linear operator is bounded. The distinction
matters only in infinite dimensions (e.g., position operator on L²(ℝ)).
-/
abbrev BoundedOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  H →L[ℂ] H



/-- Convert a linear operator to a bounded operator (finite dimensions).

In finite dimensions, every linear operator is automatically bounded,
so this conversion is always valid.

**Mathematical content:**

Uses Mathlib's `LinearMap.toContinuousLinearMap`, which constructs
the continuous extension of a linear map when it exists (always in
finite dimensions).

**Proof that this works:**

Finite-dimensional normed spaces are complete, and linear maps between
finite-dimensional spaces are always continuous. This is a consequence
of all norms being equivalent in finite dimensions.

**Usage:**

When constructing operators via their linear action (e.g., matrix
multiplication), first define as `LinOp`, then convert to `BoundedOp`
for access to adjoint and other continuous-linear-map machinery.
-/
noncomputable def LinOp.toBounded (A : LinOp H) : BoundedOp H :=
  LinearMap.toContinuousLinearMap A



/-- Adjoint of a bounded operator.

The adjoint A† is defined by the relation:
  ⟨ψ|A†φ⟩ = ⟨Aψ|φ⟩  for all ψ, φ

**Mathematical content:**

Uses Mathlib's `ContinuousLinearMap.adjoint`, which constructs the
unique operator satisfying the adjoint relation via the Riesz
representation theorem.

**Physical interpretation:**

The adjoint transforms bras: if A transforms kets |ψ⟩ → A|ψ⟩, then
A† transforms bras ⟨ψ| → ⟨ψ|A†.

In matrix representation (choosing a basis): (A†)ᵢⱼ = Āⱼᵢ (conjugate
transpose).

**Key properties (proven below):**
  - (A†)† = A (involutive)
  - (AB)† = B†A† (reverses order)
  - (A + B)† = A† + B†
  - (αA)† = ᾱA†

**Physical role:**

  - Hermitian: A† = A → real eigenvalues (observables)
  - Unitary: A†A = I → preserves norm (dynamics)
  - Normal: A†A = AA† → spectral theorem applies
-/
noncomputable def adjoint (A : BoundedOp H) : BoundedOp H :=
  ContinuousLinearMap.adjoint A

/-- Notation for adjoint -/
postfix:max "†" => adjoint


/-- Defining property of the adjoint in physics notation.

For any bounded operator A and vectors ψ, φ:
  ⟨ψ|A†φ⟩ = ⟨Aψ|φ⟩

**Proof:**

Direct from Mathlib's `ContinuousLinearMap.adjoint_inner_left`, with
argument order adjusted for our braket convention.

**Physical meaning:**

The adjoint "moves across" the inner product. This is the abstract
characterization that doesn't depend on matrix representation.

**Mnemonic:**

"A† acts on the right slot" or equivalently "A acts on the left slot."
The dagger moves the operator from one side of the inner product to
the other.

**Derivation of matrix formula:**

Taking ψ = eᵢ, φ = eⱼ in an orthonormal basis:
  (A†)ᵢⱼ = ⟨eᵢ|A†eⱼ⟩ = ⟨Aeᵢ|eⱼ⟩ = conj⟨eⱼ|Aeᵢ⟩ = conj(Aⱼᵢ) = Āⱼᵢ

So A† is the conjugate transpose in matrix form.
-/
theorem adjoint_def (A : BoundedOp H) (ψ φ : H) :
    ⟨ψ|A† φ⟩ = ⟨A ψ|φ⟩ := by
  simp only [braket, adjoint]
  rw [ContinuousLinearMap.adjoint_inner_left]



/-- The adjoint is involutive: (A†)† = A.

Taking the adjoint twice recovers the original operator.

**Proof:**

Direct from Mathlib's `ContinuousLinearMap.adjoint_adjoint`.

**Physical meaning:**

Dagger is an involution on the space of operators. Combined with
anti-linearity ((αA)† = ᾱA†) and anti-multiplicativity ((AB)† = B†A†),
the adjoint defines a *-algebra structure.

**Matrix interpretation:**

(A†)† = (Ā^T)† = (Ā^T)^T̄ = A

Conjugate transpose twice returns to the original matrix.

**Role in classification:**

Operators satisfying A† = A (Hermitian) or A†A = I (unitary) are
special because the involution acts simply on them.
-/
theorem adjoint_adjoint (A : BoundedOp H) : A†† = A :=
  ContinuousLinearMap.adjoint_adjoint A



/-- Adjoint reverses composition: (AB)† = B†A†.

The adjoint of a product is the reversed product of adjoints.

**Proof:**

Direct from Mathlib's `ContinuousLinearMap.adjoint_comp`.

**Physical meaning:**

Order reversal under adjoint reflects that:
  ⟨ψ|(AB)†φ⟩ = ⟨ABψ|φ⟩ = ⟨Bψ|A†φ⟩ = ⟨ψ|B†A†φ⟩

The operators "peel off" from inside the bra in reverse order.

**Matrix interpretation:**

(AB)† = (AB)^T̄ = B^T̄ A^T̄ = B†A†

Transpose reverses matrix multiplication order, and conjugation
distributes.

**Consequence for unitaries:**

If U is unitary (U†U = I), then:
  (U†)†(U†) = U · U† = I (also unitary)
  
The adjoint of a unitary is also unitary.
-/
theorem adjoint_comp (A B : BoundedOp H) : (A.comp B)† = B†.comp A† :=
  ContinuousLinearMap.adjoint_comp A B



/-- Adjoint distributes over addition: (A + B)† = A† + B†.

The adjoint is additive.

**Proof:**

Direct from Mathlib's `ContinuousLinearMap.adjoint.map_add`.

**Physical meaning:**

⟨ψ|(A+B)†φ⟩ = ⟨(A+B)ψ|φ⟩ = ⟨Aψ|φ⟩ + ⟨Bψ|φ⟩ = ⟨ψ|A†φ⟩ + ⟨ψ|B†φ⟩ = ⟨ψ|(A†+B†)φ⟩

Additivity of inner product transfers to additivity of adjoint.

**Algebraic structure:**

Together with (αA)† = ᾱA† and (AB)† = B†A†, this makes † a
conjugate-linear anti-homomorphism of the operator algebra—the
defining property of a *-algebra involution.
-/
theorem adjoint_add (A B : BoundedOp H) : (A + B)† = A† + B† := by
  simp only [adjoint]
  exact ContinuousLinearMap.adjoint.map_add A B



/-- Adjoint is conjugate-linear in scalars: (αA)† = ᾱA†.

Scalar multiplication conjugates under the adjoint.

**Proof:**

Direct calculation using Mathlib's adjoint and star operations.

**Physical meaning:**

⟨ψ|(αA)†φ⟩ = ⟨αAψ|φ⟩ = ᾱ⟨Aψ|φ⟩ = ᾱ⟨ψ|A†φ⟩ = ⟨ψ|ᾱA†φ⟩

The conjugation arises from conjugate-linearity of the inner product
in its first argument.

**Contrast with linearity:**

The adjoint map A ↦ A† is conjugate-linear (anti-linear), not linear:
  (αA)† = ᾱA† ≠ αA† in general

This is because † involves complex conjugation intrinsically.

**Real scalars:**

For r ∈ ℝ: (rA)† = r̄A† = rA† (real scalars pass through unchanged).
-/
theorem adjoint_smul (α : ℂ) (A : BoundedOp H) : (α • A)† = conj α • A† := by
  ext x; simp only [adjoint, ContinuousLinearMap.smul_apply]
  rw [← ContinuousLinearMap.star_eq_adjoint]
  simp; rw [← ContinuousLinearMap.star_eq_adjoint]

/-!
================================================================================
SECTION 7: HERMITIAN AND UNITARY OPERATORS
================================================================================

Hermitian (Self-adjoint): A† = A
  - Real eigenvalues
  - Orthogonal eigenvectors
  - Physical observables

Unitary: U†U = UU† = I
  - Preserves inner product: ⟨Uψ|Uφ⟩ = ⟨ψ|φ⟩
  - Time evolution
  - Quantum gates
-/

/-- Hermitian (self-adjoint) operator: A† = A.

**Physical interpretation:**

Hermitian operators represent physical observables—quantities that
can be measured. The self-adjointness condition A† = A ensures:

1. *Real eigenvalues*: Measured values are real numbers
2. *Orthogonal eigenvectors*: Distinct outcomes are distinguishable
3. *Spectral decomposition*: A = Σᵢ λᵢ|eᵢ⟩⟨eᵢ| with real λᵢ
4. *Real expectation values*: ⟨ψ|A|ψ⟩ ∈ ℝ

**Examples:**

  - Position: x̂ (in infinite dimensions)
  - Momentum: p̂ = -iℏ∇
  - Hamiltonian: H = p²/2m + V(x)
  - Pauli matrices: σₓ, σᵧ, σᵤ
  - Projectors: P = |ψ⟩⟨ψ| (for normalized |ψ⟩)

**Mathematical structure:**

Hermitian operators form a real vector space (closed under real
scalar multiplication and addition) but not a complex one (iA is
anti-Hermitian if A is Hermitian).

**Structure fields:**
  - `op`: The underlying bounded operator
  - `self_adjoint`: Proof that op† = op
-/
structure HermitianOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] where
  op : BoundedOp H
  self_adjoint : op† = op

namespace HermitianOp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
         [FiniteDimensional ℂ H]

/-- Coercion to bounded operator -/
instance : Coe (HermitianOp H) (BoundedOp H) := ⟨HermitianOp.op⟩

/-- Hermitian operators have real expectation values.

For any Hermitian operator A and vector ψ:
  Im⟨ψ|Aψ⟩ = 0

**Proof:**

⟨ψ|Aψ⟩ = ⟨ψ|A†ψ⟩ = ⟨Aψ|ψ⟩ = conj⟨ψ|Aψ⟩

A complex number equal to its conjugate is real.

**Physical meaning:**

The expectation value ⟨A⟩_ψ = ⟨ψ|A|ψ⟩ is the average measurement outcome
when observable A is measured on state |ψ⟩. Being real is physically
necessary—measured values are real numbers.

**Stronger statement:**

Not only is the expectation real, but all eigenvalues are real
(proven in `eigenvalue_real`). The expectation is a weighted average
of real eigenvalues with non-negative weights |⟨eᵢ|ψ⟩|².

**Contrast with non-Hermitian operators:**

For non-Hermitian A, ⟨ψ|Aψ⟩ can be complex. Such operators don't
represent physical observables (though they appear in effective
theories, e.g., non-Hermitian Hamiltonians for open systems).
-/
theorem expectation_real (A : HermitianOp H) (ψ : H) :
    (⟨ψ|A.op ψ⟩).im = 0 := by
  simp only [braket]
  have h : ⟪A.op ψ, ψ⟫_ℂ = conj ⟪A.op ψ, ψ⟫_ℂ := by
    calc ⟪A.op ψ, ψ⟫_ℂ
        = ⟪ψ, A.op† ψ⟫_ℂ := (ContinuousLinearMap.adjoint_inner_right A.op ψ ψ).symm
      _ = ⟪ψ, A.op ψ⟫_ℂ := by rw [A.self_adjoint]
      _ = conj ⟪A.op ψ, ψ⟫_ℂ := (inner_conj_symm ψ (A.op ψ)).symm
  have him : (⟪A.op ψ, ψ⟫_ℂ).im = -(⟪A.op ψ, ψ⟫_ℂ).im := by
    conv_lhs => rw [h, Complex.conj_im]
  linarith



/-- Eigenvalues of Hermitian operators are real.

If A is Hermitian and Aψ = λψ with ψ ≠ 0, then λ ∈ ℝ (i.e., Im(λ) = 0).

**Proof:**

From Aψ = λψ:
  λ⟨ψ|ψ⟩ = ⟨ψ|λψ⟩ = ⟨ψ|Aψ⟩

Since ⟨ψ|Aψ⟩ is real (from `expectation_real`) and ⟨ψ|ψ⟩ > 0 (since ψ ≠ 0),
we have λ = ⟨ψ|Aψ⟩/⟨ψ|ψ⟩ ∈ ℝ.

**Physical meaning:**

Eigenvalues of an observable are the possible measurement outcomes.
Since measurements yield real numbers, eigenvalues must be real.

This is not imposed by fiat—it follows mathematically from A† = A.
The physics (real measurements) and mathematics (self-adjointness)
are perfectly aligned.

**Contrast with unitary operators:**

Unitary operators have eigenvalues on the unit circle: |λ| = 1 but
λ can be complex (e.g., λ = e^{iθ}). These don't represent observables.

**Spectral theorem preview:**

Every Hermitian operator on finite-dimensional H has n real eigenvalues
(counting multiplicity) and can be written A = Σᵢ λᵢPᵢ where Pᵢ are
orthogonal projectors.
-/
theorem eigenvalue_real (A : HermitianOp H) (lambda : ℂ) (ψ : H) (hψ : ψ ≠ 0)
    (h_eigen : A.op ψ = lambda • ψ) : lambda.im = 0 := by
  have hreal := expectation_real A ψ
  have h1 : ⟨ψ|A.op ψ⟩ = conj lambda * ⟨ψ|ψ⟩ := by
    rw [h_eigen]
    exact braket_conj_linear_right lambda ψ ψ
  have hψψ_real : (⟨ψ|ψ⟩).im = 0 := braket_self_real ψ
  have hψψ_nonneg := braket_self_nonneg ψ
  have hψψ_ne : ⟨ψ|ψ⟩ ≠ 0 := fun h => hψ ((braket_self_eq_zero ψ).mp h)
  have hpos : (⟨ψ|ψ⟩).re > 0 := by
    cases' (lt_or_eq_of_le hψψ_nonneg) with h h
    · exact h
    · exfalso
      apply hψψ_ne
      apply Complex.ext
      · exact h.symm
      · exact hψψ_real
  rw [h1] at hreal
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, hψψ_real, mul_zero, neg_mul] at hreal
  have hmul : lambda.im * (⟨ψ|ψ⟩).re = 0 := by linarith
  rcases mul_eq_zero.mp hmul with h | h
  · exact h
  · linarith



/-- Eigenvectors of a Hermitian operator for distinct eigenvalues are orthogonal.

If Aψ₁ = λ₁ψ₁ and Aψ₂ = λ₂ψ₂ with λ₁ ≠ λ₂, then ⟨ψ₁|ψ₂⟩ = 0.

**Proof:**

λ₁⟨ψ₁|ψ₂⟩ = ⟨Aψ₁|ψ₂⟩ = ⟨ψ₁|A†ψ₂⟩ = ⟨ψ₁|Aψ₂⟩ = λ₂⟨ψ₁|ψ₂⟩

(using A† = A and reality of λ₂ so that conj λ₂ = λ₂)

Thus (λ₁ - λ₂)⟨ψ₁|ψ₂⟩ = 0. Since λ₁ ≠ λ₂, we have ⟨ψ₁|ψ₂⟩ = 0.

**Physical meaning:**

States corresponding to different measurement outcomes are orthogonal,
hence perfectly distinguishable. If you measure observable A and get
result λ₁, there is zero probability of finding the system in an
eigenstate of λ₂.

This is the mathematical foundation for quantum measurement:
  - Different outcomes → orthogonal states
  - Orthogonal states → perfectly distinguishable
  - Perfect distinguishability → no ambiguity in measurement

**Degeneracy:**

If λ₁ = λ₂ (degenerate eigenvalue), eigenvectors need not be orthogonal.
However, within a degenerate eigenspace, one can always choose an
orthonormal basis (Gram-Schmidt).

**Building orthonormal eigenbasis:**

Combining non-degenerate orthogonality with Gram-Schmidt for degenerate
subspaces, every Hermitian operator has a complete orthonormal eigenbasis.
This is the finite-dimensional spectral theorem.
-/
theorem eigenvectors_orthogonal (A : HermitianOp H)
    (lambda₁ lambda₂ : ℂ) (ψ₁ ψ₂ : H)
    (h₁ : A.op ψ₁ = lambda₁ • ψ₁) (h₂ : A.op ψ₂ = lambda₂ • ψ₂)
    (hlambda : lambda₁ ≠ lambda₂) : ⟨ψ₁|ψ₂⟩ = 0 := by
  by_cases hψ₂ : ψ₂ = 0
  · simp [braket, hψ₂]
  have h_lambda₂_real : lambda₂.im = 0 := eigenvalue_real A lambda₂ ψ₂ hψ₂ h₂
  have hconj_lambda₂ : conj lambda₂ = lambda₂ := Complex.conj_eq_iff_im.mpr h_lambda₂_real
  have eq1 : lambda₁ * ⟨ψ₁|ψ₂⟩ = ⟨A.op ψ₁|ψ₂⟩ := by
    rw [h₁, braket_linear_left]
  have eq2 : ⟨A.op ψ₁|ψ₂⟩ = ⟨ψ₁|A.op ψ₂⟩ := by
    rw [← A.self_adjoint]
    rw [adjoint_def]
    rw [self_adjoint]
  have eq3 : ⟨ψ₁|A.op ψ₂⟩ = lambda₂ * ⟨ψ₁|ψ₂⟩ := by
    rw [h₂, braket_conj_linear_right, hconj_lambda₂]
  have eq4 : lambda₁ * ⟨ψ₁|ψ₂⟩ = lambda₂ * ⟨ψ₁|ψ₂⟩ := by
    calc lambda₁ * ⟨ψ₁|ψ₂⟩ = ⟨A.op ψ₁|ψ₂⟩ := eq1
      _ = ⟨ψ₁|A.op ψ₂⟩ := eq2
      _ = lambda₂ * ⟨ψ₁|ψ₂⟩ := eq3
  have eq5 : (lambda₁ - lambda₂) * ⟨ψ₁|ψ₂⟩ = 0 := by
    calc (lambda₁ - lambda₂) * ⟨ψ₁|ψ₂⟩
        = lambda₁ * ⟨ψ₁|ψ₂⟩ - lambda₂ * ⟨ψ₁|ψ₂⟩ := by ring
      _ = 0 := by rw [eq4]; ring
  rcases mul_eq_zero.mp eq5 with hdiff | hbrak
  · exfalso; apply hlambda; exact sub_eq_zero.mp hdiff
  · exact hbrak



/-- The zero operator is Hermitian.

0† = 0 trivially.

**Proof:**

The adjoint of zero is zero.

**Physical interpretation:**

The zero observable always yields expectation value 0. Not physically
interesting, but algebraically necessary for the Hermitian operators
to form a vector space.
-/
def zero : HermitianOp H where
  op := 0
  self_adjoint := by simp [adjoint]



/-- The identity operator is Hermitian.

I† = I since ⟨ψ|Iφ⟩ = ⟨ψ|φ⟩ = ⟨Iψ|φ⟩.

**Proof:**

The adjoint of the identity is the identity.

**Physical interpretation:**

The identity represents the "trivial observable" that returns 1 for
every state. More usefully, I appears in:
  - Completeness: Σᵢ|eᵢ⟩⟨eᵢ| = I
  - Unitarity: U†U = I
  - Normalization: Tr(ρ) = Tr(ρ·I) = 1

**Eigenvalues:**

Every vector is an eigenvector of I with eigenvalue 1.
The spectrum is {1} with multiplicity = dim(H).
-/
def one : HermitianOp H where
  op := ContinuousLinearMap.id ℂ H
  self_adjoint := by
    ext x
    simp [adjoint]




/-- Sum of Hermitian operators is Hermitian.

If A† = A and B† = B, then (A + B)† = A† + B† = A + B.

**Proof:**

Additivity of adjoint + both operators being self-adjoint.

**Physical interpretation:**

Combined observables remain observables. If A and B are measurable
quantities, so is A + B.

Example: Total angular momentum J = L + S is Hermitian because both
orbital (L) and spin (S) angular momentum are Hermitian.

**Algebraic structure:**

This shows Hermitian operators are closed under addition, forming
an additive subgroup of all operators.
-/
def add (A B : HermitianOp H) : HermitianOp H where
  op := A.op + B.op
  self_adjoint := by
    rw [adjoint_add, A.self_adjoint, B.self_adjoint]



/-- Real scalar multiple of a Hermitian operator is Hermitian.

For r ∈ ℝ and Hermitian A: (rA)† = r̄A† = rA† = rA.

**Proof:**

Real numbers are self-conjugate: r̄ = r.

**Physical interpretation:**

Scaling an observable by a real number gives another observable.
Example: 2H (twice the Hamiltonian) is Hermitian if H is.

**Contrast with complex scalars:**

For complex α with Im(α) ≠ 0: (αA)† = ᾱA ≠ αA in general.
In particular, iA is anti-Hermitian ((iA)† = -iA) if A is Hermitian.

**Algebraic structure:**

Hermitian operators form a real vector space, not a complex one.
Closure under real scalar multiplication + addition makes them a
real subspace of the complex operator algebra.
-/
def smul_real (r : ℝ) (A : HermitianOp H) : HermitianOp H where
  op := (r : ℂ) • A.op
  self_adjoint := by
    rw [adjoint_smul, A.self_adjoint]
    simp [Complex.conj_ofReal]

end HermitianOp

/-- Unitary operator: U†U = I.

**Physical interpretation:**

Unitary operators represent reversible quantum dynamics:

1. *Time evolution*: |ψ(t)⟩ = U(t)|ψ(0)⟩ where U(t) = e^{-iHt/ℏ}
2. *Quantum gates*: Hadamard, CNOT, phase gates
3. *Symmetry transformations*: Rotations, translations, parity

The condition U†U = I ensures:
  - Norm preservation: ‖Uψ‖ = ‖ψ‖
  - Inner product preservation: ⟨Uψ|Uφ⟩ = ⟨ψ|φ⟩
  - Probability conservation: |⟨φ|Uψ⟩|² sums to 1

**Mathematical properties:**

  - Invertible: U⁻¹ = U†
  - Eigenvalues on unit circle: |λ| = 1
  - Form a group: U(n) for n×n unitaries
  - det(U) ∈ S¹ (for SU(n), det(U) = 1)

**Contrast with Hermitian:**

  - Hermitian: A† = A, eigenvalues real (observables)
  - Unitary: U†U = I, eigenvalues unit modulus (dynamics)
  - Connection: U = e^{iA} is unitary iff A is Hermitian

**Structure fields:**
  - `op`: The underlying bounded operator
  - `unitary`: Proof that op†.comp op = id
-/
structure UnitaryOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] where
  op : BoundedOp H
  unitary : op†.comp op = ContinuousLinearMap.id ℂ H

namespace UnitaryOp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
         [FiniteDimensional ℂ H]

/-- Coercion to bounded operator -/
instance : Coe (UnitaryOp H) (BoundedOp H) := ⟨UnitaryOp.op⟩

/-- Unitary operators preserve inner products.

For any unitary U and vectors ψ, φ:
  ⟨Uψ|Uφ⟩ = ⟨ψ|φ⟩

**Proof:**

⟨Uψ|Uφ⟩ = ⟨ψ|U†(Uφ)⟩ = ⟨ψ|(U†U)φ⟩ = ⟨ψ|Iφ⟩ = ⟨ψ|φ⟩

using the adjoint definition and U†U = I.

**Physical meaning:**

Unitary evolution preserves all probability amplitudes, not just norms.
This is stronger than norm preservation—it means unitary transformations
preserve the full geometry of Hilbert space.

**Consequences:**

1. *Distinguishability preserved*: Orthogonal states remain orthogonal
   ⟨ψ|φ⟩ = 0 → ⟨Uψ|Uφ⟩ = 0
   
2. *Transition probabilities preserved*: |⟨Uψ|Uφ⟩|² = |⟨ψ|φ⟩|²

3. *No information loss*: U is bijective (invertible)

**Characterization:**

An operator is unitary iff it preserves the inner product. This is
Wigner's theorem (for symmetries) in finite dimensions.
-/
theorem preserves_inner (U : UnitaryOp H) (ψ φ : H) :
    ⟨U.op ψ|U.op φ⟩ = ⟨ψ|φ⟩ := by
  calc ⟨U.op ψ|U.op φ⟩
      = ⟨ψ|U.op† (U.op φ)⟩ := by rw [adjoint_def]
    _ = ⟨ψ|(U.op†.comp U.op) φ⟩ := rfl
    _ = ⟨ψ|(ContinuousLinearMap.id ℂ H) φ⟩ := by rw [U.unitary]
    _ = ⟨ψ|φ⟩ := by simp



/-- Unitary operators preserve norms.

For any unitary U and vector ψ:
  ‖Uψ‖ = ‖ψ‖

**Proof:**

‖Uψ‖² = Re⟨Uψ|Uψ⟩ = Re⟨ψ|ψ⟩ = ‖ψ‖²

Taking square roots (both sides non-negative).

**Physical meaning:**

Unitary evolution preserves the norm of quantum states. Since we
work with normalized states (‖ψ‖ = 1), applying any unitary U
yields another normalized state.

This is probability conservation: if |ψ⟩ is a valid state (probabilities
sum to 1), then U|ψ⟩ is also valid.

**Consequence for measurements:**

Before measurement: Σᵢ |⟨eᵢ|ψ⟩|² = 1
After unitary U: Σᵢ |⟨eᵢ|Uψ⟩|² = ‖Uψ‖² = ‖ψ‖² = 1

Probabilities remain normalized after any unitary transformation.

**Isometry:**

Norm preservation makes U an isometry (distance-preserving map).
In finite dimensions, isometries are automatically surjective, so
U is a bijection.
-/
theorem preserves_norm (U : UnitaryOp H) (ψ : H) :
    ‖U.op ψ‖ = ‖ψ‖ := by
  have h : ‖U.op ψ‖^2 = ‖ψ‖^2 := by
    calc ‖U.op ψ‖^2
        = (⟨U.op ψ|U.op ψ⟩).re := norm_sq_eq_braket (U.op ψ)
      _ = (⟨ψ|ψ⟩).re := by rw [preserves_inner U ψ ψ]
      _ = ‖ψ‖^2 := (norm_sq_eq_braket ψ).symm
  have hn1 : 0 ≤ ‖U.op ψ‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖ψ‖ := norm_nonneg _
  rw [← Real.sqrt_sq hn1, ← Real.sqrt_sq hn2, h]



/-- Unitary operators satisfy UU† = I (right inverse = left inverse).

If U†U = I, then also UU† = I.

**Proof:**

In finite dimensions, a left inverse is also a right inverse.
The proof uses:
1. U†U = I implies U is injective
2. Injective linear map on finite-dim space is surjective
3. Surjectivity + left inverse → right inverse

**Physical meaning:**

U and U† are mutual inverses: U⁻¹ = U†. Time evolution forward by t
is reversed by the adjoint (backward by t):
  U(t)† = e^{+iHt/ℏ} = U(-t)

**Why this matters:**

Some definitions of unitary require both U†U = I and UU† = I.
In finite dimensions, one implies the other. In infinite dimensions,
this can fail (isometries need not be unitaries).

**Group structure:**

With UU† = U†U = I, unitaries form a group under composition:
  - Identity: I is unitary
  - Inverses: U⁻¹ = U† is unitary
  - Closure: UV is unitary if U, V are (shown in `mul`)
-/
theorem unitary_right (U : UnitaryOp H) :
    U.op.comp U.op† = ContinuousLinearMap.id ℂ H := by
  have h := U.unitary
  have hinj : Function.Injective U.op := by
    intro x y hxy
    have : U.op† (U.op x) = U.op† (U.op y) := by rw [hxy]
    simp only [← ContinuousLinearMap.comp_apply, h, ContinuousLinearMap.id_apply] at this
    exact this
  have hsurj : Function.Surjective U.op := by
    exact LinearMap.surjective_of_injective hinj
  ext x
  obtain ⟨y, hy⟩ := hsurj x
  calc (U.op.comp U.op†) x
      = U.op (U.op† x) := rfl
    _ = U.op (U.op† (U.op y)) := by rw [hy]
    _ = U.op ((U.op†.comp U.op) y) := rfl
    _ = U.op ((ContinuousLinearMap.id ℂ H) y) := by rw [h]
    _ = U.op y := by simp
    _ = x := hy



/-- The identity operator is unitary.

I†I = I·I = I ✓

**Proof:**

The identity is self-adjoint and its square is itself.

**Physical interpretation:**

The identity represents "do nothing" evolution—the trivial dynamics
where the state is unchanged. Every quantum system admits this as
the t = 0 time evolution.

**Role in group structure:**

The identity is the neutral element of the unitary group U(n).
-/
def one : UnitaryOp H where
  op := ContinuousLinearMap.id ℂ H
  unitary := by simp [adjoint]



/-- Product of unitary operators is unitary.

If U†U = I and V†V = I, then (UV)†(UV) = V†U†UV = V†IV = V†V = I.

**Proof:**

Uses (UV)† = V†U† and associativity of composition.

**Physical interpretation:**

Sequential unitary operations compose to give a unitary operation.
If U represents evolution for time t₁ and V for time t₂, then UV
represents evolution for time t₁ + t₂ (in appropriate sense).

**Quantum circuits:**

Quantum gates compose: applying Hadamard then CNOT is equivalent to
a single unitary (their product). Circuit depth = number of sequential
gate layers.

**Group structure:**

This is closure under multiplication for the unitary group U(n).
Combined with identity (`one`) and inverse (`inv`), unitaries form
a group.
-/
def mul (U V : UnitaryOp H) : UnitaryOp H where
  op := U.op.comp V.op
  unitary := by
    rw [adjoint_comp]
    calc (V.op†.comp U.op†).comp (U.op.comp V.op)
        = V.op†.comp (U.op†.comp (U.op.comp V.op)) := by rw [ContinuousLinearMap.comp_assoc]
      _ = V.op†.comp ((U.op†.comp U.op).comp V.op) := by rw [ContinuousLinearMap.comp_assoc]
      _ = V.op†.comp ((ContinuousLinearMap.id ℂ H).comp V.op) := by rw [U.unitary]
      _ = V.op†.comp V.op := by rw [ContinuousLinearMap.id_comp]
      _ = ContinuousLinearMap.id ℂ H := V.unitary



/-- Inverse of a unitary operator is its adjoint.

U⁻¹ = U† since U†U = I.

**Proof:**

We need to show (U†)†(U†) = I. Using adjoint_adjoint: U(U†) = I,
which is `unitary_right`.

**Physical interpretation:**

To reverse a unitary transformation, apply its adjoint. For time
evolution U(t) = e^{-iHt}, the reverse is U(-t) = e^{+iHt} = U(t)†.

This is time-reversal symmetry at the dynamical level: quantum
evolution is fundamentally reversible (until measurement).

**Contrast with classical irreversibility:**

Classically, friction and entropy increase make many processes
irreversible. Quantum mechanically, all unitary evolution is
reversible. Irreversibility enters only through:
  - Measurement (wavefunction collapse)
  - Decoherence (entanglement with environment)
  - Coarse-graining (tracing over degrees of freedom)
-/
noncomputable def inv (U : UnitaryOp H) : UnitaryOp H where
  op := U.op†
  unitary := by
    rw [adjoint_adjoint]
    exact U.unitary_right



/-- Eigenvalues of unitary operators have unit modulus.

If U is unitary and Uψ = λψ with ψ ≠ 0, then |λ| = 1.

**Proof:**

‖ψ‖ = ‖Uψ‖ = ‖λψ‖ = |λ| · ‖ψ‖

Since ψ ≠ 0, we have ‖ψ‖ ≠ 0, so |λ| = 1.

**Physical meaning:**

Unitary eigenvalues lie on the unit circle: λ = e^{iθ} for some θ ∈ ℝ.
This reflects that unitaries preserve norm—scaling by |λ| ≠ 1 would
change the norm.

**Time evolution interpretation:**

For U = e^{-iHt/ℏ} with H|n⟩ = Eₙ|n⟩:
  U|n⟩ = e^{-iEₙt/ℏ}|n⟩

The eigenvalue e^{-iEₙt/ℏ} has |e^{-iEₙt/ℏ}| = 1. Energy eigenstates
acquire phases but don't change in norm.

**Contrast with Hermitian:**

  - Hermitian: eigenvalues real, on the real line
  - Unitary: eigenvalues unit modulus, on the unit circle
  
Connection: U = e^{iA} maps real eigenvalues of A to unit circle
eigenvalues of U via λ_U = e^{iλ_A}.
-/
theorem eigenvalue_unit_modulus (U : UnitaryOp H) (lambda : ℂ) (ψ : H) (hψ : ψ ≠ 0)
    (h_lambda : U.op ψ = lambda • ψ) : ‖lambda‖ = 1 := by
  have h1 : ‖U.op ψ‖ = ‖ψ‖ := preserves_norm U ψ
  have h2 : ‖U.op ψ‖ = ‖lambda‖ * ‖ψ‖ := by
    rw [h_lambda, norm_smul]
  have h3 : ‖ψ‖ = ‖lambda‖ * ‖ψ‖ := by
    calc ‖ψ‖ = ‖U.op ψ‖ := h1.symm
      _ = ‖lambda‖ * ‖ψ‖ := h2
  have hψ_norm : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  calc ‖lambda‖ = ‖lambda‖ * 1 := by ring
    _ = ‖lambda‖ * (‖ψ‖ / ‖ψ‖) := by rw [div_self hψ_norm]
    _ = (‖lambda‖ * ‖ψ‖) / ‖ψ‖ := by ring
    _ = ‖ψ‖ / ‖ψ‖ := by rw [← h3]
    _ = 1 := div_self hψ_norm

end UnitaryOp


/-!
================================================================================
SECTION 8: STANDARD QUANTUM SYSTEMS
================================================================================

Common quantum systems with standard structure.
-/
/-- Type alias for standard n-dimensional complex Hilbert space -/
scoped notation "ℂ^[2]" => EuclideanSpace ℂ (Fin 2)

/-- Standard qubit basis vector.

Uses the standard basis for ℂ²:
  qubit_basis 0 = |0⟩ = (1, 0)
  qubit_basis 1 = |1⟩ = (0, 1)

**Physical interpretation:**

The computational basis for a qubit, representing two orthogonal
states of a two-level system:
  - Spin-1/2: |0⟩ = |↑⟩, |1⟩ = |↓⟩
  - Photon polarization: |0⟩ = |H⟩, |1⟩ = |V⟩
  - Two-level atom: |0⟩ = |ground⟩, |1⟩ = |excited⟩
-/
noncomputable def qubit_basis (i : Fin 2) : ℂ^[2] := std_basis 2 i



/-- Type alias for qubit Hilbert space.

A qubit is the fundamental unit of quantum information: a two-dimensional
complex Hilbert space.

**Information content:**

  - Classical bit: 0 or 1 (2 states)
  - Qubit: α|0⟩ + β|1⟩ with |α|² + |β|² = 1 (continuous family)

A qubit can be in superposition of 0 and 1, enabling quantum parallelism
and interference—the basis of quantum computational advantage.

**Bloch sphere:**

Pure qubit states correspond to points on the Bloch sphere S².
The north/south poles are |0⟩/|1⟩; the equator contains superpositions
like |+⟩, |−⟩, |+i⟩, |−i⟩.
-/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- Computational basis state |0⟩ for a qubit.

  |0⟩ = (1, 0) ∈ ℂ²

**Physical interpretations:**

  - Spin-1/2: spin up along z-axis
  - Polarization: horizontal
  - Energy: ground state

**Measurement:**

Measuring in computational basis yields 0 with certainty for |0⟩.
-/
noncomputable def qubit_0 : Qubit := qubit_basis 0

/-- Computational basis state |1⟩ for a qubit.

  |1⟩ = (0, 1) ∈ ℂ²

**Physical interpretations:**

  - Spin-1/2: spin down along z-axis
  - Polarization: vertical
  - Energy: excited state

**Orthogonality:**

⟨0|1⟩ = 0, so |0⟩ and |1⟩ are perfectly distinguishable.
-/
noncomputable def qubit_1 : Qubit := qubit_basis 1


/-- Plus state: |+⟩ = (|0⟩ + |1⟩)/√2.

Equal superposition of |0⟩ and |1⟩.

**Physical interpretation:**

  - Spin-1/2: spin up along x-axis
  - Polarization: diagonal (45°)

**Measurement:**

  - In Z-basis (computational): 50% |0⟩, 50% |1⟩
  - In X-basis: 100% |+⟩

**Role in quantum computing:**

The Hadamard gate maps |0⟩ → |+⟩, creating the superposition needed
for quantum parallelism.
-/
noncomputable def qubit_plus : Qubit :=
  (1 / Real.sqrt 2 : ℂ) • (qubit_0 + qubit_1)



/-- Minus state: |−⟩ = (|0⟩ − |1⟩)/√2.

Superposition with relative phase π between |0⟩ and |1⟩.

**Physical interpretation:**

  - Spin-1/2: spin down along x-axis
  - Polarization: anti-diagonal (−45°)

**Orthogonality:**

⟨+|−⟩ = 0, so |+⟩ and |−⟩ form an orthonormal basis (X-basis).

**Interference:**

|+⟩ and |−⟩ differ only by relative phase, yet are orthogonal.
This illustrates that relative phase is physically meaningful,
unlike global phase.
-/
noncomputable def qubit_minus : Qubit :=
  (1 / Real.sqrt 2 : ℂ) • (qubit_0 - qubit_1)



/-- Pauli X matrix (NOT gate, bit flip).

  σₓ = |0⟩⟨1| + |1⟩⟨0| = [[0, 1], [1, 0]]

Action: X|0⟩ = |1⟩, X|1⟩ = |0⟩

**Physical interpretation:**

  - Spin-1/2: 180° rotation about x-axis
  - Quantum NOT: flips computational basis states
  - Pauli algebra: σₓ² = I, σₓσᵧ = iσᵤ

**Properties:**
  - Hermitian: X† = X (proven in `pauli_X_hermitian`)
  - Unitary: X†X = I (follows from X² = I)
  - Eigenvalues: ±1 with eigenvectors |±⟩

**Classical analogue:**

The only reversible classical 1-bit gate is NOT. Pauli X is its
quantum generalization, but acts linearly on superpositions.
-/
noncomputable def pauli_X : BoundedOp Qubit :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => (fun i => if i = 0 then v 1 else v 0)
    map_add' := by intros; ext i; fin_cases i <;> simp
    map_smul' := by intros; ext i; fin_cases i <;> simp
  }


/-- Pauli Y matrix (bit and phase flip).

  σᵧ = −i|0⟩⟨1| + i|1⟩⟨0| = [[0, −i], [i, 0]]

Action: Y|0⟩ = i|1⟩, Y|1⟩ = −i|0⟩

**Physical interpretation:**

  - Spin-1/2: 180° rotation about y-axis
  - Combines bit flip and phase flip: Y = iXZ

**Properties:**
  - Hermitian: Y† = Y (proven in `pauli_Y_hermitian`)
  - Unitary: Y†Y = I
  - Eigenvalues: ±1 with eigenvectors |±i⟩ = (|0⟩ ± i|1⟩)/√2

**Pauli algebra:**

  σᵧ² = I
  σᵧσᵤ = iσₓ
  σᵤσᵧ = −iσₓ
-/
noncomputable def pauli_Y : BoundedOp Qubit :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => (fun i => if i = 0 then -Complex.I * v 1 else Complex.I * v 0)
    map_add' := by intros; ext i; fin_cases i <;> simp [mul_add]
    map_smul' := by intros; ext i; fin_cases i <;> simp <;> ring
  }


/-- Pauli Z matrix (phase flip).

  σᵤ = |0⟩⟨0| − |1⟩⟨1| = [[1, 0], [0, −1]]

Action: Z|0⟩ = |0⟩, Z|1⟩ = −|1⟩

**Physical interpretation:**

  - Spin-1/2: 180° rotation about z-axis
  - Phase flip: changes sign of |1⟩ component

**Properties:**
  - Hermitian: Z† = Z (proven in `pauli_Z_hermitian`)
  - Unitary: Z†Z = I
  - Eigenvalues: ±1 with eigenvectors |0⟩, |1⟩

**Diagonal in computational basis:**

Z is diagonal in the computational basis, making it easy to implement.
Z|+⟩ = |−⟩: maps between X-basis eigenstates.
-/
noncomputable def pauli_Z : BoundedOp Qubit :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => (fun i => if i = 0 then v 0 else -v 1)
    map_add' := by intros; ext i; fin_cases i <;> simp; ring
    map_smul' := by intros; ext i; fin_cases i <;> simp
  }


/-- Hadamard gate.

  H = (1/√2)[[1, 1], [1, −1]]

Action: H|0⟩ = |+⟩, H|1⟩ = |−⟩

**Physical interpretation:**

Creates/destroys superposition:
  - |0⟩ → (|0⟩ + |1⟩)/√2 (creates superposition)
  - |+⟩ → |0⟩ (destroys superposition)

H² = I, so Hadamard is its own inverse.

**Role in quantum computing:**

The Hadamard gate is essential for:
  1. Creating initial superpositions for quantum parallelism
  2. Basis changes (Z-basis ↔ X-basis)
  3. Interference in quantum algorithms (Deutsch-Jozsa, Grover)

**Properties:**
  - Hermitian: H† = H (self-inverse)
  - Unitary: H†H = I (proven in `hadamard_unitary`)
  - H = (X + Z)/√2 (linear combination of Paulis)
-/
noncomputable def hadamard : BoundedOp Qubit :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => (fun i => if i = 0
                                then (1 / Real.sqrt 2 : ℂ) * (v 0 + v 1)
                                else (1 / Real.sqrt 2 : ℂ) * (v 0 - v 1))
    map_add' := by intros; ext i; fin_cases i <;> simp <;> ring
    map_smul' := by intros; ext i; fin_cases i <;> simp <;> ring
  }



/-- Pauli X is Hermitian: X† = X.

**Proof:**

Direct verification that ⟨Xψ|φ⟩ = ⟨ψ|Xφ⟩ for all ψ, φ ∈ ℂ².

**Physical meaning:**

X represents an observable—the spin component along the x-axis.
Its eigenvalues ±1 correspond to spin up/down along x.

**Consequence:**

X can be measured. The measurement outcomes are ±1, and the eigenstates
|+⟩, |−⟩ are the states with definite x-spin.
-/
theorem pauli_X_hermitian : pauli_X† = pauli_X := by
  have h : ∀ x y : Qubit, ⟪pauli_X x, y⟫_ℂ = ⟪x, pauli_X y⟫_ℂ := fun x y => by
    simp only [pauli_X, EuclideanSpace.inner_eq_star_dotProduct]
    simp; ring
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right (𝕜 := ℂ)
  intro y
  calc ⟪pauli_X† x, y⟫_ℂ
      = ⟪x, pauli_X y⟫_ℂ := ContinuousLinearMap.adjoint_inner_left pauli_X y x
    _ = ⟪pauli_X x, y⟫_ℂ := (h x y).symm



/-- Pauli Y is Hermitian: Y† = Y.

**Proof:**

Direct verification that ⟨Yψ|φ⟩ = ⟨ψ|Yφ⟩ for all ψ, φ ∈ ℂ².

**Physical meaning:**

Y represents the spin component along the y-axis.
Eigenvalues ±1 correspond to spin up/down along y.
-/
theorem pauli_Y_hermitian : pauli_Y† = pauli_Y := by
  have h : ∀ x y : Qubit, ⟪pauli_Y x, y⟫_ℂ = ⟪x, pauli_Y y⟫_ℂ := fun x y => by
    simp only [pauli_Y, EuclideanSpace.inner_eq_star_dotProduct]
    simp; ring
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right (𝕜 := ℂ)
  intro y
  calc ⟪pauli_Y† x, y⟫_ℂ
      = ⟪x, pauli_Y y⟫_ℂ := ContinuousLinearMap.adjoint_inner_left pauli_Y y x
    _ = ⟪pauli_Y x, y⟫_ℂ := (h x y).symm


/-- Pauli Z is Hermitian: Z† = Z.

**Proof:**

Direct verification that ⟨Zψ|φ⟩ = ⟨ψ|Zφ⟩ for all ψ, φ ∈ ℂ².

**Physical meaning:**

Z represents the spin component along the z-axis.
Eigenvalues ±1 with eigenstates |0⟩, |1⟩.
-/
theorem pauli_Z_hermitian : pauli_Z† = pauli_Z := by
  have h : ∀ x y : Qubit, ⟪pauli_Z x, y⟫_ℂ = ⟪x, pauli_Z y⟫_ℂ := fun x y => by
    simp only [pauli_Z, EuclideanSpace.inner_eq_star_dotProduct]
    simp
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right (𝕜 := ℂ)
  intro y
  calc ⟪pauli_Z† x, y⟫_ℂ
      = ⟪x, pauli_Z y⟫_ℂ := ContinuousLinearMap.adjoint_inner_left pauli_Z y x
    _ = ⟪pauli_Z x, y⟫_ℂ := (h x y).symm

/-- Pauli X squares to identity: X² = I.

**Proof:**

Direct calculation: X(X|ψ⟩) = X|ψ'⟩ = |ψ⟩ for all basis states.

**Physical meaning:**

Two bit flips return to the original state. This makes X:
  - Involutive: X⁻¹ = X
  - Its own square root of identity

**Eigenvalue constraint:**

Since X² = I, eigenvalues λ satisfy λ² = 1, so λ = ±1.
-/
theorem pauli_X_sq : pauli_X.comp pauli_X = ContinuousLinearMap.id ℂ Qubit := by
  ext x i
  simp only [pauli_X, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  fin_cases i <;> simp

/-- Pauli Y squares to identity: Y² = I.

**Proof:**

Direct calculation using i² = −1.

**Physical meaning:**

Y is also involutive. Note Y = iXZ, so Y² = (iXZ)² = i²X²Z² = (−1)·I·I = −I...
but actually Y² = I due to the specific phase structure.
-/
theorem pauli_Y_sq : pauli_Y.comp pauli_Y = ContinuousLinearMap.id ℂ Qubit := by
  ext x i
  simp only [pauli_Y, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  fin_cases i <;> simp <;> rw [← mul_assoc, Complex.I_mul_I] <;> ring

/-- Pauli Z squares to identity: Z² = I.

**Proof:**

Z is diagonal with entries ±1, so Z² has entries (±1)² = 1.

**Physical meaning:**

Two phase flips cancel. Z² = I makes Z involutive.
-/
theorem pauli_Z_sq : pauli_Z.comp pauli_Z = ContinuousLinearMap.id ℂ Qubit := by
  ext x i
  simp only [pauli_Z, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  fin_cases i <;> simp


/-- Hadamard gate is unitary: H†H = I.

**Proof:**

H is Hermitian (H† = H), so H†H = H². Direct calculation shows
H² = I using (1/√2)² = 1/2 and the specific matrix structure.

**Physical meaning:**

Hadamard evolution is reversible. Since H = H†, applying Hadamard
twice returns to the original state.

**Key identity:**

(1/√2)² + (1/√2)² = 1/2 + 1/2 = 1

This normalization ensures unitarity.
-/
theorem hadamard_unitary : hadamard†.comp hadamard = ContinuousLinearMap.id ℂ Qubit := by
  have hH : hadamard† = hadamard := by
    have h : ∀ x y : Qubit, ⟪hadamard x, y⟫_ℂ = ⟪x, hadamard y⟫_ℂ := fun x y => by
      simp only [hadamard, EuclideanSpace.inner_eq_star_dotProduct]
      simp; ring
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right (𝕜 := ℂ)
    intro y
    calc ⟪hadamard† x, y⟫_ℂ
        = ⟪x, hadamard y⟫_ℂ := ContinuousLinearMap.adjoint_inner_left hadamard y x
      _ = ⟪hadamard x, y⟫_ℂ := (h x y).symm
  rw [hH]
  ext x i
  simp only [hadamard, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  have hsq : (1 / Real.sqrt 2 : ℂ) * (1 / Real.sqrt 2 : ℂ) = 1 / 2 := by
    rw [one_div, one_div, ← sq, inv_pow, ← Complex.ofReal_pow,
        Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
    simp
  fin_cases i
  · simp only [Fin.isValue]
    calc (1 / Real.sqrt 2 : ℂ) * ((1 / Real.sqrt 2 : ℂ) * (x 0 + x 1) + (1 / Real.sqrt 2 : ℂ) * (x 0 - x 1))
        = (1 / Real.sqrt 2 : ℂ) * (1 / Real.sqrt 2 : ℂ) * ((x 0 + x 1) + (x 0 - x 1)) := by ring
      _ = (1 / 2) * ((x 0 + x 1) + (x 0 - x 1)) := by rw [hsq]
      _ = x 0 := by ring
  · simp only [Fin.isValue]
    calc (1 / Real.sqrt 2 : ℂ) * ((1 / Real.sqrt 2 : ℂ) * (x 0 + x 1) - (1 / Real.sqrt 2 : ℂ) * (x 0 - x 1))
        = (1 / Real.sqrt 2 : ℂ) * (1 / Real.sqrt 2 : ℂ) * ((x 0 + x 1) - (x 0 - x 1)) := by ring
      _ = (1 / 2) * ((x 0 + x 1) - (x 0 - x 1)) := by rw [hsq]
      _ = x 1 := by ring

/-!
================================================================================
SECTION 9: TRACE FOR FINITE-DIMENSIONAL OPERATORS
================================================================================

For finite-dimensional H, the trace is:
  Tr(A) = Σᵢ ⟨eᵢ|A eᵢ⟩

for any orthonormal basis {eᵢ}. Key properties:
  - Tr(αA + βB) = αTr(A) + βTr(B)  (linear)
  - Tr(AB) = Tr(BA)                 (cyclic)
  - Tr(A†) = conj(Tr(A))
  - Tr(|ψ⟩⟨φ|) = ⟨φ|ψ⟩
-/

/-- Trace of an operator on ℂⁿ.

  Tr(A) = Σᵢ ⟨eᵢ|Aeᵢ⟩

where {eᵢ} is the standard basis.

**Mathematical content:**

The trace is the sum of diagonal matrix elements. It equals the sum
of eigenvalues (counting multiplicity).

**Physical role:**

  - Expectation values: ⟨A⟩_ρ = Tr(ρA) for density matrix ρ
  - Normalization: Tr(ρ) = 1 for density matrices
  - Partial trace: Tr_B(ρ_AB) gives reduced density matrix

**Key properties (proven below):**
  - Tr(A + B) = Tr(A) + Tr(B) (linear)
  - Tr(αA) = αTr(A)
  - Tr(AB) = Tr(BA) (cyclic)
  - Tr(A†) = conj(Tr(A))
  - Tr(|ψ⟩⟨φ|) = ⟨φ|ψ⟩

**Basis independence:**

The trace is independent of the choice of orthonormal basis—this
follows from cyclicity and unitary change of basis.
-/
noncomputable def trace (n : ℕ) (A : BoundedOp (ℂ^n)) : ℂ :=
  ∑ i : Fin n, ⟪std_basis n i, A (std_basis n i)⟫_ℂ


/-- Trace is additive: Tr(A + B) = Tr(A) + Tr(B).

**Proof:**

Tr(A + B) = Σᵢ ⟨eᵢ|(A+B)eᵢ⟩ = Σᵢ (⟨eᵢ|Aeᵢ⟩ + ⟨eᵢ|Beᵢ⟩) = Tr(A) + Tr(B)

using linearity of inner product and commutativity of finite sums.

**Physical meaning:**

The expectation value of A + B equals the sum of individual expectations.
This is linearity of quantum mechanical expectation values.
-/
theorem trace_add (n : ℕ) (A B : BoundedOp (ℂ^n)) :
    trace n (A + B) = trace n A + trace n B := by
  simp only [trace]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext i
  simp [ContinuousLinearMap.add_apply, inner_add_right]


/-- Trace is homogeneous: Tr(αA) = αTr(A).

**Proof:**

Tr(αA) = Σᵢ ⟨eᵢ|(αA)eᵢ⟩ = Σᵢ α⟨eᵢ|Aeᵢ⟩ = α Σᵢ ⟨eᵢ|Aeᵢ⟩ = αTr(A)

using linearity of inner product in the second argument.

**Physical meaning:**

Scaling an observable by α scales all expectation values by α.
-/
theorem trace_smul (n : ℕ) (α : ℂ) (A : BoundedOp (ℂ^n)) :
    trace n (α • A) = α * trace n A := by
  simp only [trace]
  rw [Finset.mul_sum]
  congr 1
  ext i
  simp [ContinuousLinearMap.smul_apply, inner_smul_right]


/-- Trace of identity is the dimension: Tr(I) = n.

**Proof:**

Tr(I) = Σᵢ ⟨eᵢ|Ieᵢ⟩ = Σᵢ ⟨eᵢ|eᵢ⟩ = Σᵢ 1 = n

**Physical meaning:**

The trace counts dimensions. For a density matrix ρ on ℂⁿ:
  Tr(ρ) = 1 (normalization)
  Tr(ρ²) ≤ 1 (purity, equality for pure states)
  Tr(ρI) = Tr(ρ) = 1

**Maximally mixed state:**

ρ = I/n has Tr(ρ) = Tr(I)/n = n/n = 1 ✓
-/
theorem trace_id (n : ℕ) :
    trace n (ContinuousLinearMap.id ℂ (ℂ^n)) = n := by
  simp only [trace, ContinuousLinearMap.id_apply]
  have h : ∀ i : Fin n, ⟪std_basis n i, std_basis n i⟫_ℂ = 1 := fun i => by
    have := std_basis_orthonormal n i i
    simp only [braket] at this
    simp [this]
  simp_rw [h]
  simp


/-- Trace of adjoint is conjugate of trace: Tr(A†) = conj(Tr(A)).

**Proof:**

Tr(A†) = Σᵢ ⟨eᵢ|A†eᵢ⟩ = Σᵢ ⟨Aeᵢ|eᵢ⟩ = Σᵢ conj⟨eᵢ|Aeᵢ⟩ = conj(Tr(A))

using the adjoint definition and conjugate symmetry.

**Consequence for Hermitian operators:**

If A† = A, then Tr(A) = Tr(A†) = conj(Tr(A)), so Tr(A) ∈ ℝ.
(Proven directly in `trace_hermitian_real`.)
-/
theorem trace_adjoint (n : ℕ) (A : BoundedOp (ℂ^n)) :
    trace n A† = conj (trace n A) := by
  simp only [trace, map_sum]
  congr 1
  ext i
  simp only [adjoint]
  calc ⟪std_basis n i, ContinuousLinearMap.adjoint A (std_basis n i)⟫_ℂ
      = ⟪A (std_basis n i), std_basis n i⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_right A (std_basis n i) (std_basis n i)
    _ = conj ⟪std_basis n i, A (std_basis n i)⟫_ℂ :=
        (inner_conj_symm (A (std_basis n i)) (std_basis n i)).symm


/-- Trace of Hermitian operator is real.

For A with A† = A:
  Im(Tr(A)) = 0

**Proof:**

From Tr(A) = Tr(A†) = conj(Tr(A)). A complex number equal to its
conjugate is real.

**Physical meaning:**

The trace of an observable is real. For density matrix ρ:
  ⟨A⟩ = Tr(ρA)

If A is Hermitian and ρ is positive, then Tr(ρA) ∈ ℝ.

**Note:**

This is about Tr(A) being real, not ⟨ψ|Aψ⟩ (which is `expectation_real`).
The trace sums all diagonal expectations, each real, giving a real total.
-/
theorem trace_hermitian_real (n : ℕ) (A : HermitianOp (ℂ^n)) :
    (trace n A.op).im = 0 := by
  have h := trace_adjoint n A.op
  rw [A.self_adjoint] at h
  have := Complex.conj_eq_iff_im.mp h.symm
  exact this


/-!
================================================================================
SECTION 10: OUTER PRODUCTS
================================================================================

The outer product |ψ⟩⟨φ| is the rank-one operator:
  (|ψ⟩⟨φ|)(v) = ⟨φ|v⟩ ψ

Key for density operators: ρ = |ψ⟩⟨ψ| for pure states.
-/

/-- Outer product |ψ⟩⟨φ| as a linear operator.

The outer product (|ψ⟩⟨φ|)(v) = ⟨φ|v⟩ · ψ

**Mathematical content:**

This is a rank-one operator (unless ψ or φ is zero). Its image is
span{ψ} and its kernel is {v : ⟨φ|v⟩ = 0} = φ⊥.

**Physical role:**

Outer products build:
  - Projectors: P = |ψ⟩⟨ψ| projects onto span{ψ}
  - Density matrices: ρ = |ψ⟩⟨ψ| for pure states
  - General operators: A = Σᵢⱼ Aᵢⱼ |eᵢ⟩⟨eⱼ| in a basis
  - Completeness: Σᵢ |eᵢ⟩⟨eᵢ| = I

**Properties (proven below):**
  - (|ψ⟩⟨φ|)† = |φ⟩⟨ψ|
  - Tr(|ψ⟩⟨φ|) = ⟨φ|ψ⟩
  - |ψ⟩⟨φ| · |χ⟩⟨η| = ⟨φ|χ⟩ |ψ⟩⟨η| (composition rule)
-/
noncomputable def outerProduct (ψ φ : H) : H →L[ℂ] H :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => ⟪φ, v⟫_ℂ • ψ
    map_add' := fun x y => by simp [inner_add_right, add_smul]
    map_smul' := fun c x => by simp [inner_smul_right, smul_smul]
  }

notation "|" ψ "⟩⟨" φ "|" => outerProduct ψ φ

/-- Outer product applied to a vector.

  (|ψ⟩⟨φ|)(v) = ⟪φ, v⟫_ℂ · ψ
Physical interpretation:
The outer product projects v onto the "φ direction" and outputs in
the "ψ direction," scaled by the inner product ⟨φ|v⟩.
For a projector |ψ⟩⟨ψ| (with normalized ψ):
(|ψ⟩⟨ψ|)(v) = ⟨ψ|v⟩ · ψ
This extracts the component of v along ψ.
-/
theorem outerProduct_apply (ψ φ v : H) :
(|ψ⟩⟨φ|) v = ⟪φ, v⟫_ℂ • ψ := rfl


/-- Adjoint of outer product: (|ψ⟩⟨φ|)† = |φ⟩⟨ψ|.

The adjoint swaps ψ and φ.

**Proof:**

⟨(|ψ⟩⟨φ|)†x | y⟩ = ⟨x | (|ψ⟩⟨φ|)y⟩ = ⟨x | ⟨φ|y⟩ψ⟩ = ⟨φ|y⟩⟨x|ψ⟩
                 = ⟨⟨ψ|x⟩φ | y⟩ = ⟨(|φ⟩⟨ψ|)x | y⟩

for all y, so (|ψ⟩⟨φ|)†x = (|φ⟩⟨ψ|)x.

**Physical meaning:**

In Dirac notation: (|ψ⟩⟨φ|)† = |φ⟩⟨ψ|. The adjoint reverses the
bra and ket while conjugating any scalars.

**Consequence for projectors:**

(|ψ⟩⟨ψ|)† = |ψ⟩⟨ψ|: projectors onto 1D subspaces are Hermitian.
-/
theorem outerProduct_adjoint (ψ φ : H) :
    (|ψ⟩⟨φ|)† = |φ⟩⟨ψ| := by
  simp only [adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right (𝕜 := ℂ)
  intro y
  calc ⟪ContinuousLinearMap.adjoint (|ψ⟩⟨φ|) x, y⟫_ℂ
      = ⟪x, (|ψ⟩⟨φ|) y⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_left (|ψ⟩⟨φ|) y x
    _ = ⟪x, ⟪φ, y⟫_ℂ • ψ⟫_ℂ := by rw [outerProduct_apply]
    _ = ⟪φ, y⟫_ℂ * ⟪x, ψ⟫_ℂ := by rw [inner_smul_right (𝕜 := ℂ)]
    _ = ⟪x, ψ⟫_ℂ * ⟪φ, y⟫_ℂ := by ring
    _ = conj ⟪ψ, x⟫_ℂ * ⟪φ, y⟫_ℂ := by rw [inner_conj_symm]
    _ = ⟪⟪ψ, x⟫_ℂ • φ, y⟫_ℂ := by rw [inner_smul_left (𝕜 := ℂ)]
    _ = ⟪(|φ⟩⟨ψ|) x, y⟫_ℂ := by rw [outerProduct_apply]


/-- Self outer product is Hermitian.

  (|ψ⟩⟨ψ|)† = |ψ⟩⟨ψ|

**Proof:**

Special case of `outerProduct_adjoint` with φ = ψ.

**Physical meaning:**

The projector onto a one-dimensional subspace is always Hermitian.
This makes |ψ⟩⟨ψ| a valid observable (the "is the system in state ψ?"
measurement) and a valid pure-state density matrix.
-/
theorem outerProduct_self_hermitian (ψ : H) :
    (|ψ⟩⟨ψ|)† = |ψ⟩⟨ψ| :=
  outerProduct_adjoint ψ ψ


/-- Trace of outer product: Tr(|ψ⟩⟨φ|) = ⟨φ|ψ⟩.

**Proof:**

Tr(|ψ⟩⟨φ|) = Σᵢ ⟨eᵢ|(|ψ⟩⟨φ|)eᵢ⟩ = Σᵢ ⟨eᵢ|⟨φ|eᵢ⟩ψ⟩ = Σᵢ ⟨φ|eᵢ⟩⟨eᵢ|ψ⟩
           = ⟨φ|Σᵢ |eᵢ⟩⟨eᵢ|ψ⟩ = ⟨φ|ψ⟩

using completeness Σᵢ |eᵢ⟩⟨eᵢ| = I.

**Physical meaning:**

This connects the algebraic trace to the inner product. For a
pure-state density matrix ρ = |ψ⟩⟨ψ| with normalized ψ:
  Tr(ρ) = Tr(|ψ⟩⟨ψ|) = ⟨ψ|ψ⟩ = 1

confirming trace normalization.

**Expectation values:**

For observable A and state |ψ⟩:
  ⟨A⟩ = Tr(|ψ⟩⟨ψ| A) = Tr(A |ψ⟩⟨ψ|) (cyclic)

This connects the bra-ket expectation ⟨ψ|A|ψ⟩ to the trace formula.
-/
theorem trace_outerProduct (n : ℕ) (ψ φ : ℂ^n) :
    trace n (|ψ⟩⟨φ|) = ⟪φ, ψ⟫_ℂ := by
  simp only [trace, outerProduct_apply]
  -- Step 1: Pull scalar out of inner product
  have step1 : ∀ i, ⟪std_basis n i, ⟪φ, std_basis n i⟫_ℂ • ψ⟫_ℂ
             = ⟪φ, std_basis n i⟫_ℂ * ⟪std_basis n i, ψ⟫_ℂ := by
    intro i
    rw [inner_smul_right (𝕜 := ℂ)]

  simp_rw [step1]
  -- Step 2: Use expansion ψ = Σᵢ ⟪eᵢ, ψ⟫ • eᵢ
  have expand : ψ = ∑ i : Fin n, ⟪std_basis n i, ψ⟫_ℂ • std_basis n i := by
    have h := expand_std_basis n ψ
    simp only [braket] at h
    exact h
  -- Step 3: Expand ⟪φ, ψ⟫ using linearity
  calc ∑ i : Fin n, ⟪φ, std_basis n i⟫_ℂ * ⟪std_basis n i, ψ⟫_ℂ
      = ∑ i : Fin n, ⟪std_basis n i, ψ⟫_ℂ * ⟪φ, std_basis n i⟫_ℂ := by
        congr 1; ext i; ring
    _ = ∑ i : Fin n, ⟪φ, ⟪std_basis n i, ψ⟫_ℂ • std_basis n i⟫_ℂ := by
        simp_rw [inner_smul_right (𝕜 := ℂ)]
    _ = ⟪φ, ∑ i : Fin n, ⟪std_basis n i, ψ⟫_ℂ • std_basis n i⟫_ℂ := by
        rw [inner_sum (𝕜 := ℂ)]
    _ = ⟪φ, ψ⟫_ℂ := by rw [← expand]


/-- Trace of |ψ⟩⟨ψ| for a normalized state is 1.

For a quantum state ψ with ‖ψ‖ = 1:
  Tr(|ψ⟩⟨ψ|) = 1

**Proof:**

Tr(|ψ⟩⟨ψ|) = ⟨ψ|ψ⟩ = ‖ψ‖² = 1² = 1

using `trace_outerProduct` and normalization.

**Physical meaning:**

This is the trace normalization condition for pure-state density matrices.
The density matrix ρ = |ψ⟩⟨ψ| satisfies:
  - Tr(ρ) = 1 (probabilities sum to 1)
  - ρ† = ρ (Hermitian, from `outerProduct_self_hermitian`)
  - ρ ≥ 0 (positive semidefinite)
  - ρ² = ρ (pure state: projector)

These four properties define a pure-state density matrix.

**Connection to measurement:**

For any orthonormal basis {|eᵢ⟩}, the probabilities pᵢ = ⟨eᵢ|ρ|eᵢ⟩ satisfy:
  Σᵢ pᵢ = Σᵢ ⟨eᵢ|ψ⟩⟨ψ|eᵢ⟩ = Σᵢ |⟨eᵢ|ψ⟩|² = Tr(ρ) = 1

Trace normalization ensures the Born rule produces a valid probability
distribution.

**Role in quantum information:**

Density matrices generalize pure states to mixed states (statistical
ensembles). The trace condition Tr(ρ) = 1 is the fundamental normalization
that all density matrices must satisfy, whether pure or mixed.
-/
theorem trace_outerProduct_self_normalized (n : ℕ) (ψ : QuantumState (ℂ^n)) :
    trace n (|ψ.vec⟩⟨ψ.vec|) = 1 := by
  rw [trace_outerProduct]
  rw [inner_self_eq_norm_sq_to_K, ψ.normalized]
  simp

/-!
================================================================================
SUMMARY AND EXPORTS
================================================================================

This file provides the mathematical foundation for quantum mechanics:

STRUCTURES:
  - QuantumState: normalized vectors
  - HermitianOp: self-adjoint operators (observables)
  - UnitaryOp: norm-preserving operators (dynamics)
  - SpectralDecomp: eigenvalue/eigenvector decomposition

KEY THEOREMS:
  - braket properties (conjugate symmetry, linearity)
  - Hermitian operators have real eigenvalues
  - Unitary operators preserve norm


NOTATION:
  - ⟨ψ|φ⟩: physics inner product
  - A†: adjoint

CONNECTIONS:
  - Used by: State.lean (density operators)
  - Used by: VonNeumann.lean (entropy)
  - Used by: Evolution/ (dynamics)

TODOS:
  - Complete tensor product inner product structure
  - Infinite-dimensional extension (unbounded operators)
  - More concrete examples (harmonic oscillator, spin-j)
-/

end QHilbert
