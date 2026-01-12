/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.Spectral.FunctionalCalc
/-!
# The Dirac Equation and Relativistic Quantum Mechanics

This file develops the Dirac equation for spin-1/2 particles, from the algebraic
foundations (Clifford algebra of spacetime) through spectral theory to the
physical consequences (probability conservation and the Born rule).

## Overview

The Dirac equation is the relativistic wave equation for fermions:

  iℏ ∂ψ/∂t = H_D ψ,    where   H_D = -iℏc(α·∇) + βmc²

The matrices α = (α₁, α₂, α₃) and β satisfy the Clifford algebra relations:
- αᵢ² = β² = I (involutions)
- {αᵢ, αⱼ} = 0 for i ≠ j (spatial anticommutation)
- {αᵢ, β} = 0 (momentum-mass anticommutation)

These relations ensure H_D² gives the relativistic dispersion relation
E² = (pc)² + (mc²)², which is the mathematical content of special relativity.

## Main definitions

### Clifford Algebra (§1-2)
* `diracAlpha1`, `diracAlpha2`, `diracAlpha3`: Spatial Dirac matrices in standard representation
* `diracBeta`: Mass matrix β = diag(1, 1, -1, -1)
* `gamma0`, `gamma1`, `gamma2`, `gamma3`: Covariant gamma matrices γᵘ
* `gamma5`: Chirality matrix γ⁵ = iγ⁰γ¹γ²γ³
* `DiracMatrices`: Abstract structure for any valid representation
* `standardDiracMatrices`: The Dirac-Pauli representation

### Physical Framework (§3)
* `DiracConstants`: Physical parameters (ℏ, c, m) with positivity conditions
* `DiracOperator`: Unbounded linear operator with explicit domain
* `DiracHamiltonian`: Full Dirac Hamiltonian with symmetry and density properties
* `DiracSpectralData`: Complete spectral decomposition via functional calculus

### Spectral Structure (§4)
* `diracSpectrum`: The set (-∞, -mc²] ∪ [mc², ∞)
* `diracGap`: The forbidden energy region (-mc², mc²)
* `electronProjection`: Spectral projection E([mc², ∞))
* `positronProjection`: Spectral projection E((-∞, -mc²])

### Probability Theory (§5)
* `diracCurrent`: The 4-current jᵘ = ψ̄γᵘψ
* `probabilityDensity`: ρ = j⁰ = ψ†ψ
* `totalProbability`: P(t) = ∫ρ(t,x) d³x
* `normalizedProbability`: P(x,t) = ρ(x,t) / ∫ρ d³x

## Main results

### Clifford Algebra Relations (Proved by Computation)
* `diracAlpha1_sq`, `diracAlpha2_sq`, `diracAlpha3_sq`, `diracBeta_sq`: αᵢ² = β² = I
* `diracAlpha12_anticommute`, etc.: {αᵢ, αⱼ} = 0 for i ≠ j
* `diracAlpha1_beta_anticommute`, etc.: {αᵢ, β} = 0
* `clifford_00` through `clifford_33`: {γᵘ, γᵛ} = 2ηᵘᵛI (all 16 cases)

### Gamma Matrix Properties
* `gamma0_sq_eq_one`: (γ⁰)² = I
* `gamma1_sq_eq_neg_one`, etc.: (γⁱ)² = -I for spatial indices
* `gamma_trace_zero`: Tr(γᵘ) = 0
* `gamma_trace_two`: Tr(γᵘγᵛ) = 4ηᵘᵛ
* `gamma_trace_three`: Tr(γᵘγᵛγᵖ) = 0 (odd number of gammas)
* `gamma5_sq`: (γ⁵)² = I
* `gamma5_anticommutes`: {γ⁵, γᵘ} = 0

### Spectral Theory
* `dirac_unbounded_below`, `dirac_unbounded_above`: H_D is unbounded in both directions
* `dirac_not_semibounded`: H_D has no lower bound (unlike non-relativistic QM)
* `electron_positron_orthogonal`: E₊ E₋ = 0
* `dirac_spectral_gap_zero`: E((-mc², mc²)) = 0
* `electron_positron_complete`: E₊ + E₋ = 1 (for m > 0)

### Probability Conservation
* `current_zero_eq_norm_sq`: j⁰ = Σₐ|ψₐ|² (fundamental identity)
* `current_zero_nonneg`: j⁰ ≥ 0 (probability is non-negative)
* `probability_conserved`: d/dt ∫ρ d³x = 0 (unitarity)
* `born_rule_valid`: P(x,t) = ρ/∫ρ is a valid probability distribution

## Implementation notes

### Brute-Force Clifford Verification
All 16 Clifford relations {γᵘ, γᵛ} = 2ηᵘᵛI are verified by explicit 4×4 matrix
computation. The proof strategy `ext a b; fin_cases a <;> fin_cases b <;> simp`
expands each matrix equation into 16 scalar equations and simplifies.

This is computationally expensive (`maxHeartbeats` up to 400000) but mathematically
bulletproof — no axioms needed for the algebraic foundations.

### Axioms
The file contains 11 axioms in three categories:

**Spectral theory axioms** (would follow from functional calculus completion):
* `dirac_generates_unitary`: H_D generates a strongly continuous unitary group
* `dirac_gap_in_resolvent`, `dirac_gap_in_resolvent_set`: Gap points have bounded resolvent
* `dirac_spectrum_eq`: Spectral measure vanishes on gap
* `spectral_measure_supported_on_spectrum`: E(B) = 0 if B ⊆ resolvent set
* `dirac_has_arbitrarily_negative_energy`, `dirac_has_arbitrarily_positive_energy`: Unboundedness

**PDE/analysis axioms** (standard results requiring measure theory):
* `dirac_current_conserved`: Dirac equation implies ∂ᵤjᵘ = 0
* `leibniz_integral_rule`: d/dt ∫f(t,x)dx = ∫(∂f/∂t)dx
* `continuity_equation`: ∂ρ/∂t = -∇·j
* `divergence_integral_vanishes`: ∫∇·j d³x = 0 with decay conditions

### Connection to Spectral Theory
The file imports `FunctionalCalc` and uses `IsSpectralMeasureFor` to connect
the Dirac Hamiltonian to spectral projections. This enables:
- Definition of electron/positron subspaces via spectral projections
- Proof that these subspaces are orthogonal and complete
- Time evolution via the unitary group U(t) = e^{-itH_D/ℏ}

## Physical interpretation

### The Dirac Sea and Antiparticles
The spectrum σ(H_D) = (-∞, -mc²] ∪ [mc², ∞) has negative energy states.
Dirac's interpretation: the "vacuum" has all negative-energy states filled
(the Dirac sea). A hole in the sea appears as a positron — a particle with
positive energy and opposite charge.

### Chirality and the Weak Force
The matrix γ⁵ projects onto left-handed (P_L = (1-γ⁵)/2) and right-handed
(P_R = (1+γ⁵)/2) states. The weak nuclear force couples only to left-handed
particles, which is why γ⁵ is physically important.

### Probability Conservation
Unlike the Klein-Gordon equation, the Dirac equation has a *positive-definite*
probability density ρ = ψ†ψ ≥ 0. This is the key physical requirement that
motivated Dirac's construction. The proof that dP/dt = 0 follows from the
continuity equation ∂ᵤjᵘ = 0.

### The Born Rule
The theorem `born_rule_valid` shows that ρ/∫ρ satisfies the axioms of a
probability distribution: non-negative and normalized to 1. This connects
the mathematical formalism to quantum mechanical measurement.

## References

* [Dirac, *The Principles of Quantum Mechanics*][dirac1930], Chapter XI
* [Thaller, *The Dirac Equation*][thaller1992]
* [Peskin, Schroeder, *An Introduction to Quantum Field Theory*][peskin1995], Chapter 3
* [Reed, Simon, *Methods of Modern Mathematical Physics*][reed1975], Vol. II §X.4

## Tags

Dirac equation, Clifford algebra, gamma matrices, spinor, relativistic quantum mechanics,
spectral gap, probability conservation, Born rule, chirality
-/
namespace PaulDirac
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open  MeasureTheory InnerProductSpace Complex QuantumMechanics.Cayley SpectralBridge QuantumMechanics.Generators FunctionalCalculus
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


/-- α₁ in standard representation (4×4) -/
def diracAlpha1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- α₂ in standard representation (4×4) -/
def diracAlpha2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, -I;
     0, 0, I, 0;
     0, -I, 0, 0;
     I, 0, 0, 0]

/-- α₃ in standard representation (4×4) -/
def diracAlpha3 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, -1;
     1, 0, 0, 0;
     0, -1, 0, 0]

/-- β in standard representation (4×4) -/
def diracBeta : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]


set_option maxHeartbeats 375000

/-- α₁ is an involution: α₁² = I.

**Mathematical meaning**: α₁ has eigenvalues ±1 (since x² = 1 ⟹ x = ±1).
Combined with Hermiticity, this gives a complete spectral decomposition.

**Physical meaning**: The Clifford algebra relation {αᵢ, αⱼ} = 2δᵢⱼ
(of which this is the i = j = 1 case) is what makes H_D² yield the
relativistic dispersion relation E² = (pc)² + (mc²)².

**Proof strategy**: Brute-force verification of all 16 matrix entries.
`fin_cases a <;> fin_cases b` splits into the 4×4 = 16 cases (a,b) ∈ Fin 4 × Fin 4,
then `simp` computes each entry of the product. -/
private lemma diracAlpha1_sq : diracAlpha1 * diracAlpha1 = 1 := by
  ext a b                    -- Reduce matrix equality to entry-wise: ∀ a b, (α₁²)ₐᵦ = Iₐᵦ
  fin_cases a <;> fin_cases b <;>  -- Split into 16 cases for each (a,b) pair
  simp only [diracAlpha1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val,
             Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add, ↓reduceIte]
  all_goals try simp        -- Finish off any remaining arithmetic

/-- α₂ is an involution: α₂² = I.

Unlike α₁ and α₃, the matrix α₂ contains imaginary entries (±I) from the
Pauli-Y matrix. The product α₂² involves terms like (-I)(I) = 1, which
is why `mul_neg, neg_mul` appear in the simplification. -/
private lemma diracAlpha2_sq : diracAlpha2 * diracAlpha2 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val,
             Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, add_zero, zero_add, ↓reduceIte, mul_neg, neg_mul]
  all_goals try simp

/-- α₃ is an involution: α₃² = I.

The matrix α₃ is built from the Pauli-Z matrix (diagonal ±1 entries).
The product involves (-1)(-1) = 1 terms, hence `neg_neg` in the simplification. -/
private lemma diracAlpha3_sq : diracAlpha3 * diracAlpha3 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha3, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val,
             Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add, ↓reduceIte, mul_neg, neg_neg]
  all_goals try simp

/-- β is an involution: β² = I.

The mass matrix β = diag(1, 1, -1, -1) distinguishes upper spinor components
(particle) from lower components (antiparticle). Being diagonal, the proof
is simpler than for the α matrices — just (-1)² = 1 on the lower block. -/
private lemma diracBeta_sq : diracBeta * diracBeta = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracBeta, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val,
             Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_one, mul_zero, add_zero, ↓reduceIte]
  all_goals try simp only [mul_neg, mul_one, neg_zero, neg_neg, Fin.reduceEq, ↓reduceIte]
  all_goals try ring

/-- α₁ and α₂ anticommute: {α₁, α₂} = α₁α₂ + α₂α₁ = 0.

This is the i ≠ j case of the Clifford relation {αᵢ, αⱼ} = 2δᵢⱼ.
Anticommutation of distinct α matrices ensures that H_D² produces
the Laplacian (not some cross-term mess): (α·p)² = p₁² + p₂² + p₃².

The proof mixes real entries (from α₁) with imaginary entries (from α₂),
producing cancellations like 1·I + I·(-1) = 0. -/
private lemma diracAlpha12_anticommute : diracAlpha1 * diracAlpha2 + diracAlpha2 * diracAlpha1 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha1, diracAlpha2, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.zero_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one]
  all_goals try simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, mul_zero, add_zero,
    one_mul, zero_add, mul_one, add_neg_cancel, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_zero, mul_neg, zero_mul, neg_zero, mul_zero, add_zero, mul_one]
  all_goals try ring_nf

/-- α₁ and α₃ anticommute: {α₁, α₃} = 0.

Both matrices have real entries (α₁ from Pauli-X, α₃ from Pauli-Z),
so cancellations involve only ±1 arithmetic, no complex numbers. -/
private lemma diracAlpha13_anticommute : diracAlpha1 * diracAlpha3 + diracAlpha3 * diracAlpha1 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha1, diracAlpha3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.zero_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one]
  all_goals try simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_zero, mul_zero, add_zero, mul_neg, mul_one, neg_zero]
  all_goals try ring

/-- α₂ and α₃ anticommute: {α₂, α₃} = 0.

This mixes imaginary entries (from α₂) with real entries (from α₃).
Cancellations have the form I·1 + 1·(-I) = 0. -/
private lemma diracAlpha23_anticommute : diracAlpha2 * diracAlpha3 + diracAlpha3 * diracAlpha2 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha2, diracAlpha3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.zero_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one]
  all_goals try simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_zero, mul_zero, mul_neg, mul_one, neg_neg, zero_add, add_zero, one_mul,
    add_neg_cancel]
  all_goals try ring

/-- α₁ and β anticommute: {α₁, β} = 0.

This is the key structural relation connecting momentum and mass terms in
H_D = -iℏc(α·∇) + βmc². Because {αᵢ, β} = 0, the square H_D² separates cleanly:

  H_D² = (ℏc)²(α·∇)² + (mc²)²β² = -ℏ²c²∇² + m²c⁴

with no cross terms. This yields the relativistic dispersion E² = p²c² + m²c⁴. -/
private lemma diracAlpha1_beta_anticommute : diracAlpha1 * diracBeta + diracBeta * diracAlpha1 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha1, diracBeta, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.zero_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one]
  all_goals try simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_zero, mul_zero, add_zero, mul_neg, mul_one, neg_zero]
  all_goals try ring

/-- α₂ and β anticommute: {α₂, β} = 0.

Same structural role as `diracAlpha1_beta_anticommute`. The imaginary entries
of α₂ don't affect the cancellation pattern since β is diagonal and real. -/
private lemma diracAlpha2_beta_anticommute : diracAlpha2 * diracBeta + diracBeta * diracAlpha2 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha2, diracBeta, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.zero_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one]
  all_goals try simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.reduceFinMk,
    Matrix.cons_val, mul_zero, add_zero, mul_neg, mul_one, neg_zero, zero_mul]
  all_goals try ring

/-- α₃ and β anticommute: {α₃, β} = 0.

Completes the set of α-β anticommutation relations. Both matrices have
real entries, so the cancellations are purely ±1 arithmetic. -/
private lemma diracAlpha3_beta_anticommute : diracAlpha3 * diracBeta + diracBeta * diracAlpha3 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha3, diracBeta, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.zero_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one]
  all_goals try simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.reduceFinMk,
    Matrix.cons_val, mul_zero, add_zero, mul_neg, mul_one, zero_add, neg_add_cancel]
  all_goals try ring

/-- α₁ is Hermitian: α₁† = α₁.

Hermiticity of all α matrices and β ensures the Dirac Hamiltonian is symmetric:
⟨H_D ψ, φ⟩ = ⟨ψ, H_D φ⟩ on its domain. This is the first step toward proving
essential self-adjointness.

α₁ has only real entries (0 and 1), so conjugate transpose = transpose,
and the matrix is symmetric. -/
private lemma diracAlpha1_hermitian : diracAlpha1.conjTranspose = diracAlpha1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha1, Matrix.conjTranspose, Matrix.of_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_one]

/-- α₂ is Hermitian: α₂† = α₂.

Despite having imaginary entries (±I), α₂ is still Hermitian. The key is that
I appears in antisymmetric positions: (α₂)ᵢⱼ = -I implies (α₂)ⱼᵢ = +I.
Transposing swaps positions, conjugating flips signs: I* = -I.
The two operations cancel: (α₂)†ᵢⱼ = conj((α₂)ⱼᵢ) = conj(±I) = ∓I = (α₂)ᵢⱼ. -/
private lemma diracAlpha2_hermitian : diracAlpha2.conjTranspose = diracAlpha2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha2, Matrix.conjTranspose, Matrix.of_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_neg, conj_I, neg_neg]

/-- α₃ is Hermitian: α₃† = α₃.

Like α₁, the matrix α₃ has only real entries (0 and ±1). Real symmetric
matrices are Hermitian: transpose is the identity, conjugation does nothing. -/
private lemma diracAlpha3_hermitian : diracAlpha3.conjTranspose = diracAlpha3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha3, Matrix.conjTranspose, Matrix.of_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_one, star_neg]

/-- β is Hermitian: β† = β.

The mass matrix β = diag(1, 1, -1, -1) is diagonal with real entries.
Diagonal matrices are symmetric, and real entries are self-conjugate,
so Hermiticity is immediate. -/
private lemma diracBeta_hermitian : diracBeta.conjTranspose = diracBeta := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracBeta, Matrix.conjTranspose, Matrix.of_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_one, star_neg]

/-- γ⁰ = β: the timelike gamma matrix (Hermitian). -/
def gamma0 : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

/-- γ¹ = βα₁: spacelike gamma matrix (anti-Hermitian). -/
def gamma1 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

/-- γ² = βα₂: spacelike gamma matrix (anti-Hermitian, contains ±I). -/
def gamma2 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, -I; 0, 0, I, 0; 0, I, 0, 0; -I, 0, 0, 0]

/-- γ³ = βα₃: spacelike gamma matrix (anti-Hermitian). -/
def gamma3 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]


set_option maxHeartbeats 50000

/-- Minkowski-Clifford relation for γ⁰: {γ⁰, γ⁰} = 2η⁰⁰ I = 2I.

The timelike component has η⁰⁰ = +1, so γ⁰ squares to +I.
Written as γ⁰γ⁰ + γ⁰γ⁰ = 2I to match the anticommutator form. -/
private lemma clifford_00 : gamma0 * gamma0 + gamma0 * gamma0 =
    2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma0, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add, mul_neg, neg_neg, neg_zero,
    ↓reduceIte, Fin.isValue, Fin.reduceEq, ↓reduceIte, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ⁰, γ¹} = 2η⁰¹ I = 0.

Off-diagonal Minkowski components vanish (η⁰¹ = 0), so distinct
gamma matrices anticommute. This is the covariant form of {αᵢ, β} = 0. -/
private lemma clifford_01 : gamma0 * gamma1 + gamma1 * gamma0 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma0, gamma1, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ⁰, γ²} = 0.

Off-diagonal relation with the imaginary-entry matrix γ². The ±I entries
don't affect the anticommutation since γ⁰ is diagonal. -/
private lemma clifford_02 : gamma0 * gamma2 + gamma2 * gamma0 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma0, gamma2, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ⁰, γ³} = 0.

Both matrices have real entries; cancellation is pure ±1 arithmetic. -/
private lemma clifford_03 : gamma0 * gamma3 + gamma3 * gamma0 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma0, gamma3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ¹, γ⁰} = 0.

Same as `clifford_01` with reversed order; anticommutators are symmetric. -/
private lemma clifford_10 : gamma1 * gamma0 + gamma0 * gamma1 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma0, gamma1, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation for γ¹: {γ¹, γ¹} = 2η¹¹ I = -2I.

Spacelike components have η¹¹ = -1 (Minkowski signature), so γ¹ squares to -I.
This sign difference from γ⁰ is what makes the metric indefinite. -/
private lemma clifford_11 : gamma1 * gamma1 + gamma1 * gamma1 =
    (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma1, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_mul, neg_zero, smul_eq_mul, ↓reduceIte]
  all_goals try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_zero, neg_zero]
  all_goals try ring_nf


/-- Minkowski-Clifford relation: {γ¹, γ²} = 0.

Distinct spacelike gamma matrices anticommute (η¹² = 0). This mixes
real entries (γ¹) with imaginary entries (γ²). -/
private lemma clifford_12 : gamma1 * gamma2 + gamma2 * gamma1 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma1, gamma2, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ¹, γ³} = 0.

Both matrices have real entries; purely ±1 arithmetic. -/
private lemma clifford_13 : gamma1 * gamma3 + gamma3 * gamma1 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma1, gamma3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ², γ⁰} = 0.

Same as `clifford_02` with reversed order. -/
private lemma clifford_20 : gamma2 * gamma0 + gamma0 * gamma2 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma0, gamma2, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ², γ¹} = 0.

Same as `clifford_12` with reversed order. -/
private lemma clifford_21 : gamma2 * gamma1 + gamma1 * gamma2 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma1, gamma2, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation for γ²: {γ², γ²} = 2η²² I = -2I.

Spacelike signature gives -2I. The proof uses `I_mul_I` to simplify
products of imaginary entries: (±I)(±I) = -1. -/
private lemma clifford_22 : gamma2 * gamma2 + gamma2 * gamma2 =
    (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma2, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, zero_mul, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg, neg_zero, smul_eq_mul, ↓reduceIte]
  all_goals try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_zero, neg_zero]
  all_goals try simp only [I_mul_I]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ², γ³} = 0.

Mixes imaginary entries (γ²) with real entries (γ³). -/
private lemma clifford_23 : gamma2 * gamma3 + gamma3 * gamma2 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma2, gamma3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg, neg_zero]
  all_goals try ring_nf

/-- Minkowski-Clifford relation: {γ³, γ⁰} = 0.

Same as `clifford_03` with reversed order. -/
private lemma clifford_30 : gamma3 * gamma0 + gamma0 * gamma3 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma0, gamma3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_neg, neg_zero]
  all_goals try ring_nf

/-- Minkowski-Clifford relation: {γ³, γ¹} = 0.

Same as `clifford_13` with reversed order. -/
private lemma clifford_31 : gamma3 * gamma1 + gamma1 * gamma3 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma1, gamma3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_neg, neg_zero]
  all_goals try ring_nf

/-- Minkowski-Clifford relation: {γ³, γ²} = 0.

Same as `clifford_23` with reversed order. -/
private lemma clifford_32 : gamma3 * gamma2 + gamma2 * gamma3 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma2, gamma3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg, neg_zero]
  all_goals try ring_nf

/-- Minkowski-Clifford relation for γ³: {γ³, γ³} = 2η³³ I = -2I.

Completes the diagonal relations. All three spacelike matrices square to -I,
reflecting the signature (1, -1, -1, -1) of Minkowski space. -/
private lemma clifford_33 : gamma3 * gamma3 + gamma3 * gamma3 =
    (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_mul, neg_zero, smul_eq_mul, ↓reduceIte]
  all_goals try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_zero, neg_zero]
  all_goals try ring_nf


/-- Helper: -2 as scalar matrix equals -2 • 1 -/
private lemma neg_two_eq_smul : (-2 : Matrix (Fin 4) (Fin 4) ℂ) = (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  simp only [map_neg, neg_inj]
  rfl

/-- γ⁰ is Hermitian: (γ⁰)† = γ⁰.

The timelike gamma matrix has real diagonal entries, hence is self-adjoint. -/
private lemma gamma0_hermitian_proof : gamma0.conjTranspose = gamma0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma0, Matrix.conjTranspose, Matrix.of_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_one, star_zero, star_neg]

/-- γ¹ is anti-Hermitian: (γ¹)† = -γ¹.

Spacelike gamma matrices pick up a sign under adjoint. This is connected to
the −1 in the Minkowski metric η¹¹ = −1. -/
private lemma gamma1_antihermitian : gamma1.conjTranspose = -gamma1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma1, Matrix.conjTranspose, Matrix.neg_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_one, star_neg, neg_zero]

/-- γ² is anti-Hermitian: (γ²)† = -γ².

Despite having imaginary entries, the anti-Hermiticity comes from the spatial
structure, not the presence of I. -/
private lemma gamma2_antihermitian : gamma2.conjTranspose = -gamma2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma2, Matrix.conjTranspose, Matrix.neg_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_neg, RCLike.star_def, conj_I, neg_neg, neg_zero]

/-- γ³ is anti-Hermitian: (γ³)† = -γ³. -/
private lemma gamma3_antihermitian : gamma3.conjTranspose = -gamma3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma3, Matrix.conjTranspose, Matrix.neg_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_one, star_neg, neg_zero, neg_neg]



section AdditionalLemmas

/-- The Minkowski metric tensor η^μν = diag(1, -1, -1, -1) -/
def minkowskiMetric (μ ν : Fin 4) : ℂ :=
  if μ = ν then
    if μ = 0 then 1 else -1
  else 0

/-- The chirality matrix γ⁵ = iγ⁰γ¹γ²γ³.

**Standard representation**:
        ┌         ┐
        │  0   I₂ │
  γ⁵ =  │         │
        │  I₂  0  │
        └         ┘

This is the "fifth" gamma matrix, completing the Clifford algebra
to Cl(1,3) ⊕ Cl(1,3) ≅ Cl(2,3).

**Physical role**: The projectors P_L = (1-γ⁵)/2 and P_R = (1+γ⁵)/2
select left-handed and right-handed chirality states. The weak force
couples only to P_L ψ. -/
def gamma5 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]



/-- Helper to get gamma matrix by index.

Provides uniform access: gammaAt 0 = γ⁰, gammaAt 1 = γ¹, etc.
Useful for stating general identities that hold for all μ. -/
def gammaAt (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  match μ with
  | 0 => gamma0
  | 1 => gamma1
  | 2 => gamma2
  | 3 => gamma3


/-- Tr(γ⁰) = 0: The timelike gamma matrix is traceless.

**Proof**: γ⁰ = diag(1, 1, -1, -1), so Tr = 1 + 1 + (-1) + (-1) = 0. -/
lemma gamma0_trace_zero : Matrix.trace gamma0 = 0 := by
  unfold gamma0 Matrix.trace Matrix.diag
  simp only [Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero,Matrix.cons_val_one,
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


/-- (γ⁰)² = I: The timelike gamma matrix squares to the identity.

Derived from clifford_00: γ⁰γ⁰ + γ⁰γ⁰ = 2I. -/
lemma gamma0_sq_eq_one : gamma0 * gamma0 = 1 := by
  have h := clifford_00
  -- h : gamma0 * gamma0 + gamma0 * gamma0 = 2 • 1
  -- This means 2 * (gamma0 * gamma0) = 2 * 1
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
  -- h : gamma1 * gamma1 + gamma1 * gamma1 = (-2 : ℂ) • 1
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

/-!
## Helper Lemma: Trace of Identity

For n×n matrices, Tr(I_n) = n. Here n = 4.
-/

/-- Tr(I₄) = 4: The trace of the 4×4 identity matrix. -/
lemma trace_one_fin4 : Matrix.trace (1 : Matrix (Fin 4) (Fin 4) ℂ) = 4 := by
  unfold Matrix.trace Matrix.diag
  simp only [Fin.sum_univ_four, Matrix.one_apply_eq]
  norm_num

/-- Tr(-I₄) = -4: The trace of minus the identity. -/
lemma trace_neg_one_fin4 : Matrix.trace (-(1 : Matrix (Fin 4) (Fin 4) ℂ)) = -4 := by
  rw [Matrix.trace_neg, trace_one_fin4]

/-!
## Helper Lemma: Cyclic Property of Trace

The trace satisfies Tr(AB) = Tr(BA) for any square matrices A, B.
This is a standard result in Mathlib.
-/

/-- Tr(AB) = Tr(BA): Cyclic property of trace.
    This should be `Matrix.trace_mul_comm` in Mathlib. -/
lemma trace_mul_comm (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.trace (A * B) = Matrix.trace (B * A) := by
  unfold Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply]
  -- Tr(AB) = Σᵢ (AB)ᵢᵢ = Σᵢ Σⱼ Aᵢⱼ Bⱼᵢ
  -- Tr(BA) = Σᵢ (BA)ᵢᵢ = Σᵢ Σⱼ Bᵢⱼ Aⱼᵢ
  -- These are equal by swapping summation indices
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  ring


/-- For anticommuting matrices, the trace of the product vanishes. -/
lemma trace_zero_of_anticommute (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (h : A * B + B * A = 0) : Matrix.trace (A * B) = 0 := by
  -- From h: A * B = -(B * A)
  -- Algebra: (A*B + B*A) - B*A = 0 - B*A  ⟹  A*B = -(B*A)
  have hab : A * B = -(B * A) := by
    have h' := congrArg (· - B * A) h
    simp only [add_sub_cancel_right, zero_sub] at h'
    exact h'
  -- Tr(AB) = Tr(-(BA)) = -Tr(BA) = -Tr(AB)
  have h_neg_self : Matrix.trace (A * B) = -Matrix.trace (A * B) := by
    calc Matrix.trace (A * B)
        = Matrix.trace (-(B * A)) := by rw [hab]
      _ = -Matrix.trace (B * A) := Matrix.trace_neg (B * A)
      _ = -Matrix.trace (A * B) := by rw [trace_mul_comm B A]
  -- From x = -x, we get (-x) + x = 0, i.e., x + x = 0
  have h_double : Matrix.trace (A * B) + Matrix.trace (A * B) = 0 := by
    rw [h_neg_self]      -- Now: -Tr(AB) + Tr(AB) = 0
    exact neg_add_eq_zero.mpr h_neg_self
  -- Rewrite as 2 * x = 0
  have h_two : (2 : ℂ) * Matrix.trace (A * B) = 0 := by
    rw [two_mul]
    exact h_double
  -- Since 2 ≠ 0 in ℂ, we have x = 0
  exact (mul_eq_zero.mp h_two).resolve_left two_ne_zero

/-!
## The Main Theorem

Now we combine everything. The proof splits into 16 cases:
- 4 diagonal cases (μ = ν): Use gamma squares and trace of ±I
- 12 off-diagonal cases (μ ≠ ν): Use anticommutation ⟹ trace = 0
-/

/-- Tr(γ^μ γ^ν) = 4η^μν: The fundamental two-gamma trace identity.

This is the workhorse identity for computing Feynman diagrams in QED/QCD. -/
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


/-- Moving γ⁵ through three gamma matrices picks up a factor of (-1)³ = -1.

This is the key algebraic identity:
  γ⁵ · γ^μ · γ^ν · γ^ρ = -γ^μ · γ^ν · γ^ρ · γ⁵

Each anticommutation γ⁵ γ^α = -γ^α γ⁵ contributes a factor of -1.
Three anticommutations give (-1)³ = -1. -/
lemma gamma5_move_through_three (μ ν ρ : Fin 4) :
    gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ =
    -(gammaAt μ * gammaAt ν * gammaAt ρ * gamma5) := by
  -- Move γ⁵ past γ^μ: picks up first (-1)
  have step1 : gamma5 * gammaAt μ = -(gammaAt μ * gamma5) := by
    rw [gamma5_anticommutes μ]
    exact Matrix.neg_mul (gammaAt μ) gamma5
  -- Move γ⁵ past γ^ν: picks up second (-1), total (-1)² = +1
  have step2 : gamma5 * gammaAt ν = -(gammaAt ν * gamma5) := by
    rw [gamma5_anticommutes ν]
    exact Matrix.neg_mul (gammaAt ν) gamma5
  -- Move γ⁵ past γ^ρ: picks up third (-1), total (-1)³ = -1
  have step3 : gamma5 * gammaAt ρ = -(gammaAt ρ * gamma5) := by
    rw [gamma5_anticommutes ρ]
    exact Matrix.neg_mul (gammaAt ρ) gamma5
  -- Chain the moves together
  calc gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ
      -- Rewrite γ⁵ γ^μ = -γ^μ γ⁵
      = (gamma5 * gammaAt μ) * gammaAt ν * gammaAt ρ := by noncomm_ring
    _ = (-(gammaAt μ * gamma5)) * gammaAt ν * gammaAt ρ := by rw [step1]
    _ = -(gammaAt μ * gamma5 * gammaAt ν * gammaAt ρ) := by noncomm_ring
      -- Rewrite γ⁵ γ^ν = -γ^ν γ⁵ (inside the negation)
    _ = -(gammaAt μ * (gamma5 * gammaAt ν) * gammaAt ρ) := by noncomm_ring
    _ = -(gammaAt μ * (-(gammaAt ν * gamma5)) * gammaAt ρ) := by rw [step2]
    _ = gammaAt μ * gammaAt ν * gamma5 * gammaAt ρ := by noncomm_ring
      -- Rewrite γ⁵ γ^ρ = -γ^ρ γ⁵
    _ = gammaAt μ * gammaAt ν * (gamma5 * gammaAt ρ) := by noncomm_ring
    _ = gammaAt μ * gammaAt ν * (-(gammaAt ρ * gamma5)) := by rw [step3]
    _ = -(gammaAt μ * gammaAt ν * gammaAt ρ * gamma5) := by noncomm_ring

/-- Tr(γ^μ γ^ν γ^ρ) = 0: The trace of an odd number of gamma matrices vanishes -/
lemma gamma_trace_three (μ ν ρ : Fin 4) :
    Matrix.trace (gammaAt μ * gammaAt ν * gammaAt ρ) = 0 := by
  -- Let T = Tr(γ^μ γ^ν γ^ρ)
  set T := Matrix.trace (gammaAt μ * gammaAt ν * gammaAt ρ) with hT_def

  -- Step 1: T = Tr(γ⁵γ⁵ · γ^μ γ^ν γ^ρ) since γ⁵γ⁵ = I
  have h_insert : gammaAt μ * gammaAt ν * gammaAt ρ =
                  gamma5 * gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ := by
    rw [gamma5_sq]
    noncomm_ring

  -- Step 2: Group as Tr(γ⁵ · X) where X = γ⁵ γ^μ γ^ν γ^ρ
  -- Then use cyclic property: Tr(γ⁵ · X) = Tr(X · γ⁵)
  have h_cyclic : Matrix.trace (gamma5 * gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ) =
                  Matrix.trace (gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ * gamma5) := by
    have h_assoc : gamma5 * gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ =
                   gamma5 * (gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ) := by noncomm_ring
    rw [h_assoc, trace_mul_comm]

  -- Step 3: Use γ⁵ γ^μ γ^ν γ^ρ = -γ^μ γ^ν γ^ρ γ⁵ to get
  -- γ⁵ γ^μ γ^ν γ^ρ γ⁵ = -γ^μ γ^ν γ^ρ γ⁵ γ⁵ = -γ^μ γ^ν γ^ρ
  have h_anticomm : gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ * gamma5 =
                    -(gammaAt μ * gammaAt ν * gammaAt ρ) := by
    rw [gamma5_move_through_three]
    -- Now we have -(γ^μ γ^ν γ^ρ γ⁵) * γ⁵ = -(γ^μ γ^ν γ^ρ γ⁵ γ⁵) = -(γ^μ γ^ν γ^ρ)
    have h_assoc : -(gammaAt μ * gammaAt ν * gammaAt ρ * gamma5) * gamma5 =
                   -(gammaAt μ * gammaAt ν * gammaAt ρ * (gamma5 * gamma5)) := by noncomm_ring
    rw [h_assoc, gamma5_sq]
    noncomm_ring

  -- Step 4: Chain everything: T = Tr(γ⁵γ⁵ X) = Tr(γ⁵ X γ⁵) = Tr(-X) = -T
  have h_neg_self : T = -T := by
    calc T
        = Matrix.trace (gammaAt μ * gammaAt ν * gammaAt ρ) := rfl
      _ = Matrix.trace (gamma5 * gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ) := by rw [h_insert]
      _ = Matrix.trace (gamma5 * gammaAt μ * gammaAt ν * gammaAt ρ * gamma5) := h_cyclic
      _ = Matrix.trace (-(gammaAt μ * gammaAt ν * gammaAt ρ)) := by rw [h_anticomm]
      _ = -Matrix.trace (gammaAt μ * gammaAt ν * gammaAt ρ) := Matrix.trace_neg _
      _ = -T := rfl

  -- Step 5: T = -T implies 2T = 0 implies T = 0
  have h_double : T + T = 0 := by
    rw [h_neg_self]
    exact neg_add_eq_zero.mpr h_neg_self
  have h_two : (2 : ℂ) * T = 0 := by
    rw [two_mul]
    exact h_double
  exact (mul_eq_zero.mp h_two).resolve_left two_ne_zero


set_option maxHeartbeats 400000

/-- Alternative definition: γ⁵ = iγ⁰γ¹γ²γ³ -/
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
  -- The remaining goals involve I² = -1 simplification
  all_goals try simp only [neg_neg, I_sq, neg_neg]


/-- The anticommutator {γ⁵, γ^μ} vanishes: γ⁵ γ^μ + γ^μ γ⁵ = 0  -/
lemma gamma5_gammaAt_anticommute (μ : Fin 4) :
    gamma5 * gammaAt μ + gammaAt μ * gamma5 = 0 := by
  rw [gamma5_anticommutes μ, neg_mul]
  exact neg_add_cancel (gammaAt μ * gamma5)

/-- Tr(γ⁵ γ^μ) = 0: Mixed trace with single gamma vanishes -/
lemma gamma5_gamma_trace_zero (μ : Fin 4) :
    Matrix.trace (gamma5 * gammaAt μ) = 0 := by
  exact trace_zero_of_anticommute gamma5 (gammaAt μ) (gamma5_gammaAt_anticommute μ)

end AdditionalLemmas



/-- The fiber space ℂ⁴ at each spatial point. Encodes spin (2 components)
and particle/antiparticle (2 components) degrees of freedom. -/
abbrev SpinorSpace := EuclideanSpace ℂ (Fin 4)

/-- An unbounded linear operator with explicit domain -/
structure DiracOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  domain : Submodule ℂ H
  op : domain →ₗ[ℂ] H

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Pauli-X (σₓ): spin flip operator. Real symmetric. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli-Y (σᵧ): spin flip with phase. Imaginary antisymmetric, but still Hermitian. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- Pauli-Z (σᵤ): spin measurement in z-direction. Real diagonal. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]


/-- σₓ is Hermitian: real symmetric matrix. -/
lemma pauliX_hermitian : pauliX.conjTranspose = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose, Matrix.of_apply]

/-- σᵧ is Hermitian: the ±I entries are in conjugate positions, so (σᵧ)†ᵢⱼ = conj((σᵧ)ⱼᵢ) = σᵧᵢⱼ. -/
lemma pauliY_hermitian : pauliY.conjTranspose = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, Matrix.conjTranspose, Matrix.of_apply, conj_I]

/-- σᵤ is Hermitian: real diagonal matrix. -/
lemma pauliZ_hermitian : pauliZ.conjTranspose = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose, Matrix.of_apply]

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


/-- Abstract specification of Dirac matrices -/
structure DiracMatrices where
  /-- Spatial Dirac matrices α = (α₁, α₂, α₃), coupling momentum to spinor space. -/
  alpha : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ
  /-- Mass matrix β, distinguishing particle from antiparticle components. -/
  beta : Matrix (Fin 4) (Fin 4) ℂ
  /-- αᵢ² = I: each αᵢ is an involution with eigenvalues ±1. -/
  alpha_sq : ∀ i, alpha i * alpha i = 1
  /-- β² = I: the mass matrix is an involution. -/
  beta_sq : beta * beta = 1
  /-- {αᵢ, αⱼ} = 0 for i ≠ j: distinct spatial matrices anticommute.
      This ensures (α·p)² = p₁² + p₂² + p₃² with no cross terms. -/
  alpha_anticommute : ∀ i j, i ≠ j → alpha i * alpha j + alpha j * alpha i = 0
  /-- {αᵢ, β} = 0: momentum and mass terms anticommute.
      This ensures H_D² has no αᵢβ cross terms. -/
  alpha_beta_anticommute : ∀ i, alpha i * beta + beta * alpha i = 0
  /-- αᵢ† = αᵢ: Hermiticity ensures the kinetic term is symmetric. -/
  alpha_hermitian : ∀ i, (alpha i).conjTranspose = alpha i
  /-- β† = β: Hermiticity ensures the mass term is symmetric. -/
  beta_hermitian : beta.conjTranspose = beta


/-- The standard (Dirac-Pauli) representation of the Dirac matrices -/
def standardDiracMatrices : DiracMatrices where
  alpha := fun i => match i with
    | 0 => diracAlpha1
    | 1 => diracAlpha2
    | 2 => diracAlpha3
  beta := diracBeta
  alpha_sq := by
    intro i
    fin_cases i
    · exact diracAlpha1_sq
    · exact diracAlpha2_sq
    · exact diracAlpha3_sq
  beta_sq := diracBeta_sq
  alpha_anticommute := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij          -- i = j = 0: contradiction
    · exact diracAlpha12_anticommute
    · exact diracAlpha13_anticommute
    · rw [add_comm]; exact diracAlpha12_anticommute  -- {α₂, α₁} = {α₁, α₂}
    · exact absurd rfl hij          -- i = j = 1: contradiction
    · exact diracAlpha23_anticommute
    · rw [add_comm]; exact diracAlpha13_anticommute  -- {α₃, α₁} = {α₁, α₃}
    · rw [add_comm]; exact diracAlpha23_anticommute  -- {α₃, α₂} = {α₂, α₃}
    · exact absurd rfl hij          -- i = j = 2: contradiction
  alpha_beta_anticommute := by
    intro i
    fin_cases i
    · exact diracAlpha1_beta_anticommute
    · exact diracAlpha2_beta_anticommute
    · exact diracAlpha3_beta_anticommute
  alpha_hermitian := by
    intro i
    fin_cases i
    · exact diracAlpha1_hermitian
    · exact diracAlpha2_hermitian
    · exact diracAlpha3_hermitian
  beta_hermitian := diracBeta_hermitian


set_option maxHeartbeats 20000

/-- Physical constants for the Dirac equation -/
structure DiracConstants where
  /-- Reduced Planck constant ℏ: the quantum of action. -/
  hbar : ℝ
  /-- Speed of light c: the relativistic velocity scale. -/
  c : ℝ
  /-- Particle rest mass m: determines the spectral gap. -/
  m : ℝ
  /-- ℏ > 0: required for non-trivial quantum dynamics. -/
  hbar_pos : hbar > 0
  /-- c > 0: required for Lorentz signature. -/
  c_pos : c > 0
  /-- m ≥ 0: negative mass is unphysical. Zero mass is allowed (Weyl fermions). -/
  m_nonneg : m ≥ 0

/-- Rest mass energy E₀ = mc² -/
def DiracConstants.restEnergy (κ : DiracConstants) : ℝ := κ.m * κ.c^2


/-- The Dirac Hamiltonian as an unbounded operator on a Hilbert space -/
structure DiracHamiltonian (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] extends
    DiracOperator H where
  /-- Physical constants ℏ, c, m for this particle. -/
  constants : DiracConstants
  /-- Dirac matrices satisfying the Clifford algebra. -/
  matrices : DiracMatrices
  /-- H_D is symmetric: ⟨H_D ψ, φ⟩ = ⟨ψ, H_D φ⟩ for ψ, φ in the domain.
      This follows from Hermiticity of α and β; it's the first step toward self-adjointness. -/
  symmetric : ∀ (ψ φ : domain), ⟪op ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), op φ⟫_ℂ
  /-- The domain is dense in H.
      Required for the closure of H_D to be defined on a meaningful subspace. -/
  domain_dense : Dense (domain : Set H)

/-- **Axiom**: The Dirac operator generates a strongly continuous unitary group -/
axiom dirac_generates_unitary (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) :
    ∃ (U_grp : OneParameterUnitaryGroup (H := H)) (gen : Generator U_grp),
      gen.IsSelfAdjoint ∧ gen.domain = H_D.domain

/-- The spectrum of the free Dirac operator: two half-lines separated by a gap -/
def diracSpectrum (κ : DiracConstants) : Set ℝ :=
  Set.Iic (-κ.restEnergy) ∪ Set.Ici κ.restEnergy

/-- The spectral gap: the open interval (-mc², mc²) of forbidden energies -/
def diracGap (κ : DiracConstants) : Set ℝ :=
  Set.Ioo (-κ.restEnergy) κ.restEnergy

/-- **Axiom**: Every point in the spectral gap has a bounded resolvent -/
axiom dirac_gap_in_resolvent (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) (hm : H_D.constants.m > 0) :
    ∀ E ∈ diracGap H_D.constants,
      ∃ (R : H →L[ℂ] H), ∀ (ψ : H_D.domain), R (H_D.op ψ - E • (ψ : H)) = ψ

/-- **Axiom**: The spectral measure vanishes on the gap -/
axiom dirac_spectrum_eq (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H)
    (U_grp : OneParameterUnitaryGroup (H := H)) (gen : Generator U_grp)
    (hgen : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen) :
    ∀ B ⊆ diracGap H_D.constants, MeasurableSet B → E B = 0

/-- **Axiom**: The Dirac operator has states with arbitrarily negative energy -/
axiom dirac_has_arbitrarily_negative_energy (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) (c : ℝ) :
    ∃ (ψ : H_D.domain), (ψ : H) ≠ 0 ∧ (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re < c * ‖(ψ : H)‖^2

/-- **Axiom**: The Dirac operator has states with arbitrarily positive energy -/
axiom dirac_has_arbitrarily_positive_energy (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) (c : ℝ) :
    ∃ (ψ : H_D.domain), (ψ : H) ≠ 0 ∧ (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re > c * ‖(ψ : H)‖^2

/-- The Dirac operator is unbounded below: for any c, some state has energy < c -/
theorem dirac_unbounded_below (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) :
    ∀ c : ℝ, ∃ (ψ : H_D.domain), (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re < c * ‖(ψ : H)‖^2 := by
  intro c
  obtain ⟨ψ, _, hψ⟩ := dirac_has_arbitrarily_negative_energy H H_D c
  exact ⟨ψ, hψ⟩

/-- The Dirac operator is unbounded above: for any c, some state has energy > c -/
theorem dirac_unbounded_above (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) :
    ∀ c : ℝ, ∃ (ψ : H_D.domain), (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re > c * ‖(ψ : H)‖^2 := by
  intro c
  obtain ⟨ψ, _, hψ⟩ := dirac_has_arbitrarily_positive_energy H H_D c
  exact ⟨ψ, hψ⟩

/-- Complete spectral data for a Dirac operator -/
structure DiracSpectralData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The Dirac Hamiltonian with physical constants and domain. -/
  hamiltonian : DiracHamiltonian H
  /-- The strongly continuous unitary group generated by H_D. -/
  U_grp : OneParameterUnitaryGroup (H := H)
  /-- The infinitesimal generator of U_grp (related to H_D by factors of i and ℏ). -/
  gen : Generator U_grp
  /-- The generator is self-adjoint, enabling the spectral theorem. -/
  gen_sa : gen.IsSelfAdjoint
  /-- The spectral measure: E(B) projects onto states with energy in B. -/
  E : Set ℝ → H →L[ℂ] H
  /-- E is the spectral measure associated to gen via the spectral theorem. -/
  E_spectral : FunctionalCalculus.IsSpectralMeasureFor E gen
  /-- The generator's domain equals the Hamiltonian's domain. -/
  domain_eq : gen.domain = hamiltonian.domain

/-- Time evolution operator U(t) = e^{-itH_D/ℏ}  -/
def diracTimeEvolution (data : DiracSpectralData H) (t : ℝ) : H →L[ℂ] H :=
  data.U_grp.U t

/-- Time evolution is unitary: U(t)*U(t) = U(t)U(t)* = 1 -/
theorem dirac_evolution_unitary (data : DiracSpectralData H) (t : ℝ) :
    Unitary (data.U_grp.U t) := by
  constructor
  · -- adjoint * U = 1: show U(t) is an isometry
    ext ψ
    apply ext_inner_left ℂ
    intro φ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact (data.U_grp.unitary t φ ψ)
  · -- U * adjoint = 1: use U(t)* = U(-t) and group law
    ext ψ
    apply ext_inner_left ℂ
    intro φ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, ← @inverse_eq_adjoint]
    exact data.U_grp.unitary (-t) φ ψ


/-- Functional calculus for the Dirac operator: f(H_D) = ∫f(s)dE(s) -/
noncomputable def diracFunctionalCalculus (data : DiracSpectralData H) (f : ℝ → ℂ) :
    FunctionalCalculus.functionalDomainSubmodule data.E data.E_spectral.toIsSpectralMeasure data.E_spectral.proj_univ f →ₗ[ℂ] H :=
  FunctionalCalculus.functionalCalculus data.E data.E_spectral.toIsSpectralMeasure data.E_spectral.proj_univ f

/-- The sign function for splitting electron and positron subspaces -/
noncomputable def signFunction (κ : DiracConstants) : ℝ → ℂ := fun s =>
  if s ≥ κ.restEnergy then 1
  else if s ≤ -κ.restEnergy then -1
  else 0  -- in the gap, but E is zero there anyway

/-- Projection onto the electron (positive energy) subspace: E([mc², ∞)) -/
def electronProjection (data : DiracSpectralData H) : H →L[ℂ] H :=
  data.E (Set.Ici data.hamiltonian.constants.restEnergy)

/-- Projection onto the positron (negative energy) subspace: E((-∞, -mc²]) -/
def positronProjection (data : DiracSpectralData H) : H →L[ℂ] H :=
  data.E (Set.Iic (-data.hamiltonian.constants.restEnergy))

/-- Specification of a spectral measure for a self-adjoint generator -/
structure IsSpectralMeasureFor (E : Set ℝ → H →L[ℂ] H)
    {U_grp : OneParameterUnitaryGroup (H := H)} (gen : Generator U_grp) : Prop where
  /-- E(B)E(C) = E(B ∩ C): spectral projections multiply via intersection. -/
  proj_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C)
  /-- E(B) is self-adjoint: ⟨E(B)ψ, φ⟩ = ⟨ψ, E(B)φ⟩. -/
  proj_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ
  /-- E(ℝ) = 1: the spectral measure is normalized (total probability 1). -/
  proj_univ : E Set.univ = 1
  /-- E(B ∪ C) = E(B) + E(C) for disjoint B, C: finite additivity. -/
  proj_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
             E (B ∪ C) = E B + E C
  /-- Strong operator continuity from the right for the spectral family. -/
  proj_sot : ∀ ψ t₀, Filter.Tendsto (fun t => E (Set.Iic t) ψ) (nhdsWithin t₀ (Set.Ioi t₀)) (nhds (E (Set.Iic t₀) ψ))
  /-- The defining relationship: U(t) = ∫e^{its}dE(s).
      This connects the unitary group to its spectral decomposition. -/
  unitary_eq_integral : ∀ (t : ℝ) (ψ : H),
    ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ s, Complex.exp (I * t * s) ∂(BochnerRoute.spectral_scalar_measure E ψ ⟨proj_mul, proj_sa, proj_sot, proj_empty, proj_univ, proj_add⟩)

/-- Electron and positron subspaces are orthogonal: E₊ E₋ = 0 -/
theorem electron_positron_orthogonal (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) :
    electronProjection data * positronProjection data = 0 := by
  unfold electronProjection positronProjection
  -- The sets [mc², ∞) and (-∞, -mc²] are disjoint when mc² > 0
  have h_disj : Disjoint (Set.Ici data.hamiltonian.constants.restEnergy)
                         (Set.Iic (-data.hamiltonian.constants.restEnergy)) := by
    rw [Set.disjoint_iff]
    intro x ⟨hx_ge, hx_le⟩
    simp only [Set.mem_Ici, Set.mem_Iic] at hx_ge hx_le
    -- x ≥ mc² and x ≤ -mc² requires mc² ≤ 0, contradicting mc² > 0
    have h_pos : data.hamiltonian.constants.restEnergy > 0 := by
      unfold DiracConstants.restEnergy
      apply mul_pos hm
      exact sq_pos_of_pos data.hamiltonian.constants.c_pos
    linarith
  -- Disjoint spectral sets give orthogonal projections
  exact FunctionalCalculus.spectral_projection_disjoint data.E
    data.E_spectral.toIsSpectralMeasure
    (Set.Ici data.hamiltonian.constants.restEnergy)
    (Set.Iic (-data.hamiltonian.constants.restEnergy))
    measurableSet_Ici measurableSet_Iic h_disj

/-- **Axiom**: The spectral measure is supported on the spectrum  -/
axiom spectral_measure_supported_on_spectrum
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : FunctionalCalculus.IsSpectralMeasureFor E gen)
    (B : Set ℝ) (hB : MeasurableSet B)
    -- Every point in B has a bounded resolvent (is in resolvent set)
    (h_resolvent : ∀ s ∈ B, ∃ (R : H →L[ℂ] H),
        ∀ (ψ : gen.domain), R (gen.op ψ - s • (ψ : H)) = ψ) :
    E B = 0

/-- **Axiom**: Every point in the Dirac spectral gap has a bounded resolvent -/
axiom dirac_gap_in_resolvent_set (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0)
    (s : ℝ)
    (hs_lower : -data.hamiltonian.constants.restEnergy < s)
    (hs_upper : s < data.hamiltonian.constants.restEnergy) :
    ∃ (R : H →L[ℂ] H), ∀ (ψ : data.gen.domain),
        R (data.gen.op ψ - s • (ψ : H)) = ψ

/-- The spectral gap has zero spectral measure: E((-mc², mc²)) = 0 -/
theorem dirac_spectral_gap_zero (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) :
    data.E (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                    data.hamiltonian.constants.restEnergy) = 0 := by
  apply spectral_measure_supported_on_spectrum data.gen data.gen_sa data.E data.E_spectral
  · exact measurableSet_Ioo  -- The open interval is measurable
  · intro s ⟨hs_lower, hs_upper⟩
    -- Every point in the gap has bounded resolvent
    exact dirac_gap_in_resolvent_set data hm s hs_lower hs_upper

/-- Electron and positron projections are complete: E₊ + E₋ = 1 (for m > 0) -/
theorem electron_positron_complete (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) :
    electronProjection data + positronProjection data = 1 := by
  unfold electronProjection positronProjection
  -- E([mc², ∞)) + E((-∞, -mc²]) = E(ℝ) = 1
  -- because ℝ = [mc², ∞) ∪ (-∞, -mc²] ∪ (-mc², mc²) and E(gap) = 0

  -- Step 1: mc² > 0
  have h_pos : data.hamiltonian.constants.restEnergy > 0 := by
    unfold DiracConstants.restEnergy
    apply mul_pos hm
    exact sq_pos_of_pos data.hamiltonian.constants.c_pos

  -- Step 2: The gap contributes nothing
  have h_gap : data.E (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                               data.hamiltonian.constants.restEnergy) = 0 :=
    dirac_spectral_gap_zero data hm

  -- Step 3: The three sets partition ℝ
  have h_union : Set.Ici data.hamiltonian.constants.restEnergy ∪
                 Set.Iic (-data.hamiltonian.constants.restEnergy) ∪
                 Set.Ioo (-data.hamiltonian.constants.restEnergy)
                         data.hamiltonian.constants.restEnergy = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioo, Set.mem_univ, iff_true]
    -- Trichotomy: x ≥ mc², x ≤ -mc², or x ∈ (-mc², mc²)
    by_cases h : x ≥ data.hamiltonian.constants.restEnergy
    · left; left; exact h
    · by_cases h' : x ≤ -data.hamiltonian.constants.restEnergy
      · left; right; exact h'
      · right
        push_neg at h h'
        exact ⟨h', h⟩

  -- Step 4a: Electron and positron supports are disjoint
  have h_disj1 : Disjoint (Set.Ici data.hamiltonian.constants.restEnergy)
                          (Set.Iic (-data.hamiltonian.constants.restEnergy)) := by
    rw [Set.disjoint_iff]
    intro x ⟨hx_ge, hx_le⟩
    simp only [Set.mem_Ici, Set.mem_Iic] at hx_ge hx_le
    linarith  -- x ≥ mc² and x ≤ -mc² contradicts mc² > 0

  -- Step 4b: (Electron ∪ positron) is disjoint from gap
  have h_disj2 : Disjoint (Set.Ici data.hamiltonian.constants.restEnergy ∪
                           Set.Iic (-data.hamiltonian.constants.restEnergy))
                          (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                                   data.hamiltonian.constants.restEnergy) := by
    rw [Set.disjoint_iff]
    intro x ⟨hx_union, hx_gap⟩
    simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioo] at hx_union hx_gap
    cases hx_union with
    | inl h => linarith [hx_gap.2]  -- x ≥ mc² contradicts x < mc²
    | inr h => linarith [hx_gap.1]  -- x ≤ -mc² contradicts x > -mc²

  -- Step 5: Chain of equalities using additivity
  calc data.E (Set.Ici data.hamiltonian.constants.restEnergy) +
       data.E (Set.Iic (-data.hamiltonian.constants.restEnergy))
      -- Additivity: E(A) + E(B) = E(A ∪ B) for disjoint A, B
      = data.E (Set.Ici data.hamiltonian.constants.restEnergy ∪
                Set.Iic (-data.hamiltonian.constants.restEnergy)) := by
          rw [← data.E_spectral.proj_add _ _ measurableSet_Ici measurableSet_Iic h_disj1]
      -- Add zero (will become E(gap))
    _ = data.E (Set.Ici data.hamiltonian.constants.restEnergy ∪
                Set.Iic (-data.hamiltonian.constants.restEnergy)) + 0 := by abel
      -- Replace 0 with E(gap)
    _ = data.E (Set.Ici data.hamiltonian.constants.restEnergy ∪
                Set.Iic (-data.hamiltonian.constants.restEnergy)) +
        data.E (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                        data.hamiltonian.constants.restEnergy) := by rw [h_gap]
      -- Additivity again: E(A ∪ B) + E(C) = E(A ∪ B ∪ C) for disjoint (A ∪ B), C
    _ = data.E Set.univ := by
        rw [← data.E_spectral.proj_add _ _ (measurableSet_Ici.union measurableSet_Iic)
            measurableSet_Ioo h_disj2, h_union]
      -- Normalization: E(ℝ) = 1
    _ = 1 := data.E_spectral.proj_univ


/-- Relativistic energy as a function of momentum: E(p) = √((pc)² + (mc²)²) -/
noncomputable def relativisticEnergy (κ : DiracConstants) (p : ℝ) : ℝ :=
  Real.sqrt ((p * κ.c)^2 + κ.restEnergy^2)

/-- Positive energy branch: E₊(p) = +√((pc)² + (mc²)²) -/
noncomputable def positiveEnergy (κ : DiracConstants) (p : ℝ) : ℝ := relativisticEnergy κ p

/-- Negative energy branch: E₋(p) = -√((pc)² + (mc²)²) -/
noncomputable def negativeEnergy (κ : DiracConstants) (p : ℝ) : ℝ := -relativisticEnergy κ p

/-- The relativistic energy is always at least mc² in magnitude.-/
theorem energy_geq_rest_mass (κ : DiracConstants) (p : ℝ) :
    relativisticEnergy κ p ≥ κ.restEnergy := by
  unfold relativisticEnergy DiracConstants.restEnergy
  -- Need: √((pc)² + (mc²)²) ≥ mc²
  have h_nonneg : κ.m * κ.c^2 ≥ 0 := by
    apply mul_nonneg κ.m_nonneg
    exact sq_nonneg κ.c
  have h_inner_nonneg : (p * κ.c)^2 + (κ.m * κ.c^2)^2 ≥ 0 := by positivity
  rw [ge_iff_le]
  -- Equivalent to (mc²)² ≤ (pc)² + (mc²)², i.e., 0 ≤ (pc)²
  rw [Real.le_sqrt h_nonneg h_inner_nonneg]
  nlinarith [sq_nonneg (p * κ.c)]

/-- The Dirac operator is NOT semibounded (bounded below). -/
theorem dirac_not_semibounded (H_D : DiracHamiltonian H) :
    ¬∃ c : ℝ, ∀ (ψ : H_D.domain), c * ‖(ψ : H)‖^2 ≤ (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re := by
  push_neg
  intro c
  -- For any c, there exists ψ with energy expectation < c‖ψ‖²
  obtain ⟨ψ, hψ⟩ := dirac_unbounded_below H H_D c
  exact ⟨ψ, hψ⟩

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The spectral gap contains no spectrum (placeholder version) -/
theorem dirac_spectral_gap (H_D : DiracOperator H) (m c_light : ℝ) (hm : m > 0) (hc : c_light > 0) :
    ∀ E : ℝ, -m * c_light^2 < E → E < m * c_light^2 →
      ∃ (inv : H →ₗ[ℂ] H_D.domain), True := by
  intro E _ _
  exact ⟨0, trivial⟩  -- placeholder; real statement needs resolvent machinery

/-- The Cayley transform of a self-adjoint generator is unitary. -/
theorem dirac_cayley_unitary
    (U_grp : @OneParameterUnitaryGroup H _ _ )
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    Unitary (cayleyTransform gen hsa) :=
  cayleyTransform_unitary gen hsa


section DiracCurrent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Abstract specification of gamma matrices satisfying the Minkowski-Clifford algebra. -/
structure GammaMatrices where
  gamma : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ
  clifford_minkowski : ∀ μ ν, gamma μ * gamma ν + gamma ν * gamma μ =
    2 • (if μ = ν then (if μ = 0 then 1 else -1) • (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0)
  gamma0_hermitian : (gamma 0).conjTranspose = gamma 0
  gammaI_antihermitian : ∀ i : Fin 3, (gamma i.succ).conjTranspose = -gamma i.succ


set_option maxHeartbeats 78703

/-- The standard (Dirac) representation of the gamma matrices. -/
def standardGammaMatrices : GammaMatrices where
  gamma := fun μ => match μ with
    | 0 => gamma0
    | 1 => gamma1
    | 2 => gamma2
    | 3 => gamma3
  clifford_minkowski := by
    intro μ ν
    -- 16 cases: all pairs (μ, ν) ∈ {0,1,2,3} × {0,1,2,3}
    fin_cases μ <;> fin_cases ν
    -- Each case applies the appropriate clifford_XY lemma
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, one_smul]; exact clifford_00
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, zero_ne_one, ↓reduceIte, nsmul_zero]; exact clifford_01
    · simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_02
    · simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_03
    · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, one_ne_zero, ↓reduceIte, nsmul_zero]; exact clifford_10
    · simp only [Fin.mk_one, Fin.isValue, ↓reduceIte, one_ne_zero, Int.reduceNeg, neg_smul,
        one_smul, smul_neg, nsmul_eq_mul, Nat.cast_ofNat, mul_one]; rw [neg_two_eq_smul]; exact clifford_11
    · simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_12
    · simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_13
    · simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.isValue, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_20
    · simp only [Fin.reduceFinMk, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_21
    · simp only [Fin.reduceFinMk, ↓reduceIte, Fin.isValue, Fin.reduceEq, Int.reduceNeg, neg_smul,
        one_smul, smul_neg, nsmul_eq_mul, Nat.cast_ofNat, mul_one]; rw [neg_two_eq_smul]; exact clifford_22
    · simp only [Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_23
    · simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.isValue, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_30
    · simp only [Fin.reduceFinMk, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_31
    · simp only [Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_32
    · simp only [Fin.reduceFinMk, ↓reduceIte, Fin.isValue, Fin.reduceEq, Int.reduceNeg, neg_smul,
        one_smul, smul_neg, nsmul_eq_mul, Nat.cast_ofNat, mul_one]; rw [neg_two_eq_smul]; exact clifford_33
  gamma0_hermitian := gamma0_hermitian_proof
  gammaI_antihermitian := by
    intro i
    fin_cases i
    · exact gamma1_antihermitian
    · exact gamma2_antihermitian
    · exact gamma3_antihermitian


/-- A spinor field assigns a 4-component spinor to each spacetime point.-/
structure SpinorField where
  ψ : Spacetime → (Fin 4 → ℂ)

/-- A spinor field with integrability condition.-/
structure SpinorField' where
  /-- The four-component spinor at each spacetime point: x^μ ↦ ψ_a(x). -/
  ψ : (Fin 4 → ℝ) → (Fin 4 → ℂ)
  /-- Square-integrable on each spatial slice: ∫|ψ(t,x)|² d³x < ∞ for all t. -/
  integrable : ∀ t : ℝ, Integrable (fun x : Fin 3 → ℝ =>
    ‖ψ (Fin.cons t (fun i => x i))‖^2) volume

/-- The Dirac adjoint: ψ̄ = ψ†γ⁰.-/
noncomputable def diracAdjoint (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun a => ∑ b, star (ψ b) * (Γ.gamma 0) b a

/-- The Dirac current 4-vector: j^μ = ψ̄γ^μψ. -/
noncomputable def diracCurrent (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun μ => ∑ a : Fin 4, ∑ b : Fin 4, star (ψ a) * (Γ.gamma 0 * Γ.gamma μ) a b * ψ b

/-- γ⁰ is an involution: (γ⁰)² = I.-/
lemma gamma0_sq (Γ : GammaMatrices) : Γ.gamma 0 * Γ.gamma 0 = 1 := by
  have hcliff := Γ.clifford_minkowski 0 0
  simp only [↓reduceIte, one_smul, two_nsmul] at hcliff
  -- hcliff : γ⁰γ⁰ + γ⁰γ⁰ = 2·I, so 2(γ⁰)² = 2I, so (γ⁰)² = I
  have : (2 : ℂ) • (Γ.gamma 0 * Γ.gamma 0) = (2 : ℂ) • 1 := by
    calc (2 : ℂ) • (Γ.gamma 0 * Γ.gamma 0)
        = Γ.gamma 0 * Γ.gamma 0 + Γ.gamma 0 * Γ.gamma 0 := by rw [two_smul]
      _ = 1 + 1 := hcliff
      _ = (2 : ℂ) • 1 := by rw [two_smul]
  exact smul_right_injective (Matrix (Fin 4) (Fin 4) ℂ) (two_ne_zero) this

/-- **FUNDAMENTAL THEOREM**: The zeroth component of the current equals ψ†ψ. -/
theorem current_zero_eq_norm_sq (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) :
    diracCurrent Γ ψ 0 = ∑ a, ‖ψ a‖^2 := by
  unfold diracCurrent
  -- Use (γ⁰)² = I to simplify γ⁰γ⁰ to the identity matrix
  simp only [gamma0_sq Γ, Matrix.one_apply, RCLike.star_def, mul_ite, mul_one, mul_zero,
             ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
             ofReal_sum, ofReal_pow]
  congr 1
  funext a
  -- (ψ_a)* · ψ_a = |ψ_a|²
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  exact ofReal_pow ‖ψ a‖ 2

/-- **FUNDAMENTAL THEOREM**: The probability density j⁰ is non-negative. -/
theorem current_zero_nonneg (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) :
    0 ≤ (diracCurrent Γ ψ 0).re := by
  rw [current_zero_eq_norm_sq]
  simp only [ofReal_sum, ofReal_pow, re_sum]
  -- Sum of |ψ_a|² ≥ 0 because each term is ≥ 0
  apply Finset.sum_nonneg
  intro a _
  simp only [← ofReal_pow, Complex.ofReal_re]
  exact sq_nonneg ‖ψ a‖

/-- The probability density vanishes if and only if the spinor is zero.-/
theorem current_zero_eq_zero_iff (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) :
    diracCurrent Γ ψ 0 = 0 ↔ ψ = 0 := by
  rw [current_zero_eq_norm_sq]
  constructor
  · intro h
    ext a
    -- If Σ|ψ_a|² = 0 with all terms ≥ 0, then each term = 0
    have h_nonneg : ∀ i : Fin 4, 0 ≤ ‖ψ i‖^2 := fun i => sq_nonneg _
    have h_sum_eq : ∑ i : Fin 4, ‖ψ i‖^2 = 0 := by
      exact Eq.symm ((fun {z w} => ofReal_inj.mp) (id (Eq.symm h)))
    have h_each_zero := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h_nonneg i) |>.mp h_sum_eq
    have : ‖ψ a‖^2 = 0 := h_each_zero a (Finset.mem_univ a)
    exact norm_eq_zero.mp (pow_eq_zero this)
  · intro h
    simp [h]

/-- The probability density ρ = j⁰ = ψ†ψ as a real number. -/
noncomputable def probabilityDensity (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : ℝ :=
  (diracCurrent Γ ψ 0).re

/-- The probability current (spatial components): jⁱ = ψ̄γⁱψ.-/
noncomputable def probabilityCurrent (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 3 → ℂ :=
  fun i => diracCurrent Γ ψ i.succ


end DiracCurrent

section ContinuityEquation

/-- A point in 4-dimensional spacetime: x^μ = (t, x, y, z).-/
abbrev Spacetime := Fin 4 → ℝ

/-- Standard basis vector e_μ in ℝ⁴.-/
def stdBasis (μ : Fin 4) : Spacetime := fun ν => if μ = ν then 1 else 0

/-- The four-divergence ∂_μ j^μ = ∂₀j⁰ + ∂₁j¹ + ∂₂j² + ∂₃j³.-/
noncomputable def fourDivergence (j : (Fin 4 → ℝ) → (Fin 4 → ℂ)) : (Fin 4 → ℝ) → ℂ :=
  fun x => ∑ μ, deriv (fun t => j (Function.update x μ t) μ) (x μ)

/-- Partial derivative of a spinor field: ∂_μ ψ. -/
noncomputable def partialDeriv' (μ : Fin 4) (ψ : Spacetime → (Fin 4 → ℂ)) (x : Spacetime) : Fin 4 → ℂ :=
  fun a => fderiv ℝ (fun y => ψ y a) x (stdBasis μ)

/-- **Axiom**: The Dirac equation implies current conservation: ∂_μ j^μ = 0.-/
axiom dirac_current_conserved (Γ : GammaMatrices) (ψ : SpinorField) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x) :
    ∀ x, fourDivergence (fun x => diracCurrent Γ (ψ.ψ x)) x = 0

/-- Construct a spacetime point from time t and spatial position x = (x¹, x², x³) -/
def spacetimePoint (t : ℝ) (x : Fin 3 → ℝ) : Spacetime :=
  ![t, x 0, x 1, x 2]

/-- Total probability at time t: P(t) = ∫ρ(t,x) d³x = ∫ψ†ψ d³x -/
noncomputable def totalProbability (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) : ℝ :=
  ∫ x : Fin 3 → ℝ, probabilityDensity Γ (ψ.ψ (spacetimePoint t x)) ∂volume

/-- **Axiom**: Leibniz integral rule — differentiation commutes with integration.-/
axiom leibniz_integral_rule (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) :
    deriv (totalProbability Γ ψ) t =
    ∫ x : Fin 3 → ℝ, deriv (fun s => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) t ∂volume

/-- **Axiom**: The continuity equation ∂ρ/∂t = -∇·j. -/
axiom continuity_equation (Γ : GammaMatrices) (ψ : SpinorField) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x)
    (t : ℝ) (x : Fin 3 → ℝ) :
    deriv (fun s => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) t =
    -(∑ i : Fin 3, deriv (fun s => (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re) (x i))

/-- **Axiom**: The divergence theorem with vanishing boundary conditions.  -/
axiom divergence_integral_vanishes (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ)
    (h_vanish : Filter.Tendsto (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint t x)))
                               (Filter.cocompact _) (nhds 0)) :
    ∫ x : Fin 3 → ℝ, (∑ i : Fin 3, deriv (fun s => (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re) (x i)) ∂volume = 0

/-- **MAIN THEOREM**: Total probability is conserved: d/dt ∫ρ d³x = 0.

**Hypotheses**:
- `h_dirac`: ψ satisfies the Dirac equation
- `h_vanish`: ψ decays at spatial infinity (physically reasonable)  -/
theorem probability_conserved (Γ : GammaMatrices) (ψ : SpinorField) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x)
    (h_vanish : ∀ t, Filter.Tendsto (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint t x)))
                              (Filter.cocompact _) (nhds 0)) :
    ∀ t, deriv (totalProbability Γ ψ) t = 0 := by
  intro t
  -- Step 1: Move derivative inside integral (Leibniz rule)
  rw [leibniz_integral_rule]
  -- Step 2: Apply continuity equation ∂₀ρ = -∇·j
  have h_cont := continuity_equation Γ ψ m h_dirac t
  simp_rw [h_cont]
  -- Step 3: Integral of negative divergence
  rw [MeasureTheory.integral_neg]
  -- Step 4: Divergence integral vanishes by boundary conditions
  rw [divergence_integral_vanishes Γ ψ t (h_vanish t)]
  simp

end ContinuityEquation

namespace BornRuleConnection

/-- The normalized probability density: P(x,t) = ρ(x,t) / ∫ρ d³x  -/
noncomputable def normalizedProbability (Γ : GammaMatrices) (ψ : SpinorField)
    (t : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  probabilityDensity Γ (ψ.ψ (spacetimePoint t x)) / totalProbability Γ ψ t

/-- **BORN'S RULE**: The normalized probability density is a valid probability distribution.

**The theorem**: For any non-trivial solution ψ of the Dirac equation:
1. P(x,t) ≥ 0 for all x (non-negativity)
2. ∫P(x,t) d³x = 1 (normalization) -/
theorem born_rule_valid (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x)
    (h_nonzero : totalProbability Γ ψ t ≠ 0) :
    -- Probability is non-negative
    (∀ x, 0 ≤ normalizedProbability Γ ψ t x) ∧
    -- Probability integrates to 1
    (∫ x, normalizedProbability Γ ψ t x ∂volume = 1) := by
  constructor
  · -- Part 1: Non-negativity
    intro x
    unfold normalizedProbability
    -- P = ρ(x)/∫ρ ≥ 0 because both numerator and denominator are ≥ 0
    apply div_nonneg
    · -- ρ(x) = (j⁰).re ≥ 0
      exact current_zero_nonneg Γ _
    · -- ∫ρ ≥ 0 (integral of non-negative function)
      unfold totalProbability
      apply MeasureTheory.integral_nonneg
      intro y
      exact current_zero_nonneg Γ _
  · -- Part 2: Normalization to 1
    unfold normalizedProbability
    -- ∫(ρ/∫ρ) = (1/∫ρ) · ∫ρ = 1
    simp only [div_eq_mul_inv]
    rw [MeasureTheory.integral_mul_const]
    -- (∫ρ) · (∫ρ)⁻¹ = 1 (using h_nonzero)
    exact
      CommGroupWithZero.mul_inv_cancel
        (∫ (a : Fin 3 → ℝ), probabilityDensity Γ (ψ.ψ (spacetimePoint t a))) h_nonzero

end BornRuleConnection

end PaulDirac
