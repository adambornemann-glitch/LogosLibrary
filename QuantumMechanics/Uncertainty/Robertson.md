# Robertson's Uncertainty Principle: A Companion to the Lean 4 Formalization

## Abstract
*picks up the pen again*

Certainly. Here's an abstract that situates the work historically and conveys its significance:

---

## Abstract

In July 1929, Howard Percy Robertson published a two-page note in *Physical Review* titled simply "The Uncertainty Principle." Building on Werner Heisenberg's 1927 insight and Earle Kennard's rigorous position-momentum formulation, Robertson proved that uncertainty is not merely a property of conjugate variables like position and momentum, but a universal feature of any pair of non-commuting quantum observables. His inequality,

$$\sigma_A \cdot \sigma_B \geq \frac{1}{2}\left|\langle[A,B]\rangle\right|$$

established that the product of uncertainties in two measurements is bounded below by the expectation value of their commutator — a purely algebraic object encoding the failure of the observables to be simultaneously measurable.

Robertson's relation is among the most important results in quantum mechanics. It explains why atoms are stable (electrons cannot simultaneously have definite position at the nucleus and zero momentum), why the vacuum fluctuates (field amplitudes and their rates of change do not commute), and why quantum cryptography is secure (measurement of one polarization disturbs another). The inequality has been extended by Schrödinger (1930), generalized to entropic measures by Deutsch (1983) and others, and strengthened for mixed states by Maccone and Pati (2014). It remains a cornerstone of quantum information theory, metrology, and foundations.

This document accompanies a complete formalization of Robertson's theorem in the Lean 4 theorem prover, machine-verified against the Mathlib mathematical library. The formalization reveals a fact often obscured in textbook treatments: **Robertson's inequality requires only that the operators be symmetric, not self-adjoint.** Self-adjointness — the stronger condition guaranteeing real eigenvalues and a complete spectral decomposition — is unnecessary. The proof relies solely on the Cauchy-Schwarz inequality and the algebraic properties of commutators, making it a theorem of Hilbert space geometry rather than spectral theory.

This distinction matters. Symmetric-but-not-self-adjoint operators arise naturally in quantum mechanics on bounded domains, in PT-symmetric quantum theory, and in various regularization schemes. The uncertainty relation holds for all of them.

The formalization comprises approximately 1,200 lines of Lean 4 code, proving every step from first principles: the preservation of symmetry under expectation-value shifts, the purely imaginary character of commutator expectations, the decomposition of inner products into commutator and anticommutator contributions, and the final assembly via Cauchy-Schwarz. No axioms beyond the standard Mathlib foundations are invoked. The result is a machine-certified proof that will remain valid as long as the axioms of mathematics hold.

Author: Adam Bornemann

---

## Overview

This document provides an English-language companion to a machine-verified proof of Robertson's generalized uncertainty principle, formalized in the Lean 4 theorem prover using the Mathlib library.

The formalization consists of two primary files:

| File | Purpose |
|------|---------|
| `Core.lean` | Foundational definitions, structures, and helper lemmas |
| `Robertson.lean` | The main theorem and its complete proof |

**The Central Result:**

For any two symmetric operators A and B on a Hilbert space, and any normalized quantum state ψ in the appropriate domain:

$$\sigma_A \cdot \sigma_B \geq \frac{1}{2}\left|\langle\psi, [A,B]\psi\rangle\right|$$

where:
- σ_A and σ_B are standard deviations (uncertainties)
- [A,B] = AB − BA is the commutator
- ⟨ψ, ·⟩ denotes the inner product with state ψ

---

## A Critical Mathematical Insight: Symmetry Suffices

**This formalization reveals that Robertson's inequality requires only SYMMETRIC operators, not the stronger condition of SELF-ADJOINTNESS.**

This distinction, often glossed over in physics textbooks, has significant mathematical implications.

### Definitions

**Symmetric Operator:**
An operator A with domain D is *symmetric* if for all ψ, φ ∈ D:
$$\langle A\psi, \varphi\rangle = \langle\psi, A\varphi\rangle$$

**Self-Adjoint Operator:**
An operator A is *self-adjoint* if it is symmetric AND the domain of A equals the domain of its adjoint A†.

### Why This Matters

| Property | Symmetric | Self-Adjoint |
|----------|-----------|--------------|
| Can move operator across inner product | ✓ | ✓ |
| Real eigenvalues guaranteed | ✗ | ✓ |
| Complete orthonormal eigenbasis | ✗ | ✓ |
| Spectral theorem applies | ✗ | ✓ |
| Uncertainty relation holds | ✓ | ✓ |

The proof of Robertson's inequality uses ONLY the ability to move operators across inner products. It never invokes the spectral theorem, never requires real eigenvalues, and never needs a complete eigenbasis.

**Physical Example:**
The momentum operator P = −iℏ(d/dx) on the interval [0,1] is symmetric for many boundary conditions, but self-adjoint only for specific choices (e.g., periodic boundary conditions). Robertson's inequality holds for ALL symmetric cases.

---

## File 1: Core.lean — Foundations

### Section 1: Imports and Dependencies

The formalization builds on Mathlib's:
- `InnerProductSpace` — Hilbert space structure
- `LinearMap` — Unbounded operators  
- `ContinuousLinearMap` — Bounded operators
- `Submodule` — Operator domains
- Complex number and real analysis libraries

### Section 2: Core Quantum Structures

#### Normalized States

```
structure NormalizedState (H : Type*) where
  vec : H
  normalized : ‖vec‖ = 1
```

**Mathematical Meaning:** A unit vector |ψ⟩ in a complex Hilbert space H. The normalization condition ‖ψ‖ = 1 ensures Born rule probabilities sum to unity.

**Status:** DEFINITION (not an axiom or theorem)

#### Bounded Observables

```
structure Observable (H : Type*) where
  op : H →L[ℂ] H                    -- Continuous linear map
  SymmetricOperator : IsSelfAdjoint op
```

**Mathematical Meaning:** A bounded linear operator that equals its adjoint. Examples include spin operators, bounded potentials, and projection operators.

**Status:** DEFINITION

#### Unbounded Observables

```
structure UnboundedObservable (H : Type*) where
  op : H →ₗ[ℂ] H                           -- Linear map (not necessarily continuous)
  domain : Submodule ℂ H                   -- Dense domain
  dense : Dense (domain : Set H)
  SymmetricOperator : ∀ (ψ φ : H), ψ ∈ domain → φ ∈ domain →
    ⟪op ψ, φ⟫_ℂ = ⟪ψ, op φ⟫_ℂ
```

**Mathematical Meaning:** A linear operator defined on a dense subspace, satisfying the symmetry condition. This is the key structure for position, momentum, and Hamiltonian operators.

**Critical Note:** The `SymmetricOperator` field requires only SYMMETRY:
$$\langle A\psi, \varphi\rangle = \langle\psi, A\varphi\rangle$$

This is strictly weaker than self-adjointness. The entire Robertson proof works with this weaker hypothesis.

**Status:** DEFINITION

### Section 3: Statistical Quantities

#### Expectation Value

```
def unboundedExpectationValue (A : UnboundedObservable H) (ψ : H) : ℝ :=
  (⟪ψ, A.op ψ⟫_ℂ).re
```

**Mathematical Meaning:** ⟨A⟩_ψ = Re⟨ψ|A|ψ⟩

For symmetric operators on normalized states, this is always real.

**Status:** DEFINITION

#### Variance

```
def unboundedVariance (A : UnboundedObservable H) (ψ : H) (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : ℝ :=
  let A_exp := unboundedExpectationValue A ψ h_norm hψ
  let A' := A.op - A_exp • (1 : H →ₗ[ℂ] H)
  ‖A' ψ‖^2
```

**Mathematical Meaning:** Var(A) = ‖(A − ⟨A⟩I)ψ‖² = ⟨A²⟩ − ⟨A⟩²

**Status:** DEFINITION

#### Standard Deviation

```
def unboundedStandardDeviation (A : UnboundedObservable H) (ψ : H) : ℝ :=
  Real.sqrt (unboundedVariance A ψ h_norm hψ)
```

**Mathematical Meaning:** σ_A = √Var(A)

**Status:** DEFINITION

### Section 4: Algebraic Operations

#### Commutator

For bounded operators:
```
def commutator (A B : H →L[ℂ] H) : H →L[ℂ] H :=
  A ∘L B - B ∘L A
```

**Mathematical Meaning:** [A,B] = AB − BA

**Status:** DEFINITION

#### Anticommutator

```
def anticommutator (A B : H →L[ℂ] H) : H →L[ℂ] H :=
  A ∘L B + B ∘L A
```

**Mathematical Meaning:** {A,B} = AB + BA

**Status:** DEFINITION

---

## Key Lemmas in Core.lean

### Lemma: Symmetry Preserved Under Real Shifts

```
lemma isSymmetric_sub_smul_of_real (A : H →ₗ[ℂ] H) (λ : ℝ) (D : Submodule ℂ H)
    (hA_sym : ∀ v w, v ∈ D → w ∈ D → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ) :
    ∀ v w, v ∈ D → w ∈ D → ⟪(A - λ • 1) v, w⟫_ℂ = ⟪v, (A - λ • 1) w⟫_ℂ
```

**Plain English:** If A is symmetric and λ is a real number, then A − λI is also symmetric.

**Why It Matters:** This lets us shift operators by their expectation values (which are real) while preserving the symmetry needed for the proof.

**Status:** PROVEN THEOREM ✓

### Lemma: Commutator Expectation is Purely Imaginary

```
lemma expectation_commutator_re_eq_zero (A B : H →ₗ[ℂ] H) (ψ : H) ...
    (hA_sa : ∀ v w, ... → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ)
    (hB_sa : ∀ v w, ... → ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ) ... :
    (⟪ψ, (A ∘ₗ B - B ∘ₗ A) ψ⟫_ℂ).re = 0
```

**Plain English:** For symmetric operators A and B, the expectation value ⟨ψ|[A,B]|ψ⟩ is purely imaginary.

**Proof Sketch:**
$$\langle\psi, [A,B]\psi\rangle = \langle\psi, AB\psi\rangle - \langle\psi, BA\psi\rangle$$
$$= \langle A\psi, B\psi\rangle - \langle B\psi, A\psi\rangle$$
$$= \langle A\psi, B\psi\rangle - \overline{\langle A\psi, B\psi\rangle}$$
$$= 2i \cdot \text{Im}\langle A\psi, B\psi\rangle$$

This is purely imaginary.

**Status:** PROVEN THEOREM ✓

### Lemma: Anticommutator Expectation is Purely Real

```
lemma expectation_anticommutator_im_eq_zero (A B : H →ₗ[ℂ] H) (ψ : H) ... :
    (⟪ψ, (A ∘ₗ B + B ∘ₗ A) ψ⟫_ℂ).im = 0
```

**Plain English:** For symmetric operators A and B, the expectation value ⟨ψ|{A,B}|ψ⟩ is purely real.

**Proof Sketch:** Similar to above, but addition instead of subtraction gives:
$$\langle A\psi, B\psi\rangle + \overline{\langle A\psi, B\psi\rangle} = 2 \cdot \text{Re}\langle A\psi, B\psi\rangle$$

**Status:** PROVEN THEOREM ✓

### Theorem: Inner Product Decomposition

```
theorem inner_product_decomposition (A B : H →ₗ[ℂ] H) (ψ : H) ... :
    2 * ⟪A ψ, B ψ⟫_ℂ = ⟪ψ, (A ∘ₗ B + B ∘ₗ A) ψ⟫_ℂ + ⟪ψ, (A ∘ₗ B - B ∘ₗ A) ψ⟫_ℂ
```

**Plain English:** 
$$2\langle A\psi, B\psi\rangle = \langle\psi, \{A,B\}\psi\rangle + \langle\psi, [A,B]\psi\rangle$$

The inner product decomposes into anticommutator (real) and commutator (imaginary) parts.

**Status:** PROVEN THEOREM ✓

### Theorem: Variance is Non-Negative

```
theorem unboundedVariance_nonneg (A : UnboundedObservable H) (ψ : H) ... :
    0 ≤ unboundedVariance A ψ h_norm hψ
```

**Plain English:** Var(A) ≥ 0 always.

**Proof:** Var(A) = ‖(A − ⟨A⟩I)ψ‖², and norms are non-negative.

**Status:** PROVEN THEOREM ✓

### Theorem: Standard Deviation is Non-Negative

```
theorem unboundedStandardDeviation_nonneg (A : UnboundedObservable H) (ψ : H) ... :
    0 ≤ unboundedStandardDeviation A ψ h_norm hψ
```

**Plain English:** σ_A ≥ 0 always.

**Proof:** Square roots of non-negative numbers are non-negative.

**Status:** PROVEN THEOREM ✓

---

## File 2: Robertson.lean — The Main Theorem

### The Statement

```
theorem robertson_uncertainty_principle
    (A B : UnboundedObservable H)
    (ψ : H)
    (h_norm : ‖ψ‖ = 1)
    (h_domain_A : ψ ∈ A.domain)
    (h_domain_B : ψ ∈ B.domain)
    (h_domain_comp_AB : B.op ψ ∈ A.domain)
    (h_domain_comp_BA : A.op ψ ∈ B.domain) :
    unboundedStandardDeviation A ψ h_norm h_domain_A *
    unboundedStandardDeviation B ψ h_norm h_domain_B ≥
    (1/2) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖
```

**In Mathematical Notation:**

$$\sigma_A \cdot \sigma_B \geq \frac{1}{2}\left|\langle\psi, [A,B]\psi\rangle\right|$$

**Hypotheses Required:**
1. ψ is normalized: ‖ψ‖ = 1
2. ψ is in the domain of A
3. ψ is in the domain of B  
4. Bψ is in the domain of A (so ABψ is defined)
5. Aψ is in the domain of B (so BAψ is defined)

**What is NOT Required:**
- Self-adjointness (only symmetry)
- Boundedness of operators
- Spectral decomposition
- Real eigenvalues

**Status:** PROVEN THEOREM ✓

---

## The Proof: Step by Step

### Step 1: Shift Operators by Expectation Values

**Define:**
$$\tilde{A} = A - \langle A\rangle I$$
$$\tilde{B} = B - \langle B\rangle I$$

**Properties of shifted operators:**
- ⟨Ã⟩ = ⟨B̃⟩ = 0 (zero expectation)
- [Ã, B̃] = [A, B] (same commutator)
- Var(A) = ‖Ãψ‖² (variance equals squared norm)
- Ã and B̃ remain symmetric (by `isSymmetric_sub_smul_of_real`)

**Lean Implementation:**
```
set A_exp := unboundedExpectationValue A ψ h_norm h_domain_A
set B_exp := unboundedExpectationValue B ψ h_norm h_domain_B
set A' := A.op - A_exp • (1 : H →ₗ[ℂ] H)
set B' := B.op - B_exp • (1 : H →ₗ[ℂ] H)

have h_A'_symmOp : ∀ v w, v ∈ A.domain → w ∈ A.domain → ⟪A' v, w⟫_ℂ = ⟪v, A' w⟫_ℂ :=
  isSymmetric_sub_smul_of_real A.op A_exp A.domain A.SymmetricOperator
```

### Step 2: Apply Cauchy-Schwarz

**The Cauchy-Schwarz Inequality:**
$$|\langle u, v\rangle|^2 \leq \|u\|^2 \cdot \|v\|^2$$

**Applied to u = Ãψ, v = B̃ψ:**
$$|\langle\tilde{A}\psi, \tilde{B}\psi\rangle|^2 \leq \|\tilde{A}\psi\|^2 \cdot \|\tilde{B}\psi\|^2 = \text{Var}(A) \cdot \text{Var}(B)$$

**Lean Implementation:**
```
have h_cauchy_schwarz :
    unboundedVariance A ψ h_norm h_domain_A * unboundedVariance B ψ h_norm h_domain_B ≥
    ‖⟪A' ψ, B' ψ⟫_ℂ‖^2 := by
  show ‖A' ψ‖^2 * ‖B' ψ‖^2 ≥ ‖⟪A' ψ, B' ψ⟫_ℂ‖^2
  have hcs : ‖⟪A' ψ, B' ψ⟫_ℂ‖ ≤ ‖A' ψ‖ * ‖B' ψ‖ := norm_inner_le_norm (A' ψ) (B' ψ)
  -- ... square both sides
```

### Step 3: Decompose the Inner Product

**Key Identity:**
$$2\langle\tilde{A}\psi, \tilde{B}\psi\rangle = \langle\psi, \{\tilde{A},\tilde{B}\}\psi\rangle + \langle\psi, [\tilde{A},\tilde{B}]\psi\rangle$$

**Where:**
- Anticommutator term ⟨ψ, {Ã,B̃}ψ⟩ is REAL
- Commutator term ⟨ψ, [Ã,B̃]ψ⟩ is PURELY IMAGINARY

**Lean Implementation:**
```
have h_decomposition :
    ⟪A' ψ, B' ψ⟫_ℂ =
    (1/2 : ℂ) * (⟪ψ, (A' ∘ₗ B' + B' ∘ₗ A') ψ⟫_ℂ + ⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ)

have h_C_imaginary : C.re = 0 := 
  expectation_commutator_re_eq_zero A' B' ψ ...

have h_D_real : D.im = 0 := 
  expectation_anticommutator_im_eq_zero A' B' ψ ...
```

### Step 4: Extract the Commutator Bound

**Since the commutator term is purely imaginary:**
$$|\langle\tilde{A}\psi, \tilde{B}\psi\rangle|^2 = (\text{Re})^2 + (\text{Im})^2 \geq (\text{Im})^2$$

**And the imaginary part comes from the commutator:**
$$(\text{Im})^2 = \frac{1}{4}|\langle\psi, [\tilde{A},\tilde{B}]\psi\rangle|^2$$

**Therefore:**
$$|\langle\tilde{A}\psi, \tilde{B}\psi\rangle|^2 \geq \frac{1}{4}|\langle\psi, [A,B]\psi\rangle|^2$$

**Lean Implementation:**
```
have h_commutator_bound :
    ‖⟪A' ψ, B' ψ⟫_ℂ‖^2 ≥ (1/4) * ‖⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ‖^2 := by
  calc ‖⟪A' ψ, B' ψ⟫_ℂ‖^2
    _ = ‖(1/2 : ℂ) * (D + C)‖^2 := by rw [h_decomposition]
    _ = (1/4) * ‖D + C‖^2 := by norm_num; ring
    _ = (1/4) * (D.re^2 + C.im^2) := by ...  -- D real, C imaginary
    _ ≥ (1/4) * C.im^2 := by nlinarith       -- D.re² ≥ 0
    _ = (1/4) * ‖C‖^2 := by ...              -- C purely imaginary
```

### Step 5: Prove Commutator Invariance

**Key Algebraic Fact:**
$$[\tilde{A}, \tilde{B}] = [A - \langle A\rangle I, B - \langle B\rangle I] = [A, B]$$

**Why:** Scalar multiples of identity commute with everything:
$$[\lambda I, B] = \lambda B - B\lambda = 0$$

**Lean Implementation:**
```
have h_commutator_invariant :
  ⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ = ⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ := by
  -- Expand and show all cross terms cancel
  calc ⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ
    _ = ⟪ψ, A' (B' ψ) - B' (A' ψ)⟫_ℂ := by ...
    -- ... long algebraic manipulation showing scalar terms cancel
    _ = ⟪ψ, A.op (B.op ψ) - B.op (A.op ψ)⟫_ℂ := by abel_nf
    _ = ⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ := by ...
```

### Step 6: Combine and Take Square Roots

**We have established:**
$$\text{Var}(A) \cdot \text{Var}(B) \geq |\langle\tilde{A}\psi, \tilde{B}\psi\rangle|^2 \geq \frac{1}{4}|\langle[A,B]\rangle|^2$$

**Taking square roots (valid since all quantities are non-negative):**
$$\sigma_A \cdot \sigma_B \geq \frac{1}{2}|\langle[A,B]\rangle|$$

**Lean Implementation:**
```
have h_sqrt : Real.sqrt (...) ≥ Real.sqrt (...) := Real.sqrt_le_sqrt h_combined

have lhs_eq : Real.sqrt (Var_A * Var_B) = √Var_A * √Var_B := 
  Real.sqrt_mul (unboundedVariance_nonneg ...)

have rhs_eq : Real.sqrt ((1/4) * ‖z‖²) = (1/2) * ‖z‖ := by
  rw [Real.sqrt_mul, Real.sqrt_sq (norm_nonneg _)]
  -- √(1/4) = 1/2

unfold unboundedStandardDeviation
rw [lhs_eq, rhs_eq] at h_sqrt
exact h_sqrt
```

---

## Summary: What is Proven vs. Assumed

### PROVEN THEOREMS (machine-verified)

| Theorem | Statement |
|---------|-----------|
| `isSymmetric_sub_smul_of_real` | Symmetry preserved under real shifts |
| `expectation_commutator_re_eq_zero` | Commutator expectation is purely imaginary |
| `expectation_anticommutator_im_eq_zero` | Anticommutator expectation is purely real |
| `inner_product_decomposition` | 2⟨Aψ,Bψ⟩ = ⟨{A,B}⟩ + ⟨[A,B]⟩ |
| `unboundedVariance_nonneg` | Variance ≥ 0 |
| `unboundedStandardDeviation_nonneg` | Standard deviation ≥ 0 |
| **`robertson_uncertainty_principle`** | **σ_A · σ_B ≥ ½\|⟨[A,B]⟩\|** |

### AXIOMS (assumed from Mathlib)

| Axiom | Source |
|-------|--------|
| Hilbert space structure | Mathlib `InnerProductSpace` |
| Cauchy-Schwarz inequality | Mathlib `norm_inner_le_norm` |
| Properties of complex numbers | Mathlib `Complex` |
| Properties of real square root | Mathlib `Real.sqrt` |

### DEFINITIONS (neither proven nor assumed)

All structures (`NormalizedState`, `Observable`, `UnboundedObservable`, etc.) and computational definitions (`expectationValue`, `variance`, `commutator`, etc.) are definitions — they introduce new concepts but make no claims.

---

## Physical Applications

### Position-Momentum (Heisenberg-Kennard)

For [X, P] = iℏ:
$$\sigma_x \cdot \sigma_p \geq \frac{\hbar}{2}$$

### Angular Momentum

For [Lₓ, Lᵧ] = iℏLᵤ:
$$\sigma_{L_x} \cdot \sigma_{L_y} \geq \frac{\hbar}{2}|\langle L_z\rangle|$$

### Energy-Time

For time-independent H and observable A with [H, A] = iℏ(dA/dt):
$$\sigma_E \cdot \sigma_A \geq \frac{\hbar}{2}\left|\frac{d\langle A\rangle}{dt}\right|$$

---

## The Significance of Symmetry

The fact that Robertson's inequality requires only symmetry (not self-adjointness) has several implications:

1. **Broader Applicability:** The uncertainty relation holds for symmetric operators that fail to be self-adjoint, such as momentum on a half-line with certain boundary conditions.

2. **Domain Flexibility:** Self-adjointness requires careful matching of domains (Dom(A) = Dom(A†)), which can be technically demanding. Symmetry only requires the operator to be "movable" across inner products on its domain.

3. **Pedagogical Clarity:** The proof reveals that uncertainty is fundamentally about Hilbert space geometry (Cauchy-Schwarz) and algebraic structure (commutators), not about spectral theory.

4. **Mathematical Hygiene:** By identifying the minimal hypotheses, we understand exactly what the uncertainty principle depends on — and what it does not.

---

## References

1. Robertson, H.P. (1929). "The Uncertainty Principle". *Physical Review* 34(2): 163-164.

2. Kennard, E.H. (1927). "Zur Quantenmechanik einfacher Bewegungstypen". *Zeitschrift für Physik* 44(4-5): 326-352.

3. Schrödinger, E. (1930). "Zum Heisenbergschen Unschärfeprinzip". *Sitzungsberichte der Preussischen Akademie der Wissenschaften*, Physikalisch-mathematische Klasse 14: 296-303.

4. Von Neumann, J. (1932). *Mathematische Grundlagen der Quantenmechanik*. Springer.

5. Reed, M. & Simon, B. (1980). *Methods of Modern Mathematical Physics I: Functional Analysis*. Academic Press.

6. Hall, B.C. (2013). *Quantum Theory for Mathematicians*. Springer.

---

## Appendix: Lean 4 Syntax Guide for Non-Lean Readers

| Lean Syntax | Meaning |
|-------------|---------|
| `theorem name : statement := by proof` | Proves `statement` using `proof` |
| `def name : type := value` | Defines `name` to be `value` |
| `structure Name where field : type` | Defines a data structure |
| `∀ x, P x` | "For all x, P(x) holds" |
| `∃ x, P x` | "There exists x such that P(x)" |
| `→` | Implication ("if...then") |
| `∧` | Logical AND |
| `∨` | Logical OR |
| `¬` | Logical NOT |
| `⟪x, y⟫_ℂ` | Complex inner product ⟨x, y⟩ |
| `‖x‖` | Norm of x |
| `H →ₗ[ℂ] H` | Linear map from H to H over ℂ |
| `H →L[ℂ] H` | Continuous linear map from H to H over ℂ |
| `calc a = b := h1; _ = c := h2` | Chain of equalities with proofs |
| `by simp` | Prove by simplification |
| `by ring` | Prove by ring arithmetic |
| `by linarith` | Prove by linear arithmetic |
| `by nlinarith` | Prove by nonlinear arithmetic |
| `by exact h` | Prove by citing hypothesis h |

