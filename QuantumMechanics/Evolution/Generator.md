# Stone's Theorem: Core Structures and Definitions
## A Natural Language Companion to the Lean 4 Formalization

---

## Abstract

In 1932, Marshall Stone established a bijective correspondence between two fundamental objects in functional analysis:

- **Strongly continuous one-parameter unitary groups** {U(t)}_{t∈ℝ}: families of norm-preserving operators satisfying U(s+t) = U(s)U(t)
- **Self-adjoint operators** A: unbounded operators satisfying A = A* (including equality of domains)

The correspondence is given by U(t) = exp(itA), where the exponential is defined via the spectral theorem.

This file establishes the foundational structures for a machine-verified proof in Lean 4. The key insight driving the formalization: **unbounded operators require explicit domain tracking**. Unlike bounded operators, which are defined on all of H, the generator A is only defined on a dense subspace D(A) ⊂ H. Lean's type system forces us to be honest about this.

The formalization proves:
1. **Unitary group properties**: U(-t) = U(t)*, norm preservation, operator norm equals 1
2. **Generator structure**: Domain, operator, density, symmetry, and the defining limit formula
3. **Self-adjointness criterion**: Range(A ± iI) = H characterizes self-adjoint generators
4. **Uniqueness preparation**: Self-adjoint generators of the same group have identical domains and actions

This companion document explains each definition and theorem for readers unfamiliar with Lean 4, while preserving the logical precision that formalization demands.

---

## 1. The Physical and Mathematical Picture

### 1.1 Two Sides of One Coin

Stone's theorem connects dynamics to infinitesimal generators:

| Dynamics Side | Generator Side |
|---------------|----------------|
| U(t) = time evolution operator | A = Hamiltonian / infinitesimal generator |
| Defined for all t ∈ ℝ | Defined on dense domain D(A) ⊂ H |
| Bounded operators (‖U(t)‖ = 1) | Typically unbounded |
| Group law: U(s+t) = U(s)U(t) | Recovered via limit: Aψ = lim_{t→0} (U(t)ψ - ψ)/(it) |

**Physical interpretation**: In quantum mechanics, U(t) = exp(-itH/ℏ) describes how quantum states evolve in time. The Hamiltonian H generates this evolution. Stone's theorem says this relationship is bijective: every reasonable time evolution comes from exactly one self-adjoint Hamiltonian, and vice versa.

### 1.2 Why Unboundedness Matters

The momentum operator P = -iℏ(d/dx) on L²(ℝ) is unbounded: there is no constant C such that ‖Pψ‖ ≤ C‖ψ‖ for all ψ. The eigenfunctions of P (plane waves e^{ikx}) don't even live in L²(ℝ).

Yet P generates translations: U(t) = exp(itP/ℏ) shifts wavefunctions by t. This U(t) is perfectly well-defined and bounded (in fact ‖U(t)‖ = 1), even though its generator is unbounded.

The Lean formalization handles this via **domain tracking**: the generator is a linear map from a submodule D(A) ⊂ H to H, not from H to H. This is not a limitation of the proof assistant—it reflects the actual mathematics.

### 1.3 The Domain Question

For which vectors ψ ∈ H does the limit

$$A\psi = \lim_{t \to 0} \frac{U(t)\psi - \psi}{it}$$

exist? This defines the domain D(A). The formalization proves:

1. D(A) is a linear subspace (closed under addition and scalar multiplication)
2. D(A) is dense in H (every vector can be approximated by domain vectors)
3. D(A) is invariant under U(t) (time evolution preserves the domain)
4. D(A) is maximal for self-adjoint generators (if the limit exists, the vector is in the domain)

Property 4 is crucial: it means the domain is not a choice but is uniquely determined by the unitary group.

---

## 2. One-Parameter Unitary Groups

### 2.1 The Definition

A **strongly continuous one-parameter unitary group** is a family of operators {U(t)}_{t∈ℝ} satisfying four axioms:

| Axiom | Mathematical Statement | Physical Meaning |
|-------|------------------------|------------------|
| Unitarity | ⟨U(t)ψ, U(t)φ⟩ = ⟨ψ, φ⟩ | Inner products preserved |
| Group law | U(s+t) = U(s)∘U(t) | Evolution composes |
| Identity | U(0) = I | No evolution at t=0 |
| Strong continuity | t ↦ U(t)ψ is continuous | No instantaneous jumps |

**Lean implementation**: The structure `OneParameterUnitaryGroup` bundles:
- `U : ℝ → (H →L[ℂ] H)` — the family of continuous linear maps
- `unitary` — proof of inner product preservation
- `group_law` — proof of the composition property
- `identity` — proof that U(0) = I
- `strong_continuous` — proof of continuity in ψ

Note: We use `H →L[ℂ] H` (continuous linear maps), not arbitrary linear maps. This is because U(t) is bounded for each t, even though the generator may be unbounded.

### 2.2 What We Do Not Assume

The definition requires only **strong continuity**: for each fixed ψ, the map t ↦ U(t)ψ is continuous as a function from ℝ to H.

We do **not** assume:
- Norm continuity (t ↦ U(t) continuous in operator norm)
- Differentiability (existence of dU/dt)
- Any specific form like U(t) = exp(itA)

Stone's theorem will *prove* that differentiability follows from strong continuity, and that the exponential form holds. This is the remarkable content of the theorem.

**Historical note**: Von Neumann (1932) showed that even weak measurability (t ↦ ⟨U(t)ψ, φ⟩ is measurable for all ψ, φ) suffices, at least for separable Hilbert spaces. The Lean formalization uses strong continuity as it is more standard and sufficient for our purposes.

---

## 3. Derived Properties of Unitary Groups

### 3.1 Inverse Equals Adjoint

**Theorem** (`inverse_eq_adjoint`): For any strongly continuous one-parameter unitary group and any t ∈ ℝ:

$$U(-t) = U(t)^*$$

**Proof strategy**:

1. From the group law: U(t)U(-t) = U(t + (-t)) = U(0) = I
2. Therefore U(-t) is the inverse of U(t)
3. From unitarity: ⟨U(t)ψ, U(t)φ⟩ = ⟨ψ, φ⟩
4. The defining property of the adjoint is: ⟨U(t)^*ψ, φ⟩ = ⟨ψ, U(t)φ⟩
5. We show U(-t) satisfies this property:

$$\langle U(-t)\psi, \phi \rangle = \langle U(t)(U(-t)\psi), U(t)\phi \rangle = \langle \psi, U(t)\phi \rangle$$

The first equality uses unitarity; the second uses U(t)U(-t) = I.

**Why this matters**:
- Shows unitary operators are normal: U(t)U(t)* = U(t)*U(t)
- Essential for proving the generator is symmetric
- Confirms physical reversibility: backward evolution is the adjoint of forward evolution

### 3.2 Norm Preservation

**Theorem** (`norm_preserving`): For any t ∈ ℝ and ψ ∈ H:

$$\|U(t)\psi\| = \|\psi\|$$

**Proof strategy**:

1. Unitarity gives: ⟨U(t)ψ, U(t)ψ⟩ = ⟨ψ, ψ⟩
2. The norm satisfies: ‖x‖² = Re⟨x, x⟩ (for complex Hilbert spaces, ⟨x,x⟩ is already real)
3. Therefore: ‖U(t)ψ‖² = ‖ψ‖²
4. Both sides are non-negative, so taking square roots: ‖U(t)ψ‖ = ‖ψ‖

**Lean subtlety**: The proof handles the square root carefully. From ‖U(t)ψ‖² = ‖ψ‖², we get ‖U(t)ψ‖ = ‖ψ‖ or ‖U(t)ψ‖ = -‖ψ‖. The second case is impossible since norms are non-negative.

**Why this matters**:
- U(t) is an isometry (distance-preserving)
- In quantum mechanics: probability is conserved (‖ψ‖ = 1 implies ‖U(t)ψ‖ = 1)
- Implies injectivity: if U(t)ψ = 0, then ‖ψ‖ = 0, so ψ = 0

### 3.3 Operator Norm Equals One

**Theorem** (`norm_one`): For any t ∈ ℝ (assuming H is nontrivial):

$$\|U(t)\| = 1$$

**Proof strategy**: Two inequalities.

*Upper bound* (‖U(t)‖ ≤ 1):
- For any ψ: ‖U(t)ψ‖ = ‖ψ‖ ≤ 1·‖ψ‖
- Therefore ‖U(t)‖ ≤ 1

*Lower bound* (‖U(t)‖ ≥ 1):
- From U(0) = I: ‖I‖ = 1
- From the group law: I = U(0) = U(t + (-t)) = U(t)∘U(-t)
- By submultiplicativity: 1 = ‖I‖ = ‖U(t)∘U(-t)‖ ≤ ‖U(t)‖·‖U(-t)‖
- Since ‖U(-t)‖ ≤ 1 and ‖U(t)‖ ≤ 1, the only way their product is ≥ 1 is if both equal 1

**Technical requirement**: We need H to be nontrivial (contain nonzero vectors). In the zero space, all operators have norm 0.

**Why this matters**:
- Unitary operators form the "unit sphere" in operator space
- Time evolution is optimally stable: condition number = 1
- No amplification or decay of states under unitary dynamics

---

## 4. The Generator: Unbounded Operators Done Right

### 4.1 The Challenge

The generator A is defined by:

$$A\psi = \lim_{t \to 0} \frac{U(t)\psi - \psi}{it}$$

This limit may not exist for all ψ ∈ H. For example, if U(t) = exp(itP) where P is the momentum operator, the limit only exists for differentiable functions with appropriate decay.

**The formalization must track**:
1. Which vectors ψ are in the domain D(A)
2. What value Aψ takes for those vectors
3. That D(A) is dense (so A captures enough information)
4. That D(A) is maximal (so we haven't artificially restricted it)

### 4.2 The Generator Structure

The Lean structure `Generator` for a unitary group U_grp contains:

| Field | Type | Meaning |
|-------|------|---------|
| `domain` | `Submodule ℂ H` | The dense subspace D(A) |
| `op` | `domain →ₗ[ℂ] H` | The linear map A: D(A) → H |
| `dense_domain` | `Dense (domain : Set H)` | Proof that D(A) is dense |
| `generator_formula` | (see below) | Proof that Aψ equals the limit |
| `domain_invariant` | (see below) | Proof that U(t) preserves D(A) |
| `symmetric` | (see below) | Proof that ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩ |
| `domain_maximal` | (see below) | Proof that D(A) contains all vectors where the limit exists |

### 4.3 The Generator Formula

The field `generator_formula` states:

```
∀ (ψ : domain),
  Tendsto (fun t : ℝ => ((I : ℂ) * (t : ℂ))⁻¹ • (U_grp.U t (ψ : H) - (ψ : H)))
          (𝓝[≠] 0)
          (𝓝 (op ψ))
```

**Translation**: For every ψ in the domain, the expression

$$\frac{U(t)\psi - \psi}{it}$$

converges to Aψ as t → 0 through nonzero values.

**Technical notes**:
- `𝓝[≠] 0` is the punctured neighborhood filter: we approach 0 but never equal 0
- `(I : ℂ)` is the imaginary unit i = √(-1)
- The formula uses (it)⁻¹ rather than 1/(it) for type-theoretic reasons
- `(ψ : H)` coerces from the subtype `domain` to the ambient space H

### 4.4 Symmetry vs. Self-Adjointness

The `symmetric` field states:

$$\forall \psi, \phi \in D(A): \quad \langle A\psi, \phi \rangle = \langle \psi, A\phi \rangle$$

**This is NOT self-adjointness!** For unbounded operators:

| Property | Definition | Implication |
|----------|------------|-------------|
| Symmetric | ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩ for ψ, φ ∈ D(A) | A ⊆ A* |
| Self-adjoint | A = A* including D(A) = D(A*) | A = A* |

A symmetric operator can have D(A) ⊊ D(A*). Self-adjointness requires the domains to match exactly.

**Why this distinction matters**: Many symmetric operators have multiple self-adjoint extensions, or none at all. The generator of a unitary group is not merely symmetric—it is self-adjoint. But proving self-adjointness requires more work.

### 4.5 Domain Maximality

The field `domain_maximal` states:

```
∀ ψ : H, (∃ η : H, Tendsto (limit expression) (𝓝[≠] 0) (𝓝 η)) → ψ ∈ domain
```

**Translation**: If the limit defining Aψ exists for some vector ψ, then ψ is in the domain.

This is essential for proving:
1. The domain is uniquely determined by the unitary group
2. Self-adjoint generators of the same group have the same domain
3. The generator is unique (not just unique up to restriction)

---

## 5. Self-Adjointness Criterion

### 5.1 The Definition

A generator is self-adjoint if:

$$\text{Range}(A + iI) = H \quad \text{and} \quad \text{Range}(A - iI) = H$$

**Lean implementation** (`Generator.IsSelfAdjoint`):

```
(∀ φ : H, ∃ (ψ : H) (hψ : ψ ∈ gen.domain), gen.op ⟨ψ, hψ⟩ + I • ψ = φ) ∧
(∀ φ : H, ∃ (ψ : H) (hψ : ψ ∈ gen.domain), gen.op ⟨ψ, hψ⟩ - I • ψ = φ)
```

**Translation**: For every vector φ ∈ H, there exists a domain vector ψ such that (A ± i)ψ = φ.

### 5.2 Why This Criterion?

**Theorem** (not in this file, but standard): A symmetric operator A is self-adjoint if and only if Range(A ± iI) = H.

The intuition: for a symmetric operator, A* ⊇ A. The defect is measured by the "deficiency indices"—the dimensions of ker(A* ± iI). If both deficiency indices are zero, then D(A*) = D(A) and A is self-adjoint.

Range(A + iI) = H is equivalent to ker(A* - iI) = {0}, giving deficiency index zero on one side. Similarly for Range(A - iI).

### 5.3 The Hard Part of Stone's Theorem

Proving self-adjointness is the difficult direction of Stone's theorem. The strategy (to be formalized in subsequent files):

1. Construct the resolvent: for λ with Im(λ) ≠ 0, define

$$R_\lambda \phi = \int_0^{\pm\infty} e^{-i\lambda t} U(t)\phi \, dt$$

2. Show R_λ maps H into D(A)
3. Show (A - λI)R_λ = I on H
4. Conclude Range(A - λI) = H

This integral construction is why Stone's original proof required 662 pages of careful analysis.

---

## 6. Uniqueness Lemmas

### 6.1 Domain Characterization

**Lemma** (`generator_domain_char`): A vector ψ is in the domain if and only if the limit defining Aψ exists:

$$\psi \in D(A) \iff \exists \eta \in H: \lim_{t \to 0} \frac{U(t)\psi - \psi}{it} = \eta$$

This is immediate from `generator_formula` (forward direction) and `domain_maximal` (backward direction).

### 6.2 Self-Adjoint Generators Have Maximal Domains

**Lemma** (`selfAdjoint_domain_maximal`): If gen is a self-adjoint generator and the limit exists for ψ, then ψ ∈ D(A).

This follows directly from `domain_maximal` and doesn't actually use self-adjointness—but the lemma is stated in the self-adjoint context for clarity.

### 6.3 Uniqueness of Domain

**Lemma** (`selfAdjoint_generators_domain_eq`): If gen₁ and gen₂ are both self-adjoint generators of the same unitary group, then D(A₁) = D(A₂).

**Proof**:
- Take ψ ∈ D(A₁)
- By `generator_formula`, the limit exists with value A₁ψ
- By `domain_maximal` for gen₂, ψ ∈ D(A₂)
- Symmetrically, D(A₂) ⊆ D(A₁)

### 6.4 Uniqueness of Action

**Lemma** (`generator_op_eq_on_domain`): If ψ ∈ D(A₁) ∩ D(A₂), then A₁ψ = A₂ψ.

**Proof**: Both are the unique limit of the same expression (U(t)ψ - ψ)/(it). Limits in Hausdorff spaces are unique.

### 6.5 Full Uniqueness

**Lemma** (`generator_op_ext_of_eq_on_domain`): If gen₁ and gen₂ have the same domain and agree on that domain, then their operators are equal (in the heterogeneous equality sense required by dependent types).

This uses `HEq` (heterogeneous equality) because the operators have different types: `gen₁.domain →ₗ[ℂ] H` vs `gen₂.domain →ₗ[ℂ] H`. Once we prove the domains are equal, we can transport across this equality.

---

## 7. Logical Structure

```
OneParameterUnitaryGroup
├── Axioms
│   ├── unitary: ⟨U(t)ψ, U(t)φ⟩ = ⟨ψ, φ⟩
│   ├── group_law: U(s+t) = U(s)∘U(t)
│   ├── identity: U(0) = I
│   └── strong_continuous: t ↦ U(t)ψ continuous
│
├── Derived Properties
│   ├── inverse_eq_adjoint: U(-t) = U(t)*
│   ├── norm_preserving: ‖U(t)ψ‖ = ‖ψ‖
│   └── norm_one: ‖U(t)‖ = 1
│
└── Generator
    ├── Structure
    │   ├── domain: Submodule ℂ H
    │   ├── op: domain →ₗ[ℂ] H
    │   ├── dense_domain: D(A) dense in H
    │   ├── generator_formula: Aψ = lim (U(t)ψ - ψ)/(it)
    │   ├── domain_invariant: U(t) preserves D(A)
    │   ├── symmetric: ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩
    │   └── domain_maximal: limit exists ⟹ ψ ∈ D(A)
    │
    ├── Self-Adjointness
    │   └── IsSelfAdjoint: Range(A ± iI) = H
    │
    └── Uniqueness
        ├── generator_domain_char: ψ ∈ D(A) ↔ limit exists
        ├── selfAdjoint_generators_domain_eq: D(A₁) = D(A₂)
        ├── generator_op_eq_on_domain: A₁ψ = A₂ψ
        └── generator_op_ext_of_eq_on_domain: A₁ = A₂
```

---

## 8. Summary of Formal Results

### 8.1 Unitary Group Properties

| Theorem | Statement |
|---------|-----------|
| `inverse_eq_adjoint` | U(-t) = U(t)* |
| `norm_preserving` | ‖U(t)ψ‖ = ‖ψ‖ |
| `norm_one` | ‖U(t)‖ = 1 (requires nontrivial H) |

### 8.2 Generator Structure Fields

| Field | Statement |
|-------|-----------|
| `domain` | Dense submodule D(A) ⊂ H |
| `op` | Linear map A: D(A) → H |
| `dense_domain` | D(A) is dense in H |
| `generator_formula` | Aψ = lim_{t→0} (U(t)ψ - ψ)/(it) |
| `domain_invariant` | U(t)(D(A)) ⊆ D(A) |
| `symmetric` | ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩ for ψ, φ ∈ D(A) |
| `domain_maximal` | Limit exists ⟹ ψ ∈ D(A) |

### 8.3 Self-Adjointness and Uniqueness

| Theorem/Definition | Statement |
|--------------------|-----------|
| `IsSelfAdjoint` | Range(A + iI) = H ∧ Range(A - iI) = H |
| `generator_domain_char` | ψ ∈ D(A) ↔ limit exists |
| `selfAdjoint_domain_maximal` | Self-adjoint + limit exists ⟹ ψ ∈ D(A) |
| `selfAdjoint_generators_domain_eq` | Self-adjoint generators have equal domains |
| `generator_op_eq_on_domain` | Generators agree on common domain |
| `generator_op_ext_of_eq_on_domain` | Same domain + same action ⟹ same operator |

---

## 9. Dependencies and Design Choices

### 9.1 Mathlib Imports

The formalization relies on:

| Module | Purpose |
|--------|---------|
| `Analysis.InnerProductSpace.*` | Hilbert space structure, adjoints |
| `Analysis.Normed.Operator.ContinuousLinearMap` | Bounded operators |
| `MeasureTheory.*` | L² spaces, integration (for later resolvent construction) |
| `Topology.MetricSpace.Completion` | Completeness of H |

### 9.2 Design Choice: Submodule Domains

The domain is a `Submodule ℂ H` rather than a `Set H` or `Subspace ℂ H`. This choice:

- Ensures the domain is closed under ℂ-linear combinations
- Provides access to Mathlib's submodule API
- Matches the Robertson unbounded operator pattern referenced in the file

### 9.3 Design Choice: Continuous Linear Maps

U(t) is typed as `H →L[ℂ] H` (continuous linear maps) rather than just linear maps. This:

- Captures the boundedness of U(t) in the type
- Provides access to operator norm lemmas
- Distinguishes the bounded U(t) from the unbounded generator A

---

## 10. What Comes Next

This file establishes foundations. The full Stone's theorem requires:

1. **Existence of the generator** (partially addressed by `domain_maximal`)
2. **Self-adjointness proof** via the resolvent integral
3. **Converse direction**: self-adjoint A ↦ unitary group exp(itA)
4. **Bijectivity**: the two constructions are mutual inverses

The self-adjointness proof is the technical heart. The key construction:

$$\psi_\pm = \int_0^{\pm\infty} e^{\mp t} U(t)\phi \, dt$$

satisfies (A ± i)ψ_± = φ, proving Range(A ± iI) = H.

---

## 11. Historical Note

Stone's original 1932 paper "On One-Parameter Unitary Groups in Hilbert Space" appeared in the Annals of Mathematics. The full treatment occupied his 662-page monograph *Linear Transformations in Hilbert Space and Their Applications to Analysis*.

Von Neumann's simultaneous work showed that strong continuity could be weakened to weak measurability. The collaboration between Stone and von Neumann during this period produced some of the deepest results in functional analysis, including the Stone-von Neumann theorem on the uniqueness of the canonical commutation relations.

The domain subtleties formalized here were well understood by 1932—the careful treatment of unbounded operators was one of the major achievements of that era.

---

## References

[1] M. H. Stone, "On One-Parameter Unitary Groups in Hilbert Space," Ann. Math. **33**, 643-648 (1932).

[2] M. H. Stone, *Linear Transformations in Hilbert Space and Their Applications to Analysis*, AMS Colloquium Publications Vol. 15 (1932).

[3] J. von Neumann, "Über einen Satz von Herrn M. H. Stone," Ann. Math. **33**, 567-573 (1932).

[4] M. Reed and B. Simon, *Methods of Modern Mathematical Physics*, Vol. I: Functional Analysis, Academic Press (1980), Ch. VIII.

[5] B. C. Hall, *Quantum Theory for Mathematicians*, Springer GTM 267 (2013), Ch. 9-10.

---

## Appendix: Reading the Lean Code

For readers unfamiliar with Lean 4 syntax:

| Lean | Mathematics |
|------|-------------|
| `∀ x : T, P x` | For all x of type T, P(x) holds |
| `∃ x : T, P x` | There exists x of type T such that P(x) |
| `⟪ψ, φ⟫_ℂ` | Inner product ⟨ψ, φ⟩ |
| `H →L[ℂ] H` | Continuous ℂ-linear maps from H to H |
| `Submodule ℂ H` | ℂ-linear subspace of H |
| `domain →ₗ[ℂ] H` | ℂ-linear map from domain to H |
| `𝓝 x` | Neighborhood filter of x |
| `𝓝[≠] 0` | Punctured neighborhood of 0 |
| `Tendsto f F G` | f converges along filter F to filter G |
| `ContinuousLinearMap.adjoint` | The Hilbert space adjoint T* |

The `calc` blocks are structured calculations, chaining equalities or inequalities with justifications.

---

_Author: Adam Bornemann_
