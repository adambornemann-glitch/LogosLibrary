# Stone's Theorem: Resolvent Theory
**A Natural Language Companion to the Lean 4 Formalization**

## Abstract

This file develops the **resolvent** of a self-adjoint generator: the family of bounded operators

$$R_z = (A - zI)^{-1}, \quad \text{Im}(z) \neq 0$$

The resolvent is the bridge between unbounded and bounded operator theory. An unbounded self-adjoint operator A generates a *family* of bounded operators R_z, one for each z off the real axis, satisfying:

1. **Existence**: Range(A - zI) = H for all Im(z) ≠ 0
2. **Bound**: ‖R_z‖ ≤ 1/|Im(z)|
3. **Resolvent identity**: R_z - R_w = (z - w)R_z R_w
4. **Adjoint identity**: R_z* = R_{z̄}
5. **Analyticity**: z ↦ R_z is analytic on ℂ \ ℝ

These properties encode the spectral structure of A. The spectrum σ(A) ⊆ ℝ is precisely where the resolvent fails to exist, and the spectral measure can be recovered via:

$$E((a,b]) = \lim_{\epsilon \to 0^+} \frac{1}{2\pi i} \int_a^b [R_{\lambda+i\epsilon} - R_{\lambda-i\epsilon}] d\lambda$$

All results are machine-verified in Lean 4.

---

## 1. The Resolvent Philosophy

### 1.1 From Unbounded to Bounded

The generator A of a unitary group is typically unbounded (think: momentum operator P = -i d/dx). Working with unbounded operators requires constant attention to domains.

The resolvent transforms this problem: for each z with Im(z) ≠ 0, the operator R_z = (A - zI)^{-1} is **bounded** and defined on **all** of H. The family {R_z} captures complete information about A.

### 1.2 Why Off the Real Axis?

For self-adjoint A:
- **On the real axis**: (A - λI)^{-1} may not exist (λ could be an eigenvalue or in the continuous spectrum)
- **Off the real axis**: (A - zI)^{-1} always exists and is bounded

The imaginary part of z provides a "buffer" that prevents resonance with the spectrum.

### 1.3 The Magic Number 1/|Im(z)|

The bound ‖R_z‖ ≤ 1/|Im(z)| is sharp and universal for self-adjoint operators. It says:
- Far from the real axis (large |Im(z)|): resolvent is small
- Near the real axis (small |Im(z)|): resolvent can blow up
- The blowup rate is exactly 1/|Im(z)|

This is the *definition* of having spectrum on the real axis.

---

## 2. Resolvent at ±i: The Starting Point

### 2.1 Why Start with ±i?

The self-adjointness criterion provides:
- Range(A + iI) = H
- Range(A - iI) = H

These are exactly the conditions for R_{-i} = (A + iI)^{-1} and R_i = (A - iI)^{-1} to exist as maps H → D(A).

### 2.2 Existence via Self-Adjointness

**Lemma** (`resolvent_at_i_spec`): For any φ ∈ H, there exists ψ ∈ D(A) such that (A - iI)ψ = φ.

**Proof**: This is just unpacking the self-adjointness condition `hsa.2 φ`, which states Range(A - iI) = H.

**Technical note**: The definition uses nested existentials:
```
∃ (ψ : H) (hψ : ψ ∈ gen.domain), gen.op ⟨ψ, hψ⟩ - I • ψ = φ
```
This requires two applications of `Classical.choose` to fully extract the witness.

### 2.3 Uniqueness via Eigenvalue Argument

**Lemma** (`resolvent_at_i_unique`): If (A - iI)ψ₁ = (A - iI)ψ₂ = φ, then ψ₁ = ψ₂.

**Proof strategy**:
1. Subtract: (A - iI)(ψ₁ - ψ₂) = 0
2. So A(ψ₁ - ψ₂) = i(ψ₁ - ψ₂), making i an eigenvalue
3. Take inner product: ⟨A(ψ₁ - ψ₂), ψ₁ - ψ₂⟩ = i‖ψ₁ - ψ₂‖²
4. But A is symmetric, so ⟨Aξ, ξ⟩ ∈ ℝ for any ξ ∈ D(A)
5. A purely imaginary number equals a real number only if both = 0
6. Therefore ‖ψ₁ - ψ₂‖ = 0

**Key insight**: Self-adjoint operators cannot have non-real eigenvalues. This is *the* obstruction that makes (A - zI) invertible for z ∉ ℝ.

### 2.4 Construction of R_i

**Definition** (`resolvent_at_i`):
```lean
noncomputable def resolvent_at_i (gen : Generator U_grp) 
    (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H
```

**Construction**:
- `toFun φ := Classical.choose (hsa.2 φ)` — the unique solution
- `map_add'` — linearity via uniqueness
- `map_smul'` — scalar multiplication via uniqueness
- `cont` — continuity via Lipschitz bound ‖R_i φ‖ ≤ ‖φ‖

**The continuity proof** uses the key identity:

$$\|(A - iI)\psi\|^2 = \|A\psi\|^2 + \|\psi\|^2$$

This follows from expanding the norm and noting the cross term vanishes:
$$\text{Re}\langle A\psi, i\psi\rangle = \text{Re}(i\langle A\psi, \psi\rangle) = 0$$
since ⟨Aψ, ψ⟩ ∈ ℝ by symmetry.

### 2.5 The Bound ‖R_i‖ ≤ 1

**Theorem** (`resolvent_at_i_bound`): ‖R_i‖ ≤ 1.

**Proof**: From the identity ‖(A - iI)ψ‖² = ‖Aψ‖² + ‖ψ‖² ≥ ‖ψ‖², we get:
$$\|R_i\phi\| = \|\psi\| \leq \|(A-iI)\psi\| = \|\phi\|$$

---

## 3. The Lower Bound Estimate

### 3.1 The Foundation of Everything

**Theorem** (`lower_bound_estimate`): For any z ∈ ℂ with Im(z) ≠ 0 and any ψ ∈ D(A):

$$\|(A - zI)\psi\| \geq |\text{Im}(z)| \cdot \|\psi\|$$

**Proof**:
1. Write z = x + iy where y = Im(z) ≠ 0
2. (A - zI)ψ = (A - xI)ψ - iy·ψ
3. Expand: ‖(A-xI)ψ - iy·ψ‖² = ‖(A-xI)ψ‖² + |y|²‖ψ‖² + 2Re⟨(A-xI)ψ, -iy·ψ⟩
4. The cross term vanishes:
   - Re⟨(A-xI)ψ, -iy·ψ⟩ = -y · Im⟨(A-xI)ψ, ψ⟩
   - But ⟨(A-xI)ψ, ψ⟩ ∈ ℝ (since A-xI is symmetric)
   - So the cross term is 0
5. Therefore: ‖(A-zI)ψ‖² ≥ |y|²‖ψ‖²

### 3.2 Why This Matters

The lower bound estimate immediately gives:
1. **Injectivity**: (A - zI) is injective for Im(z) ≠ 0 (no kernel)
2. **Closed range**: Range(A - zI) is closed (bounded below operators have closed range)
3. **Resolvent bound**: If R_z exists, then ‖R_z‖ ≤ 1/|Im(z)|

### 3.3 Physical Interpretation

In quantum mechanics, this says: you cannot have a resonance exactly at a complex energy z with Im(z) ≠ 0 for a self-adjoint Hamiltonian. The imaginary part provides a "lifetime" that prevents exact resonance.

---

## 4. General Resolvent: The Main Theorem

### 4.1 Statement

**Theorem** (`self_adjoint_range_all_z`): For any z ∈ ℂ with Im(z) ≠ 0 and any φ ∈ H:

$$\exists! \psi \in D(A): (A - zI)\psi = \phi$$

This proves Range(A - zI) = H for all z off the real axis.

### 4.2 Proof Strategy

The proof is significantly more involved than the ±i case, using three key ingredients:

**Part 1: Orthogonal complement is trivial**

If χ ⊥ Range(A - zI), i.e., ⟨(A - zI)ψ, χ⟩ = 0 for all ψ ∈ D(A), then χ = 0.

*Proof*: From orthogonality, we derive:
$$\langle A\psi, \chi\rangle = \bar{z} \langle\psi, \chi\rangle$$

for all ψ ∈ D(A). This is like having χ as an "eigenfunction of A*" with eigenvalue z̄.

Using both surjectivity conditions (A ± iI surjective) and the symmetry of A, we show this forces χ = 0 unless z̄ = z (i.e., z ∈ ℝ), which contradicts Im(z) ≠ 0.

**Part 2: Range is closed**

If u_n → φ where each u_n = (A - zI)ψ_n, then φ ∈ Range(A - zI).

*Proof*: The lower bound estimate gives:
$$\|\psi_m - \psi_n\| \leq \frac{1}{|\text{Im}(z)|} \|u_m - u_n\|$$

So {ψ_n} is Cauchy whenever {u_n} is Cauchy. Since H is complete, ψ_n → ψ_∞ for some ψ_∞.

The key step: use the resolvent R_i to show ψ_∞ ∈ D(A). The identity:
$$\psi_n = R_i(u_n + (z-i)\psi_n)$$
and continuity of R_i gives ψ_∞ = R_i(φ + (z-i)ψ_∞) ∈ D(A).

**Part 3: Dense + Closed = Everything**

From Parts 1 and 2:
- Range(A - zI) is dense (orthogonal complement is {0})
- Range(A - zI) is closed

Therefore Range(A - zI) = H.

### 4.3 The Resolvent Operator

**Definition** (`resolvent`):
```lean
noncomputable def resolvent (gen : Generator U_grp) (z : ℂ)
    (hz : z.im ≠ 0) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H
```

Constructed as `LinearMap.mkContinuous` with:
- Linear structure via uniqueness
- Continuity bound: ‖R_z φ‖ ≤ (1/|Im(z)|) · ‖φ‖

---

## 5. Neumann Series Machinery

### 5.1 The Operator Geometric Series

For a bounded operator T with ‖T‖ < 1, the series:
$$\sum_{n=0}^\infty T^n = (I - T)^{-1}$$

converges in operator norm.

### 5.2 Implementation

**Definition** (`neumannPartialSum`):
$$S_n = I + T + T^2 + \cdots + T^{n-1}$$

**Lemma** (`neumannPartialSum_mul`): Telescoping identity
$$(I - T) \cdot S_n = I - T^n$$

**Lemma** (`neumannPartialSum_cauchy`): When ‖T‖ < 1, the partial sums form a Cauchy sequence.

**Definition** (`neumannSeries`): The limit of partial sums.

**Lemma** (`neumannSeries_mul_left`, `neumannSeries_mul_right`):
$$(I - T) \cdot S = I = S \cdot (I - T)$$

### 5.3 Application to Resolvent

**Lemma** (`resolvent_near_i`): For z near i (specifically, ‖z - i‖ < 1), the resolvent R_z exists and can be constructed via Neumann series.

*Key*: Set T = (z - i) · R_i. Since ‖R_i‖ ≤ 1 and ‖z - i‖ < 1, we have ‖T‖ < 1, enabling the Neumann expansion.

---

## 6. The Resolvent Identity

### 6.1 Statement

**Theorem** (`resolvent_identity`): For any z, w with Im(z), Im(w) ≠ 0:

$$R_z - R_w = (z - w) R_z R_w$$

### 6.2 Proof

Let ψ_w = R_w φ, so (A - wI)ψ_w = φ.
Let η = R_z ψ_w, so (A - zI)η = ψ_w.

Key calculation:
$$(A - zI)\psi_w = \phi + (w - z)\psi_w$$

Both ψ_w and ψ_z + (w-z)η solve (A - zI)x = φ + (w-z)ψ_w.

By uniqueness: ψ_w = ψ_z + (w-z)η.

Rearranging: ψ_z - ψ_w = (z-w)η = (z-w)R_z R_w φ.

### 6.3 Significance

The resolvent identity shows:
1. Resolvents at different points are related
2. The resolvent family is "holomorphic" in z
3. It encodes the semigroup property for exponentials

---

## 7. The Resolvent Adjoint Identity

### 7.1 Statement

**Theorem** (`resolvent_adjoint`): For any z with Im(z) ≠ 0:

$$R_z^* = R_{\bar{z}}$$

### 7.2 Proof

Need to show: ⟨φ, R_z ψ⟩ = ⟨R_{z̄} φ, ψ⟩.

Let ξ = R_z ψ and η = R_{z̄} φ. Then:
- Aξ = ψ + zξ
- Aη = φ + z̄η

Key: ⟨Aη, ξ⟩ = ⟨η, Aξ⟩ by symmetry of A.

Expand LHS: ⟨φ + z̄η, ξ⟩ = ⟨φ, ξ⟩ + z⟨η, ξ⟩
Expand RHS: ⟨η, ψ + zξ⟩ = ⟨η, ψ⟩ + z⟨η, ξ⟩

Cancel z⟨η, ξ⟩ from both sides: ⟨φ, ξ⟩ = ⟨η, ψ⟩. ∎

### 7.3 Significance

This identity is essential for:
1. Proving symmetrized Yosida approximants are self-adjoint
2. Spectral theory: the Stone formula involves R_{λ+iε} - R_{λ-iε}
3. The resolvent is "real" in the sense that R_z* = R_{z̄}

---

## 8. Analytic Structure

### 8.1 Neumann Expansion Near Any Point

**Theorem** (`resolventFun_hasSum`): For z₀ with Im(z₀) ≠ 0 and ‖z - z₀‖ < |Im(z₀)|:

$$R_z = \sum_{n=0}^\infty (z - z_0)^n R_{z_0}^{n+1}$$

converges in operator norm.

**Proof**:
1. z is also off the real axis (since |z.im - z₀.im| < |z₀.im|)
2. Set T = (z - z₀) · R_{z₀}
3. ‖T‖ ≤ ‖z - z₀‖ · ‖R_{z₀}‖ ≤ ‖z - z₀‖/|Im(z₀)| < 1
4. Neumann series gives (I - T)^{-1}
5. Resolvent identity gives R_z = R_{z₀} · (I - T)^{-1}

### 8.2 Holomorphicity

The Neumann expansion shows z ↦ R_z is **analytic** on ℂ \ ℝ with:
- Radius of convergence at z₀: at least |Im(z₀)|
- Power series coefficients: R_{z₀}^{n+1}

---

## 9. Summary of Results

### 9.1 Existence and Uniqueness

| Theorem | Statement |
|---------|-----------|
| `resolvent_at_i_spec` | ∃ ψ ∈ D(A): (A - iI)ψ = φ |
| `resolvent_at_i_unique` | Such ψ is unique |
| `resolvent_at_neg_i_unique` | Analogous for (A + iI) |
| `self_adjoint_range_all_z` | ∃! ψ ∈ D(A): (A - zI)ψ = φ for Im(z) ≠ 0 |

### 9.2 Bounds

| Theorem | Statement |
|---------|-----------|
| `lower_bound_estimate` | ‖(A - zI)ψ‖ ≥ |Im(z)| · ‖ψ‖ |
| `resolvent_at_i_bound` | ‖R_i‖ ≤ 1 |
| `resolvent_bound` | ‖R_z‖ ≤ 1/|Im(z)| |

### 9.3 Algebraic Identities

| Theorem | Statement |
|---------|-----------|
| `resolvent_identity` | R_z - R_w = (z - w) R_z R_w |
| `resolvent_adjoint` | R_z* = R_{z̄} |

### 9.4 Neumann Series

| Lemma/Theorem | Statement |
|---------------|-----------|
| `neumannPartialSum_mul` | (I - T) · S_n = I - T^n |
| `neumannSeries_mul_left` | (I - T) · S = I for ‖T‖ < 1 |
| `neumannSeries_mul_right` | S · (I - T) = I |
| `resolventFun_hasSum` | R_z = Σ (z-z₀)^n R_{z₀}^{n+1} |

### 9.5 API for Spectral Theory

| Definition | Purpose |
|------------|---------|
| `OffRealAxis` | {z : ℂ // z.im ≠ 0} |
| `UpperHalfPlane` | {z : ℂ // 0 < z.im} |
| `LowerHalfPlane` | {z : ℂ // z.im < 0} |
| `resolventFun` | z ↦ R_z as a function for integration |

---

## 10. Logical Dependencies

```
Bochner.lean (Generator construction)
    │
    ▼
Resolvent.lean
    │
    ├── Lower Bound Estimate
    │       │
    │       ├── Uniqueness (no complex eigenvalues)
    │       │
    │       └── Range closed (bounded below)
    │
    ├── Orthogonal complement trivial
    │       │
    │       └── Range dense
    │
    ├── Dense + Closed = Surjective
    │       │
    │       └── self_adjoint_range_all_z
    │
    ├── Neumann Series Machinery
    │       │
    │       ├── resolvent_near_i
    │       │
    │       └── resolventFun_hasSum (analyticity)
    │
    ├── Resolvent Identity
    │
    └── Resolvent Adjoint Identity
```

---

## 11. What This Enables

### 11.1 The Spectral Theorem

With the resolvent, one can prove the spectral theorem via:

$$E((a,b]) = \text{s-}\lim_{\epsilon \to 0^+} \frac{1}{2\pi i} \int_a^b [R_{\lambda+i\epsilon} - R_{\lambda-i\epsilon}] d\lambda$$

The resolvent adjoint identity R_z* = R_{z̄} ensures the integrand is skew-adjoint, making E self-adjoint.

### 11.2 Functional Calculus

For Borel f: ℝ → ℂ, define:

$$f(A) = \int_\mathbb{R} f(\lambda) dE(\lambda)$$

The resolvent is f(λ) = 1/(λ - z) for z ∉ ℝ.

### 11.3 The Other Direction of Stone's Theorem

Given a self-adjoint A with spectral measure E, the unitary group is:

$$U(t) = \int_\mathbb{R} e^{it\lambda} dE(\lambda)$$

The resolvent provides the bridge: knowing R_z for all z ∉ ℝ determines E, which determines U(t).

---

## 12. Historical Note

The resolvent was introduced by Hilbert in 1904 for bounded operators in the context of integral equations. The extension to unbounded operators came in the 1920s-30s with the work of von Neumann and Stone.

The bound ‖R_z‖ ≤ 1/|Im(z)| characterizes the spectrum of A as lying on the real axis. This is the *definition* of self-adjointness in the modern Kato-Rellich perturbation theory: an operator is self-adjoint if and only if it is symmetric and the resolvent exists with the correct bound for all z ∉ ℝ.

Your formalization captures this characterization completely.

---

## References

[1] M. Reed and B. Simon, *Methods of Modern Mathematical Physics*, Vol. I, Ch. VIII.

[2] T. Kato, *Perturbation Theory for Linear Operators*, Springer (1966).

[3] M. H. Stone, "On One-Parameter Unitary Groups in Hilbert Space," Ann. Math. **33**, 643-648 (1932).

---

*Companion document to Resolvent.lean*

*Author: Adam Bornemann*
