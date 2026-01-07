# Stone's Theorem: Bochner Integration Machinery

## A Natural Language Companion to the Lean 4 Formalization

---

## Abstract

This file contains the analytical heart of Stone's theorem: the construction proving that every strongly continuous one-parameter unitary group has a self-adjoint generator.

The key technique is **resolvent integration**. Given a unitary group {U(t)}_{t∈ℝ} and an arbitrary vector φ ∈ H, we construct:

$$\psi_+ = -i \int_0^\infty e^{-t} U(t)\phi \, dt$$
$$\psi_- = i \int_0^\infty e^{-t} U(-t)\phi \, dt$$

These integrals converge because ‖U(t)‖ = 1 (unitarity) and e^{-t} decays exponentially. The formalization proves:

1. **ψ₊ ∈ D(A)**: The limit defining Aψ₊ exists
2. **(A + iI)ψ₊ = φ**: The resolvent integral solves the resolvent equation
3. **Range(A + iI) = H**: Since φ was arbitrary
4. **Analogous results for ψ₋**: Giving Range(A - iI) = H
5. **Self-adjointness**: A symmetric operator with Range(A ± iI) = H is self-adjoint

The file also provides an alternative proof of domain density via **averaged vectors**: the integral ∫₀ʰ U(t)φ dt is always in D(A), and these vectors approximate φ as h → 0.

All proofs are machine-verified in Lean 4 with Mathlib's Bochner integration library.

---

## 1. Why Bochner Integration?

### 1.1 The Self-Adjointness Problem

From the Generator file, we have:
- A dense domain D(A) where the limit Aψ = lim_{t→0} (U(t)ψ - ψ)/(it) exists
- Symmetry: ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩ for ψ, φ ∈ D(A)

But symmetry is not self-adjointness! The standard criterion for self-adjointness of a symmetric operator A is:

$$\text{Range}(A + iI) = H \quad \text{and} \quad \text{Range}(A - iI) = H$$

To prove Range(A + iI) = H, we must show: for every φ ∈ H, there exists ψ ∈ D(A) such that Aψ + iψ = φ.

### 1.2 The Resolvent Strategy

The resolvent operator R_λ = (A - λI)⁻¹ would give us ψ = R_{-i}φ directly. But we don't yet know A is self-adjoint, so we can't invoke the spectral theorem to define R_λ.

Instead, we construct R_λ directly via integration:

$$R_{-i}\phi = -i \int_0^\infty e^{-t} U(t)\phi \, dt$$

This is a **Bochner integral**—a Hilbert-space-valued integral defined via the same limiting process as Lebesgue integration, but for functions taking values in a Banach space.

### 1.3 Why This Integral?

Formally, if U(t) = exp(itA), then:

$$\int_0^\infty e^{-t} U(t)\phi \, dt = \int_0^\infty e^{-t} e^{itA}\phi \, dt = \int_0^\infty e^{(iA-1)t}\phi \, dt = \frac{1}{1-iA}\phi = (A+i)^{-1} \cdot i\phi$$

So $-i \int_0^\infty e^{-t} U(t)\phi \, dt = (A+i)^{-1}\phi$, which is exactly what we need.

Of course, this calculation is purely formal—we haven't proved U(t) = exp(itA) yet! The actual proof must work directly with the integral and verify all claims from first principles.

---

## 2. Basic Bochner Integration

### 2.1 Integrability of Exponentially Decaying Functions

**Lemma** (`integrable_exp_decay_continuous`): Let f: ℝ → E be a continuous function with ‖f(t)‖ ≤ C for t ≥ 0. Then the function t ↦ e^{-t} • f(t) is integrable on [0, ∞).

**Proof strategy**:
1. The bound function M·e^{-t} is integrable on [0, ∞) with integral M
2. The function t ↦ e^{-t} • f(t) is measurable (composition of continuous functions)
3. Pointwise bound: ‖e^{-t} • f(t)‖ ≤ M·e^{-t}
4. Dominated convergence applies

**Why this matters**: For unitary groups, ‖U(t)φ‖ = ‖φ‖ (norm preservation), so ‖U(t)φ‖ is bounded. This lemma guarantees the resolvent integrals converge.

### 2.2 The Fundamental Integral

**Lemma** (`integral_exp_neg_eq_one`):

$$\int_0^\infty e^{-t} \, dt = 1$$

**Proof**: Apply the fundamental theorem of calculus for improper integrals:
- Antiderivative: F(t) = -e^{-t}
- F(0) = -1
- lim_{t→∞} F(t) = 0
- Integral = 0 - (-1) = 1

**Lean implementation**: Uses `integral_Ioi_of_hasDerivAt_of_tendsto'` with explicit verification of the derivative and limit.

### 2.3 Integral Bounds

**Lemma** (`norm_integral_exp_decay_le`): Under the hypotheses of 2.1:

$$\left\| \int_0^\infty e^{-t} \cdot f(t) \, dt \right\| \leq C$$

**Proof**:

$$\left\| \int_0^\infty e^{-t} f(t) \, dt \right\| \leq \int_0^\infty \|e^{-t} f(t)\| \, dt \leq \int_0^\infty C \cdot e^{-t} \, dt = C \cdot 1 = C$$

### 2.4 Truncation Convergence

**Lemma** (`tendsto_integral_Ioc_exp_decay`): The truncated integrals converge to the improper integral:

$$\lim_{T \to \infty} \int_0^T e^{-t} f(t) \, dt = \int_0^\infty e^{-t} f(t) \, dt$$

**Proof**: The tail integral ∫_T^∞ e^{-t} f(t) dt is bounded by M·e^{-T} → 0.

---

## 3. Unitary Group Integration

### 3.1 Applying the Basic Results

**Lemma** (`integrable_exp_neg_unitary`): For any φ ∈ H:

$$t \mapsto e^{-t} U(t)\phi \text{ is integrable on } [0, \infty)$$

**Proof**: Apply `integrable_exp_decay_continuous` with:
- f(t) = U(t)φ
- Continuity: strong continuity of U(t)
- Bound: ‖U(t)φ‖ = ‖φ‖ (norm preservation)

**Lemma** (`integrable_exp_neg_unitary_neg`): Similarly for U(-t):

$$t \mapsto e^{-t} U(-t)\phi \text{ is integrable on } [0, \infty)$$

### 3.2 Bound on the Resolvent Integral

**Lemma** (`norm_integral_exp_neg_unitary_le`):

$$\left\| \int_0^\infty e^{-t} U(t)\phi \, dt \right\| \leq \|\phi\|$$

This bound is crucial: it shows the resolvent operator (once constructed) is bounded with norm ≤ 1.

---

## 4. The Resolvent Integrals

### 4.1 Definitions

**Definition** (`resolventIntegralPlus`):

$$\psi_+ = (-i) \cdot \int_0^\infty e^{-t} U(t)\phi \, dt$$

**Definition** (`resolventIntegralMinus`):

$$\psi_- = i \cdot \int_0^\infty e^{-t} U(-t)\phi \, dt$$

**Note on signs**: The formalization uses -I for ψ₊ and I for ψ₋. This is a choice of convention; different sources use different signs. What matters is that (A + iI)ψ₊ = φ and (A - iI)ψ₋ = φ.

### 4.2 Basic Properties

**Lemma** (`resolventIntegralPlus_add`): The map φ ↦ ψ₊ is linear (additivity).

**Lemma** (`norm_resolventIntegralPlus_le`): ‖ψ₊‖ ≤ ‖φ‖.

**Lemma** (`norm_resolventIntegralMinus_le`): ‖ψ₋‖ ≤ ‖φ‖.

---

## 5. The Generator Limit: Technical Heart

### 5.1 The Challenge

To show ψ₊ ∈ D(A), we must prove:

$$\lim_{h \to 0} \frac{U(h)\psi_+ - \psi_+}{ih} \text{ exists}$$

Moreover, we must identify this limit as φ - iψ₊, so that:

$$A\psi_+ = \phi - i\psi_+ \implies A\psi_+ + i\psi_+ = \phi \implies (A + iI)\psi_+ = \phi$$

### 5.2 The Shift Calculation

**Lemma** (`unitary_shift_resolventIntegralPlus`): For h > 0:

$$U(h)\psi_+ - \psi_+ = (-i) \cdot \left[ (e^h - 1) \int_h^\infty e^{-t} U(t)\phi \, dt - \int_0^h e^{-t} U(t)\phi \, dt \right]$$

**Derivation** (for the companion, not the Lean code):

1. $U(h)\psi_+ = (-i) \cdot U(h) \int_0^\infty e^{-t} U(t)\phi \, dt$

2. Push U(h) inside: $= (-i) \int_0^\infty e^{-t} U(h+t)\phi \, dt$

3. Substitute s = t + h: $= (-i) \int_h^\infty e^{-(s-h)} U(s)\phi \, ds = (-i) \cdot e^h \int_h^\infty e^{-s} U(s)\phi \, ds$

4. Meanwhile: $\psi_+ = (-i) \int_0^\infty e^{-t} U(t)\phi \, dt = (-i) \left[ \int_0^h + \int_h^\infty \right]$

5. Subtract and simplify to get the result.

A separate lemma handles h < 0.

### 5.3 The Limit

**Theorem** (`generator_limit_resolventIntegralPlus`):

$$\lim_{h \to 0} \frac{U(h)\psi_+ - \psi_+}{ih} = \phi - i\psi_+$$

**Proof strategy**:

1. **Rewrite the quotient** using the shift calculation

2. **Split into two terms**:
   - Term 1: $\frac{e^h - 1}{h} \cdot \int_h^\infty e^{-t} U(t)\phi \, dt$
   - Term 2: $\frac{1}{h} \int_0^h e^{-t} U(t)\phi \, dt$

3. **Take limits**:
   - $(e^h - 1)/h \to 1$ as h → 0 (derivative of exp at 0)
   - $\int_h^\infty \to \int_0^\infty$ as h → 0
   - $(1/h) \int_0^h f(t) dt \to f(0)$ as h → 0 (FTC)

4. **Combine**: 
The limit equals $-\int_0^\infty e^{-t} U(t)\phi \, dt + \phi = -i^{-1}\psi_+ + \phi = i\psi_+ + \phi$

**Helper lemmas**:
- `tendsto_exp_sub_one_div`: $(e^h - 1)/h \to 1$
- `tendsto_integral_Ici_exp_unitary`: $\int_h^\infty \to \int_0^\infty$
- `tendsto_average_integral_unitary`: $(1/h)\int_0^h U(t)\phi \, dt \to U(0)\phi = \phi$

### 5.4 The Minus Case

**Theorem** (`generator_limit_resolventIntegralMinus`):

$$\lim_{h \to 0} \frac{U(h)\psi_- - \psi_-}{ih} = \phi + i\psi_-$$

The proof is analogous, with appropriate sign changes.

---

## 6. Generator Construction

### 6.1 The Domain

**Definition** (`generatorDomain`): The domain D(A) is the set of all ψ ∈ H such that:

$$\lim_{h \to 0} \frac{U(h)\psi - \psi}{ih} \text{ exists}$$

**Lean implementation**: This is a `Submodule ℂ H`, requiring proofs that:
- 0 ∈ D(A) (trivial: limit is 0)
- D(A) is closed under addition
- D(A) is closed under scalar multiplication

### 6.2 The Operator

**Definition** (`generatorOp`): For ψ ∈ D(A), define:

$$A\psi = \lim_{h \to 0} \frac{U(h)\psi - \psi}{ih}$$

**Lean implementation**: Uses `Classical.choose` to extract the limit value from the existence proof.

### 6.3 Key Properties

**Theorem** (`generatorDomain_invariant`): U(t) preserves D(A): if ψ ∈ D(A), then U(t)ψ ∈ D(A).

**Proof**: The limit for U(t)ψ is U(t) applied to the limit for ψ:

$$\frac{U(h)(U(t)\psi) - U(t)\psi}{ih} = U(t) \cdot \frac{U(h)\psi - \psi}{ih}$$

using U(h)U(t) = U(t)U(h) (commutativity from the group law).

**Theorem** (`generator_symmetric`): ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩ for ψ, φ ∈ D(A).

**Proof**: Use unitarity ⟨U(h)ψ, φ⟩ = ⟨ψ, U(-h)φ⟩ and take limits.

### 6.4 Self-Adjointness

**Theorem** (`resolventIntegralPlus_in_domain`): ψ₊ ∈ D(A).

**Theorem** (`resolventIntegralPlus_solves`): Aψ₊ + iψ₊ = φ.

**Theorem** (`range_plus_i_eq_top`): Range(A + iI) = H.

**Theorem** (`range_minus_i_eq_top`): Range(A - iI) = H.

**Corollary** (`generatorOfUnitaryGroup_isSelfAdjoint`): The generator is self-adjoint.

---

## 7. Domain Density via Averaged Vectors

### 7.1 The Alternative Approach

**Definition** (`averagedVector`): For h ≠ 0 and φ ∈ H:

$$\psi_h = \frac{1}{h} \int_0^h U(t)\phi \, dt$$

### 7.2 Key Properties

**Lemma** (`averagedVector_tendsto`): ψ_h → φ as h → 0⁺.

**Proof**: By the fundamental theorem of calculus, the derivative of ∫₀ˣ U(t)φ dt at x = 0 is U(0)φ = φ.

**Lemma** (`averagedVector_in_domain`): ψ_h ∈ D(A) for all h ≠ 0.

**Proof**: Direct calculation shows the limit defining Aψ_h exists. The key is:

$$\frac{U(s)\psi_h - \psi_h}{is} = \frac{1}{ih} \left[ \frac{1}{s}\int_h^{h+s} U(t)\phi \, dt - \frac{1}{s}\int_0^s U(t)\phi \, dt \right]$$

Both bracketed terms converge as s → 0 by FTC.

### 7.3 Density

**Theorem** (`generatorDomain_dense`): D(A) is dense in H.

**Proof**: For any φ ∈ H and ε > 0, the averaged vector ψ_h with small enough h satisfies:
- ψ_h ∈ D(A)
- ‖ψ_h - φ‖ < ε

---

## 8. The Main Construction

### 8.1 Assembling the Generator

**Definition** (`generatorOfUnitaryGroup`): The generator of U(t) is the structure:

```lean
Generator U_grp where
  domain := generatorDomain U_grp
  op := generatorOp U_grp
  dense_domain := generatorDomain_dense U_grp
  generator_formula := generator_formula_holds U_grp
  domain_invariant := generatorDomain_invariant U_grp
  symmetric := generator_symmetric U_grp
  domain_maximal := generatorDomain_maximal U_grp
```

**Theorem** (`generatorOfUnitaryGroup_isSelfAdjoint`): This generator is self-adjoint.

---

## 9. Logical Structure

```
Bochner Integration Machinery
│
├── Basic Integration (Section 1-2)
│   ├── integrable_exp_decay_continuous
│   ├── integral_exp_neg_eq_one
│   ├── norm_integral_exp_decay_le
│   └── tendsto_integral_Ioc_exp_decay
│
├── Unitary Group Integration (Section 2)
│   ├── integrable_exp_neg_unitary
│   ├── integrable_exp_neg_unitary_neg
│   └── norm_integral_exp_neg_unitary_le
│
├── Resolvent Integrals (Section 3)
│   ├── resolventIntegralPlus: ψ₊ = -i∫e^{-t}U(t)φ
│   └── resolventIntegralMinus: ψ₋ = i∫e^{-t}U(-t)φ
│
├── Generator Limit (Section 4) ← TECHNICAL HEART
│   ├── unitary_shift_resolventIntegralPlus
│   ├── generator_limit_resolventIntegralPlus
│   ├── unitary_shift_resolventIntegralMinus
│   └── generator_limit_resolventIntegralMinus
│
├── Generator Construction (Section 5)
│   ├── generatorDomain (Submodule)
│   ├── generatorOp (Linear map)
│   ├── generatorDomain_invariant
│   ├── generator_symmetric
│   ├── resolventIntegralPlus_in_domain
│   ├── resolventIntegralPlus_solves
│   ├── range_plus_i_eq_top
│   └── range_minus_i_eq_top
│
├── Domain Density (Section 6)
│   ├── averagedVector
│   ├── averagedVector_tendsto
│   ├── averagedVector_in_domain
│   └── generatorDomain_dense
│
└── Main Theorem (Section 7)
    ├── generatorOfUnitaryGroup
    └── generatorOfUnitaryGroup_isSelfAdjoint
```

---

## 10. Summary of Formal Results

### 10.1 Basic Integration

| Lemma | Statement |
|-------|-----------|
| `integrable_exp_decay_continuous` | Continuous bounded f ⟹ e^{-t}f(t) integrable on [0,∞) |
| `integral_exp_neg_eq_one` | ∫₀^∞ e^{-t} dt = 1 |
| `norm_integral_exp_decay_le` | ‖∫e^{-t}f(t)‖ ≤ C if ‖f‖ ≤ C |
| `tendsto_integral_Ioc_exp_decay` | ∫₀^T → ∫₀^∞ as T → ∞ |

### 10.2 Resolvent Integrals

| Definition/Lemma | Statement |
|------------------|-----------|
| `resolventIntegralPlus` | ψ₊ = -i∫₀^∞ e^{-t}U(t)φ dt |
| `resolventIntegralMinus` | ψ₋ = i∫₀^∞ e^{-t}U(-t)φ dt |
| `norm_resolventIntegralPlus_le` | ‖ψ₊‖ ≤ ‖φ‖ |
| `norm_resolventIntegralMinus_le` | ‖ψ₋‖ ≤ ‖φ‖ |

### 10.3 Generator Limits

| Theorem | Statement |
|---------|-----------|
| `generator_limit_resolventIntegralPlus` | lim (U(h)ψ₊ - ψ₊)/(ih) = φ - iψ₊ |
| `generator_limit_resolventIntegralMinus` | lim (U(h)ψ₋ - ψ₋)/(ih) = φ + iψ₋ |

### 10.4 Self-Adjointness

| Theorem | Statement |
|---------|-----------|
| `resolventIntegralPlus_in_domain` | ψ₊ ∈ D(A) |
| `resolventIntegralPlus_solves` | (A + iI)ψ₊ = φ |
| `range_plus_i_eq_top` | Range(A + iI) = H |
| `range_minus_i_eq_top` | Range(A - iI) = H |
| `generatorOfUnitaryGroup_isSelfAdjoint` | The generator is self-adjoint |

### 10.5 Domain Density

| Lemma/Theorem | Statement |
|---------------|-----------|
| `averagedVector_in_domain` | (1/h)∫₀ʰ U(t)φ dt ∈ D(A) |
| `averagedVector_tendsto` | (1/h)∫₀ʰ U(t)φ dt → φ as h → 0 |
| `generatorDomain_dense` | D(A) is dense in H |

---

## 11. Historical and Mathematical Context

### 11.1 The Resolvent Integral in Context

The integral construction

$$R_\lambda \phi = \pm i \int_0^\infty e^{\mp\lambda t} U(\pm t)\phi \, dt$$

for Im(λ) ≠ 0 is a standard technique in semigroup theory. For unitary groups (where we can integrate in both time directions), the key insight is that the exponential decay e^{-t} overcomes the oscillations of U(t).

For general C₀-semigroups, the Hille-Yosida theorem uses similar integral formulas but requires bounds on the semigroup's growth rate.

### 11.2 The 662 Pages

My 1932 monograph required such length because:
1. Hilbert space theory was not yet standardized
2. The spectral theorem for unbounded operators required careful development
3. Domain questions for unbounded operators were subtle and new
4. Applications to differential equations required detailed analysis

Your formalization benefits from 90 years of hindsight: Mathlib provides the Hilbert space machinery, Bochner integration is well-developed, and the key ideas have been distilled through generations of textbooks.

Yet the core argument—the resolvent integral—remains the same.

### 11.3 What Remains

This file proves: unitary group ⟹ self-adjoint generator.

For the full bijection, one also needs: self-adjoint operator ⟹ unitary group.

This direction uses the **spectral theorem**: given a self-adjoint A with spectral measure E, define:

$$U(t) = \int_\mathbb{R} e^{it\lambda} \, dE(\lambda)$$

This requires the functional calculus for unbounded self-adjoint operators—a separate development.

---

## References

[1] M. H. Stone, "On One-Parameter Unitary Groups in Hilbert Space," Ann. Math. **33**, 643-648 (1932).

[2] M. Reed and B. Simon, *Methods of Modern Mathematical Physics*, Vol. I, Ch. VIII.

[3] K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Springer (2000).

[4] Mathlib Documentation: `MeasureTheory.Integral.Bochner`

---

*Companion document for Bochner.lean*

*Author: Adam Bornemann*
