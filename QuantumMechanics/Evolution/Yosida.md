# Companion Document: Stone/Yosida.lean
**The Yosida Approximation and Construction of exp(itA)**

## Abstract

This file completes Stone's theorem by constructing the one-parameter unitary group exp(itA) for any self-adjoint operator A, using the Yosida approximation technique. Where Bochner.lean established the forward direction (unitary group → self-adjoint generator), this file establishes the reverse: every self-adjoint operator generates a strongly continuous unitary group.

The construction proceeds by:
1. Defining bounded approximants Aₙ that converge strongly to A on the domain
2. Forming unitary exponentials exp(t·i·Aₙ) via power series
3. Proving these exponentials form a Cauchy sequence via the Duhamel formula
4. Taking the strong limit to define exp(itA)
5. Verifying all required properties (unitarity, group law, generator identity)

The Yosida approach is more elementary than the spectral theorem approach and generalizes to C₀-semigroups. All results are machine-verified in Lean 4 with complete proofs.

---

### Table of Contents

1. [Historical and Mathematical Context](#section-1)
2. [Complex Arithmetic for Spectral Parameters](#section-2)
3. [The Yosida Operators](#section-3)
4. [Norm Bounds](#section-4)
5. [Self-Adjointness and Skew-Adjointness](#section-5)
6. [The J Operator: Approximate Identity](#section-6)
7. [Convergence of Yosida Approximants](#section-7)
8. [Exponential of Bounded Operators](#section-8)
9. [Unitarity of Yosida Exponentials](#section-9)
10. [The Duhamel Formula](#section-10)
11. [Definition and Properties of exp(itA)](#section-11)
12. [Logical Structure](#section-12)
13. [Summary Tables](#section-13)
14. [Completing Stone's Theorem](#section-14)

---

<a name="section-1"></a>
### Section 1: Historical and Mathematical Context

#### The Problem

Given a self-adjoint operator A on a Hilbert space H, we want to construct the time evolution operator U(t) = exp(itA). For bounded A, this is straightforward via the power series:

$$\exp(itA) = \sum_{k=0}^{\infty} \frac{(itA)^k}{k!}$$

But for unbounded A (the physically relevant case), this series doesn't converge in operator norm—the terms (itA)^k/k! are unbounded operators, and the sum is meaningless.

#### Historical Approaches

**Stone (1932):** Used the spectral theorem. If A = ∫λ dE(λ), then exp(itA) = ∫e^{itλ} dE(λ). This requires constructing the spectral measure E, which is substantial machinery.

**Yosida (1948):** Introduced bounded approximants Aₙ that converge to A on the domain. The exponentials exp(itAₙ) are well-defined and converge strongly to exp(itA). This approach:
- Avoids the spectral theorem
- Generalizes to C₀-semigroups (Hille-Yosida theorem)
- Is more "constructive"

**Hille-Yosida (1948):** Characterized which operators generate C₀-semigroups via resolvent conditions. Stone's theorem is the special case for unitary groups.

#### The Yosida Strategy

The key insight is that while A is unbounded, its resolvent R(z) = (A - zI)⁻¹ is bounded for z not in the spectrum. For self-adjoint A, the spectrum is real, so R(in) exists and satisfies ‖R(in)‖ ≤ 1/n.

The Yosida approximant is:
$$A_n = n^2 R(in) - in \cdot I$$

This is bounded (‖Aₙ‖ ≤ 2n) and converges strongly to A on the domain D(A).

#### Why This File Matters

This file completes the bijection of Stone's theorem:

```
Self-adjoint operators ←――――――→ Strongly continuous unitary groups
         A            ――――→     exp(itA)     [Yosida.lean]
    generator of U    ←――――      U(t)        [Bochner.lean]
```

The round-trip A → exp(itA) → generator = A establishes the correspondence.

---

<a name="section-2"></a>
### Section 2: Complex Arithmetic for Spectral Parameters (§0 in file)

The Yosida approximation evaluates the resolvent at purely imaginary points z = ±in. This section establishes the elementary facts needed.

#### Resolvent Existence

For self-adjoint A, the spectrum σ(A) ⊆ ℝ. The resolvent R(z) = (A - zI)⁻¹ exists precisely when z ∉ σ(A), i.e., when Im(z) ≠ 0.

**Lemma** `I_mul_pnat_im_ne_zero`: For n ∈ ℕ⁺, Im(in) = n ≠ 0.

*Proof:* Direct calculation: Im(i·n) = 1·n + 0·0 = n > 0. ∎

**Lemma** `neg_I_mul_pnat_im_ne_zero`: For n ∈ ℕ⁺, Im(-in) = -n ≠ 0.

These lemmas ensure R(in) and R(-in) exist for the Yosida construction.

#### Resolvent Bound

For self-adjoint A, the resolvent satisfies the fundamental estimate:
$$\|R(z)\| \leq \frac{1}{|\text{Im}(z)|}$$

**Lemma** `abs_I_mul_pnat_im`: |Im(in)| = n.

Combined with the resolvent bound:
$$\|R(in)\| \leq \frac{1}{n}$$

This 1/n decay is the foundation of all Yosida estimates.

#### Norm Lemmas

**Lemma** `norm_pnat_sq`: ‖n²‖_ℂ = n² (n² is a non-negative real)

**Lemma** `norm_I_mul_pnat`: ‖i·n‖ = n (since |i| = 1)

These are used throughout the norm bounds.

#### Resolvent Specification

**Lemma** `resolvent_spec`: For z with Im(z) ≠ 0 and any φ ∈ H:
- R(z)φ ∈ D(A)
- (A - zI)(R(z)φ) = φ

This is the defining property: the resolvent maps H into D(A) and inverts (A - zI).

---

<a name="section-3"></a>
### Section 3: The Yosida Operators (§1 in file)

#### The Resolvent Operators

**Definition** `resolventAtIn n`: The resolvent at z = in, bundled with the proof that Im(in) ≠ 0:
```
resolventAtIn n := R(in) : H →L[ℂ] H
```

**Definition** `resolventAtNegIn n`: The resolvent at z = -in:
```
resolventAtNegIn n := R(-in) : H →L[ℂ] H
```

Both are needed for the symmetrized approximant.

#### The Standard Yosida Approximant

**Definition** `yosidaApprox n`:
$$A_n = n^2 R(in) - in \cdot I$$

**Motivation:** Starting from the resolvent equation (A - in·I)R(in) = I:
$$A \cdot R(in) = in \cdot R(in) + I$$

Heuristically, "solving for A" on the range of R(in):
$$A \approx in + R(in)^{-1} = in + n^2 R(in)^{-1} \cdot R(in)^{-1} \cdot R(in) \approx n^2 R(in) - in \cdot I$$

The precise statement is that Aₙφ → Aφ for φ ∈ D(A).

#### The Symmetrized Approximant

**Definition** `yosidaApproxSym n`:
$$A_n^{\text{sym}} = \frac{n^2}{2}(R(in) + R(-in))$$

**Why symmetrize?** The standard approximant Aₙ is not self-adjoint. But the resolvent adjoint formula gives:
$$R(z)^* = R(\bar{z})$$

For z = in, we have z̄ = -in, so:
- R(in)* = R(-in)
- (R(in) + R(-in))* = R(-in) + R(in) = R(in) + R(-in) ✓

The sum is self-adjoint, making Aₙˢʸᵐ self-adjoint.

**Why self-adjointness matters:** For exp(t·i·Aₙˢʸᵐ) to be unitary, we need i·Aₙˢʸᵐ to be skew-adjoint, which requires Aₙˢʸᵐ to be self-adjoint.

#### Yosida's J Operator

**Definition** `yosidaJ n`:
$$J_n = -in \cdot R(in)$$

**Key properties:**
- ‖Jₙ‖ ≤ 1 uniformly (the n from |-in| cancels the 1/n from ‖R(in)‖)
- Jₙ → I strongly (the "approximate identity")

**The name "J":** In Yosida's work, Jₙ serves as a mollifier that smooths vectors into the domain while converging to the identity.

**Definition** `yosidaJNeg n`:
$$J_n^- = in \cdot R(-in)$$

This is the adjoint of Jₙ: (Jₙ)* = Jₙ⁻.

#### The Negative Approximant

**Definition** `yosidaApproxNeg n`:
$$A_n^- = n^2 R(-in) + in \cdot I$$

This is the counterpart to Aₙ using the conjugate resolvent. The symmetrized version is:
$$A_n^{\text{sym}} = \frac{1}{2}(A_n + A_n^-)$$

---

<a name="section-4"></a>
### Section 4: Norm Bounds (§2 in file)

#### Bound on Yosida Approximants

**Theorem** `yosidaApprox_norm_bound`:
$$\|A_n\| \leq 2n$$

*Proof:*
$$\|A_n\| = \|n^2 R(in) - in \cdot I\| \leq \|n^2 R(in)\| + \|in \cdot I\|$$
$$= n^2 \|R(in)\| + n \leq n^2 \cdot \frac{1}{n} + n = n + n = 2n$$
∎

**Why linear growth is acceptable:** The bound grows with n, but:
1. Each Aₙ is bounded, so exp(itAₙ) is defined via power series
2. The exponentials are unitary (norm 1) regardless of ‖Aₙ‖
3. We only need pointwise convergence, not uniform operator bounds

#### Uniform Bound on J Operators

**Lemma** `yosidaJ_norm_bound`:
$$\|J_n\| = \|-in \cdot R(in)\| \leq 1$$

*Proof:*
$$\|J_n\| = |-in| \cdot \|R(in)\| = n \cdot \|R(in)\| \leq n \cdot \frac{1}{n} = 1$$
∎

**The magic of cancellation:** The factor n from the scalar exactly cancels the 1/n from the resolvent bound. This is not coincidence—Jₙ approximates the identity (which has norm 1).

**Lemma** `yosidaJNeg_norm_bound`:
$$\|J_n^-\| \leq 1$$

Same bound by the same argument.

**Why uniformity matters:** The bound ‖Jₙ‖ ≤ 1 is uniform in n, enabling:
- Extension of convergence from D(A) to all of H (ε/3 argument)
- Application of Banach-Steinhaus
- Control of error terms in the Duhamel estimate

---

<a name="section-5"></a>
### Section 5: Self-Adjointness and Skew-Adjointness (§3 in file)

#### Self-Adjointness of Symmetrized Approximant

**Theorem** `yosidaApproxSym_selfAdjoint`:
$$(A_n^{\text{sym}})^* = A_n^{\text{sym}}$$

*Proof:*

The resolvent adjoint formula R(z)* = R(z̄) gives:
- R(in)* = R(-in)
- R(-in)* = R(in)

Therefore:
$$(R(in) + R(-in))^* = R(-in) + R(in) = R(in) + R(-in)$$

The scalar n²/2 is real (equals its own conjugate), so:
$$\left(\frac{n^2}{2}(R(in) + R(-in))\right)^* = \frac{n^2}{2}(R(in) + R(-in))$$
∎

#### Skew-Adjointness of i·Aₙˢʸᵐ

**Theorem** `I_smul_yosidaApproxSym_skewAdjoint`:
$$(i \cdot A_n^{\text{sym}})^* = -i \cdot A_n^{\text{sym}}$$

*Proof:*

Using (cT)* = c̄·T* and ī = -i:
$$(i \cdot A_n^{\text{sym}})^* = (-i) \cdot (A_n^{\text{sym}})^* = (-i) \cdot A_n^{\text{sym}} = -(i \cdot A_n^{\text{sym}})$$
∎

#### Why Skew-Adjointness Implies Unitarity

For a bounded operator B, exp(tB) is unitary for all t ∈ ℝ if and only if B is skew-adjoint (B* = -B).

*Proof sketch:*
$$(\exp(tB))^* = \exp(tB^*) = \exp(-tB) = (\exp(tB))^{-1}$$

where the last equality uses the group law exp(-tB)·exp(tB) = exp(0) = I.

Applied to B = i·Aₙˢʸᵐ: skew-adjointness ensures exp(t·i·Aₙˢʸᵐ) is unitary for all t.

---

<a name="section-6"></a>
### Section 6: The J Operator: Approximate Identity (§4 in file)

#### The Fundamental Identity

**Lemma** `yosidaJ_eq_sub_resolvent_A`: For φ ∈ D(A):
$$J_n \varphi = \varphi - R(in)(A\varphi)$$

*Derivation:*

From the resolvent equation R(z)(A - zI)φ = φ for φ ∈ D(A):
$$R(in)(A\varphi) - in \cdot R(in)\varphi = \varphi$$

Rearranging:
$$-in \cdot R(in)\varphi = \varphi - R(in)(A\varphi)$$
$$J_n\varphi = \varphi - R(in)(A\varphi)$$
∎

**Geometric interpretation:** Jₙ is "almost" the identity, with a correction term R(in)∘A that becomes negligible as n → ∞.

#### Convergence on the Domain

**Lemma** `yosidaJ_tendsto_on_domain`: For φ ∈ D(A):
$$J_n\varphi \to \varphi \text{ as } n \to \infty$$

*Proof:*

Using the fundamental identity:
$$\|J_n\varphi - \varphi\| = \|R(in)(A\varphi)\| \leq \|R(in)\| \cdot \|A\varphi\| \leq \frac{1}{n} \|A\varphi\|$$

For fixed φ ∈ D(A), the quantity ‖Aφ‖ is finite, so (1/n)‖Aφ‖ → 0.

**Convergence rate:** O(1/n) with constant ‖Aφ‖. ∎

#### Strong Convergence on All of H

**Theorem** `yosida_J_tendsto_id`: For any ψ ∈ H:
$$J_n\psi \to \psi \text{ as } n \to \infty$$

*Proof (ε/3 argument):*

Given ε > 0:

1. **Approximate by domain:** Since D(A) is dense, choose φ ∈ D(A) with ‖ψ - φ‖ < ε/3.

2. **Convergence on domain:** Choose N such that n ≥ N implies ‖Jₙφ - φ‖ < ε/3.

3. **Combine using uniform bound:** For n ≥ N:
$$\|J_n\psi - \psi\| \leq \|J_n\psi - J_n\varphi\| + \|J_n\varphi - \varphi\| + \|\varphi - \psi\|$$
$$\leq \|J_n\| \cdot \|\psi - \varphi\| + \|J_n\varphi - \varphi\| + \|\varphi - \psi\|$$
$$\leq 1 \cdot \frac{\varepsilon}{3} + \frac{\varepsilon}{3} + \frac{\varepsilon}{3} = \varepsilon$$

The uniform bound ‖Jₙ‖ ≤ 1 is essential here. ∎

#### The Negative J Operator

**Lemma** `yosidaJNeg_eq_sub_resolvent_A`: For φ ∈ D(A):
$$J_n^-\varphi = \varphi - R(-in)(A\varphi)$$

**Lemma** `yosidaJNeg_tendsto_id`: Jₙ⁻ψ → ψ for all ψ ∈ H.

Both operators converge strongly to the identity.

---

<a name="section-7"></a>
### Section 7: Convergence of Yosida Approximants (§5 in file)

#### The Key Factorization

**Theorem** `yosidaApprox_eq_J_comp_A`: For φ ∈ D(A):
$$A_n\varphi = J_n(A\varphi)$$

*Derivation:*

From Jₙφ = φ - R(in)(Aφ), solve for R(in)(Aφ):
$$R(in)(A\varphi) = \varphi + in \cdot R(in)\varphi$$

Now compute Jₙ(Aφ) = -in·R(in)(Aφ):
$$J_n(A\varphi) = -in \cdot (\varphi + in \cdot R(in)\varphi)$$
$$= -in \cdot \varphi + n^2 \cdot R(in)\varphi$$
$$= n^2 R(in)\varphi - in \cdot \varphi = A_n\varphi$$

(using (-in)(in) = n²) ∎

**Why this is powerful:** The convergence Aₙ → A on the domain reduces to the already-proved Jₙ → I:
$$A_n\varphi = J_n(A\varphi) \to I(A\varphi) = A\varphi$$

#### Strong Convergence of Yosida Approximants

**Theorem** `yosidaApprox_tendsto_on_domain`: For φ ∈ D(A):
$$A_n\varphi \to A\varphi \text{ as } n \to \infty$$

*Proof:* Immediate from Aₙφ = Jₙ(Aφ) and Jₙ → I strongly. ∎

#### Analogues for Negative and Symmetrized Approximants

**Lemma** `yosidaApproxNeg_eq_JNeg_A`: Aₙ⁻φ = Jₙ⁻(Aφ)

**Lemma** `yosidaApproxNeg_tendsto_on_domain`: Aₙ⁻φ → Aφ

**Lemma** `yosidaApproxSym_eq_avg`: 
$$A_n^{\text{sym}} = \frac{1}{2}(A_n + A_n^-)$$

**Theorem** `yosidaApproxSym_tendsto_on_domain`: Aₙˢʸᵐφ → Aφ

Since both Aₙ and Aₙ⁻ converge to A, their average does too.

#### Commutativity with Resolvents

**Theorem** `yosidaApprox_commutes_resolvent`:
$$A_n \circ R(z) = R(z) \circ A_n$$

*Proof:* Since Aₙ = n²R(in) - in·I and resolvents at different points commute (from the resolvent identity), we have R(in)∘R(z) = R(z)∘R(in), hence Aₙ∘R(z) = R(z)∘Aₙ. ∎

**Significance:** This commutativity extends to exponentials and ensures exp(itAₙ) preserves the domain structure.

---

<a name="section-8"></a>
### Section 8: Exponential of Bounded Operators (§6 in file)

#### Definition via Power Series

**Definition** `expBounded B t`:
$$\exp(tB) = \sum_{k=0}^{\infty} \frac{(tB)^k}{k!}$$

For bounded B, this converges absolutely in operator norm:
$$\left\|\frac{(tB)^k}{k!}\right\| \leq \frac{(|t| \cdot \|B\|)^k}{k!}$$

and Σ xᵏ/k! = eˣ converges for all x.

#### The Semigroup Law

**Theorem** `expBounded_group_law`:
$$\exp((s+t)B) = \exp(sB) \circ \exp(tB)$$

*Proof:* Since sB and tB commute (both are scalar multiples of B), the Cauchy product formula gives:
$$\exp(sB) \cdot \exp(tB) = \sum_n \sum_{j+k=n} \frac{(sB)^j(tB)^k}{j!k!} = \sum_n \frac{((s+t)B)^n}{n!} = \exp((s+t)B)$$

using the binomial theorem. ∎

#### Norm Bound

**Theorem** `expBounded_norm_bound`:
$$\|\exp(tB)\| \leq \exp(|t| \cdot \|B\|)$$

*Proof:*
$$\|\exp(tB)\| \leq \sum_k \frac{\|tB\|^k}{k!} = \exp(\|tB\|) = \exp(|t| \cdot \|B\|)$$
∎

For skew-adjoint B, the sharp bound is ‖exp(tB)‖ = 1.

#### Adjoint of Powers

**Theorem** `adjoint_pow`:
$$(B^k)^* = (B^*)^k$$

*Proof by induction:*
- Base: (B⁰)* = I* = I = (B*)⁰
- Step: (Bᵏ⁺¹)* = (Bᵏ·B)* = B*·(Bᵏ)* = B*·(B*)ᵏ = (B*)ᵏ⁺¹ ∎

#### Adjoint of Exponential

**Theorem** `adjoint_expBounded`:
$$(\exp(tB))^* = \exp(tB^*)$$

*Proof:* Since adjoint is continuous and linear:
$$(\exp(tB))^* = \left(\sum_k \frac{(tB)^k}{k!}\right)^* = \sum_k \frac{((tB)^k)^*}{k!} = \sum_k \frac{(tB^*)^k}{k!} = \exp(tB^*)$$
∎

#### Unitarity from Skew-Adjointness

**Theorem** `expBounded_skewAdjoint_unitary`: If B* = -B, then:
$$(\exp(tB))^* \circ \exp(tB) = I \quad \text{and} \quad \exp(tB) \circ (\exp(tB))^* = I$$

*Proof:*
$$(\exp(tB))^* = \exp(tB^*) = \exp(-tB)$$

Using the semigroup law:
$$(\exp(tB))^* \circ \exp(tB) = \exp(-tB) \circ \exp(tB) = \exp(0) = I$$

Similarly for the other order. ∎

---

<a name="section-9"></a>
### Section 9: Unitarity of Yosida Exponentials (§7 in file)

#### Inner Product Preservation

**Theorem** `expBounded_yosidaApproxSym_unitary`:
$$\langle \exp(t \cdot i \cdot A_n^{\text{sym}})\psi, \exp(t \cdot i \cdot A_n^{\text{sym}})\varphi \rangle = \langle \psi, \varphi \rangle$$

*Proof:*

1. i·Aₙˢʸᵐ is skew-adjoint (from `I_smul_yosidaApproxSym_skewAdjoint`)
2. Skew-adjoint operators have unitary exponentials (from `expBounded_skewAdjoint_unitary`)
3. Unitary operators preserve inner products:
$$\langle U\psi, U\varphi \rangle = \langle \psi, U^*U\varphi \rangle = \langle \psi, \varphi \rangle$$
∎

#### Isometry Property

**Theorem** `expBounded_yosidaApproxSym_isometry`:
$$\|\exp(t \cdot i \cdot A_n^{\text{sym}})\psi\| = \|\psi\|$$

*Proof:* From inner product preservation with φ = ψ:
$$\|U\psi\|^2 = \langle U\psi, U\psi \rangle = \langle \psi, \psi \rangle = \|\psi\|^2$$

Taking square roots. ∎

**Significance:** This isometry property is the key to the Cauchy sequence argument. When comparing exp(t·i·Aₘˢʸᵐ)ψ and exp(t·i·Aₙˢʸᵐ)ψ, we can use:
$$\|\exp(t \cdot i \cdot A_m^{\text{sym}})(\psi - \varphi)\| = \|\psi - \varphi\|$$

to control error terms independent of m and n.

---

<a name="section-10"></a>
### Section 10: The Duhamel Formula (§8 in file)

This is the analytical heart of the construction—the technique that controls how well the bounded approximants exp(t·i·Aₙˢʸᵐ) approximate the true evolution U(t).

#### The Variation of Parameters Strategy

**Goal:** Compare U(t)φ with exp(tBₙ)φ where Bₙ = i·Aₙˢʸᵐ.

**Auxiliary function:** Define f : [0,t] → H by:
$$f(s) = \exp((t-s)B_n) \cdot U(s)\varphi$$

This interpolates between:
- f(0) = exp(tBₙ)·U(0)φ = exp(tBₙ)φ
- f(t) = exp(0)·U(t)φ = U(t)φ

The difference U(t)φ - exp(tBₙ)φ = f(t) - f(0) = ∫₀ᵗ f'(s) ds by FTC.

#### The Integrand

**Definition** `duhamelIntegrand`:
$$\text{integrand}(s) = \exp((t-s)B_n) \cdot (iA - B_n) \cdot U(s)\varphi$$

where Bₙ = i·Aₙˢʸᵐ, so iA - Bₙ = i·(A - Aₙˢʸᵐ).

#### Helper Lemmas for Differentiation

**Lemma** `expBounded_hasDerivAt_zero`:
$$\frac{d}{d\tau}\exp(\tau B)\Big|_{\tau=0} = B$$

*Proof:* The derivative of the power series at τ = 0 picks out the k = 1 term. ∎

**Lemma** `expBounded_hasDerivAt`:
$$\frac{d}{d\tau}\exp(\tau B) = B \circ \exp(\tau B)$$

**Lemma** `B_commute_expBounded`:
$$B \circ \exp(\tau B) = \exp(\tau B) \circ B$$

Since exp(τB) is a power series in B.

**Lemma** `unitary_hasDerivAt_zero`: For φ ∈ D(A):
$$\frac{d}{dt}U(t)\varphi\Big|_{t=0} = iA\varphi$$

This is the generator formula from the definition of A.

**Lemma** `unitary_hasDerivAt`: For φ ∈ D(A):
$$\frac{d}{dt}U(t)\varphi = iA \cdot U(t)\varphi$$

*Proof:* Using U(t+h)φ = U(t)(U(h)φ) and the chain rule with the generator formula at h = 0. ∎

#### The Product Rule Calculation

**Computing f'(s):**

$$f(s) = \exp((t-s)B_n) \cdot U(s)\varphi$$

Using the product rule for operator-valued functions:
$$f'(s) = \frac{d}{ds}[\exp((t-s)B_n)] \cdot U(s)\varphi + \exp((t-s)B_n) \cdot \frac{d}{ds}[U(s)\varphi]$$

First term (chain rule with τ = t - s, dτ/ds = -1):
$$\frac{d}{ds}[\exp((t-s)B_n)] = -B_n \cdot \exp((t-s)B_n)$$

Second term:
$$\frac{d}{ds}[U(s)\varphi] = iA \cdot U(s)\varphi$$

Combining:
$$f'(s) = -B_n \exp((t-s)B_n) U(s)\varphi + \exp((t-s)B_n) \cdot iA \cdot U(s)\varphi$$

Using commutativity Bₙ·exp(τBₙ) = exp(τBₙ)·Bₙ:
$$f'(s) = \exp((t-s)B_n)(-B_n + iA)U(s)\varphi = \exp((t-s)B_n)(iA - B_n)U(s)\varphi$$

#### The Duhamel Identity

**Theorem** `duhamel_identity`: For φ ∈ D(A):
$$U(t)\varphi - \exp(t \cdot i \cdot A_n^{\text{sym}})\varphi = \int_0^t \exp((t-s) \cdot i \cdot A_n^{\text{sym}}) \cdot i(A - A_n^{\text{sym}}) \cdot U(s)\varphi \, ds$$

*Proof:* Apply FTC to f(s):
$$f(t) - f(0) = \int_0^t f'(s) \, ds$$
$$U(t)\varphi - \exp(tB_n)\varphi = \int_0^t \exp((t-s)B_n)(iA - B_n)U(s)\varphi \, ds$$
∎

#### The Key Simplification: Constant Norm on Orbit

**Lemma** `norm_gen_diff_constant`:
$$\|A(U(s)\varphi) - A_n^{\text{sym}}(U(s)\varphi)\| = \|A\varphi - A_n^{\text{sym}}\varphi\|$$

*Proof:*

Three key facts:
1. **Generator commutes with unitary group** (`generator_commutes_unitary`): A(U(s)φ) = U(s)(Aφ)
2. **Yosida approximant commutes with unitary group** (`yosidaApproxSym_commutes_unitary`): Aₙˢʸᵐ(U(s)φ) = U(s)(Aₙˢʸᵐφ)
3. **Unitary group is isometric** (`U_norm_preserving`): ‖U(s)ψ‖ = ‖ψ‖

Therefore:
$$\|A(U(s)\varphi) - A_n^{\text{sym}}(U(s)\varphi)\| = \|U(s)(A\varphi) - U(s)(A_n^{\text{sym}}\varphi)\|$$
$$= \|U(s)(A\varphi - A_n^{\text{sym}}\varphi)\| = \|A\varphi - A_n^{\text{sym}}\varphi\|$$
∎

**This is the killer lemma:** The supremum over the orbit collapses to a single value!

#### The Duhamel Estimate

**Theorem** `duhamel_estimate`: For φ ∈ D(A):
$$\|U(t)\varphi - \exp(t \cdot i \cdot A_n^{\text{sym}})\varphi\| \leq |t| \cdot \|A\varphi - A_n^{\text{sym}}\varphi\|$$

*Proof:*

Taking norms of the Duhamel identity:
$$\|U(t)\varphi - \exp(tB_n)\varphi\| \leq \int_0^{|t|} \|\exp((t-s)B_n)(iA - B_n)U(s)\varphi\| \, ds$$

Since exp((t-s)Bₙ) is unitary (hence isometric):
$$= \int_0^{|t|} \|(iA - B_n)U(s)\varphi\| \, ds = \int_0^{|t|} \|(A - A_n^{\text{sym}})U(s)\varphi\| \, ds$$

By `norm_gen_diff_constant`, this is constant in s:
$$= \int_0^{|t|} \|A\varphi - A_n^{\text{sym}}\varphi\| \, ds = |t| \cdot \|A\varphi - A_n^{\text{sym}}\varphi\|$$
∎

#### Convergence on the Domain

**Theorem** `expBounded_yosidaApproxSym_tendsto_unitary`: For φ ∈ D(A):
$$\exp(t \cdot i \cdot A_n^{\text{sym}})\varphi \to U(t)\varphi$$

*Proof:* From the Duhamel estimate:
$$\|\exp(tB_n)\varphi - U(t)\varphi\| \leq |t| \cdot \|A_n^{\text{sym}}\varphi - A\varphi\|$$

Since Aₙˢʸᵐφ → Aφ on the domain, the RHS → 0. ∎

#### The Cauchy Sequence

**Theorem** `expBounded_yosidaApproxSym_cauchy`: For any ψ ∈ H:
$$\{\exp(t \cdot i \cdot A_n^{\text{sym}})\psi\}_{n \geq 1} \text{ is Cauchy}$$

*Proof (ε/3 argument):*

Given ε > 0:

1. **Approximate by domain:** Choose φ ∈ D(A) with ‖ψ - φ‖ < ε/3.

2. **Cauchy on domain:** The sequence exp(t·i·Aₙˢʸᵐ)φ converges to U(t)φ, hence is Cauchy. Choose N such that m, n ≥ N implies ‖exp(...)ₘφ - exp(...)ₙφ‖ < ε/3.

3. **Triangle inequality:** For m, n ≥ N:
$$\|\exp(...)_m\psi - \exp(...)_n\psi\|$$
$$\leq \|\exp(...)_m(\psi - \varphi)\| + \|\exp(...)_m\varphi - \exp(...)_n\varphi\| + \|\exp(...)_n(\varphi - \psi)\|$$
$$= \|\psi - \varphi\| + \|\exp(...)_m\varphi - \exp(...)_n\varphi\| + \|\varphi - \psi\|$$

(using isometry for the first and third terms)
$$< \frac{\varepsilon}{3} + \frac{\varepsilon}{3} + \frac{\varepsilon}{3} = \varepsilon$$
∎

---

<a name="section-11"></a>
### Section 11: Definition and Properties of exp(itA) (§9 in file)

#### The Definition

**Definition** `exponential'`:
$$\exp(itA)\psi := \lim_{n \to \infty} \exp(t \cdot i \cdot A_n^{\text{sym}})\psi$$

The limit exists by:
1. The sequence is Cauchy (`expBounded_yosidaApproxSym_cauchy`)
2. H is complete

The definition constructs a continuous linear map H →L[ℂ] H via:
- `toFun`: The pointwise limit
- `map_add'`: Limit of sums = sum of limits
- `map_smul'`: Limit of scalar multiples = scalar multiple of limit
- `cont`: Bounded by 1 (limit of isometries)

#### Unitarity

**Theorem** `exponential_unitary`:
$$\langle \exp(itA)\psi, \exp(itA)\varphi \rangle = \langle \psi, \varphi \rangle$$

*Proof:*

Each approximant preserves inner products:
$$\langle \exp(t \cdot i \cdot A_n^{\text{sym}})\psi, \exp(t \cdot i \cdot A_n^{\text{sym}})\varphi \rangle = \langle \psi, \varphi \rangle$$

Inner product is continuous in both arguments:
$$\lim_n \langle \exp(...)_n\psi, \exp(...)_n\varphi \rangle = \langle \exp(itA)\psi, \exp(itA)\varphi \rangle$$

The LHS is constantly ⟨ψ, φ⟩, so the limit equals ⟨ψ, φ⟩. ∎

#### Group Law

**Theorem** `exponential_group_law`:
$$\exp(i(s+t)A)\psi = \exp(isA)(\exp(itA)\psi)$$

*Proof:*

Each approximant satisfies the group law:
$$\exp((s+t) \cdot i \cdot A_n^{\text{sym}}) = \exp(s \cdot i \cdot A_n^{\text{sym}}) \circ \exp(t \cdot i \cdot A_n^{\text{sym}})$$

For the limit, we need to show:
$$\lim_n \exp(s \cdot i \cdot A_n^{\text{sym}})(\exp(t \cdot i \cdot A_n^{\text{sym}})\psi) = \exp(isA)(\exp(itA)\psi)$$

This uses an ε/2 argument:
1. Inner limit: exp(t·i·Aₙˢʸᵐ)ψ → exp(itA)ψ
2. Outer limit: exp(s·i·Aₙˢʸᵐ)χ → exp(isA)χ for the limit χ = exp(itA)ψ
3. Combine using isometry to control the cross term ∎

#### Identity at Zero

**Theorem** `exponential_identity`:
$$\exp(i \cdot 0 \cdot A)\psi = \psi$$

*Proof:* Each exp(0·i·Aₙˢʸᵐ)ψ = ψ, so the constant sequence converges to ψ. ∎

#### Strong Continuity

**Theorem** `exponential_strong_continuous`: For each ψ ∈ H:
$$t \mapsto \exp(itA)\psi \text{ is continuous}$$

*Proof:*

On domain elements, exponential(t)φ = U(t)φ, and U is strongly continuous.

For general ψ, use ε/3:
1. Approximate ψ by φ ∈ D(A)
2. Use continuity at φ
3. Control errors using isometry ‖exp(itA)(ψ - φ)‖ = ‖ψ - φ‖ ∎

#### Generator Equals A

**Theorem** `exponential_generator_eq`: For φ ∈ D(A):
$$\lim_{t \to 0} t^{-1}(\exp(itA)\varphi - \varphi) = iA\varphi$$

*Proof:*

On domain elements, exponential(t)φ = U(t)φ. The generator formula for U gives:
$$\lim_{t \to 0} (it)^{-1}(U(t)\varphi - \varphi) = A\varphi$$

Converting: t⁻¹ = i·(it)⁻¹, so:
$$t^{-1}(U(t)\varphi - \varphi) = i \cdot (it)^{-1}(U(t)\varphi - \varphi) \to i \cdot A\varphi$$
∎

**Corollary:** The generator of the unitary group exp(itA) is A itself.

#### Derivative on Domain

**Theorem** `exponential_derivative_on_domain`: For ψ ∈ D(A):
$$\frac{d}{dt}\exp(itA)\psi = iA \cdot \exp(itA)\psi$$

This is the **Schrödinger equation**: writing ψ(t) = exp(itA)ψ₀:
$$\frac{d\psi}{dt} = iA\psi$$

---

<a name="section-12"></a>
### Section 12: Logical Structure

#### Dependency Diagram

```
                    Resolvent Theory (from Resolvent.lean)
                                 │
                                 ▼
           ┌─────────────────────┴─────────────────────┐
           │                                           │
           ▼                                           ▼
    Yosida Operators                           J Operators
    (Aₙ, Aₙˢʸᵐ, Aₙ⁻)                          (Jₙ, Jₙ⁻)
           │                                           │
           ▼                                           ▼
    Norm Bounds                               Fundamental Identity
    ‖Aₙ‖ ≤ 2n                                Jₙφ = φ - R(in)(Aφ)
           │                                           │
           ▼                                           ▼
    Self-Adjointness                          J Convergence
    (Aₙˢʸᵐ)* = Aₙˢʸᵐ                          Jₙ → I strongly
           │                                           │
           ▼                                           │
    Skew-Adjointness                                   │
    (i·Aₙˢʸᵐ)* = -i·Aₙˢʸᵐ                               
           │                                           │
           ▼                                           ▼
    ┌──────┴──────┐                    Approximant Factorization
    │             │                         Aₙφ = Jₙ(Aφ)
    ▼             │                              │
Bounded           │                              ▼
Exponentials      │                    Approximant Convergence
exp(tB) theory    │                      Aₙˢʸᵐφ → Aφ on D(A)
    │             │                              │
    ▼             │                              │
Yosida Exp        │                              │
Unitarity ────────┴──────────────────────────────┤
    │                                            │
    ▼                                            ▼
    └────────────► Duhamel Formula ◄─────────────┘
                         │
                         ▼
              Duhamel Estimate
              ‖U(t)φ - exp(tBₙ)φ‖ ≤ |t|·‖Aφ - Aₙˢʸᵐφ‖
                         │
                         ▼
              Convergence on Domain
              exp(tBₙ)φ → U(t)φ
                         │
                         ▼
              Cauchy Sequence
              (ε/3 argument)
                         │
                         ▼
              Definition of exp(itA)
              := s-lim exp(t·i·Aₙˢʸᵐ)
                         │
        ┌────────────────┼────────────────┐
        ▼                ▼                ▼
   Unitarity        Group Law      Strong Continuity
        │                │                │
        └────────────────┼────────────────┘
                         ▼
              Generator = A
              (completing Stone's theorem)
```

#### Critical Path

The essential dependencies forming the main proof:

1. Resolvent exists at z = in (Im ≠ 0)
2. Resolvent bound ‖R(in)‖ ≤ 1/n
3. Yosida approximant defined: Aₙˢʸᵐ = (n²/2)(R(in) + R(-in))
4. Self-adjointness of Aₙˢʸᵐ (from resolvent adjoint formula)
5. Unitarity of exp(t·i·Aₙˢʸᵐ) (from skew-adjointness)
6. Factorization Aₙφ = Jₙ(Aφ) on domain
7. Convergence Aₙˢʸᵐφ → Aφ on domain (from Jₙ → I)
8. Duhamel formula (variation of parameters)
9. Duhamel estimate using norm constancy on orbit
10. Cauchy sequence property (ε/3 argument)
11. Definition via limit
12. Properties of limit (unitarity, group law, generator)

---

<a name="section-13"></a>
### Section 13: Summary Tables

#### Table 1: Yosida Operators

| Operator | Definition | Key Property |
|----------|------------|--------------|
| `resolventAtIn n` | R(in) | ‖R(in)‖ ≤ 1/n |
| `resolventAtNegIn n` | R(-in) | R(in)* = R(-in) |
| `yosidaApprox n` | n²R(in) - in·I | Aₙφ → Aφ on D(A) |
| `yosidaApproxSym n` | (n²/2)(R(in) + R(-in)) | Self-adjoint |
| `yosidaJ n` | -in·R(in) | ‖Jₙ‖ ≤ 1, Jₙ → I |
| `yosidaJNeg n` | in·R(-in) | Jₙ* = Jₙ⁻ |

#### Table 2: Norm Bounds

| Bound | Statement | Role |
|-------|-----------|------|
| Resolvent | ‖R(in)‖ ≤ 1/n | Foundation of all estimates |
| Approximant | ‖Aₙ‖ ≤ 2n | Each Aₙ is bounded |
| J operator | ‖Jₙ‖ ≤ 1 | Uniform bound enables ε/3 |
| Exponential | ‖exp(t·i·Aₙˢʸᵐ)‖ = 1 | Unitary, hence isometric |

#### Table 3: Convergence Results

| Result | Statement | Method |
|--------|-----------|--------|
| J on domain | Jₙφ → φ | ‖Jₙφ - φ‖ ≤ (1/n)‖Aφ‖ |
| J on all H | Jₙψ → ψ | ε/3 + uniform bound |
| Approximant on domain | Aₙˢʸᵐφ → Aφ | Aₙφ = Jₙ(Aφ) |
| Exponential on domain | exp(tBₙ)φ → U(t)φ | Duhamel estimate |
| Exponential on all H | exp(tBₙ)ψ Cauchy | ε/3 + isometry |

#### Table 4: Properties of exp(itA)

| Property | Theorem | Proof Method |
|----------|---------|--------------|
| Well-defined | `exponential'` | Limit of Cauchy sequence |
| Linear | `map_add'`, `map_smul'` | Limit of linear ops |
| Bounded | `cont` | Limit of isometries |
| Unitary | `exponential_unitary` | Limit preserves inner product |
| Group law | `exponential_group_law` | Limit + composition |
| Identity | `exponential_identity` | exp(0) = I |
| Strong continuity | `exponential_strong_continuous` | ε/3 via domain |
| Generator = A | `exponential_generator_eq` | Equal to U on domain |

#### Table 5: Duhamel Machinery

| Lemma | Statement | Role |
|-------|-----------|------|
| `expBounded_hasDerivAt_zero` | d/dτ[exp(τB)]|_{τ=0} = B | Start derivative chain |
| `expBounded_hasDerivAt` | d/dτ[exp(τB)] = B·exp(τB) | General derivative |
| `unitary_hasDerivAt` | d/dt[U(t)φ] = iA·U(t)φ | Unitary group derivative |
| `duhamelIntegrand_continuous` | Integrand is continuous | Enables integration |
| `norm_gen_diff_constant` | Norm constant on orbit | Key simplification |
| `duhamel_identity` | FTC gives integral formula | Main identity |
| `duhamel_estimate` | ‖U(t)φ - exp(tBₙ)φ‖ ≤ |t|·‖...‖ | Convergence control |

---

<a name="section-14"></a>
### Section 14: Completing Stone's Theorem

#### The Full Statement

**Stone's Theorem:** There is a bijective correspondence between:
- Self-adjoint operators A on a Hilbert space H
- Strongly continuous one-parameter unitary groups U(t) on H

The correspondence is given by:
- **Forward (Bochner.lean):** U(t) ↦ A (the generator, constructed via resolvent integrals)
- **Reverse (Yosida.lean):** A ↦ exp(itA) (constructed via Yosida approximation)

#### Verification of the Bijection

**Claim 1:** If U(t) is a strongly continuous unitary group with generator A, then exp(itA) = U(t).

*Proof:* By `expBounded_yosidaApproxSym_tendsto_unitary`, for φ ∈ D(A):
$$\exp(t \cdot i \cdot A_n^{\text{sym}})\varphi \to U(t)\varphi$$

By definition, exp(itA)φ = lim exp(t·i·Aₙˢʸᵐ)φ. Therefore exp(itA)φ = U(t)φ for φ ∈ D(A).

Since D(A) is dense and both exp(itA) and U(t) are continuous, equality extends to all of H:
$$\exp(itA) = U(t)$$
∎

**Claim 2:** If A is self-adjoint, then exp(itA) is a strongly continuous unitary group with generator A.

*Proof:*
1. **Unitary:** `exponential_unitary`
2. **Group law:** `exponential_group_law`
3. **Identity:** `exponential_identity`
4. **Strong continuity:** `exponential_strong_continuous`
5. **Generator = A:** `exponential_generator_eq`
∎

**Claim 3:** The correspondence is bijective.

*Proof:*
- Injectivity of U ↦ generator: Proved in Generator.lean (uniqueness)
- Injectivity of A ↦ exp(itA): If exp(itA) = exp(itB), then their generators are equal, so A = B
- Surjectivity: Every self-adjoint A generates exp(itA), and every unitary group has a self-adjoint generator ∎

#### Physical Interpretation

**Quantum Mechanics:** The Hamiltonian H (energy observable) is self-adjoint. Time evolution is:
$$|\psi(t)\rangle = e^{-iHt/\hbar}|\psi(0)\rangle$$

(In our units, ℏ = 1 and A = -H, giving exp(itA) = exp(-iHt).)

Stone's theorem says:
- The Schrödinger equation iℏ∂ψ/∂t = Hψ has a unique unitary solution operator
- This solution operator is exactly exp(-iHt/ℏ)
- The correspondence between Hamiltonians and time evolutions is perfect

**Conservation Laws:** Unitarity (‖exp(itA)ψ‖ = ‖ψ‖) is conservation of probability. The total probability of finding the particle somewhere remains 1 under time evolution.

#### What This Formalization Achieves

1. **Complete proof of Stone's theorem** in Lean 4, without axiomatization of the main results

2. **Two independent constructions:**
   - Resolvent integral (Bochner): analytic, uses ∫e^{-t}U(t) dt
   - Yosida approximation: algebraic, uses n²R(in) - in·I

3. **Machine verification** of delicate analysis:
   - Duhamel formula (variation of parameters)
   - ε/3 arguments for extending convergence
   - Interchange of limits and integration

4. **Modular structure:**
   - Generator.lean: Structure and uniqueness
   - Resolvent.lean: Resolvent properties
   - Bochner.lean: Forward direction
   - Yosida.lean: Reverse direction

5. **Foundation for further work:**
   - Spectral theorem (alternative approach)
   - Perturbation theory
   - Scattering theory
   - Quantum field theory

---

### Appendix: Technical Implementation Notes

#### Lean 4 Specifics

**Continuous Linear Maps:** The exponential is defined as `H →L[ℂ] H`, requiring:
- `toFun`: The underlying function
- `map_add'`: Additivity proof
- `map_smul'`: Scalar multiplication proof
- `cont`: Continuity proof

**Limit Construction:** Uses `limUnder atTop` for the strong operator limit. The existence proof constructs the limit via completeness of H.

**Differentiation:** Uses Mathlib's `HasDerivAt` for real-valued functions into Banach spaces. The Duhamel proof requires:
- `HasDerivAt.comp` for chain rule
- `IsBoundedBilinearMap.hasFDerivAt` for product rule
- `intervalIntegral.integral_eq_sub_of_hasDerivAt` for FTC

**Commutativity:** Extensive use of `Commute` from Mathlib for operator commutativity, enabling the exponential group law.

#### Proof Techniques

**The ε/3 Argument:** Used in three places:
1. Extending Jₙ → I from domain to all H
2. Showing exp(tBₙ)ψ is Cauchy
3. Proving strong continuity of exp(itA)

**Isometry Control:** The uniform bound ‖exp(t·i·Aₙˢʸᵐ)‖ = 1 (from unitarity) is used throughout to control error terms independent of n.

**The Killer Simplification:** `norm_gen_diff_constant` collapses the supremum in the Duhamel estimate to a single value, avoiding difficult uniform convergence arguments.

---

*A natural language companion to Yosida.lean*
*Author: Adam Bornemann*
