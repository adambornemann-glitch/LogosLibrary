# Companion Document: Schrödinger's Uncertainty Relation
**The Forgotten Strengthening of 1930**

## Abstract

This document accompanies a Lean 4 formalization of Schrödinger's strengthened uncertainty relation, published in 1930, which improves upon Robertson's generalized uncertainty principle of 1929. While Robertson's inequality

$$\sigma_A \sigma_B \geq \frac{1}{2}|\langle[A,B]\rangle|$$

has become the standard textbook form, Schrödinger showed that a tighter bound holds:

$$\sigma_A^2 \sigma_B^2 \geq \frac{1}{4}|\langle[A,B]\rangle|^2 + \text{Cov}(A,B)^2$$

The additional covariance term is always non-negative, making Schrödinger's bound at least as tight as Robertson's, and strictly tighter when the observables are correlated in the quantum state.

The formalization demonstrates that:
1. Robertson's inequality is a **corollary** of Schrödinger's, not a separate theorem
2. Both relations follow from **symmetry alone**—self-adjointness is not required
3. The "uncertainty" is **geometric**, arising from the structure of inner product spaces
4. The proof preserves **equality** through the Cauchy-Schwarz decomposition, discarding nothing

This represents one of the first complete formalizations of Schrödinger's strengthening in any proof assistant.

---

## Table of Contents

1. [Historical Context: 1930](#section-1)
2. [The Mathematical Insight](#section-2)
3. [Statement of the Theorems](#section-3)
4. [The Proof Strategy](#section-4)
5. [The Covariance Term](#section-5)
6. [When Does Schrödinger Beat Robertson?](#section-6)
7. [Physical Interpretation](#section-7)
8. [The Proof Architecture](#section-8)
9. [Philosophical Implications](#section-9)
10. [The Forgotten History](#section-10)
11. [What This Formalization Achieves](#section-11)
12. [Epilogue: The Rehabilitation](#section-12)

---

<a name="section-1"></a>
## Section 1: Historical Context: 1930

### The Turbulent Birth of Quantum Mechanics

By 1930, quantum mechanics was only five years old, yet already the subject of fierce debate about its interpretation and mathematical foundations.

**1925-1926:** The *Annus Mirabilis* of quantum mechanics saw two seemingly different formulations emerge:

- **Werner Heisenberg** (Göttingen) developed **matrix mechanics**, representing observables as infinite matrices and states as column vectors. The theory was algebraic and abstract.

- **Erwin Schrödinger** (Zurich) developed **wave mechanics**, representing states as wave functions ψ(x) and observables as differential operators. The theory was analytic and visual.

Schrödinger himself proved the mathematical equivalence of these formulations in 1926, but the *interpretive* battle was just beginning.

### The Copenhagen-Vienna Axis

**Niels Bohr** and **Werner Heisenberg** in Copenhagen championed what became known as the "Copenhagen interpretation":
- The wave function represents our *knowledge* of the system, not the system itself
- Measurement causes "collapse" of the wave function
- Quantum mechanics is *irreducibly probabilistic*
- Complementarity: wave and particle are mutually exclusive but complementary descriptions

**Schrödinger**, along with **Einstein** and later **de Broglie**, resisted this interpretation:
- The wave function should describe *reality*, not just knowledge
- "Collapse" is not a physical process—it's a calculational convenience
- The apparent randomness arises from our incomplete description, not from nature
- There should be a continuous, deterministic underlying theory

### Heisenberg's Uncertainty Principle (1927)

In his famous 1927 paper, Heisenberg introduced the uncertainty principle through the *gamma-ray microscope* thought experiment. He argued that measuring a particle's position disturbs its momentum, leading to:

$$\Delta x \cdot \Delta p \gtrsim h$$

This was a *physical* argument about measurement disturbance, not a mathematical theorem. The notation was imprecise—what exactly did Δx mean? The inequality was approximate.

### Kennard's Rigorous Formulation (1927)

Earl Hesse Kennard, working at Cornell, provided the first *rigorous* statement. For position and momentum operators satisfying $[\hat{x}, \hat{p}] = i\hbar$:

$$\sigma_x \sigma_p \geq \frac{\hbar}{2}$$

where σ denotes standard deviation. This was a mathematical theorem about wave functions, not a statement about measurement disturbance.

### Robertson's Generalization (1929)

Howard Percy Robertson at Princeton generalized Kennard's result to arbitrary observables. For any two self-adjoint operators A and B:

$$\sigma_A \sigma_B \geq \frac{1}{2}|\langle\psi|[A,B]|\psi\rangle|$$

This was published in Physical Review in a short paper of barely two pages. The proof used the Cauchy-Schwarz inequality.

### Schrödinger's Strengthening (1930)

One year later, Schrödinger—then at the University of Berlin—published a short note in the proceedings of the Prussian Academy of Sciences. He observed that Robertson's proof *discards information*.

The Cauchy-Schwarz inequality gives:
$$|\langle u, v \rangle|^2 \leq \|u\|^2 \|v\|^2$$

Robertson used this with $u = (A - \langle A \rangle)\psi$ and $v = (B - \langle B \rangle)\psi$, but he only extracted the *imaginary part* of $\langle u, v \rangle$, throwing away the real part.

Schrödinger kept both parts:
$$\sigma_A^2 \sigma_B^2 \geq \frac{1}{4}|\langle[A,B]\rangle|^2 + \frac{1}{4}|\langle\{Ã,B̃\}\rangle|^2$$

where $Ã = A - \langle A \rangle$ and $\{Ã, B̃\} = ÃB̃ + B̃Ã$ is the anticommutator.

### The Paper That Was Forgotten

Schrödinger's 1930 paper was published in German, in the proceedings of a German academy, just as the political situation in Germany was deteriorating. By 1933, Schrödinger had left Berlin (despite not being Jewish, he found the Nazi regime intolerable), and the paper was largely forgotten.

For decades, textbooks presented only Robertson's inequality. Even Merzbacher's influential *Quantum Mechanics* (1961) derived the Schrödinger form but immediately set the covariance term to zero without comment.

The paper was not translated into English until 1999, when A. Angelow and M. Batoni published an annotated translation in the Bulgarian Journal of Physics.

---

<a name="section-2"></a>
## Section 2: The Mathematical Insight

### What Robertson Did

Robertson's proof proceeds as follows:

**Step 1:** Define shifted operators
$$Ã = A - \langle A \rangle I, \quad B̃ = B - \langle B \rangle I$$

These satisfy $\langle Ã \rangle = \langle B̃ \rangle = 0$ and $[Ã, B̃] = [A, B]$.

**Step 2:** Apply Cauchy-Schwarz
$$|\langle Ã\psi, B̃\psi \rangle|^2 \leq \|Ã\psi\|^2 \cdot \|B̃\psi\|^2 = \text{Var}(A) \cdot \text{Var}(B)$$

**Step 3:** Extract the imaginary part

For self-adjoint A, B, the commutator expectation $\langle[A,B]\rangle$ is purely imaginary. Robertson observed:
$$|\langle Ã\psi, B̃\psi \rangle| \geq |\text{Im}\langle Ã\psi, B̃\psi \rangle| = \frac{1}{2}|\langle[A,B]\rangle|$$

**Step 4:** Combine
$$\text{Var}(A) \cdot \text{Var}(B) \geq \frac{1}{4}|\langle[A,B]\rangle|^2$$

Taking square roots gives Robertson's inequality.

### What Schrödinger Observed

Schrödinger noticed that Step 3 *throws away information*. The complex number $\langle Ã\psi, B̃\psi \rangle$ has both real and imaginary parts:

$$\langle Ã\psi, B̃\psi \rangle = \text{Re}\langle Ã\psi, B̃\psi \rangle + i \cdot \text{Im}\langle Ã\psi, B̃\psi \rangle$$

The Pythagorean theorem in ℂ gives:
$$|\langle Ã\psi, B̃\psi \rangle|^2 = (\text{Re}\langle Ã\psi, B̃\psi \rangle)^2 + (\text{Im}\langle Ã\psi, B̃\psi \rangle)^2$$

Robertson used only the second term. Schrödinger kept both.

### The Decomposition

For symmetric operators A and B, there is a beautiful decomposition:

$$2\langle Ã\psi, B̃\psi \rangle = \langle\psi, \{Ã, B̃\}\psi\rangle + \langle\psi, [Ã, B̃]\psi\rangle$$

where:
- $\{Ã, B̃\} = ÃB̃ + B̃Ã$ is the **anticommutator** (symmetric part)
- $[Ã, B̃] = ÃB̃ - B̃Ã$ is the **commutator** (antisymmetric part)

For symmetric operators:
- The anticommutator expectation is **real**: $\langle\{Ã, B̃\}\rangle \in \mathbb{R}$
- The commutator expectation is **purely imaginary**: $\langle[Ã, B̃]\rangle \in i\mathbb{R}$

Therefore:
$$\text{Re}\langle Ã\psi, B̃\psi \rangle = \frac{1}{2}\langle\{Ã, B̃\}\rangle$$
$$\text{Im}\langle Ã\psi, B̃\psi \rangle = \frac{1}{2i}\langle[A, B]\rangle$$

### The Schrödinger Bound

Combining everything:

$$|\langle Ã\psi, B̃\psi \rangle|^2 = \frac{1}{4}|\langle\{Ã, B̃\}\rangle|^2 + \frac{1}{4}|\langle[A, B]\rangle|^2$$

This is an **equality**, not an inequality! The only inequality in the entire proof is Cauchy-Schwarz:

$$\text{Var}(A) \cdot \text{Var}(B) \geq |\langle Ã\psi, B̃\psi \rangle|^2 = \frac{1}{4}|\langle\{Ã, B̃\}\rangle|^2 + \frac{1}{4}|\langle[A, B]\rangle|^2$$

Robertson's inequality follows by dropping the non-negative anticommutator term.

---

<a name="section-3"></a>
## Section 3: Statement of the Theorems

### Robertson's Uncertainty Relation (1929)

**Theorem (Robertson):** Let A and B be symmetric operators on a Hilbert space H, and let ψ be a normalized state in the domain of A, B, AB, and BA. Then:

$$\sigma_A \sigma_B \geq \frac{1}{2}|\langle\psi, [A,B]\psi\rangle|$$

where $\sigma_A = \sqrt{\langle(A - \langle A \rangle)^2\rangle}$ is the standard deviation.

### Schrödinger's Strengthened Relation (1930)

**Theorem (Schrödinger):** Under the same hypotheses:

$$\sigma_A^2 \sigma_B^2 \geq \frac{1}{4}|\langle\psi, [A,B]\psi\rangle|^2 + \text{Cov}(A,B)^2$$

where the **quantum covariance** is:

$$\text{Cov}(A,B) = \frac{1}{2}\langle\psi, \{Ã, B̃\}\psi\rangle = \frac{1}{2}\left(\langle AB + BA \rangle - 2\langle A \rangle\langle B \rangle\right)$$

### Robertson as a Corollary

**Corollary:** Robertson's inequality follows from Schrödinger's by dropping a non-negative term:

$$\sigma_A^2 \sigma_B^2 \geq \frac{1}{4}|\langle[A,B]\rangle|^2 + \underbrace{\text{Cov}(A,B)^2}_{\geq 0} \geq \frac{1}{4}|\langle[A,B]\rangle|^2$$

### The Hierarchy

```
Cauchy-Schwarz Inequality (Pure Mathematics)
            ↓
            ↓  Applied to shifted operators Ã, B̃
            ↓
Schrödinger's Uncertainty Relation (Full geometric content)
            ↓
            ↓  Drop covariance term (lose information)
            ↓
Robertson's Uncertainty Relation (Commutator bound only)
            ↓
            ↓  Specialize to [x,p] = iℏ
            ↓
Heisenberg-Kennard Relation (σ_x σ_p ≥ ℏ/2)
```

---

<a name="section-4"></a>
## Section 4: The Proof Strategy

### Overview

The proof proceeds in six steps:

1. **Shift by expectations** — Define Ã = A - ⟨A⟩I, B̃ = B - ⟨B⟩I
2. **Apply Cauchy-Schwarz** — Var(A)·Var(B) ≥ |⟨Ãψ, B̃ψ⟩|²
3. **Decompose the inner product** — 2⟨Ãψ, B̃ψ⟩ = ⟨{Ã,B̃}⟩ + ⟨[Ã,B̃]⟩
4. **Identify real and imaginary parts** — Use symmetry of operators
5. **Apply Pythagorean theorem** — |z|² = Re(z)² + Im(z)²
6. **Relate to original operators** — Commutator is shift-invariant

### Step 1: Shift by Expectations

Define the centered operators:
$$Ã := A - \langle A \rangle_\psi I$$
$$B̃ := B - \langle B \rangle_\psi I$$

**Key properties:**
- $\langle Ã \rangle = \langle B̃ \rangle = 0$ (zero mean)
- $[Ã, B̃] = [A, B]$ (commutator is shift-invariant)
- $\|Ã\psi\|^2 = \text{Var}(A)$ (variance as squared norm)
- Symmetry is preserved: if A is symmetric, so is Ã

The shift-invariance of the commutator is crucial and follows from:
$$[A - λI, B - μI] = AB - AμI - λIB + λμI - BA + BλI + μIA - λμI = AB - BA = [A,B]$$

### Step 2: Apply Cauchy-Schwarz

The Cauchy-Schwarz inequality in an inner product space states:
$$|\langle u, v \rangle|^2 \leq \langle u, u \rangle \cdot \langle v, v \rangle = \|u\|^2 \cdot \|v\|^2$$

Applied to $u = Ã\psi$ and $v = B̃\psi$:
$$|\langle Ã\psi, B̃\psi \rangle|^2 \leq \|Ã\psi\|^2 \cdot \|B̃\psi\|^2 = \text{Var}(A) \cdot \text{Var}(B)$$

**This is the only inequality in the entire proof.**

### Step 3: Decompose the Inner Product

Using symmetry of A (so $\langle A\psi, \phi \rangle = \langle \psi, A\phi \rangle$):

$$\langle Ã\psi, B̃\psi \rangle = \langle \psi, ÃB̃\psi \rangle$$

Now use the algebraic identity:
$$2ÃB̃ = (ÃB̃ + B̃Ã) + (ÃB̃ - B̃Ã) = \{Ã, B̃\} + [Ã, B̃]$$

Therefore:
$$2\langle Ã\psi, B̃\psi \rangle = \langle\psi, \{Ã, B̃\}\psi\rangle + \langle\psi, [Ã, B̃]\psi\rangle$$

### Step 4: Identify Real and Imaginary Parts

**Lemma (Anticommutator is Real):** For symmetric A, B:
$$\langle\psi, \{Ã, B̃\}\psi\rangle \in \mathbb{R}$$

*Proof:* The anticommutator of symmetric operators is symmetric:
$$\langle \{Ã, B̃\}\psi, \phi \rangle = \langle ÃB̃\psi, \phi \rangle + \langle B̃Ã\psi, \phi \rangle = \langle \psi, B̃Ã\phi \rangle + \langle \psi, ÃB̃\phi \rangle = \langle \psi, \{Ã, B̃\}\phi \rangle$$

For a symmetric operator S, $\langle\psi, S\psi\rangle = \overline{\langle S\psi, \psi\rangle} = \overline{\langle\psi, S\psi\rangle}$, so $\langle\psi, S\psi\rangle \in \mathbb{R}$. ∎

**Lemma (Commutator is Imaginary):** For symmetric A, B:
$$\langle\psi, [A, B]\psi\rangle \in i\mathbb{R}$$

*Proof:* 
$$\langle\psi, [A,B]\psi\rangle = \langle\psi, AB\psi\rangle - \langle\psi, BA\psi\rangle = \langle A\psi, B\psi\rangle - \langle B\psi, A\psi\rangle$$
$$= \langle A\psi, B\psi\rangle - \overline{\langle A\psi, B\psi\rangle} = 2i \cdot \text{Im}\langle A\psi, B\psi\rangle$$

This is purely imaginary. ∎

### Step 5: Apply Pythagorean Theorem

Let $D = \langle\{Ã, B̃\}\rangle$ (real) and $C = \langle[A, B]\rangle$ (purely imaginary).

Then:
$$2\langle Ã\psi, B̃\psi \rangle = D + C$$

The squared norm:
$$|2\langle Ã\psi, B̃\psi \rangle|^2 = |D + C|^2 = D^2 + |C|^2$$

(This uses Re(C) = 0 and Im(D) = 0.)

Therefore:
$$4|\langle Ã\psi, B̃\psi \rangle|^2 = \langle\{Ã, B̃\}\rangle^2 + |\langle[A, B]\rangle|^2$$

### Step 6: Final Assembly

Combining Steps 2 and 5:

$$\text{Var}(A) \cdot \text{Var}(B) \geq |\langle Ã\psi, B̃\psi \rangle|^2 = \frac{1}{4}\langle\{Ã, B̃\}\rangle^2 + \frac{1}{4}|\langle[A, B]\rangle|^2$$

Recognizing that $\frac{1}{2}\langle\{Ã, B̃\}\rangle = \text{Cov}(A,B)$:

$$\boxed{\sigma_A^2 \sigma_B^2 \geq \frac{1}{4}|\langle[A, B]\rangle|^2 + \text{Cov}(A,B)^2}$$

This is Schrödinger's uncertainty relation.

---

<a name="section-5"></a>
## Section 5: The Covariance Term

### Definition of Quantum Covariance

The **quantum covariance** of observables A and B in state ψ is:

$$\text{Cov}(A,B) := \frac{1}{2}\langle\psi, \{Ã, B̃\}\psi\rangle = \frac{1}{2}\left(\langle AB + BA \rangle - 2\langle A \rangle\langle B \rangle\right)$$

Equivalently:
$$\text{Cov}(A,B) = \frac{1}{2}\langle AB + BA \rangle - \langle A \rangle\langle B \rangle$$

### Comparison with Classical Covariance

In classical probability theory, the covariance of random variables X and Y is:
$$\text{Cov}(X,Y) = \mathbb{E}[XY] - \mathbb{E}[X]\mathbb{E}[Y]$$

In quantum mechanics, since A and B may not commute, "AB" is ambiguous. The symmetric ordering $\frac{1}{2}(AB + BA)$ is the natural quantum analogue, leading to:
$$\text{Cov}(A,B) = \frac{1}{2}\langle AB + BA \rangle - \langle A \rangle\langle B \rangle$$

This is **real** for symmetric operators, just like classical covariance.

### Properties of Quantum Covariance

1. **Symmetry:** $\text{Cov}(A,B) = \text{Cov}(B,A)$

2. **Bilinearity:** $\text{Cov}(αA + βA', B) = α\text{Cov}(A,B) + β\text{Cov}(A',B)$

3. **Variance recovery:** $\text{Cov}(A,A) = \text{Var}(A)$

4. **Shift invariance:** $\text{Cov}(A + λI, B + μI) = \text{Cov}(A,B)$

5. **Bounds:** By Schrödinger's inequality:
   $$|\text{Cov}(A,B)| \leq \sigma_A \sigma_B$$
   
   (This is the quantum analogue of the classical correlation bound.)

### Physical Interpretation

The covariance measures the **correlation** between observables in the quantum state:

- **Cov(A,B) > 0:** Positive correlation—knowing A is above average suggests B is above average
- **Cov(A,B) < 0:** Negative correlation—knowing A is above average suggests B is below average
- **Cov(A,B) = 0:** Uncorrelated—no linear relationship between A and B in this state

**Important:** Uncorrelated does NOT mean independent in quantum mechanics. Even with Cov(A,B) = 0, the observables may still exhibit quantum correlations detectable through the commutator.

### The Correlation Coefficient

Define the **quantum correlation coefficient**:
$$\rho(A,B) := \frac{\text{Cov}(A,B)}{\sigma_A \sigma_B}$$

By Schrödinger's inequality:
$$|\rho(A,B)| \leq \sqrt{1 - \frac{|\langle[A,B]\rangle|^2}{4\sigma_A^2\sigma_B^2}}$$

When the commutator term is large, the correlation coefficient is bounded away from ±1.

---

<a name="section-6"></a>
## Section 6: When Does Schrödinger Beat Robertson?

### The Equality Cases

**Robertson is tight** (Schrödinger = Robertson) when:
$$\text{Cov}(A,B) = 0$$

This occurs when the observables are uncorrelated in the quantum state.

**Schrödinger is strictly stronger** when:
$$\text{Cov}(A,B) \neq 0$$

### Example 1: Gaussian Wave Packets (Robertson is Tight)

For position and momentum with a Gaussian wave packet centered at the origin:
$$\psi(x) = \left(\frac{1}{2\pi\sigma_x^2}\right)^{1/4} \exp\left(-\frac{x^2}{4\sigma_x^2}\right)$$

One can verify:
- $\langle x \rangle = \langle p \rangle = 0$
- $\langle xp + px \rangle = 0$ (by symmetry)
- Therefore $\text{Cov}(x,p) = 0$

The Schrödinger bound reduces to Robertson's bound, which is saturated:
$$\sigma_x \sigma_p = \frac{\hbar}{2}$$

These are the **minimum uncertainty states** for position-momentum.

### Example 2: Displaced Gaussians (Robertson is Tight)

Even if $\langle x \rangle \neq 0$ or $\langle p \rangle \neq 0$, centered Gaussians have:
$$\text{Cov}(x,p) = \frac{1}{2}\langle xp + px \rangle - \langle x \rangle\langle p \rangle = 0$$

Robertson remains tight.

### Example 3: Squeezed States (Schrödinger is Stronger)

A squeezed vacuum state has:
$$\sigma_x \sigma_p = \frac{\hbar}{2}\cosh(2r)$$

where r is the squeezing parameter. The covariance is:
$$\text{Cov}(x,p) = \frac{\hbar}{2}\sinh(2r)$$

For r > 0, the Schrödinger bound gives:
$$\sigma_x^2 \sigma_p^2 \geq \frac{\hbar^2}{4} + \frac{\hbar^2}{4}\sinh^2(2r) = \frac{\hbar^2}{4}\cosh^2(2r)$$

This is strictly stronger than Robertson's $\sigma_x^2 \sigma_p^2 \geq \frac{\hbar^2}{4}$.

In fact, squeezed states **saturate** Schrödinger's inequality—they achieve equality.

### Example 4: Qubits (Schrödinger is Always Exact)

For two-level quantum systems (qubits), a remarkable fact holds:

**Theorem:** For any qubit state ψ and any pair of observables A, B:
$$\sigma_A^2 \sigma_B^2 = \frac{1}{4}|\langle[A,B]\rangle|^2 + \text{Cov}(A,B)^2$$

Schrödinger's inequality is an **equality** for all qubits!

*Proof sketch:* This follows from the geometry of SU(2) acting on the Bloch sphere. The three Pauli matrices span all traceless observables, and SU(2) acts transitively, leaving no "slack" in the Cauchy-Schwarz inequality.

### Summary Table

| System | State | Cov(A,B) | Schrödinger vs Robertson |
|--------|-------|----------|--------------------------|
| Position-Momentum | Centered Gaussian | 0 | Equal (both tight) |
| Position-Momentum | Squeezed state | ≠ 0 | Schrödinger strictly stronger |
| Position-Momentum | Coherent state | 0 | Equal (both tight) |
| Qubit | Any state | varies | Schrödinger is exact equality |
| Angular momentum | Spin coherent state | 0 | Equal |
| Angular momentum | Squeezed spin state | ≠ 0 | Schrödinger strictly stronger |

---

<a name="section-7"></a>
## Section 7: Physical Interpretation

### The Geometric Picture

The uncertainty relation has a beautiful geometric interpretation in phase space.

Consider the complex number:
$$z = \langle Ã\psi, B̃\psi \rangle \in \mathbb{C}$$

This lies in the complex plane with:
- **Real axis:** Covariance (correlation between A and B)
- **Imaginary axis:** Half the commutator expectation (incompatibility of A and B)

The Cauchy-Schwarz inequality says:
$$|z|^2 \leq \sigma_A^2 \sigma_B^2$$

The point z must lie within a disk of radius $\sigma_A \sigma_B$.

**Robertson** bounds only the imaginary part: $|z| \geq |\text{Im}(z)|$
**Schrödinger** uses the full Pythagorean theorem: $|z|^2 = \text{Re}(z)^2 + \text{Im}(z)^2$

### Incompatibility vs. Correlation

The uncertainty relation captures **two distinct sources** of uncertainty product:

1. **Incompatibility** (commutator term): A and B cannot be simultaneously diagonalized. Measuring one disturbs the other. This is the genuinely "quantum" contribution.

2. **Correlation** (covariance term): A and B are statistically correlated in the state. Even classically correlated variables have $\text{Var}(A)\text{Var}(B) \geq \text{Cov}(A,B)^2$.

Robertson captures only incompatibility. Schrödinger captures both.

### The Symplectic Perspective

In phase space, the covariance matrix of position and momentum is:
$$\Sigma = \begin{pmatrix} \sigma_x^2 & \text{Cov}(x,p) \\ \text{Cov}(x,p) & \sigma_p^2 \end{pmatrix}$$

The Schrödinger uncertainty relation is equivalent to:
$$\det(\Sigma) \geq \frac{\hbar^2}{4}$$

This has a beautiful interpretation: the phase space uncertainty ellipse must have area at least $\pi\hbar/2$.

More generally, for n modes with covariance matrix Σ:
$$\Sigma + \frac{i\hbar}{2}J \geq 0$$

where $J$ is the symplectic form. This is the **Robertson-Schrödinger uncertainty principle** in its symplectic formulation.

### Why Physicists Ignored the Covariance

Several reasons explain the historical neglect of Schrödinger's strengthening:

1. **Position-momentum with Gaussians:** The most common example has Cov(x,p) = 0, so Robertson suffices.

2. **Commutator is "more quantum":** The commutator captures what's uniquely quantum about uncertainty—the covariance also appears classically.

3. **Simpler formula:** Robertson's bound $\sigma_A\sigma_B \geq \frac{1}{2}|\langle[A,B]\rangle|$ is cleaner than Schrödinger's.

4. **State-independence:** For canonical pairs, $[x,p] = i\hbar$ is state-independent, while Cov(x,p) varies with the state.

5. **Historical accident:** Schrödinger's paper was in German, in a German academy, published as Europe descended into chaos.

---

<a name="section-8"></a>
## Section 8: The Proof Architecture

### File Structure

The formalization consists of two main files:

```
Uncertainty Relation Formalization
│
├── Core.lean (~800 lines)
│   ├── Hilbert space structures
│   ├── Observable definitions (bounded and unbounded)
│   ├── Statistical quantities (expectation, variance, std dev)
│   ├── Commutator and anticommutator
│   ├── Key lemmas:
│   │   ├── expectation_commutator_re_eq_zero
│   │   ├── expectation_anticommutator_im_eq_zero
│   │   ├── isSymmetric_sub_smul_of_real
│   │   └── inner_product_decomposition
│   └── Physical constants and examples
│
└── Theorem.lean (~600 lines)
    ├── Robertson's uncertainty principle
    ├── Schrödinger's strengthened relation
    ├── Robertson as corollary of Schrödinger
    ├── Quantum covariance definition
    └── Schrödinger with explicit covariance
```

### Key Structures

**UnboundedObservable:** Represents a (possibly unbounded) symmetric operator
```lean
structure UnboundedObservable (H : Type*) [NormedAddCommGroup H] 
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  op : H →ₗ[ℂ] H
  domain : Submodule ℂ H
  dense : Dense (domain : Set H)
  SymmetricOperator : ∀ (ψ φ : H), ψ ∈ domain → φ ∈ domain →
    ⟪op ψ, φ⟫_ℂ = ⟪ψ, op φ⟫_ℂ
```

**Key observation:** Only symmetry is required, not self-adjointness!

### The Main Theorems

**Robertson:**
```lean
theorem robertson_uncertainty_principle :
    unboundedStandardDeviation A ψ * unboundedStandardDeviation B ψ ≥
    (1/2) * ‖⟪ψ, [A.op, B.op] ψ⟫_ℂ‖
```

**Schrödinger:**
```lean
theorem schrodinger_uncertainty_principle :
    unboundedVariance A ψ * unboundedVariance B ψ ≥
    (1/4) * ‖⟪ψ, [A.op, B.op] ψ⟫_ℂ‖^2 +
    (1/4) * (⟪ψ, {Ã, B̃} ψ⟫_ℂ).re^2
```

**Robertson from Schrödinger:**
```lean
theorem robertson_from_schrodinger :
    unboundedVariance A ψ * unboundedVariance B ψ ≥
    (1/4) * ‖⟪ψ, [A.op, B.op] ψ⟫_ℂ‖^2 := by
  have h_schrodinger := schrodinger_uncertainty_principle ...
  have h_cov_nonneg : 0 ≤ (1/4) * (...).re^2 := by
    apply mul_nonneg; norm_num; exact sq_nonneg _
  linarith
```

### Proof Flow

```
┌─────────────────────────────────────────────────────────────────┐
│                         Core.lean                               │
│                                                                 │
│  isSymmetric_sub_smul_of_real                                   │
│  "Shifting a symmetric operator by a real scalar preserves      │
│   symmetry"                                                     │
│                           ↓                                     │
│  expectation_commutator_re_eq_zero                              │
│  "Commutator expectation is purely imaginary"                   │
│                           ↓                                     │
│  expectation_anticommutator_im_eq_zero                          │
│  "Anticommutator expectation is purely real"                    │
│                           ↓                                     │
│  inner_product_decomposition                                    │
│  "2⟨Ãψ,B̃ψ⟩ = ⟨{Ã,B̃}⟩ + ⟨[Ã,B̃]⟩"                                 │
└─────────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────────┐
│                       Theorem.lean                              │
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │ schrodinger_uncertainty_principle                       │    │
│  │                                                         │    │
│  │ Step 1: Shift operators (A' = A - ⟨A⟩I)                 │    │
│  │ Step 2: Cauchy-Schwarz (Var(A)Var(B) ≥ |⟨A'ψ,B'ψ⟩|²)    │    │
│  │ Step 3: Decompose inner product                         │    │
│  │ Step 4: Pythagorean theorem (keep BOTH terms!)          │    │
│  │ Step 5: Commutator is shift-invariant                   │    │
│  │ Step 6: Final assembly                                  │    │
│  └─────────────────────────────────────────────────────────┘    │
│                           ↓                                     │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │ robertson_from_schrodinger                              │    │
│  │                                                         │    │
│  │ "Drop the covariance term (it's ≥ 0)"                   │    │
│  │ Uses: linarith                                          │    │
│  └─────────────────────────────────────────────────────────┘    │
│                           ↓                                     │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │ schrodinger_with_covariance                             │    │
│  │                                                         │    │
│  │ "Express in terms of quantum covariance"                │    │
│  │ Cov(A,B) = ½⟨{Ã,B̃}⟩                                     │    │
│  └─────────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────────┘
```

---

<a name="section-9"></a>
## Section 9: Philosophical Implications

### Symmetry Suffices

A crucial insight from this formalization: **the uncertainty relation requires only symmetry, not self-adjointness.**

An operator A is **symmetric** if:
$$\langle A\psi, \phi \rangle = \langle \psi, A\phi \rangle \quad \forall \psi, \phi \in D(A)$$

An operator A is **self-adjoint** if it is symmetric AND $D(A^*) = D(A)$.

The distinction matters for unbounded operators:
- Momentum $P = -i\hbar\frac{d}{dx}$ on $L^2[0,1]$ is symmetric for many boundary conditions
- It is self-adjoint only for specific choices (e.g., periodic boundary conditions)

**Self-adjointness is required for:**
- The spectral theorem
- Stone's theorem (generating unitary groups)
- The Born rule interpretation (real eigenvalues as measurement outcomes)

**Self-adjointness is NOT required for:**
- The uncertainty relation

This suggests that the uncertainty bound is more fundamental than the measurement interpretation—it's a geometric fact about Hilbert spaces that would hold in any theory with this mathematical structure.

### Uncertainty as Geometry

The proof makes clear that uncertainty is **geometric**, not ontological:

1. States are vectors in a Hilbert space
2. Observables act as linear operators
3. Cauchy-Schwarz relates inner products to norms
4. The commutator/anticommutator decomposition is pure algebra

There is no reference to:
- Measurement
- Wave function collapse
- Observer effects
- Intrinsic randomness

The uncertainty relation is a theorem about inner product spaces. It would hold for *any* physical theory formulated in this mathematical language.

### The Source of "Quantum Randomness"

The formalization supports a view that "quantum randomness" arises from description, not from nature:

1. The full quantum state evolves deterministically (Schrödinger equation)
2. When we describe a subsystem, we trace out degrees of freedom
3. This tracing introduces apparent randomness (reduced density matrix)
4. The uncertainty relation quantifies this "cost of truncation"

As noted in the original conversation: *"The 'randomness' isn't in the physics. It's in the truncation. It's perspectival."*

### Covariance as Classical Residue

The covariance term Cov(A,B) also appears in classical probability theory. It represents correlation that would exist even classically.

Only the commutator term $\frac{1}{4}|\langle[A,B]\rangle|^2$ is uniquely quantum—it vanishes for commuting observables and represents the irreducible incompatibility of quantum measurements.

Schrödinger's formula thus cleanly separates:
- **Classical uncertainty:** Cov(A,B)² (correlation-based)
- **Quantum uncertainty:** ¼|⟨[A,B]⟩|² (incompatibility-based)

---

<a name="section-10"></a>
## Section 10: The Forgotten History

### The 1930 Paper

Schrödinger's paper "Zum Heisenbergschen Unschärfeprinzip" appeared in the Sitzungsberichte der Preussischen Akademie der Wissenschaften, Physikalisch-mathematische Klasse, volume 14, pages 296-303.

The Prussian Academy of Sciences had been one of the most prestigious scientific institutions in the world since its founding in 1700. Its proceedings had published papers by Planck, Einstein, and many others.

But by 1930, the Academy was in decline. The economic chaos of Weimar Germany, followed by the rise of Nazism, would soon destroy German scientific preeminence. Many of the Academy's members would be forced into exile or worse.

### Schrödinger's Departure

In 1933, Schrödinger left Berlin. Unlike many colleagues, he was not Jewish—he simply found the Nazi regime intolerable. He would spend the next years in Oxford, Graz (briefly), and finally Dublin, where he remained at the Institute for Advanced Studies until 1956.

His 1930 paper, published in German in the proceedings of an institution that would soon be politicized and marginalized, was largely forgotten.

### The English Translation

It was not until 1999—69 years later—that an English translation appeared. A. Angelow and M. Batoni published "About Heisenberg Uncertainty Relation (by E. Schrödinger)" in the Bulgarian Journal of Physics, volume 26, pages 193-203. An annotated version also appeared on the arXiv (quant-ph/9903100).

The translators noted in their introduction:

*"The main reason to publish the original Schrödinger's paper in English, is the fact that no one of the books on Quantum Mechanics cites it."*

### Textbook Neglect

Even comprehensive quantum mechanics textbooks typically present only Robertson's inequality:

- **Sakurai** (Modern Quantum Mechanics): Robertson only
- **Griffiths** (Introduction to Quantum Mechanics): Robertson only, Schrödinger as exercise
- **Messiah** (Quantum Mechanics): Robertson only
- **Cohen-Tannoudji** (Quantum Mechanics): Robertson only
- **Merzbacher** (Quantum Mechanics): Derives Schrödinger form, immediately sets covariance to zero

The Schrödinger strengthening survived mainly in specialized literature on squeezed states, quantum optics, and quantum information theory—fields where the covariance term actually matters.

### Recent Revival

In recent years, there has been renewed interest in uncertainty relations beyond Robertson:

- **Maccone-Pati (2014):** Sum-based uncertainty relations that are nontrivial even when ⟨[A,B]⟩ = 0
- **Quantum information theory:** Entropic uncertainty relations (Maassen-Uffink, etc.)
- **Quantum metrology:** Schrödinger's relation determines precision limits
- **Quantum optics:** Squeezed states saturate Schrödinger, not Robertson

The Schrödinger uncertainty relation is finally receiving the attention it deserves.

---

<a name="section-11"></a>
## Section 11: What This Formalization Achieves

### Technical Achievements

1. **Complete proof of Schrödinger's uncertainty relation** with all domain tracking for unbounded operators

2. **Robertson as a corollary:** Explicitly derived from Schrödinger by dropping a non-negative term

3. **Symmetry suffices:** The proof uses only operator symmetry, not self-adjointness

4. **Full equality preservation:** The Cauchy-Schwarz decomposition maintains equality through the Pythagorean theorem

5. **Machine verification:** Every step is checked by Lean's type system—no gaps, no hand-waving

### Pedagogical Achievements

1. **Correct logical order:** Schrödinger is the theorem; Robertson is the corollary

2. **Geometric clarity:** The proof reveals uncertainty as inner product geometry

3. **Physical interpretation:** Separation of classical correlation (covariance) from quantum incompatibility (commutator)

4. **Historical accuracy:** Proper attribution to Schrödinger's 1930 contribution

### Philosophical Achievements

1. **Uncertainty is geometric:** Not a statement about measurement or knowledge, but about Hilbert space structure

2. **Symmetry, not self-adjointness:** The bound is more fundamental than spectral theory

3. **No ontological claims:** The proof makes no reference to "intrinsic randomness" or "measurement disturbance"

---

<a name="section-12"></a>
## Section 12: Epilogue: The Rehabilitation

### Schrödinger's Late Views

In his final decades, Schrödinger wrote extensively about the interpretation of quantum mechanics. He remained convinced that:

1. The wave function represents physical reality, not just knowledge
2. The Schrödinger equation is complete—no "collapse" is needed
3. The apparent randomness arises from our incomplete description

These views were dismissed as "old-fashioned" by the Copenhagen mainstream. But they anticipated later developments:

- **Everett's many-worlds interpretation (1957):** Takes the wave function as literally real
- **Decoherence theory (1970s-present):** Explains apparent collapse as entanglement with environment
- **Quantum Darwinism (2000s):** Explains classical emergence from quantum substrate

Schrödinger may have been right all along.

### The Wave Function is Real

Modern developments increasingly support treating the wave function as physically real:

- **PBR theorem (2012):** Under mild assumptions, the wave function cannot be merely epistemic
- **Quantum computing:** Exploits interference of wave function amplitudes
- **Quantum error correction:** Protects coherent superpositions as physical resources

The "Copenhagen interpretation" is no longer the consensus view among physicists who think carefully about foundations.

### The Uncertainty Principle Reconsidered

The Schrödinger formalization suggests reconsidering what the uncertainty principle actually says:

**Not:** "Nature is inherently random"
**Not:** "Measurement disturbs the system"
**Not:** "We cannot know both position and momentum"

**Rather:** "In a Hilbert space with symmetric operators satisfying certain commutation relations, the product of standard deviations has a geometric lower bound."

This is a mathematical theorem. Its physical interpretation depends on what we take the Hilbert space and operators to represent.

### A Machine-Verified Truth

This formalization joins a small but growing body of machine-verified physics:

- Kepler's laws from Newton's laws (various formalizations)
- Special relativity (Coq, Isabelle)
- Quantum computing (various proof assistants)
- Stone's theorem (this project)
- Schrödinger's uncertainty relation (this project)

As these formalizations accumulate, we approach a new standard of rigor in mathematical physics—one where "proof" means "verified by machine," not "published in a journal."

Schrödinger's 1930 result, ignored for ninety years, is now proven beyond any possibility of doubt.

---

## Final Summary

```
================================================================================
            SCHRÖDINGER'S UNCERTAINTY RELATION (Complete)
================================================================================

Let A and B be symmetric operators on a Hilbert space H.
Let ψ be a normalized state in the appropriate domain.

THEOREM (Schrödinger 1930): 

    σ_A² σ_B² ≥ (1/4)|⟨[A,B]⟩|² + Cov(A,B)²

where:
    • σ_A² = Var(A) = ⟨(A - ⟨A⟩)²⟩
    • [A,B] = AB - BA  (commutator)
    • Cov(A,B) = ½⟨{Ã,B̃}⟩ = ½(⟨AB+BA⟩ - 2⟨A⟩⟨B⟩)  (quantum covariance)

--------------------------------------------------------------------------------

COROLLARY (Robertson 1929):

    σ_A σ_B ≥ (1/2)|⟨[A,B]⟩|

Proof: Drop the non-negative covariance term from Schrödinger's relation.

--------------------------------------------------------------------------------

KEY INSIGHTS:

    • Only SYMMETRY is required, not self-adjointness
    • The uncertainty bound is GEOMETRIC (Cauchy-Schwarz + Pythagoras)
    • Robertson DISCARDS the covariance term; Schrödinger KEEPS it
    • The separation reveals:
        - Quantum incompatibility: (1/4)|⟨[A,B]⟩|²
        - Classical correlation: Cov(A,B)²

--------------------------------------------------------------------------------

FORMALIZATION:

    • ~1400 lines of Lean 4 code
    • Machine-verified proofs
    • Complete treatment of unbounded operators
    • Robertson derived as corollary of Schrödinger

================================================================================
```

---

## References

### Primary Sources

1. **Schrödinger, E.** (1930). "Zum Heisenbergschen Unschärfeprinzip." *Sitzungsberichte der Preussischen Akademie der Wissenschaften, Physikalisch-mathematische Klasse* 14: 296-303.

2. **Robertson, H.P.** (1929). "The Uncertainty Principle." *Physical Review* 34(2): 163-164.

3. **Kennard, E.H.** (1927). "Zur Quantenmechanik einfacher Bewegungstypen." *Zeitschrift für Physik* 44(4-5): 326-352.

4. **Heisenberg, W.** (1927). "Über den anschaulichen Inhalt der quantentheoretischen Kinematik und Mechanik." *Zeitschrift für Physik* 43(3-4): 172-198.

### Translations and Commentary

5. **Angelow, A. & Batoni, M.** (1999). "About Heisenberg Uncertainty Relation (by E. Schrödinger)." *Bulgarian Journal of Physics* 26(5/6): 193-203. [arXiv:quant-ph/9903100]

6. **Angelow, A.** (2007). "Evolution of Schrödinger Uncertainty Relation in Quantum Mechanics." [arXiv:0710.0670]

### Modern Developments

7. **Maccone, L. & Pati, A.K.** (2014). "Stronger Uncertainty Relations for All Incompatible Observables." *Physical Review Letters* 113: 260401.

8. **Gutiérrez, J.C. et al.** (2021). "Robertson-Schrödinger uncertainty relation for qubits: a visual approach." *European Journal of Physics* 42: 035401.

9. **Kimura, G. et al.** (2025). "Beyond Robertson-Schrödinger: A General Uncertainty Relation Unveiling Hidden Noncommutative Trade-offs." [arXiv:2504.20404]

### Textbooks

10. **Sakurai, J.J. & Napolitano, J.** (2017). *Modern Quantum Mechanics*, 2nd ed. Cambridge University Press.

11. **Hall, B.C.** (2013). *Quantum Theory for Mathematicians*. Springer.

12. **Griffiths, D.J. & Schroeter, D.F.** (2018). *Introduction to Quantum Mechanics*, 3rd ed. Cambridge University Press.

### Philosophical Works

13. **Bitbol, M.** (1996). *Schrödinger's Philosophy of Quantum Mechanics*. Kluwer.

14. **Fine, A.** (1986). *The Shaky Game: Einstein, Realism and the Quantum Theory*. University of Chicago Press.

---

*This companion document accompanies the Lean 4 formalization of Schrödinger's uncertainty relation.*

*Mathematical content: Erwin Schrödinger (1930)*
*Formalization: Adam Bornemann*
*Companion document: Written in collaboration with a role-played Schrödinger, January 2026*
