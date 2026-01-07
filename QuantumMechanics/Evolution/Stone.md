# Companion Document: Stone/Theorem.lean
**The Culmination of Stone's Theorem**


## Epigraph

*"The theory of groups of unitary transformations depending upon a real parameter has been investigated by von Neumann, and others. In the present note we shall be concerned particularly with the infinitesimal aspects of such groups."*

— Marshall Harvey Stone, *On One-Parameter Unitary Groups in Hilbert Space* (1932)

---

### Abstract

This file assembles the complete formalization of Stone's theorem, one of the foundational results of quantum mechanics and functional analysis. The theorem establishes a perfect bijective correspondence between strongly continuous one-parameter unitary groups and self-adjoint operators on Hilbert spaces—the mathematical backbone of quantum dynamics.

The formalization spans approximately 10,000 lines of Lean 4 code across five files, culminating in this final assembly. All major results are machine-verified, representing one of the most complete formalizations of unbounded operator theory in any proof assistant.

---

### Table of Contents

1. [Historical Context: 1932](#section-1)
2. [The Mathematical Revolution](#section-2)
3. [Statement of Stone's Theorem](#section-3)
4. [Part I: Group → Generator](#section-4)
5. [The Resolvent Bridge](#section-5)
6. [Part II: Generator → Group](#section-6)
7. [Part III: The Bijection](#section-7)
8. [Significance to Spectral Theory](#section-8)
9. [The Complete Proof Architecture](#section-9)
10. [What This Formalization Achieves](#section-10)
11. [Epilogue: The Legacy](#section-11)

---

<a name="section-1"></a>
### Section 1: Historical Context: 1932

#### The Annus Mirabilis of Quantum Mathematics

The year 1932 stands as a watershed moment in the mathematical foundations of quantum mechanics. Within months of each other, two mathematicians working on opposite sides of the Atlantic published results that would permanently reshape our understanding of the quantum world:

**John von Neumann** (Princeton/Berlin) published *Mathematische Grundlagen der Quantenmechanik*, his monumental treatise establishing Hilbert space as the proper mathematical setting for quantum mechanics. The book introduced the spectral theorem for unbounded self-adjoint operators and laid the rigorous foundations for quantum measurement theory.

**Marshall Harvey Stone** (Harvard/Yale) published *On One-Parameter Unitary Groups in Hilbert Space* and the expanded *Linear Transformations in Hilbert Space*, characterizing exactly which operators generate time evolution in quantum systems.

These were not independent discoveries—von Neumann and Stone were in correspondence, aware of each other's work, and building on a common foundation laid by Hilbert, Hellinger, and others. But they approached the same fundamental question from different angles:

- **Von Neumann asked:** Given an observable (self-adjoint operator), what is its spectral decomposition?
- **Stone asked:** Given a time evolution (unitary group), what generates it?

The answers turned out to be two sides of the same coin.

#### The Princeton-Harvard Axis

In the early 1930s, American mathematics was coming into its own. The Institute for Advanced Study had just been founded in Princeton (1930), and von Neumann was among its first permanent members. Stone, meanwhile, was at Harvard (moving to Yale in 1931), where he had studied under G.D. Birkhoff.

The two men represented different mathematical temperaments:

**Von Neumann** was the polymath—his 1932 book drew on measure theory, ergodic theory, operator algebras, and foundations of mathematics. His approach to the spectral theorem was measure-theoretic, using projection-valued measures to decompose self-adjoint operators.

**Stone** was the analyst—his approach was more direct, using limiting arguments and resolvent techniques. Where von Neumann integrated, Stone differentiated. Where von Neumann decomposed spectrally, Stone approximated via resolvents.

#### The Intellectual Heritage

Both men stood on the shoulders of giants:

**David Hilbert** (1862-1943) had developed the theory of integral equations and introduced what we now call Hilbert spaces. His work on bounded self-adjoint operators, particularly the spectral theorem for compact operators, provided the template.

**Ernst Hellinger** (1883-1950) and **Otto Toeplitz** (1881-1940) had extended Hilbert's work to unbounded operators in the 1910s, recognizing that quantum observables like position and momentum were inherently unbounded.

**Hermann Weyl** (1885-1955) had studied the relationship between Lie groups and quantum mechanics, introducing what we now call the Weyl relations for the canonical commutation relations.

**Erwin Schrödinger** (1887-1961) and **Werner Heisenberg** (1901-1976) had, in 1925-1926, created wave mechanics and matrix mechanics respectively—two seemingly different theories that von Neumann and Stone would prove mathematically equivalent.

#### The Physical Motivation

By 1932, the physical foundations of quantum mechanics were largely in place:

- **Planck** (1900): Energy quantization
- **Einstein** (1905): Photons and the photoelectric effect  
- **Bohr** (1913): Atomic structure and discrete energy levels
- **de Broglie** (1924): Wave-particle duality
- **Heisenberg** (1925): Matrix mechanics and the uncertainty principle
- **Schrödinger** (1926): Wave equation
- **Born** (1926): Probabilistic interpretation
- **Dirac** (1928): Relativistic wave equation

What was missing was *rigorous mathematics*. Physicists manipulated "delta functions," treated unbounded operators cavalierly, and interchanged limits with abandon. The mathematical foundations were shaky at best.

Von Neumann and Stone provided those foundations. After 1932, quantum mechanics had a rigorous mathematical framework that would stand the test of time.

---

<a name="section-2"></a>
### Section 2: The Mathematical Revolution

#### The Problem of Unbounded Operators

The central difficulty in quantum mechanics is that physical observables are represented by *unbounded* operators. The momentum operator $P = -i\hbar\frac{d}{dx}$ and the position operator $Q = x$ are not defined on all of Hilbert space—they have dense domains.

For bounded operators, the theory is clean:
- The exponential $e^{tA} = \sum_{n=0}^{\infty} \frac{(tA)^n}{n!}$ converges in operator norm
- The adjoint $A^*$ exists and is bounded
- The spectrum is contained in a disk of radius $\|A\|$

For unbounded operators, everything is harder:
- The power series doesn't converge
- The adjoint requires careful domain considerations
- The spectrum can be all of $\mathbb{R}$ (or $\mathbb{C}$)
- Even basic operations like $A + B$ require domain compatibility

#### Stone's Insight

Stone's key insight was that while unbounded operators are difficult, the *groups they generate* are well-behaved. If $A$ is self-adjoint (the quantum analogue of "real"), then:

1. $U(t) = e^{itA}$ is unitary for all $t \in \mathbb{R}$
2. $U(s)U(t) = U(s+t)$ (group law)
3. $t \mapsto U(t)\psi$ is continuous for all $\psi \in H$ (strong continuity)

The unitary operators $U(t)$ are bounded (in fact, isometries), so the analytic difficulties of unbounded operators are tamed by passing to their exponentials.

Stone's theorem says this passage is *reversible*: every strongly continuous unitary group arises from a unique self-adjoint operator.

#### The Resolvent Philosophy

The unbounded operator $A$ is difficult to work with directly, but it generates a family of *bounded* operators—the resolvents:

$$R_z = (A - zI)^{-1}, \quad \text{Im}(z) \neq 0$$

For each $z$ off the real axis, $R_z$ is a bounded operator defined on all of $H$. The family $\{R_z\}$ encodes complete information about $A$:

- The spectrum $\sigma(A)$ is where the resolvent fails to exist
- The spectral measure can be recovered from boundary values of $R_z$
- The exponential $e^{itA}$ can be constructed from resolvent approximations

This is the approach taken in this formalization: use the resolvent to bridge unbounded and bounded operator theory.

#### Connection to the Spectral Theorem

Von Neumann's spectral theorem provides an alternative construction:

If $A = \int_{\mathbb{R}} \lambda \, dE(\lambda)$ where $E$ is the spectral measure, then:
$$e^{itA} = \int_{\mathbb{R}} e^{it\lambda} \, dE(\lambda)$$

This is more conceptual but requires developing the full machinery of spectral measures. The resolvent/Yosida approach is more elementary and generalizes to $C_0$-semigroups (the Hille-Yosida theorem).

---

<a name="section-3"></a>
### Section 3: Statement of Stone's Theorem

#### The Theorem

**Stone's Theorem (1932):** Let $H$ be a complex Hilbert space. There is a bijective correspondence between:

**(A)** Strongly continuous one-parameter unitary groups $\{U(t)\}_{t \in \mathbb{R}}$ on $H$

**(B)** Self-adjoint operators $A$ on $H$ (possibly unbounded)

The correspondence is given by $U(t) = e^{itA}$.

#### Unpacking the Statement

**One-parameter unitary group:** A family $\{U(t)\}_{t \in \mathbb{R}}$ of bounded linear operators satisfying:
- $U(t)^* U(t) = U(t) U(t)^* = I$ (unitarity)
- $U(s+t) = U(s)U(t)$ for all $s, t \in \mathbb{R}$ (group law)
- $U(0) = I$ (identity)

**Strongly continuous:** For each $\psi \in H$, the map $t \mapsto U(t)\psi$ is continuous.

**Self-adjoint:** An operator $A$ with dense domain $D(A)$ satisfying:
- $\langle A\psi, \phi \rangle = \langle \psi, A\phi \rangle$ for all $\psi, \phi \in D(A)$ (symmetry)
- $D(A^*) = D(A)$ (domain of adjoint equals domain)

**The Generator:** Given $U(t)$, the generator $A$ is defined by:
$$D(A) = \left\{\psi \in H \,\Big|\, \lim_{t \to 0} \frac{U(t)\psi - \psi}{it} \text{ exists}\right\}$$
$$A\psi = \lim_{t \to 0} \frac{U(t)\psi - \psi}{it}$$

This is the quantum mechanical momentum-from-translation principle: differentiate the group to get the generator.

---

<a name="section-4"></a>
### Section 4: Part I: Group → Generator

This direction is established in **Bochner.lean** using resolvent integral techniques.

#### Existence

**Theorem** `stone_existence`:
```lean
theorem stone_existence (U_grp : OneParameterUnitaryGroup (H := H)) :
    ∃ (gen : Generator U_grp), gen.IsSelfAdjoint
```

*Every strongly continuous one-parameter unitary group has a self-adjoint generator.*

**The Construction:**

1. **Define the domain:**
$$D(A) = \left\{\psi \in H \,\Big|\, \lim_{t \to 0} \frac{U(t)\psi - \psi}{it} \text{ exists in } H\right\}$$

2. **Define the operator:**
$$A\psi = \lim_{t \to 0} \frac{U(t)\psi - \psi}{it}$$

3. **Prove the domain is dense:** The averaged vectors $\psi_h = \frac{1}{h}\int_0^h U(t)\psi \, dt$ lie in $D(A)$ and converge to $\psi$ as $h \to 0$.

4. **Prove symmetry:** Using unitarity $\langle U(t)\psi, \phi \rangle = \langle \psi, U(-t)\phi \rangle$:
$$\langle A\psi, \phi \rangle = \lim_{t \to 0} \frac{\langle U(t)\psi - \psi, \phi \rangle}{it} = \lim_{t \to 0} \frac{\langle \psi, U(-t)\phi - \phi \rangle}{it} = \langle \psi, A\phi \rangle$$

5. **Prove self-adjointness:** Show $\text{Range}(A \pm iI) = H$ using resolvent integrals:
$$\psi_{\pm} = \mp i \int_0^{\infty} e^{-t} U(\pm t)\phi \, dt$$
solves $(A \pm iI)\psi_{\pm} = \phi$.

#### Uniqueness

**Theorem** `stone_uniqueness`:
```lean
theorem stone_uniqueness
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen₁ gen₂ : Generator U_grp)
    (hsa₁ : gen₁.IsSelfAdjoint)
    (hsa₂ : gen₂.IsSelfAdjoint) :
    HEq gen₁.op gen₂.op ∧ gen₁.domain = gen₂.domain
```

*The self-adjoint generator is unique.*

**The Argument:**

Self-adjoint operators are *maximally symmetric*: if $A$ is self-adjoint and $B$ is symmetric with $A \subseteq B$ (meaning $D(A) \subseteq D(B)$ and $B|_{D(A)} = A$), then $A = B$.

If two self-adjoint operators generate the same unitary group, they must agree on their intersection—but maximality forces their domains to be equal.

#### Combined Statement

**Theorem** `stone_part_one`:
```lean
theorem stone_part_one (U_grp : OneParameterUnitaryGroup (H := H)) :
    ∃! (gen : Generator U_grp), gen.IsSelfAdjoint
```

*Every strongly continuous one-parameter unitary group has a **unique** self-adjoint generator.*

---

<a name="section-5"></a>
### Section 5: The Resolvent Bridge

To construct the exponential $e^{itA}$ from a self-adjoint operator $A$, we need the **resolvent**—the bridge between unbounded and bounded operator theory. This material is developed in **Resolvent.lean**.

#### 5.1 The Lower Bound Estimate

The foundation of all resolvent theory is a single inequality.

**Theorem** (`lower_bound_estimate`): For any $z \in \mathbb{C}$ with $\text{Im}(z) \neq 0$ and any $\psi \in D(A)$:

$$\|(A - zI)\psi\| \geq |\text{Im}(z)| \cdot \|\psi\|$$

**Proof:**

Write $z = x + iy$ where $y = \text{Im}(z) \neq 0$. Then:

$$(A - zI)\psi = (A - xI)\psi - iy\psi$$

Expanding the norm squared:

$$\|(A - zI)\psi\|^2 = \|(A-xI)\psi\|^2 + |y|^2\|\psi\|^2 + 2\text{Re}\langle (A-xI)\psi, -iy\psi \rangle$$

The cross term is:

$$2\text{Re}\langle (A-xI)\psi, -iy\psi \rangle = -2y \cdot \text{Im}\langle (A-xI)\psi, \psi \rangle$$

But $(A - xI)$ is symmetric (since $A$ is symmetric and $xI$ is self-adjoint), so $\langle (A-xI)\psi, \psi \rangle \in \mathbb{R}$. Therefore the imaginary part vanishes, and the cross term is zero.

We conclude:

$$\|(A - zI)\psi\|^2 = \|(A-xI)\psi\|^2 + |y|^2\|\psi\|^2 \geq |y|^2\|\psi\|^2$$

Taking square roots gives the result. $\blacksquare$

**Consequences:**

1. **Injectivity:** $(A - zI)$ has trivial kernel for $\text{Im}(z) \neq 0$
2. **No complex eigenvalues:** Self-adjoint operators have only real spectrum
3. **Resolvent bound:** If $R_z$ exists, then $\|R_z\| \leq 1/|\text{Im}(z)|$
4. **Closed range:** Operators bounded below have closed range

#### 5.2 Surjectivity: Range$(A - zI) = H$

**Theorem** (`self_adjoint_range_all_z`): For any $z \in \mathbb{C}$ with $\text{Im}(z) \neq 0$ and any $\phi \in H$:

$$\exists! \psi \in D(A): (A - zI)\psi = \phi$$

**Proof Architecture:**

The proof proceeds in three steps:

**Step 1: Orthogonal complement is trivial.**

Suppose $\chi \perp \text{Range}(A - zI)$, meaning $\langle (A - zI)\psi, \chi \rangle = 0$ for all $\psi \in D(A)$.

This implies $\langle A\psi, \chi \rangle = \bar{z} \langle \psi, \chi \rangle$ for all $\psi \in D(A)$.

Using the self-adjointness criterion (specifically, Range$(A \pm iI) = H$ which we have from Part I), one shows this forces $\chi = 0$ unless $z \in \mathbb{R}$.

Since $\text{Im}(z) \neq 0$, we have $\chi = 0$.

**Step 2: Range is closed.**

Suppose $\{u_n\} \subset \text{Range}(A - zI)$ with $u_n \to \phi$. Write $u_n = (A - zI)\psi_n$.

By the lower bound estimate:

$$\|\psi_m - \psi_n\| \leq \frac{1}{|\text{Im}(z)|} \|u_m - u_n\|$$

So $\{\psi_n\}$ is Cauchy whenever $\{u_n\}$ is Cauchy. By completeness of $H$, $\psi_n \to \psi_\infty$.

The key technical step: show $\psi_\infty \in D(A)$. This uses the resolvent $R_i$ (which exists by self-adjointness):

$$\psi_n = R_i(u_n + (z-i)\psi_n)$$

Taking limits and using continuity of $R_i$:

$$\psi_\infty = R_i(\phi + (z-i)\psi_\infty) \in D(A)$$

since Range$(R_i) = D(A)$.

**Step 3: Dense + Closed = Everything.**

From Steps 1 and 2:
- Range$(A - zI)^\perp = \{0\}$, so Range$(A - zI)$ is dense
- Range$(A - zI)$ is closed

A closed dense subspace of $H$ is all of $H$. $\blacksquare$

#### 5.3 The Resolvent Operator

**Definition** (`resolvent`):
```lean
noncomputable def resolvent (gen : Generator U_grp) (z : ℂ)
    (hz : z.im ≠ 0) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H
```

For each $z$ with $\text{Im}(z) \neq 0$, the resolvent $R_z = (A - zI)^{-1}$ is:
- A bounded linear operator on all of $H$
- With bound $\|R_z\| \leq 1/|\text{Im}(z)|$
- And range $D(A)$

#### 5.4 The Resolvent Identity

**Theorem** (`resolvent_identity`): For any $z, w$ with $\text{Im}(z), \text{Im}(w) \neq 0$:

$$R_z - R_w = (z - w) R_z R_w$$

**Proof:**

Let $\psi_w = R_w \phi$, so $(A - wI)\psi_w = \phi$.

Compute:
$$(A - zI)\psi_w = (A - wI)\psi_w + (w - z)\psi_w = \phi + (w-z)\psi_w$$

Therefore:
$$\psi_w = R_z(\phi + (w-z)\psi_w) = R_z\phi + (w-z)R_z\psi_w = R_z\phi + (w-z)R_z R_w\phi$$

Rearranging: $R_w\phi - R_z\phi = (w-z)R_z R_w\phi$, giving the identity. $\blacksquare$

#### 5.5 The Resolvent Adjoint Identity

**Theorem** (`resolvent_adjoint`): For any $z$ with $\text{Im}(z) \neq 0$:

$$R_z^* = R_{\bar{z}}$$

**Proof:**

We must show $\langle \phi, R_z \psi \rangle = \langle R_{\bar{z}} \phi, \psi \rangle$ for all $\phi, \psi \in H$.

Let $\xi = R_z \psi$ and $\eta = R_{\bar{z}} \phi$. Then:
- $A\xi = \psi + z\xi$ (since $(A - zI)\xi = \psi$)
- $A\eta = \phi + \bar{z}\eta$ (since $(A - \bar{z}I)\eta = \phi$)

By symmetry of $A$:
$$\langle A\eta, \xi \rangle = \langle \eta, A\xi \rangle$$

Expanding the left side:
$$\langle \phi + \bar{z}\eta, \xi \rangle = \langle \phi, \xi \rangle + z\langle \eta, \xi \rangle$$

Expanding the right side:
$$\langle \eta, \psi + z\xi \rangle = \langle \eta, \psi \rangle + z\langle \eta, \xi \rangle$$

The $z\langle \eta, \xi \rangle$ terms cancel, leaving:
$$\langle \phi, \xi \rangle = \langle \eta, \psi \rangle$$

which is $\langle \phi, R_z\psi \rangle = \langle R_{\bar{z}}\phi, \psi \rangle$. $\blacksquare$

#### 5.6 Why the Resolvent Enables Yosida

The Yosida approximation requires bounded self-adjoint approximants to $A$. The resolvent provides exactly this.

**The naive attempt** $A_n = nR_{in}$ fails: while bounded, it is *not* self-adjoint because $(R_{in})^* = R_{-in} \neq R_{in}$.

**The symmetrization** fixes this:

$$A_n^{\text{sym}} = \frac{n^2}{2}(R_{in} + R_{-in})$$

**Theorem:** $A_n^{\text{sym}}$ is self-adjoint.

**Proof:** Using the adjoint identity:
$$(A_n^{\text{sym}})^* = \frac{n^2}{2}(R_{in}^* + R_{-in}^*) = \frac{n^2}{2}(R_{-in} + R_{in}) = A_n^{\text{sym}}$$

$\blacksquare$

This is why the resolvent adjoint identity is essential: it allows construction of bounded self-adjoint approximants to the unbounded self-adjoint operator $A$.

#### 5.7 Summary of Resolvent Results

| Theorem | Statement | Role in Stone's Theorem |
|---------|-----------|------------------------|
| `lower_bound_estimate` | $\|(A - zI)\psi\| \geq |\text{Im}(z)| \cdot \|\psi\|$ | Foundation of everything |
| `self_adjoint_range_all_z` | Range$(A - zI) = H$ for Im$(z) \neq 0$ | Resolvent exists |
| `resolvent_bound` | $\|R_z\| \leq 1/|\text{Im}(z)|$ | Yosida convergence |
| `resolvent_identity` | $R_z - R_w = (z - w) R_z R_w$ | Analytic structure |
| `resolvent_adjoint` | $R_z^* = R_{\bar{z}}$ | Yosida self-adjointness |

---

<a name="section-6"></a>
### Section 6: Part II: Generator → Group

This direction is established in **Yosida.lean** using the Yosida approximation, built on the resolvent theory of Section 5.

#### The Exponential Map

**Theorem** `stone_exponential_eq_group`:
```lean
theorem stone_exponential_eq_group
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ : H) :
    exponential' gen hsa h_dense t ψ = U_grp.U t ψ
```

*The exponential constructed via Yosida approximation equals the original unitary group.*

**The Construction:**

1. **Yosida approximants:** Define bounded self-adjoint operators using the resolvent:
$$A_n^{\text{sym}} = \frac{n^2}{2}(R_{in} + R_{-in})$$

   These are self-adjoint by the resolvent adjoint identity (Section 5.5).

2. **Bounded exponentials:** For each $n$, $e^{it A_n^{\text{sym}}}$ is unitary (since $A_n^{\text{sym}}$ is bounded and self-adjoint, the power series converges and unitarity follows from self-adjointness).

3. **Convergence on the domain:** For $\psi \in D(A)$:
$$A_n^{\text{sym}}\psi \to A\psi \quad \text{as } n \to \infty$$

   This uses the resolvent bound and the identity $R_z(A - zI)\psi = \psi$.

4. **The Duhamel estimate:** For $\psi \in D(A)$:
$$\|U(t)\psi - e^{it A_n^{\text{sym}}}\psi\| \leq |t| \cdot \|A\psi - A_n^{\text{sym}}\psi\| \to 0$$

   This follows from the Duhamel formula (fundamental theorem of calculus for operator-valued functions).

5. **Extension to all of $H$:** The approximations form a Cauchy sequence:
$$\|e^{it A_m^{\text{sym}}}\psi - e^{it A_n^{\text{sym}}}\psi\| \to 0$$

   By density of $D(A)$ and the $\varepsilon/3$ argument, convergence extends to all $\psi \in H$.

6. **Definition:**
$$e^{itA} := \text{s-lim}_{n \to \infty} e^{it A_n^{\text{sym}}}$$

#### Properties of the Exponential

**Theorem** `stone_exponential_is_unitary_group`:
```lean
theorem stone_exponential_is_unitary_group
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H)) :
    (∀ t ψ φ, ⟪exponential' gen hsa h_dense t ψ, exponential' gen hsa h_dense t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ) ∧
    (∀ s t ψ, exponential' gen hsa h_dense (s + t) ψ = exponential' gen hsa h_dense s (exponential' gen hsa h_dense t ψ)) ∧
    (∀ ψ, exponential' gen hsa h_dense 0 ψ = ψ) ∧
    (∀ ψ, Continuous (fun t => exponential' gen hsa h_dense t ψ))
```

*The exponential satisfies all the axioms of a strongly continuous unitary group.*

| Property | Statement | Proof Method |
|----------|-----------|--------------|
| Unitarity | $\langle e^{itA}\psi, e^{itA}\phi \rangle = \langle \psi, \phi \rangle$ | Limit of unitary operators |
| Group law | $e^{i(s+t)A} = e^{isA} e^{itA}$ | Limit of group law |
| Identity | $e^{i \cdot 0 \cdot A} = I$ | Limit of $e^0 = I$ |
| Strong continuity | $t \mapsto e^{itA}\psi$ continuous | Limit of continuous maps |

---

<a name="section-7"></a>
### Section 7: Part III: The Bijection

#### Closing the Loop

**Theorem** `stone_generator_of_exponential`:
```lean
theorem stone_generator_of_exponential
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    Tendsto (fun t : ℝ => ((I * t)⁻¹ : ℂ) • (exponential' gen hsa h_dense t ψ - ψ))
            (𝓝[≠] 0) (𝓝 (gen.op ⟨ψ, hψ⟩))
```

*The generator of $e^{itA}$ is $A$ itself.*

This closes the bijection:
- Start with unitary group $U(t)$
- Extract generator $A$
- Form exponential $e^{itA}$
- Compute generator of $e^{itA}$
- Result: $A$ again

#### The Complete Bijection

**Theorem** `stone_bijection`:
```lean
theorem stone_bijection :
    ∀ (U_grp : OneParameterUnitaryGroup (H := H)),
    ∃! (gen : Generator U_grp), gen.IsSelfAdjoint ∧
      (∀ (hsa : gen.IsSelfAdjoint) (h_dense : Dense (gen.domain : Set H)),
        ∀ t ψ, U_grp.U t ψ = exponential' gen hsa h_dense t ψ)
```

*Stone's theorem: the complete bijective correspondence.*

**The Bijection Diagram:**

```
┌─────────────────────────────────────┐         ┌─────────────────────────────────────┐
│  Strongly Continuous                │         │  Self-Adjoint Operators             │
│  One-Parameter Unitary Groups       │         │  (possibly unbounded)               │
│                                     │         │                                     │
│  {U(t)}_{t∈ℝ} such that:            │         │  A : D(A) → H such that:            │
│  • U(t)* U(t) = I                   │         │  • D(A) dense in H                  │
│  • U(s+t) = U(s)U(t)                │         │  • ⟨Aψ,φ⟩ = ⟨ψ,Aφ⟩                  │
│  • U(0) = I                         │         │  • D(A*) = D(A)                     │
│  • t ↦ U(t)ψ continuous             │         │                                     │
└─────────────────────────────────────┘         └─────────────────────────────────────┘
                    │                                           │
                    │                                           │
                    │    Generator via                          │    Exponential via
                    │    resolvent integrals                    │    Yosida approximation
                    │    (Bochner.lean)                         │    (Yosida.lean)
                    │                                           │
                    ▼                                           ▼
            ┌───────────────┐                           ┌───────────────┐
            │               │                           │               │
            │   A = lim     │                           │  U(t) = lim   │
            │   U(t)ψ - ψ   │                           │  exp(itAₙˢʸᵐ) 
            │   ─────────   │                           │               │
            │      it       │                           │  where        │
            │               │                           │  Aₙˢʸᵐ = n²/2   
            └───────┬───────┘                           │  (Rᵢₙ + R₋ᵢₙ)  
                    │                                   └───────┬───────┘
                    │                                           │
                    │              ┌─────────────┐              │
                    │              │             │              │
                    └──────────────│  RESOLVENT  │──────────────┘
                                   │             │
                                   │  Rz=(A-zI)⁻¹│
                                   │             │
                                   │ (Section 5) │
                                   └──────┬──────┘
                                          │
                                          ▼
                                ┌─────────────────┐
                                │                 │
                                │   BIJECTION     │
                                │                 │
                                │  U(t) = e^{itA} │
                                │                 │
                                └─────────────────┘
```

---

<a name="section-8"></a>
### Section 8: Significance to Spectral Theory

#### The Bridge Between Dynamics and Spectrum

Stone's theorem is the bridge connecting two fundamental mathematical structures:

**Dynamical Structure:** The one-parameter group $U(t)$ describes time evolution—how quantum states change over time.

**Spectral Structure:** The self-adjoint generator $A$ has a spectrum—the possible values of the observable it represents.

The theorem says these are equivalent descriptions: knowing the dynamics $U(t)$ is the same as knowing the observable $A$.

#### Connection to the Spectral Theorem

Von Neumann's spectral theorem says every self-adjoint operator $A$ has a spectral decomposition:
$$A = \int_{\mathbb{R}} \lambda \, dE(\lambda)$$

where $E$ is a projection-valued measure on $\mathbb{R}$.

Stone's theorem then gives:
$$e^{itA} = \int_{\mathbb{R}} e^{it\lambda} \, dE(\lambda)$$

The spectral decomposition of $A$ directly determines the time evolution.

**The Resolvent Connection:**

The spectral measure can be recovered from the resolvent via the Stone formula:
$$E((a,b]) = \text{s-}\lim_{\varepsilon \to 0^+} \frac{1}{2\pi i} \int_a^b [R_{\lambda+i\varepsilon} - R_{\lambda-i\varepsilon}] \, d\lambda$$

The resolvent adjoint identity $R_z^* = R_{\bar{z}}$ ensures:
$$[R_{\lambda+i\varepsilon} - R_{\lambda-i\varepsilon}]^* = R_{\lambda-i\varepsilon} - R_{\lambda+i\varepsilon} = -[R_{\lambda+i\varepsilon} - R_{\lambda-i\varepsilon}]$$

so the integrand is skew-adjoint, making $E$ self-adjoint (in fact, a projection).

**Physical Interpretation:**
- The spectrum $\sigma(A)$ consists of possible measurement outcomes
- The spectral measure $E$ gives probabilities: $\langle \psi, E(\Delta)\psi \rangle$ is the probability of measuring a value in $\Delta$
- Time evolution multiplies each spectral component by $e^{it\lambda}$—a phase rotation at rate $\lambda$

#### The Spectrum-Dynamics Dictionary

| Spectral Property | Dynamical Consequence |
|-------------------|----------------------|
| Eigenvalue $\lambda$ | Stationary state with phase $e^{it\lambda}$ |
| Continuous spectrum | Dispersive evolution (wave spreading) |
| Absolutely continuous spectrum | Decay to zero (scattering) |
| Point spectrum | Periodic or quasi-periodic motion |
| Gap in spectrum | Forbidden energy range |

#### SNAG (Stone-Naimark-Ambrose-Godement) Theorem

Stone's theorem generalizes to locally compact abelian groups. If $G$ is such a group and $U: G \to B(H)$ is a strongly continuous unitary representation, then:
$$U(g) = \int_{\hat{G}} \chi(g) \, dE(\chi)$$

where $\hat{G}$ is the Pontryagin dual (character group) and $E$ is a projection-valued measure on $\hat{G}$.

For $G = \mathbb{R}$, we have $\hat{G} = \mathbb{R}$ and $\chi_\lambda(t) = e^{it\lambda}$, recovering Stone's theorem.

#### Applications in Physics

**Quantum Mechanics:**
- Hamiltonian $H$ generates time evolution: $|\psi(t)\rangle = e^{-iHt/\hbar}|\psi(0)\rangle$
- Momentum generates translations: $T_a = e^{-iPa/\hbar}$
- Angular momentum generates rotations: $R_\theta = e^{-iJ\theta/\hbar}$

**Quantum Field Theory:**
- Energy-momentum generates spacetime translations
- Lorentz generators give boosts and rotations
- Internal symmetries (gauge transformations) have their generators

**Statistical Mechanics:**
- Imaginary time evolution: $e^{-\beta H}$ is the Boltzmann weight
- Kubo-Martin-Schwinger (KMS) condition characterizes equilibrium states

---

<a name="section-9"></a>
### Section 9: The Complete Proof Architecture

#### File Structure

```
Stone's Theorem Formalization
│
├── Generator.lean (~700 lines)
│   ├── OneParameterUnitaryGroup structure
│   ├── Generator structure
│   ├── IsSelfAdjoint predicate
│   └── Uniqueness theorems
│
├── Resolvent.lean (~2500 lines)
│   ├── Lower bound estimate
│   ├── Resolvent existence and bounds
│   ├── Resolvent identity
│   ├── Resolvent adjoint identity
│   ├── Range surjectivity (A - zI)
│   ├── Neumann series machinery
│   └── Analytic structure
│
├── Bochner.lean (~2500 lines)
│   ├── Bochner integration infrastructure
│   ├── Resolvent integral construction
│   ├── Generator limit calculations
│   └── Domain density proofs
│
├── Yosida.lean (~3500 lines)
│   ├── Yosida operators (Aₙˢʸᵐ, Jₙ, etc.)
│   ├── Self-adjointness of approximants
│   ├── Norm bounds and convergence
│   ├── Bounded exponential theory
│   ├── Duhamel formula
│   └── Exponential definition and properties
│
└── Theorem.lean (~300 lines)
    ├── stone_existence
    ├── stone_uniqueness
    ├── stone_part_one
    ├── stone_exponential_eq_group
    ├── stone_exponential_is_unitary_group
    ├── stone_generator_of_exponential
    └── stone_bijection
```

#### Dependency Graph

```
                         Generator.lean
                              │
                              │ (structures, definitions)
                              │
              ┌───────────────┼───────────────┐
              │               │               │
              ▼               ▼               ▼
       Resolvent.lean    Bochner.lean    (shared)
              │               │               
              │  • lower_bound_estimate       
              │  • resolvent construction     
              │  • resolvent_identity         
              │  • resolvent_adjoint          
              │               │               
              └───────┬───────┘
                      │
                      ▼
                 Yosida.lean
                      │
                      │ (uses resolvent to build
                      │  Yosida approximants,
                      │  Duhamel formula,
                      │  exponential construction)
                      │
                      ▼
                 Theorem.lean
                      │
                      │ (assembly,
                      │  bijection theorem)
                      │
                      ▼
               STONE'S THEOREM
```

#### Key Theorems by File

**Generator.lean:**
- `OneParameterUnitaryGroup`: Structure for unitary groups
- `Generator`: Structure for generators with all required properties
- `selfAdjoint_generators_domain_eq`: Self-adjoint generators have equal domains
- `generator_op_eq_on_domain`: Generators agree on common domain

**Resolvent.lean:**
- `lower_bound_estimate`: $\|(A-zI)\psi\| \geq |\text{Im}(z)| \cdot \|\psi\|$
- `resolvent_bound`: $\|R_z\| \leq 1/|\text{Im}(z)|$
- `resolvent_identity`: $R_z - R_w = (z - w)R_z R_w$
- `resolvent_adjoint`: $R_z^* = R_{\bar{z}}$
- `self_adjoint_range_all_z`: Range$(A - zI) = H$ for Im$(z) \neq 0$

**Bochner.lean:**
- `integrable_exp_neg_unitary`: $e^{-t}U(t)\psi$ is integrable
- `generator_limit_resolventIntegralPlus`: The limit calculation for $\psi_+$
- `generatorOfUnitaryGroup_isSelfAdjoint`: The constructed generator is self-adjoint
- `generatorDomain_dense`: $D(A)$ is dense in $H$

**Yosida.lean:**
- `yosidaApproxSym_selfAdjoint`: $A_n^{\text{sym}}$ is self-adjoint
- `yosida_J_tendsto_id`: $J_n \to I$ strongly
- `yosidaApproxSym_tendsto_on_domain`: $A_n^{\text{sym}}\psi \to A\psi$ on domain
- `duhamel_identity`: The Duhamel formula
- `expBounded_yosidaApproxSym_cauchy`: The exponentials form a Cauchy sequence
- `exponential_unitary`: The exponential preserves inner products

**Theorem.lean:**
- `stone_existence`: Existence of self-adjoint generator
- `stone_uniqueness`: Uniqueness of generator
- `stone_bijection`: The complete bijective correspondence

---

<a name="section-10"></a>
### Section 10: What This Formalization Achieves

#### Technical Achievements

1. **Complete proof of Stone's theorem** with both directions:
   - Group → Generator (Bochner resolvent integrals)
   - Generator → Group (Yosida approximation)

2. **Full treatment of unbounded operators:**
   - Domain tracking throughout
   - Self-adjointness via Range$(A \pm iI) = H$ criterion
   - Resolvent theory for spectral analysis

3. **Complete resolvent theory:**
   - Lower bound estimate with proof
   - Surjectivity via orthogonal complement + closed range
   - Resolvent identity and adjoint identity
   - Neumann series for analytic structure

4. **The Duhamel formula** for comparing evolutions:
   - Product rule for operator-valued functions
   - Fundamental theorem of calculus for the integral
   - Isometry simplification via norm constancy on orbits

5. **Machine verification** of delicate analysis:
   - ε/3 arguments for extending convergence
   - Interchange of limits and integrals
   - Uniform bounds enabling density arguments

#### Mathematical Significance

This formalization demonstrates that:

1. **Unbounded operator theory can be formalized:** Despite the domain subtleties, Lean 4's dependent types handle everything correctly.

2. **The proofs are constructive enough:** The Yosida approximation gives an explicit construction of the exponential.

3. **The full bijection is verified:** Not just existence, but the complete correspondence with both directions.

#### Comparison to Other Formalizations

To our knowledge, this is one of the most complete formalizations of Stone's theorem in any proof assistant:

- **Isabelle/HOL:** Has bounded operator theory but limited unbounded theory
- **Coq:** Some spectral theory exists but not full Stone's theorem
- **Lean 3 (mathlib):** Bounded operators well-developed; unbounded theory growing
- **This formalization:** Complete Stone's theorem with unbounded operators

#### Lines of Code

| File | Lines | Content |
|------|-------|---------|
| Generator.lean | ~700 | Structures, uniqueness |
| Resolvent.lean | ~2500 | Resolvent theory |
| Bochner.lean | ~2500 | Resolvent integrals |
| Yosida.lean | ~4500 | Yosida approximation |
| Theorem.lean | ~300 | Final assembly |
| **Total** | **~11000** | Complete Stone's theorem |

---

<a name="section-11"></a>
### Section 11: Epilogue: The Legacy

#### The Impact of Stone's Theorem

Stone's 1932 result has had lasting impact across mathematics and physics:

**Functional Analysis:** Stone's theorem is a cornerstone of the theory of unbounded operators. It established that self-adjointness is the "right" condition for quantum observables—not just symmetry, but the stronger condition ensuring unique dynamics.

**Quantum Mechanics:** The theorem provides the mathematical justification for Schrödinger's equation. The equation $i\hbar \frac{\partial \psi}{\partial t} = H\psi$ is not just a postulate—it's the infinitesimal form of the unique unitary evolution generated by a self-adjoint Hamiltonian.

**Representation Theory:** Stone's theorem is the abelian case of a much larger theory. Non-abelian generalizations lead to the representation theory of Lie groups and the Peter-Weyl theorem.

**C*-algebras:** Stone's theorem generalizes to the GNS construction and the theory of C*-dynamical systems. Von Neumann algebras, which von Neumann introduced in the same period, provide the natural framework.

**Quantum Field Theory:** The Wightman axioms and the Haag-Kastler axioms for algebraic quantum field theory are direct descendants of Stone's theorem, requiring that symmetry groups act via strongly continuous unitary representations.

#### Stone's Later Work

Marshall Stone went on to make fundamental contributions to:

- **Boolean algebras:** Stone duality (1936) relates Boolean algebras to compact Hausdorff spaces
- **General topology:** The Stone-Čech compactification (1937)
- **Approximation theory:** The Stone-Weierstrass theorem (1937, 1948)

His 1932 work on unitary groups remained his most influential contribution to analysis.

#### Von Neumann's Parallel Path

Von Neumann's 1932 book established:

- The spectral theorem for unbounded self-adjoint operators
- The mathematical foundations of quantum measurement
- The density matrix formalism for mixed states
- The quantum logic approach (later developed with Birkhoff)

Together, Stone and von Neumann gave quantum mechanics its rigorous mathematical foundation—a foundation that has stood for nearly a century.

#### A Personal Reflection

In formalizing Stone's theorem, we follow in the footsteps of these giants. The theorem they proved in 1932 is as relevant today as ever:

- Quantum computing relies on unitary evolution
- Quantum error correction uses group-theoretic structure
- Topological quantum matter involves spectral properties
- Quantum simulation implements time evolution

The mathematics of 1932 remains the mathematics of 2025. What has changed is that we can now *verify* these arguments with machine precision, ensuring that no subtle error has crept in over decades of textbook transmission.

This formalization is a tribute to Stone, von Neumann, Yosida, and all who built the mathematical foundations of quantum mechanics. Their work endures.

---

### Final Summary

```
================================================================================
                        STONE'S THEOREM (Complete)
================================================================================

Let H be a complex Hilbert space.

THEOREM: There is a bijective correspondence between:

    { Strongly continuous one-parameter unitary groups U(t) on H }
                                  ↕
    { Self-adjoint operators A on H }

given by U(t) = exp(itA).

--------------------------------------------------------------------------------

PART I (Bochner.lean): GROUP → GENERATOR

  Given U(t), define:
    D(A) = {ψ | lim_{t→0} (U(t)ψ - ψ)/(it) exists}
    Aψ = lim_{t→0} (U(t)ψ - ψ)/(it)

  Then A is self-adjoint and unique.

--------------------------------------------------------------------------------

GLUE (Resolvent.lean): THE RESOLVENT BRIDGE

  For self-adjoint A, the resolvent Rz = (A - zI)⁻¹ exists for all Im(z) ≠ 0.

  Key results:
    • Lower bound: ‖(A - zI)ψ‖ ≥ |Im(z)| · ‖ψ‖
    • Surjectivity: Range(A - zI) = H for Im(z) ≠ 0
    • Bound: ‖Rz‖ ≤ 1/|Im(z)|
    • Resolvent identity: Rz - Rw = (z - w)Rz Rw
    • Adjoint identity: Rz* = R_z̄

  The adjoint identity enables self-adjoint Yosida approximants.

--------------------------------------------------------------------------------

PART II (Yosida.lean): GENERATOR → GROUP

  Given self-adjoint A, define:
    Aₙˢʸᵐ = (n²/2)(R_{in} + R_{-in})  (bounded, self-adjoint by adjoint identity)
    exp(itA) = s-lim_{n→∞} exp(itAₙˢʸᵐ)

  Then exp(itA) is a strongly continuous unitary group.

--------------------------------------------------------------------------------

PART III (Theorem.lean): THE BIJECTION

  • Generator of exp(itA) is A
  • exp(itA) of generator of U(t) is U(t)
  • The correspondence is bijective

--------------------------------------------------------------------------------

FORMALIZATION:
  • ~11,000 lines of Lean 4 code
  • Machine-verified proofs
  • Complete treatment of unbounded operators
  • Full resolvent theory with all identities

================================================================================
```

---

*This is a natural language companion to Stone.lean*

*Author: Adam Bornemann*
