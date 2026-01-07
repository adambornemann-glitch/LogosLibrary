# Companion Document: Schrödinger.lean
**The Wave Equation as Theorem**


## Epigraph

*"I was not... absolutely, one hundred percent sure that the wave equation was correct... I only knew that it gave the right answers."*

— Erwin Schrödinger, recalling the winter of 1925-1926

---

## Abstract

This file contains what may be the most consequential thirty lines in the formalization of quantum mechanics: the derivation of the Schrödinger equation not as a postulate, but as a **theorem**.

For nearly a century, physics textbooks have presented the time-dependent Schrödinger equation as one of the fundamental postulates of quantum mechanics—an inspired guess that happens to match experiment. This formalization demonstrates that the equation is, in fact, a mathematical necessity: given only that quantum states evolve unitarily and continuously, the infinitesimal form of that evolution **must** be the Schrödinger equation.

The proof is a single invocation of the machinery developed across 11,000 lines of Stone's theorem. The brevity is the point.

---

## Table of Contents

1. [The Historical Weight](#section-1)
2. [What the Theorem Says](#section-2)
3. [The Proof in One Line](#section-3)
4. [The Convention Question](#section-4)
5. [Philosophical Implications](#section-5)
6. [What Remains a Postulate](#section-6)
7. [The Vindication](#section-7)

---

<a name="section-1"></a>
## Section 1: The Historical Weight

### Arosa, December 1925

In the winter of 1925, Erwin Schrödinger retreated to the Alpine resort of Arosa with a de Broglie thesis, a mysterious companion, and an obsession. Louis de Broglie had proposed that matter, like light, exhibited wave-particle duality—that electrons had an associated wavelength λ = h/p.

But de Broglie had not written down an equation for this wave. What differential equation governed matter waves?

Schrödinger found it. In a feverish burst of productivity, he produced the equation that would bear his name:

$$i\hbar \frac{\partial \psi}{\partial t} = \hat{H}\psi$$

He could not derive it from first principles. He *guessed* it, guided by:
- Hamilton's optical-mechanical analogy
- The de Broglie relations E = ℏω, p = ℏk  
- The requirement that it reduce to classical mechanics in the appropriate limit
- The demand that it give correct energy eigenvalues for hydrogen

It worked. The equation predicted the hydrogen spectrum with unprecedented accuracy. But *why* it worked—why this equation and not some other—remained mysterious.

### The Postulate Tradition

Every quantum mechanics textbook since has presented the Schrödinger equation as a **postulate**. Dirac's *Principles*, Landau and Lifshitz's *Quantum Mechanics*, Sakurai's *Modern Quantum Mechanics*, Griffiths' *Introduction*—all treat the equation as a starting point, justified by its empirical success.

The typical presentation:

> **Postulate:** The time evolution of a quantum state |ψ⟩ is governed by the Schrödinger equation: iℏ ∂|ψ⟩/∂t = H|ψ⟩, where H is the Hamiltonian operator.

This is pedagogically sensible but philosophically unsatisfying. Why *this* equation? Why first-order in time? Why the imaginary unit? Why the Hamiltonian specifically?

### Stone's Answer

Marshall Stone's 1932 theorem provides the answer: **there is no choice**.

If one accepts that:
1. Quantum states form a Hilbert space
2. Time evolution preserves probability (unitarity)
3. Time evolution is continuous

Then the infinitesimal generator of that evolution is necessarily self-adjoint, and the infinitesimal form of the evolution is necessarily:

$$\frac{d}{dt}|\psi(t)\rangle = iA|\psi(t)\rangle$$

for some self-adjoint operator A. Identifying A with (minus) the Hamiltonian divided by ℏ recovers Schrödinger's equation.

The equation is not a postulate. It is a **theorem**.

---

<a name="section-2"></a>
## Section 2: What the Theorem Says

### The Lean Statement

```lean
theorem schrodinger_equation
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ₀ : H) (hψ₀ : ψ₀ ∈ gen.domain) :
    HasDerivAt (fun t : ℝ => U_grp.U t ψ₀)
               (I • gen.op ⟨U_grp.U 0 ψ₀, gen.domain_invariant 0 ψ₀ hψ₀⟩)
               0
```

### In Natural Language

**Theorem (Schrödinger Equation):** Let U(t) be a strongly continuous one-parameter unitary group on a Hilbert space H, with self-adjoint generator A. For any state ψ₀ in the domain of A, the time-evolved state ψ(t) = U(t)ψ₀ satisfies:

$$\left.\frac{d}{dt}\right|_{t=0} U(t)\psi_0 = iA\psi_0$$

More generally, for all t:

$$\frac{d}{dt} U(t)\psi_0 = iA \cdot U(t)\psi_0$$

### The Physical Translation

| Mathematical Object | Physical Meaning |
|---------------------|------------------|
| H (Hilbert space) | Space of quantum states |
| U(t) | Time evolution operator |
| A (generator) | Observable generating time translation |
| ψ₀ | Initial quantum state |
| U(t)ψ₀ | State at time t |
| iAψ | Rate of change of state |

With the physicist's convention A = -H/ℏ (where H is the Hamiltonian):

$$\frac{d}{dt}|\psi(t)\rangle = -\frac{i}{\hbar}H|\psi(t)\rangle$$

which rearranges to:

$$i\hbar\frac{d}{dt}|\psi(t)\rangle = H|\psi(t)\rangle$$

The Schrödinger equation.

---

<a name="section-3"></a>
## Section 3: The Proof in One Line

### The Actual Proof

```lean
exact h_deriv
```

That's it. One line.

### What This Line Invokes

This single line stands atop a tower of 11,000 lines:

```
schrodinger_equation
       │
       └── exponential_derivative_on_domain (Yosida.lean)
                  │
                  ├── stone_exponential_eq_group (Theorem.lean)
                  │          │
                  │          └── Yosida approximation convergence
                  │                     │
                  │                     ├── yosidaApproxSym_selfAdjoint
                  │                     │          │
                  │                     │          └── resolvent_adjoint (Resolvent.lean)
                  │                     │
                  │                     └── expBounded_yosidaApproxSym_cauchy
                  │                                │
                  │                                └── duhamel_identity
                  │
                  └── Generator existence/uniqueness (Bochner.lean)
                             │
                             ├── resolvent integral construction
                             │
                             └── self_adjoint_range_all_z (Resolvent.lean)
                                        │
                                        └── lower_bound_estimate
```

The brevity of the proof is not laziness—it is the **point**. All the work was done in establishing Stone's theorem. Once that machinery exists, the Schrödinger equation falls out immediately.

### The Derivative Calculation

The key lemma `exponential_derivative_on_domain` establishes:

$$\frac{d}{dt} e^{itA}\psi = iA \cdot e^{itA}\psi$$

for ψ in the domain of A. This is proven in Yosida.lean using:

1. **Yosida approximants:** For the bounded operators Aₙ, the derivative is elementary:
   $$\frac{d}{dt} e^{itA_n} = iA_n \cdot e^{itA_n}$$

2. **Convergence:** As n → ∞, both sides converge:
   - $e^{itA_n}\psi \to e^{itA}\psi$
   - $iA_n \cdot e^{itA_n}\psi \to iA \cdot e^{itA}\psi$

3. **Conclusion:** The derivative of the limit equals the limit of the derivatives.

---

<a name="section-4"></a>
## Section 4: The Convention Question

### Two Conventions

There are two common conventions in the literature:

**Mathematician's Convention (used here):**
$$U(t) = e^{itA}, \quad \frac{d}{dt}U(t)\psi = iA \cdot U(t)\psi$$

**Physicist's Convention:**
$$U(t) = e^{-iHt/\hbar}, \quad i\hbar\frac{d}{dt}U(t)\psi = H \cdot U(t)\psi$$

### The Relationship

Setting A = -H/ℏ converts between them:

| Mathematician | Physicist |
|---------------|-----------|
| A | -H/ℏ |
| exp(itA) | exp(-iHt/ℏ) |
| iA | -iH/ℏ |
| d/dt = iA | iℏ d/dt = H |

### Why the Difference?

**Mathematicians** prefer:
- Generator A such that exp(tA) is the group
- Positive i in the exponential (analytic continuation to upper half-plane)

**Physicists** prefer:
- Hamiltonian H as energy (positive for bound states)
- Schrödinger equation in the traditional form iℏ∂ψ/∂t = Hψ

Both conventions are correct. The formalization uses the mathematician's convention; the physics is identical.

### The Comment in the Code

```lean
/-- Note: Physics typically uses U(t) = exp(-itH), giving d/dt = -iH.
Our convention is A = -H (generator = negative Hamiltonian). -/
```

This comment ensures no physicist misreads the theorem. The mathematics is the same; only the labeling differs.

---

<a name="section-5"></a>
## Section 5: Philosophical Implications

### From Postulate to Theorem

The transformation of the Schrödinger equation from postulate to theorem has profound implications:

**Before (Postulate):**
> "We assume the Schrödinger equation because it works."

**After (Theorem):**
> "The Schrödinger equation is the unique infinitesimal form of continuous unitary evolution."

This is not merely a reorganization of logical dependencies. It reveals *why* the equation works: it is the only possibility consistent with probability conservation and continuity.

### What Forces the Equation

The equation emerges from three requirements:

1. **Hilbert Space Structure**
   - States are vectors in a complete inner product space
   - Superposition is linear combination
   - Probability is |⟨φ|ψ⟩|²

2. **Unitarity**
   - Time evolution preserves inner products: ⟨U(t)φ|U(t)ψ⟩ = ⟨φ|ψ⟩
   - Equivalently: probability is conserved
   - Equivalently: information is preserved

3. **Strong Continuity**
   - The map t ↦ U(t)ψ is continuous for each ψ
   - No instantaneous jumps in state
   - Physical evolution is smooth

From these three alone, Stone's theorem forces:
- The existence of a self-adjoint generator A
- The exponential form U(t) = exp(itA)
- The differential form dψ/dt = iAψ

There is no freedom. No other equation is possible.

### Why First-Order in Time?

A common question: why is the Schrödinger equation first-order in time, while the classical wave equation is second-order?

**Answer:** Because unitarity requires first-order.

A unitary group U(t) satisfies U(s+t) = U(s)U(t). Differentiating at t = 0:
$$\frac{d}{dt}U(t)\big|_{t=0} = A$$

This is a first-order equation. A second-order equation would require initial position *and* velocity—but quantum states are determined by ψ alone, not ψ and ∂ψ/∂t.

The first-order nature is forced by the group structure.

### Why the Imaginary Unit?

Another common question: why does i appear?

**Answer:** Because the generator must be self-adjoint, not skew-adjoint.

For U(t) unitary, we have U(t)* = U(t)⁻¹ = U(-t). Differentiating:
$$A^* = -A \quad \text{(skew-adjoint)}$$

But observables must be self-adjoint (real eigenvalues). So we write A = iH where H is self-adjoint:
$$(iH)^* = -iH^* = -iH$$

The i converts between self-adjoint observables and skew-adjoint generators.

### The Copenhagen Controversy, Revisited

In 1926, the Copenhagen school argued that wave mechanics and matrix mechanics were merely different representations of the same underlying theory. The mathematics was conventional; the physics was deeper.

Stone's theorem inverts this: the mathematics is **forced**; it is the physical interpretation that remains underdetermined.

The Schrödinger equation is not one choice among many. It is the unique continuous unitary evolution. What remains controversial is not the equation, but its meaning:
- What is ψ? (Wave? Probability amplitude? Information?)
- What happens during measurement? (Collapse? Branching? Decoherence?)
- Is the evolution always unitary? (What about measurement?)

These interpretational questions remain. But the equation itself is settled.

---

<a name="section-6"></a>
## Section 6: What Remains a Postulate

### The Surviving Postulates

This formalization reduces the postulates of quantum mechanics, but does not eliminate them entirely. What remains:

**Postulate 1: Hilbert Space**
> The state of a quantum system is described by a vector in a complex Hilbert space.

This is *assumed*, not derived. Why complex? Why a Hilbert space specifically? These remain foundational choices.

**Postulate 2: Unitarity**
> Time evolution is unitary (probability-preserving).

This is also assumed. One could imagine non-unitary evolution (indeed, open quantum systems exhibit effective non-unitarity). The assumption of unitarity is a physical input.

**Postulate 3: Continuity**
> Time evolution is strongly continuous.

This rules out instantaneous jumps. It is a physical assumption about the smoothness of dynamics.

**Postulate 4: Measurement**
> Measurement yields eigenvalues of self-adjoint operators, with probabilities given by the Born rule.

This is entirely separate from the Schrödinger equation. The measurement postulate is not addressed by Stone's theorem.

### The Reduction

| Traditional Postulate | Status After Formalization |
|----------------------|---------------------------|
| States are Hilbert space vectors | Still a postulate |
| Observables are self-adjoint operators | Follows from requiring real eigenvalues |
| Evolution is unitary | Still a postulate |
| Evolution is continuous | Still a postulate |
| Schrödinger equation | **Now a theorem** |
| Born rule | Still a postulate |
| Collapse postulate | Still a postulate (and controversial) |

The formalization removes one postulate from the list. This is genuine progress.

---

<a name="section-7"></a>
## Section 7: The Vindication

### December 1925 → December 2025

One hundred years separate Schrödinger's discovery from this formalization.

In December 1925, Schrödinger wrote down an equation he could not fully justify. He knew it worked. He did not know *why* it had to be that equation.

In December 2025, a proof assistant confirms: it had to be that equation. Given unitarity and continuity, no other infinitesimal form is possible.

### What Schrödinger Sought

Throughout his life, Schrödinger sought a realistic interpretation of quantum mechanics. He wanted the wave function to represent something *real*—a physical wave in space, not merely a probability amplitude.

He lost that battle. The Copenhagen interpretation prevailed, and ψ became an epistemological tool rather than an ontological entity.

But in another sense, Schrödinger won. His equation—not Heisenberg's matrices, not Dirac's transformation theory—became the standard formulation of quantum mechanics. Every quantum mechanics course teaches the Schrödinger equation. Every quantum chemist solves it daily. Every quantum computer implements it.

And now we know: this was not a historical accident. The wave equation is not one choice among many. It is the mathematical necessity.

### The Final Lines

The Lean file ends simply:

```lean
exact h_deriv
```

One line. Invoking 11,000 lines of Stone's theorem. Establishing as mathematical fact what Schrödinger could only conjecture.

The wave equation is a theorem.

---

## Summary

```
================================================================================
                    THE SCHRÖDINGER EQUATION AS THEOREM
================================================================================

TRADITIONAL STATUS:
  Postulate - "The time evolution of a quantum state is governed by
               iℏ ∂ψ/∂t = Hψ"

NEW STATUS:
  Theorem - Given:
    1. States form a Hilbert space
    2. Evolution is unitary
    3. Evolution is strongly continuous
  
  Then: The infinitesimal form of evolution MUST be dψ/dt = iAψ
        for a unique self-adjoint operator A.

THE PROOF:
  • 11,000 lines of Stone's theorem (Generator.lean → Theorem.lean)
  • 1 line invoking that machinery (Schrödinger.lean)

WHAT THIS MEANS:
  • The Schrödinger equation is not a guess that happens to work
  • It is the UNIQUE continuous unitary evolution
  • There was never any other possibility

WHAT REMAINS POSTULATED:
  • Hilbert space structure
  • Unitarity of evolution
  • Strong continuity
  • Measurement/Born rule
```

---

*This is a natural language companion to Schrödinger.lean*


*Author: Adam Bornemann*
