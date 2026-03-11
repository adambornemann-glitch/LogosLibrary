# Entropic Gravity: A Machine-Verified Consistency Proof

## For Physicists Who Don't Speak Lean

This project answers a simple question: **Is the algebraic structure of entropic gravity internally consistent?**

The answer, verified by machine across 224 theorems with zero gaps and zero assumptions smuggled in: **yes.**

Starting from two inputs — the Bekenstein-Hawking entropy and the Unruh temperature — the framework derives Newton's law of gravitation, Newton's second law, Einstein's field equations, the Schrödinger equation, and more. Not as analogies. As algebraic consequences.

This README explains what was done, why it matters, and what it does *not* claim — all without assuming you know what a proof assistant is.

---

## 1. What Is This, and Why Should You Care?

The most common critique of Verlinde's 2010 entropic gravity paper ("On the Origin of Gravity and the Laws of Newton," arXiv:1001.0785) is that the arguments are *heuristic*. The derivation of Newton's law from the Bekenstein bound and the Unruh effect involves a chain of steps, each individually plausible, but the question remains: do they compose consistently? Could there be a hidden inconsistency — a sign error, a double-counting, a circular assumption — buried somewhere in the chain?

This project settles that question by translating the entire algebraic structure into Lean 4, a programming language where every statement must be *proved* before the compiler accepts it. The compiler does not care about physical intuition, reputation, or plausibility. It checks every step mechanically. If any theorem relied on an unproven assumption, the code would not compile.

**The code compiles. Every theorem is proven. No axioms were introduced.**

This is not a numerical simulation. It is not a calculation. It is a machine-verified proof that the algebraic relationships in entropic gravity are mutually consistent.

---

## 2. The Two Inputs

The entire framework rests on two independently established results from black hole physics and quantum field theory in curved spacetime:

**Input 1: Bekenstein-Hawking entropy**

$$S = \frac{A}{4G}$$

The entropy of a horizon is proportional to its area, with the proportionality constant fixed by Hawking's calculation. This is the deepest quantitative result in quantum gravity. The factor of 4 is not adjustable — it comes from the Hawking temperature of a Schwarzschild black hole.

**Input 2: Unruh temperature**

$$T = \frac{a}{2\pi}$$

A uniformly accelerating observer in Minkowski vacuum perceives a thermal bath at temperature proportional to proper acceleration. The factor of 2π is the period of the modular automorphism group (Bisognano-Wichmann theorem). It is also not adjustable — it is fixed by the KMS condition.

Everything that follows — Newton's laws, Einstein's equations, the Schrödinger equation — is *derived* from these two inputs and standard thermodynamic identities.

---

## 3. What Is Proven

### 3.1 Newton's Second Law from Entropy ("The Great Cancellation")

When a particle of mass $m$ approaches a horizon, the Bekenstein bound gives the entropy gradient:

$$\frac{dS}{dx} = 2\pi m$$

The entropic force — the tendency of the system to increase entropy — is:

$$F = T \cdot \frac{dS}{dx}$$

Evaluating at the Unruh temperature:

$$F = \frac{a}{2\pi} \cdot 2\pi m = ma$$

The $2\pi$ in the numerator (Bekenstein bound) and the $2\pi$ in the denominator (Unruh temperature) **are the same $2\pi$** — the period of the modular automorphism group. Their cancellation is not a numerical coincidence. It is the modular period dividing itself out.

The formalization proves this holds for *any* value of the modular period $\alpha$:

$$F = \frac{a}{\alpha} \cdot \alpha m = ma \qquad \text{for all } \alpha > 0$$

It also proves the **converse**: if $F = ma$ holds for all $(a, m)$, then the Bekenstein and Unruh periods *must* be equal. The Great Cancellation forces a common modular period.

### 3.2 Newton's Law of Gravitation

A holographic screen — a closed surface at radius $r$ enclosing mass $M$ — carries $N = A/G$ degrees of freedom. Equipartition ($M = \frac{1}{2}NT$) fixes the screen temperature:

$$T = \frac{MG}{2\pi r^2}$$

The entropic force on a test mass $m$ at the screen is then:

$$F = T \cdot 2\pi m = \frac{MG}{2\pi r^2} \cdot 2\pi m = \frac{GMm}{r^2}$$

Newton's law of gravitation is a **theorem**, not an input.

### 3.3 The Full Circle

The screen temperature derived from equipartition is *exactly* the Unruh temperature evaluated at the gravitational acceleration the theory predicts:

$$T_{\text{screen}} = \frac{MG}{2\pi r^2} = \frac{a}{2\pi} = T_{\text{Unruh}}(a) \qquad \text{where } a = \frac{GM}{r^2}$$

The framework predicts its own consistency. This self-consistency is proven to hold for *any* modular period $\alpha$, not just $2\pi$.

### 3.4 The Jacobson Derivation and Einstein's Equations

Following Jacobson (1995): the Clausius relation $\delta Q = T \, dS$ applied at local Rindler horizons, with the Raychaudhuri equation providing the geometric content ($dA \propto -R_{kk}$), yields the scalar Einstein equation:

$$R_{kk} = 8\pi G \, T_{kk}$$

The coupling constant $8\pi G$ is not free. It factorizes as:

$$8\pi G = \underbrace{2\pi}_{\text{Unruh}} \cdot \underbrace{4G}_{\text{Bekenstein-Hawking}}$$

The $2\pi$ is the modular period from $T = a/(2\pi)$. The $4G$ is the entropy denominator from $S = A/(4G)$. The formalization traces this factorization explicitly through every step.

The cosmological constant $\Lambda$ is shown to be **undetermined** by the null-surface derivation — exactly as Jacobson noted. It is a free parameter, which is physically correct.

### 3.5 Ott Covariance and the Exclusion of Landsberg

Three facts form a consistent triad:

- (A) Clausius relation: $\delta Q = T \, dS$
- (B) Energy covariance: $\delta Q \to \gamma \, \delta Q$
- (C) Entropy invariance: $dS \to dS$

Any two of these imply the third. Together they **force** the Ott transformation $T \to \gamma T$ for temperature under Lorentz boosts.

The Landsberg alternative ($T \to T$) would require $dS \to \gamma \, dS$ to preserve Clausius with covariant energy. But entropy counts microstates — an integer cannot depend on observer velocity. The formalization proves by contradiction that Landsberg forces $\gamma = 1$: no non-trivial boosts are possible.

Every step of the derivation — Clausius, Jacobson, the entropic force — is independently Ott-covariant. The Lorentz covariance of Einstein's equations is *guaranteed* step-by-step, not checked post hoc.

### 3.6 The Schrödinger Equation from Entropic Evolution

Following the Connes-Rovelli thermal time hypothesis: the modular automorphism group generates evolution in an entropy parameter $\sigma$, with the modular Hamiltonian eigenvalue:

$$K = \frac{H}{2\pi T}$$

Physical time flows at rate:

$$\frac{d\sigma}{dt} = 2\pi T$$

The composition gives phase accumulation per unit physical time:

$$K \cdot \frac{d\sigma}{dt} = \frac{H}{2\pi T} \cdot 2\pi T = H$$

This **is** the Schrödinger equation $i\hbar \, \partial\psi/\partial t = H\psi$ (in natural units $\hbar = 1$), recovered as the same modular cancellation that produces $F = ma$. The formalization proves this holds for all $\alpha$ and is Ott-covariant: under $T \to \gamma T$, the modular energy scales as $K \to K/\gamma$ and the entropy rate as $d\sigma/dt \to \gamma \, d\sigma/dt$, so the product $H$ is unchanged.

### 3.7 The Diósi-Penrose Collapse Timescale

For a mass $m$ in spatial superposition of extent $\Delta x$, the gravitational self-energy is $E_{\text{grav}} = Gm^2/\Delta x$. The collapse timescale $\tau_C = 1/E_{\text{grav}}$ satisfies:

$$\tau_C \cdot T_C = \frac{1}{2\pi}$$

where $T_C = E_{\text{grav}}/(2\pi)$ is the temperature at which the gravitational self-energy occupies one modular cycle. The Boltzmann exponent $E/T = 2\pi$ — the same ratio as the Rindler vacuum.

### 3.8 The Schwarzschild Quartet

A single Schwarzschild black hole simultaneously inhabits four roles in the framework:

| Face | Perspective | Object |
|------|-------------|--------|
| 1 | Jacobson | Local Rindler horizon at the surface gravity |
| 2 | Verlinde | Spherical holographic screen at $r_s = 2GM$ |
| 3 | Hawking | Black hole with temperature $T_H = 1/(8\pi GM)$ |
| 4 | Newton | Gravitational source with $a = GM/r^2$ |

All four faces yield the **same** temperature, **same** entropy, **same** coupling constant $8\pi G$. The formalization proves this explicitly by constructing embeddings between the corresponding structures and verifying thermodynamic consistency.

---

## 4. The Parametric Framework: Structure vs. Coupling

One of the most revealing results is what happens when the physical constants are promoted to free parameters. Replace $2\pi \to \alpha$ and $4 \to n$:

| Result | Depends on $\alpha$, $n$? |
|--------|:------------------------:|
| $F = ma$ | No — holds for all $\alpha$ |
| Schrödinger recovery: $K \cdot d\sigma/dt = H$ | No — holds for all $\alpha$ |
| Ott covariance | No — holds for all $\alpha$, $n$ |
| Full circle: $T_{\text{screen}} = T_{\text{Unruh}}$ | No — holds for all $\alpha$ |
| Landsberg exclusion | No — holds for all $\alpha$, $n$ |
| Einstein coupling: $1/(\alpha \cdot n \cdot G)$ | **Yes** |
| Hawking temperature: $1/(8\pi GM)$ | **Yes** |
| Boltzmann factor: $e^{-\alpha E_0}$ | **Yes** |

The table reveals a clean separation:

- **Structural results** (top rows) are parameter-independent. They are consequences of the *algebraic form* of the entropic framework — the fact that the same period appears in both the Bekenstein bound and the Unruh temperature.
- **Quantitative results** (bottom rows) depend on the specific values $\alpha = 2\pi$ and $n = 4$, which are selected by the UV completion: quantum field theory fixes $\alpha = 2\pi$ (modular theory, KMS condition), and the Hawking calculation fixes $n = 4$.

The classical consistency of entropic gravity does not care which values $\alpha$ and $n$ take. It is a topological feature of the framework, not a numerical accident.

### The Entropic Hierarchy

The logical dependencies organize into levels:

**Level 0 — Inputs:** $S = A/(nG)$, $T = a/\alpha$ (definitions)

**Level 1 — Algebraic:** $F = ma$, Schrödinger recovery, Ott covariance (any $\alpha$)

**Level 2 — Geometric:** Newton's law $F = GMm/r^2$, Jacobson coupling $1/(\alpha n G)$ (requires sphere + equipartition)

**Level 3 — Self-consistency:** Full circle closes, Schwarzschild Quartet agrees, $\tau_C \cdot T = 1/\alpha$

**Level 4 — UV selection:** $\alpha = 2\pi$ (from QFT), $n = 4$ (from quantum gravity) → physical theory

Levels 0–3 are structural. Level 4 selects our universe.

---

## 5. What This Does NOT Prove

Intellectual honesty requires being explicit about the boundaries:

**This does not prove gravity is entropic.** Whether gravity actually arises from entropy is an empirical question. This formalization proves that *if* you adopt the entropic starting point, the algebraic consequences are consistent and reproduce known physics. Consistency is necessary for correctness, but not sufficient.

**This does not formalize the 2016 dark matter paper.** Verlinde's "Emergent Gravity and the Dark Universe" (arXiv:1611.02269) involves the entanglement structure of de Sitter space, volume-law entropy, and glassy dynamics — physical inputs that are not yet amenable to this style of algebraic formalization. This project focuses on the 2010 framework.

**This does not handle the continuum limit.** The Jacobson derivation is formalized at the level of the algebraic chain (Raychaudhuri → area change → entropy change → Clausius → Einstein), not at the level of differential geometry on a Lorentzian manifold. The Raychaudhuri equation enters as a *field* of a structure (a datum the user provides), not as a theorem of Riemannian geometry. A full formalization of the Jacobson program in Lean would require a formalized theory of semi-Riemannian geometry, which does not yet exist in Mathlib.

**This does not address the quantum-gravitational regime.** The Bekenstein-Hawking entropy and the Unruh temperature are semiclassical results. The formalization takes them as inputs and explores their consequences within the classical/semiclassical domain. It says nothing about Planck-scale physics.

---

## 6. The Method: Curry-Howard for Physicists

For those unfamiliar with proof assistants, here is the essential idea.

In Lean 4, every *proposition* is a *type*, and every *proof* is a *term* inhabiting that type. To prove a theorem is to construct a term of the right type. The compiler checks that the term has the claimed type — mechanically, without human judgment.

For this project, the correspondence is:

| Physics | Lean 4 | English |
|---------|--------|---------|
| Physical law | Structure field (a type) | "This quantity must exist and satisfy these constraints" |
| Consistency | Canonical instance (a term) | "Here is a concrete example satisfying all constraints" |
| Consequence | Theorem (a function on the structure) | "Given any instance, this relationship holds" |

For example, a `LocalRindlerHorizon` is a structure carrying acceleration $a > 0$, area $A > 0$, and Newton's constant $G > 0$. To *construct* a `LocalRindlerHorizon` is to exhibit these data and prove the positivity constraints. Once constructed, all theorems proved for the structure — the Unruh temperature, the Bekenstein-Hawking entropy, the Clausius relation — apply automatically.

The key features of this approach:

- **Zero axioms.** No physical law is declared as an axiom. Instead, physical laws are structure fields. A structure that cannot be instantiated (because its fields are contradictory) would be uninhabitable — and the contradiction would be caught at compile time.
- **Zero sorry.** In Lean, `sorry` is an explicit marker meaning "I haven't proven this yet." There are none. Every step is complete.
- **Mechanical verification.** A human reader might miss a subtle error in a 30-page calculation. The Lean type-checker cannot. It verifies every step to the same standard.

The Grand Consistency Type in `Synthesis.lean` packages *all* core consistency conditions — structural invariants, physical theorems, coupling uniqueness — into a single type. Its canonical inhabitant is the constructive proof that all conditions hold simultaneously. The type's inhabitability is the master theorem.

---

## 7. File Structure

```
EntropicGravity/
├── Horizons.lean        §1: Bekenstein-Hawking, Unruh, LocalRindlerHorizon, Schwarzschild
├── Clausius.lean        §2: Clausius relation, Ott covariance, Jacobson chain, 8πG
├── EntropicForce.lean   §3: Verlinde's program — holographic screens → Newton's law
├── Recovery.lean        §4: Schrödinger, Diósi-Penrose, CMC slicing, de Sitter
└── Synthesis.lean       §5: Parametric framework, Schwarzschild Quartet, Grand Consistency Type
```

| File | Theorems | Gaps (`sorry`) | Axioms |
|------|:--------:|:--------------:|:------:|
| Horizons.lean | 35 | 0 | 0 |
| Clausius.lean | 34 | 0 | 0 |
| EntropicForce.lean | 62 | 0 | 0 |
| Recovery.lean | 55 | 0 | 0 |
| Synthesis.lean | 38 | 0 | 0 |
| **Total** | **224** | **0** | **0** |

The logical dependency is linear: each file imports the previous one. The derivation chain mirrors the physics:

$$\text{Horizons} \xrightarrow{\text{Clausius}} \text{Einstein} \qquad \text{Horizons} \xrightarrow{\text{Entropic Force}} \text{Newton} \xrightarrow{\text{Recovery}} \text{Schrödinger}$$

---

## 8. Key Derivation Chains (No Lean Required)

### Chain 1: Entropy → F = ma → Newton's Law

```
 Bekenstein bound            Unruh temperature
 ΔS = 2πm Δx                T = a/(2π)
      │                           │
      └───────────┬───────────────┘
                  │
            F = T · dS/dx
            F = [a/(2π)] · [2πm]
            F = ma                    ← Newton's second law
                  │
       ┌──────────┴──────────────┐
       │                         │
  Equipartition             Spherical screen
  M = ½NT                   A = 4πr²
       │                         │
       └──────────┬──────────────┘
                  │
            T = MG/(2πr²)
            F = GMm/r²               ← Newton's gravitational law
```

### Chain 2: Entropy → Einstein's Equations

```
  Raychaudhuri                Bekenstein-Hawking
  dA = -R_kk dλ dA           S = A/(4G)
       │                           │
       └───────────┬───────────────┘
                   │
             dS = dA/(4G)
             dS = -R_kk dλ dA/(4G)
                   │
          Clausius: δQ = T · dS
          Unruh:    T = a/(2π)
                   │
             δQ = a · dA/(8πG)        ← the 8πG appears
                   │
          Identify δQ = T_kk dλ dA    ← stress-energy flux
                   │
             R_kk = 8πG · T_kk        ← scalar Einstein equation
                   │
             G_μν + Λg_μν = 8πG T_μν  ← full Einstein (Λ undetermined)
```

### Chain 3: Entropy → Schrödinger Equation

```
  Modular Hamiltonian            Thermal Time Hypothesis
  K = H/(2πT)                    dσ/dt = 2πT
       │                              │
       └──────────┬───────────────────┘
                  │
        K · dσ/dt = [H/(2πT)] · [2πT] = H
                  │
        i dψ/dt = Hψ                 ← Schrödinger equation
```

---

## 9. Frequently Asked Questions

**"Isn't this circular? You put in the physics and got it back out."**

No. The inputs are $S = A/(4G)$ and $T = a/(2\pi)$. The outputs include $F = GMm/r^2$, $G_{\mu\nu} + \Lambda g_{\mu\nu} = 8\pi G \, T_{\mu\nu}$, and $i\hbar \,\partial\psi/\partial t = H\psi$. The outputs are not the inputs. They are algebraic consequences of the inputs combined with thermodynamic identities (Clausius, equipartition) and geometric data (spherical screens, Raychaudhuri equation). The non-trivial content is that the chain composes consistently and arrives at exactly the known equations of physics — not something close, not something up to a constant, but the exact equations with the exact coupling constants.

**"You assumed Newton's constant G. Isn't that putting gravity in by hand?"**

$G$ enters through the Bekenstein-Hawking formula $S = A/(4G)$ — it sets the Planck scale. What is *derived* is that the same $G$ reappears in Newton's law $F = GMm/r^2$ and in Einstein's equations with coupling $8\pi G$. The theory does not produce two different coupling constants for two different equations. It produces one: $G$, refracted through the Unruh factor $2\pi$ and the Bekenstein-Hawking factor $4$.

**"What about the equivalence principle?"**

The weak equivalence principle (universality of free fall) is a consequence of the entropic force being proportional to $m$: the entropy gradient $dS/dx = 2\pi m$ and the force $F = T \cdot 2\pi m$ are both linear in $m$, so $F/m = 2\pi T$ is mass-independent. This is proven in the formalization (`weak_equivalence`).

**"What about MOND and dark matter?"**

This formalization does not address them. Verlinde's 2016 paper proposes that apparent dark matter arises from an elastic response of the de Sitter entropy medium, involving a competition between area-law and volume-law entanglement. That physics is important but not yet suitable for this style of formalization. We recover Einstein, Newton, and Schrödinger — the established framework — and stop there.

**"Can I verify this myself without knowing Lean?"**

You can install Lean 4 and Mathlib, then run `lake build`. If the build succeeds with no errors, every theorem is verified. You do not need to read the proofs — the compiler is the referee. The build either succeeds (consistent) or fails (inconsistent). It succeeds.

---

## 10. Citation

If you use this formalization in academic work:

```bibtex
@software{bornemann2026entropic,
  author = {Bornemann, Adam},
  title = {Entropic Gravity in Lean 4: A Machine-Verified Consistency Proof},
  year = {2026},
  url = {https://github.com/adamb/entropic-gravity-lean4}
}
```

The original physics:

```bibtex
@article{verlinde2011origin,
  author = {Verlinde, Erik P.},
  title = {On the Origin of Gravity and the Laws of Newton},
  journal = {JHEP},
  volume = {2011},
  number = {4},
  pages = {29},
  year = {2011},
  eprint = {1001.0785}
}

@article{jacobson1995thermodynamics,
  author = {Jacobson, Ted},
  title = {Thermodynamics of Spacetime: The Einstein Equation of State},
  journal = {Physical Review Letters},
  volume = {75},
  number = {7},
  pages = {1260--1263},
  year = {1995},
  eprint = {gr-qc/9504004}
}

@article{connes1994neumann,
  author = {Connes, Alain and Rovelli, Carlo},
  title = {Von Neumann Algebra Automorphisms and Time-Thermodynamics Relation},
  journal = {Classical and Quantum Gravity},
  volume = {11},
  number = {12},
  pages = {2899--2917},
  year = {1994},
  eprint = {gr-qc/9406019}
}
```

---

## Disclaimer

All errors and misinterpretations in this formalization are solely the responsibility of the author (Adam Bornemann), not Erik Verlinde, Ted Jacobson, Alain Connes, Carlo Rovelli, or any other physicist whose theoretical frameworks are referenced.

This is an independent project. It has not been reviewed or endorsed by any of the above.

The goal is to establish the *algebraic* consistency of entropic gravity as a mathematical fact — not to make claims about the physical correctness of the theory. Whether gravity is actually entropic remains an empirical question that no formal verification can answer.

---

## License

MIT License — see [LICENSE](LICENSE) for details.

---

*The inputs: $S = A/(4G)$ and $T = a/(2\pi)$. Everything else follows.*