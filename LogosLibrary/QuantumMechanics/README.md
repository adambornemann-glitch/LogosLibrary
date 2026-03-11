# Quantum Mechanics

**Status: Spectral Theory is still under construction. Modular Theory is
proved through the cocycle identity; KMS discharge is next.**

This directory is a formally verified development of non-relativistic and
relativistic quantum mechanics in Lean 4, built on Mathlib. It begins with
the operator theory that quantum mechanics actually requires — unbounded
symmetric operators on infinite-dimensional Hilbert spaces with explicit
domains — and carries this machinery through to Stone's theorem, the spectral
theorem, the Dirac equation, the complete uncertainty relation hierarchy,
a formally verified bijection between unitarity and the first law of
thermodynamics, and the Tomita–Takesaki modular theory with its consequences
for relativistic temperature transformations.

The first ~12,000 lines contain zero axioms beyond Lean's kernel and Mathlib.

## What is here

| Section | Lines | Axioms | What it proves |
|---------|------:|-------:|----------------|
| [**Uncertainty/**](Uncertainty/) | ~1,200 | 0 | Robertson, Schrödinger, Heisenberg (twice: Cauchy–Schwarz and Cramér–Rao) |
| [**UnitaryEvo/**](UnitaryEvo/) | 7,754 | 0 | Stone's theorem, Schrödinger equation as corollary |
| [**BellsTheorem/**](BellsTheorem/) | 2,982 | 0 | CHSH inequality, Tsirelson's bound (tight), quantum violation |
| [**SpectralTheory/**](SpectralTheory/) | 10,139 | 66 | Spectral theorem (three routes), Borel functional calculus, Dirac equation, unitarity ↔ first law |
| [**ModularTheory/**](ModularTheory/) | ~3,830 | 3 + hypotheses | Tomita–Takesaki, Connes cocycle, KMS condition, thermal time, Ott forced |
| **Total** | **~26,000** | **69 + hypotheses** | |

Each section has its own detailed README. This document describes the
architecture connecting them.

## The logical structure

The development follows a single thread: what does it take to do quantum
mechanics honestly?

**Layer 1: Operator foundations (axiom-free).** Quantum observables are
unbounded symmetric operators with dense domains. The type
`UnboundedObservable H` enforces this at the type level — you cannot apply
an operator to a vector without proving it lives in the domain. This is not
pedantry. It is the difference between formalizing quantum mechanics and
formalizing a caricature of it. Every physics textbook silently assumes
domain questions away; this library does not.

**Layer 2: Time evolution (axiom-free).** Stone's theorem establishes the
bijection between strongly continuous one-parameter unitary groups and
self-adjoint operators. The proof proceeds in both directions: forward via
Bochner integrals and deficiency indices, reverse via Yosida approximation
and Duhamel's formula. The Schrödinger equation falls out as a one-page
corollary — it is not an axiom but a theorem, equivalent to two physical
requirements: probability conservation (unitarity) and continuous dynamics
(strong continuity).

**Layer 3: Spectral theory (66 axioms).** The spectral theorem for
unbounded self-adjoint operators, constructed via three independent routes
(Bochner, resolvent/Stieltjes inversion, Cayley transform) that are proved
to agree. The Borel functional calculus f(A) = ∫f dE follows. The axioms
here are overwhelmingly "soft" — Bochner's theorem, dominated convergence
applications, Fubini — asserting well-known results from measure theory and
harmonic analysis that require substantial infrastructure not yet in Mathlib.
The single "hard" axiom is the existence of compatible spectral measures in
the Cayley construction.

**Layer 4: Bell's theorem (axiom-free).** The CHSH inequality, Tsirelson's
bound, and quantum violation, ported from Echenim & Mhalla's Isabelle/HOL
formalization with proper attribution, then substantially extended. The
classical bound |S| ≤ 2 is proved via measure-theoretic local hidden
variable models. Tsirelson's bound |S| ≤ 2√2 is proved tight: the upper
bound follows from the operator identity S² = 4I − [A₀,A₁]·[B₀,B₁] and
commutator norm estimates; the lower bound is achieved by explicit
computation on the Bell state with Pauli observables. This section works
with finite-dimensional matrices throughout — CHSH is inherently
finite-dimensional and does not require the unbounded operator machinery.

**Layer 5: Modular theory and thermal time (3 axioms + hypotheses).**
Tomita–Takesaki modular theory for von Neumann algebras with cyclic and
separating vectors: the Tomita operator S₀, modular operator Δ, modular
conjugation J, and the modular automorphism group σ\_t. The Connes cocycle
theorem, proving that modular flows of different faithful normal states
differ only by inner automorphisms, yielding the canonical flow
δ : ℝ → Out(M) intrinsic to the algebra. The KMS condition, its convexity,
and the Liouville argument for time-invariance. The thermal time hypothesis
of Connes–Rovelli, with the consequence that the Ott temperature
transformation T → γT is the unique law compatible with both special
relativity and the modular structure — Landsberg's T → T is proved
inconsistent with the cocycle theorem. The 3 true axioms are
`ClosabilityFromDenseAdjoint` (Reed–Simon VIII.1), `relative_formal_adjoint_cross`
(a cross inner-product identity in standard form), and `gibbs_modular_flow`
(identifying modular unitaries with Hamiltonian evolution for Gibbs states).
Several bundled structure hypotheses (e.g. `TomitaTheorem`, `IntertwiningData`)
are dischargeable via the spectral calculus already in SpectralTheory.

**Layer 6: Applications.** The spectral and modular machinery is applied to:

- **The Dirac equation.** Clifford algebra (all 16 gamma matrix relations
  verified by computation, axiom-free), the Dirac Hamiltonian as an
  unbounded operator, its spectral gap, particle–antiparticle decomposition,
  positive-definite probability density, and probability conservation.

- **Relativistic thermodynamics.** Two independent routes to the same
  conclusion. SpectralTheory/RelThermo.lean (976 lines) proves unitarity
  of quantum time evolution and the first law of thermodynamics are in
  bijection. ModularTheory/ThermalTime.lean (521 lines) proves the Ott
  temperature transformation is forced by Tomita–Takesaki modular theory
  and the Connes cocycle. The two routes converge: the cocycle theorem
  provides the algebraic reason *why* unitarity and thermodynamics are
  linked, and the Ott correction is the Lorentz-covariant expression of
  that link.

- **Uncertainty relations.** Robertson, Schrödinger (with covariance),
  Heisenberg, and a second derivation of Heisenberg from information
  geometry via the Cramér–Rao bound. The information-geometric proof
  makes explicit that quantum uncertainty is a manifestation of the
  Fisher metric.

- **Bell's theorem.** The CHSH inequality (|S| ≤ 2 for local hidden
  variable models), Tsirelson's bound (|S| ≤ 2√2 for all quantum
  states), and the quantum violation (Bell state achieves 2√2). Ported
  from Echenim & Mhalla's Isabelle/HOL formalization with proper
  attribution, then substantially extended. This section works with
  finite-dimensional matrices — CHSH is inherently finite-dimensional —
  and proves Tsirelson's bound tight in both directions.

## Dependency graph

```
                    UnboundedObservable          Finite-dim matrices
                    (operator foundations)        (Mathlib Matrix)
                           │                           │
              ┌────────────┼────────────┐              │
              │            │            │              │
              ▼            ▼            ▼              ▼
         Uncertainty   Generator    Resolvent    BellsTheorem
         Relations     ─────────────────┤        CHSH, Tsirelson,
              │            │            │        quantum violation
              │            ▼            │
              │        Bochner ─────────┤
              │            │            │
              │            ▼            │
              │         Yosida ◄────────┘
              │            │
              │            ▼
              │      Stone's Theorem
              │            │
              │            ├────────────────────────┐
              │            ▼                        ▼
              │     Spectral Theorem          Schrödinger
              │     (3 routes agree)           Equation
              │            │
              │            ▼
              │    Functional Calculus
              │            │
              │     ┌──────┼──────────────────┐
              │     ▼      ▼                  ▼
              │   Dirac  RelThermo    TomitaTakesaki
              │                       S₀, Δ, J, σ_t
              │                           │
              │                     ┌─────┴──────┐
              │                     ▼            ▼
              │              RelativeModular   KMS/
              │              S_{ψ,φ}, Δ_{ψ,φ}  PeriodicStrip,
              │              (Dψ:Dφ)_t         Condition,
              │                     │          Modular
              │                     ▼            │
              │                  Cocycle ─────────┘
              │                  Out(M),  │
              │                  state-ind │
              │                           ▼
              │                     ThermalTime
              │                     Ott forced,
              │                     Landsberg refuted
              │
              └──► CramerRao.lean
                   (information geometry route)
```

## Design philosophy

### Domain honesty

The decision to model operators as genuinely partial functions — with
`Submodule ℂ H` domains and explicit membership proofs at every
application — is the single most important design choice in this library.
It has consequences everywhere:

- Computing `[A,B]ψ` requires four domain proofs, bundled in
  `DomainConditions`.
- The Yosida approximants are bounded (hence total), and their
  convergence to the unbounded generator happens *on the domain*.
- Stone's theorem is a statement about the domain of the generator
  equalling the set of vectors where a certain limit exists.
- The Tomita operator S₀ is defined on the dense subspace MΩ with an
  explicit well-definedness proof from the separating property of Ω.
  Its closure, polar decomposition, and the extraction of Δ and J all
  carry domain conditions through the construction.

This is more work than assuming everything is bounded. It is also correct.
The textbook approach of treating momentum as a matrix that you can
multiply by anything is, strictly speaking, wrong — and a proof assistant
will not let you get away with it.

### Axiom discipline

**The headline number is "12,000 lines, zero axioms."** That's the Uncertainty
section, the entire Stone's theorem development, and Bell's theorem —
proved from nothing but Lean's kernel and Mathlib. The 69 true axioms enter
in SpectralTheory (66) and ModularTheory (3). They fall into clear categories:

| Category | Count | Example |
|----------|------:|---------|
| Measure-theoretic machinery | ~24 | Bochner's theorem, DCT applications, Fubini |
| Spectral integral construction | ~22 | Simple function approximation, spectral integrals |
| PDE / analysis results | ~11 | Divergence theorem, continuity equation |
| Spectral existence | 1 | Compatible spectral measures exist |
| Modular theory | 3 | Closability (Reed–Simon VIII.1), cross adjoint, Gibbs flow |
| Miscellaneous | ~8 | Lorentzian approximation, Fourier uniqueness |

ModularTheory additionally uses **bundled structure hypotheses** — named
assumptions like `TomitaTheorem` and `IntertwiningData` that are not axioms
in the logical sense but package results whose full proofs require
substantial further infrastructure (e.g. unbounded polar decomposition,
the relative Tomita theorem). These are explicitly documented and
intended for discharge as the library grows. See the
[ModularTheory README](ModularTheory/) for the complete inventory.

Every axiom is documented in the file where it appears. The intent is
to discharge them as Mathlib grows and as time permits. The Uncertainty
and UnitaryEvo sections demonstrate that this is feasible: they were
written axiom-free from the start.

### Two proofs are better than one

Heisenberg's uncertainty principle is proved twice: once via Cauchy–Schwarz
(the textbook proof, in `Robertson.lean` → `Heisenberg.lean`) and once via
the Cramér–Rao bound from information geometry (in `CramerRao.lean`). The
spectral theorem is constructed via three routes that are proved to agree.
Relativistic thermodynamics is now approached from two directions:
RelThermo.lean (via unitarity and the first law) and ThermalTime.lean (via
the Connes cocycle and modular theory).

This is not redundancy. When different branches of mathematics produce the
same theorem through different proof architectures, you learn something
about both the theorem and your abstractions. The fact that `CramerRao.lean`
compiles and imports `Robertson.lean` proves that the library's type theory
for unbounded operators, commutators, variance, and domain conditions is
robust enough to support both algebraic and geometric arguments. The fact
that RelThermo and ThermalTime arrive at the same physics — one from
spectral theory, one from modular theory — proves that the library's
abstractions for von Neumann algebras and unbounded operators are mutually
consistent at the level of physical consequences. That is a stronger claim
than any individual theorem.

## What is not here (yet)

| Planned section | Depends on | Status |
|-----------------|------------|--------|
| **KMS discharge** | Spectral calculus for Δ^{iz} | Next target |
| **Full Tomita proof** | Unbounded polar decomposition | Planned |
| **Connes inverse** | KMS strip + analytic continuation | Planned |
| **Hydrogen atom** | Functional calculus, Coulomb potential | Planned |
| **Perturbation theory** | Resolvent, spectral projections | Planned |
| **Type III classification** | Cocycle + flow of weights | Future |
| **Haag–Hugenholtz–Winnink** | KMS + GNS | Future |
| **Bisognano–Wichmann** | Modular theory + Wightman axioms | Future |

The most impactful next step is the **KMS discharge**: proving that the
vacuum state ω(a) = ⟨Ω, aΩ⟩, equipped with the modular automorphism group
σ\_t from TomitaTakesaki.lean, satisfies `IsKMSState ω σ 1` as a theorem
rather than as a hypothesis. This requires constructing the KMS function
F\_{a,b}(z) = ⟨Ω, a Δ^{iz} b Ω⟩ using the spectral calculus for complex
powers of Δ, verifying analyticity on the strip, and checking the boundary
conditions. The spectral machinery in SpectralTheory/FunctionalCalc already
provides the foundation.

The Hydrogen atom requires the spectral theory of the Coulomb Hamiltonian
(-Δ - 1/r on L²(ℝ³)), which needs Kato's theorem on relative boundedness.
The resolvent and functional calculus machinery already in SpectralTheory
provides the right starting point.

Perturbation theory (Kato–Rellich, Dyson series) builds directly on the
resolvent identities proved in UnitaryEvo/Resolvent.

Type III classification, Haag–Hugenholtz–Winnink, and Bisognano–Wichmann
extend the modular theory into operator algebra classification and algebraic
quantum field theory. The cocycle machinery in ModularTheory/Cocycle.lean
is the entry point for all three.

## Building

This directory depends on Mathlib. Ensure your `lakefile.lean` points to
a compatible Mathlib commit (see the project root), then:

```
lake build LogosLibrary.QuantumMechanics
```

## References

### Operator theory and spectral theory
- M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, Academic Press, 1980.
- K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer, 2012.
- W. Rudin, *Functional Analysis*, 2nd ed., McGraw-Hill, 1991.

### Quantum mechanics (mathematical)
- B. C. Hall, *Quantum Theory for Mathematicians*, Springer, 2013.
- T. Kato, *Perturbation Theory for Linear Operators*, Springer, 1995.

### Quantum mechanics (physical)
- D. J. Griffiths, *Introduction to Quantum Mechanics*, 3rd ed., Cambridge, 2018.
- B. Thaller, *The Dirac Equation*, Springer, 1992.

### Information geometry
- S. Amari, *Information Geometry and Its Applications*, Springer, 2016.
- S. L. Braunstein, C. M. Caves, "Statistical distance and the geometry of quantum states", *Phys. Rev. Lett.* **72** (1994), 3439–3443.

### Uncertainty relations
- H. P. Robertson, "The uncertainty principle", *Phys. Rev.* **34** (1929), 163–164.
- E. Schrödinger, "Zum Heisenbergschen Unschärfeprinzip", *Sitzungsber. Preuss. Akad. Wiss.* (1930), 296–303.

### Bell's theorem
- J. S. Bell, "On the Einstein Podolsky Rosen paradox", *Physics* **1** (1964), 195–200.
- J. F. Clauser, M. A. Horne, A. Shimony, R. A. Holt, "Proposed experiment to test local hidden-variable theories", *Phys. Rev. Lett.* **23** (1969), 880–884.
- B. S. Tsirelson, "Quantum generalizations of Bell's inequality", *Lett. Math. Phys.* **4** (1980), 93–100.
- M. Echenim, M. Mhalla, "A formalization of the CHSH inequality and Tsirelson's upper-bound in Isabelle/HOL", 2023.

### Stone's theorem
- M. H. Stone, "On one-parameter unitary groups in Hilbert space", *Ann. Math.* **33** (1932), 643–648.
- J. von Neumann, "Über Funktionen von Funktionaloperatoren", *Ann. Math.* **33** (1932), 294–310.

### Modular theory
- M. Tomita, "Quasi-standard von Neumann algebras" (1967, unpublished).
- M. Takesaki, "Tomita's theory of modular Hilbert algebras and its application," *Lecture Notes in Mathematics* 128, Springer, 1970.
- M. Takesaki, *Theory of Operator Algebras I–III*, Springer, 1979–2003.
- A. Connes, "Une classification des facteurs de type III," *Ann. Sci. École Norm. Sup.* **6** (1973), 133–252.
- A. Connes, *Noncommutative Geometry*, Academic Press, 1994.

### Thermal time and KMS
- A. Connes, C. Rovelli, "Von Neumann algebra automorphisms and time-thermodynamics relation in generally covariant quantum theories," *Class. Quant. Grav.* **11** (1994), 2899–2917. [gr-qc/9406019]
- R. Kubo, "Statistical-mechanical theory of irreversible processes," *J. Phys. Soc. Japan* **12** (1957), 570–586.
- P. C. Martin, J. Schwinger, "Theory of many-particle systems. I," *Phys. Rev.* **115** (1959), 1342–1373.
- R. Haag, N. Hugenholtz, M. Winnink, "On the equilibrium states in quantum statistical mechanics," *Comm. Math. Phys.* **5** (1967), 215–236.

### Temperature transformation
- H. Ott, "Lorentz-Transformation der Wärme und der Temperatur," *Z. Physik* **175** (1963), 70–104.
- C. Rovelli, M. Smerlak, "Thermal time and Tolman–Ehrenfest effect," *Class. Quant. Grav.* **28** (2011), 075007.
- T.-T. Paetz, "An analysis of the 'thermal-time concept' of Connes and Rovelli," Diploma thesis, Georg-August-Universität Göttingen, 2010.
- N. Swanson, "Can quantum thermodynamics save time?," *Philosophy of Science* **88** (2021), 281–302.
- E. Y. S. Chua, "The time in thermal time," *J. Gen. Phil. Sci.* (2025).
