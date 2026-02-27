# Quantum Mechanics

**Status: ✅ Compiles. ~22,100 lines. Zero `sorry`.**

This directory is a formally verified development of non-relativistic and
relativistic quantum mechanics in Lean 4, built on Mathlib. It begins with
the operator theory that quantum mechanics actually requires — unbounded
symmetric operators on infinite-dimensional Hilbert spaces with explicit
domains — and carries this machinery through to Stone's theorem, the spectral
theorem, the Dirac equation, the complete uncertainty relation hierarchy, and
a formally verified bijection between unitarity and the first law of
thermodynamics.

The first ~12,000 lines contain zero axioms beyond Lean's kernel and Mathlib.

## What is here

| Section | Lines | Axioms | What it proves |
|---------|------:|-------:|----------------|
| [**Uncertainty/**](Uncertainty/) | ~1,200 | 0 | Robertson, Schrödinger, Heisenberg (twice: Cauchy–Schwarz and Cramér–Rao) |
| [**UnitaryEvo/**](UnitaryEvo/) | 7,754 | 0 | Stone's theorem, Schrödinger equation as corollary |
| [**BellsTheorem/**](BellsTheorem/) | 2,982 | 0 | CHSH inequality, Tsirelson's bound (tight), quantum violation |
| [**SpectralTheory/**](SpectralTheory/) | 10,139 | 66 | Spectral theorem (three routes), Borel functional calculus, Dirac equation, unitarity ↔ first law |
| **Total** | **~22,100** | **66** | |

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

**Layer 5: Applications.** The spectral machinery is applied to:

- **The Dirac equation.** Clifford algebra (all 16 gamma matrix relations
  verified by computation, axiom-free), the Dirac Hamiltonian as an
  unbounded operator, its spectral gap, particle–antiparticle decomposition,
  positive-definite probability density, and probability conservation.

- **Relativistic thermodynamics.** A 976-line proof that unitarity of
  quantum time evolution and the first law of thermodynamics are in
  bijection. This resolves the Ott–Landsberg debate (running since the
  1960s) by showing that Ott's transformation law for temperature under
  Lorentz boosts follows from the same structure that gives you unitary
  evolution.

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
              │     ┌──────┼──────┐
              │     ▼      ▼      ▼
              │   Dirac  RelThermo  ···
              │                    (Hydrogen, KMS,
              │                     Perturbation)
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

This is more work than assuming everything is bounded. It is also correct.
The textbook approach of treating momentum as a matrix that you can
multiply by anything is, strictly speaking, wrong — and a proof assistant
will not let you get away with it.

### Axiom discipline

**The headline number is "12,000 lines, zero axioms."** That's the Uncertainty
section, the entire Stone's theorem development, and Bell's theorem —
proved from nothing but Lean's kernel and Mathlib. The 66 axioms only enter
when you hit spectral measure construction and the Dirac PDE machinery in
SpectralTheory. They fall into clear categories:

| Category | Count | Example |
|----------|------:|---------|
| Measure-theoretic machinery | ~24 | Bochner's theorem, DCT applications, Fubini |
| Spectral integral construction | ~22 | Simple function approximation, spectral integrals |
| PDE / analysis results | ~11 | Divergence theorem, continuity equation |
| Spectral existence | 1 | Compatible spectral measures exist |
| Miscellaneous | ~8 | Lorentzian approximation, Fourier uniqueness |

Every axiom is documented in the file where it appears. The intent is
to discharge them as Mathlib grows and as time permits. The Uncertainty
and UnitaryEvo sections demonstrate that this is feasible: they were
written axiom-free from the start.

### Two proofs are better than one

Heisenberg's uncertainty principle is proved twice: once via Cauchy–Schwarz
(the textbook proof, in `Robertson.lean` → `Heisenberg.lean`) and once via
the Cramér–Rao bound from information geometry (in `CramerRao.lean`). The
spectral theorem is constructed via three routes that are proved to agree.

This is not redundancy. When different branches of mathematics produce the
same theorem through different proof architectures, you learn something
about both the theorem and your abstractions. The fact that `CramerRao.lean`
compiles and imports `Robertson.lean` proves that the library's type theory
for unbounded operators, commutators, variance, and domain conditions is
robust enough to support both algebraic and geometric arguments. That is
a stronger claim than any individual theorem.

## What is not here (yet)

| Planned section | Depends on | Status |
|-----------------|------------|--------|
| **Hydrogen atom** | Functional calculus, Coulomb potential | Planned |
| **Perturbation theory** | Resolvent, spectral projections | Planned |
| **KMS states** | Functional calculus, modular theory | Planned |

The Hydrogen atom requires the spectral theory of the Coulomb Hamiltonian
(-Δ - 1/r on L²(ℝ³)), which needs Kato's theorem on relative boundedness.
The resolvent and functional calculus machinery already in SpectralTheory
provides the right starting point.

Perturbation theory (Kato–Rellich, Dyson series) builds directly on the
resolvent identities proved in UnitaryEvo/Resolvent.

KMS (Kubo–Martin–Schwinger) states connect thermal equilibrium to modular
automorphisms of operator algebras, closing the loop between quantum
mechanics and thermodynamics that RelThermo.lean opens from the other
direction.

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
