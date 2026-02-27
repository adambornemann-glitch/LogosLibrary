# Logos Library

**Formally Verified Foundations for Quantum Mechanics, Information Geometry, and Relativistic Thermodynamics**

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://leanprover.github.io/lean4/doc/)

---

## What This Is

Logos Library is a Lean 4 formalization project building verified
mathematical foundations for quantum mechanics and related physics. It is
built on [Mathlib](https://github.com/leanprover-community/mathlib4).

The library takes unbounded operators seriously. Quantum observables —
position, momentum, Hamiltonians — are not bounded operators on
finite-dimensional spaces. They are unbounded symmetric operators with
dense domains on infinite-dimensional Hilbert spaces, and every textbook
silently assumes the domain questions away. A proof assistant will not let
you do this, nor should it. The type `UnboundedObservable H` enforces
domain membership at the type level: you cannot apply an operator to a
vector without proving it lives in the domain. This is more work than
pretending everything is bounded. It is also correct.

**Current scope:**

| Module | Lines | Axioms | Contents |
|--------|------:|-------:|----------|
| [**QuantumMechanics/**](LogosLibrary/QuantumMechanics/) | ~22,100 | 66 | Stone's theorem, spectral theorem (3 routes), uncertainty relations, Bell's theorem, Dirac equation, unitarity ↔ first law |
| [**InformationGeometry/**](LogosLibrary/InformationGeometry/) | ~2,000 | 0 | Fisher–Rao metric from first principles, statistical manifolds, score functions |
| [**Relativity/**](LogosLibrary/Relativity/) | ~4,500 | 1 | Ott–Landsberg resolution (7 proofs), thermal time uniqueness, Kerr black hole application |
| **Total** | **~28,600** | **66** | |

Each module has its own detailed README. This document describes the
architecture connecting them.

---

## Axiom Discipline

The first ~14,000 lines of this library — the uncertainty relations, the
entirety of Stone's theorem, Bell's theorem, and all of information
geometry — use zero axioms beyond Lean's kernel and Mathlib. No `sorry`,
no `axiom`, no escape hatches.

The 66 axioms enter only when the development reaches spectral measure
construction and the Dirac PDE machinery, where substantial
measure-theoretic infrastructure not yet in Mathlib is required. They
fall into clear categories:

| Category | Count | Example |
|----------|------:|---------|
| Measure-theoretic machinery | ~24 | Bochner's theorem, DCT applications, Fubini |
| Spectral integral construction | ~22 | Simple function approximation, spectral integrals |
| PDE / analysis results | ~11 | Divergence theorem, continuity equation |
| Spectral existence | 1 | Compatible spectral measures exist |
| Miscellaneous | ~8 | Lorentzian approximation, Fourier uniqueness |

Every axiom is documented in the file where it appears. The intent is to
discharge them as Mathlib grows. The axiom-free sections demonstrate that
this is feasible: they were written without axioms from the start.

---

## Highlights

### Stone's Theorem (~11,000 lines, axiom-free)

The bijection between strongly continuous one-parameter unitary groups and
self-adjoint operators. Both directions: forward via Bochner integrals and
deficiency indices, reverse via Yosida approximation and Duhamel's formula.
The Schrödinger equation falls out as a one-page corollary — not an axiom,
but a theorem equivalent to probability conservation plus continuous
dynamics.

### Spectral Theorem (~10,100 lines, 66 axioms)

The spectral theorem for unbounded self-adjoint operators via three
independent routes — Bochner, resolvent/Stieltjes inversion, and Cayley
transform — proved to agree. The Borel functional calculus follows.

### Bell's Theorem (~3,000 lines, axiom-free - in definitions)

The CHSH inequality, Tsirelson's bound (proved tight in both directions),
and quantum violation via explicit computation on the Bell state. Ported
from Echenim & Mhalla's Isabelle/HOL formalization with proper attribution,
then substantially extended. This section works with finite-dimensional
matrices throughout — CHSH is inherently finite-dimensional and does not
require the unbounded operator machinery.

### Uncertainty Relations (~1,200 lines, axiom-free)

Robertson, Schrödinger (with covariance), and Heisenberg — proved twice.
Once via Cauchy–Schwarz (the textbook route) and once via the Cramér–Rao
bound from information geometry, making explicit that quantum uncertainty is
a manifestation of the Fisher metric. The fact that both proofs compile
against the same type-theoretic infrastructure is a stronger statement about
the library's design than either proof alone.

### Fisher–Rao Metric (~2,000 lines, axiom-free)

The Fisher information metric constructed from first principles: parametric
family of densities → score function → vanishing expectation → Fisher matrix
→ symmetry, positive definiteness, bilinearity → Riemannian metric on the
statistical manifold. The central exchange of limits (differentiating under
the integral sign) is justified via Mathlib's dominated convergence
infrastructure with explicit bounds at every step.

### Ott–Landsberg Resolution (~2,500 lines, 1 axiom)

The 60-year debate on relativistic temperature transformation, resolved.
Seven independent arguments — Landauer's principle, entropy invariance,
free energy, partition function, 4-vector structure, detailed balance,
specific heat — each forcing Ott's law T → γT and each refuting Landsberg.
Applied to Kerr black holes with explicit proofs for strictly subextremal
cases.

### Thermal Time Uniqueness (~2,000 lines, axiom-free)

Connes and Rovelli (1994) proposed t = τ/T relating physical time to modular
flow. This library proves the form is not a proposal but is forced: any
function f(T, τ) satisfying positivity, linearity in τ, and Lorentz
covariance must equal c · τ/T. Time dilation emerges as a consequence.

### Unitarity ↔ First Law (976 lines, 66 axioms)

A bijection between unitary quantum time evolution and the first law of
thermodynamics. This connects the Ott–Landsberg resolution to the quantum
mechanical foundations: the same structure that gives you unitary evolution
gives you the correct temperature transformation.

### The Dirac Equation (within SpectralTheory, 66 axioms)

Clifford algebra (all 16 gamma matrix relations verified by computation,
axiom-free), the Dirac Hamiltonian as an unbounded operator, spectral gap,
particle–antiparticle decomposition, positive-definite probability density,
and probability conservation.

---

## Architecture

```
                         Logos Library
                              │
               ┌──────────────┼──────────────┐
               │              │              │
               ▼              ▼              ▼
      InformationGeometry  QuantumMechanics  Relativity
      (Fisher–Rao metric)  (operator theory  (Ott, thermal
                            → spectral thm)   time, Kerr)
                              │
               ┌──────────────┼──────────────┐
               │              │              │
               ▼              ▼              ▼
          Uncertainty    UnitaryEvo     BellsTheorem
          Relations      (Stone's thm)  (CHSH, Tsirelson)
               │              │
               │              ▼
               │        SpectralTheory
               │         (3 routes)
               │              │
               │       ┌──────┼──────┐
               │       ▼      ▼      ▼
               │     Dirac  RelThermo  ···
               │             (↔ first law)
               │
               └──► CramerRao
                    (info geometry route
                     to Heisenberg)
```

The CramerRao module bridges QuantumMechanics and InformationGeometry:
Heisenberg's uncertainty principle derived from the Fisher metric rather
than Cauchy–Schwarz. The Relativity module connects to QuantumMechanics
through the unitarity ↔ first law bijection.

---

## Quick Start

```bash
# Clone
git clone https://github.com/adambornemann-glitch/Logos_Library
cd Logos_Library

# Install Lean 4 (if needed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Get mathlib cache
lake exe cache get

# Update dependencies
lake update

# Build everything
lake build

# Or build individual modules
lake build LogosLibrary.QuantumMechanics
lake build LogosLibrary.InformationGeometry
lake build LogosLibrary.Relativity
```

---

## Dependencies

- **Lean 4**: Version pinned in `lean-toolchain`
- **Mathlib4**: Commit pinned in `lakefile.lean`

---

## References

Each module README contains full references. The primary sources are:

- M. Reed, B. Simon, *Methods of Modern Mathematical Physics I*, Academic Press, 1980.
- K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer, 2012.
- B. C. Hall, *Quantum Theory for Mathematicians*, Springer, 2013.
- S. Amari, *Information Geometry and Its Applications*, Springer, 2016.
- M. Echenim, M. Mhalla, "A formalization of the CHSH inequality and Tsirelson's upper-bound in Isabelle/HOL", 2023.

---

## Contact

**Author:** Adam Bornemann
**Email:** AdamBornemann@gmail.com

---

## License

MIT

---

## Acknowledgments

Built with [Lean 4](https://leanprover.github.io/lean4/doc/) and
[Mathlib](https://github.com/leanprover-community/mathlib4).
