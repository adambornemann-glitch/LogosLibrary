# LogosLibrary — Source Map

This is the Lean 4 source tree. If you're looking for what the project *is*,
see the [Logos Library README](../README.md). This document tells you where things
*are*.

---

**268 files · 45,716 lines of code · 3,569 proofs · 1,453 definitions · 106
axioms · 455 types**

---

## Module Overview

```
LogosLibrary/
├── InformationGeometry/     Classical information geometry
│   ├── CramerRao/           Cramér-Rao lower bound
│   └── Fisher/              Fisher information, score, statistical manifolds
│
├── QuantumComputing/        Computation meets thermodynamics
│   ├── PvNP/                Thermodynamic approach to P vs NP
│   └── ThermalTuringMachine/  Landauer-aware computation
│
├── QuantumMechanics/        The core quantum library
│   ├── BellsTheorem/        CHSH, Tsirelson, LHV models
│   ├── ModularTheory/       Tomita-Takesaki, KMS, thermal time
│   ├── SpectralTheory/      Functional calculus, Dirac equation, Cayley transform
│   ├── Uncertainty/         Robertson, Schrödinger, Heisenberg, Cramér-Rao
│   └── UnitaryEvo/          Stone's theorem, Yosida, Bochner, resolvents
│
├── Relativity/              Classical and semiclassical gravity
│   ├── GR/
│   │   ├── Forbidden/       Forbidden SdS (the wobble theorem)
│   │   └── Kerr/            Kerr metric, ring resolution, thermodynamics
│   ├── SR/                  Minkowski spacetime
│   └── Thermodynamics/      Jacobson's derivation, Ott transform
│
├── StochasticCalculus/      Rough paths foundations
│   ├── PVariation/          p-variation for paths
│   └── SewingLemma.lean     The sewing lemma
│
└── Superior/                The unification layer
    ├── Bridges/             Inter-framework dictionaries
    ├── CommonResources/     Shared algebraic and topological toolkit
    │   ├── CliffordPeriodicity/   Bott periodicity and clock for Clifford algebras
    │   ├── DivisionAlgebra/      ℝ, ℂ, ℍ, 𝕆 and their properties
    │   ├── HopfTower/            Hopf fibrations, knots, octonions
    │   ├── ModularFlow            Modular flow machinery
    │   ├── Quintet                The quintet equation (E = mc² = IkT ln 2)
    │   └── Time/                  Thermal time, supercausets, cosmology
    ├── EconomicGauge/       The Index Number Problem: A Differential Geometric Approach
    ├── HotGravity/          Gravity as thermodynamics
    │   ├── EntropicGravity/       Verlinde-style entropic force, recovery of Newton/Einstein
    │   ├── LoopQuantumGravity/    Spin networks, spin foams, EPRL vertex, quantum tetrahedra
    │   ├── NanoThermo/            Nanoscale thermodynamics, Page curve
    │   ├── ObjectiveReduction/    Measurement as thermodynamic process
    │   └── ShapeDynamics/         Shape dynamics, entropic time
    ├── KnotTheory/          Knots, strings, and gauge theory
    │   ├── Knots/                 Minimum knot, extended invariants
    │   ├── Strings/               String-theoretic structures, quaternionic strings
    │   └── YangMills/             Entropy manifolds, topological mass gap
    ├── SpectralTriples/     Noncommutative geometry
    │   ├── GeometricUnity/        Metric bundle, Shiab operator, observerse Lagrangian
    │   └── Triples/               Spectral triples, spectral action, product geometry
    └── SplitMechanics/      Thermal reinterpretation of quantum foundations
        └── ThermalBell/          Decay Gap, Dictionary & more.
```

## The Seven Pillars

### `InformationGeometry/`

Classical statistical geometry built from scratch. Defines statistical models
and manifolds, the score function, Fisher information (as both a scalar and a
Riemannian metric), and proves the Cramér-Rao bound via an inner-product
Cauchy-Schwarz inequality. This is the information-theoretic foundation that
the rest of the library draws on.  See the [Information Geometry README](InformationGeometry/README.md).

### `QuantumComputing/`

Two lines of development. The **Thermal Turing Machine** formalises
Landauer-aware computation where erasure costs energy, building up from
one-bit operations through simplex structures. The **P vs NP** module takes a
thermodynamic angle: computation embeddings, cost-blind reductions, locality
bounds, phase transitions, and symmetry breaking — the thesis being that
computational hardness has a thermodynamic signature.  See the
[Quantum Computing README](QuantumComputing/README.md).

### `QuantumMechanics/`

The largest and most foundational module. See the
[Quantum Mechanics README](QuantumMechanics/README.md).  Five sub-libraries:

- **BellsTheorem**: Full CHSH formalism, Tsirelson's bound (via commutator
  algebra and unitary bounds), local hidden variable models, quantum
  correlations, and the violation theorem. This is textbook quantum
  foundations done properly.

- **ModularTheory**: Tomita-Takesaki modular theory, KMS conditions
  (including the periodic strip construction), cocycles, relative modular
  operators, and thermal time. This is the operator-algebraic backbone.

- **SpectralTheory**: Three routes to the spectral theorem (Bochner,
  resolvent, Cayley transform), plus the full functional calculus pipeline
  (algebraic, bounded, cross-measure, scalar measure, spectral projections).
  Also contains the Dirac equation: Clifford algebras, gamma matrix traces,
  Pauli matrices, conserved currents, and spectral theory of the Dirac
  operator. Also relativistic thermodynamics.

- **Uncertainty**: Robertson, Schrödinger, and Heisenberg uncertainty
  relations, plus unbounded operator infrastructure. The Forbidden SdS proof
  imports directly from here.

- **UnitaryEvo**: Stone's theorem and everything needed to prove it. The
  Yosida approximation (with Duhamel's formula, exponential bounds, adjoint
  properties, convergence), Bochner integrals for operator-valued functions,
  and a comprehensive resolvent library (analytic properties, identities,
  norm bounds, range characterisation, surjectivity). This is serious
  functional analysis.

### `Relativity/`

General and special relativity, plus gravitational thermodynamics.

- **GR/Forbidden**: The Forbidden SdS proof — angular momentum operators,
  Robertson uncertainty, thermal excitation, reductio, lifetime estimates, and
  the measurement theorem. See the
  [Forbidden SdS README](Relativity/GR/Forbidden/README.md).

- **GR/Kerr**: The Kerr metric library — Boyer-Lindquist coordinates, horizon
  structure, ergosphere, thermodynamics, singularity resolution via finite
  complexity, extensions, and the quintet equation. See the
  [Kerr README](Relativity/GR/Kerr/README.md).

- **SR**: Minkowski spacetime definitions and basic properties.

- **Thermodynamics**: Jacobson's derivation of Einstein's equations from
  thermodynamic assumptions, and the Ott relativistic temperature
  transformation. These two files alone contain 105 proofs.

### `StochasticCalculus/`

Rough paths theory: p-variation for paths and the sewing lemma. These
are foundational tools for stochastic analysis that appear to feed into the
thermodynamic arguments elsewhere.  See the [Stochastic Calculus README](StochasticCalculus/README.md).

### `Superior/`

The unification layer — where everything comes together. This is the most
ambitious part of the library: an attempt to show that gravity, quantum
mechanics, knot theory, and noncommutative geometry are different facets of a
single thermodynamic structure.  See the
  [Superior README](Superior/README.md).

- **Bridges**: Translation dictionaries between frameworks. Entropic gravity
  ↔ shape dynamics, loop quantum gravity ↔ entropic gravity, LQG ↔ shape
  dynamics, and synthesis files that tie them together.

- **CommonResources**: The shared algebraic toolkit. Clifford algebras with
  Bott periodicity, division algebras (ℝ, ℂ, ℍ, 𝕆), the Hopf tower
  (fibrations, knots, octonions), modular flow, the quintet equation, thermal
  time (basic theory, consistency, information theory, measurement), and
  supercausets (basic, cosmology, quaternionic entropy, synthesis, thermal
  causets).

- **EconomicGauge**: # The gauge-theoretic approach to
  economic index numbers introduced by Pia Malaney in her 1996 Harvard
  thesis *The Index Number Problem: A Differential Geometric Approach*.
  The central result is the **Classification Theorem**: the topological
  type of an economy—the irreducible obstruction to consistent price
  comparison—is a single integer, the first Chern number c₁ ∈ ℤ of
  the purchasing power bundle.

- **HotGravity**: Gravity from thermodynamics. Entropic gravity (Clausius
  relation, entropic force, horizons, recovery of Newton and Einstein,
  synthesis). Loop quantum gravity (SU(2) representations, spin networks,
  spin foams, EPRL vertex, quantum tetrahedra, modular theory, master
  theorem). Nanoscale thermodynamics (definition, limits, monotonicity,
  biconditional, Page curve). Objective reduction (E-process, chemical
  measurement). Shape dynamics (entropic time, synthesis).

- **KnotTheory**: Minimum knots and extended invariants. Strings (basic,
  quaternionic, thermal, topological, synthesis). Yang-Mills (entropy
  manifolds, topological mass gap).

- **SpectralTriples**: Noncommutative geometry via Connes-style spectral
  triples (definitions, spectral action, concrete spectrum, product geometry).
  Geometric Unity (metric bundle, Shiab operator, observerse Lagrangian,
  computing Λ). Spectral bridge connecting these to the rest.

- **SplitMechanics**: A thermal reinterpretation of quantum foundations.
  Thermal Bell inequalities (asymmetric temperature, duality structure, hidden
  structure, no-signaling, optimal budget, origin of 2√2, PR boxes, pointwise
  bounds, quantum compatibility, sequential measurements, shared energy
  budget). Thermal local hidden variables (TLHV: critical questions,
  decomposition, measurement, reduction, setting-dependent, summary, thermal
  dictionary). Other inequalities (CGLMP, KCBS, Leggett-Garg, qutrit,
  ThermMerm, unity). Plus Bohmian mechanics, It-from-Split, and subsystem
  emergence.

## Dependency Flow

The broad dependency structure flows upward:

```
InformationGeometry ──────────────────────────────────┐
                                                      │
QuantumMechanics ─────────────────────────────────────┤
  ├── Uncertainty ← Robertson, unbounded operators    │
  ├── SpectralTheory ← functional calculus            │
  ├── ModularTheory ← Tomita-Takesaki, KMS            ├──→ Superior
  ├── UnitaryEvo ← Stone's theorem, Yosida            │
  └── BellsTheorem ← CHSH, Tsirelson                  │
                                                      │
Relativity ───────────────────────────────────────────┤
  ├── SR ← Minkowski                                  │
  ├── GR ← Forbidden SdS, Kerr                        │
  └── Thermodynamics ← Jacobson, Ott                  │
                                                      │
StochasticCalculus ───────────────────────────────────┘
QuantumComputing ─────────────────────────────────────┘
```

The `Superior` module sits at the top, importing from all others. The
`CommonResources` sub-module provides shared algebraic structures
(Clifford algebras, Hopf fibrations, quaternions) that are used across
multiple `Superior` sub-modules.

## Statistics at a Glance

**Files:** 263 `.lean` files

## Summary

| Metric | Count |
|--------|------:|
| Total raw lines | 99,806 |
| Lines of code (no block comments, no blanks, no `--`-only) | 42,787 |
| Blank lines | 17,619 |
| Comment-only lines (`--`) | 3,080 |
| Lines inside `/- -/` block comments | 44,577 |

## Declarations

| Kind | Count |
|------|------:|
| `theorem` | 2,658 |
| `lemma` | 794 |
| `def` | 1,273 |
| `axiom` | 101 |
| `structure` | 375 |
| `class` | 5 |
| `instance` | 20 |
| `abbrev` | 12 |
| `inductive` | 22 |
| **Proofs (theorem + lemma)** | **3,452** |
| **Definitions (def + abbrev)** | **1,285** |
| **Axioms** | **101** |
| **Types (structure + class + inductive)** | **402** |

The comment-to-code ratio is nearly 1:1, which is either commendable
documentation or excessive editorialising depending on your perspective.

## Top 20 Files by Proof Count (theorem + lemma)

| # | File | Proofs |
|--:|------|-------:|
| 1 | `Superior/HotGravity/EntropicGravity/EntropicForce.lean` | 65 |
| 2 | `Superior/HotGravity/EntropicGravity/Recovery.lean` | 64 |
| 3 | `Superior/SpectralTriples/Triples/SpectralDefs.lean` | 63 |
| 4 | `Superior/SpectralTriples/GeometricUnity/ObserverseLagrangian.lean` | 60 |
| 5 | `Superior/SpectralTriples/GeometricUnity/ShiabOperator.lean` | 59 |
| 6 | `Superior/HotGravity/EntropicGravity/Horizons.lean` | 55 |
| 7 | `Relativity/Thermodynamics/Ott.lean` | 54 |
| 8 | `Superior/CommonResources/HopfTower/HopfTowerKnot.lean` | 53 |
| 9 | `Superior/HotGravity/ShapeDynamics/EntropicTime.lean` | 52 |
| 10 | `Relativity/Thermodynamics/Jacobson.lean` | 51 |
| 11 | `Superior/CommonResources/DivisionAlgebra/Basic.lean` | 51 |
| 12 | `Superior/HotGravity/ShapeDynamics/Synthesis.lean` | 51 |
| 13 | `Superior/CommonResources/HopfTower/HopfFibration.lean` | 50 |
| 14 | `QuantumComputing/ThermalTuringMachine/Lemmas.lean` | 44 |
| 15 | `Superior/SpectralTriples/Triples/ConcreteSpectrum.lean` | 44 |
| 16 | `Superior/SplitMechanics/BohmianMech.lean` | 42 |
| 17 | `Superior/CommonResources/DivisionAlgebra/Quaternions.lean` | 40 |
| 18 | `Superior/SpectralTriples/Triples/ProductGeometry.lean` | 40 |
| 19 | `Superior/CommonResources/CliffordPeriodicity/Clock.lean` | 39 |
| 20 | `Superior/CommonResources/HopfTower/HopfTowerOctonion.lean` | 38 |

## Axiom Transparency

The library contains **101 axioms**. This sounds like a lot until you look at
what they actually are. The vast majority are mathematical infrastructure —
results that are true, well-known, and simply awaiting formalisation in
Mathlib. The genuinely *physical* commitments are few and clearly delineated.

### Axioms by Category

| Category | Count | What they are |
|----------|------:|---------------|
| Spectral theory infrastructure | 57 | Spectral integrals, resolvent kernels, functional calculus, Bochner |
| Relativity / black holes | 7 | Thermal excitation, proper time, Cauchy instability, equilibrium |
| Hopf fibrations / topology | 10 | Existence of Hopf maps, Adams' theorem, homotopy groups, Hurwitz |
| Noncommutative geometry | 6 | Fiber integrals, spectral action, Geometric Unity placeholders |
| Quantum foundations | 11 | KMS speed limit, Born rule, GNS construction, Tomita-Takesaki |
| Knot theory / gauge theory | 5 | Color triples, SU(3) stabiliser, energy bound, boundary principle |
| Modular theory | 2 | Relative formal adjoint, Gibbs modular flow |

### The Spectral Theory Bulk (57 axioms)

Over half the axioms live in `QuantumMechanics/SpectralTheory/`. These are
*not* physical assumptions — they are mathematical facts about spectral
measures, functional calculus, resolvent operators, and the Dirac equation
that are standard in functional analysis but not yet available in Mathlib.
Examples: Bochner's theorem, Stone's formula, Lorentzian kernel concentration,
dominated convergence for arctan kernels, agreement of the three routes to the
spectral theorem. These axioms are placeholders for theorems that *could* be
proved in Lean given sufficient upstream library support. They are the price
of building on top of mathematics that Mathlib hasn't got to yet.

### The Physical Axioms (~20 axioms)

These are the ones that carry actual physical content — the assumptions you
must accept (or deny) to buy the conclusions:

**Forbidden SdS** (1 axiom): `thermal_excites_after_positive_time` — a thermal
bath at positive temperature excites angular momentum. This is the sole
physical axiom of the wobble theorem.

**Kerr metric** (6 axioms): Proper time integrals, Cauchy horizon instability,
vacuum validity range, and thermal equilibrium. Standard GR and semiclassical
results stated without proof.

**Quantum foundations** (11 axioms): GNS construction, Tomita-Takesaki theorem,
modular Hamiltonian existence, purity/faithfulness under restriction, KMS as
speed limit, Born rule as KMS. These encode the operator-algebraic framework
for quantum mechanics.

**Modular theory** (2 axioms): The relative formal adjoint cross-relation and
the Gibbs modular flow condition.

### The Topological Axioms (~15 axioms)

Deep topological results stated without proof: Adams' theorem (only four Hopf
fibrations exist), Hurwitz's theorem (division algebras only in dimensions
1, 2, 4, 8), homotopy groups of spheres. Also: gauge theory axioms for the
mass gap argument (energy bound, boundary principle). These are theorems in
mathematics, not assumptions about physics.

### How to Read This

If you want to evaluate a specific result in this library:

1. Find the theorem.
2. Trace its imports.
3. Identify which axioms it depends on.
4. Decide if you accept them.

The spectral theory axioms are "I believe standard functional analysis."
The physical axioms are "I believe this about the universe." The topological
axioms are "I believe Adams proved this in 1960." The library makes no effort
to hide the distinction.

For a full axiom catalogue with exact signatures and file locations, run:
```bash
python3 lean_stats.py LogosLibrary/     # library statistics
grep -rn "^axiom\|^noncomputable axiom\|^private axiom" LogosLibrary/ | wc -l  # axiom count
```
