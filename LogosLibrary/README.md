# LogosLibrary — Source Map

This is the Lean 4 source tree. If you're looking for what the project *is*,
see the [Logos Library README](../README.md). This document tells you where things
*are*.

---

**354 files · 54,343 lines of code · 4,034 proofs · 1,514 definitions · 114
axioms · 479 types**

---

## Module Overview

```
LogosLibrary/
├── InformationGeometry/         Classical and quantum information geometry
│   ├── CompositeObservable.lean Composite observable theory
│   ├── CramerRao/               Cramér-Rao lower bound
│   ├── Fisher/                  Fisher information, score, statistical manifolds
│   └── QuantumFisherModel.lean  Quantum Fisher information
│
├── QuantumComputing/            Computation meets thermodynamics
│   ├── PvNP/                    Thermodynamic approach to P vs NP
│   └── ThermalTuringMachine/    Landauer-aware computation
│
├── QuantumMechanics/            The core quantum library
│   ├── BellsTheorem/            CHSH, Tsirelson, LHV models
│   ├── ModularTheory/           Tomita-Takesaki, KMS, thermal time
│   ├── SpectralTheory/          Functional calculus, Dirac equation, Cayley transform
│   ├── Uncertainty/             Robertson, Schrödinger, Heisenberg, Cramér-Rao
│   └── UnitaryEvo/              Stone's theorem, Yosida, Bochner, resolvents
│
├── Relativity/                  Classical and semiclassical gravity
│   ├── GR/
│   │   ├── Forbidden/           Forbidden SdS (the wobble theorem)
│   │   └── Kerr/                Kerr metric, ring resolution, thermodynamics
│   ├── SR/                      Minkowski spacetime
│   └── Thermodynamics/          Jacobson's derivation, Ott transform
│
├── StochasticCalculus/          Rough paths from the ground up
│   ├── Stage_0/                 Sewing lemma and p-variation
│   │   ├── PVariation/          p-variation for paths
│   │   └── SewingLemma/         Three-layer sewing construction
│   ├── Stage_1/                 Young integration
│   │   └── YoungIntegration/    Defect, integral, p-var continuity
│   └── Stage_2/                 Rough paths and controlled paths
│       ├── Algebra/             Group-like elements, homogeneous norms, truncated tensors
│       ├── Axioms/              Normed tensor square data
│       ├── Controlled/          Controlled path definitions
│       ├── Integral/            Rough integral and Itô-Lyons map
│       └── RoughPath/           Rough path definitions
│
└── Superior/                    The unification layer
    ├── Bridges/                 Inter-framework dictionaries
    │   ├── CProcess.lean        C-process bridge
    │   └── Gravity/             EG↔SD, LQG↔EG, LQG↔SD, synthesis
    ├── CommonResources/         Shared algebraic and topological toolkit
    │   ├── CliffordPeriodicity/       Bott periodicity and clock for Clifford algebras
    │   ├── DivisionAlgebra/           ℝ, ℂ, ℍ, 𝕆 and their properties
    │   ├── GenerationsTheorem.lean    Three generations from octonion geometry
    │   ├── HopfTower/                 Hopf fibrations, Chern classes, Fano plane, knots
    │   │   ├── ChernClass.lean        U(1) bundles, Chern numbers, K-theory
    │   │   ├── FanoPlane/             Fano combinatorics, Boolean maps, G₂ automorphisms
    │   │   ├── HopfFibration.lean     The four Hopf maps and Adams' theorem
    │   │   └── Knots/                 Twelve-file knot tower (I–V, Möbius, Fueter, synthesis)
    │   ├── ModularFlow.lean           Modular flow machinery
    │   ├── Quintet.lean               The quintet equation (E = mc² = IkT ln 2)
    │   └── Time/                      Thermal time, supercausets, cosmology
    ├── EconomicGauge/           The Index Number Problem via differential geometry
    │   ├── BlochBridge.lean           Bloch sphere ↔ economic gauge bridge
    │   ├── ChernBridge.lean           Chern class bridge
    │   ├── Classification.lean        The Classification Theorem (c₁ ∈ ℤ)
    │   └── MalaneyWeinstein.lean      Malaney–Weinstein gauge connection
    ├── HotGravity/              Gravity as thermodynamics
    │   ├── EntropicGravity/           Clausius, entropic force, horizons, Newton/Einstein recovery
    │   ├── LoopQuantumGravity/        SU(2) reps, spin networks, spin foams, EPRL vertex,
    │   │                              quantum tetrahedra, modular theory, master theorem
    │   ├── NanoThermo/                Nanoscale thermodynamics, Page curve
    │   ├── ObjectiveReduction/        E-process, chemical measurement
    │   └── ShapeDynamics/             Entropic time, synthesis
    ├── KnotTheory/              Knots, strings, and gauge theory
    │   ├── Knots/                     Minimum knot, extended invariants
    │   ├── Strings/                   Basic, quaternionic, thermal, topological, synthesis
    │   └── YangMills/                 Entropy manifolds, topological mass gap
    ├── SpectralTriples/         Noncommutative geometry
    │   ├── GeometricUnity/            Metric bundle, Shiab operator, observerse Lagrangian, Λ
    │   ├── SpectralBridge.lean        NCG ↔ rest-of-library bridge
    │   └── Triples/                   Spectral triples, spectral action, product geometry
    └── SplitMechanics/          Thermal reinterpretation of quantum foundations
        ├── MöbiusGears/               Möbius cycle, bridge, four-tooth gear
        ├── Riemann/                   Thermodynamic zeta: beta, explicit formula, gears,
        │                              local/prime factors, positivity
        └── ThermalBell/               Decay gap, dictionary, CHSH, Tsirelson & more
```

## The Seven Pillars

### `InformationGeometry/`

Classical and quantum statistical geometry built from scratch. Defines
statistical models and manifolds, the score function, Fisher information (as
both a scalar and a Riemannian metric), and proves the Cramér-Rao bound via an
inner-product Cauchy-Schwarz inequality. The `CompositeObservable` file
extends the framework to composite observables, and `QuantumFisherModel`
provides a quantum information-geometric model. This is the
information-theoretic foundation that the rest of the library draws on. See
the [Information Geometry README](InformationGeometry/README.md).

### `QuantumComputing/`

Two lines of development. The **Thermal Turing Machine** formalises
Landauer-aware computation where erasure costs energy, building up from
one-bit operations through simplex structures. The **P vs NP** module takes a
thermodynamic angle: computation embeddings, cost-blind reductions, locality
bounds, phase transitions, and symmetry breaking — the thesis being that
computational hardness has a thermodynamic signature. See the
[Quantum Computing README](QuantumComputing/README.md).

### `QuantumMechanics/`

The largest and most foundational module. See the
[Quantum Mechanics README](QuantumMechanics/README.md). Five sub-libraries:

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

A three-stage pipeline from the sewing lemma to rough integration. See the
[Stochastic Calculus README](StochasticCalculus/README.md).

- **Stage 0**: The foundations. The sewing lemma is built in three layers of
  increasing generality (dyadic partitions, decay estimates, continuous
  control), each with its own map construction proving existence and
  uniqueness of the sewn limit. Alongside it, p-variation for paths.

- **Stage 1**: Young integration. Defect estimates, the integral definition,
  linearity, integration by parts, regularity, consistency, uniqueness, and
  p-variation continuity of the Young integral.

- **Stage 2**: Rough paths proper. Algebraic foundations (group-like elements
  in truncated tensor algebras, homogeneous norms), controlled path
  definitions, and the rough integral culminating in the Itô-Lyons map —
  the universal limit theorem that makes rough path theory work. These feed
  into the thermodynamic arguments elsewhere.

### `Superior/`

The unification layer — where everything comes together. This is the most
ambitious part of the library: an attempt to show that gravity, quantum
mechanics, knot theory, and noncommutative geometry are different facets of a
single thermodynamic structure. See the
[Superior README](Superior/README.md).

- **Bridges**: Translation dictionaries between frameworks. Entropic gravity
  ↔ shape dynamics, loop quantum gravity ↔ entropic gravity, LQG ↔ shape
  dynamics, synthesis files that tie them together, and a C-process bridge.

- **CommonResources**: The shared algebraic toolkit. Clifford algebras with
  Bott periodicity (basic theory, clock, dimensions, Möbius clock, signature,
  spinor data, tables), division algebras (ℝ, ℂ, ℍ, 𝕆), the Hopf tower
  (fibrations, Adams' theorem, Chern classes and K-theory, the Fano plane
  with G₂ automorphisms, a twelve-file knot tower from Knot I through Knot V
  plus Möbius tower, Fueter restriction, non-associativity, self-similarity,
  and synthesis), a generations theorem deriving three fermion families from
  octonion geometry, modular flow, the quintet equation, thermal time (basic
  theory, consistency, information theory, measurement), and supercausets
  (basic, cosmology, quaternionic entropy, synthesis, thermal causets).

- **EconomicGauge**: The gauge-theoretic approach to economic index numbers
  introduced by Pia Malaney in her 1996 Harvard thesis *The Index Number
  Problem: A Differential Geometric Approach*. The central result is the
  **Classification Theorem**: the topological type of an economy — the
  irreducible obstruction to consistent price comparison — is a single
  integer, the first Chern number c₁ ∈ ℤ of the purchasing power bundle.
  Four files: the Malaney-Weinstein gauge connection, the classification
  theorem, plus Bloch sphere and Chern class bridges to the physics.

- **HotGravity**: Gravity from thermodynamics. Entropic gravity (Clausius
  relation, entropic force, horizons, recovery of Newton and Einstein,
  synthesis). Loop quantum gravity (SU(2) representations, spin networks,
  spin foams, EPRL vertex, quantum tetrahedra, modular theory, master
  theorem — seven files totalling over 200 proofs). Nanoscale thermodynamics
  (definition, limits, monotonicity, biconditional, Page curve). Objective
  reduction (E-process, chemical measurement). Shape dynamics (entropic time,
  synthesis).

- **KnotTheory**: Minimum knots and extended invariants. Strings (basic,
  quaternionic, thermal, topological, synthesis). Yang-Mills (entropy
  manifolds, topological mass gap).

- **SpectralTriples**: Noncommutative geometry via Connes-style spectral
  triples (definitions, spectral action, concrete spectrum, product geometry).
  Geometric Unity (metric bundle, Shiab operator, observerse Lagrangian,
  computing Λ). Spectral bridge connecting these to the rest.

- **SplitMechanics**: A thermal reinterpretation of quantum foundations, now
  with three sub-modules. **ThermalBell**: CHSH, constraints, core, decay gap,
  dictionary, entropy, geometry, Tsirelson. **MöbiusGears**: Möbius cycle,
  bridge, and four-tooth gear constructions. **Riemann**: a thermodynamic
  approach to the zeta function via gear assemblies — zeta data, beta
  function, local and prime factors, explicit formula, gear assembly,
  positivity, and an Archimedean gear. Also: Bohmian mechanics, It-from-Split,
  and subsystem emergence.

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
StochasticCalculus ───────────────────────────────────┤
  Stage_0 → Stage_1 → Stage_2                         │
                                                      │
QuantumComputing ─────────────────────────────────────┘
```

The `Superior` module sits at the top, importing from all others. The
`CommonResources` sub-module provides shared algebraic structures
(Clifford algebras, Hopf fibrations, quaternions) that are used across
multiple `Superior` sub-modules.

## Statistics at a Glance

**Files:** 354 `.lean` files

## Summary

| Metric | Count |
|--------|------:|
| Total raw lines | 124,623 |
| Lines of code (no block comments, no blanks, no `--`-only) | 54,343 |
| Blank lines | 21,261 |
| Comment-only lines (`--`) | 3,769 |
| Lines inside `/- -/` block comments | 55,081 |

## Declarations

| Kind | Count |
|------|------:|
| `theorem` | 3,148 |
| `lemma` | 886 |
| `def` | 1,495 |
| `axiom` | 114 |
| `structure` | 446 |
| `class` | 6 |
| `instance` | 34 |
| `abbrev` | 19 |
| `inductive` | 27 |
| **Proofs (theorem + lemma)** | **4,034** |
| **Definitions (def + abbrev)** | **1,514** |
| **Axioms** | **114** |
| **Types (structure + class + inductive)** | **479** |

The comment-to-code ratio has now crossed 1:1 — 58,850 comment lines to
54,343 code lines. Whether this is commendable documentation or excessive
editorialising remains a matter of perspective.

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
| 8 | `Superior/HotGravity/ShapeDynamics/EntropicTime.lean` | 52 |
| 9 | `Relativity/Thermodynamics/Jacobson.lean` | 51 |
| 10 | `Superior/CommonResources/DivisionAlgebra/Basic.lean` | 51 |
| 11 | `Superior/CommonResources/DivisionAlgebra/Quaternions.lean` | 51 |
| 12 | `Superior/HotGravity/ShapeDynamics/Synthesis.lean` | 51 |
| 13 | `Superior/CommonResources/HopfTower/HopfFibration.lean` | 50 |
| 14 | `QuantumComputing/ThermalTuringMachine/Lemmas.lean` | 44 |
| 15 | `Superior/SpectralTriples/Triples/ConcreteSpectrum.lean` | 44 |
| 16 | `Superior/SplitMechanics/BohmianMech.lean` | 42 |
| 17 | `Superior/SpectralTriples/Triples/ProductGeometry.lean` | 40 |
| 18 | `Superior/CommonResources/CliffordPeriodicity/Clock.lean` | 39 |
| 19 | `Superior/HotGravity/LoopQuantumGravity/EPRLVertex.lean` | 38 |
| 20 | `Superior/HotGravity/LoopQuantumGravity/SU2Rep.lean` | 38 |

## Axiom Transparency

The library contains **114 axioms**. This sounds like a lot until you look at
what they actually are. The vast majority are mathematical infrastructure —
results that are true, well-known, and simply awaiting formalisation in
Mathlib. The genuinely *physical* commitments are few and clearly delineated.

### Axioms by Category

| Category | Count | What they are |
|----------|------:|---------------|
| Spectral theory infrastructure | 57 | Spectral integrals, resolvent kernels, functional calculus, Bochner |
| Hopf fibrations / topology | 19 | Hopf maps, Adams' theorem, Chern classes, K-theory, Fano plane, G₂, homotopy groups, Hurwitz |
| Quantum foundations | 11 | KMS speed limit, Born rule, GNS construction, Tomita-Takesaki, modular Hamiltonian |
| Riemann / zeta function | 8 | Euler product, Weil positivity, gear assembly, exp bounds |
| Relativity / black holes | 7 | Thermal excitation, proper time, Cauchy instability, equilibrium |
| Noncommutative geometry | 6 | Fiber integrals, spectral action, Geometric Unity placeholders |
| Knot theory / gauge theory | 5 | Color triples, SU(3) stabiliser, energy bound, boundary principle |
| Economic gauge theory | 1 | Chern-Weil integral quantisation |

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

### The Topological Axioms (19 axioms)

Deep topological results stated without proof: Adams' theorem (only four Hopf
fibrations exist), Hurwitz's theorem (division algebras only in dimensions
1, 2, 4, 8), homotopy groups of spheres, U(1) bundle classification over S²,
K-theory of spheres, G₂ transitivity on octonion subalgebras, the Fano plane
orbit structure, and the generations theorem stabiliser. These are theorems in
mathematics, not assumptions about physics.

### The Physical Axioms (~15 axioms)

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

### The Riemann Axioms (8 axioms)

New to this version. These support the thermodynamic approach to the zeta
function in `SplitMechanics/Riemann/`. Two are numerical (`exp 1 < 3` and
`2 < exp 1` — embarrassingly provable, just not yet proved here). The rest
are structural: the Euler product identity, Weil positivity implying zeros on
the critical line, gear assembly combinatorics, and global limit convergence.
The headline axiom is `weilPositivity_implies_onLine`: if the Weil positivity
condition holds, then every zero lies on the critical line. This is the
conditional core of the Riemann module — the library doesn't claim to prove
RH, it formalises what would follow from a thermodynamic positivity condition.

### The Remaining Axioms (13 axioms)

Noncommutative geometry placeholders (6): fiber integrals producing
Einstein-Hilbert and Yang-Mills actions, spinor decomposition, symmetric space
Einstein condition, fiber volume positivity, chimeric gauge curvature.

Knot theory / gauge theory (5): color triple existence and standardness, SU(3)
stabiliser structure, energy bound, and boundary principle for the mass gap.

Economic gauge theory (1): Chern-Weil integral quantisation.

### How to Read This

If you want to evaluate a specific result in this library:

1. Find the theorem.
2. Trace its imports.
3. Identify which axioms it depends on.
4. Decide if you accept them.

The spectral theory axioms are "I believe standard functional analysis."
The physical axioms are "I believe this about the universe." The topological
axioms are "I believe Adams proved this in 1960." The Riemann axioms are
"I believe this conditional structure." The library makes no effort to hide
the distinction.

For a full axiom catalogue with exact signatures, file locations, and
namespace groupings, see the [Axiom Audit](axiom_audit.md).

For quick statistics, run:
```bash
python3 lean_stats.py LogosLibrary/     # library statistics
grep -rn "^axiom\|^noncomputable axiom\|^private axiom" LogosLibrary/ | wc -l  # axiom count
```


