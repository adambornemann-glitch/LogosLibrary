# The Superior Method

**Machine-verified structural comparison across physics — via Curry–Howard
as a structural comparator.**

---

## What This Is

Superior is a map, not the terrain.

Quantum mechanics, general relativity, and thermodynamics are the terrain —
established by experiment, understood through decades of physical intuition.
Superior does not compete with any of them.  What it does is fly over all
three at 50,000 feet and photograph the geology.  It's the SR-71 of proof
techniques: no engagement with the ground, no ordnance dropped — just
reconnaissance at altitude, fast enough that the type-checker clears every
frame before you can argue with it.

The tool is the Curry–Howard correspondence, used not to *do* physics but
to *compare* physics: each domain is formalised independently as a Lean 4
structure, and the type-checker reports whether two independently-built
structures are secretly the same mathematical object.  When a bridge
file compiles, the identification is a theorem.  When it fails to compile,
the difference is a theorem.  Both outcomes are informative.

**What is verified:** Algebraic and dimensional consistency.  Every theorem
is machine-checked.  Every physical assumption is an explicit, named
structure field.  There are no hidden gaps.

**What is not verified:** Physical truth.  The compiler checks mathematics,
not physics.  Whether the structures that recur across modules reflect
something about nature is an empirical question — and one that no amount
of type-checking can answer.

---

## The Method in Detail

The Curry–Howard correspondence turns structural comparison into
type-checking:

| Physics | Lean 4 | What the compiler checks |
|---------|--------|--------------------------|
| Physical law | Structure field (a type) | "This quantity must exist and satisfy these constraints" |
| Consistency | Canonical instance (a term) | "Here is concrete data satisfying all constraints simultaneously" |
| Consequence | Theorem (a function on the structure) | "Given any instance, this relationship holds" |
| Cross-domain identification | Bridge file (a definitional equality) | "The structure from Module A *is* the structure from Module B" |

A structure that cannot be instantiated — because its fields are
contradictory — is uninhabitable.  The contradiction is caught at compile
time.  A bridge that cannot be proved — because the two structures genuinely
differ — fails to compile.  Both outcomes are informative.

The key features of the approach:

- **Explicit axioms.** Every physical assumption is a named field in a
  structure.  `grep` for them.  Count them.  Argue about whether they're
  reasonable.  They are not buried in definitions or hidden in notation.
  The full catalogue is in the [Axiom Audit](axiom_audit.md).
- **Zero sorry policy.** `sorry` is Lean's explicit marker for "I haven't
  proved this yet."  Two appear in the entire framework (both genuine open
  problems in the literature).  Everything else is complete.
- **Independent construction.** Modules are built without importing each
  other.  When two modules produce the same structure, this is *discovered*
  by the bridge file, not *assumed* by shared imports.
- **Mechanical verification.** A human reader might miss a subtle error in
  a 30-page calculation.  The Lean type-checker cannot.

---

## The Organising Observation

The modular automorphism group of a faithful state on a von Neumann
algebra — the mathematical core of the Tomita–Takesaki theorem — appears
in different guises across physics:

- In **thermodynamics**, it generates the KMS (thermal equilibrium) flow
- In **quantum field theory**, it generates Lorentz boosts (Bisognano–Wichmann)
- In **black hole physics**, it generates the Hawking temperature
- In **quantum measurement**, one modular cycle separates reversible and
  irreversible processes
- In **the Connes–Rovelli thermal time hypothesis**, it generates physical
  time itself
- In **causal set theory**, one modular cycle is one birth event
- In **number theory**, one modular cycle is a local functional equation
  at each prime

The framework does not postulate that these are the same.  It formalises
each domain separately, then checks — via bridge files — whether the
structures coincide.  In every case checked, they do.

---

## The Architecture

The framework is organised into six clusters plus a shared foundation.
Each cluster groups related modules; bridges connect across clusters.

**CommonResources** provides the shared mathematical infrastructure:
division algebras, Clifford periodicity, the Hopf tower (including the
Fano plane and Chern classes), modular flow, and time (Thermal Time +
Super-Causets).

Each cluster's internal bridges live inside the cluster.  Only genuinely
lateral connections — between modules in different clusters — live in
`Bridges/`.

---

## The Clusters

### CommonResources — Shared Foundations
[see README](CommonResources/README.md)

**[Division Algebras](CommonResources/DivisionAlgebra/README.md)**
Basic definitions, quaternion infrastructure, and
the algebraic foundations shared by KnotTheory and SpectralTriples.
(102 theorems, 0 sorry, 0 axioms)

**[Clifford Periodicity](CommonResources/CliffordPeriodicity/README.md)**
The 8-fold periodicity of real Clifford algebras as a verified lookup
API.  Target result: Cl(9,0) ≅ M₁₆(ℂ) — the Clifford algebra of a
9-dimensional Riemannian manifold is intrinsically complex with spinor
fibre ℂ¹⁶.  Uniqueness theorem: n = 3 is the only base dimension for
which the chimeric bundle Met(Xⁿ) produces this structure.  Includes
the Bott clock, the ABS classification for indefinite signatures,
signature cancellation, and the Möbius conjugation map.
(104 theorems, 0 sorry, 0 axioms)

**[Hopf Tower](CommonResources/HopfTower/README.md)**
The Cayley–Dickson doubling chain ℝ ↪ ℂ ↪ ℍ ↪ 𝕆 and the four Hopf
fibrations between spheres.  Five binding theorems ("Knots") prove each
Hopf map restricts to the previous one under the canonical embedding.
The Fueter restriction chain Δ₈ → Δ₄ → Δ₂ → Δ₁.  Möbius involution
axioms at every level.  Non-associativity of 𝕆 by explicit witness,
proving the tower terminates.  Includes [Chern classes](CommonResources/HopfTower/ChernClass.lean)
for U(1) bundles over S² and the [Fano Plane](CommonResources/HopfTower/FanoPlane/README.md) —
seven quaternionic subalgebras of 𝕆, the boolean map strategy, and the
three-generation structure from G₂ orbits.
(199 theorems, 0 sorry, 14 axioms — Adams' theorem, Hopf fibration
existence, G₂ transitivity, and Chern class infrastructure)

**Generations Theorem** — The three-generation structure of the Standard
Model as a theorem of octonionic incidence geometry.
(11 theorems, 0 sorry, 1 axiom)

**Modular Flow** — Shared modular flow infrastructure used across clusters.
(33 theorems, 0 sorry, 0 axioms)

**Quintet** — The five-fold structure linking modular flow instances.
(26 theorems, 0 sorry, 0 axioms)

**[Thermal Time](CommonResources/Time/ThermalTime/README.md)**
Formalises the Connes–Rovelli thermal time hypothesis:
physical time is the modular flow rescaled by temperature, t = τ/T.
Resolves the Ott–Landsberg debate on relativistic temperature through
seven independent proofs.  Derives time dilation as a theorem of
thermodynamics.  Proves that measurements require ΔS ≥ 2π nats.
(61 theorems, 0 sorry, 0 axioms)

**[Super-Causets](CommonResources/Time/SuperCausets/README.md)**
Causal set theory with the Second Law as ontologically
prior.  If entropy is strictly monotone along the causal relation
(x ≺ y ⟹ S(x) < S(y)), then irreflexivity and asymmetry of the causal
order are *theorems*, not axioms.  One birth event equals one modular cycle
(2π nats).  Three physical requirements force the entropy parameter to be
quaternionic (ℍ), yielding D_spatial = 3 via the Hopf fibration.  The
spectral action on the total space U⁹ recovers the Standard Model.
Poisson fluctuations give Λ ∼ 2π/√N.  Two `sorry` (both open problems:
Gibbs inequality and the causal set Hauptvermutung).
(106 theorems, 2 sorry, 0 axioms)

---

### KnotTheory — Strings, Gauge Theory, and the Hopf Knots

**Strings** — QCD flux tubes as strings with time from modular flow.
From string tension σ > 0: three spatial dimensions with emergent time,
the Lüscher coefficient −π/12 from two transverse modes, a gravitational
hierarchy relation, and time-temperature conjugacy.
(73 theorems, 0 sorry, 4 axioms — standard topology facts)

**Yang–Mills / Topological Mass Gap** — The mass gap reframed as a
topological obstruction: the minimum energy of a closed colour-flux
configuration, determined by the gauge group's division-algebraic
structure.  Hurwitz's theorem forces exactly three non-trivial gauge
factors: U(1), SU(2), SU(3).

> **Important caveat:** This is a topological reframing, not a proof in
> the Wightman-axiomatic sense required by the Clay Millennium Problem.

(67 theorems, 0 sorry, 2 axioms)

**Knots** *(internal bridges)* — The Hopf Knot proves the complex and
quaternionic Hopf fibrations are one construction under ℂ ↪ ℍ: the
embedding S³ ↪ S⁷ preserves the sphere, the Hopf maps correspond, and
the S¹ fiber actions commute.  The Extended Knot continues to 𝕆 and
proves confinement from non-associativity: the type `ColorFactorization`
is uninhabitable.
(53 theorems, 0 sorry, 3 axioms)

---

### HotGravity — Thermodynamic Approaches to Gravity and Measurement

**Entropic Gravity** — Verlinde's entropic gravity program, formalised
and extended.  From S = A/(4G) and T = a/(2π), derives Newton's laws,
Einstein's field equations, the Schrödinger equation, and the
Diósi–Penrose collapse timescale.  Parametric analysis separates structural
results (any modular period α) from quantitative ones (α = 2π).  See the
[Entropic Gravity README](HotGravity/EntropicGravity/README.md).
(253 theorems, 0 sorry, 0 axioms)

**Loop Quantum Gravity** — A formal skeleton of LQG from SU(2)
representations through the EPRL vertex amplitude.  Covers: representation
theory with enforced dimension formulae, quantum tetrahedra with volume
and area operators, spin networks on K₅, spin foam dynamics, modular
theory for boundary states, and the EPRL synthesis.  All arithmetic in ℕ
via the encoding twoJ = 2j.  Contains universal theorems (area gap, Casimir
injectivity, equal-spin universality) proved for all spins, not
spot-checked.  A 27-number numerical fingerprint serves as a compile-time
regression test.  See the [LQG README](HotGravity/LoopQuantumGravity/README.md).
(207 theorems, 0 sorry, 0 axioms)

**Nanothermodynamics** — Proves that Hill's nanothermodynamics (subdivision
potential, Hamiltonian of mean force, anomalous heat capacities,
non-extensive entropy) is restricted modular flow.  The translation:
"trace out environment" = restrict to subalgebra; "subdivision potential"
= entropic cost of the algebraic cut.  See the
[Nanothermodynamics README](HotGravity/NanoThermo/README.md).
(70 theorems, 0 sorry, 0 axioms)

**Shape Dynamics** — A thermodynamic completion of Barbour–Gomes–Gryb–Koslowski
Shape Dynamics.  CMC slicing is thermal equilibrium, York time is
thermodynamic time, temperature interpolates continuously between QM
(T → 0) and classical Shape Dynamics (T → ∞).  The Schrödinger equation
is recovered as the zero-temperature limit.  See the
[Shape Dynamics README](HotGravity/ShapeDynamics/README.md).
(103 theorems, 0 sorry, 0 axioms)

**Objective Reduction** — The 2π-nat threshold applied to physical
decoherence.  Three sub-modules: Diósi–Penrose gravitational decoherence,
chemical measurement theory (Marcus electron transfer, Born–Oppenheimer
as a decoherence-rate inequality), and a bridge proving chemical
decoherence and nanothermodynamic subdivision are the same phenomenon.
See the [Objective Reduction README](HotGravity/ObjectiveReduction/README.md).
(33 theorems, 0 sorry, 0 axioms)

---

### SpectralTriples — Noncommutative Geometry and the Observerse

**Triples** — The spectral triple on U⁹.  KO classification, Clifford
types, Seeley–DeWitt heat kernel expansion with 5 bosonic poles, fiber
bundle decomposition U⁹ = X³ × Sym²₊(ℝ³), Kaluza–Klein mechanism
(gauge curvature emerges from the product geometry, though neither factor
carries gauge curvature alone), S³ spectrum, and coupling constants.  See
the [Spectral Triples README](SpectralTriples/README.md).
(177 theorems, 0 sorry, 2 axioms)

**Geometric Unity** — Two layers of Eric Weinstein's Geometric Unity.
Layer 1: the observerse U⁹ = Tot(Met(X³)) is 9-dimensional, Bott
periodicity gives Cl(9,0) ≅ M₁₆(ℂ), the spinor fibre ℂ¹⁶ accommodates
one generation of SM fermions plus a right-handed neutrino.  Layer 2: the
spectral action on U⁹ via Connes' noncommutative geometry, with the
chimeric bundle, shiab operator, and gauge breaking U(16) →
SU(3) × SU(2) × U(1).  See the
[Geometric Unity README](SpectralTriples/GeometricUnity/README.md).
(189 theorems, 0 sorry, 4 axioms)

**Spectral Bridge** *(internal bridge)* — Term-by-term match between the
spectral action on U⁹ and the Observerse Lagrangian: gravity ↔ a₂,
gauge ↔ a₄, fermions ↔ ½⟨Jψ, Dψ⟩.  The correspondence is the unique
dimensionally consistent assignment (of 3! = 6 possible, exactly one
works).
(18 theorems, 0 sorry, 0 axioms)

---

### SplitMechanics — The Subsystem Decomposition and Its Consequences

**The Subsystem Pentagon** — When a pure global state is restricted to a
subsystem (partial trace), the resulting mixed state has a modular operator
Δ ≠ 1.  Five features emerge simultaneously — the KMS condition, the Born
rule (via GNS), nontrivial modular flow, unitarity, and spectral
invariance — proved to stand or fall together.  Also resolves the foliation
problem of Bohmian mechanics by writing the guiding equation in modular
time.
(70 theorems, 0 sorry, 9 axioms — GNS, Tomita–Takesaki, and restriction
properties awaiting Mathlib infrastructure)

**Thermal Bell** — Bell inequality violations as a thermal phenomenon.
The CHSH bound, Tsirelson's bound, and the decay gap between quantum and
classical correlations, all derived from the KMS structure of subsystem
states.
(123 theorems, 0 sorry, 0 axioms)

**[Möbius Gears](SplitMechanics/MobiusGears/README.md)** — A type-class
framework for conjugation operators satisfying a 4-axiom tooth profile
(involution, anti-structure, size preservation, ground state).  Three
known instances: Cayley–Dickson conjugation (algebraic, 4/4 axioms),
Tomita modular conjugation (operator-theoretic, 4/4), and Bott clock
conjugation (combinatorial shadow, 1/4).  The triangle theorem proves
the algebraic and operator twists are the same object in different
categories, while the combinatorial twist is a faithful but lossy shadow.
(67 theorems, 0 sorry, 0 axioms in the algebraic files)

**[The Riemann Machine](SplitMechanics/Riemann/README.md)** — The Riemann
Hypothesis expressed as a positivity condition on a network of Möbius
gears indexed by the primes of ℚ.  Each prime contributes a local gear
satisfying the 4-axiom tooth profile, with β_p = log p as the forced
inverse temperature.  Five equivalent formulations of RH are proved
mutually equivalent.  The framework **does not prove RH** — it proves
that the Möbius gear language is a consistent and complete vocabulary
for expressing it, and reduces the problem to a single analytic limit step.
(93 theorems, 0 sorry, 8 axioms — Weil converse, global limit convergence,
and analytic data)

---

### EconomicGauge — Gauge Theory and the Index Number Problem

**[Economic Gauge Theory](EconomicGauge/README.md)** — A formalisation and
extension of the Malaney–Weinstein gauge-theoretic approach to economic
index numbers.  The numéraire freedom (choice of unit of account) is a
U(1) gauge symmetry.  The Malaney–Weinstein connection 1-form encodes
the Divisia price index as parallel transport, curvature measures path
dependence, and the Classification Theorem proves that the topological
type of an economy is a single integer: the first Chern number c₁ ∈ ℤ
of the purchasing power bundle.

Extensions beyond the original thesis: the Bloch ball identification
(expenditure shares map isometrically into S² via the square-root
embedding, with Fisher = Fubini–Study), topological classification by
Chern number, and the Bott periodicity connection (KU vs KO information
loss).
(69 theorems, 0 sorry, 1 axiom — Chern–Weil integral)

---

### Bridges — Lateral Connections Between Clusters

Intra-cluster wiring lives inside its cluster.  What remains in Bridges/
are genuinely lateral connections between clusters with no shared ancestor
besides CommonResources.

**CProcess** — Connects Objective Reduction and Nanothermodynamics (both
in HotGravity).  Chemical decoherence and nanothermodynamic subdivision
are the same phenomenon: at decoherence, I(A:B) = 2π, giving ε = 2πT/N.
Marcus monotonicity is NanoThermo's `subdivision_monotone_in_MI` applied
to chemistry.
(14 theorems, 0 sorry, 0 axioms)

**Gravity Bridges** — Pairwise and triangular compatibility proofs for
LQG, Entropic Gravity, and Shape Dynamics (all in HotGravity).  Three
pairwise bridges plus one triangular synthesis proving mutual consistency
across 41 physical postulates with 0 bridge postulates.  See the
[Gravity Bridges README](Bridges/Gravity/README.md).
(103 theorems, 0 sorry, 0 axioms)

---

## Cluster Dependencies

```
Self-contained clusters (no cross-cluster imports):
  SplitMechanics
  KnotTheory         (internal Knots connect Strings ↔ YangMills)
  HotGravity         (internal Gravity bridges connect submodules)
  SpectralTriples    (internal SpectralBridge connects submodules)
  EconomicGauge

Shared foundation:
  CommonResources    provides DivisionAlgebra, CliffordPeriodicity,
                     HopfTower (incl. FanoPlane, ChernClass, Knots),
                     ModularFlow, Quintet, GenerationsTheorem, and
                     Time (ThermalTime + SuperCausets) to all clusters

Cross-cluster bridges:
  Bridges/CProcess   HotGravity: ObjectiveReduction ↔ NanoThermo
  Bridges/Gravity/   HotGravity: LQG ↔ EntropicGravity ↔ ShapeDynamics
```

---

## Recurring Structures

Several results appear independently across modules and are then
identified by bridge files:

| Structure | Modules where it appears independently |
|-----------|---------------------------------------|
| 2π nats = one modular cycle | Thermal Time, NanoThermo, Objective Reduction, Shape Dynamics, Split Mechanics, Entropic Gravity, LQG, Super-Causets |
| K = H/T Lorentz-invariant | Thermal Time, Strings, NanoThermo, Split Mechanics, Super-Causets |
| Ott transformation T → γT | Thermal Time (×7), Strings, NanoThermo, Shape Dynamics, Entropic Gravity, Super-Causets |
| S¹ fibre persistence through Hopf tower | Strings, Yang–Mills, Knots, Super-Causets |
| Cl(9) ≅ M₁₆(ℂ) from Bott periodicity | Geometric Unity, Spectral Triples, Spectral Bridge, Super-Causets, Clifford Periodicity |
| E_grav × τ = ℏ | Shape Dynamics, Objective Reduction, Strings, Entropic Gravity |
| ℍ forced by R1 + R2 + R3 | Strings, Super-Causets |
| D_spatial = 3 from Hopf base | Strings, Super-Causets, Clifford Periodicity (uniqueness) |
| 4-axiom Möbius tooth profile | Hopf Tower (CD), Split Mechanics (Tomita), Riemann Machine (arithmetic) |
| Fisher = Fubini–Study | Economic Gauge (Bloch bridge) |

The recurrence is not built in — each module derives from its own starting
point.  The recurrence is discovered, not assumed.

---

## Combined Statistics

| Module | Theorems | `sorry` | Axioms |
|--------|:--------:|:-------:|:------:|
| **CommonResources** | | | |
| Division Algebras | 102 | 0 | 0 |
| Clifford Periodicity | 104 | 0 | 0 |
| Hopf Tower (incl. Fano, Chern) | 199 | 0 | 14 |
| Generations Theorem | 11 | 0 | 1 |
| Modular Flow | 33 | 0 | 0 |
| Quintet | 26 | 0 | 0 |
| Thermal Time | 61 | 0 | 0 |
| Super-Causets | 106 | 2 | 0 |
| **KnotTheory** | | | |
| Strings | 73 | 0 | 4 |
| Yang–Mills / Mass Gap | 67 | 0 | 2 |
| Knots (internal bridges) | 53 | 0 | 3 |
| **HotGravity** | | | |
| Entropic Gravity | 253 | 0 | 0 |
| Loop Quantum Gravity | 207 | 0 | 0 |
| Nanothermodynamics | 70 | 0 | 0 |
| Shape Dynamics | 103 | 0 | 0 |
| Objective Reduction | 33 | 0 | 0 |
| **SpectralTriples** | | | |
| Triples | 177 | 0 | 2 |
| Geometric Unity | 189 | 0 | 4 |
| Spectral Bridge (internal) | 18 | 0 | 0 |
| **SplitMechanics** | | | |
| Subsystem Pentagon + Bohmian | 70 | 0 | 9 |
| Thermal Bell | 123 | 0 | 0 |
| Möbius Gears | 67 | 0 | 0 |
| Riemann Machine | 93 | 0 | 8 |
| **EconomicGauge** | 69 | 0 | 1 |
| **Bridges** | | | |
| CProcess | 14 | 0 | 0 |
| Gravity (4 files) | 103 | 0 | 0 |
| **Total** | **2,425** | **2** | **48** |

**130 files.  67,400 lines.  21,769 lines of code.**

**A note on accounting:** The axiom count (48) reflects irreducible
assumptions from algebraic topology (Adams' theorem, Hopf fibration
existence, homotopy groups), Lie group theory (G₂ transitivity),
operator algebras (GNS, Tomita–Takesaki), Riemannian geometry
(symmetric space Einstein condition), and analytic number theory
(Weil converse, global limit convergence) that Mathlib does not yet
cover.  Structure fields (physical postulates like "entropy is monotone
along the causal order") are not counted as axioms — they are the
explicit inputs to each module, visible in the type signature of every
theorem that uses them.  The full axiom catalogue with source locations
is in the [Axiom Audit](axiom_audit.md).

---

## What Is and Isn't Claimed

**What the method does:**

It verifies the algebraic and dimensional consistency of a modular-flow
approach to physics across multiple domains.  It proves that structures
built independently in separate modules are the same mathematical objects.
It machine-checks every theorem.  It separates physical interpretation from
mathematical content explicitly in every module.  It carries physical
constants (G, ℏ, k_B, c) explicitly throughout — never silently setting
them to 1.

**What the method does not do:**

It does not construct the full differential-geometric objects (chimeric
connections, fibre integration maps) that would be needed for a complete
formalisation — Mathlib does not yet have the infrastructure.  It does not
compute physical predictions (coupling constants, mass ratios, mixing
angles).  It does not claim to solve the Clay Millennium Problem or prove
the Riemann Hypothesis.  It does not address the preferred-split problem —
the choice of subsystem decomposition is an input, not derived.  And it
does not verify physical interpretations by machine: the proof assistant
checks mathematics, not physics.

The central observation — that modular flow provides a common algebraic
skeleton across these domains — is supported by algebraic evidence.  The
algebraic evidence is what the compiler verifies.  Whether nature actually
works this way is an empirical question that no amount of type-checking
can answer.

---

## File Structure

```
Superior/
├── CommonResources/
│   ├── CliffordPeriodicity/       Bott clock, Cl(p,q), uniqueness of dim 9
│   │   ├── Basic.lean             Base fields ℝ/ℂ/ℍ, algebra structure types
│   │   ├── Table.lean             Cl(0)–Cl(15), periodicity step function
│   │   ├── Clock.lean             Universal characterisation, ℂ unique fixed pt
│   │   ├── MobiusClock.lean       Conjugation k ↦ (8−k), palindrome symmetry
│   │   ├── Signature.lean         Cl(p,q), ABS index, signature cancellation
│   │   ├── Dimensions.lean        n=3 unique base dim yielding ℂ¹⁶ spinors
│   │   └── SpinorData.lean        Spinor bundle, U(16), Hermitian decomposition
│   ├── DivisionAlgebra/           Basic definitions, quaternions
│   │   ├── Basic.lean
│   │   └── Quaternions.lean
│   ├── HopfTower/                 ℝ ↪ ℂ ↪ ℍ ↪ 𝕆 via Cayley-Dickson
│   │   ├── ChernClass.lean        U(1) bundles over S², K-theory
│   │   ├── FanoPlane/             Seven ℍ-subalgebras of 𝕆, G₂, generations
│   │   │   ├── Defs.lean          Incidence structure, multiplication table
│   │   │   ├── BoolMap.lean       Boolean subalgebra proofs (28 goals by ring)
│   │   │   └── G2Automorph.lean   G₂ = Aut(𝕆), three orbits
│   │   ├── HopfFibration.lean     Four Hopf maps, Adams' theorem
│   │   └── Knots/                 Five binding theorems, Fueter chain, Möbius J
│   │       ├── Defs.lean          Hopf maps, embeddings, Fueter symbols
│   │       ├── Knot_I–V.lean      ℝ↪ℂ, ℂ↪ℍ, ℝ↪ℍ, ℍ↪𝕆, ℝ↪𝕆
│   │       ├── FueterRestriction   Δ₈ → Δ₄ → Δ₂ → Δ₁
│   │       ├── NonAssociativity    𝕆 witness, ℍ⊂𝕆 associativity
│   │       ├── InclusionChain      S⁰ ⊂ S¹ ⊂ S³ ⊂ S⁷
│   │       ├── SelfSimilarity      TowerKnotData, dimension doubling
│   │       ├── MobiusTower.lean    J axioms at ℍ and 𝕆, restriction chain
│   │       └── Synthesis.lean      Master theorem: all eight properties
│   ├── GenerationsTheorem.lean    Three generations from 𝕆 incidence
│   ├── ModularFlow.lean           Shared modular flow infrastructure
│   ├── Quintet.lean               Five-fold modular structure
│   └── Time/
│       ├── ThermalTime/           Connes–Rovelli, KMS, Ott covariance
│       └── SuperCausets/          Second Law → partial order → ℍ → D=3
│
├── KnotTheory/
│   ├── Strings/                   QCD flux tubes, Lüscher, emergent dimensions
│   ├── YangMills/                 Topological mass gap, Hurwitz → gauge factors
│   └── Knots/                     Strings ↔ YangMills (ℂ ↪ ℍ ↪ 𝕆)
│
├── HotGravity/
│   ├── EntropicGravity/           Verlinde → Newton, Einstein, Schrödinger
│   ├── LoopQuantumGravity/        SU(2) reps → spin networks → EPRL vertex
│   ├── NanoThermo/                Hill = modular flow, subdivision potential
│   ├── ObjectiveReduction/        Diósi–Penrose, chemical measurement, 2π
│   └── ShapeDynamics/             QM ↔ classical interpolation, York time
│
├── SpectralTriples/
│   ├── Triples/                   Spectral action, Seeley–DeWitt, spectrum
│   ├── GeometricUnity/            Observerse U⁹, Cl(9) ≅ M₁₆(ℂ), shiab
│   └── SpectralBridge.lean        Triples ↔ GeometricUnity term-by-term
│
├── SplitMechanics/
│   ├── ItFromSplit.lean           Subsystem Pentagon: five features at once
│   ├── BohmianMech.lean           Foliation problem, guiding eq in modular time
│   ├── ThermalBell/               CHSH, Tsirelson, Bell violations as KMS
│   ├── MobiusGears/               4-axiom tooth profile, CD ↔ Tomita ↔ Bott
│   │   ├── MobiusTower.lean       CD conjugation at ℍ and 𝕆
│   │   ├── MobiusBridge.lean      CD ↔ Bott bridge, intertwining failure
│   │   ├── MobiusCycle.lean       Tomita J as Möbius half-twist
│   │   └── FourTooth.lean         Triangle theorem, 4-axiom comparison
│   └── Riemann/                   RH as Möbius gear positivity
│       ├── ZetaData.lean          ξ(s), functional equation, RH as a type
│       ├── ExplicitFormula.lean   Weil kernel, WeilPositivity ↔ RH
│       ├── LocalFactor.lean       Tooth profile per place of ℚ
│       ├── ArchimedeanGear.lean   Γ_ℝ(s), Gaussian, Fourier-as-J
│       ├── PrimeFactor.lean       Euler factors, β_p = log p forced
│       ├── GearAssembly.lean      Meshing, carrier shaft, semi-local growth
│       ├── BetaFunction.lean      β-function, partition identity
│       └── Positivity.lean        Five faces of RH, global coherence
│
├── EconomicGauge/
│   ├── MalaneyWeinstein.lean      MW connection, Divisia, curvature, arbitrage
│   ├── BlochBridge.lean           Bloch ball, Fisher = Fubini–Study
│   ├── ChernBridge.lean           Chern number, KU vs KO information loss
│   └── Classification.lean        Full pipeline, grand unified theorem
│
└── Bridges/
    ├── CProcess.lean              ObjectiveReduction ↔ NanoThermo
    └── Gravity/                   LQG ↔ EG ↔ SD pairwise + triangle
        ├── LQGtoEQ.lean
        ├── EGtoSD.lean
        ├── LQGtoSD.lean
        └── Synthesis.lean
```

---

## Citation

```bibtex
@software{bornemann2026superior,
  author = {Bornemann, Adam},
  title = {The Superior Method: Machine-Verified Structural Comparison
           Across Physics in Lean 4},
  year = {2026},
  url = {https://gitlab.com/pedagogical/logos_library}
}
```

---

## Disclaimer

All errors and misinterpretations are solely the responsibility of the
author (Adam Bornemann).  This is an independent project.  It has not been
reviewed or endorsed by Erik Verlinde, Ted Jacobson, Alain Connes, Carlo
Rovelli, Julian Barbour, Eric Weinstein, Roger Penrose, Lajos Diósi,
Alain Chamseddine, Lee Smolin, Rafael Sorkin, Pia Malaney, or any other
physicist or mathematician whose work is referenced.

The goal is to explore what happens when modular flow is taken seriously
as a unifying structure — and to make the algebraic consequences
machine-checkable.  Whether this perspective is physically correct is a
question for experiment, not for compilers.

---

## License

MIT. See [LICENSE](../LICENSE).
