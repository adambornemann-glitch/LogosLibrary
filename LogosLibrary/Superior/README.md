# The Superior Method

**Machine-verified algebraic consistency across physics — via Curry-Howard as
a structural comparator.**

---

## What This Is

Superior is a **methodology**, not a theory. The method:

1. Formalise a domain of physics in Lean 4, with every physical assumption
   as an explicit named structure field.
2. Formalise a second domain independently — different file, different
   starting assumptions, no imports between them.
3. Write a bridge file. Ask: does Lean's type checker accept that the
   structure built in Module A is *definitionally equal* to the structure
   built in Module B?

If the bridge compiles, the two domains share algebraic structure. If it
doesn't, they don't. The compiler is the comparator. It doesn't care about
physical intuition, reputation, or plausibility. It checks whether two
independently constructed mathematical objects are the same object.

This is Curry-Howard used as an experimental instrument: propositions are
types, proofs are terms, and structural coincidence is a *checkable fact*
rather than a hand-wavy analogy.

The method is applied here across modules spanning quantum mechanics,
thermodynamics, gauge theory, gravity, causal set theory, and spectral
geometry — organised into five clusters plus a shared foundation. The
modules are connected by explicit bridge files that prove — or fail to
prove — structural identifications. In every case checked so far, the
identifications compile.

**What is verified:** Algebraic and dimensional consistency. Every theorem
is machine-checked. Every physical assumption is an explicit, named
structure field. There are no hidden gaps.

**What is not verified:** Physical truth. The compiler checks mathematics,
not physics. Whether the structures that recur across modules reflect
something about nature is an empirical question.

---

## The Method in Detail

The Curry-Howard correspondence turns structural comparison into
type-checking:

| Physics | Lean 4 | What the compiler checks |
|---------|--------|--------------------------|
| Physical law | Structure field (a type) | "This quantity must exist and satisfy these constraints" |
| Consistency | Canonical instance (a term) | "Here is concrete data satisfying all constraints simultaneously" |
| Consequence | Theorem (a function on the structure) | "Given any instance, this relationship holds" |
| Cross-domain identification | Bridge file (a definitional equality) | "The structure from Module A *is* the structure from Module B" |

A structure that cannot be instantiated — because its fields are
contradictory — is uninhabitable. The contradiction is caught at compile
time. A bridge that cannot be proved — because the two structures genuinely
differ — fails to compile. Both outcomes are informative.

The key features of the approach:

- **Explicit axioms.** Every physical assumption is a named field in a
  structure. `grep` for them. Count them. Argue about whether they're
  reasonable. They are not buried in definitions or hidden in notation.
- **Zero sorry policy.** `sorry` is Lean's explicit marker for "I haven't
  proved this yet." Two appear in the entire framework (both genuine open
  problems in the literature). Everything else is complete.
- **Independent construction.** Modules are built without importing each
  other. When two modules produce the same structure, this is *discovered*
  by the bridge file, not *assumed* by shared imports.
- **Mechanical verification.** A human reader might miss a subtle error in
  a 30-page calculation. The Lean type-checker cannot.

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

The framework does not postulate that these are the same. It formalises
each domain separately, then checks — via bridge files — whether the
structures coincide. In every case checked, they do.

---

## The Architecture

The framework is organised into five clusters plus a shared foundation.
Each cluster groups related modules; bridges connect across clusters.

**CommonResources** provides the shared mathematical infrastructure:
division algebras, the Hopf tower, and time (Thermal Time + Super-Causets).

Each cluster's internal bridges live inside the cluster. Only genuinely
lateral connections — between modules in different clusters — live in
`Bridges/`.

---

## The Clusters

### CommonResources — Shared Foundations
[see README](CommonResources/README.md)

**[Division Algebras](CommonResources/DivisionAlgebras/README.md)**
Basic definitions, quaternion infrastructure, and
the algebraic foundations shared by KnotTheory and SpectralTriples.

**[Hopf Tower](CommonResources/README.md)**
The Cayley-Dickson doubling chain ℝ ↪ ℂ ↪ ℍ ↪ 𝕆.
Hopf fibrations at each level (S¹ → S³ → S², S³ → S⁷ → S⁴,
S⁷ → S¹⁵ → S⁸), Clifford periodicity, the Fueter chain, and the
non-associativity witness for 𝕆.

**[Thermal Time](CommonResources/Time/ThermalTime/README.md)**
Formalises the Connes–Rovelli thermal time hypothesis:
physical time is the modular flow rescaled by temperature, t = τ/T.
Resolves the Ott–Landsberg debate on relativistic temperature through
seven independent proofs. Derives time dilation as a theorem of
thermodynamics. Proves that measurements require ΔS ≥ 2π nats.
(~50 theorems, 0 sorry, 1 axiom)

**[Super-Causets](CommonResources/Time/SuperCausets/README.md)** 
Causal set theory with the Second Law as ontologically
prior. If entropy is strictly monotone along the causal relation
(x ≺ y ⟹ S(x) < S(y)), then irreflexivity and asymmetry of the causal
order are *theorems*, not axioms. One birth event equals one modular cycle
(2π nats). Three physical requirements force the entropy parameter to be
quaternionic (ℍ), yielding D_spatial = 3 via the Hopf fibration. The
spectral action on the total space U⁹ recovers the Standard Model.
Poisson fluctuations give Λ ∼ 2π/√N. Two `sorry` (both open problems:
Gibbs inequality and the causal set Hauptvermutung). (161 theorems,
2 sorry, 0 axioms)

---

### KnotTheory — Strings, Gauge Theory, and the Hopf Knots

**Strings** — QCD flux tubes as strings with time from modular flow.
From string tension σ > 0: three spatial dimensions with emergent time,
the Lüscher coefficient −π/12 from two transverse modes, a gravitational
hierarchy relation, and time-temperature conjugacy. (~80 theorems,
0 sorry, 0 axioms beyond 3 standard topology facts)

**Yang–Mills / Topological Mass Gap** — The mass gap reframed as a
topological obstruction: the minimum energy of a closed colour-flux
configuration, determined by the gauge group's division-algebraic
structure. Hurwitz's theorem forces exactly three non-trivial gauge
factors: U(1), SU(2), SU(3).

> **Important caveat:** This is a topological reframing, not a proof in
> the Wightman-axiomatic sense required by the Clay Millennium Problem.

(~100 theorems, 0 sorry, 7 axioms including Adams' theorem)

**Knots** *(internal bridges)* — The Hopf Knot proves the complex and
quaternionic Hopf fibrations are one construction under ℂ ↪ ℍ: the
embedding S³ ↪ S⁷ preserves the sphere, the Hopf maps correspond, and
the S¹ fiber actions commute. The Extended Knot continues to 𝕆 and
proves confinement from non-associativity: the type `ColorFactorization`
is uninhabitable. (~55 theorems, 0 sorry, 3 axioms)

---

### HotGravity — Thermodynamic Approaches to Gravity and Measurement

**Entropic Gravity** — Verlinde's entropic gravity program, formalised
and extended. From S = A/(4G) and T = a/(2π), derives Newton's laws,
Einstein's field equations, the Schrödinger equation, and the
Diósi–Penrose collapse timescale. Parametric analysis separates structural
results (any modular period α) from quantitative ones (α = 2π). See the
[Entropic Gravity README](HotGravity/EntropicGravity/README.md) for full
details. (224 theorems, 0 sorry, 0 axioms)

**Loop Quantum Gravity** — A formal skeleton of LQG from SU(2)
representations through the EPRL vertex amplitude. Covers: representation
theory with enforced dimension formulae, quantum tetrahedra with volume
and area operators, spin networks on K₅, spin foam dynamics, modular
theory for boundary states, and the EPRL synthesis. All arithmetic in ℕ
via the encoding twoJ = 2j. Contains universal theorems (area gap, Casimir
injectivity, equal-spin universality) proved for all spins, not
spot-checked. A 27-number numerical fingerprint serves as a compile-time
regression test. See the [LQG README](HotGravity/LoopQuantumGravity/README.md).
(~250 theorems, 0 sorry, 0 axioms)

**Nanothermodynamics** — Proves that Hill's nanothermodynamics (subdivision
potential, Hamiltonian of mean force, anomalous heat capacities,
non-extensive entropy) is restricted modular flow. The translation:
"trace out environment" = restrict to subalgebra; "subdivision potential"
= entropic cost of the algebraic cut. See the [Nanothermodynamics README](HotGravity/NanoThermo/README.md).
(~80 theorems, 0 sorry, 0 axioms)

**Shape Dynamics** — A thermodynamic completion of Barbour–Gomes–Gryb–Koslowski
Shape Dynamics. CMC slicing is thermal equilibrium, York time is
thermodynamic time, temperature interpolates continuously between QM
(T → 0) and classical Shape Dynamics (T → ∞). The Schrödinger equation
is recovered as the zero-temperature limit. See the [Shape Dynamics README](HotGravity/ShapeDynamics/README.md).
(~100 theorems, 0 sorry, 0 axioms)

**Objective Reduction** — The 2π-nat threshold applied to physical
decoherence. Three sub-modules: Diósi–Penrose gravitational decoherence,
chemical measurement theory (Marcus electron transfer, Born–Oppenheimer
as a decoherence-rate inequality), and a bridge proving chemical
decoherence and nanothermodynamic subdivision are the same phenomenon.
See the [Objective Reduction README](HotGravity/ObjectiveReduction/README.md)
(~60 theorems, 0 sorry, 0 axioms)

---

### SpectralTriples — Noncommutative Geometry and the Observerse

**Triples** — The spectral triple on U⁹. KO classification, Clifford
types, Seeley-DeWitt heat kernel expansion with 5 bosonic poles, fiber
bundle decomposition U⁹ = X³ × Sym²₊(ℝ³), Kaluza-Klein mechanism
(gauge curvature emerges from the product geometry, though neither factor
carries gauge curvature alone), S³ spectrum, and coupling constants.  See the [Spectral Triples README](SpectralTriples/README.md)
(~156 theorems, 0 sorry, 2 axioms)

**Geometric Unity** — Two layers of Eric Weinstein's Geometric Unity.
Layer 1: the observerse U⁹ = Tot(Met(X³)) is 9-dimensional, Bott
periodicity gives Cl(9,0) ≅ M₁₆(ℂ), the spinor fibre ℂ¹⁶ accommodates
one generation of SM fermions plus a right-handed neutrino. Layer 2: the
spectral action on U⁹ via Connes' noncommutative geometry, with the
chimeric bundle, shiab operator, and gauge breaking U(16) →
SU(3) × SU(2) × U(1). See the [Geometric Unity README](SpectralTriples/GeometricUnity/README.md). (210+ theorems, 0 sorry, 1 axiom)

**Spectral Bridge** *(internal bridge)* — Term-by-term match between the
spectral action on U⁹ and the Observerse Lagrangian: gravity ↔ a₂,
gauge ↔ a₄, fermions ↔ ½⟨Jψ, Dψ⟩. The correspondence is the unique
dimensionally consistent assignment (of 3! = 6 possible, exactly one
works). (~20 theorems, 0 sorry, 0 axioms)

---

### SplitMechanics — The Subsystem Decomposition

When a pure global state is restricted to a subsystem (partial trace),
the resulting mixed state has a modular operator Δ ≠ 1. Five features
emerge simultaneously — the KMS condition, the Born rule (via GNS),
nontrivial modular flow, unitarity, and spectral invariance — proved to
stand or fall together. Also resolves the foliation problem of Bohmian
mechanics by writing the guiding equation in modular time. (~75 theorems,
0 sorry, 8 axioms)

---

### Bridges — Lateral Connections Between Clusters

Intra-cluster wiring lives inside its cluster. What remains in Bridges/
are genuinely lateral connections between clusters with no shared ancestor
besides CommonResources.

**CProcess** — Connects Objective Reduction and Nanothermodynamics (both
in HotGravity). Chemical decoherence and nanothermodynamic subdivision
are the same phenomenon: at decoherence, I(A:B) = 2π, giving ε = 2πT/N.
Marcus monotonicity is NanoThermo's `subdivision_monotone_in_MI` applied
to chemistry. (~15 theorems, 0 sorry, 0 axioms)

**Gravity Bridges** — Pairwise and triangular compatibility proofs for
LQG, Entropic Gravity, and Shape Dynamics (all in HotGravity). Three
pairwise bridges plus one triangular synthesis proving mutual consistency
across 41 physical postulates with 0 bridge postulates. See the
[Gravity Bridges README](Bridges/Gravity/README.md). (48 theorems,
0 sorry, 0 axioms)

---

## Cluster Dependencies

```
Self-contained clusters (no cross-cluster imports):
  SplitMechanics
  KnotTheory         (internal Knots connect Strings ↔ YangMills)
  HotGravity         (internal Gravity bridges connect submodules)
  SpectralTriples    (internal SpectralBridge connects submodules)

Shared foundation:
  CommonResources    provides DivisionAlgebra, HopfTower, and
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
| Cl(9) ≅ M₁₆(ℂ) from Bott periodicity | Geometric Unity, Spectral Triples, Spectral Bridge, Super-Causets |
| E_grav × τ = ℏ | Shape Dynamics, Objective Reduction, Strings, Entropic Gravity |
| ℍ forced by R1 + R2 + R3 | Strings, Super-Causets |
| D_spatial = 3 from Hopf base | Strings, Super-Causets |

The recurrence is not built in — each module derives from its own starting
point. The recurrence is discovered, not assumed.

---

## Combined Statistics

| Module | Theorems | `sorry` | Axioms |
|--------|:--------:|:-------:|:------:|
| **CommonResources** | | | |
| Thermal Time | ~50 | 0 | 1 |
| Super-Causets | 161 | 2 | 0 |
| **KnotTheory** | | | |
| Strings | ~80 | 0 | 0 |
| Yang–Mills / Mass Gap | ~100 | 0 | 7 |
| Knots (internal bridges) | ~55 | 0 | 3 |
| **HotGravity** | | | |
| Entropic Gravity | 224 | 0 | 0 |
| Loop Quantum Gravity | ~250 | 0 | 0 |
| Nanothermodynamics | ~80 | 0 | 0 |
| Shape Dynamics | ~100 | 0 | 0 |
| Objective Reduction | ~60 | 0 | 0 |
| **SpectralTriples** | | | |
| Triples | ~156 | 0 | 2 |
| Geometric Unity | 210+ | 0 | 1 |
| Spectral Bridge (internal) | ~20 | 0 | 0 |
| **SplitMechanics** | ~75 | 0 | 8 |
| **Bridges** | | | |
| CProcess | ~15 | 0 | 0 |
| Gravity (4 files) | 48 | 0 | 0 |
| **Total** | **~1,684+** | **2** | **22** |

**A note on accounting:** The axiom count (22) reflects true axioms —
irreducible assumptions from operator algebras, algebraic topology, or
Riemannian geometry that Mathlib does not yet cover. Structure fields
(physical postulates like "entropy is monotone along the causal order")
are not counted as axioms — they are the explicit inputs to each module,
visible in the type signature of every theorem that uses them. The
framework is moving towards tracking all postulates carried by each
theorem, providing full transparency on what each result actually assumes.

**A note on counts:** Module theorem counts are approximate (~) and may
shift as code deduplication continues. Shared infrastructure extracted
into CommonResources reduces per-module counts while preserving total
coverage.

---

## What Is and Isn't Claimed

**What the method does:**

It verifies the algebraic and dimensional consistency of a modular-flow
approach to physics across multiple domains. It proves that structures
built independently in separate modules are the same mathematical objects.
It machine-checks every theorem. It separates physical interpretation from
mathematical content explicitly in every module. It carries physical
constants (G, ℏ, k_B, c) explicitly throughout — never silently setting
them to 1.

**What the method does not do:**

It does not construct the full differential-geometric objects (chimeric
connections, fibre integration maps) that would be needed for a complete
formalisation — Mathlib does not yet have the infrastructure. It does not
compute physical predictions (coupling constants, mass ratios, mixing
angles). It does not claim to solve the Clay Millennium Problem. It does
not address the preferred-split problem — the choice of subsystem
decomposition is an input, not derived. And it does not verify physical
interpretations by machine: the proof assistant checks mathematics, not
physics.

The central observation — that modular flow provides a common algebraic
skeleton across these domains — is supported by algebraic evidence. The
algebraic evidence is what the compiler verifies. Whether nature actually
works this way is an empirical question that no amount of type-checking
can answer.

---

## File Structure

```
Superior/
├── CommonResources/
│   ├── DivisionAlgebra/          Basic definitions, quaternions
│   │   ├── Basic.lean
│   │   └── Quaternions.lean
│   ├── HopfTower/                ℝ ↪ ℂ ↪ ℍ ↪ 𝕆 via Cayley-Dickson
│   │   ├── HopfFibration.lean
│   │   ├── HopfTowerKnot.lean
│   │   └── HopfTowerOctonion.lean
│   └── Time/
│       ├── ThermalTime/          Connes–Rovelli, KMS, Ott covariance
│       └── SuperCausets/         Second Law → partial order → ℍ → D=3
│
├── KnotTheory/
│   ├── Strings/                  QCD flux tubes, Lüscher, emergent dimensions
│   ├── YangMills/                Topological mass gap, Hurwitz → gauge factors
│   └── Knots/                    Strings ↔ YangMills (ℂ ↪ ℍ ↪ 𝕆)
│
├── HotGravity/
│   ├── EntropicGravity/          Verlinde → Newton, Einstein, Schrödinger
│   ├── LoopQuantumGravity/       SU(2) reps → spin networks → EPRL vertex
│   ├── NanoThermo/               Hill = modular flow, subdivision potential
│   ├── ObjectiveReduction/       Diósi–Penrose, chemical measurement, 2π
│   └── ShapeDynamics/            QM ↔ classical interpolation, York time
│
├── SpectralTriples/
│   ├── Triples/                  Spectral action, Seeley–DeWitt, spectrum
│   ├── GeometricUnity/           Observerse U⁹, Cl(9) ≅ M₁₆(ℂ), shiab
│   └── SpectralBridge.lean       Triples ↔ GeometricUnity term-by-term
│
├── SplitMechanics/               Subsystem Pentagon, Born = KMS, Bohmian
│
└── Bridges/
    ├── CProcess.lean             ObjectiveReduction ↔ NanoThermo
    └── Gravity/                  LQG ↔ EG ↔ SD pairwise + triangle
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
author (Adam Bornemann). This is an independent project. It has not been
reviewed or endorsed by Erik Verlinde, Ted Jacobson, Alain Connes, Carlo
Rovelli, Julian Barbour, Eric Weinstein, Roger Penrose, Lajos Diósi,
Alain Chamseddine, Lee Smolin, Rafael Sorkin, or any other physicist or
mathematician whose work is referenced.

The goal is to explore what happens when modular flow is taken seriously
as a unifying structure — and to make the algebraic consequences
machine-checkable. Whether this perspective is physically correct is a
question for experiment, not for compilers.

---

## License

MIT. See [LICENSE](../LICENSE).
