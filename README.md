# Logos Library

**Formally verified physics in Lean 4 — from Minkowski spacetime to rotating black holes to the thermodynamic origin of time, and a machine-checked methodology for discovering structural coincidences across physics.**

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://leanprover.github.io/lean4/doc/)

---

## What This Is

Logos Library is a Lean 4 formalisation of physics built on [Mathlib](https://github.com/leanprover-community/mathlib4). The library contains ~109,000 lines of Lean across two interlocking parts:

**Part I — Core Physics Library.** Four modules formalising quantum mechanics, information geometry, relativity, and quantum computing. ~48,000 lines. Every theorem is machine-checked; every physical assumption is an explicit `axiom` with a name you can grep for. The central thread: a dependency chain from special relativity through the Kerr metric for rotating black holes, through a resolution of the 60-year Ott–Landsberg debate on relativistic temperature, to a derivation of Einstein's field equations from thermodynamics, and finally to a proof that the Connes–Rovelli thermal time relation is the *unique* Lorentz-covariant connection between temperature and time. Time dilation emerges as a theorem, not a postulate.

**Part II — The Superior Method.** A methodology for using Lean's type-checker as a structural comparator across physics. Seventeen sub-modules — spanning QCD flux tubes, loop quantum gravity, entropic gravity, noncommutative geometry, causal set theory, and more — are formalised independently, then connected by bridge files that ask: does Lean accept that the structure built in Module A is definitionally equal to the structure built in Module B? If the bridge compiles, the two domains share algebraic structure. If it doesn't, they don't. The compiler is the comparator. ~1,684 theorems, 2 `sorry` (both genuine open problems), 22 axioms across the full framework.

This is a formalisation of *physics*, not only of mathematics. The axioms are not deficiencies — they mark exactly where mathematics ends and physics begins. Every axiom names a physical principle whose proof would require infrastructure not yet available in Lean or Mathlib. The library makes these assumptions visible and auditable in a way that no informal physics paper can.


## Part I — Core Physics Library

| Module | Lines | Axioms | Sorry | What it does |
|--------|------:|-------:|------:|--------------|
| [**Quantum Mechanics**](LogosLibrary/QuantumMechanics/) | ~26,000 | 69 | 0 | Unbounded operators, Stone's theorem, spectral theorem (3 routes), Schrödinger equation, Bell/CHSH/Tsirelson, Dirac equation, uncertainty relations (Robertson, Schrödinger, Heisenberg ×2), unitarity ↔ first law, Tomita–Takesaki modular theory, Connes cocycle, KMS condition, thermal time |
| [**Information Geometry**](LogosLibrary/InformationGeometry/) | ~2,000 | 0 | 0 | Fisher–Rao metric from first principles, score functions, statistical manifolds, Cramér–Rao bound |
| [**Relativity**](LogosLibrary/Relativity/) | ~12,800 | ~14 | 0 | Minkowski spacetime, Kerr black holes, Ott transformation (7 independent proofs), Jacobson's derivation, Connes–Rovelli thermal time uniqueness, SdS instability (original) |
| [**Quantum Computing**](LogosLibrary/QuantumComputing/) | ~7,000 | 8 | 4 | Thermal Turing machine, conditional P ≠ NP from information geometry **(experimental)** |

Each module has its own detailed README with file-by-file descriptions, axiom inventories, and dependency graphs.

**On the first ~12,000 lines of QM:** These contain zero axioms beyond Lean's kernel and Mathlib. That covers the full uncertainty relation hierarchy, Stone's theorem in both directions, and Bell's theorem — proved from nothing but the axioms of dependent type theory and whatever Mathlib provides. The 69 axioms enter only when you hit spectral measure construction, PDE machinery, and modular theory, overwhelmingly asserting standard results from measure theory and harmonic analysis that Mathlib does not yet cover.

**On line counts:** The Relativity and Quantum Computing files interleave Lean code with physical motivation, historical context, and pedagogical explanation. They are intended to be readable as self-contained introductions to the physics, not merely as machine-checkable artefacts. The proof content is a fraction of the stated line count in those sections. The Quantum Mechanics and Information Geometry sections are leaner.


### How the Core Modules Connect

```
            Information Geometry                Quantum Mechanics
           +----------------------+         +----------------------------+
           | Fisher-Rao metric    |         | Stone's theorem            |
           | Statistical manifold |         | Spectral theorem (×3)      |
           | Cramer-Rao bound     |         | Bell / Tsirelson           |
           +-------+------+-------+         | Dirac equation             |
                   |      |                 | Unitarity <-> 1st law      |
                   |      |                 | Tomita-Takesaki / KMS      |
                   |      |                 | Connes cocycle / Ott forced |
                   |      |                 +-------+--------------------+
                   |      |                         |
        +----------+      +----------+              |
        v                            v              v
  Quantum Computing              Relativity
  +------------------+        +--------------------------+
  | Thermal TM       |        | Minkowski spacetime       |
  | Fisher metric on |        | Kerr black holes          |
  |  computation     |        | Ott transformation (x7)   |
  |  paths           |        | Jacobson's derivation     |
  | P != NP          |        | Thermal time uniqueness   |
  |  (conditional)   |        | SdS instability (original)|
  +------------------+        +--------------------------+

Cross-module imports:
  * Info Geometry -> QM:     Cramer-Rao gives a second proof of Heisenberg
  * Info Geometry -> QC:     Fisher metric provides the geometric backbone
  * QM -> Relativity:        Unitarity <-> 1st law resolves Ott-Landsberg
  * QM -> Relativity:        Robertson uncertainty used in SdS instability
  * QM -> Relativity:        Modular theory / cocycle forces Ott covariance
  * Relativity -> QM:        Lorentz structure feeds back into Dirac equation
```


## Part II — The Superior Method

The Superior Method uses Curry–Howard as an experimental instrument. The idea:

1. Formalise a domain of physics in Lean 4, with every physical assumption as an explicit named structure field.
2. Formalise a second domain independently — different file, different starting assumptions, no imports between them.
3. Write a bridge file. Ask: does Lean's type-checker accept that the structure built in Module A is *definitionally equal* to the structure built in Module B?

If the bridge compiles, the two domains share algebraic structure. If it doesn't, they don't. Structural coincidence becomes a checkable fact rather than a hand-wavy analogy.

**What is verified:** Algebraic and dimensional consistency. Every theorem is machine-checked. Every physical assumption is an explicit, named structure field. There are no hidden gaps.

**What is not verified:** Physical truth. The compiler checks mathematics, not physics. Whether the structures that recur across modules reflect something about nature is an empirical question.

See the [Superior README](Superior/README.md) for the full methodology, architecture, and cluster descriptions.


### Superior — Cluster Overview

| Cluster | Modules | Theorems | Sorry | Axioms | What it covers |
|---------|---------|:--------:|:-----:|:------:|----------------|
| [**CommonResources**](Superior/CommonResources/) | Thermal Time, Super-Causets, Division Algebras, Hopf Tower | ~211 | 2 | 1 | Shared foundations: Connes–Rovelli, Second Law → causal order, ℝ ↪ ℂ ↪ ℍ ↪ 𝕆 |
| [**KnotTheory**](Superior/KnotTheory/) | Strings, Yang–Mills, Knots | ~235 | 0 | 10 | QCD flux tubes, topological mass gap, Hopf knot unification |
| [**HotGravity**](Superior/HotGravity/) | Entropic Gravity, LQG, NanoThermo, Shape Dynamics, Objective Reduction | ~714 | 0 | 0 | Five thermodynamic routes to gravity and measurement |
| [**SpectralTriples**](Superior/SpectralTriples/) | Triples, Geometric Unity, Spectral Bridge | ~386 | 0 | 3 | Noncommutative geometry, the observerse U⁹, spectral action |
| [**SplitMechanics**](Superior/SplitMechanics/) | — | ~75 | 0 | 8 | Subsystem decomposition: Born rule = KMS, modular Bohm |
| [**Bridges**](Superior/Bridges/) | CProcess, Gravity (×4) | ~63 | 0 | 0 | Lateral connections across clusters |
| **Total** | | **~1,684** | **2** | **22** | |

The two `sorry` are in Super-Causets and correspond to the Gibbs inequality and the causal set Hauptvermutung — both genuine open problems in the literature.


### The Organising Observation

The modular automorphism group of a faithful state on a von Neumann algebra — the mathematical core of Tomita–Takesaki — appears independently across modules:

| Structure | Where it appears independently |
|-----------|-------------------------------|
| 2π nats = one modular cycle | Thermal Time, NanoThermo, Objective Reduction, Shape Dynamics, Split Mechanics, Entropic Gravity, LQG, Super-Causets |
| Ott transformation T → γT | Thermal Time (×7), Strings, NanoThermo, Shape Dynamics, Entropic Gravity, Super-Causets |
| K = H/T Lorentz-invariant | Thermal Time, Strings, NanoThermo, Split Mechanics, Super-Causets |
| Cl(9) ≅ M₁₆(ℂ) from Bott periodicity | Geometric Unity, Spectral Triples, Spectral Bridge, Super-Causets |
| D_spatial = 3 from Hopf base | Strings, Super-Causets |

Each module derives these from its own starting point. The recurrence is discovered by bridge files, not assumed by shared imports.


## Combined Statistics

| | Theorems | Sorry | Axioms | Lines |
|---|:---:|:---:|:---:|---:|
| **Core Physics Library** | | 4 | ~91 | ~48,000 |
| Quantum Mechanics | | 0 | 69 | ~26,000 |
| Information Geometry | | 0 | 0 | ~2,000 |
| Relativity | | 0 | ~14 | ~12,800 |
| Quantum Computing | | 4 | 8 | ~7,000 |
| **Superior Method** | ~1,684 | 2 | 22 | ~62,000 |
| **Library total** | | **6** | **~113** | **~109,000** |

**On axioms:** Every axiom names a specific mathematical result (Bochner's theorem, dominated convergence, Adams' theorem) or a specific physical principle (the thermal time ansatz, Landauer's bound, the Bekenstein–Hawking area law). Structure fields — explicit physical postulates like "entropy is monotone along the causal order" — are not counted as axioms; they are visible in the type signature of every theorem that uses them.

**On sorry:** The 4 in Quantum Computing mark an experimental, conditional argument (P ≠ NP from information geometry). The 2 in Super-Causets mark genuine open problems. Every other theorem in the library is complete.


## What Is Proven vs. What Is Axiomatised

**Fully machine-checked (no axioms, no sorry):** Minkowski spacetime. Lorentz boosts. Causal trichotomy. Robertson, Schrödinger, and Heisenberg uncertainty (twice: algebraic and information-geometric). Stone's theorem (both directions). Schrödinger equation as a corollary. Bell/CHSH inequality. Tsirelson's bound (tight in both directions). Kerr horizon structure, ergosphere, ring singularity characterisation. Seven independent refutations of Landsberg. Uniqueness of Ott's temperature transformation from Clausius preservation. Uniqueness of the thermal time relation. Time dilation as a theorem. Thermal Turing machine core. Landauer compliance. Fisher–Rao metric construction. Entropic gravity (Newton, Einstein, Schrödinger from holographic postulates). Loop quantum gravity (SU(2) representations through EPRL vertex). Nanothermodynamics as restricted modular flow. Shape dynamics with QM–classical interpolation. The spectral action on U⁹. All Superior bridge files (0 axioms across all bridges).

**Axiomatised (physically standard, not yet formalisable in Lean):** Bochner's theorem. Dominated convergence applications. The Raychaudhuri equation. The Bekenstein–Hawking area law. Entropy invariance under Lorentz transformations. The thermal time ansatz. Adams' theorem on Hopf invariant one. Closability from dense adjoint (Reed–Simon VIII.1). These are textbook results or well-established physical principles whose formal proofs require measure theory on infinite-dimensional spaces, differential geometry, algebraic topology, or PDE infrastructure that Mathlib does not yet provide.

**Under construction:** Modular theory is proved through the Connes cocycle identity; KMS discharge (proving the vacuum state satisfies the KMS condition as a theorem rather than a hypothesis) is the next target. Several bundled structure hypotheses in the Tomita–Takesaki development are intended for discharge as the spectral calculus matures.

**Experimental (conditional, axioms open):** The P ≠ NP development in Quantum Computing. This is a conditional proof: *if* the SAT phase transition creates an information-geometric bottleneck for sequential local computation, *then* P ≠ NP. See the [Quantum Computing README](LogosLibrary/QuantumComputing/) for full details.


## Design Decisions

**Unbounded operators, honestly.** The type `UnboundedObservable H` models quantum observables as genuinely partial functions with `Submodule ℂ H` domains. You cannot apply an operator to a vector without proving it lives in the domain. Computing a commutator `[A,B]ψ` requires four domain membership proofs, bundled in `DomainConditions`. This is more work than pretending everything is bounded. It is also correct.

**Physics axioms are features, not bugs.** A formalisation of physics must distinguish between mathematical theorems (which the machine checks) and physical postulates (which the machine takes as axioms). The axioms in this library are not gaps in proofs — they are the *physical content*. Flagging them explicitly is the entire point.

**Multiple proof routes.** Heisenberg is proved twice (Cauchy–Schwarz and Cramér–Rao). The spectral theorem is constructed via three independent routes proved to agree. Relativistic thermodynamics is approached from two directions: spectral theory (unitarity ↔ first law) and modular theory (Connes cocycle forces Ott). When different branches of mathematics produce the same result through different architectures, the agreement is evidence that the abstractions are sound.

**Independent construction, then bridging.** The Superior modules are built without importing each other. When two modules produce the same structure, this is *discovered* by a bridge file, not *assumed* by shared imports. The bridge files contain zero axioms — every identification is a theorem.

**Expository source files.** The Relativity, Quantum Computing, and several Superior modules interleave Lean code with physical motivation, historical context, and pedagogical explanation. Whether you find this helpful or maddening is a matter of taste, but the intent is that these files serve as self-contained introductions to the physics for anyone with a working knowledge of Lean.


## Why Formalise Physics?

Most formalisation efforts target pure mathematics — and for good reason. Pure mathematics has no axioms beyond the foundational system, so a complete formalisation is a complete verification. Physics is different: at some point you must assert that entropy counts microstates, or that thermal equilibrium exists, or that Landauer's bound holds. No amount of type theory will derive these from first principles.

The value of formalising physics is twofold.

**First: the machine forces you to say exactly what you assume.** Every informal physics paper implicitly assumes dozens of things — Lorentz invariance, thermodynamic equilibrium, the existence of well-defined temperatures — and buries them in phrases like "it is well known that" or "we may assume without loss of generality." A proof assistant does not accept hand-waving. The result is a document that separates the mathematical content (which is verified) from the physical content (which is explicit) with a precision that no informal paper can match.

**Second: the machine can discover structural coincidences.** When two domains of physics are formalised independently and a bridge file compiles, proving their output structures are definitionally equal, you have learned something that would be extraordinarily difficult to establish informally. The identification is not a claim about physics — it is a machine-checked fact about the algebraic structure of the two formalisations. Whether nature respects that algebraic structure is a question for experiment. But the algebraic fact is exact, and it is verified.


## Quick Start

```bash
# Clone
git clone https://github.com/adambornemann-glitch/Logos_Library.git
cd Logos_Library

# Install Lean 4 (if needed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Fetch Mathlib cache (saves a long build)
lake exe cache get

# Build everything
# Note: First build takes a while
lake build

# Or build individual modules
lake build LogosLibrary.QuantumMechanics
lake build LogosLibrary.InformationGeometry
lake build LogosLibrary.Relativity
lake build LogosLibrary.QuantumComputing
lake build Superior
```

**Requirements:** Lean 4 (version pinned in `lean-toolchain`), Mathlib4 (commit pinned in `lakefile.lean`). At least 16 GB RAM recommended; 8 GB is the practical minimum.


## References

Each module and sub-module README contains full references. The primary sources for the core library:

- M. Reed, B. Simon, *Methods of Modern Mathematical Physics I*, Academic Press, 1980.
- K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer, 2012.
- B. C. Hall, *Quantum Theory for Mathematicians*, Springer, 2013.
- M. Takesaki, *Theory of Operator Algebras I–III*, Springer, 1979–2003.
- S. Amari, *Information Geometry and Its Applications*, Springer, 2016.
- M. Echenim, M. Mhalla, "A formalization of the CHSH inequality and Tsirelson's upper-bound in Isabelle/HOL", 2023.
- H. Ott, "Lorentz-Transformation der Wärme und der Temperatur," *Z. Physik* 175, 70–104, 1963.
- T. Jacobson, "Thermodynamics of Spacetime," *Phys. Rev. Lett.* 75, 1260–1263, 1995.
- A. Connes, C. Rovelli, "Von Neumann algebra automorphisms and time-thermodynamics relation," *Class. Quantum Grav.* 11, 2899–2917, 1994.
- A. Connes, *Noncommutative Geometry*, Academic Press, 1994.
- E. Verlinde, "On the origin of gravity and the laws of Newton," *JHEP* 2011:029, 2011.


## Author

Adam Bornemann — [AdamBornemann@gmail.com](mailto:AdamBornemann@gmail.com)

## License

MIT. See [LICENSE](LICENSE).

## Acknowledgements

Built with [Lean 4](https://leanprover.github.io/lean4/doc/) and [Mathlib](https://github.com/leanprover-community/mathlib4). The Bell's theorem development is ported from Echenim and Mhalla's Isabelle/HOL formalisation with proper attribution and substantial extension.
