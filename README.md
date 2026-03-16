# Logos Library

**Formally verified physics and mathematics in Lean 4 — from quantum mechanics 
to rotating black holes to rough path theory, built on Mathlib.**

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://leanprover.github.io/lean4/doc/)

---

## What This Is

Logos Library is a Lean 4 formalisation built on 
[Mathlib](https://github.com/leanprover-community/mathlib4), spanning physics and 
pure mathematics across ~125,000 lines of Lean in 354 files. The library contains 
4,034 machine-checked proofs, 114 explicit axioms, and 7 `sorry`.

The library has three parts:

- **Core Physics Library** — quantum mechanics, information geometry, general 
  relativity, and quantum computing. The central thread runs from special relativity 
  through Kerr black holes, through a resolution of the Ott–Landsberg debate on 
  relativistic temperature, to a derivation of Einstein's field equations from 
  thermodynamics, and a proof that the Connes–Rovelli thermal time relation is the 
  unique Lorentz-covariant connection between temperature and time.

- **Stochastic Calculus** — a formalisation of rough path theory from first 
  principles: the sewing lemma, Young integration, and rough path integration in 
  the range p ∈ [2,3), heading toward the Universal Limit Theorem. This has never 
  been formalised in any proof assistant.

- **The Superior Method** — a methodology for using Lean's type-checker as a 
  structural comparator across independently formalised domains of physics.


See the [inner README](LogosLibrary/README.md) for detailed statistics, file 
listings, and dependency information.

---


## Core Physics Library

Four modules formalising quantum mechanics, information geometry, relativity, and 
quantum computing. The central thread: a dependency chain from special relativity 
through Kerr black holes, through a resolution of the 60-year Ott–Landsberg debate 
on relativistic temperature, to a derivation of Einstein's field equations from 
thermodynamics, and a proof that the Connes–Rovelli thermal time relation is the 
unique Lorentz-covariant connection between temperature and time. Time dilation 
emerges as a theorem, not a postulate.

| Module | What it covers |
|--------|---------------|
| [**Quantum Mechanics**](LogosLibrary/QuantumMechanics/) | Unbounded operators, Stone's theorem, spectral theorem (3 routes), Schrödinger equation, Bell/CHSH/Tsirelson, Dirac equation, uncertainty relations, unitarity ↔ first law, Tomita–Takesaki modular theory, Connes cocycle, KMS condition, thermal time |
| [**Information Geometry**](LogosLibrary/InformationGeometry/) | Fisher–Rao metric from first principles, score functions, statistical manifolds, Cramér–Rao bound |
| [**Relativity**](LogosLibrary/Relativity/) | Minkowski spacetime, Kerr black holes, Ott transformation (7 independent proofs), Jacobson's thermodynamic derivation of Einstein's equations, Connes–Rovelli thermal time uniqueness, SdS forbidden region (original) |
| [**Quantum Computing**](LogosLibrary/QuantumComputing/) | Thermal Turing machine, Landauer compliance, conditional P ≠ NP from information geometry **(experimental)** |

Each module has its own README with file-by-file descriptions, axiom inventories, 
and dependency information.

### How the Core Modules Connect

```
            Information Geometry                Quantum Mechanics
           +----------------------+         +-----------------------------+
           | Fisher-Rao metric    |         | Stone's theorem             |
           | Statistical manifold |         | Spectral theorem (×3)       |
           | Cramer-Rao bound     |         | Bell / Tsirelson            |
           +-------+------+-------+         | Dirac equation              |
                   |      |                 | Unitarity <-> 1st law       |
                   |      |                 | Tomita-Takesaki / KMS       |
                   |      |                 | Connes cocycle / Ott forced |
                   |      |                 +-------+---------------------+
                   |      |                         |
        +----------+      +----------+              |
        v                            v              v
  Quantum Computing              Relativity
  +------------------+        +---------------------------+
  | Thermal TM       |        | Minkowski spacetime       |
  | Fisher metric on |        | Kerr black holes          |
  |  computation     |        | Ott transformation (x7)   |
  |  paths           |        | Jacobson's derivation     |
  | P != NP          |        | Thermal time uniqueness   |
  |  (conditional)   |        | SdS forbidden region      |
  +------------------+        +---------------------------+

Cross-module imports:
  Info Geometry  → QM:         Cramér–Rao gives a second proof of Heisenberg
  Info Geometry  → QC:         Fisher metric provides the geometric backbone
  QM → Relativity:             Unitarity ↔ first law resolves Ott–Landsberg
  QM → Relativity:             Robertson uncertainty used in SdS instability
  QM → Relativity:             Modular theory / cocycle forces Ott covariance
  Relativity → QM:             Lorentz structure feeds back into Dirac equation
```

---

## Stochastic Calculus

A formalisation of rough path theory from first principles, targeting a complete 
machine-checked proof of the Universal Limit Theorem: the solution map 
**X** ↦ Y^**X** of a rough differential equation is well-defined and continuous 
in the p-variation rough path metric. This has never been formalised in any proof 
assistant.

The development is organised in five stages, each building on the previous:

| Stage | What it covers | Status |
|-------|---------------|--------|
| [**Stage 0**](LogosLibrary/StochasticCalculus/Stage_0/) | Sewing lemma (three layers: interval control, cross-controlled, continuous control). p-variation theory. | Complete |
| [**Stage 1**](LogosLibrary/StochasticCalculus/Stage_1/) | Young integration: the Young–Loève estimate, additivity, uniqueness, regularity, linearity, integration by parts, continuity. | Complete |
| [**Stage 2**](LogosLibrary/StochasticCalculus/Stage_2/) | Truncated tensor algebra, group-like elements, p-rough paths, Gubinelli derivatives, the rough integral, closure theorem, Itô–Lyons continuity estimate. | Complete |
| **Stage 3** | Picard iteration, local and global existence/uniqueness for rough differential equations. | Planned |
| **Stage 4** | The Universal Limit Theorem. | Planned |

Classical stochastic calculus builds integrals from probability — martingale theory, 
filtrations, conditional expectations. Rough path theory takes a different approach: 
enhance the driving signal with sufficient algebraic data and the integral becomes a 
continuous function of the enhanced path. Probability enters only at the end, in 
identifying which enhancement a particular stochastic process selects. Everything 
else is deterministic analysis.

See the [Stochastic Calculus README](LogosLibrary/StochasticCalculus/) for the full 
architecture, dependency flow, and references.


---

## The Superior Method

The Superior Method uses Lean's type-checker as a structural comparator across 
independently formalised domains of physics. Two modules are built in separate 
files with no shared imports. A bridge file then asks: does Lean accept that the 
structure built in Module A is definitionally equal to the structure built in 
Module B? If the bridge compiles, the two domains share algebraic structure. The 
compiler is the comparator.

| Cluster | What it covers |
|---------|---------------|
| [**CommonResources**](LogosLibrary/Superior/CommonResources/) | Shared foundations: Connes–Rovelli thermal time, Super-Causets, division algebras ℝ ↪ ℂ ↪ ℍ ↪ 𝕆, Hopf tower, Clifford periodicity, Fano plane, modular flow |
| [**KnotTheory**](LogosLibrary/Superior/KnotTheory/) | QCD flux tubes, topological mass gap, string theory thermal structure, Hopf knot unification |
| [**HotGravity**](LogosLibrary/Superior/HotGravity/) | Five thermodynamic routes to gravity: entropic gravity, loop quantum gravity, nanothermodynamics, shape dynamics, objective reduction |
| [**SpectralTriples**](LogosLibrary/Superior/SpectralTriples/) | Noncommutative geometry, Geometric Unity and the observerse U⁹, spectral action |
| [**SplitMechanics**](LogosLibrary/Superior/SplitMechanics/) | Subsystem decomposition, Bohmian mechanics, thermal Bell tests, Möbius gears, Riemann zeta via Weil positivity |
| [**EconomicGauge**](LogosLibrary/Superior/EconomicGauge/) | Malaney–Weinstein economic index number problem, gauge-theoretic classification of price distortion |
| [**Bridges**](LogosLibrary/Superior/Bridges/) | Lateral connections across clusters — zero axioms in every bridge file |

See the [Superior README](LogosLibrary/Superior/README.md) for the full 
methodology, architecture, and the organising observation that makes the whole 
thing tick.


## Library Statistics

| | Proofs | Axioms | Sorry | Files |
|---|:---:|:---:|:---:|:---:|
| **Core Physics Library** | | | | |
| Quantum Mechanics | | 59 | 0 | |
| Information Geometry | | 0 | 0 | |
| Relativity | | 7 | 0 | |
| Quantum Computing | | 0 | 4 | |
| **Stochastic Calculus** | | 0 | 1 | |
| **Superior Method** | | 48 | 2 | |
| **Library total** | **4,034** | **114** | **7** | **354** |

124,623 lines of Lean. See the [inner README](LogosLibrary/README.md) for 
per-file breakdowns, and the [axiom audit](docs/axiom_audit.md) for the 
complete axiom catalogue.


## What Is Proven vs. What Is Axiomatised

**Fully machine-checked (no axioms, no sorry):** Minkowski spacetime. Lorentz 
boosts. Robertson, Schrödinger, and Heisenberg uncertainty (twice: algebraic and 
information-geometric). Stone's theorem (both directions). Schrödinger equation as 
a corollary. Bell/CHSH inequality. Tsirelson's bound. Kerr horizon structure, 
ergosphere, ring singularity. Seven independent refutations of Landsberg. 
Uniqueness of Ott's temperature transformation. Uniqueness of the thermal time 
relation. Time dilation as a theorem. Fisher–Rao metric construction. Sewing 
lemma (all three layers). Young integration (existence, uniqueness, regularity, 
linearity, integration by parts). Rough path integration with Itô–Lyons 
continuity. All Superior bridge files.

**Axiomatised (standard results not yet formalisable in Lean):** Bochner's theorem. 
Dominated convergence applications. Adams' theorem on Hopf invariant one. Various 
spectral integration results requiring measure theory on infinite-dimensional 
spaces. These are textbook results whose formal proofs require infrastructure 
Mathlib does not yet provide. See the [axiom audit](docs/axiom_audit.md) for the 
full list — every axiom names a specific result.

**Experimental:** The P ≠ NP development in Quantum Computing is conditional: *if* 
the SAT phase transition creates an information-geometric bottleneck for sequential 
local computation, *then* P ≠ NP.


## Design Decisions

**Unbounded operators, honestly.** `UnboundedObservable H` models quantum 
observables as genuinely partial functions. You cannot apply an operator to a 
vector without proving it lives in the domain. This is more work than pretending 
everything is bounded. It is also correct.

**Physics axioms are features, not bugs.** The axioms are not gaps in proofs — 
they are the physical content. A formalisation of physics must distinguish 
mathematical theorems (which the machine checks) from physical postulates (which 
the machine takes as given). Making these assumptions visible and auditable is the 
entire point.

**Multiple proof routes.** Heisenberg is proved twice. The spectral theorem is 
constructed via three routes proved to agree. Relativistic thermodynamics is 
approached from two directions. When different branches of mathematics produce the 
same result through different architectures, the agreement is evidence.

**Independent construction, then bridging.** The Superior modules are built without 
importing each other. Structural coincidence is discovered by bridge files, not 
assumed by shared imports. The bridges contain zero axioms.

**Expository source files.** Several modules interleave Lean code with physical 
motivation, historical context, and pedagogical explanation. The intent is that 
these files serve as self-contained introductions to the physics for anyone with a 
working knowledge of Lean.


## Quick Start

```bash
# Clone
git clone https://gitlab.com/pedagogical/logos_library
cd Logos_Library

# Install Lean 4 (if needed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Fetch Mathlib cache
lake exe cache get

# Build everything (first build takes a while; 16 GB RAM recommended)
lake build

# Or build individual modules
lake build LogosLibrary.QuantumMechanics
lake build LogosLibrary.Relativity
lake build LogosLibrary.StochasticCalculus
lake build Superior
```


## References

Each module README contains full references. The primary sources:

- M. Reed, B. Simon, *Methods of Modern Mathematical Physics I*, Academic Press, 1980.
- K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer, 2012.
- B. C. Hall, *Quantum Theory for Mathematicians*, Springer, 2013.
- M. Takesaki, *Theory of Operator Algebras I–III*, Springer, 1979–2003.
- S. Amari, *Information Geometry and Its Applications*, Springer, 2016.
- T. Jacobson, "Thermodynamics of Spacetime," *Phys. Rev. Lett.* 75, 1260–1263, 1995.
- A. Connes, C. Rovelli, "Von Neumann algebra automorphisms and time-thermodynamics relation," *Class. Quantum Grav.* 11, 2899–2917, 1994.
- P. Friz, M. Hairer, *A Course on Rough Paths*, 2nd ed., Springer, 2020.
- T. Lyons, "Differential equations driven by rough signals," *Rev. Mat. Iberoam.* 14, 215–310, 1998.


## Author

Adam Bornemann — [AdamBornemann@gmail.com](mailto:AdamBornemann@gmail.com)

## License

MIT. See [LICENSE](LICENSE).

## Acknowledgements

Built with [Lean 4](https://leanprover.github.io/lean4/doc/) and 
[Mathlib](https://github.com/leanprover-community/mathlib4). The Bell's theorem 
development is ported from Echenim and Mhalla's Isabelle/HOL formalisation with 
proper attribution and substantial extension.


