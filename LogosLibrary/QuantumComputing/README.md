# Quantum Computing

**The most experimental section of the Logos Library.**

## Fair Warning

Everything else in this library — the units, the pedagogy, the deep theorems in spectral theory and quantum mechanics, the epistemic detectors — is built to the standard you'd expect from a formally verified codebase: definitions are correct, theorems are machine-checked, sorry counts are low and documented.

This section is different. It is where the library reaches past what is known and tries to grab hold of what might be true. The Thermal Turing Machine is solid engineering with clean definitions and sorry-free theorems. The P ≠ NP development is a conditional result resting on physically motivated axioms that have not yet been discharged. The bridge files connecting them are explicitly exploratory.

If you are reading this library to learn what formal verification can do for established mathematics, start elsewhere. If you are reading it to see what happens when you point a theorem prover at open problems in theoretical computer science and let it tell you where your arguments break, you are in the right place.

The formalization has already earned its keep: the original P ≠ NP axiom system was **inconsistent** — the type checker caught a contradiction between an assumed exponential Fisher–Rao distance and a proved constant upper bound on the diameter of the simplex. The corrected argument (restricted path length, not endpoint distance) is a better mathematical idea, and it was found because Lean refused to accept the worse one. That alone justifies the approach.

Nothing here should be mistaken for a claimed proof of P ≠ NP. It is a framework, a set of conditional results, and an ongoing investigation.


## What Lives Here

```
QuantumComputing/
├── ThermalTuringMachine/        ← Computation with thermodynamic accounting
│   ├── Core.lean                   Definitions, Landauer compliance, KMS grounding
│   ├── Lemmas.lean                 Structural lemmas
│   ├── OneBit.lean                 Concrete machines, complexity classes
│   ├── Simple.lean                 One-Bit Bridge, Part 1
│   ├── Simplex.lean                One-Bit Bridge, Part 2
│   └── README.md
│
├── PvNP/                        ← P ≠ NP from information geometry
│   ├── CostBlind.lean              Cost-blind TM symmetry
│   ├── ComputationEmbedding.lean   Fisher–Rao metric on computation paths
│   ├── SymmetryBreaking.lean       Fisher metric breaks cost-blind symmetry
│   ├── PhaseTransition.lean        Restricted path barrier at SAT transition
│   ├── LocalityBound.lean          TM locality + final assembly
│   └── README.md
│
└── README.md                    ← You are here
```


## The Two Developments

### 1. Thermal Turing Machine

A standard Turing machine augmented with a thermal reservoir at inverse temperature β, a per-transition dissipation function, and a structural invariant: every logically irreversible step dissipates at least kT ln 2 of energy (Landauer's principle). Reversible computations are vacuously compliant (Bennett's principle). The temperature is grounded by the KMS condition on a C\*-algebraic system, not postulated.

This is the foundation. It is sorry-free in the core files and provides the per-step thermodynamic cost that the P ≠ NP argument needs.

**Key results (all machine-checked, no sorry):**

- Landauer compliance forces irreversible erasers to pay T ln 2
- Bennett's principle: reversible TMs are vacuously Landauer-compliant
- Total dissipation ≥ (irreversible steps) × T ln 2 over any execution trace
- KMS grounding ties β to actual thermal equilibrium
- Concrete machines (trivial, bit-flipper, eraser) validate the framework

### 2. P ≠ NP from Information Geometry

A conditional proof that P ≠ NP, structured as: if the SAT phase transition creates an information-geometric bottleneck for sequential local computation, then no polynomial-time algorithm can solve SAT. The argument proceeds in five steps:

1. **Cost-blind symmetry**: standard TMs have too much symmetry to carry complexity content
2. **Computation embedding**: every computation traces a path on the probability simplex with a well-defined Fisher–Rao length
3. **Symmetry breaking**: the Fisher metric is canonical (Chentsov) and distributional, breaking cost-blind symmetry
4. **Phase transition barrier**: near the SAT transition, locally-constrained paths must accumulate exponential thermodynamic length
5. **Locality bound**: TM steps have bounded Fisher displacement; combining with the barrier gives an exponential step lower bound

The logical chain from axioms to conclusion is machine-checked (2 sorry, neither in the critical path). The hard content lives in 8 named axioms, documented in an explicit manifest with discharge routes.

**The corrected argument** (v2): The endpoint Fisher–Rao distance is bounded by π (proved). The barrier is not that the destination is far away — it is that a Turing machine cannot follow the geodesic because its steps are local pushforwards nearly orthogonal to the geodesic direction near the phase transition. The machine is forced through an exponential detour.


## How They Connect

The two developments are complementary and partially linked:

```
                    Thermal Turing Machine
                    ─────────────────────
                    Per-step cost: each irreversible
                    transition dissipates ≥ kT ln 2
                            │
                            │  "How much does each step cost?"
                            │
                            ▼
                    ┌───────────────────┐
                    │   One-Bit Bridge  │  ← exploratory, connects the towers
                    │   (Simple.lean,   │
                    │    Simplex.lean)  │
                    └───────────────────┘
                            │
                            │  "How many steps do you need?"
                            │
                            ▼
                    P ≠ NP from Info Geometry
                    ─────────────────────────
                    Step count: locally-constrained paths
                    through the SAT transition require
                    exponentially many steps
```

The TTM answers: **what does each computational step cost?**
The P ≠ NP stack answers: **how many steps does a solver need?**
The bridge asks: **can we combine them into a total thermodynamic cost bound?**

The bridge files (Simple.lean, Simplex.lean) are the first investigation of this connection. Their honest finding: the Landauer cost per step and the Fisher geometric step count measure different things and are not directly proportional. The relationship is a three-layer composition — Fisher geometry bounds step count, Landauer bounds cost per step, and the composition bounds total cost. This is more subtle and more informative than "dissipation = T × distance."

The TTM also provides the `ThermalP`, `ThermalNP`, `ThermalDecider`, and `ThermalVerifier` definitions — thermodynamic complexity classes that the P ≠ NP stack could eventually target. These are well-typed definitions, not theorems, but they set the stage.


## Sorry Inventory

| Subdirectory | File | Count | Statement | Severity |
|---|---|---|---|---|
| TTM | Core.lean | 0 | — | — |
| TTM | Lemmas.lean | 0 | — | — |
| TTM | OneBit.lean | 0 | — | — |
| TTM | Simple.lean | 0 | — | — |
| TTM | Simplex.lean | 2 | Gibbs' inequality; π/2 > ln 2 | Low |
| PvNP | CostBlind.lean | 0 | — | — |
| PvNP | ComputationEmbedding.lean | 1 | Spherical triangle inequality | Medium |
| PvNP | SymmetryBreaking.lean | 1 | Point mass construction on Fintype | Low |
| PvNP | PhaseTransition.lean | 0 | — | — |
| PvNP | LocalityBound.lean | 0 | — | — |

**Total: 4 sorry across ~2,500+ lines.** None are in the critical proof chain of either development.

The P ≠ NP development additionally rests on 8 named axioms (fields of Lean structures), documented in a manifest. These are the load-bearing assumptions. They are not sorry — they are explicitly axiomatised content with identified discharge routes.


## Dependencies

Both developments depend on the broader Logos Library:

- **ThermalTuringMachine** imports from `LogosLibrary.Superior.ThermalTime.InfoTheory` (Landauer cost, nats-per-bit) and `LogosLibrary.QuantumMechanics.ModularTheory.KMS.Condition` (KMS states on C\*-algebras)
- **PvNP** imports from the Information Geometry library (`StatisticalModel`, `FisherInformation`, `FisherMetric`, `CramerRao`)
- Both import extensively from Mathlib (Analysis, MeasureTheory, Topology, Tactic)

The bridge files (Simple.lean, Simplex.lean) are partially self-contained — they redefine some constants locally for exploration and import only Mathlib. This is intentional for rapid iteration but should be unified before integration into the main build.


## Maturity Assessment

| Component | Maturity | Description |
|---|---|---|
| TTM Core + Lemmas | **Solid** | Clean definitions, sorry-free, good lemma coverage |
| TTM Concrete machines | **Solid** | Eraser test is a genuine validation of the framework |
| TTM Complexity classes | **Definitions only** | Well-typed but no separation theorems |
| TTM Bridge files | **Exploratory** | Honest findings, 2 sorry, constants need unification |
| PvNP logical chain | **Conditional** | Machine-checked from axioms to conclusion |
| PvNP axiom discharge | **Open** | 8 axioms with identified routes, none yet discharged |
| PvNP Curie–Weiss | **Proof of concept** | Correctly predicts polynomial (not exponential) for easy problems |
| Integration (TTM ↔ PvNP) | **Early** | Bridge files are first steps; full integration is future work |


## What This Section Is Not

This is not a proof of P ≠ NP. The complexity theory community will correctly observe that the hard content lives in the axioms, particularly the restricted path barrier (Axiom 1), and that discharging those axioms requires formalizing substantial chunks of random k-SAT phase transition theory at Ding–Sly–Sun-level difficulty.

This is not a completed theory of thermodynamic computation. The TTM lacks output extraction, space complexity, and composition — all needed for a full complexity theory.

This is not finished. It is the most actively developed and least stable part of the library.

## What This Section Is

It is a formally verified framework for asking whether thermodynamic constraints on physical computation have anything to say about P versus NP. The framework has already caught one inconsistency in its own axioms and produced a corrected argument that is mathematically stronger than the original. The TTM provides clean, sorry-free infrastructure for reasoning about the thermodynamic cost of computation. The P ≠ NP stack provides a conditional result with an explicit axiom manifest.

The formalisation does what formalisation is supposed to do: it tells you exactly what you've assumed, exactly what you've proved, and exactly where the gaps are. The gaps are documented. The assumptions are named. The proofs are machine-checked.

Whether the axioms are true is a question for physics and combinatorics, not for the type checker. But the type checker has already done its job: it has shown that **if** they are true, **then** P ≠ NP follows by pure logic. And it has caught at least one case where a plausible-sounding axiom was, in fact, nonsense.

That is the value of formalisation applied to open problems. Not certainty — clarity.


## Building

```bash
# From the Logos Library root:

# Thermal Turing Machine
lake build LogosLibrary.QuantumComputing.ThermalTuringMachine.Core
lake build LogosLibrary.QuantumComputing.ThermalTuringMachine.Lemmas
lake build LogosLibrary.QuantumComputing.ThermalTuringMachine.OneBit

# P ≠ NP
lake build LogosLibrary.QuantumComputing.PvNP.CostBlind
lake build LogosLibrary.QuantumComputing.PvNP.ComputationEmbedding
lake build LogosLibrary.QuantumComputing.PvNP.SymmetryBreaking
lake build LogosLibrary.QuantumComputing.PvNP.PhaseTransition
lake build LogosLibrary.QuantumComputing.PvNP.LocalityBound

# Bridge files (self-contained, Mathlib only)
lake build LogosLibrary.QuantumComputing.ThermalTuringMachine.Simple
lake build LogosLibrary.QuantumComputing.ThermalTuringMachine.Simplex
```


## A Note on Experimental Work in Formal Verification

There is a widespread assumption that formal verification is only useful for established mathematics — that you should formalise theorems you already know are true. This section is a deliberate test of the opposite proposition: that formal verification is *most* useful when you don't know whether your argument is correct, because the type checker will find your mistakes faster and more reliably than any human referee.

The original P ≠ NP axiom system was inconsistent. A human reviewer might have missed this — the contradiction required combining a theorem proved in one file with an axiom stated in another, and the exponential-vs-constant comparison is easy to overlook when you're thinking about phase transitions. The type checker cannot overlook it. It doesn't get tired, it doesn't get excited about the conclusion, and it doesn't skip the boring parts.

If you are going to be wrong, be wrong in Lean. At least you'll find out.
