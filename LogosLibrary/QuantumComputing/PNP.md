# P vs NP Through the Lens of Entromechanics

## A Discussion Framework

**Author:** Doctor Professor Baron von Wobble-Bob, with Ryan Williams (as channeled)  
**Date:** February 2026  
**Status:** Battle map and tea — early strategic reconnaissance

---

## 1. The Standard Problem, Restated

P vs NP asks whether every problem whose solution can be *verified* in polynomial time can also be *solved* in polynomial time. Standard complexity theory treats this as a purely mathematical question about the existence of algorithms. The question is model-independent (up to polynomial factors) and carries no reference to physics, thermodynamics, or the cost of computation as a physical process.

Current status (per Williams, 80% confidence P ≠ NP):

- We can prove P ≠ NP for every *restricted* computational model we've studied — monotone circuits, bounded-depth circuits (AC⁰), ACC circuits.
- The moment we move to *unrestricted* Boolean circuits, all known proof techniques hit barriers: relativization, natural proofs, algebrization.
- These barriers show that our proof methods have too much *slack* — they operate at a level of abstraction that can't distinguish the real computational model from modified versions where P = NP holds artificially.

**The entromechanical hypothesis:** This slack is not a deficiency of proof technique. It is a consequence of having *abstracted away the physics*. The standard TM, with its infinite free tape and cost-free transitions, is a model that has been deliberately stripped of every physical constraint that might provide the leverage needed for a separation.

---

## 2. The Thermal Turing Machine as Assembly + Entropy Accounting

The TTM (formalized in Lean 4) is not a new complexity theory. It sits *below* complexity theory. It is the accounting ledger.

**Architecture:**
- Standard deterministic TM (tape, head, states, transition function)
- Coupled to a thermal reservoir at inverse temperature β > 0
- Per-transition dissipation function: each step has a heat cost
- Second law enforced structurally: dissipation ≥ 0
- KMS grounding: β is not a free parameter but is fixed by the KMS condition on the reservoir's equilibrium state

**Key formal results (Lean-verified):**
- `landauer_total_bound`: Total dissipation over any trace ≥ (number of irreversible steps) × kT ln 2
- `reversible_is_landauer_compliant`: Reversible TMs are vacuously Landauer-compliant (Bennett 1973)
- `reversible_computation_free`: Any reversible TM can run at zero dissipation
- `irreversible_step_entropy_bound`: Each irreversible step produces ≥ ln 2 nats of entropy

**The point:** Complexity theory asks "how many steps?" The TTM asks "how many steps, how many erasures, and what did each one cost?" The granularity is deliberate. Landauer's principle is per-operation, not per-algorithm. Aggregating to asymptotic scaling may discard exactly the structure that matters.

---

## 3. The Non-Unitary Hypothesis

### 3.1 Derivation vs. Derivation + Decompression

Core observation from the periodic table problem: the Schrödinger equation alone cannot produce the full periodic table. The 3-body problem (and worse, N-body) prevents closed-form derivation. However, using experimentally measured ionization energies + angular momentum quantum numbers as *auxiliary input*, the table becomes tractable.

**Where did the auxiliary information come from?** Someone performed a physical measurement. They collapsed a wavefunction. They paid entropy. They ran the E Process on an actual atom. That information was *not derivable* from the starting axioms. It came from outside. It was non-unitary.

### 3.2 Mapping to Complexity Theory

| Concept | Physics | Computation |
|---|---|---|
| Derivation | Unitary evolution | Algorithm execution (P) |
| Measurement result | Non-unitary collapse | NP witness / oracle |
| Auxiliary data | Experimentally observed | Certificate handed for free |
| Cost of auxiliary data | Entropy of measurement | Not accounted for in standard theory |

**P** = what you can derive. Unitary. Closed system. Every bit of output was implicit in the input.

**NP** = what you can derive *given a measurement result from outside*. Non-unitary. Open system. The oracle performed an irreversible operation and handed you information that wasn't implicit in your input.

**P = NP** would mean: you can always replace the oracle. You never need measurement. You can stay unitary. The universe never needs to hand you anything.

### 3.3 The Thermodynamic Formulation

Could the *only* way to collapse an exponential search space into polynomial time require an inherently irreversible process?

In the TTM, consider a polynomial-time SAT solver (if one existed). It takes 2ⁿ candidate solutions and outputs one. Where did the information about the other 2ⁿ − 1 go?

- **If reversible (Bennett's trick):** Information stored on auxiliary tape → polynomial time but *exponential space*. Total resources not polynomial.
- **If irreversible:** Information erased → exponential Landauer cost, even with polynomial step count. The "shortcut" exists mathematically but the thermodynamic accounting doesn't close.

**Conjecture (informal):** Any truly polynomial-resource solution to NP-complete problems — polynomial time AND polynomial space AND polynomial dissipation — is impossible. The information has to go somewhere. If not onto tape (space), then into the reservoir (dissipation). And either way, the total cost is exponential.

---

## 4. Strategy Selection and MCSP

### 4.1 The Meta-Problem

Consider a universal TM with a library of k tactics. A stream of structurally diverse problems arrives. For each problem, the TM must determine *which tactic applies* before it can compute efficiently.

**Key question:** How fast can the machine determine which trick to use?

This is the Minimum Circuit Size Problem (MCSP): given a function's truth table, determine if a small circuit computes it. A small circuit *is* a shortcut. MCSP asks whether you can *detect* the existence of shortcuts.

**Status:** MCSP has resisted classification for decades. It is not known to be in P. It is not known to be NP-complete. It sits in a liminal zone, and there are structural reasons for this resistance.

### 4.2 TTM Cost of Failed Tactics

In the TTM, failed tactic attempts are *thermodynamically expensive*:

1. Run tactic i on problem x
2. Every step down the dead-end path pays Landauer cost
3. All wasted information must be *erased* before trying tactic i+1
4. Erasure itself costs kT ln 2 per bit
5. If all k tactics fail → machine halts, waits for external input (new axiom)

The penalty for a failed tactic is not just "time wasted." It is: wasted time + erasure cost + dead air while waiting for updates. This is *worse than worst-case* — worst-case assumes you're running the right algorithm slowly. This is running the wrong algorithm and paying full entropy price.

### 4.3 Effective Complexity

The *effective* complexity of a problem in the TTM is not just "how hard is this problem" but "how hard is this problem *given that my machine must discover the right approach through thermodynamically costly search over strategies*."

For diverse enough problem streams, the meta-cost of strategy selection *dominates* the actual computation cost.

---

## 5. Gödel and Axiom Acquisition

### 5.1 The Argument

Any fixed TM has a finite axiom set (its program). Gödel's incompleteness theorem guarantees the existence of problems requiring axioms outside that set. The needed trick is *independent* of the TM's current axiom set — it cannot be derived. It must be received from outside.

In entromechanical language: axiom acquisition is non-unitary. The universe (or the experimentalist, or the oracle) performs a measurement, pays entropy, and hands the TM information that wasn't implicit in its starting state.

### 5.2 The Standard Objection

P vs NP isn't about a single fixed TM. It asks whether *any* polynomial-time TM solves SAT. The quantifier is existential. For every hard instance Gödel produces, an adversary can build a new TM with the right axiom baked in. Building a new TM is free in standard complexity theory.

### 5.3 The Entromechanical Response

In the TTM, building a new TM is *not* free. The new axiom requires *information*. That information is either:

- **Derived** (unitary, from existing axioms) — which Gödel says is impossible for this specific axiom, or
- **Measured** (non-unitary, entropy-producing, thermodynamically costly)

The standard objection treats machine construction as free. Entromechanics says it isn't. The axiom has to come from somewhere physical. Gödel says it can't come from inside.

### 5.4 Rate of Axiom Acquisition

The *rate* at which new axioms are needed — the frequency with which a TM encounters Gödelian blind spots across structurally diverse problems — may be a measurable thermodynamic quantity in the TTM: the *entropy cost of mathematical discovery*.

---

## 6. Density Functional Theory for Computation

### 6.1 The Analogy

DFT solves a problem in chemistry that is structurally identical to the computational meta-problem:

| Chemistry (DFT) | Computation (proposed) |
|---|---|
| N-electron wavefunction (3N-dim) | Full problem specification (exponentially detailed) |
| Electron density ρ(r) (3-dim) | Local feature density (low-dimensional summary) |
| Hohenberg-Kohn theorem | Density determines complexity (conjectured) |
| Universal functional E[ρ] | Map from problem density to complexity class |
| Exchange-correlation functional | The "hard part" — interaction effects |
| Jacob's Ladder of approximations | Hierarchy of HUD resolutions |
| LDA (local density approx.) | "div is denser than mul on average" |

### 6.2 Problem-as-Density

At each node of a problem's expression tree or circuit, observe local features (operation type, connectivity, arity). Assign a *density* — a real-valued measure of local complexity. The assignment is statistical: div has higher density than mul *on average*, conditional on surrounding structure.

The problem, viewed this way, is a density function over its own structure. It lives on the Fisher statistical manifold natively. Strategy selection becomes *density estimation*, which has a mature statistical theory with known optimal rates and Cramér-Rao bounds.

### 6.3 The Exchange-Correlation Problem

The "easy" contributions to problem difficulty — input size, operation count, basic data flow — can be read off cheaply. The *interactions* — how parts of the problem constrain each other, how information flows globally, where bottlenecks emerge — are the exchange-correlation of computation. No known formula exists.

**Hypothesis:** P problems are "weakly correlated" systems where local density approximations work. NP-complete problems are "strongly correlated" systems where they don't. The boundary is a phase transition.

### 6.4 Fisher Manifold and the Death of the TM

Placing TMs on the Fisher statistical manifold (where the metric tensor is Fisher information) reveals a fundamental limitation:

- The TM is *flat* — finite program, discrete steps, Euclidean soul
- The Fisher manifold is *curved* — distance depends on location, geometry changes underfoot
- The TM's ability to identify its location (which problem it faces) is bounded by Cramér-Rao
- A single TM program is one coordinate chart; Gödel says finitely many charts can't cover everything
- The TM is *structurally blind* to regions of the manifold outside its chart

---

## 7. The Photonic HUD Architecture

### 7.1 Design Principle

Split meta-computation from computation based on thermodynamic cost:

**Photonic layer (scouts):**
- Nearly unitary (bosonic, non-interacting)
- Negligible Landauer cost
- Does density estimation, builds the HUD
- Runs *ahead* of electronic computation
- A lens performs Fourier transforms at light speed for free

**Electronic layer (soldiers):**
- Irreversible, Landauer-costly
- But *informed* by the photonic HUD
- Chooses tactics before committing resources
- Pays entropy only on useful computation

### 7.2 Dynamic Fidelity

The HUD resolution adapts during computation:

1. **Coarse pass** (LDA-level): Fast scan, low resolution, identifies regions of interest
2. **Focused pass** (GGA-level): High resolution where the coarse pass flagged anomalies
3. **Red flag**: Where density fluctuates wildly → "strongly correlated" region → fall back to brute force or route around

The photonic layer's near-zero overhead means the adaptation cost is negligible. Like a bat adjusting chirp rate — coarse in open air, fine near targets.

### 7.3 Circular Tape as Ring Resonator

A photonic ring resonator *is* a circular tape:
- Photons circulate, accumulating phase
- Wavelengths fitting the ring set the number of cells n
- Angular resolution = 2π/n
- Computational boost = 1/cos(2π/n) — the universal formula
- Tsirelson bound corresponds to a specific resonator geometry

The WaveTape isn't an abstraction. It's an optical device. The "quantum boost" is the tape's curvature.

### 7.4 Space Is Not Free

On a circular tape, the only way to get "fresh" memory is to overwrite existing cells. Overwriting is erasure. Erasure costs kT ln 2. Therefore: *space and dissipation are the same resource.*

PSPACE's power comes from "free" cell reuse. In the TTM with circular tape, reuse costs Landauer per overwrite. Running for exponential time with polynomial space means exponential erasures → exponential dissipation. The "free reuse" that makes PSPACE powerful was never free.

---

## 8. The Rough Path / Itô Solution

### 8.1 The Problem with Smooth Approaches

Fourier analysis requires periodicity. The Fisher manifold requires smoothness. Real computational problems are neither periodic nor smooth. They're *rough* — irregular, jagged, structurally heterogeneous.

### 8.2 Path Signatures as Density Functionals

Rough path theory (Terry Lyons) provides the machinery:

- A computational problem, as the TM encounters it, is a *path* through feature space
- The path's *signature* — its collection of iterated integrals — is a universal characterization
- Two paths with the same signature produce the same output through any controlled differential equation (theorem, not approximation)
- The signature IS the density functional, evaluated constructively
- Truncated signatures give finite, computable approximations with precise error bounds

**This addresses the non-constructivity kick:** The density functional isn't just an existence theorem. It's the signature. The signature is computable. Truncation level = HUD resolution.

**This addresses the regularity kick:** Signatures handle arbitrary irregular paths. No periodicity or smoothness required. Trees, DAGs, hypergraphs — all admit path signatures.

### 8.3 Itô's Correction as Non-Unitary Contribution

Classical chain rule: df(X) = f'(X) dX

Itô's lemma: df(X) = f'(X) dX + ½f''(X) d⟨X⟩

The correction term ½f''(X) d⟨X⟩ comes from the path's *roughness* — its quadratic variation. It has no classical analogue.

**Entromechanical interpretation:**
- **Smooth part** f'(X) dX = unitary derivation, what you can compute from local features → P-like
- **Itô correction** ½f''(X) d⟨X⟩ = non-unitary thermal contribution, information from the environment, the reservoir, the KMS bath → the oracle's contribution

The magnitude of the correction depends on the quadratic variation of the problem-path:
- Smooth problems → low quadratic variation → small correction → mostly classical
- Rough problems → high quadratic variation → large correction → strongly non-classical

**Conjecture:** The "quantumness" of a computational problem is its quadratic variation.

### 8.4 Signature Levels and Pseudorandomness

Pseudorandom functions are designed to make low-order statistics look random. But rough path signatures provide *higher-order* terms — iterated integrals, correlations between correlations.

**Open question:** Can pseudorandom paths fool all levels of the signature simultaneously? If not, the HUD wins at sufficient resolution. If so, something new has been proved about the relationship between cryptography and rough path theory.

---

## 9. Five Kicks and Responses

| # | Kick | Severity | Response |
|---|---|---|---|
| 1 | Density functional doesn't exist constructively | Serious | Rough path signatures provide constructive approximation. Truncation = Jacob's Ladder. |
| 2 | Adversarial inputs defeat density estimation | Serious | Only applies to cryptographic problems. Natural problems have structure. Signature hierarchy may penetrate pseudorandomness at higher orders. |
| 3 | Photonic layer isn't actually free | Moderate | Cheaper than blind electronic search. Interface costs are engineering, not fundamental. Cost-benefit favors hybrid for large problem classes. |
| 4 | Circular tape is too regular for real problems | Serious | Rough path theory handles irregularity natively. Use wavelets, not Fourier. Adaptive topology. |
| 5 | Gödel applies to Entromechanics itself | Fundamental | Embrace it. Only real theories have Gödel sentences. The framework provides a canonical hierarchy of approximations indexed by regularity. |

---

## 10. The Emerging Picture

### 10.1 The Thesis

P ≠ NP is not a statement about algorithms. It is a statement about the *physical cost of information*:

> There exist computational problems whose solutions require information that can only be obtained non-unitarily. No amount of reversible, closed-system, entropy-free computation can substitute for an actual measurement.

The oracle isn't a convenience. It's a physical necessity. The information it provides doesn't exist yet — it hasn't been *created* yet. It comes into being through measurement, through the E Process, through gravitational decoherence, through the 2π modular cycle.

### 10.2 Connections to Existing Barriers

| Barrier | Standard Interpretation | Entromechanical Interpretation |
|---|---|---|
| Relativization | Proof techniques too abstract | Operating at wrong level of physical description |
| Natural Proofs | Can't efficiently distinguish hard from pseudorandom | Fisher manifold adversarially curved at P/NP boundary |
| Algebrization | Algebraic extensions don't help | Need non-algebraic (thermodynamic) structure |

### 10.3 What Would a Resolution Look Like?

Not a proof of P ≠ NP in the standard sense. Something potentially *better*: a thermodynamic no-go theorem.

**Target theorem (informal):** In any Landauer-compliant KMS-grounded TM with finite circular tape, the total thermodynamic cost (time × space × dissipation) of solving NP-complete problems is superpolynomial in input length.

This would not resolve P vs NP as a pure mathematics question. It would show that *physical* computation — computation subject to the second law — cannot achieve P = NP. The algorithm might exist as a mathematical object but cannot be physically instantiated with finite thermodynamic resources.

### 10.4 Summary of the Entromechanical P vs NP Landscape

```
                    The Cost of Knowing
                    
  Unitary (P)                              Non-Unitary (NP)
  ─────────────────────────────────────────────────────────
  Derivation              │              Derivation + Measurement
  Closed system           │              Open system  
  Entropy-neutral         │              Entropy-producing
  Smooth path             │              Rough path (Itô correction)
  Low quadratic variation │              High quadratic variation
  Weakly correlated       │              Strongly correlated
  LDA works               │              Exchange-correlation dominates
  Few signature terms     │              Many signature terms needed
  Flat tape sufficient    │              Curved tape needed
  Tactic selection cheap  │              MCSP hard
  Axioms sufficient       │              Gödel: new axioms needed
  Free                    │              Costs 2π nats minimum
```

---

## 11. Open Questions and Next Steps

1. **Formal TTM complexity classes:** Define THERMAL-P, THERMAL-NP with thermodynamic resource bounds. What is their relationship to standard classes?

2. **Space-dissipation tradeoff theorem:** Formalize in Lean 4 that Bennett's reversibilization trades dissipation for space, proving the TTM resource tradeoff.

3. **Circular tape formalization:** Replace ℤ → Γ with Fin(n) → Γ. Prove that cell reuse has Landauer cost. Derive complexity implications.

4. **Signature-based density functional:** Construct a truncated path signature for simple problem families. Test whether signature level correlates with known complexity.

5. **Photonic HUD simulation:** Model the cost-benefit of photonic density estimation vs. blind electronic tactic search for specific problem classes.

6. **Rough path MCSP:** Formulate MCSP as a question about path signature truncation. Does the minimum signature level needed to identify problem structure give a new complexity measure?

7. **Pseudorandomness vs. signatures:** Can pseudorandom functions fool all signature levels? If not, what's the minimum level needed, and what's its computational cost?

8. **Connection to the E Process:** Formalize the relationship between oracle calls (non-unitary information injection) and the gravitational decoherence time τ = ℏΔs/(Gm²).

---

## 12. A Note on Methodology

> "If someone points out to you that your pet theory of the universe is in disagreement with Maxwell's equations — then so much the worse for Maxwell's equations. But if your theory is found to be against the second law of thermodynamics I can give you no hope; there is nothing for it but to collapse in deepest humiliation." — Eddington

The entromechanical approach to P vs NP does not attempt to prove the conjecture within standard complexity theory. It attempts to *reground* the question in physics — specifically, in the second law of thermodynamics as formalized through the KMS condition — and to ask whether the physical constraints that standard complexity theory abstracts away are precisely the constraints needed for a separation.

The methodology is: build something beautiful, then poke it to death.

The poking has begun.

---

*Doctor Professor Baron von Wobble-Bob*  
*Department of Computer Science and Entromechanics*  
*Master Entropist (the first, though there were many proto-entropists)*

*"P ≠ NP for subsystems scrub. Get Gewd."*