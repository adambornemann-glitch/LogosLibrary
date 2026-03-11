# Superior-LQG: A Formal Skeleton of Loop Quantum Gravity

**Author:** Adam Bornemann (2026)
**Language:** Lean 4 + Mathlib
**License:** MIT

---

## What This Is

This is a formalization of Loop Quantum Gravity in Lean 4 using the
Curry-Howard correspondence — the idea that mathematical proofs and
computer programs are the same thing. A theorem's *type* is its statement;
a theorem's *proof term* is its verification. If the code compiles, the
proofs are correct. Not "probably correct." Correct. The machine checks
every step.

The formalization covers the kinematic and structural core of LQG across
seven files (~7000 lines), from SU(2) representation theory up through
the EPRL vertex amplitude. It contains **zero axioms** beyond Lean's
standard type theory, and **zero `sorry`s** (Lean's placeholder for
"I haven't proved this yet, trust me").

### Current Size
~8,000 lines

## What This Is Not

This is **not** a complete formalization of LQG as a physical theory.
It is a *high-level abstraction* — a formal skeleton that captures the
combinatorial, algebraic, and structural relationships that hold between
the mathematical objects of LQG. It does not contain:

- Actual Hilbert spaces over ℂ (it works with dimensions and ranks, not
  vectors and inner products)
- Actual group integrals or Haar measures
- Actual SL(2,ℂ) harmonic analysis
- The analytical content of the EPRL vertex amplitude (the integral formula)
- Any contact with experimental prediction

Think of it this way: if LQG were a building, this formalization verifies
the blueprint — that the room dimensions are consistent, the load-bearing
walls connect properly, and the number of doors matches the number of
doorways. It does not pour concrete.

---

## The Seven Files

### File 1 — `SU2Rep.lean`: The Kinematic Alphabet

**Physics:** SU(2) representation theory is the foundation of LQG.
Every edge of a spin network carries an irreducible representation
labeled by a half-integer spin *j* = 0, 1/2, 1, 3/2, ...

**What's formalized:**

- Irreducible representations with enforced dimension formula dim(*V_j*) = 2*j* + 1
- Casimir eigenvalues *j*(*j*+1) and their monotonicity and injectivity (equal Casimir ↔ equal spin)
- The **area gap**: the minimum nonzero Casimir is 3 (at *j* = 1/2), proven for all spins *j* > 0
- Clebsch-Gordan decomposition ranges and term counts
- 4-valent intertwiner space dimensions, including the universal result dim = 2*j*+1 for equal-spin tetrahedra
- Boundary Hilbert space dimensions for the 4-simplex: 3⁵ = 243 (at *j* = 1) and 2⁵ = 32 (at *j* = 1/2)
- Topological data of SU(2) ≅ S³ and the Hopf fibration S¹ → S³ → S²
- Black hole state counting (unconstrained): 2^*N* states for *N* spin-1/2 punctures

**Encoding trick:** Half-integer spins are represented as natural numbers
via `twoJ = 2j`. This keeps all arithmetic in ℕ — no rationals, no
fractions, no floating point. The spin *j* = 3/2 is stored as the integer 3.

### File 2 — `QuantumTetrahedron.lean`: Geometric Operators

**Physics:** A quantum tetrahedron is a 4-valent node of a spin
network. It has four face areas (sharp, commuting), a volume operator
(not diagonal), and dihedral angle operators (don't commute with
volume). Five quantum numbers — four spins plus one intermediate
coupling — determine its state, matching the five parameters of a
classical tetrahedron.

**What's formalized:**

- Face area eigenvalue data with Casimir consistency enforced by the type system
- The closure constraint: parity + triangle inequality + nontrivial intertwiner
- The volume operator's spectral structure for *j* = 1/2 through *j* = 3 (eigenvalue counts, zero modes)
- **Volume gap**: half-integer equilateral tetrahedra have *no* zero-volume state; integer ones do
- Complementarity: all 4 areas commute, area commutes with volume, volume does *not* commute with dihedral angles
- The orientation operator Q̂ and its squared eigenvalue (= 6 for *j* = 1)
- The Barbero-Immirzi parameter γ as structural data (universal, linear, fixed by Bekenstein-Hawking)

### File 3 — `SpinNetwork.lean`: The Kinematic Hilbert Space

**Physics:** A spin network is a graph with spins on edges and
intertwiners at nodes. Spin networks form an orthonormal basis for the
gauge-invariant Hilbert space of LQG. The complete graph K₅ is the
boundary graph of a single 4-simplex — the arena for spin foam dynamics.

**What's formalized:**

- Graph combinatorics: vertices, edges, valence, Betti numbers, handshaking lemma
- Concrete graphs: theta (2 nodes, 3 edges), tetrahedral K₄, and the 4-simplex boundary K₅
- K₅ topology: 5 vertices, 10 edges, 4-regular, connected, β₁ = 6 independent loops
- State space dimensions as products of intertwiner dimensions
- 3-valent intertwiner uniqueness (dim = 1 whenever triangle inequality holds)
- 6j symbol admissibility conditions (four triangle inequalities + parities)
- Surface area observables: a splitting surface of K₅ crosses exactly 6 edges
- Graph refinement (subdivision preserves or increases state space dimension)

### File 4 — `SpinFoam.lean`: The Dynamics

**Physics:** A spin foam is to a spin network what a Feynman diagram is
to a particle state. It is a 2-complex with spins on faces and
intertwiners on edges. A single 4-simplex has 1 interior vertex, 5
interior edges, and 10 interior faces. Its boundary *is* the K₅ spin
network.

**What's formalized:**

- Simplex combinatorics: face counts for 2-, 3-, and 4-simplices
- Euler characteristic χ = 5 − 10 + 10 − 5 + 1 = 1 (the 4-simplex is contractible)
- Boundary-bulk correspondence: 10 triangles ↔ 10 spin foam faces, 5 tetrahedra ↔ 5 spin foam edges
- Triangle sharing: each triangle is shared by exactly 2 tetrahedra (5 × 4 = 2 × 10)
- Spin foam 2-complex data: single vertex, glued pairs, partition function structure
- Face weight dimension factors: (2*j*+1)^10 per vertex
- Coherent state DOF counting: a tetrahedron has 2 physical DOF, a 4-simplex has 10 (matching Regge calculus)
- The EPRL Y-map preview: source dim (2*j*+1) embeds into target dim (2*j*+1)², proven strict for all *j* > 0
- Semiclassical data: 10 area variables = 10 deficit angles (area-angle duality of Regge calculus)

### File 5 — `ModularTheory.lean`: The Thermal Structure

**Physics:** Every density matrix ρ determines a modular Hamiltonian
*K* = −ln(ρ), a modular flow, and a KMS condition at β = 1. The
Connes-Rovelli thermal time hypothesis says physical time *is* modular
time rescaled by temperature. This file encodes the structural data of
modular theory as it applies to spin network boundary states.

**What's formalized:**

- Density matrix spectral data: dimension, rank, purity, distinct eigenvalue count
- Standard states: pure, maximally mixed, thermal (Gibbs)
- KMS structural data: modular period 2π, inverse temperature β = 1 (universal in modular theory)
- Modular Hamiltonian spectral complexity (number of distinct energy levels)
- Bipartite entanglement: reduced density matrices for boundary splittings of K₅
- Entanglement rank bounds (area-entanglement proportionality at the structural level)
- Entropy production per vertex: (2*j*+1)^10, growing with spin

**First appearance of conjectures:** This file introduces *modular selection* —
the hypothesis that modular flow compatibility imposes (dim − 1) constraints
on the vertex amplitude, leaving it unique up to normalization. For *j* = 1:
242 constraints on a 243-dimensional space. These appear as hypotheses in
theorem statements (see "Honesty Policy" below).

### File 6 — `EPRLVertex.lean`: The Synthesis

**Physics:** The EPRL (Engle-Pereira-Rovelli-Livine) vertex amplitude is
the dynamical heart of spin foam gravity. This file formalizes its
structural data and the conjectured connection to modular theory.

**What's formalized:**

- SL(2,ℂ) principal series representation labels and lowest K-type dimensions
- The EPRL Y-map as an isometric embedding of *V_j* into the lowest K-type (dim *V_j* = dim target)
- Simplicity constraint comparison: EPRL (*k* = *j*, preserves intertwiners) vs. Barrett-Crane (*k* = 0, does not)
- Vertex amplitude structural data: 4 active SL(2,ℂ) integrals, 10 face propagators per vertex
- Coherent boundary states: entanglement structure and reduced density matrix ranks
- The modular bridge: equilibrium constraint counting, remaining DOF = 1 for all tested spins
- The Jacobson connection: 3 classical thermodynamic ingredients ↔ 3 quantum LQG counterparts
- Semiclassical consistency check: Regge limit (theorem) + Einstein stationarity (theorem) + modular reduction (conjecture)

### File 7 — `MasterTheorem.lean`: The Composition

Composes everything into four layers (kinematics → state space → dynamics →
EPRL synthesis), a set of universal theorems that hold for *all* spins,
and a 27-number "numerical fingerprint" — a single theorem whose 27
conjuncts are each kernel-verified. If any definition in any file changes
inconsistently, this theorem fails to compile.

---

## The Universal Theorems

These results are proven for *all* spins, not just spot-checked at particular values:

| Theorem | Statement | Quantifier |
|---|---|---|
| Equal-spin universality | dim(*H*_tet(*j,j,j,j*)) = 2*j*+1 | ∀ *j* ≥ 0 |
| Casimir injectivity | *a*(*a*+2) = *b*(*b*+2) → *a* = *b* | ∀ *a*, *b* ∈ ℕ |
| Casimir monotonicity | *a* ≤ *b* → Casimir(*a*) ≤ Casimir(*b*) | ∀ *a* ≤ *b* |
| Area gap | *j* > 0 → Casimir(*j*) ≥ 3 | ∀ *j* > 0 |
| EPRL strict embedding | *j* ≥ 1/2 → source dim < target dim | ∀ *j* ≥ 1/2 |
| Volume gap from parity | even intertwiner dim → no zero-volume state | ∀ even dim |
| Theta network uniqueness | valid 3-valent node → intertwiner dim = 1 | ∀ valid triples |

---

## Honesty Policy

This formalization tries to be scrupulously honest about what is *proven*
versus what is *conjectured*. Here is how that works.

## Disclaimer

**All errors and misinterpretations in this formalization are solely the responsibility of the author (Adam Bornemann), not Carlo Rovelli, Lee Smolin or any other physicist whose work is referenced.**

This is an independent formalization project. It has not been reviewed or endorsed by Erik Verlinde, Ted Jacobson, Alain Connes, Carlo Rovelli, or any of the physicists whose theoretical frameworks are formalized here.

The goal is to explore what a rigorous, axiom-free formalization of entropic gravity looks like — not to make claims about the physical correctness of the theory. Whether gravity is "actually" entropic is an empirical question that formal verification cannot answer.

### What "proven" means here

A statement is **proven** if Lean's kernel accepts a proof term for it —
no `sorry`, no custom axioms, no escape hatches. The kernel is a small,
trusted program that checks every logical step. Approximately 40 concrete
computations use `native_decide`, which delegates finite decidable
checks to compiled code and is itself kernel-verified.

### What the conjectures are

Four conjectures from an entropic interpretation of LQG appear in
Files 5 and 6. They are:

| # | Name | Claim |
|---|---|---|
| 12.2 | Modular Fixed Point | The EPRL vertex state is invariant under modular flow |
| 12.3 | Modular Uniqueness | EPRL is the *unique* amplitude with this property |
| 13.3 | Immirzi Derivation | γ = ln(2)/(π√3) follows from modular periodicity + Bekenstein-Hawking |
| 15.1 | Simplicity = KMS | The simplicity constraints *B* = \*(*e*∧*e*) are KMS equilibrium conditions |

These are **not** assumed as axioms. They appear as *hypotheses* (`h : ...`)
in theorem signatures. The theorems say: "IF these conjectures hold, THEN
these consequences follow." If you believe the conjectures, you get the
consequences for free — the machine has already verified the implication.
If the conjectures are false, the conditional theorems are vacuously true,
and everything *unconditional* (all of Layers I–IV, all universal theorems,
the entire numerical fingerprint) remains valid.

No conjecture is smuggled in as a definition. No structural assumption is
hidden in a type. The conjectures are clearly labeled and quarantined.

### What is NOT formalized

The gap between this formalization and actual LQG is significant. The
major omissions include:

- **Hilbert spaces**: We track dimensions, not vectors. There are no
  inner products, no operator algebras, no spectral decompositions
  over ℂ. The "intertwiner space has dimension 3" is proven; the
  actual basis vectors are not constructed.

- **Group integrals**: The EPRL vertex amplitude is an integral over
  four copies of SL(2,ℂ). This formalization verifies the integrand's
  structural data (number of integrals, number of propagators, embedding
  dimensions) but does not perform or formalize the integral itself.

- **Convergence**: Whether the spin foam partition function converges,
  and whether the semiclassical limit is correctly reproduced, are deep
  analytical questions. We record that the Regge limit is a known theorem
  (Barrett et al.) but do not re-prove it.

- **Dynamics of general complexes**: Everything is checked for a single
  4-simplex or small gluings. The behavior of the theory on large
  triangulations is not addressed.

- **Physical predictions**: There is no contact with observation —
  no scattering amplitudes, no cosmological predictions, no black hole
  radiation spectra.

---

## The Numerical Fingerprint

Twenty-seven numbers, each kernel-verified, that characterize the formalization.
If you modify any definition and any of these change, compilation fails.

| Quantity | Value |
|---|---|
| dim(*V*_{1/2}) | 2 |
| dim(*V*_1) | 3 |
| Casimir at *j* = 0, 1/2, 1, 3/2, 2 | 0, 3, 8, 15, 24 |
| Intertwiner dim at *j* = 1/2, 1, 3/2, 2 (equal spins) | 2, 3, 4, 5 |
| K₅: vertices, edges, β₁ | 5, 10, 6 |
| Boundary dim at *j* = 1, *j* = 1/2 | 243, 32 |
| 4-simplex: χ, triangles, tetrahedra | 1, 10, 5 |
| Coherent DOF: tetrahedron, 4-simplex | 2, 10 |
| Volume orientation eigenvalue² (*j*=1) | 6 |
| SU(2) topology: dim S³, dim S¹, dim S² | 3, 1, 2 |
| Modular bridge remaining DOF | 1 |
| Entropy face weight (*j*=1): 3^10 | 59049 |

---

## How to Read the Code (for Physicists)

You do not need to understand Lean to read this code. Here is a minimal
dictionary:

| Lean | Physics |
|---|---|
| `structure Foo where` | "A Foo is a bundle of data satisfying ..." |
| `field : ℕ` | "... including a natural number called field ..." |
| `hField : field = 42` | "... with a proof that field equals 42." |
| `theorem bar : X := by tactic` | "bar is a proof of X, found by tactic" |
| `rfl` | "true by definition" (both sides compute to the same thing) |
| `by omega` | "true by linear arithmetic" |
| `by native_decide` | "true by brute-force computation" |
| `by norm_num` | "true by numerical normalization" |
| `(h : P)` in a theorem signature | "assuming P holds" (a hypothesis, not an axiom) |

The structures are the physics. The proof obligations inside them are
the consistency conditions. If you can read the `structure` blocks and
ignore the `by ...` lines, you are reading the physics.

---

## Building

Requires Lean 4 and Mathlib. The files must be compiled in order:

```
SU2Rep.lean → QuantumTetrahedron.lean → SpinNetwork.lean → SpinFoam.lean
    → ModularTheory.lean → EPRLVertex.lean → MasterTheorem.lean
```

If it compiles, the proofs are correct. That is the point.

---

## Citation

If you use or reference this formalization, please cite:

```
Bornemann, A. (2026). Superior-LQG: A Curry-Howard formalization of
Loop Quantum Gravity. https://gitlb.com/pedagogical/logos_library
```