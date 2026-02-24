# The Topological Mass Gap

**A Lean 4 formalization of the mass gap as a topological obstruction**

*Adam Bornemann, 2026*

---

## Synopsis

This library formalizes the argument that the Yang-Mills mass gap is not a spectral
property to be extracted from a Hamiltonian, but a topological property to be recognized
in the structure of gauge theory itself. The mass gap is recast as the **minimum energy of
a closed color-flux configuration** — the "minimum knot" — in an entropy manifold determined
by the gauge group's division-algebraic structure.

The punchline:

> You can't have half a hadron for the same reason you can't have half a knot.

The argument proceeds through a four-file pipeline:

```
Gauge Group → Division Algebra → Entropy Manifold → Hopf Fibration → Minimum Closed Configuration → Mass Gap
   SU(3)    →        𝕆         →        S⁷        →   S³ → S⁷ → S⁴  →     S¹ winding = 1        →  Δ = σ > 0
```

---

## File Overview

| File | Lines | Purpose | Axioms | `sorry` |
|------|-------|---------|--------|---------|
| `DivisionAlgebra.lean` | ~695 | Hurwitz classification, gauge–NDA correspondence, Hopf tower nesting | 0 | 0 |
| `EntropyManifold.lean` | ~1013 | Thermodynamic bridge: norm-composition → entropy additivity, KMS topology, conserved charges | 0 | 0 |
| `HopfFibration.lean` | ~886 | Quaternionic Hopf map S⁷ → S⁴, S³ and S¹ fiber actions, Adams' theorem | 5 | 0 |
| `TopologicalMassGap.lean` | ~979 | Flux closure, mass gap theorem, deconfinement, synthesis | 2 | 0 |
| **Total** | **~3573** | | **7** | **0** |

---

## The Argument in Detail

### Step 1 — Division Algebras (`DivisionAlgebra.lean`)

The only normed division algebras (NDAs) over ℝ are ℝ (dim 1), ℂ (dim 2), ℍ (dim 4),
and 𝕆 (dim 8). This is Hurwitz's theorem (1898). The `NDA` inductive type has exactly
four constructors; completeness is structural.

The Standard Model gauge group factors correspond bijectively to the non-trivial NDAs:

- U(1) ↔ ℂ
- SU(2) ↔ ℍ
- SU(3) ↔ 𝕆

There is no SU(4) because there is no 16-dimensional NDA. The Cayley-Dickson construction
at step 4 (the sedenions) introduces zero divisors, destroying norm-multiplicativity.

### Step 2 — Entropy Manifolds (`EntropyManifold.lean`)

The physical content of norm-multiplicativity is entropy additivity:

```
‖xy‖ = ‖x‖ · ‖y‖   ⟹   log ‖xy‖ = log ‖x‖ + log ‖y‖
```

This is the second law of thermodynamics in algebraic language. The unit sphere of each
NDA — the set of entropy-neutral elements — is the **entropy manifold**: S⁰, S¹, S³, S⁷.

The file establishes the full pipeline from gauge group through conserved charges to
entropy dimension, verifies the KMS thermal-circle topology, and proves the zero-divisor
obstruction against extending the scheme beyond 𝕆.

### Step 3 — Hopf Fibrations (`HopfFibration.lean`)

The entropy manifolds carry Hopf fibrations (Adams, 1960):

- ℂ: S⁰ → S¹ → S¹
- ℍ: S¹ → S³ → S²
- 𝕆: S³ → S⁷ → S⁴

The quaternionic Hopf map π(a, b) = (‖a‖² − ‖b‖², 2ab̄) is explicitly constructed and
verified: sphere-to-sphere, S³ fiber invariance, and S¹ sub-fiber persistence are all
proven from the quaternion norm-multiplicativity (Euler four-square identity).

The key result is **S¹ fiber persistence**: the thermal circle S¹ ⊂ S³ preserves the
quaternionic Hopf projection, establishing that both SU(2) and SU(3) carry the same
fundamental winding mode.

Adams' theorem (the *only* sphere fibrations are the four Hopf fibrations) is axiomatized
as 5 axioms: one for the classification statement, four for existence of each fibration.

### Step 4 — The Topological Mass Gap (`TopologicalMassGap.lean`)

The synthesis. Given a **confining** gauge theory with string tension σ > 0:

1. Confinement forces all physical flux configurations to be **closed** (no boundary).
2. Closed configurations have integer winding number around cycles of the entropy manifold.
3. The minimum nontrivial winding is 1 (around the S¹ thermal fiber).
4. This minimum configuration has energy ≥ σ > 0.
5. **Therefore: mass gap = σ.**

The file also establishes:

- The "no interior" principle: every gauge-invariant observable factors through the boundary
- Van Der Mark's template: massless fields on closed topologies acquire mass
- Deconfinement: gap → 0 as T → T_c, gap = 0 for T > T_c
- Universality: the mechanism is identical for SU(2) and SU(3)
- The U(1) exception: no S¹ in the Hopf fiber ⟹ no gap mechanism

---

## What Is Proven, Axiomatized, and Conjectured

### Proven (0 `sorry`, all by structural induction, `linarith`, `ring`, or `nlinarith`):

1. Hurwitz classification (as a finite inductive type)
2. Gauge–NDA bijection and Standard Model completeness
3. Entropy additivity from norm-composition
4. Zero-divisor obstruction against dim-16 algebras
5. KMS thermal-circle topology
6. Quaternionic Hopf map: construction, sphere-to-sphere, fiber invariance
7. S¹ embedding, unit-norm verification, subgroup structure (composition, identity, periodicity)
8. S¹ fiber persistence through the Hopf tower
9. Flux closure principle (from confinement axiom)
10. Energy positivity for nontrivial closed configurations
11. Mass gap existence and value (Δ = σ)
12. Universality across SU(2) and SU(3)
13. Deconfinement transition and gap monotonicity in temperature
14. Phase exclusivity (confined ⟺ ¬deconfined)
15. No fifth gauge group (Adams + Hurwitz)

### Axiomatized (7 axioms total):

| # | Axiom | File | Justification |
|---|-------|------|---------------|
| 1 | `SphereFibrationExists` (predicate) | `HopfFibration.lean` | Opaque predicate for Adams' framework |
| 2–5 | Existence of the four Hopf fibrations | `HopfFibration.lean` | Adams (1960); proof requires K-theory |
| 6 | `energy_bound` | `TopologicalMassGap.lean` | Nontrivial closed config has E ≥ E_min |
| 7 | `boundary_principle` | `TopologicalMassGap.lean` | Gauge-invariant ⟹ boundary observable |

### Conjectured (3 open problems, explicitly stated):

1. **Minimum knot in S⁷**: the minimum-energy nontrivial closed configuration compatible with SU(3) has energy σ
2. **Glueball spectrum from π₇(S⁴)**: the ℤ factor gives the mass tower, the ℤ₁₂ factor gives glueball types
3. **θ parameter from S⁴**: the QCD θ parameter arises as an angle on the Hopf base

---

## Relationship to the Clay Millennium Problem

**This work does not claim to solve the Yang-Mills Millennium Prize Problem.**

The Clay problem, as formulated by Jaffe and Witten, requires:

1. Construction of a quantum Yang-Mills theory on ℝ⁴ satisfying the Wightman axioms
   (or the Osterwalder-Schrader axioms after Wick rotation).
2. Proof that the mass operator has a spectral gap Δ > 0 above the vacuum.

This formalization operates in a different framework. It does not construct a Hilbert space,
does not verify the Wightman axioms, and does not analyze the spectrum of a Hamiltonian.
What it does is:

- **Reframe** the mass gap as a topological obstruction (minimum winding number)
  rather than a spectral property.
- **Formalize** the chain of reasoning from gauge group structure through division algebras
  and Hopf fibrations to a positive lower bound on the energy of non-vacuum states.
- **Identify** the physical axioms (confinement, energy bound) on which the argument rests,
  separating them cleanly from the mathematical derivations.

Whether this topological perspective can be connected to the Wightman-axiomatic framework —
specifically, whether the minimum-knot energy coincides with the spectral gap of a
rigorously constructed Hamiltonian — is an open question. The two formulations live in
different mathematical worlds, and bridging them would require substantial further work,
likely involving stochastic quantisation or constructive field theory in four Euclidean
dimensions.

---

## Dependencies

- **Lean 4** (tested with current toolchain)
- **Mathlib** (`Mathlib.Tactic`, `Mathlib.Algebra.Quaternion`, `Mathlib.Analysis.SpecialFunctions.*`, `Mathlib.Topology.*`)
- **LogosLibrary** (internal library; `Superior.Strings.Quaternion`, `Superior.ThermalTime.Basic`, `Superior.YangMills.DivisionAlgebra`)

---

## Architecture

```
DivisionAlgebra.lean          ← Foundation: NDA classification, gauge correspondence
        │
        ├──→ EntropyManifold.lean    ← Physics bridge: thermodynamics, KMS, conserved charges
        │
        └──→ HopfFibration.lean      ← Geometry: Hopf maps, fiber actions, Adams' theorem
                    │
                    └──→ TopologicalMassGap.lean  ← Synthesis: flux closure, mass gap, deconfinement
```

---

## Key Definitions

| Name | Type | Meaning |
|------|------|---------|
| `NDA` | `inductive` | The four normed division algebras |
| `FluxConfig` | `structure` | A flux configuration with winding number, energy, closure |
| `GaugeTheory` | `structure` | A gauge theory with entropy dim, fiber dim, string tension σ |
| `PhysicalState` | `structure` | A flux configuration satisfying the closure constraint |
| `MassGapProof` | `structure` | Complete mass-gap data: theory, Hopf data, gap value |
| `HopfMassGapData` | `structure` | Fiber dimension, S¹ containment, minimum winding energy |
| `TopologicalMass` | `structure` | Van Der Mark template: field scale × winding = mass |
| `EntropyManifoldData` | `structure` | Full pipeline data for a single gauge factor |

---

## Key Theorems

| Name | Statement |
|------|-----------|
| `grand_synthesis` | For σ > 0: QCD gap > 0, SU(2) gap > 0, gaps equal, S¹ mechanism, U(1) exception |
| `yang_mills_mass_gap_exists` | ∃ Δ > 0 equal to the QCD mass gap |
| `mass_gap` | In a confining theory, every nontrivial state has energy > 0 |
| `gap_mechanism_universal` | SU(2) and SU(3) mass gaps are equal at the same σ |
| `s1_fiber_persistence` | S¹ action preserves both components of the quaternionic Hopf map |
| `standard_model_complete` | Every non-trivial NDA ↔ exactly one SM gauge factor |
| `no_fifth_gauge_group` | No Hopf fibration with fiber S¹⁵; no NDA beyond four |
| `confinement_implies_gap` | Confining gauge factor → topological mass gap |
| `gap_decreases_with_temperature` | Below T_c: higher T → smaller gap |
| `entropy_additive` | S(xy) = S(x) + S(y) from norm-composition |
| `zero_divisor_breaks_norm_composition` | Zero divisors are incompatible with entropy accounting |
| `time_dilation_from_entropy` | Lorentz time dilation derived from entropy flow rate transformation |

---

## License

MIT. See `LICENSE`.

---

## Citation

If referencing this work, please cite it as a **formalized reframing** of the mass gap
problem, not as a solution to the Clay Millennium Problem. Precision about claims is not
modesty — it is correctness.

---

*"Maths is truth. Once you discover something in maths, it applies to all eternity."*
— Martin Hairer
