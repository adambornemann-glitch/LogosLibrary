# Introduction to Split Mechanics

**The science of subsystems, formalized in Lean 4**

*Adam Bornemann, Founder 2026*

---

## What Split Mechanics Is

Split Mechanics is an interpretation of quantum mechanics built on one observation:

**Every feature of quantum mechanics that we consider fundamental — the Born rule,
unitarity, the KMS condition, spectral invariance, nontrivial time evolution — is
a consequence of looking at part of a system instead of the whole.**

The total universe in a pure state has none of these features. The modular operator
is trivial (Δ = 1). The modular flow is the identity. Nothing happens. This is the
Wheeler-DeWitt silence: HΨ = 0.

The moment you draw a boundary — system A here, environment B there — the partial
trace takes the pure global state to a mixed reduced state on A. The reduced state
is faithful (because entanglement ensures every observable has nonzero expectation)
and not pure (because entanglement creates mixedness). Therefore Δ_A ≠ 1. And in
that single act, the Tomita-Takesaki theorem delivers everything:

- The **KMS condition** at β = 1 (strip analyticity of correlation functions)
- The **Born rule** in the form ω(a) = ⟨Ω, π(a)Ω⟩ (the GNS representation)
- **Nontrivial modular flow** (time exists — there are observables the dynamics moves)
- **Unitarity** (the modular flow preserves the state)
- **Spectral invariance** (measurement statistics are preserved under evolution)

These five are not independent postulates. They are five faces of one phenomenon:
the nontriviality of the modular operator on a subsystem's reduced state. They
stand or fall together. When Δ = 1, all five degenerate. When Δ ≠ 1, all five ignite.

The name is a play on Wheeler's "It From Bit." The "it" — physics, time, probability,
unitarity — comes from the "split" — the act of drawing a boundary between system
and environment.

---

## Part I: The Subsystem Pentagon

**File: `ItFromSplit.lean` — Foundations of Split Mechanics #1**

### The Pentagon

```
                    KMS
                   ╱   ╲
                  ╱     ╲
          Spectral       Born
         Invariance       Rule
              │    ╲   ╱    │
              │     ╲ ╱     │
              │   Δ ≠ 1     │
              │     ╱ ╲     │
              │    ╱   ╲    │
           Unitarity ─── Self-Adjointness

        All edges are biconditionals.
        All vertices vanish for Δ = 1.
        All vertices ignite for Δ ≠ 1.
```

The center of the pentagon is Δ_A ≠ 1 — the nontriviality of the modular operator.
The generator is entanglement — the partial trace that creates the split. The modulus
is the von Neumann entropy S_A = −Tr(ρ_A log ρ_A) = ⟨K⟩_ω, which measures *how much*
Δ ≠ 1. The pentagon is not binary; it breathes with S_A, which breathes with the
gravitational coupling G.

### The Chain of Reasoning

```
Total universe in pure state (HΨ = 0)
                │
                │  Subsystem decomposition: M_total = M_A ⊗ M_B
                ↓
Partial trace: ω_A = Tr_B(|Ψ⟩⟨Ψ|)
                │
                │  ω_A is faithful (entanglement)
                │  ω_A is normal (automatic for restrictions)
                │  ω_A is NOT pure (entanglement creates mixedness)
                ↓
Tomita-Takesaki theorem: modular data (σ_t, Δ, K = −log Δ)
                │
                │  Δ ≠ 1 because ω_A is mixed and faithful
                ↓
ALL FIVE VERTICES simultaneously:
  KMS at β = 1         (ModularData.kms_at_one)
  Born rule             (every_state_has_born_rule, from GNS)
  Nontrivial flow       (nontrivial_implies_dynamically_nontrivial)
  Unitarity             (ModularData.invariant)
  Spectral invariance   (unitarity_iff_invariance)
                │
                │  Physical conversion
                ↓
τ_C · T = 1/(2π)       (modular_identity)
```

### Key Results

**The Pentagon Theorem** (`pentagon_theorem`). For any faithful normal state with
nontrivial modular operator, all five vertices of the Subsystem Pentagon are
simultaneously nontrivial. Δ ≠ 1 implies everything.

**The Collapse Theorem** (`pentagon_collapse`). When Δ = 1, the modular flow is the
identity and all five vertices degenerate. Spectral invariance holds vacuously (because
nothing moves). Unitarity is trivially true (the identity is unitary). The KMS condition
degenerates (the analytic function is constant). The Born rule loses its measurement
context. Time stops flowing.

**The Emergence Theorem** (`emergence`). Given a pure state on a total system and an
entangled subsystem decomposition, the partial trace simultaneously creates:
faithfulness, normality, the Born rule form, modular data with KMS at β = 1, and
mixedness of the reduced state.

**The Master Theorem** (`it_from_split`). Given a universe in a pure state and a
subsystem decomposition with physical parameters, the partial trace simultaneously
creates all five pentagon vertices, the non-purity of the reduced state, and the
modular identity τ_C · T = 1/(2π).

**The Modulus Theorem** (`entropy_pos_iff_nontrivial`). S_A > 0 if and only if Δ ≠ 1
if and only if the pentagon is inflated. The von Neumann entropy is the quantitative
measure of how much physics the subsystem has.

### Pentagon Edges

| Edge | Theorem |
|------|---------|
| KMS ↔ Born | `kms_iff_born` |
| Modular Flow ↔ KMS | `modular_flow_iff_kms` |
| Self-Adjointness ↔ Unitarity | `stones_theorem_note` |
| Unitarity ↔ Spectral Invariance | `unitarity_iff_invariance` |
| Born ↔ Spectral Invariance | `born_iff_spectral_invariance` |

### Physical Conversion

| Result | Theorem |
|--------|---------|
| τ_C · T = 1/(2π) | `modular_identity` |
| β_physical · T = 1 | `one_kms_cycle` |
| τ_C = 1/(2πT) | `τ_C_eq_inv` |
| T = 1/(2πτ_C) | `T_eq_inv` |
| G → 0 ⟹ τ_C → ∞ | `wdw_limit_τ` (Wheeler-DeWitt recovery) |
| G → 0 ⟹ T → 0 | `wdw_limit_T` |
| G → ∞ ⟹ τ_C → 0 | `classical_limit_τ` |

### Axioms (Part I)

The file axiomatizes standard theorems of operator algebra that would require a full
formalization of von Neumann algebras in Lean to prove from scratch:

| Axiom | Content | Status |
|-------|---------|--------|
| `gns_construction` | GNS theorem | Textbook (1940s) |
| `tomita_takesaki` | Faithful normal states have unique modular data | Textbook (1967/1970) |
| `pure_state_trivial_modular` | Pure states on factors have Δ = 1 | Standard |
| `restriction_faithful` | Reduced state of entangled pure state is faithful | Standard |
| `restriction_normal` | Reduced state of normal state is normal | Automatic |
| `restriction_not_pure` | Reduced state of entangled pure state is mixed | Standard |
| `nontrivial_implies_dynamically_nontrivial` | Δ ≠ 1 implies observables move | From faithfulness |
| `modular_hamiltonian_exists` | Modular Hamiltonian has well-defined entropy | Standard |

None of these encode physical assumptions beyond standard quantum mechanics. The
load-bearing content of Split Mechanics is not hidden in the axioms — it is in the
*architecture*: the recognition that these standard results, composed correctly,
produce the entire structure of quantum mechanics from one act.

---

## Part II: Lorentz-Covariant Bohmian Mechanics

**File: `BohmianMechanics.lean` — Foundations of Split Mechanics #2**

### The Foliation Problem

Bohmian mechanics requires evaluating all particle positions "at the same time."
The guiding equation is defined on a simultaneity surface — a spacelike hypersurface
where "now" is. But special relativity says simultaneity is frame-dependent.

This is the **foliation problem**: Bohmian mechanics appears to require a preferred
foliation of spacetime, breaking Lorentz covariance. The problem has been open since
Bohm's original 1952 formulation. The standard position in the literature is that
Bohmian mechanics is empirically compatible with Lorentz covariance but not manifestly
covariant.

### The Resolution

Two ingredients, both from thermodynamic first principles:

1. **The Ott transformation**: Temperature transforms as energy under Lorentz boosts:
   T' = γT.
2. **Thermal time**: Physical time is derived from modular flow: t = τ/T, where τ is
   the modular parameter (Lorentz invariant) and T is temperature (frame dependent).

From these two facts:

| Quantity | Rest frame | Boosted frame | Transformation |
|----------|-----------|---------------|----------------|
| Energy H | H | γH | Covariant |
| Temperature T | T | γT | Covariant (Ott) |
| Modular Hamiltonian K = H/T | K | γH/γT = K | **Invariant** |
| Quantum potential κ = U_Q/T | κ | γU_Q/γT = κ | **Invariant** |
| Modular parameter τ | τ | τ | **Invariant** |
| Coordinate time t = τ/T | t | τ/γT = t/γ | Time dilation |

The modular parameter τ is Lorentz invariant. "Simultaneity" in the guiding equation
means equal τ, not equal t. All observers agree on τ. The proof is one algebraic
cancellation: K = H/T → γH/(γT) = H/T. In Lean 4, this is `field_simp`.

**There is no foliation problem.** The foliation was never physical. It was an artifact
of writing the guiding equation in coordinate time instead of modular time.

### Connection to the Pentagon

The Bohmian file uses one axiom: `born_rule_is_kms`, the identification of quantum
equilibrium (ρ = |ψ|²) with the KMS condition for the modular Hamiltonian.

**This axiom is discharged by Part I.** In `ItFromSplit.lean`, the theorem
`kms_iff_born` proves that the Born rule form and the KMS condition at β = 1 are
equivalent for any faithful normal state — which is exactly what a subsystem's
reduced state is when entanglement is present.

The Bohmian file's single axiom is a theorem one level down. The foliation problem
was sitting on top of the pentagon the whole time.

### The Thermal Duality

The classical CHSH bound (|S| ≤ 2) and the Tsirelson quantum bound (|S| ≤ 2√2)
are the antisymmetric and symmetric combinations of a single thermal parameter
β = √2 − 1:

| Identity | Value | Physical meaning |
|----------|-------|-----------------|
| β + 1/β | 2√2 | Quantum (Tsirelson) bound |
| 1/β − β | 2 | Classical (Bell) bound |
| β · (1/β) | 1 | Conjugate identity |

The Tsirelson bound is a thermodynamic constraint: the KMS condition limits thermal
correlations to ε ≤ (√2 − 1)/2, giving |S| ≤ 2 + 4ε = 2√2. Classical and quantum
mechanics are not different theories. They are the antisymmetric and symmetric sectors
of one thermal duality.

### Bohm's Implicate and Explicate Orders

Bohm's philosophical distinction is given precise type-theoretic content:

- **Implicate order** = `ImplicateOrder`: the Lorentz-invariant modular variables K, κ
- **Explicate order** = `ExplicateOrder`: the frame-dependent quantities H, U_Q, T, t
- **Unfolding** = multiplication by temperature: `ImplicateOrder.unfold`
- **Enfolding** = division by temperature: `ExplicateOrder.enfold`

The round-trip theorem `enfold_unfold_id` proves the implicate order is the fixed
point of the unfold/enfold cycle. Different temperatures (different frames) produce
different explicate orders from the same implicate order. The implicate order is prior.

### Measurement as Thermalization

Measurement is not instantaneous collapse. It is a thermodynamic process requiring
at least 2π nats of entropy production — one modular cycle. This connects directly
to Part I: one trip around the KMS strip of the pentagon's modular flow.

- `no_instantaneous_measurement`: every measurement takes strictly positive time
- `measurement_time_transforms`: measurement time dilates correctly under boosts
- `bitsPerMeasurement`: one measurement establishes 2π/ln(2) ≈ 9.06 bits

### Key Theorems (Part II)

| Theorem | Statement |
|---------|-----------|
| `modular_hamiltonian_boost_invariant` | K = H/T is Lorentz invariant |
| `modular_quantum_potential_invariant` | κ = U_Q/T is Lorentz invariant |
| `modular_velocity_invariant` | v_mod = v_guide/T is Lorentz invariant |
| `physical_time_dilation` | t' = t/γ derived from Ott + thermal time |
| `implicate_order_boost_invariant` | Boosted system has same implicate order |
| `enfold_unfold_id` | Implicate order is fixed point of frame changes |
| `covariance_complete` | All covariance results simultaneously |
| `tsirelson_from_thermal_constraint` | 2 + 4ε = 2√2 |
| `quantum_bound_from_duality` | β + 1/β = 2√2 |
| `classical_bound_from_duality` | 1/β − β = 2 |
| `chsh_tsirelson_bound` | Any thermal HV model satisfies \|S\| ≤ 2√2 |
| `no_instantaneous_measurement` | Measurement takes positive time |
| `lorentz_covariant_bohmian_mechanics` | The complete master synthesis |

---

## Part III: Objective Reduction

**File: `EProcess.lean` — Foundations of Split Mechanics #3**

The 2π nat entropy threshold from Part II's measurement theory is not specific to
measurement. It is the universal decoherence threshold: the completion of one modular
cycle. In `EProcess.lean`, this is formalized as Diósi-Penrose gravitational
decoherence with a Compton wavelength UV regularization, proving that the same 2π
threshold governs gravitational collapse, chemical decoherence (via `ChemicalMeasurement.lean`),
and nanothermodynamic subdivision (via `CProcess.lean`).

The pentagon's modular flow provides the dynamical context. The entropy modulus S_A
determines the decoherence timescale. The 2π cycle is one trip around the KMS strip.

---

## Part IV: Bell's Theorem and Quantum Contextuality
Directory: `BellsTheorem/` — 26 files, 8,139 lines. Zero `sorry`. One axiom.
Part II derived the Tsirelson bound from thermal duality as a single result inside
`BohmianMechanics.lean`. This directory is the full expansion of that idea: a complete
formalization of Bell's theorem and quantum contextuality bounds within the thermal
framework.
The foundation is an 11-file Lean 4 port of Echenim & Mhalla's Isabelle/HOL
formalization of Bell's theorem and the CHSH inequality (housed in
`QuantumMechanics.BellsTheorem`). The thermal extension adds 8,139 lines across
three subdirectories:

TLHV/ — The thermal hidden variable model. CHSH decomposes as
S = S_classical + S_thermal. The bound |S| ≤ 2 + 4ε recovers Bell (ε = 0) and
Tsirelson (ε = ε_tsirelson) as special cases.
ThermalBell/ — The hidden structure. The classical bound (2) and quantum
bound (2√2) are the antisymmetric and symmetric combinations of the conjugate
pair β = √2 − 1 and 1/β = √2 + 1. Separable states enhance correlations as
O(ε²); entangled states as O(ε). No-signaling forces balanced marginals at
optimality.
OtherInequalities/ — The universal formula. Six additional inequalities
(Mermin, Leggett-Garg, KCBS, CGLMP, I₃₃₂₂) all follow from one principle:
Quantum Bound = Classical Bound / cos(2π / slots), where slots is
determined by the measurement structure. The capstone theorem
`second_law_of_entanglement` unifies all of them.

The single axiom (`kms_constrains_correlation`) states that KMS periodicity
constrains ε ≤ (√2 − 1)/2. All other results — the decomposition, the duality,
the universal formula — are unconditional theorems.
See `BellsTheorem/ReadMe.md` for the full directory
guide, theorem tables, and reading order.

## The Complete Architecture

```
GENERATOR:     Entanglement (causes the split)
                        │
                        ↓
    MODULUS:        S_A = ⟨K⟩_ω ∈ [0, ∞)
                   │                          │
                   │  S_A = 0 ⟺ Δ = 1        │
                   │  (pentagon collapse)     │
                   │                          │
                   │  S_A > 0 ⟺ Δ ≠ 1        │
                   │  (pentagon theorem)      │
                   │                          │
                   ↓                          ↓
    PENTAGON:       KMS ↔ Born ↔ Modular ↔ Unitarity ↔ Spectral
                        │
                        ↓
    CONVERSION:     τ_C · T = 1/(2π)
                        │
              ┌─────────┼──────────┐
              ↓         ↓          ↓
         COVARIANCE  DUALITY   MEASUREMENT
          K → K     β+1/β=2√2  ΔS ≥ 2π
         (Part II)  (Part II)  (Part II/III)
                        │
                        ↓
                   BELL (Part IV)
              26 files, 8,139 lines
                        │
              ┌─────────┼──────────┐
              ↓         ↓          ↓
           CHSH    UNIVERSAL    DUALITY
          |S|≤2+4ε  Q=C/cos θ  β ↔ 1/β
              ↓         ↓          ↓
           Mermin   Leggett    KCBS
           CGLMP    -Garg     I₃₃₂₂
```

### The Dependency Chain

1. **#1: ItFromSplit.lean** — The Subsystem Pentagon. Five faces of Δ ≠ 1 from
   one cause: subsystem decomposition. Proves KMS ↔ Born.
2. **#2: BohmianMechanics.lean** — Uses KMS = Born (now a theorem, not an axiom)
   to ground quantum equilibrium, then resolves the foliation problem via Ott +
   thermal time. Derives the Tsirelson bound thermodynamically.
3. **#3: EProcess.lean** — The 2π nat threshold as one modular cycle. Diósi-Penrose
   regularization. Connects to chemistry and nanothermodynamics.
4. **IV: BellsTheorem/** — Expands the thermal duality from Part II into a complete
   formalization of Bell's theorem and six additional contextuality inequalities.
   Proves the universal formula: Quantum Bound = Classical Bound / cos(2π/slots).
   26 files, 8,139 lines, one axiom.

---

## What Is and Isn't Claimed

### What is claimed

Split Mechanics claims that the five standard features of quantum mechanics (Born rule,
unitarity, KMS condition, spectral invariance, nontrivial time evolution) are not
independent postulates but logically equivalent consequences of subsystem decomposition.
This is a structural observation about the existing mathematical framework of algebraic
quantum field theory. It reorganizes known mathematics; it does not introduce new physics.

Additionally, the foliation problem of Bohmian mechanics is dissolved by writing the
guiding equation in modular time rather than coordinate time, using the Ott temperature
transformation to ensure the modular variables are Lorentz invariant.

### What is not claimed

- **New experimental predictions.** Split Mechanics is an interpretation, not a new
  theory. It makes the same predictions as standard quantum mechanics. Its value is
  conceptual clarity, not empirical novelty.

- **Resolution of all interpretive questions.** The measurement problem is reframed
  (measurement is thermalization, taking positive time proportional to 1/T) but the
  question of why *this particular* subsystem decomposition rather than another is
  not addressed. The preferred split is an input.

- **Empirical distinguishability from standard QM.** In quantum equilibrium, the
  covariant Bohmian theory makes the same predictions as standard Bohmian mechanics,
  which makes the same predictions as standard quantum mechanics.

- **Full formalization of operator algebra.** The GNS and Tomita-Takesaki theorems are
  axiomatized, not proved from Lean primitives. A complete formalization would require
  building von Neumann algebra theory in Mathlib.

---

## Statistics

| | ItFromSplit (#1) | BohmianMechanics (#2) | EProcess (#3) | BellsTheorem (IV) | Total |
|--|-----------------|----------------------|---------------|-------------------|-------|
| Files | 1 | 1 | 1 | 26 | 29 |
| Lines | — | — | — | 8,139 | — |
| Theorems | ~35 | ~40 | — | ~200+ | ~275+ |
| `sorry` | 0 | 0 | 0 | 0 | **0** |
| Axioms | 8 (operator algebra) | 1 (discharged by #1) | — | 1 (KMS constraint) | 9 |

All axioms in Parts I–III encode established results from the mathematical literature.
The single Bell axiom (`kms_constrains_correlation`) is a physical claim: that KMS
periodicity constrains thermal correlations. Everything else is proved from Mathlib
foundations.

---

## References

**Operator Algebras**
- M. Tomita, "Quasi-standard von Neumann algebras" (1967)
- M. Takesaki, "Tomita's theory of modular Hilbert algebras" (1970)
- A. Connes, *Noncommutative Geometry* (1994), Chapter V

**Thermal Time**
- A. Connes & C. Rovelli, "Von Neumann algebra automorphisms and
  time-thermodynamics relation," Class. Quant. Grav. 11 (1994)

**Bohmian Mechanics**
- D. Bohm, "A suggested interpretation of the quantum theory in terms
  of hidden variables," Phys. Rev. 85 (1952)
- D. Bohm, *Wholeness and the Implicate Order* (1980)
- D. Dürr, S. Goldstein, N. Zanghì, "Quantum equilibrium and the origin
  of absolute uncertainty," J. Stat. Phys. 67 (1992)

**Relativistic Thermodynamics**
- H. Ott, "Lorentz-Transformation der Wärme und der Temperatur,"
  Z. Physik 175 (1963)

---

## The Punchline

Quantum mechanics is not a theory about small things. It is not a theory about
measurement. It is not a theory about probability.

Quantum mechanics is what happens when you look at part of a system instead of the whole.

The Born rule is the KMS condition. Unitarity is the First Law. Time is modular flow.
Temperature is how far you are from the global pure state. Entropy measures how much
physics your subsystem has. The foliation problem disappears because the modular
parameter doesn't care about your reference frame. The Tsirelson bound is thermodynamic.
Classical and quantum are two sectors of one duality.

And all of it — every feature we have spent a century arguing about — comes from one act:

Drawing a boundary.

It from split.

---

## License

MIT. See `LICENSE`.

---

*"The notion that all these fragments are separately existent is evidently
an illusion, and this illusion cannot do other than lead to endless conflict
and confusion."*
— David Bohm, *Wholeness and the Implicate Order* (1980)

*"Time is the modular flow of a faithful normal state."*
— Connes & Rovelli (1994)

*"If your theory is found to be against the second law of thermodynamics
I can give you no hope; there is nothing for it but to collapse in
deepest humiliation."*
— Arthur Stanley Eddington
