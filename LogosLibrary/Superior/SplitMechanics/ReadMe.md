# Split Mechanics: It From Split

**The Subsystem Pentagon, formalized in Lean 4**

*Adam Bornemann, 2026*

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

## The Subsystem Pentagon

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

## The Chain of Reasoning

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

## What Is Proved

### The Pentagon Theorem (`pentagon_theorem`)

For any faithful normal state with nontrivial modular operator, all five vertices
of the Subsystem Pentagon are simultaneously nontrivial. This is the forward
direction: Δ ≠ 1 implies everything.

### The Collapse Theorem (`pentagon_collapse`)

When Δ = 1, the modular flow is the identity and all five vertices degenerate.
Spectral invariance holds vacuously (because nothing moves). Unitarity is trivially
true (the identity is unitary). The KMS condition degenerates (the analytic function
is constant). The Born rule loses its measurement context. Time stops flowing.

### The Emergence Theorem (`emergence`)

Given a pure state on a total system and an entangled subsystem decomposition, the
partial trace simultaneously creates: faithfulness, normality, the Born rule form,
modular data with KMS at β = 1, and mixedness of the reduced state.

### The Master Theorem (`it_from_split`)

The complete result. Given a universe in a pure state and a subsystem decomposition
with physical parameters, the partial trace simultaneously creates all five pentagon
vertices, the non-purity of the reduced state, and the modular identity τ_C · T = 1/(2π).

### The Modulus Theorem (`entropy_pos_iff_nontrivial`)

S_A > 0 if and only if Δ ≠ 1 if and only if the pentagon is inflated. The von Neumann
entropy is the quantitative measure of how much physics the subsystem has.

### Pentagon Edges (Biconditionals)

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

### Degenerate Cases

| Result | Theorem |
|--------|---------|
| Pure state ⟹ trivial modular flow | `pure_state_no_time` |
| Trivial flow ⟹ vacuous invariance | `trivial_flow_trivial_invariance` |
| Trivial flow + tracial ⟹ degenerate KMS | `trivial_flow_degenerate_kms` |

## What Is Axiomatized

The file axiomatizes the standard theorems of operator algebra theory that would require
a full formalization of von Neumann algebras in Lean to prove from scratch:

| Axiom | Mathematical content | Status |
|-------|---------------------|--------|
| `gns_construction` | The GNS theorem: every state has a Hilbert space representation | Textbook (1940s) |
| `tomita_takesaki` | Faithful normal states have unique modular data | Textbook (1967/1970) |
| `pure_state_trivial_modular` | Pure states on factors have Δ = 1 | Standard |
| `restriction_faithful` | Reduced state of entangled pure state is faithful | Standard |
| `restriction_normal` | Reduced state of normal state is normal | Automatic |
| `restriction_not_pure` | Reduced state of entangled pure state is mixed | Standard |
| `nontrivial_implies_dynamically_nontrivial` | Δ ≠ 1 implies observables move | From faithfulness |
| `modular_hamiltonian_exists` | Modular Hamiltonian has well-defined entropy | Standard |

These are all established results in the mathematical literature. None encode physical
assumptions beyond standard quantum mechanics. The load-bearing content of Split Mechanics
is not hidden in the axioms — it is in the *architecture*: the recognition that these
standard results, composed correctly, produce the entire structure of quantum mechanics
from one act (the partial trace).

## Relationship to the Rest of the Library

This file is **Foundations of Split Mechanics #1**. It provides the base on which:

- **#2 (BohmianMechanics.lean)**: The `born_rule_is_kms` axiom in the Bohmian file
  is the content of `kms_iff_born` here — a *theorem*, not an axiom. The Bohmian
  file's single axiom is discharged by the Split Mechanics foundation. Lorentz
  covariance, measurement as thermalization, and the thermal duality all sit on
  the pentagon.

- **#3 (EProcess.lean)**: The objective reduction threshold (2π nats of entropy
  production) is the completion of one modular cycle — one trip around the KMS strip.
  The pentagon's modular flow provides the dynamical context in which decoherence
  occurs. The entropy modulus S_A determines the decoherence timescale.

- **The nanothermodynamics files**: Hill's subdivision potential as restricted modular
  flow is the *physical conversion* arm of the pentagon: τ_C · T = 1/(2π) expressed
  in thermodynamic language.

## What Is and Isn't Claimed

### What is claimed

Split Mechanics claims that the five standard features of quantum mechanics (Born rule,
unitarity, KMS condition, spectral invariance, nontrivial time evolution) are not
independent postulates but logically equivalent consequences of subsystem decomposition.
This is a structural observation about the existing mathematical framework of algebraic
quantum field theory (Tomita-Takesaki, GNS, Stone's theorem). It reorganizes known
mathematics; it does not introduce new physics.

### What is not claimed

- **New experimental predictions.** Split Mechanics is an interpretation, not a new
  theory. It makes the same predictions as standard quantum mechanics. Its value is
  conceptual clarity, not empirical novelty.

- **Resolution of all interpretive questions.** The measurement problem is reframed
  (measurement is thermalization, taking positive time proportional to 1/T) but
  the question of why *this* subsystem decomposition rather than another is not
  addressed. The preferred split is an input.

- **Full formalization of the axiomatized results.** The GNS theorem, Tomita-Takesaki
  theorem, and related operator-algebraic results are axiomatized, not proved from
  first principles in Lean. A complete formalization would require building the
  theory of von Neumann algebras in Mathlib, which is a separate (large) project.

## Statistics

| Metric | Value |
|--------|-------|
| Theorems | ~35 |
| `sorry` | 0 |
| Axioms | 8 (all standard operator algebra results) |

## The Punchline

Quantum mechanics is not a theory about small things. It is not a theory about
measurement. It is not a theory about probability.

Quantum mechanics is what happens when you look at part of a system instead of the whole.

The Born rule is the KMS condition. Unitarity is the First Law. Time is modular flow.
Temperature is how far you are from the global pure state. Entropy measures how much
physics your subsystem has. And all of it — every feature we have spent a century
arguing about — comes from one act: drawing a boundary.

It from split.

---

## License

MIT. See `LICENSE`.

---

*"The notion that all these fragments are separately existent is evidently
an illusion."* — David Bohm

*"Time is the modular flow of a faithful normal state."* — Connes & Rovelli
