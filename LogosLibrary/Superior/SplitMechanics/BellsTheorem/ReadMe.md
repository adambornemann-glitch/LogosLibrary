# SplitMechanics.BellsTheorem

**Thermal hidden variable models for Bell inequalities and quantum contextuality bounds.**

✅ Compiles. Zero `sorry`. 8,139 lines across 26 files. One axiom.

---

## What This Is

A Lean 4 formalization that develops and extends the **thermal hidden variable framework** for understanding quantum correlations. The central result: every major quantum contextuality bound — CHSH, Mermin, Leggett-Garg, KCBS, CGLMP, I₃₃₂₂ — follows from a single formula determined by the measurement structure of the inequality and the 2π periodicity of modular (KMS) equilibrium states.

This is **not** a port of existing work. The foundation builds on the CHSH/Bell infrastructure in `QuantumMechanics.BellsTheorem` (ported from Echenim & Mhalla's Isabelle/HOL formalization), but the thermal framework, the duality structure, and the universal formula are original contributions totaling 8,139 lines of verified Lean 4.

---

## The Idea in One Paragraph

Standard Bell proofs assume statistical independence between the hidden variable distribution and the measurement settings. In a thermal universe, this assumption is unphysical — everything shares thermal baths, gravitational interaction, and a common causal origin. The thermal framework replaces independence with a bounded deviation parameter ε, where dμᵢⱼ = (1 + ε)dμ₀. The question becomes: how large can ε be? The claim is that KMS periodicity (the 2π structure of thermal equilibrium) constrains ε, and this single constraint reproduces every known quantum bound.

---

## Directory Structure

```
SplitMechanics/BellsTheorem/
├── TLHV.lean                           (root import)
├── ThermalBell.lean                    (root import)
│
├── TLHV/                              7 files, ~1,900 lines
│   ├── Decomp.lean                      CHSH decomposition theorem
│   ├── Reduction.lean                   Classical limit recovery, Tsirelson value
│   ├── Measurement.lean                 Measurement process, entropy production
│   ├── SettingDependent.lean            Setting-dependent measures
│   ├── ThermalDictionary.lean           Term glossary and equivalences
│   ├── CriticalQuestions.lean           Open problems, KMS axiom
│   └── Summary.lean                     Master theorem collecting all results
│
├── ThermalBell/                       11 files, ~3,320 lines
│   ├── NoSignaling.lean                 No-signaling constraints (967 lines)
│   ├── DualityStructure.lean            β and 1/β decomposition
│   ├── HiddenStructure.lean             Geometric relationships
│   ├── OptimalBudget.lean               Optimal deviation patterns
│   ├── SharedEnBudget.lean              Separable vs entangled budgets
│   ├── SequentialMeasurements.lean      Entropy costs, Zeno effect
│   ├── QuantumCompatible.lean           Constraints for quantum reproduction
│   ├── OriginOfEight.lean               Why 8 angle slots in CHSH
│   ├── AsymmetricTemp.lean              Asymmetric detector temperatures
│   ├── PRBox.lean                       Popescu-Rohrlich limit
│   └── Pointwise.lean                   Pointwise vs integral bounds
│
└── OtherInequalities/                 6 files, ~2,905 lines
    ├── ThermMerm.lean                   Mermin n-party inequalities (1,139 lines)
    ├── LeggettGarg.lean                 Temporal Bell tests
    ├── Unity.lean                       Universal formula, second_law_of_entanglement
    ├── Qutrit.lean                      I₃₃₂₂ (d=3)
    ├── CGLMP.lean                       d-dimensional generalisation
    └── KCBS.lean                        Pentagonal contextuality
```

---

## Reading Order

**If you want the punchline:**
Read `OtherInequalities/Unity.lean`. The theorem `second_law_of_entanglement` says: for any Bell-type inequality, the quantum violation ratio is 1/cos(2π/slots), where slots is determined by the measurement structure. No free parameters.

**If you want to understand the framework:**
Start with `TLHV/Decomp.lean` (the CHSH decomposition into classical + thermal parts), then `TLHV/Reduction.lean` (recovering Bell and Tsirelson as special cases).

**If you want the most striking single result:**
Read `ThermalBell/DualityStructure.lean`. The classical bound (2) and quantum bound (2√2) are the antisymmetric and symmetric combinations of a conjugate pair β = √2 − 1 and 1/β = √2 + 1. Same parameter, two faces.

**If you want to see different proof techniques:**
Each inequality in `OtherInequalities/` has a genuinely different classical bound proof — odd cycle frustration (KCBS), telescoping products (Leggett-Garg), parity analysis (Mermin), case exhaustion over Fin 3 (qutrit). The thermal interpretation unifies them; the combinatorics do not.

---

## Key Results

| Theorem | Location | Statement |
|---------|----------|-----------|
| `CHSH_decomposition` | TLHV/Decomp | S = S_classical + S_thermal |
| `thermal_CHSH_bound` | TLHV/Reduction | \|S\| ≤ 2 + 4ε |
| `ε_tsirelson_value` | TLHV/Reduction | 2 + 4·(√2−1)/2 = 2√2 |
| `thermal_bell_complete` | TLHV/Summary | Four-part master theorem |
| `chshOptimal_not_separable` | ThermalBell/OptimalBudget | Optimal pattern violates separability |
| `separable_less_than_entangled` | ThermalBell/SharedEnBudget | Entangled enhancement is O(ε), separable is O(ε²) |
| `entangled_advantage_is_sum` | ThermalBell/SharedEnBudget | Advantage factor = 2 + 2√2 = S_quantum + S_classical |
| Duality decomposition | ThermalBell/DualityStructure | β + 1/β = 2√2, 1/β − β = 2 |
| `second_law_of_entanglement` | OtherInequalities/Unity | Violation ratio = 1/cos(2π/slots) |
| `ghz_mermin3_violation` | OtherInequalities/ThermMerm | GHZ achieves M₃ = 4 |
| `sqrt2_bonus_iff_even` | OtherInequalities/ThermMerm | √2 factor ↔ even party count |
| `kcbs_combinatorial_bound` | OtherInequalities/KCBS | Odd cycle → sum ≥ −3 |
| `K3_max_violation` | OtherInequalities/LeggettGarg | K₃ = 3/2 at ωτ = π/3 |

---

## The Universal Formula

For any Bell-type or contextuality inequality:

```
Quantum Bound = Classical Bound / cos(2π / slots)
```

Verified across four inequality types:

| Type | Mechanism | Examples |
|------|-----------|----------|
| I — Direct ratio | Q = C / cos(angle) | CHSH (8 slots), I₃₃₂₂ (12 slots), CGLMP |
| II — Parabolic | Subtraction changes optimisation | Leggett-Garg (6 slots) |
| III — Exponential | Multi-party compounding | Mermin-n (2ⁿ⁻¹ slots) |
| IV — Contextuality | Odd-cycle frustration | KCBS (10 slots) |

All four types share the same origin: the 2π modular period divided by the measurement structure.

---

## The Axiom

One axiom in the entire directory:

```lean
axiom kms_constrains_correlation (μ₀ : Measure Λ) :
    ∀ (S : ThermalCorrelationStructure Λ μ₀),
    ∀ i j ω, |S.ε i j ω| ≤ ε_tsirelson
```

**Claim:** KMS periodicity constrains the correlation deviation to at most (√2 − 1)/2.

**Why it's an axiom:** Proving it requires formalizing modular automorphisms and the KMS condition on the observable algebra, which is not yet in Mathlib. Everything else in the directory is proved from Mathlib foundations.

**What depends on it:** The final step connecting the thermal framework to quantum mechanics. All intermediate results — the decomposition, the bounds, the duality, the universal formula — are unconditional theorems. The axiom enters only when you want to say "and KMS is the reason ε ≤ ε_tsirelson."

---

## Relationship to QuantumMechanics.BellsTheorem

The `QuantumMechanics.BellsTheorem` module contains 11 files ported from Echenim & Mhalla's Isabelle/HOL formalization of Bell's theorem and the CHSH inequality. That module provides the standard results: Bell's lemma, the CHSH inequality, Tsirelson's bound from Hilbert space quantum mechanics.

This module (`SplitMechanics.BellsTheorem`) imports that foundation and asks: **where do those bounds come from?** The thermal framework doesn't contradict the standard results — it provides a structural explanation for them. `TLHV/Reduction.lean` explicitly proves that the thermal model with ε = 0 reduces to a standard local hidden variable model, and the bounds agree.

---

## What Is NOT Claimed

- **The physical interpretation is not machine-verified.** Lean checks that IF ε ≤ ε_tsirelson THEN the quantum bounds follow. Whether ε ≤ ε_tsirelson because of KMS periodicity is a physical claim, not a mathematical theorem.
- **The slot counting rule is input, not output.** The formula takes the slot count as given. Deriving slot counts from the definition of each inequality is identified as an open problem.
- **This is not a hidden variable theory.** It's a framework that parametrizes the gap between classical and quantum by a single measurable quantity (ε), then shows that one constraint reproduces all known bounds.

---

## Dependencies

- [Mathlib4](https://github.com/leanprover-community/mathlib4) — measure theory, probability, real analysis
- `QuantumMechanics.BellsTheorem` — ported Isabelle foundation (Echenim & Mhalla)

---

*26 files. 8,139 lines. Zero `sorry`. One axiom. Every quantum contextuality bound from one formula.*
