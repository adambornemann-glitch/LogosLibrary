# Thermal Turing Machine

**A Turing machine where every computational step is thermodynamically accountable.**

## What This Is

A standard Turing machine has states, a tape, and a transition function. A Thermal Turing Machine has all of that plus a thermal reservoir at inverse temperature β, a dissipation function assigning heat output to each transition, and a structural invariant: every logically irreversible step must dissipate at least kT ln 2 of energy.

That structural invariant is Landauer's principle (1961). The framework also captures Bennett's converse (1973): logically reversible computations — those whose transition function is injective — can in principle dissipate zero heat, because the Landauer condition holds vacuously when no transition erases information.

The temperature β is not a free parameter. It is grounded by the KMS (Kubo–Martin–Schwinger) condition on the reservoir state: there exists a C\*-algebra, a dynamics, and a state satisfying the KMS analyticity condition on the strip 0 < Im(z) < β. This means the Landauer bound inherits physical legitimacy from thermal equilibrium rather than from a postulated temperature.

## Status

| File | Lines | `sorry` count | Content |
|------|-------|---------------|---------|
| `Core.lean` | ~514 | 0 | Definitions, Landauer compliance, KMS grounding, entropy production |
| `Lemmas.lean` | ~400 | 0 | Structural lemmas: tape, direction, step iteration, temperature–β algebra, traces |
| `OneBit.lean` | ~666 | 0 | Concrete machines, decision problems, thermodynamic complexity classes |
| `Simple.lean` | ~383 | 0 | One-Bit Bridge Part 1: Bernoulli Fisher geometry meets Landauer |
| `Simplex.lean` | ~496 | 2 | One-Bit Bridge Part 2: refined Landauer bound, bridge inequality |

The two `sorry`s in `Simplex.lean` are:

1. **Gibbs' inequality** (`bernoulliEntropy_le_log2`): H(θ) ≤ ln 2 for Bernoulli(θ). True and provable via log-convexity, but requires machinery not yet built.
2. **π/2 > ln 2** (`fisher_distance_vs_entropy_at_half`): A numerical comparison. True and provable from analysis lemmas, but tedious to discharge without dedicated infrastructure.

Neither sorry blocks any theorem in the core TTM files.

## What Is Proved

### Core framework (sorry-free)

- **Landauer compliance as a structural invariant.** Irreversible transitions must dissipate ≥ T ln 2. This is not postulated globally; it is checked per-transition.
- **Bennett's principle.** A reversible TM is vacuously Landauer-compliant (`reversible_is_landauer_compliant`). Falls out of the type system in three lines.
- **Reversibility ↔ no irreversible transitions.** The equivalence `reversible_iff_forall_not_irreversible` is proved in both directions.
- **Total dissipation bound.** For any valid execution trace: total heat ≥ (number of irreversible steps) × T ln 2 (`landauer_total_bound`). Proved by induction over the trace.
- **Entropy production per step.** Each irreversible step produces at least ln 2 nats of entropy in the reservoir (`irreversible_step_entropy_bound`).
- **KMS grounding.** The `KMSThermalTM` structure ties the machine's β to an actual KMS state on a C\*-algebraic system. Temperature consistency between machine and reservoir is proved.
- **The full stack.** `LandauerMachine` = KMS-grounded + Landauer-compliant. The physically complete thermodynamic computer.

### Concrete machines (sorry-free)

- **Trivial machine** (always halts): reversible, Landauer-compliant, zero dissipation. ✓
- **Bit flipper** (reads and negates one bit): reversible, Landauer-compliant, zero dissipation. ✓
- **Eraser** (unconditionally writes false): irreversible at (start, true). The framework correctly **forces** dissipation ≥ T ln 2 for compliance (`eraser_landauer_iff`). An eraser with insufficient dissipation is provably non-compliant (`eraser_too_cheap_not_compliant`).

The eraser is the key sanity check. The framework says: *you may build an eraser, but physics will charge you for it.*

### One-Bit Bridge (2 sorry, exploratory)

The bridge files investigate the relationship between Landauer's thermodynamic cost and Fisher–Rao geometry on the Bernoulli statistical manifold. The honest finding:

**They measure different things.** The Landauer cost T ln 2 is a worst-case per-bit bound independent of the input distribution. The Fisher distance 2 arcsin(√θ) depends on the prior. The Shannon entropy H(θ) also depends on the prior. They agree (up to T) only at θ = 1/2.

What is proved:

- **Landauer ≥ T × entropy** (`landauer_vs_entropy`): the Landauer bound is at least the information-theoretic cost.
- **Excess is non-negative** (`landauerExcess_nonneg`): the gap T(ln 2 − H(θ)) ≥ 0.
- **Excess vanishes at maximum entropy** (`landauerExcess_zero_at_half`): Landauer is tight when θ = 1/2.
- **Bridge inequality** (`bridge_inequality`): Fisher distance / step size × Landauer cost > 0 as a total cost lower bound.
- **Fisher information minimized at maximum entropy** (`bernoulliFisher_min_at_half`): I(θ) ≥ 4 = I(1/2). The uniform distribution is hardest to learn from. Proved via AM–GM.

The bridge is not "dissipation = T × Fisher distance." It is a three-layer composition: Fisher geometry bounds step count, Landauer bounds cost per step, composition bounds total cost.

### Thermodynamic complexity classes (speculative, sorry-free definitions)

- **`ThermalDecider`**: a TM that decides a language with time and heat bounds.
- **`ThermalP`**: languages decidable in polynomial time with polynomially bounded heat.
- **`ThermalVerifier`**: a polynomial-time verifier with Landauer compliance.
- **`ThermalNP`**: languages with a polynomial-time thermal verifier.

These are well-typed definitions, not theorems. They set the stage but do not yet prove separation results.

## Architecture

```
ThermalTuringMachine/
├── Core.lean          ← Definitions + main theorems
├── Lemmas.lean        ← Structural lemmas
├── OneBit.lean        ← Concrete machines + complexity classes
├── Simple.lean        ← One-Bit Bridge, Part 1
└── Simplex.lean       ← One-Bit Bridge, Part 2
```

**Dependencies:**

- `LogosLibrary.Superior.ThermalTime.InfoTheory` — `natsPerBit`, `landauerCost`
- `LogosLibrary.QuantumMechanics.ModularTheory.KMS.Condition` — `IsKMSState`, `CStarAlgebra`, `Dynamics`
- Mathlib (Analysis, MeasureTheory, Tactic)

The core files (`Core.lean`, `Lemmas.lean`, `OneBit.lean`) import the full Logos Library stack. The bridge files (`Simple.lean`, `Simplex.lean`) are partially self-contained — they redefine `natsPerBit` and `landauerCost` locally for exploration purposes and import only Mathlib.

## The Physical Content

Landauer (1961) showed that erasing one bit costs at least kT ln 2 of heat. Bennett (1973) showed that reversible computations can avoid this cost entirely. Together they tie computation to thermodynamics.

This formalization goes further in one direction: the temperature T is not assumed. It is derived from the KMS condition, which characterizes thermal equilibrium via analytic continuation. The Landauer bound then inherits its physical content from the deepest characterization of temperature available in mathematical physics.

The exploration files ask: can this thermodynamic structure separate P from NP? The answer so far is: the framework can *express* the question precisely (solvers erase failed candidates; verifiers do not), but *proving* that search requires exponentially more erasures than verification is the hard open problem. The gap analysis in `OneBit.lean` §6 is explicit about what is missing.

## Known Limitations

1. **Universe polymorphism in KMSReservoir.** The `grounded` field is existentially quantified over a universe level. This is fine for the current structure but will need a concrete C\*-algebra when you want to discharge the existential.

2. **No output extraction.** The framework defines halting but not "what the machine computed." Needed for language recognition.

3. **No space complexity.** Bennett's reversible simulation trades heat for space. The framework cannot yet express this tradeoff.

4. **No composition.** Sequential and parallel composition of ThermalTMs is not yet defined. Needed for subroutine analysis.

5. **The bridge files redefine constants.** `Simple.lean` and `Simplex.lean` locally redefine `natsPerBit`, `landauerCost`, and `bernoulliEntropy` rather than importing them from the library. This is fine for exploration but should be unified before these files join the main build.

## References

- R. Landauer, "Irreversibility and Heat Generation in the Computing Process", IBM J. Res. Dev. 5(3), 183–191 (1961)
- C.H. Bennett, "Logical Reversibility of Computation", IBM J. Res. Dev. 17(6), 525–532 (1973)
- R. Kubo, "Statistical-Mechanical Theory of Irreversible Processes", J. Phys. Soc. Japan 12, 570–586 (1957)
- P.C. Martin & J. Schwinger, "Theory of Many-Particle Systems. I", Phys. Rev. 115, 1342–1373 (1959)

## Building

```bash
# From the Logos Library root:
lake build LogosLibrary.QuantumComputing.ThermalTuringMachine.Core
lake build LogosLibrary.QuantumComputing.ThermalTuringMachine.Lemmas
lake build LogosLibrary.QuantumComputing.ThermalTuringMachine.OneBit
```

The bridge files (`Simple.lean`, `Simplex.lean`) build independently against Mathlib.
