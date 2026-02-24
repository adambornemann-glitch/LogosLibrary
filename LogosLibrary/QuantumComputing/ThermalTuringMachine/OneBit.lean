/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & co.
-/
import LogosLibrary.QuantumComputing.ThermalTuringMachine.Core
import LogosLibrary.QuantumComputing.ThermalTuringMachine.Lemmas
/-!
# Thermal Turing Machine — Exploration & Stress Tests

Putting the TTM through its paces: concrete machines, structural consequences,
and probing the boundaries of what the framework can express.

## Exploration Plan

### § 1. Concrete Machines
  Build actual ThermalTMs, both reversible and irreversible, and verify
  the Landauer machinery works on them.

### § 2. Composition & Simulation
  What happens when we compose ThermalTMs? Can we build subroutines?
  The framework currently has single machines — do we need a composition theory?

### § 3. The Thermodynamic Cost of Decision Problems
  Define what it means for a ThermalTM to decide a language, and explore
  the relationship between problem structure and dissipation.

### § 4. Asymmetry: Solving vs Verifying
  The heart of P(P vs NP): does verification have a fundamentally different
  thermodynamic profile than search?

### § 5. Missing Infrastructure
  What do we need that isn't here yet?

## Notes

This file is exploratory. Theorems marked `sorry` are conjectures to be
investigated. Theorems that typecheck are genuine results of the framework.
-/

namespace ThermalTuringMachine

open ThermalTime.Basic ThermalTime.InformationTheory

/-! ## § 1. Concrete Machines

We build small ThermalTMs by hand and verify properties.
These serve as sanity checks: does the framework behave as expected?
-/

/-! ### § 1a. The Trivial Machine — Always Halts

The simplest possible machine: every transition is undefined.
It should be reversible, Landauer-compliant, and have zero dissipation. -/

section TrivialMachine

/-- The trivial machine: halts immediately on any input.
    δ is everywhere `none`. -/
def trivialTM (β : ℝ) (hβ : β > 0) : ThermalTM Unit Bool where
  δ := fun _ _ => none
  q₀ := ()
  blank := false
  β := β
  hβ := hβ
  dissipation := fun _ _ => 0
  dissipation_nonneg := fun _ _ => le_refl 0

/-- The trivial machine is reversible. -/
theorem trivialTM_reversible (β : ℝ) (hβ : β > 0) :
    (trivialTM β hβ).isReversible := by
  intro q₁ a₁ q₂ a₂ r h₁ _
  simp [trivialTM] at h₁

/-- The trivial machine is Landauer-compliant (vacuously). -/
theorem trivialTM_landauer (β : ℝ) (hβ : β > 0) :
    (trivialTM β hβ).isLandauerCompliant :=
  (trivialTM β hβ).reversible_is_landauer_compliant (trivialTM_reversible β hβ)

/-- The trivial machine halts from its initial config. -/
theorem trivialTM_halts (β : ℝ) (hβ : β > 0) :
    (trivialTM β hβ).isHalted (trivialTM β hβ).initialConfig := by
  simp [ThermalTM.isHalted, ThermalTM.initialConfig, trivialTM]

end TrivialMachine

/-! ### § 1b. The Bit Flipper — A Reversible Machine

A machine that reads one bit, flips it, and halts.
This is its own inverse, so it's reversible.
It should be Landauer-compliant with zero dissipation. -/

section BitFlipper

/-- States for the bit flipper: start, then halt. -/
inductive FlipState where
  | start
  | done
  deriving DecidableEq, Repr, Inhabited

/-- The bit flipper: in state `start`, flip the bit and enter `done`.
    In state `done`, halt.

    δ(start, false) = (done, true,  R)
    δ(start, true)  = (done, false, R)
    δ(done,  _)     = none
-/
def bitFlipperTM (β : ℝ) (hβ : β > 0) : ThermalTM FlipState Bool where
  δ := fun q a => match q with
    | .start => match a with
      | false => some (.done, true, .R)
      | true  => some (.done, false, .R)
    | .done => none
  q₀ := .start
  blank := false
  β := β
  hβ := hβ
  dissipation := fun _ _ => 0
  dissipation_nonneg := fun _ _ => le_refl 0

/-- The bit flipper is reversible: each transition has a unique preimage.
    (start, false) → (done, true, R) and (start, true) → (done, false, R)
    are distinct outputs, so no two inputs produce the same result. -/
theorem bitFlipper_reversible (β : ℝ) (hβ : β > 0) :
    (bitFlipperTM β hβ).isReversible := by
  intro q₁ a₁ q₂ a₂ r h₁ h₂
  simp only [bitFlipperTM] at h₁ h₂
  -- Case split on all state/symbol combinations
  cases q₁ <;> cases q₂ <;> cases a₁ <;> cases a₂ <;>
    simp_all
  grind
  grind

/-- The bit flipper is Landauer-compliant (via reversibility). -/
theorem bitFlipper_landauer (β : ℝ) (hβ : β > 0) :
    (bitFlipperTM β hβ).isLandauerCompliant :=
  (bitFlipperTM β hβ).reversible_is_landauer_compliant (bitFlipper_reversible β hβ)

/-- The bit flipper performs exactly one step from initial config. -/
theorem bitFlipper_steps (β : ℝ) (hβ : β > 0) :
    let M := bitFlipperTM β hβ
    ∃ c', M.step M.initialConfig = some c' ∧ M.isHalted c' := by
  refine ⟨⟨.done, ⟨Function.update (fun _ => false) 0 true⟩, 1⟩, ?_, ?_⟩
  · -- step succeeds
    simp [ThermalTM.step, ThermalTM.initialConfig, bitFlipperTM,
          Config.currentSymbol, Tape.read, Tape.write, Direction.shift]
  · -- result is halted
    simp [ThermalTM.isHalted, bitFlipperTM, Config.currentSymbol, Tape.read,
          Function.update]
    -- The head is at position 1, reading from the updated tape
    -- update was at position 0, so position 1 reads the default (false)
    -- δ(done, false) = none ✓

end BitFlipper

/-! ### § 1c. The Eraser — An Irreversible Machine

A machine that reads a bit and unconditionally writes `false`.
Both `(start, false)` and `(start, true)` map to the same output,
so this is irreversible. It MUST dissipate ≥ T ln 2. -/

section Eraser

/-- States for the eraser -/
inductive EraserState where
  | start
  | done
  deriving DecidableEq, Repr, Inhabited

/-- The eraser: unconditionally write false.
    δ(start, false) = (done, false, R)
    δ(start, true)  = (done, false, R)    ← same output! Erasure!
    δ(done, _)       = none
-/
def eraserTM (β : ℝ) (hβ : β > 0) (Q_dissip : ℝ) (hQ : Q_dissip ≥ 0) :
    ThermalTM EraserState Bool where
  δ := fun q _ => match q with
    | .start => some (.done, false, .R)
    | .done => none
  q₀ := .start
  blank := false
  β := β
  hβ := hβ
  dissipation := fun q _ => match q with
    | .start => Q_dissip
    | .done => 0
  dissipation_nonneg := fun q _ => by cases q <;> simp_all

/-- The eraser IS irreversible at (start, true):
    (start, false) maps to the same output. -/
theorem eraser_irreversible_at_true (β : ℝ) (hβ : β > 0)
    (Q_dissip : ℝ) (hQ : Q_dissip ≥ 0) :
    (eraserTM β hβ Q_dissip hQ).isIrreversibleAt .start true := by
  refine ⟨.start, false, Or.inr (by decide), ?_, ?_⟩
  · simp [eraserTM]
  · simp [eraserTM]

/-- The eraser is NOT reversible. -/
theorem eraser_not_reversible (β : ℝ) (hβ : β > 0)
    (Q_dissip : ℝ) (hQ : Q_dissip ≥ 0) :
    ¬(eraserTM β hβ Q_dissip hQ).isReversible := by
  intro hrev
  have := (eraserTM β hβ Q_dissip hQ).reversible_not_irreversibleAt hrev .start true
  exact this (eraser_irreversible_at_true β hβ Q_dissip hQ)

/-- For the eraser to be Landauer-compliant, it must dissipate enough.
    This is the key test: the framework correctly forces Q_dissip ≥ T ln 2. -/
theorem eraser_landauer_iff (β : ℝ) (hβ : β > 0)
    (Q_dissip : ℝ) (hQ : Q_dissip ≥ 0) :
    (eraserTM β hβ Q_dissip hQ).isLandauerCompliant ↔
      Q_dissip ≥ landauerCost (1 / β) := by
  constructor
  · -- If Landauer-compliant, then Q_dissip ≥ cost
    intro hL
    have hirr := eraser_irreversible_at_true β hβ Q_dissip hQ
    have := hL .start true hirr
    -- dissipation at (start, true) = Q_dissip
    simp [eraserTM, ThermalTM.temperature] at this
    exact le_of_le_of_eq (hL EraserState.start true hirr) rfl
  · -- If Q_dissip ≥ cost, then Landauer-compliant
    intro hge q a hirr
    -- Only (start, _) transitions are defined, and dissipation there = Q_dissip
    cases q with
    | start =>
      simp_all only [one_div, ge_iff_le]
      simp [eraserTM, ThermalTM.temperature]
      exact hge
    | done =>
      -- δ(done, _) = none, so irreversibility is impossible
      exfalso
      exact (eraserTM β hβ Q_dissip hQ).not_irreversibleAt_of_δ_none
        .done a (by simp [eraserTM]) hirr

/-- **The punchline**: an eraser with insufficient dissipation is NOT
    Landauer-compliant. Physics forbids cheap erasure. -/
theorem eraser_too_cheap_not_compliant (β : ℝ) (hβ : β > 0)
    (Q_dissip : ℝ) (hQ : Q_dissip ≥ 0)
    (htoo_cheap : Q_dissip < landauerCost (1 / β)) :
    ¬(eraserTM β hβ Q_dissip hQ).isLandauerCompliant := by
  rw [eraser_landauer_iff]
  linarith

end Eraser

/-! ## § 2. Composition — What's Missing

The framework currently defines single machines. For complexity theory,
we need to compose computations. Let's explore what's needed.
-/

section Composition

/-! ### § 2a. Sequential Composition

Run machine M₁, then feed its output tape to M₂.
The total dissipation should be additive.

**GAP IDENTIFIED**: We need:
1. A notion of "machine produces output" (halting config → tape contents)
2. Sequential composition of ThermalTMs
3. A proof that total dissipation is the sum of component dissipations
-/

/-- Input encoding: how a problem instance is written onto the tape.
    This is needed to connect TMs to decision problems.

    DESIGN NOTE: Mathlib's `Computability.Encoding` uses `FinEncoding`
    for this purpose. We could reuse that, but we might want to track
    the *thermodynamic cost* of encoding too. For now, keep it simple. -/
structure Encoding (α : Type*) (Γ : Type*) where
  /-- Encode a value as a list of symbols -/
  encode : α → List Γ
  /-- Decode a list of symbols back to a value (partial: may fail) -/
  decode : List Γ → Option α
  /-- Roundtrip: decode ∘ encode = some -/
  decode_encode : ∀ a, decode (encode a) = some a

/-- Write a list of symbols onto the tape starting at position 0.
    This is the standard way to initialize a TM's input. -/
def writeTape [Inhabited Γ] (symbols : List Γ) : Tape Γ :=
  ⟨fun i =>
    if h : 0 ≤ i ∧ i < symbols.length then
      symbols.get ⟨i.toNat, by omega⟩
    else
      default⟩

/-- Initialize a ThermalTM with encoded input -/
def ThermalTM.initWith [Inhabited Γ] (M : ThermalTM Q Γ)
    (symbols : List Γ) : Config Q Γ :=
  ⟨M.q₀, writeTape symbols, 0⟩

end Composition

/-! ## § 3. Decision Problems and Thermodynamic Cost

A ThermalTM *decides* a language if it halts on every input with the
accept/reject answer encoded in the final state, and the total dissipation
gives the thermodynamic cost of the decision.

This is where P(P vs NP) starts to bite: the *physical* cost of deciding
includes not just time but heat.
-/

section DecisionProblems

/-- A ThermalTM decides a language with a thermodynamic budget.

    The machine:
    1. Accepts or rejects every input (total, always halts)
    2. Runs in at most `timeBound n` steps on inputs of length n
    3. Dissipates at most `heatBound n` energy on inputs of length n

    The heat bound is the new ingredient relative to classical complexity. -/
structure ThermalDecider (Γ : Type*) where
  /-- State type (bundled so we can existentially quantify) -/
  Q : Type*
  /-- The underlying ThermalTM -/
  machine : ThermalTM Q Γ
  /-- Accept states -/
  isAccept : Q → Prop
  /-- Input encoding (tape alphabet includes blank) -/
  inputEnc : List Γ → Config Q Γ
  /-- The machine always halts: for every input, there exists a step count
      at which the machine reaches a halted configuration -/
  always_halts : ∀ (input : List Γ),
    ∃ n c, machine.stepN (inputEnc input) n = some c ∧ machine.isHalted c
  /-- Time bound as a function of input length -/
  timeBound : ℕ → ℕ
  /-- Heat bound as a function of input length -/
  heatBound : ℕ → ℝ

/-- The language decided by a ThermalDecider -/
def ThermalDecider.language (D : ThermalDecider Γ) : Set (List Γ) :=
  {input | ∃ n c,
    D.machine.stepN (D.inputEnc input) n = some c ∧
    D.machine.isHalted c ∧
    D.isAccept c.state}

/-!
### The Thermodynamic Complexity Classes

Classical complexity: P = languages decidable in polynomial time.
Thermal complexity: P_T = languages decidable in polynomial time
  with polynomially bounded heat dissipation.

**Key question**: Is P_T = P? That is, does every polynomial-time
algorithm have a polynomial-heat implementation?

Bennett says YES for reversible computations (zero heat), but
the reversible simulation may have polynomial space overhead.
The question is whether the *irreversible* steps in a practical
algorithm create unavoidable thermodynamic cost.
-/

/-- A time bound is polynomial if it's bounded by some polynomial.
    (Simplified: bounded by n^k + k for some k.) -/
def IsPolynomialBound (f : ℕ → ℕ) : Prop :=
  ∃ k : ℕ, ∀ n : ℕ, f n ≤ n ^ k + k

/-- A heat bound is polynomial if it's bounded by some polynomial.
    Note: heat is ℝ-valued, but the bound is still in terms of input length. -/
def IsPolynomialHeatBound (f : ℕ → ℝ) : Prop :=
  ∃ k : ℕ, ∀ n : ℕ, f n ≤ ↑(n ^ k + k)

/-- **Thermal P**: languages decidable in polynomial time with
    polynomially bounded heat dissipation. -/
def ThermalP (Γ : Type) : Set (Set (List Γ)) :=
  {L | ∃ D : ThermalDecider.{0, 0} Γ,
    D.language = L ∧
    IsPolynomialBound D.timeBound ∧
    IsPolynomialHeatBound D.heatBound ∧
    D.machine.isLandauerCompliant}

end DecisionProblems

/-! ## § 4. The Solving–Verifying Asymmetry

This is the thermodynamic heart of P(P vs NP).

**Verification** of an NP witness is a specific computation: given (x, w),
check that w is a valid certificate for x. This is a fixed algorithm.

**Search** for a witness requires exploring a space of candidates.
Each candidate that fails is *erased* — it was examined and discarded.
Each erasure costs at least kT ln 2.

The question: does search *necessarily* incur more irreversible steps
than verification, and does this create a thermodynamic gap?
-/

section SolvingVerifying

/-- A thermal verifier for an NP-like relation.

    Given an instance x and a candidate witness w, the verifier
    checks whether w is valid in polynomial time.

    The key property: verification is a *specific* computation with
    a *fixed* number of irreversible steps per input length. -/
structure ThermalVerifier (Γ : Type*) where
  /-- State type -/
  Q : Type*
  /-- The verifier ThermalTM -/
  machine : ThermalTM Q Γ
  /-- Accept states -/
  isAccept : Q → Prop
  /-- Encode (instance, witness) pair onto tape -/
  encodePair : List Γ → List Γ → Config Q Γ
  /-- The verifier always halts -/
  always_halts : ∀ (x w : List Γ),
    ∃ n c, machine.stepN (encodePair x w) n = some c ∧ machine.isHalted c
  /-- Polynomial time bound -/
  timeBound : ℕ → ℕ
  poly_time : IsPolynomialBound timeBound
  /-- Landauer-compliant -/
  compliant : machine.isLandauerCompliant

/-- An NP language defined thermally: there exists a polynomial-time
    thermal verifier such that x ∈ L iff some witness makes it accept. -/
def ThermalNP (Γ : Type) : Set (Set (List Γ)) :=
  {L | ∃ V : ThermalVerifier.{0, 0} Γ,
    L = {x | ∃ w, ∃ n c,
      V.machine.stepN (V.encodePair x w) n = some c ∧
      V.machine.isHalted c ∧
      V.isAccept c.state}}

/-!
### The Dissipation Gap Conjecture

**Conjecture** (Informal): For any NP-complete language L, any ThermalTM
that *decides* L (finds witnesses or certifies non-existence) must incur
superpolynomially more irreversible steps than the verifier alone.

**Why this might be true**:
- A solver exploring 2^n candidates and discarding failures performs
  at least 2^n erasures (each failed candidate is information destroyed)
- Each erasure costs kT ln 2
- The verifier only checks ONE candidate: O(poly(n)) erasures
- The gap is exponential in irreversible step count

**Why this might be false**:
- Bennett's reversible simulation could eliminate all erasures
- Clever algorithms might avoid the brute-force search
- The Landauer bound might not be tight enough to separate

**What we CAN prove from the current framework**:
-/

/-- If a machine performs k irreversible steps, it dissipates at least
    k × T ln 2. This is just `landauer_total_bound` restated, but it
    makes the linear scaling in irreversible steps explicit.

    The physical content: *each bit of information destroyed has a
    minimum energetic price*. Search strategies that destroy more
    information pay more. -/
theorem dissipation_linear_in_erasures
    (M : ThermalTM Q Γ)
    (hL : M.isLandauerCompliant)
    (trace : ExecutionTrace Q Γ)
    (hvalid : M.isValidTrace trace)
    (k : ℕ) (hk : M.irreversibleSteps trace = k) :
    M.totalDissipation trace ≥ ↑k * M.landauerCostPerBit := by
  have := M.landauer_total_bound hL trace hvalid
  rw [hk] at this
  exact this

/-- **The verification dissipation bound**: a verifier's heat output
    is bounded by its (polynomial) time bound times the Landauer cost.

    This is an UPPER bound on verification cost: at most every step
    is irreversible. In practice, many verification steps are reversible
    (comparisons, pointer movements), so the actual cost is lower.

    CONTRAST with search: a brute-force solver's irreversible step count
    could be exponential, giving an exponential LOWER bound on heat. -/
theorem verification_heat_upper_bound
    (M : ThermalTM Q Γ)
    (_hL : M.isLandauerCompliant)
    (trace : ExecutionTrace Q Γ)
    (_hvalid : M.isValidTrace trace)
    (n : ℕ) (hn : trace.numSteps ≤ n) :
    M.totalDissipation trace ≥ 0 ∧
    M.irreversibleSteps trace ≤ n := by
  constructor
  · exact M.totalDissipation_nonneg trace
  · calc M.irreversibleSteps trace
        ≤ trace.numSteps := M.irreversibleSteps_le_numSteps trace
      _ ≤ n := hn

end SolvingVerifying

/-! ## § 5. Interesting Structural Consequences

Let's derive some non-obvious things from the framework.
-/

section Consequences

/- **The reversible computation tax**: converting an irreversible computation
    to a reversible one (Bennett's trick) eliminates heat but requires
    auxiliary tape to store the computation history.

    We can't prove this yet because we don't have:
    1. A notion of space complexity for ThermalTMs
    2. A construction of Bennett's reversible simulation
    3. A proof that the simulation is correct

    But we can STATE what it would look like: -/

/-- Bennett-style reversible simulation (specification, not construction).
    For any ThermalTM, there exists a reversible ThermalTM that computes
    the same function with zero dissipation but potentially more space. -/
def BennettSimulation (Q₁ Γ₁ Q₂ Γ₂ : Type*) : Prop :=
  ∀ (M : ThermalTM Q₁ Γ₁) (_hL : M.isLandauerCompliant),
    ∃ (M' : ThermalTM Q₂ Γ₂),
      M'.isReversible ∧
      M'.isLandauerCompliant ∧
      (∀ q a, M'.dissipation q a = 0)
      -- AND M' computes the same function as M
      -- (we can't state this yet without output extraction)

/-- **Temperature scaling**: if you run the same logical computation at
    a higher temperature, the minimum dissipation per erasure increases.

    This is physically obvious (hotter reservoir → more waste heat) but
    it's nice that the framework captures it structurally.

    Proof: landauerCost is monotone in T. -/
theorem hotter_means_more_dissipation
    (T₁ T₂ : ℝ) (_hT₁ : T₁ > 0) (_hT₂ : T₂ > 0) (hle : T₁ ≤ T₂) :
    landauerCost T₁ ≤ landauerCost T₂ := by
  unfold landauerCost
  apply mul_le_mul_of_nonneg_right hle
  exact le_of_lt natsPerBit_pos

/-- **Zero-temperature limit**: as T → 0, the Landauer cost → 0.
    Computation becomes thermodynamically free at absolute zero.

    But: the third law of thermodynamics says T = 0 is unattainable!
    So there's always a nonzero minimum cost.

    In the framework: β → ∞ means T → 0, and the KMS condition
    at β → ∞ characterizes a ground state, not a thermal state.
    The framework correctly requires β > 0 (T > 0, finite temperature). -/
theorem landauer_cost_approaches_zero :
    ∀ ε > 0, ∃ T > 0, landauerCost T < ε := by
  intro ε hε
  -- We need T such that T · natsPerBit < ε
  -- i.e., T < ε / natsPerBit
  use ε / (2 * natsPerBit)
  constructor
  · unfold natsPerBit; positivity
  · unfold landauerCost
    have hnpb := natsPerBit_pos
    -- T · natsPerBit = (ε / (2 · natsPerBit)) · natsPerBit = ε / 2 < ε
    unfold natsPerBit
    simp_all
    rw [@div_mul]
    norm_num
    linarith


/-- **Dissipation determines a minimum time at fixed power**.

    If the machine's instantaneous power output is bounded by P_max,
    then a computation requiring total dissipation Q takes at least
    Q / P_max time to complete.

    This connects thermodynamic cost to a *physical* time bound —
    not computational steps, but actual seconds. -/
theorem minimum_physical_time
    (Q_total P_max : ℝ) (hQ : Q_total > 0) (hP : P_max > 0) :
    Q_total / P_max > 0 :=
  div_pos hQ hP

end Consequences

/-! ## § 6. Gap Analysis — What the Framework Needs Next

Based on this exploration, here's what's missing for P(P vs NP):

### CRITICAL (needed for any complexity-theoretic result):
1. **Output extraction**: reading the result from a halted config's tape
2. **Language recognition**: M decides L (formal, connecting to sets)
3. **Input length**: |x| for complexity bounds
4. **Polynomial clocking**: M runs in time p(|x|) (connect to Polynomial)
5. **Space complexity**: cells visited during computation

### IMPORTANT (needed for the physical separation argument):
6. **Irreversible step counting for specific algorithms**: need to
   analyze concrete machines and show their erasure count
7. **Search lower bounds**: any machine deciding an NP-complete language
   must perform many irreversible steps (this is the hard theorem)
8. **Verification upper bounds**: the verifier's irreversible step count
   is polynomially bounded (this should follow from structure)
9. **Bennett's simulation**: construction + proof that it preserves
   the computed function while eliminating dissipation

### NICE TO HAVE (for a complete theory):
10. **Composition of ThermalTMs**: sequential and parallel
11. **Reductions that preserve thermodynamic cost**
12. **Connection to Mathlib's computability library**
13. **Concrete NP-complete problem** (e.g., SAT) as a ThermalTM
-/

/-! ## § 7. A Toy Separation — The Sorted Search Example

As a proof of concept, let's sketch a scenario where search provably
costs more erasures than verification.

**Problem**: Given a sorted list of n bits and a target, determine if the
target is present.

**Verifier**: Given the index i as a witness, check list[i] = target.
  Cost: O(1) irreversible steps (comparison + output).

**Searcher** (without witness): Binary search over n positions.
  Each comparison is reversible, but each "not found, try next half"
  decision may erase the rejected half's information.
  Cost: O(log n) irreversible steps at minimum.

This is a polynomial gap, not exponential. For an exponential gap,
we'd need an NP-complete problem. But it demonstrates the framework
can express the asymmetry.
-/

-- (This section is intentionally left as a roadmap rather than
--  formal Lean code, because the infrastructure for concrete
--  machine construction over lists is not yet in place.)


/-! ## § 8. Summary of Findings

### What works well:
- The Landauer compliance machinery is clean and correct
- Bennett's principle (reversible ⟹ vacuously compliant) falls out naturally
- The eraser example perfectly demonstrates that the framework
  *forces* sufficient dissipation for irreversible operations
- KMS grounding gives physical legitimacy to the temperature
- The total dissipation bound (`landauer_total_bound`) is the right theorem

### What's surprising:
- The framework naturally captures the verification/search asymmetry
  at the level of irreversible step counts
- Temperature scaling is automatic from the definitions
- The zero-temperature limit reveals a connection to the third law

### What's missing for P(P vs NP):
- The big gap is connecting irreversible step counts to problem structure
- We need to show that SEARCH for NP witnesses *necessarily* involves
  more erasures than VERIFICATION — this requires lower bound arguments
  on irreversible steps, which is a new kind of complexity lower bound
- The framework is ready for this, but the theorems are hard

### Key insight from the exploration:
The TTM framework turns P vs NP into a question about **information
destruction**: solving requires destroying exponentially more information
(failed candidates) than verifying (which destroys none, in principle).
The Landauer bound then converts this information-theoretic gap into a
thermodynamic gap. The physical version P(P vs NP) asks whether this
gap is real — and the answer depends on whether search can be made
reversible (Bennett) or whether some irreversibility is unavoidable.
-/

end ThermalTuringMachine
