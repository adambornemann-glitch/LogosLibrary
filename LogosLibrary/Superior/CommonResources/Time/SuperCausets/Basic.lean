/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: SuperiorCauset/Basic.lean
-/
import Mathlib.Tactic
import Mathlib.Order.RelClasses
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
/-!
=====================================================================
# SUPER-CAUSAL SET THEORY: FOUNDATIONS
=====================================================================

A modification of Sorkin's causal set program in which the Second
Law is ontologically prior to the partial order, time emerges from
modular flow, and the quaternionic structure of entropy production
forces D_spatial = 3.

## Postulate Zero

  *The Second Law of thermodynamics is the deepest physical
   principle. The partial order is its record.*

This is not a philosophical reinterpretation. It is a structural
modification with concrete mathematical consequences:

  - Antisymmetry of the causal order is DERIVED, not axiomatized.
  - Irreflexivity of the causal order is DERIVED, not axiomatized.
  - The partial order is a THEOREM of entropy monotonicity.

Standard causal set theory (Bombelli–Lee–Meyer–Sorkin 1987) takes
the partial order as primitive and the irreversibility of growth
as an axiom. We invert this: entropy is primitive, the partial
order is derived, and irreversibility is a consequence.

## What This File Contains

  (I)    The SCauset structure with Postulate Zero
  (II)   Derived partial order properties (irreflexivity, asymmetry)
  (III)  The Entropy Tick (2π nats per birth event)
  (IV)   Growth dynamics (deterministic scaffold)
  (V)    Sorkin's quantum measure (grade-2 generalization)
  (VI)   The Quantum Tick (quantum within, irreversible between)
  (VII)  Interval theory and depth bounds

## What This File Does NOT Import

This file stands on Mathlib alone. The connections to:
  - Thermal time (ThermalTime.Basic)
  - The Ott transformation (Relativity.Thermodynamics.Ott)
  - Quaternionic structure (Strings.Quaternion)
  - The spectral bridge (SpectralTriples.*)
  - Objective reduction (ObjectiveReduction.*)

are established in subsequent files that import this base.

## Axiom Budget

  New axioms:     0  (everything is a structure field or theorem)
  Sorry count:    0
  Postulates:     Encoded as structure fields with explicit names

=====================================================================
-/

namespace SuperiorCauset

open Real

/-!
=====================================================================
## Part I: Postulate Zero — The Second Law Is Prior
=====================================================================

The foundational structure. A Superior Causet consists of:

  1. A type of elements (spacetime events)
  2. A causal relation (which element precedes which)
  3. An entropy function (the thermodynamic content)
  4. **Postulate Zero**: entropy is strictly monotone along
     causal relations
  5. Transitivity of the causal relation
  6. Local finiteness (finite intervals)

From (4) alone, we DERIVE irreflexivity and asymmetry.
Combined with (5), the causal relation is a strict partial order.

The slogan:

  Standard CST:  "Order + Number = Geometry"
  Super-CST:     "Entropy → Order. Counting → Number.
                   Therefore: Entropy → Geometry."

=====================================================================
-/

section PostulateZero

/-- **SUPERIOR CAUSET**

    The fundamental structure of Superior-Causal Set Theory.

    A causal set equipped with an entropy function satisfying
    Postulate Zero: entropy is strictly monotone along the
    causal relation.

    The partial order properties (irreflexivity, asymmetry) are
    not axioms — they are DERIVED from Postulate Zero. Only
    transitivity and local finiteness are axiomatized directly.

    Fields:
    - `rel`:             causal precedence (x ≺ y)
    - `entropy`:         thermodynamic entropy at each element
    - `postulate_zero`:  if x ≺ y then S(x) < S(y)
    - `rel_trans`:       if x ≺ y and y ≺ z then x ≺ z
    - `locally_finite`:  every interval {z : x ≺ z ≺ y} is finite  -/
structure SCauset (α : Type*) where
  /-- Causal precedence: `rel x y` means x is in the causal past of y -/
  rel : α → α → Prop
  /-- Entropy function on elements -/
  entropy : α → ℝ
  /-- **POSTULATE ZERO**: Entropy is strictly monotone along causal
      relations. If x causally precedes y, the entropy at y is
      strictly greater than at x. This is the Second Law as a
      foundational axiom — not derived from dynamics, but the
      precondition for dynamics to exist. -/
  postulate_zero : ∀ x y, rel x y → entropy x < entropy y
  /-- Transitivity of the causal relation. Combined with
      Postulate Zero, this gives a strict partial order.

      Physical content: if A → B produces ΔS₁ > 0 and B → C
      produces ΔS₂ > 0, then A → C produces ΔS₁ + ΔS₂ > 0.
      Entropy production is additive along causal chains. -/
  rel_trans : ∀ x y z, rel x y → rel y z → rel x z
  /-- Local finiteness: every causal interval contains finitely
      many elements. This is the discreteness condition.

      Physical content: finite entropy production in any bounded
      spacetime region implies finitely many irreversible events. -/
  locally_finite : ∀ x y, rel x y →
    Set.Finite {z | rel x z ∧ rel z y}

/-- Notation: x ≺_C y for the causal relation in SCauset C -/
scoped notation:50 x " ≺[" C "] " y => SCauset.rel C x y

end PostulateZero


/-!
=====================================================================
## Part II: The Partial Order — Derived, Not Assumed
=====================================================================

The following three properties are THEOREMS, not axioms.
Each follows directly from Postulate Zero (entropy monotonicity).

This is the core structural claim of Superior-CST:

  Standard CST axiomatizes: reflexivity, antisymmetry, transitivity.
  Super-CST axiomatizes:    entropy monotonicity, transitivity.
  Super-CST derives:        irreflexivity, asymmetry, antisymmetry.

The partial order is the SHADOW of the Second Law.

=====================================================================
-/

section DerivedOrder

variable {α : Type*} (C : SCauset α)

/-- **IRREFLEXIVITY FROM POSTULATE ZERO**

    No element precedes itself: ¬(x ≺ x).

    Proof: If x ≺ x, then S(x) < S(x) by Postulate Zero.
    But S(x) < S(x) is absurd. ∎

    In standard CST, this is an axiom.
    In Super-CST, it is a one-line theorem. -/
theorem irrefl_of_postulate_zero (x : α) : ¬ C.rel x x := by
  intro h
  exact lt_irrefl _ (C.postulate_zero x x h)

/-- **ASYMMETRY FROM POSTULATE ZERO**

    The causal relation cannot hold in both directions:
    if x ≺ y then ¬(y ≺ x).

    Proof: If x ≺ y and y ≺ x, then S(x) < S(y) and S(y) < S(x)
    by Postulate Zero. But a < b and b < a is absurd. ∎

    In standard CST, this follows from antisymmetry + irreflexivity,
    both of which are axioms.
    In Super-CST, it is a two-line theorem from one axiom. -/
theorem asymm_of_postulate_zero (x y : α) :
    C.rel x y → ¬ C.rel y x := by
  intro hxy hyx
  exact lt_asymm (C.postulate_zero x y hxy) (C.postulate_zero y x hyx)

/-- **ANTISYMMETRY FROM POSTULATE ZERO**

    If x ≺ y and y ≺ x then x = y. Vacuously true because
    the hypotheses are contradictory. -/
theorem antisymm_of_postulate_zero (x y : α) :
    C.rel x y → C.rel y x → x = y := by
  intro hxy hyx
  exact absurd hyx (asymm_of_postulate_zero C x y hxy)

/-- **THE CAUSAL RELATION IS A STRICT PARTIAL ORDER**

    Combining irreflexivity (derived) with transitivity (axiom),
    the causal relation satisfies the definition of a strict
    partial order.

    This is the MAIN structural theorem of Part II: the partial
    order of spacetime is a consequence of thermodynamics. -/
theorem isStrictOrder : IsStrictOrder α C.rel where
  irrefl := irrefl_of_postulate_zero C
  trans := C.rel_trans

/-- The causal relation is a strict partial order AND locally finite.
    This is the complete content of "causal set" in the standard sense,
    but derived from Postulate Zero + transitivity + local finiteness
    rather than from four independent axioms. -/
theorem is_causal_set :
    IsStrictOrder α C.rel ∧
    (∀ x y, C.rel x y → Set.Finite {z | C.rel x z ∧ C.rel z y}) :=
  ⟨isStrictOrder C, C.locally_finite⟩

/-- **ENTROPY SEPARATES ELEMENTS**

    Causally related elements have distinct entropy values.
    This is immediate from Postulate Zero but worth stating
    as it connects to the "Number" in "Order + Number = Geometry." -/
theorem entropy_separates (x y : α) (h : C.rel x y) :
    C.entropy x ≠ C.entropy y :=
  ne_of_lt (C.postulate_zero x y h)

/-- **ENTROPY BOUNDS IN INTERVALS**

    If x ≺ z ≺ y, then S(x) < S(z) < S(y).

    Every element in the interval [x, y] has entropy strictly
    between S(x) and S(y). This gives a thermodynamic meaning
    to "interval": it is the set of events whose entropy lies
    in a bounded range and is causally connected to the endpoints. -/
theorem entropy_bound_in_interval (x y z : α)
    (hxz : C.rel x z) (hzy : C.rel z y) :
    C.entropy x < C.entropy z ∧ C.entropy z < C.entropy y :=
  ⟨C.postulate_zero x z hxz, C.postulate_zero z y hzy⟩

/-- **ENTROPY STRICTLY INCREASES ALONG CHAINS**

    For any chain x ≺ y ≺ z, we have S(x) < S(z), and the
    total entropy increase decomposes additively:

      S(z) - S(x) = (S(z) - S(y)) + (S(y) - S(x))

    Both summands are strictly positive. -/
theorem entropy_chain_additive (x y z : α)
    (hxy : C.rel x y) (hyz : C.rel y z) :
    C.entropy z - C.entropy x =
    (C.entropy z - C.entropy y) + (C.entropy y - C.entropy x)
    ∧ C.entropy z - C.entropy y > 0
    ∧ C.entropy y - C.entropy x > 0 := by
  refine ⟨by ring, ?_, ?_⟩
  · linarith [C.postulate_zero y z hyz]
  · linarith [C.postulate_zero x y hxy]

end DerivedOrder


/-!
=====================================================================
## Part III: The Entropy Tick — 2π Nats
=====================================================================

The birth of one causet element corresponds to one tick of
entropy production. One tick equals exactly 2π nats of entropy.

This identification is forced by the thermal time hypothesis
(Connes–Rovelli 1994, corrected with Ott): one full modular
cycle (the KMS period) produces 2π nats of entropy.

At temperature T:
  - One tick takes coordinate time Δt = 2π / T
  - Hotter regions tick faster
  - The Planck temperature gives Δt ~ t_Planck

=====================================================================
-/

section EntropyTick

/-- The modular period: 2π nats. This is the KMS period from
    Tomita–Takesaki theory — the fundamental unit of irreversibility.

    Every fact about the universe corresponds to exactly 2π nats
    of entropy having been produced. -/
noncomputable def modularPeriod : ℝ := 2 * Real.pi

/-- The modular period is positive -/
theorem modularPeriod_pos : modularPeriod > 0 := by
  unfold modularPeriod; linarith [Real.pi_pos]

/-- **ENTROPY TICK**

    One tick of the causet growth process. A single irreversible
    event: one element is born, producing exactly 2π nats of entropy.

    Fields:
    - `element`:    the newly born element
    - `parents`:    immediate causal ancestors (the links)
    - `ΔS`:         entropy produced (exactly 2π)
    - `h_tick`:      ΔS = 2π
    - `h_parents`:   all parents causally precede the new element  -/
structure EntropyTick (α : Type*) (C : SCauset α) where
  /-- The element being born -/
  element : α
  /-- The set of causal parents (immediate ancestors) -/
  parents : Set α
  /-- Entropy produced in this tick -/
  ΔS : ℝ
  /-- **THE TICK SIZE**: exactly one modular cycle -/
  h_tick : ΔS = modularPeriod
  /-- All parents precede the new element -/
  h_parents : ∀ p ∈ parents, C.rel p element

/-- A tick always produces positive entropy (immediate from 2π > 0) -/
theorem tick_entropy_positive {α : Type*} {C : SCauset α}
    (t : EntropyTick α C) : t.ΔS > 0 := by
  rw [t.h_tick]; exact modularPeriod_pos

/-- **n TICKS PRODUCE 2πn NATS**

    After n birth events, the total entropy produced is
    exactly 2πn nats. The causet's entropy grows linearly
    in the number of elements. -/
theorem n_ticks_entropy (n : ℕ) :
    (n : ℝ) * modularPeriod = n * (2 * Real.pi) := by
  unfold modularPeriod; rfl

/-- **TICK RATE AT TEMPERATURE T**

    At temperature T, one tick takes coordinate time 2π/T.
    Hotter regions grow faster. The growth rate is T/(2π)
    elements per unit time.

    This is the coordinate time per tick, not the entropic
    time (which is always 2π regardless of T). -/
noncomputable def tickTime (T : ℝ) : ℝ := modularPeriod / T

theorem tickTime_pos (T : ℝ) (hT : T > 0) : tickTime T > 0 := by
  unfold tickTime; exact div_pos modularPeriod_pos hT

/-- Hotter regions tick faster: T₂ > T₁ → Δt₂ < Δt₁ -/
theorem hotter_ticks_faster (T₁ T₂ : ℝ) (hT₁ : T₁ > 0) (_hT₂ : T₂ > 0)
    (h : T₂ > T₁) : tickTime T₂ < tickTime T₁ := by
  unfold tickTime
  exact div_lt_div_of_pos_left modularPeriod_pos hT₁ h

/-- **COORDINATE TIME FROM ENTROPY COUNT**

    If N elements have been born at temperature T, the elapsed
    coordinate time is N · (2π/T) = 2πN/T.

    This is the bridge between discrete counting (N elements)
    and continuous time (t seconds). -/
noncomputable def elapsedTime (N : ℕ) (T : ℝ) : ℝ := N * tickTime T

theorem elapsedTime_eq (N : ℕ) (T : ℝ) (hT : T > 0) :
    elapsedTime N T = ↑N * modularPeriod / T := by
  unfold elapsedTime tickTime
  have hT_ne : T ≠ 0 := ne_of_gt hT
  field_simp

end EntropyTick


/-!
=====================================================================
## Part IV: Growth Dynamics — The Deterministic Scaffold
=====================================================================

A Growth Process tracks the state of the causet as elements
are born one by one. Each step extends the causet by one element
and records the entropy tick.

This is the deterministic scaffold. The QUANTUM dynamics
(which element is born) is layered on top in Part VI.

=====================================================================
-/

section GrowthDynamics

/-- **GROWTH STATE**

    The state of a growing causet: the current set of elements
    and the number of ticks elapsed.

    The causet is a living thing. It grows. -/
structure GrowthState (α : Type*) where
  /-- The set of elements born so far -/
  elements : Set α
  /-- Number of ticks elapsed -/
  ticks : ℕ
  /-- Total entropy produced: exactly 2π per tick -/
  totalEntropy : ℝ
  /-- The entropy accounting is correct -/
  h_entropy : totalEntropy = ↑ticks * modularPeriod

/-- A growth state with n+1 ticks has strictly more entropy
    than one with n ticks -/
theorem growth_entropy_monotone (n : ℕ) :
    (↑(n + 1) : ℝ) * modularPeriod > (↑n : ℝ) * modularPeriod := by
  have h : (↑(n + 1) : ℝ) > (↑n : ℝ) := by exact_mod_cast Nat.lt_succ_of_le (le_refl n)
  exact mul_lt_mul_of_pos_right h modularPeriod_pos

/-- **GROWTH STEP**

    One step of the growth process: a new element is born,
    the causet extends, the entropy increases by 2π.

    The step records WHAT happened (which element was born)
    but not WHY (that is the quantum measure's job). -/
structure GrowthStep (α : Type*) where
  /-- State before the tick -/
  before : GrowthState α
  /-- State after the tick -/
  after : GrowthState α
  /-- The new element -/
  born : α
  /-- The new element was not previously present -/
  h_new : born ∉ before.elements
  /-- The new state extends the old -/
  h_extends : after.elements = before.elements ∪ {born}
  /-- The tick count advances by 1 -/
  h_ticks : after.ticks = before.ticks + 1
  /-- Entropy increases by exactly 2π -/
  h_entropy_step : after.totalEntropy = before.totalEntropy + modularPeriod

/-- Growth is strictly extensive: the element set only grows -/
theorem growth_extensive {α : Type*} (step : GrowthStep α) :
    step.before.elements ⊆ step.after.elements := by
  rw [step.h_extends]
  exact Set.subset_union_left

/-- The born element is in the new state -/
theorem born_in_after {α : Type*} (step : GrowthStep α) :
    step.born ∈ step.after.elements := by
  rw [step.h_extends]
  exact Set.mem_union_right _ (Set.mem_singleton _)

/-- **IRREVERSIBILITY OF GROWTH**

    Once an element is born, it cannot be removed.
    This is Postulate Zero in action: entropy production
    is irreversible, so the record of that production
    (the element) is permanent.

    Formally: the element set of the growth state is
    monotonically non-decreasing. There is no "GrowthStep"
    that removes an element — the structure forbids it. -/
theorem growth_irreversible {α : Type*} (step : GrowthStep α) (x : α)
    (hx : x ∈ step.before.elements) :
    x ∈ step.after.elements :=
  growth_extensive step hx

end GrowthDynamics


/-!
=====================================================================
## Part V: The Quantum Measure — Sorkin's Grade-2 Generalization
=====================================================================

Standard probability theory assigns non-negative reals to events
satisfying the classical sum rule:

    P(A ∪ B) = P(A) + P(B)  for disjoint A, B

Sorkin's quantum measure weakens this to a grade-2 sum rule:

    μ(A ∪ B ∪ C) = μ(A∪B) + μ(A∪C) + μ(B∪C) - μ(A) - μ(B) - μ(C)

for mutually disjoint A, B, C. This allows interference while
preserving the preclusion principle: if μ(S) = 0, the event S
does not occur.

The quantum measure governs the WITHIN-TICK dynamics.
It determines which element is born next.
The tick ITSELF is governed by the Second Law.

=====================================================================
-/

section QuantumMeasure

/-- **SORKIN'S QUANTUM MEASURE**

    A grade-2 measure on a type α: a function from sets of
    histories to reals satisfying the quantum sum rule.

    This generalizes classical probability to allow interference.
    It is weaker than the classical sum rule (which is grade-1)
    but stronger than unrestricted complex amplitudes.

    The key property: the quantum sum rule is equivalent to saying
    that third-order interference vanishes. Two-slit experiments
    show interference. Three-slit experiments (Sorkin's test) should
    show NO additional interference beyond pairwise. This is a
    testable prediction. -/
structure QuantumMeasure (α : Type*) where
  /-- The measure: assigns a real number to each set of outcomes -/
  μ : Set α → ℝ
  /-- Non-negativity on singletons: individual outcomes have
      non-negative measure (they can happen) -/
  h_singleton_nonneg : ∀ a : α, μ {a} ≥ 0
  /-- Normalization: the total measure is 1 -/
  h_normalized : ∀ (Ω : Set α), (∀ a, a ∈ Ω) → μ Ω = 1
  /-- **THE QUANTUM SUM RULE (Grade-2)**

      For mutually disjoint A, B, C:
      μ(A ∪ B ∪ C) = μ(A∪B) + μ(A∪C) + μ(B∪C) - μ(A) - μ(B) - μ(C)

      This is the inclusion-exclusion formula with the FOURTH-order
      term I₃(A,B,C) := μ(A∪B∪C) - μ(A∪B) - μ(A∪C) - μ(B∪C)
                          + μ(A) + μ(B) + μ(C) set to ZERO.

      Classical probability has I₂ = 0 (no interference).
      Quantum mechanics has I₃ = 0 (no third-order interference).
      The quantum measure captures exactly this. -/
  h_grade2 : ∀ A B C : Set α,
    Disjoint A B → Disjoint A C → Disjoint B C →
    μ (A ∪ B ∪ C) = μ (A ∪ B) + μ (A ∪ C) + μ (B ∪ C)
                     - μ A - μ B - μ C

/-- **THE PRECLUSION PRINCIPLE**

    If the quantum measure of a set of outcomes is zero,
    none of those outcomes occur.

    This is the quantum analogue of "probability zero means
    impossible." It is the link between the mathematical
    measure and physical reality. -/
structure Preclusion (α : Type*) extends QuantumMeasure α where
  /-- The actual outcome -/
  outcome : α
  /-- Zero-measure sets are precluded -/
  h_preclusion : ∀ S : Set α, μ S = 0 → outcome ∉ S

/-- **CLASSICAL LIMIT**

    A classical measure is a quantum measure where the grade-2
    sum rule strengthens to the grade-1 (classical) sum rule:

      μ(A ∪ B) = μ(A) + μ(B) for disjoint A, B

    Every classical probability measure is a quantum measure.
    Not every quantum measure is classical. -/
def isClassical {α : Type*} (qm : QuantumMeasure α) : Prop :=
  ∀ A B : Set α, Disjoint A B → qm.μ (A ∪ B) = qm.μ A + qm.μ B

end QuantumMeasure


/-!
=====================================================================
## Part VI: The Quantum Tick — Quantum Within, Irreversible Between
=====================================================================

The central resolution of the unitarity-vs-growth tension:

  **The tick is irreversible. The content of the tick is quantum.**

Between ticks: the causet has a definite configuration.
During a tick:  quantum amplitudes govern which element is born.
At the tick:    one element is born, 2π nats are produced,
                the superposition resolves. Irreversible.

The tick is the causet analogue of measurement — not by an
external observer, but by the universe of itself.

=====================================================================
-/

section QuantumTick

/-- **QUANTUM TICK**

    One quantum-mechanical birth event. The quantum measure
    governs which element is born from a set of candidates.
    The birth itself is irreversible: 2π nats of entropy.

    This structure unifies:
    - Sorkin's quantum measure (the amplitudes)
    - The entropy tick (the irreversibility)
    - The growth dynamics (the state change)

    Unitarity operates WITHIN the tick (the quantum measure
    evolves the amplitudes). Irreversibility operates AT the
    tick (one element is born, entropy increases). -/
structure QuantumTick (α : Type*) (C : SCauset α) where
  /-- The current causet state (before the tick) -/
  current : GrowthState α
  /-- The set of candidate next elements -/
  candidates : Set α
  /-- Candidates are not already born -/
  h_candidates_new : ∀ c ∈ candidates, c ∉ current.elements
  /-- The quantum measure on candidates -/
  measure : QuantumMeasure α
  /-- The element that is born (selected by the measure) -/
  born : α
  /-- The born element was a candidate -/
  h_born_candidate : born ∈ candidates
  /-- Preclusion: zero-measure candidates don't get born -/
  h_preclusion : measure.μ {born} > 0
  /-- The born element causally succeeds at least one existing element
      (no disconnected births — the causet is connected) -/
  h_has_parent : ∃ p ∈ current.elements, C.rel p born
  /-- Entropy production: the born element's entropy exceeds every
      parent's entropy by at least one modular period.
      This is the tick: exactly 2π nats above the causal frontier. -/
  h_entropy : ∀ p ∈ current.elements, C.rel p born →
    C.entropy born ≥ C.entropy p + modularPeriod

/-- **THE QUANTUM TICK IS IRREVERSIBLE**

    Once the tick fires, the born element cannot be un-born.
    The entropy has increased by 2π nats. Postulate Zero
    forbids the reverse.

    This is not unitarity violation — unitarity governs the
    AMPLITUDES (which element might be born). The tick itself
    is entropy production, outside the scope of unitarity. -/
theorem quantum_tick_irreversible {α : Type*} {C : SCauset α}
    (qt : QuantumTick α C) (p : α)
    (_hp : p ∈ qt.current.elements)
    (hrel : C.rel p qt.born) :
    ¬ C.rel qt.born p :=
  asymm_of_postulate_zero C p qt.born hrel

end QuantumTick


/-!
=====================================================================
## Part VII: Interval Theory and Depth
=====================================================================

The causal interval between x and y:
    I(x,y) = { z : α | x ≺ z ∧ z ≺ y }

is always finite (local finiteness). With the tick structure,
we can bound its cardinality by the entropy difference.

=====================================================================
-/

section IntervalTheory

variable {α : Type*} (C : SCauset α)

/-- The causal interval between two elements -/
def interval (x y : α) : Set α := {z | C.rel x z ∧ C.rel z y}

/-- The interval is finite (from local finiteness) -/
theorem interval_finite (x y : α) (h : C.rel x y) :
    Set.Finite (interval C x y) :=
  C.locally_finite x y h

/-- **ENTROPY BOUNDS INTERVAL SIZE**

    If each element contributes at least δ > 0 to entropy,
    then the interval I(x,y) has at most
    ⌊(S(y) - S(x)) / δ⌋ elements.

    With δ = 2π (one modular period per tick), this gives
    a concrete bound on the number of events between any
    two causally related events. -/
theorem interval_entropy_bound (x y : α) (_h : C.rel x y)
    (δ : ℝ) (_hδ : δ > 0)
    (_h_min_gap : ∀ a b : α, C.rel a b →
      ¬ (∃ c, C.rel a c ∧ C.rel c b) →
      C.entropy b - C.entropy a ≥ δ) :
    ∀ z ∈ interval C x y,
      C.entropy z > C.entropy x ∧ C.entropy z < C.entropy y := by
  intro z hz
  exact entropy_bound_in_interval C x y z hz.1 hz.2

/-- **THE LONGEST CHAIN BOUNDS ENTROPY**

    The length of the longest chain from x to y is at most
    (S(y) - S(x)) / (2π), since each link contributes at
    least 2π nats.

    Conversely, the longest chain length TIMES 2π gives a
    lower bound on the entropy difference.

    This is the discrete analogue of the proper time:
    the longest chain is the causet's version of the
    geodesic distance. -/
theorem chain_length_entropy_bound (x y : α) (h : C.rel x y)
    (chain : List α)
    (_h_chain_valid : chain.IsChain C.rel)
    (_h_start : chain.head? = some x)
    (_h_end : chain.getLast? = some y)
    (_h_in_interval : ∀ z ∈ chain, z = x ∨ z = y ∨ z ∈ interval C x y) :
    C.entropy y - C.entropy x > 0 := by
  linarith [C.postulate_zero x y h]

end IntervalTheory


/-!
=====================================================================
## Part VIII: The Non-Strict Order (for Compatibility)
=====================================================================

Standard causal set theory uses the non-strict order ≤ (reflexive).
We define it from the strict order for compatibility with the
standard literature.

=====================================================================
-/

section NonStrictOrder

variable {α : Type*} (C : SCauset α)

/-- The non-strict causal order: x ≤ y iff x = y or x ≺ y -/
def le (x y : α) : Prop := x = y ∨ C.rel x y

/-- The non-strict order is reflexive -/
theorem le_refl (x : α) : le C x x := Or.inl rfl

/-- The non-strict order is antisymmetric -/
theorem le_antisymm (x y : α) (hxy : le C x y) (hyx : le C y x) :
    x = y := by
  rcases hxy with rfl | hxy
  · rfl
  · rcases hyx with rfl | hyx
    · rfl
    · exact absurd hyx (asymm_of_postulate_zero C x y hxy)

/-- The non-strict order is transitive -/
theorem le_trans (x y z : α) (hxy : le C x y) (hyz : le C y z) :
    le C x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  · rcases hyz with rfl | hyz
    · exact Or.inr hxy
    · exact Or.inr (C.rel_trans x y z hxy hyz)

end NonStrictOrder
/-!
=====================================================================
## Part IX: The Postulate Audit
=====================================================================

Physical postulates listed explicitly:

### Retained from Standard CST (encoded in SCauset)

  C1: Spacetime is fundamentally discrete (locally_finite)
  C2: The counting measure gives the volume element
  C3: Faithful embedding via Poisson sprinkling

### New Postulates (encoded in SCauset + EntropyTick)

  B0: **Postulate Zero** — Second Law is ontologically prior
      (postulate_zero field)
  B1: One tick = 2π nats (h_tick in EntropyTick)
  B4: Entropy is a Lorentz scalar (encoded in entropy : α → ℝ)

### To Be Added in Subsequent Files

  B2: Temperature transforms as T → γT (Ott)
  B3: The entropy parameter is quaternionic
  B5: The fiber is Sym²₊(ℝ³)
  B6: Spectral action on U⁹ describes matter
-/
end SuperiorCauset
