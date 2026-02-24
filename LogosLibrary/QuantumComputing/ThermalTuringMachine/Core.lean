/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.Superior.ThermalTime.InfoTheory
import LogosLibrary.QuantumMechanics.ModularTheory.KMS.Condition
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
/-!
# Thermal Turing Machine — Core Definitions

A Turing machine where every computational step is thermodynamically accountable.

## The Physics

Landauer's principle (1961) establishes that erasing one bit of information in a
system coupled to a thermal reservoir at temperature T requires dissipating at
least k_B T ln 2 of energy as heat. This is not an engineering limitation but a
consequence of the second law of thermodynamics.

Bennett (1973) showed the converse: logically reversible computations — those
whose step function is injective on configurations — can in principle be performed
with arbitrarily small dissipation. Together, Landauer and Bennett tie computation
theory to thermodynamics at the foundational level.

We go further: the temperature T is not a free parameter but is *grounded* by the
KMS (Kubo-Martin-Schwinger) condition on the reservoir state. This means the
Landauer bound inherits physical legitimacy from the thermal equilibrium condition
on the strip 0 < Im(z) < β, rather than from a postulated temperature.

## Architecture

1. **Tape, Configuration, Direction** — Standard TM components
2. **ThermalTM** — A TM with inverse temperature β and per-transition dissipation
3. **Step function** — Deterministic evolution of configurations
4. **Logical reversibility** — Injectivity of the transition map
5. **Landauer compliance** — The structural invariant: irreversible ⟹ dissipation ≥ kT ln 2
6. **Execution traces** — Cumulative thermodynamic accounting
7. **KMS grounding** — The reservoir temperature is physically meaningful

## References

* R. Landauer, "Irreversibility and Heat Generation in the Computing Process",
  IBM J. Res. Dev. 5(3), 183–191, 1961
* C.H. Bennett, "Logical Reversibility of Computation",
  IBM J. Res. Dev. 17(6), 525–532, 1973
* R. Kubo, "Statistical-Mechanical Theory of Irreversible Processes",
  J. Phys. Soc. Japan 12, 570–586, 1957
* P.C. Martin, J. Schwinger, "Theory of Many-Particle Systems. I",
  Phys. Rev. 115, 1342–1373, 1959
-/

namespace ThermalTuringMachine

open ThermalTime.Basic ThermalTime.InformationTheory

set_option linter.unusedVariables false

/-! ## Basic Turing Machine Components -/

/-- Direction the tape head moves after a transition -/
inductive Direction where
  | L  -- left
  | R  -- right
  deriving DecidableEq, Repr, Inhabited

/-- The tape: an integer-indexed array of symbols from alphabet Γ.

    We model an infinite tape as a function ℤ → Γ. The distinguished blank symbol
    is carried by the machine, not the tape, following standard convention. -/
structure Tape (Γ : Type*) where
  /-- Contents of each cell -/
  cell : ℤ → Γ

/-- Read the symbol at position i -/
@[simp] def Tape.read (tape : Tape Γ) (i : ℤ) : Γ := tape.cell i

/-- Write symbol a at position i, leaving all other cells unchanged -/
def Tape.write (tape : Tape Γ) (i : ℤ) (a : Γ) : Tape Γ :=
  ⟨Function.update tape.cell i a⟩

@[simp] lemma Tape.write_read_eq [DecidableEq ℤ] (tape : Tape Γ) (i : ℤ) (a : Γ) :
    (tape.write i a).read i = a := by
  simp [write, read, Function.update_self]

@[simp] lemma Tape.write_read_ne [DecidableEq ℤ] (tape : Tape Γ) (i j : ℤ) (a : Γ) (h : j ≠ i) :
    (tape.write i a).read j = tape.read j := by
  simp [write, read, Function.update, if_neg h]

/-- Configuration of a Turing machine: current state, tape, and head position -/
structure Config (Q Γ : Type*) where
  /-- Current control state -/
  state : Q
  /-- Current tape contents -/
  tape : Tape Γ
  /-- Current head position -/
  head : ℤ

/-- The symbol currently under the read/write head -/
@[simp] def Config.currentSymbol (c : Config Q Γ) : Γ := c.tape.read c.head

/-- New head position after moving in direction d -/
@[simp] def Direction.shift (d : Direction) (pos : ℤ) : ℤ :=
  match d with
  | .L => pos - 1
  | .R => pos + 1

/-! ## The Thermal Turing Machine -/

/-- A Thermal Turing Machine: a deterministic TM coupled to a thermal reservoir.

    Beyond the standard transition function, a ThermalTM carries:
    - An inverse temperature β > 0 characterizing the reservoir
    - A dissipation function assigning heat output to each transition
    - A guarantee that dissipation is non-negative (second law)

    The inverse temperature β will be grounded by the KMS condition in §7. -/
structure ThermalTM (Q : Type*) (Γ : Type*) where
  /-- Transition function: δ(q, a) = some (q', a', d) means
      "in state q reading a, write a', move d, enter q'".
      δ(q, a) = none means halt. -/
  δ : Q → Γ → Option (Q × Γ × Direction)
  /-- Initial state -/
  q₀ : Q
  /-- Blank symbol -/
  blank : Γ
  /-- Inverse temperature of the coupled thermal reservoir.
      In natural units where k_B = ℏ = 1, β = 1/T. -/
  β : ℝ
  /-- Positive temperature (finite, nonzero) -/
  hβ : β > 0
  /-- Heat dissipated into the reservoir when the machine transitions
      from state q reading symbol a. In natural units (k_B = 1). -/
  dissipation : Q → Γ → ℝ
  /-- Second law: dissipation is non-negative.
      Heat flows from computation into the reservoir, never out. -/
  dissipation_nonneg : ∀ q a, dissipation q a ≥ 0

variable {Q Γ : Type*}

/-- Temperature of the thermal reservoir: T = 1/β -/
noncomputable def ThermalTM.temperature (M : ThermalTM Q Γ) : ℝ := 1 / M.β

theorem ThermalTM.temperature_pos (M : ThermalTM Q Γ) : M.temperature > 0 :=
  div_pos one_pos M.hβ

theorem ThermalTM.temperature_ne_zero (M : ThermalTM Q Γ) : M.temperature ≠ 0 :=
  ne_of_gt M.temperature_pos

theorem ThermalTM.β_eq_inv_temperature (M : ThermalTM Q Γ) :
    M.β = 1 / M.temperature := by
  unfold temperature; field_simp

/-! ## Step Function -/

/-- Execute one step of the Thermal TM.

    Given a configuration, either:
    - Return `some c'` where c' is the successor configuration, or
    - Return `none` if the machine halts (no transition defined) -/
def ThermalTM.step (M : ThermalTM Q Γ) (c : Config Q Γ) : Option (Config Q Γ) :=
  match M.δ c.state c.currentSymbol with
  | none => none
  | some (q', a', d) => some ⟨q', c.tape.write c.head a', d.shift c.head⟩

/-- A configuration is halted when no transition is defined -/
def ThermalTM.isHalted (M : ThermalTM Q Γ) (c : Config Q Γ) : Prop :=
  M.δ c.state c.currentSymbol = none

/-- step returns none iff halted -/
theorem ThermalTM.step_none_iff_halted (M : ThermalTM Q Γ) (c : Config Q Γ) :
    M.step c = none ↔ M.isHalted c := by
  simp only [step, isHalted]
  cases M.δ c.state c.currentSymbol with
  | none => simp
  | some r => simp

/-- step returns some iff not halted -/
theorem ThermalTM.step_some_iff_not_halted (M : ThermalTM Q Γ) (c : Config Q Γ) :
    (∃ c', M.step c = some c') ↔ ¬ M.isHalted c := by
  rw [← M.step_none_iff_halted]
  cases M.step c with
  | none => simp
  | some c' => simp

/-- Iterated step: run the machine for n steps -/
def ThermalTM.stepN (M : ThermalTM Q Γ) (c : Config Q Γ) : ℕ → Option (Config Q Γ)
  | 0 => some c
  | n + 1 => (M.stepN c n).bind M.step

/-- Zero steps is the identity -/
@[simp] theorem ThermalTM.stepN_zero (M : ThermalTM Q Γ) (c : Config Q Γ) :
    M.stepN c 0 = some c := rfl

/-- n+1 steps = n steps then one more -/
@[simp] theorem ThermalTM.stepN_succ (M : ThermalTM Q Γ) (c : Config Q Γ) (n : ℕ) :
    M.stepN c (n + 1) = (M.stepN c n).bind M.step := rfl

/-! ## Logical Reversibility

A computation is *logically reversible* if its transition map is injective:
distinct inputs always produce distinct outputs. Bennett (1973) showed that
any computation can be made reversible at the cost of auxiliary tape, and that
reversible computations can in principle dissipate zero heat. -/

/-- A TM is (locally) reversible if its transition function is injective
    on defined transitions: whenever two input pairs produce the same
    output triple, the inputs must be identical.

    This is the key property for zero-dissipation computation. -/
def ThermalTM.isReversible (M : ThermalTM Q Γ) : Prop :=
  ∀ q₁ a₁ q₂ a₂ r,
    M.δ q₁ a₁ = some r →
    M.δ q₂ a₂ = some r →
    q₁ = q₂ ∧ a₁ = a₂

/-- A transition at (q, a) is irreversible if some distinct input (q', a')
    maps to the same output. This is an erasure: two distinguishable
    computational states become indistinguishable. -/
def ThermalTM.isIrreversibleAt (M : ThermalTM Q Γ) (q : Q) (a : Γ) : Prop :=
  ∃ q' a', (q' ≠ q ∨ a' ≠ a) ∧
    M.δ q a = M.δ q' a' ∧ M.δ q a ≠ none

/-- Reversibility implies no transition is irreversible -/
theorem ThermalTM.reversible_not_irreversibleAt
    (M : ThermalTM Q Γ) (hrev : M.isReversible)
    (q : Q) (a : Γ) : ¬ M.isIrreversibleAt q a := by
  intro ⟨q', a', hneq, hδ_eq, hδ_ne_none⟩
  -- Since δ q a ≠ none, extract the output
  obtain ⟨r, hr⟩ : ∃ r, M.δ q a = some r := by
    cases h : M.δ q a with
    | none => exact absurd h hδ_ne_none
    | some val => exact ⟨val, rfl⟩
  -- The other input maps to the same output
  have hr' : M.δ q' a' = some r := hδ_eq ▸ hr
  -- By reversibility, the inputs must be identical
  obtain ⟨hq_eq, ha_eq⟩ := hrev q a q' a' r hr hr'
  -- But we assumed they differ — contradiction
  rcases hneq with hq_ne | ha_ne
  · exact hq_ne hq_eq.symm
  · exact ha_ne ha_eq.symm

/-! ## Landauer Compliance

The central structural invariant: every irreversible transition must dissipate
at least k_B T ln 2 of heat. In natural units, this is T · ln 2. -/

/-- **Landauer compliance**: the structural invariant of a Thermal TM.

    For every transition that is logically irreversible (erases at least one bit),
    the heat dissipated satisfies:

      Q_dissipated ≥ k_B T ln 2

    In natural units: dissipation(q, a) ≥ T · ln 2 = landauerCost(T) -/
def ThermalTM.isLandauerCompliant (M : ThermalTM Q Γ) : Prop :=
  ∀ q a, M.isIrreversibleAt q a →
    M.dissipation q a ≥ landauerCost M.temperature

/-- The Landauer cost at the machine's operating temperature -/
noncomputable def ThermalTM.landauerCostPerBit (M : ThermalTM Q Γ) : ℝ :=
  landauerCost M.temperature

theorem ThermalTM.landauerCostPerBit_pos (M : ThermalTM Q Γ) :
    M.landauerCostPerBit > 0 :=
  landauerCost_pos M.temperature M.temperature_pos

/-- **Bennett's principle**: a reversible TM is vacuously Landauer-compliant.

    Since no transition is irreversible, the Landauer bound applies to nothing,
    and the machine can in principle run at zero dissipation. This is the formal
    content of Bennett's 1973 result. -/
theorem ThermalTM.reversible_is_landauer_compliant
    (M : ThermalTM Q Γ) (hrev : M.isReversible) :
    M.isLandauerCompliant := by
  intro q a hirr
  -- No irreversible transitions exist in a reversible TM
  exact absurd hirr (M.reversible_not_irreversibleAt hrev q a)

/-! ## Execution Traces and Cumulative Thermodynamics -/

/-- Heat dissipated at a single configuration (the cost of the transition *from* it) -/
noncomputable def ThermalTM.stepDissipation (M : ThermalTM Q Γ) (c : Config Q Γ) : ℝ :=
  M.dissipation c.state c.currentSymbol

/-- An execution trace: a nonempty list of configurations visited during computation.
    The last element is either a halted configuration or the state after the final step. -/
structure ExecutionTrace (Q Γ : Type*) where
  /-- Configurations visited, in order -/
  configs : List (Config Q Γ)
  /-- A trace must be nonempty -/
  nonempty : configs ≠ []

/-- Number of steps in a trace (one less than the number of configurations) -/
def ExecutionTrace.numSteps (t : ExecutionTrace Q Γ) : ℕ :=
  t.configs.length - 1

/-- A trace is valid for a ThermalTM if consecutive configurations are related by step -/
def ThermalTM.isValidTrace (M : ThermalTM Q Γ) (trace : ExecutionTrace Q Γ) : Prop :=
  ∀ (i : ℕ), (h : i + 1 < trace.configs.length) →
    M.step (trace.configs[i]'(by omega)) = some (trace.configs[i + 1]'h)

/-- A trace is complete if it ends in a halted configuration -/
def ThermalTM.isCompleteTrace (M : ThermalTM Q Γ) (trace : ExecutionTrace Q Γ) : Prop :=
  M.isValidTrace trace ∧
  M.isHalted (trace.configs.getLast trace.nonempty)

/-- Total heat dissipated over a trace: sum of dissipation at each non-terminal config.
    The last configuration contributes no dissipation (it's the result, not a step). -/
noncomputable def ThermalTM.totalDissipation
    (M : ThermalTM Q Γ) (trace : ExecutionTrace Q Γ) : ℝ :=
  (trace.configs.dropLast.map (fun c => M.stepDissipation c)).sum

/-- Total dissipation is non-negative (follows from per-step non-negativity) -/
theorem ThermalTM.totalDissipation_nonneg
    (M : ThermalTM Q Γ) (trace : ExecutionTrace Q Γ) :
    M.totalDissipation trace ≥ 0 := by
  unfold totalDissipation
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨c, _, rfl⟩ := hx
  exact M.dissipation_nonneg c.state c.currentSymbol

open Classical in
/-- Number of irreversible steps in a trace -/
noncomputable def ThermalTM.irreversibleSteps
    (M : ThermalTM Q Γ) (trace : ExecutionTrace Q Γ) : ℕ :=
  (trace.configs.dropLast.filter
    (fun c => decide (M.isIrreversibleAt c.state c.currentSymbol))).length

/-! ## The Landauer Bound on Computations

The culmination: for a Landauer-compliant ThermalTM, the total heat dissipated
over any computation is bounded below by the number of irreversible steps
times the Landauer cost per bit.

  Q_total ≥ n_irreversible × k_B T ln 2

This is the second law of thermodynamics applied to computation. -/
open Classical in
/-- **The Landauer bound on total dissipation.**

    For a Landauer-compliant ThermalTM, total dissipation over any valid trace
    is at least the number of irreversible steps times the cost per bit.

    This is the computational second law. -/

theorem ThermalTM.landauer_total_bound
    (M : ThermalTM Q Γ)
    (hL : M.isLandauerCompliant)
    (trace : ExecutionTrace Q Γ)
    (_hvalid : M.isValidTrace trace) :
    M.totalDissipation trace ≥
      ↑(M.irreversibleSteps trace) * M.landauerCostPerBit := by
  unfold totalDissipation irreversibleSteps
  generalize trace.configs.dropLast = l
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.filter]
    have hx_nonneg : M.stepDissipation x ≥ 0 :=
      M.dissipation_nonneg x.state x.currentSymbol
    cases hpx : decide (M.isIrreversibleAt x.state x.currentSymbol) with
    | false =>
      simp only
      linarith
    | true =>
      simp only [List.length_cons]
      have hirr : M.isIrreversibleAt x.state x.currentSymbol := by
        rwa [decide_eq_true_eq] at hpx
      have hx_bound : M.stepDissipation x ≥ M.landauerCostPerBit :=
        hL x.state x.currentSymbol hirr
      push_cast
      linarith

/-! ## KMS Grounding

The temperature parameter β in a ThermalTM is physically meaningful only when
grounded by the KMS condition on the reservoir state.

A KMS state at inverse temperature β satisfies the analytic continuation condition
on the strip {z : 0 < Im(z) < β}. This characterizes thermal equilibrium without
reference to a Hamiltonian or trace — it works for infinite systems where neither
may exist.

When the reservoir is KMS-grounded:
- The temperature T = 1/β is *the* equilibrium temperature (unique by the
  KMS condition's relationship to the modular automorphism group)
- The Landauer bound k_B T ln 2 is not postulated but derived from equilibrium
- Detailed balance holds, connecting dissipation to entropy production -/

/-- A KMS-grounded thermal reservoir.

    This existentially asserts that the inverse temperature β corresponds to
    an actual thermal equilibrium state satisfying the KMS condition on some
    C*-algebraic system. -/
structure KMSReservoir where
  /-- Inverse temperature -/
  β : ℝ
  /-- Positive temperature -/
  hβ : β > 0
  /-- There exists a C*-algebra, dynamics, and state satisfying KMS at β.
      This grounds the temperature physically: T = 1/β is a real equilibrium
      temperature, not a free parameter. -/
  grounded : ∃ (A : Type u) (_ : KMSCondition.CStarAlgebra A)
    (α : KMSCondition.Dynamics A) (ω : KMSCondition.State A),
    KMSCondition.IsKMSState ω α β
/-
**flag**: 
The KMSReservoir.grounded field is existentially quantified 
over a universe level. That's fine for now but when you go 
to discharge it, you'll need a concrete C*-algebra.
-/

/-- Temperature of the reservoir -/
noncomputable def KMSReservoir.temperature (R : KMSReservoir) : ℝ := 1 / R.β

/-- A KMS-grounded Thermal TM: the full construction.

    This is a ThermalTM whose reservoir temperature is physically meaningful,
    established by the KMS condition rather than postulated. The Landauer bound
    then inherits physical legitimacy from the thermal equilibrium. -/
structure KMSThermalTM (Q : Type*) (Γ : Type*) extends ThermalTM Q Γ where
  /-- The thermal reservoir satisfying KMS at the machine's β -/
  reservoir : KMSReservoir
  /-- The machine and reservoir agree on inverse temperature -/
  β_consistent : toThermalTM.β = reservoir.β

/-- The KMS-grounded temperature equals the machine temperature -/
theorem KMSThermalTM.temperature_consistent (M : KMSThermalTM Q Γ) :
    M.toThermalTM.temperature = M.reservoir.temperature := by
  unfold ThermalTM.temperature KMSReservoir.temperature
  rw [M.β_consistent]

/-! ## Key Properties and Structural Theorems -/

/-- A Landauer-compliant KMS-grounded TM:
    the physically complete thermodynamic computer. -/
structure LandauerMachine (Q : Type*) (Γ : Type*) extends KMSThermalTM Q Γ where
  /-- The machine respects Landauer's principle -/
  landauer_compliant : toKMSThermalTM.toThermalTM.isLandauerCompliant


/-- The dissipation per irreversible step in a LandauerMachine is at least
    the KMS-grounded Landauer cost -/
theorem LandauerMachine.step_bound (M : LandauerMachine Q Γ)
    (q : Q) (a : Γ) (hirr : M.toKMSThermalTM.toThermalTM.isIrreversibleAt q a) :
    M.toKMSThermalTM.toThermalTM.dissipation q a ≥
      landauerCost M.reservoir.temperature := by
  have hL := M.landauer_compliant q a hirr
  unfold ThermalTM.landauerCostPerBit at hL
  rw [M.toKMSThermalTM.temperature_consistent] at hL
  exact hL

/-- **Reversible computations are thermodynamically free.**

    A reversible LandauerMachine with zero dissipation function is valid:
    the Landauer condition holds vacuously because no step is irreversible. -/
theorem reversible_computation_free
    (δ : Q → Γ → Option (Q × Γ × Direction))
    (q₀ : Q) (blank : Γ) (β : ℝ) (hβ : β > 0)
    (hrev : ∀ q₁ a₁ q₂ a₂ r,
      δ q₁ a₁ = some r → δ q₂ a₂ = some r → q₁ = q₂ ∧ a₁ = a₂) :
    ∃ (M : ThermalTM Q Γ),
      M.isReversible ∧ M.isLandauerCompliant ∧
      (∀ q a, M.dissipation q a = 0) := by
  refine ⟨{
    δ := δ
    q₀ := q₀
    blank := blank
    β := β
    hβ := hβ
    dissipation := fun _ _ => 0
    dissipation_nonneg := fun _ _ => le_refl 0
  }, hrev, ?_, fun _ _ => rfl⟩
  intro q a hirr
  have hrev' : ThermalTM.isReversible
    ⟨δ, q₀, blank, β, hβ, fun _ _ => 0, fun _ _ => le_refl 0⟩ := hrev
  exact absurd hirr (ThermalTM.reversible_not_irreversibleAt _ hrev' q a)


/-! ## Entropy Production

Connection between logical irreversibility and thermodynamic entropy.
Each irreversible step produces at least ln 2 nats of entropy in the reservoir. -/

/-- Entropy produced in the reservoir per step: Q_dissipated / T = β · Q_dissipated -/
noncomputable def ThermalTM.stepEntropyProduction
    (M : ThermalTM Q Γ) (c : Config Q Γ) : ℝ :=
  M.β * M.stepDissipation c

/-- For a Landauer-compliant machine, each irreversible step produces
    at least ln 2 nats of entropy — exactly one bit's worth -/
theorem ThermalTM.irreversible_step_entropy_bound
    (M : ThermalTM Q Γ) (hL : M.isLandauerCompliant)
    (c : Config Q Γ) (hirr : M.isIrreversibleAt c.state c.currentSymbol) :
    M.stepEntropyProduction c ≥ natsPerBit := by
  unfold stepEntropyProduction stepDissipation
  have hbound := hL c.state c.currentSymbol hirr
  unfold landauerCostPerBit landauerCost at hbound
  -- hbound : dissipation ≥ T · natsPerBit = (1/β) · natsPerBit
  -- Goal  : β · dissipation ≥ natsPerBit
  have hβ_pos := M.hβ
  unfold temperature at hbound
  -- dissipation ≥ (1/β) · natsPerBit
  -- ⟹ β · dissipation ≥ β · (1/β) · natsPerBit = natsPerBit
  calc M.β * M.dissipation c.state c.currentSymbol
      ≥ M.β * (1 / M.β * natsPerBit) := by
        apply mul_le_mul_of_nonneg_left hbound (le_of_lt hβ_pos)
    _ = natsPerBit := by field_simp

end ThermalTuringMachine
