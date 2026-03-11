/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumComputing.ThermalTuringMachine.Core
import Mathlib.Tactic
/-!
# Thermal Turing Machine — Utility Lemmas

Low-level structural lemmas for the ThermalTM infrastructure.
Everything here follows directly from the core definitions.

## Contents

1. **Tape** — Extensionality, write idempotence/identity/commutativity
2. **Direction** — Shift injectivity and distinctness
3. **Step iteration** — Composition, propagation of halting, decomposition
4. **Temperature–β identities** — Algebraic relationships
5. **Dissipation & entropy** — Non-negativity propagation
6. **Reversibility** — Halted transitions, equivalence with ¬irreversible
7. **Traces** — Singleton dissipation, sub-trace monotonicity
-/

namespace ThermalTuringMachine
open ThermalTime.Basic ThermalTime.InformationTheory

variable {Q Γ : Type*}

/-! ## § Tape Infrastructure -/

/-- Extensionality for tapes: pointwise-equal cell functions give equal tapes. -/
@[ext]
theorem Tape.ext {t₁ t₂ : Tape Γ} (h : ∀ i, t₁.cell i = t₂.cell i) : t₁ = t₂ := by
  cases t₁; cases t₂; congr 1; funext i; exact h i

/-- Writing twice at the same cell: the second write wins. -/
@[simp]
theorem Tape.write_write_same [DecidableEq ℤ]
    (tape : Tape Γ) (i : ℤ) (a b : Γ) :
    (tape.write i a).write i b = tape.write i b := by
  ext j
  simp only [write]
  by_cases h : j = i
  · subst h; simp [Function.update_self]
  · simp only [Function.update_idem]

/-- Writing the symbol already present is the identity. -/
@[simp]
theorem Tape.write_id [DecidableEq ℤ]
    (tape : Tape Γ) (i : ℤ) :
    tape.write i (tape.read i) = tape := by
  ext j
  simp only [write, read]
  by_cases h : j = i
  · subst h; simp [Function.update_self]
  · simp only [Function.update_eq_self]

/-- Writes at distinct positions commute. -/
theorem Tape.write_comm [DecidableEq ℤ]
    (tape : Tape Γ) (i j : ℤ) (a b : Γ) (hij : i ≠ j) :
    (tape.write i a).write j b = (tape.write j b).write i a := by
  ext k
  simp only [write]
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
  simp_all only [ne_eq, Function.update_idem, not_true_eq_false]
  <;>
  --subst hki
  simp_all only [not_false_eq_true, ne_eq, Function.update_of_ne]
  subst hki
  simp_all only [Function.update_self]
  subst hkj
  simp_all only [Function.update_self]

/-! ## § Direction -/

/-- Shifting the head is injective: distinct positions remain distinct. -/
theorem Direction.shift_injective (d : Direction) :
    Function.Injective d.shift := by
  intro x y h
  cases d <;> simp [shift] at h <;> omega

/-- A shifted position is never the original position. -/
theorem Direction.shift_ne_self (d : Direction) (pos : ℤ) :
    d.shift pos ≠ pos := by
  cases d <;> simp [shift]

/-- Left shift is right shift's inverse. -/
theorem Direction.shift_L_R (pos : ℤ) :
    Direction.L.shift (Direction.R.shift pos) = pos := by
  simp [shift]

/-- Right shift is left shift's inverse. -/
theorem Direction.shift_R_L (pos : ℤ) :
    Direction.R.shift (Direction.L.shift pos) = pos := by
  simp [shift]

/-! ## § Step Iteration -/

/-- One step via `stepN` agrees with `step`. -/
@[simp]
theorem ThermalTM.stepN_one (M : ThermalTM Q Γ) (c : Config Q Γ) :
    M.stepN c 1 = M.step c := by
  simp [stepN]

/-- `stepN` composes: m + n steps = m steps then n steps. -/
theorem ThermalTM.stepN_add (M : ThermalTM Q Γ) (c : Config Q Γ) (m n : ℕ) :
    M.stepN c (m + n) = (M.stepN c m).bind (fun c' => M.stepN c' n) := by
  induction n with
  | zero =>
    simp only [Nat.add_zero, stepN_zero]
    cases M.stepN c m <;> rfl
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 from by omega]
    simp only [stepN_succ, ih]
    -- Option.bind associativity
    cases M.stepN c m with
    | none => rfl
    | some c' => rfl

/-- Once halted, the machine stays halted: `none` persists through further steps. -/
theorem ThermalTM.stepN_none_persist (M : ThermalTM Q Γ) (c : Config Q Γ)
    (n k : ℕ) (h : M.stepN c n = none) :
    M.stepN c (n + k) = none := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [show n + (k + 1) = (n + k) + 1 from by omega]
    simp [stepN_succ, ih]

/-- Monotonicity: if `stepN c (n + k) = some c'`, then `stepN c n` succeeds too. -/
theorem ThermalTM.stepN_some_of_later (M : ThermalTM Q Γ) (c : Config Q Γ)
    (n k : ℕ) (c' : Config Q Γ) (h : M.stepN c (n + k) = some c') :
    ∃ c'', M.stepN c n = some c'' := by
  by_contra hne
  push_neg at hne
  have : M.stepN c n = none := by
    cases heq : M.stepN c n with
    | none => rfl
    | some val => exact False.elim (hne val heq)
  have := M.stepN_none_persist c n k this
  rw [this] at h
  grind only

/-- Decompose a successful step into its components. -/
theorem ThermalTM.step_result (M : ThermalTM Q Γ) (c c' : Config Q Γ)
    (h : M.step c = some c') :
    ∃ q' a' d, M.δ c.state c.currentSymbol = some (q', a', d) ∧
      c' = ⟨q', c.tape.write c.head a', d.shift c.head⟩ := by
  cases hδ : M.δ c.state c.currentSymbol with
  | none =>
    simp [step] at h
    simp_all only [Config.currentSymbol, Tape.read, reduceCtorEq, Direction.shift,
    false_and, exists_const, exists_false]
  | some val =>
    obtain ⟨q', a', d⟩ := val
    refine ⟨q', a', d, rfl, ?_⟩
    have hs : M.step c = some ⟨q', c.tape.write c.head a', d.shift c.head⟩ := by
      simp [step]
      simp_all only [Config.currentSymbol, Tape.read]
    rw [hs] at h
    exact (Option.some.inj h).symm

/-- After a step, the new state comes from δ. -/
theorem ThermalTM.step_state (M : ThermalTM Q Γ) (c c' : Config Q Γ)
    (h : M.step c = some c') (q' : Q) (a' : Γ) (d : Direction)
    (hδ : M.δ c.state c.currentSymbol = some (q', a', d)) :
    c'.state = q' := by
  have hs : M.step c = some ⟨q', c.tape.write c.head a', d.shift c.head⟩ := by
    simp [step]
    simp_all only [Config.currentSymbol, Tape.read]
  rw [hs] at h
  exact congrArg Config.state (Option.some.inj h).symm
-- Note: signature uses Γ for q' which may need adjustment to Q for state

/-- A halted configuration stays halted forever. -/
theorem ThermalTM.halted_stays (M : ThermalTM Q Γ) (c : Config Q Γ) (n : ℕ)
    (h : M.isHalted c) : M.stepN c (n + 1) = none := by
  induction n with
  | zero =>
    simp only [stepN_succ, stepN_zero, Option.bind_some]
    simp [isHalted] at h
    simp [step, h]
  | succ n ih =>
    simp only [stepN_succ, Option.bind_eq_none_iff]
    intro h h2
    simp_all only [stepN_succ, reduceCtorEq]

/-! ## § Temperature–β Identities -/

/-- Fundamental identity: β · T = 1 -/
theorem ThermalTM.β_mul_temperature (M : ThermalTM Q Γ) :
    M.β * M.temperature = 1 := by
  unfold temperature; field_simp
  exact div_self (ne_of_gt M.hβ)

/-- Fundamental identity: T · β = 1 -/
theorem ThermalTM.temperature_mul_β (M : ThermalTM Q Γ) :
    M.temperature * M.β = 1 := by
  rw [mul_comm]; exact M.β_mul_temperature

/-- β is the reciprocal of temperature. -/
theorem ThermalTM.β_eq_inv_temp (M : ThermalTM Q Γ) :
    M.β = M.temperature⁻¹ := by
  have := M.β_mul_temperature
  field_simp [M.temperature_ne_zero] at this ⊢
  linarith

/-- Temperature is the reciprocal of β. -/
theorem ThermalTM.temperature_eq_inv_β (M : ThermalTM Q Γ) :
    M.temperature = M.β⁻¹ := by
  unfold temperature
  rw [one_div]

/-- β is not zero (immediate from positivity). -/
theorem ThermalTM.β_ne_zero (M : ThermalTM Q Γ) : M.β ≠ 0 :=
  ne_of_gt M.hβ

/-- Two machines at the same β have the same temperature. -/
theorem ThermalTM.temperature_eq_of_β_eq (M₁ M₂ : ThermalTM Q Γ)
    (h : M₁.β = M₂.β) : M₁.temperature = M₂.temperature := by
  simp only [temperature, h]

/-- KMS reservoir temperature is positive. -/
theorem KMSReservoir.temperature_pos (R : KMSReservoir) :
    R.temperature > 0 :=
  div_pos one_pos R.hβ

/-- KMS reservoir temperature is nonzero. -/
theorem KMSReservoir.temperature_ne_zero (R : KMSReservoir) :
    R.temperature ≠ 0 :=
  ne_of_gt R.temperature_pos

/-! ## § Dissipation and Entropy Production -/

/-- Per-step dissipation is non-negative (convenience wrapper). -/
theorem ThermalTM.stepDissipation_nonneg (M : ThermalTM Q Γ) (c : Config Q Γ) :
    M.stepDissipation c ≥ 0 :=
  M.dissipation_nonneg c.state c.currentSymbol

/-- Per-step entropy production is non-negative:
    β > 0 and dissipation ≥ 0 gives β · dissipation ≥ 0. -/
theorem ThermalTM.stepEntropyProduction_nonneg (M : ThermalTM Q Γ) (c : Config Q Γ) :
    M.stepEntropyProduction c ≥ 0 := by
  unfold stepEntropyProduction
  exact mul_nonneg (le_of_lt M.hβ) (M.stepDissipation_nonneg c)

/-- Entropy production is dissipation divided by temperature (β · Q = Q / T). -/
theorem ThermalTM.stepEntropyProduction_eq_div_temp (M : ThermalTM Q Γ)
    (c : Config Q Γ) :
    M.stepEntropyProduction c = M.stepDissipation c / M.temperature := by
  unfold stepEntropyProduction
  rw [M.β_eq_inv_temp]
  ring

/-- For a Landauer-compliant machine, irreversible dissipation scales with T. -/
theorem ThermalTM.dissipation_scales_with_temperature
    (M : ThermalTM Q Γ) (hL : M.isLandauerCompliant)
    (q : Q) (a : Γ) (hirr : M.isIrreversibleAt q a) :
    M.dissipation q a ≥ M.temperature * natsPerBit := by
  have := hL q a hirr
  unfold ThermalTime.InformationTheory.landauerCost at this
  convert hL q a hirr using 1

/-! ## § Reversibility and Irreversibility -/

/-- An undefined transition is never irreversible:
    δ(q, a) = none precludes erasure. -/
theorem ThermalTM.not_irreversibleAt_of_δ_none (M : ThermalTM Q Γ)
    (q : Q) (a : Γ) (h : M.δ q a = none) :
    ¬M.isIrreversibleAt q a := by
  intro ⟨_, _, _, _, hne⟩
  exact hne h

/-- Reversibility is equivalent to the absence of irreversible transitions. -/
theorem ThermalTM.reversible_iff_forall_not_irreversible (M : ThermalTM Q Γ) :
    M.isReversible ↔ ∀ q a, ¬M.isIrreversibleAt q a := by
  constructor
  · exact fun hrev q a => M.reversible_not_irreversibleAt hrev q a
  · -- Converse: if no transition is irreversible, the machine is reversible
    intro h q₁ a₁ q₂ a₂ r hδ₁ hδ₂
    -- Suppose q₁ ≠ q₂ ∨ a₁ ≠ a₂ for contradiction
    by_contra hne
    apply h q₁ a₁
    refine ⟨q₂, a₂, ?_, ?_, ?_⟩
    · -- q₂ ≠ q₁ ∨ a₂ ≠ a₁ from ¬(q₁ = q₂ ∧ a₁ = a₂)
      by_contra hall
      push_neg at hall
      exact hne ⟨hall.1.symm, hall.2.symm⟩
    · -- δ q₁ a₁ = δ q₂ a₂ (both = some r)
      rw [hδ₁, hδ₂]
    · -- δ q₁ a₁ ≠ none
      rw [hδ₁]; exact Option.some_ne_none r

/-- A machine that halts everywhere is vacuously reversible. -/
theorem ThermalTM.reversible_of_always_halted (M : ThermalTM Q Γ)
    (h : ∀ q a, M.δ q a = none) : M.isReversible := by
  intro q₁ a₁ q₂ a₂ r hδ₁ _
  rw [h] at hδ₁
  grind only

/-- Irreversibility at (q, a) implies the transition is defined. -/
theorem ThermalTM.δ_ne_none_of_irreversible (M : ThermalTM Q Γ)
    (q : Q) (a : Γ) (h : M.isIrreversibleAt q a) :
    M.δ q a ≠ none := by
  obtain ⟨_, _, _, _, hne⟩ := h
  exact hne

/-- Irreversibility at (q, a) means there's a witness with the same output. -/
theorem ThermalTM.irreversible_witness (M : ThermalTM Q Γ)
    (q : Q) (a : Γ) (h : M.isIrreversibleAt q a) :
    ∃ q' a' r, (q' ≠ q ∨ a' ≠ a) ∧ M.δ q a = some r ∧ M.δ q' a' = some r := by
  obtain ⟨q', a', hne, hδ_eq, hδ_ne⟩ := h
  obtain ⟨r, hr⟩ : ∃ r, M.δ q a = some r := by
    cases heq : M.δ q a with
    | none => exact absurd heq hδ_ne
    | some val => exact ⟨val, rfl⟩
  exact ⟨q', a', r, hne, hr, hδ_eq ▸ hr⟩

/-! ## § Execution Trace Lemmas -/

/-- A single-configuration trace has zero dissipation (no steps taken). -/
theorem ThermalTM.totalDissipation_singleton (M : ThermalTM Q Γ) (c : Config Q Γ) :
    M.totalDissipation ⟨[c], List.cons_ne_nil _ _⟩ = 0 := by
  simp [totalDissipation]

/-- A valid trace of length 1 is trivially valid (no consecutive pairs to check). -/
theorem ThermalTM.isValidTrace_singleton (M : ThermalTM Q Γ) (c : Config Q Γ) :
    M.isValidTrace ⟨[c], List.cons_ne_nil _ _⟩ := by
  intro i h
  simp at h

/-- The number of irreversible steps is bounded by the trace length. -/
theorem ThermalTM.irreversibleSteps_le_numSteps (M : ThermalTM Q Γ)
    (trace : ExecutionTrace Q Γ) :
    M.irreversibleSteps trace ≤ trace.numSteps := by
  unfold irreversibleSteps
  calc (trace.configs.dropLast.filter _).length
      ≤ trace.configs.dropLast.length := List.length_filter_le _ _
    _ ≤ trace.configs.length - 1 := by
        rw [List.length_dropLast]

/-- No irreversible steps in a single-configuration trace. -/
theorem ThermalTM.irreversibleSteps_singleton (M : ThermalTM Q Γ)
    (c : Config Q Γ) :
    M.irreversibleSteps ⟨[c], List.cons_ne_nil _ _⟩ = 0 := by
  simp [irreversibleSteps]

/-! ## § KMS Consistency Propagation -/

/-- A KMS-grounded machine inherits positive temperature. -/
theorem KMSThermalTM.temperature_pos (M : KMSThermalTM Q Γ) :
    M.toThermalTM.temperature > 0 :=
  M.toThermalTM.temperature_pos

/-- A KMS-grounded machine inherits positive β. -/
theorem KMSThermalTM.β_pos (M : KMSThermalTM Q Γ) :
    M.toThermalTM.β > 0 :=
  M.toThermalTM.hβ

/-- The reservoir β is positive (propagated from KMSReservoir). -/
theorem KMSThermalTM.reservoir_β_pos (M : KMSThermalTM Q Γ) :
    M.reservoir.β > 0 :=
  M.reservoir.hβ

/-- A LandauerMachine has positive Landauer cost per bit. -/
theorem LandauerMachine.landauerCostPerBit_pos (M : LandauerMachine Q Γ) :
    M.toKMSThermalTM.toThermalTM.landauerCostPerBit > 0 :=
  M.toKMSThermalTM.toThermalTM.landauerCostPerBit_pos

/-- A LandauerMachine satisfies the total dissipation bound. -/
theorem LandauerMachine.total_bound (M : LandauerMachine Q Γ)
    (trace : ExecutionTrace Q Γ) (hvalid : M.toKMSThermalTM.toThermalTM.isValidTrace trace) :
    M.toKMSThermalTM.toThermalTM.totalDissipation trace ≥
      ↑(M.toKMSThermalTM.toThermalTM.irreversibleSteps trace) *
        M.toKMSThermalTM.toThermalTM.landauerCostPerBit :=
  M.toKMSThermalTM.toThermalTM.landauer_total_bound M.landauer_compliant trace hvalid

/-! ## § Miscellaneous Convenience -/

/-- The initial configuration of a ThermalTM on a blank tape. -/
def ThermalTM.initialConfig (M : ThermalTM Q Γ) : Config Q Γ :=
  ⟨M.q₀, ⟨fun _ => M.blank⟩, 0⟩

/-- The initial config reads the blank symbol. -/
@[simp]
theorem ThermalTM.initialConfig_currentSymbol (M : ThermalTM Q Γ) :
    M.initialConfig.currentSymbol = M.blank := rfl

/-- The initial config is in the start state. -/
@[simp]
theorem ThermalTM.initialConfig_state (M : ThermalTM Q Γ) :
    M.initialConfig.state = M.q₀ := rfl

/-- The initial config head is at position 0. -/
@[simp]
theorem ThermalTM.initialConfig_head (M : ThermalTM Q Γ) :
    M.initialConfig.head = 0 := rfl

end ThermalTuringMachine
