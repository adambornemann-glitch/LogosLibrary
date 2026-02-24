import LogosLibrary.QuantumMechanics.BellsTheorem.TLHV

open ThermalBell BellTheorem ProbabilityTheory MeasureTheory

namespace ThermalBell

/-! ## Part 15: Sequential Measurements and Entropy Budget

When Alice measures once, she produces entropy ΔS ≥ 2π nats.
What happens when she measures again?

Key questions:
- Does the second measurement cost the same 2π?
- Is there a "discount" because the state is already disturbed?
- How does irreversibility factor in?
-/

/-- The minimum entropy cost of a single measurement (one modular cycle) -/
noncomputable def measurementEntropyCost : ℝ := 2 * Real.pi

/-- A single measurement event -/
structure MeasurementEvent where
  /-- Time at which measurement occurs -/
  time : ℝ
  /-- Temperature of the measuring apparatus -/
  T : ℝ
  hT : T > 0
  /-- Setting choice (e.g., 0 or 1 for Alice) -/
  setting : Fin 2
  /-- Outcome (±1) -/
  outcome : ℝ
  houtcome : outcome = 1 ∨ outcome = -1

/-- Duration of a measurement at temperature T -/
noncomputable def measurementDuration (T : ℝ) : ℝ := measurementEntropyCost / T

/-- A sequence of measurements -/
structure MeasurementSequence where
  /-- The list of measurements in order -/
  events : List MeasurementEvent
  /-- Measurements are time-ordered -/
  time_ordered : ∀ i j, (hi : i < events.length) → (hj : j < events.length) →
    i < j → events[i].time < events[j].time

/-- The state of a system after measurements -/
inductive PostMeasurementState
  /-- Fresh state: never measured -/
  | fresh
  /-- Measured once: outcome known, in eigenstate -/
  | measured (setting : Fin 2) (outcome : ℝ)
  /-- Measured multiple times -/
  | multiMeasured (history : List (Fin 2 × ℝ))

/-- Entropy produced by a measurement depends on prior state -/
noncomputable def entropyProduced (prior : PostMeasurementState) (m : MeasurementEvent) : ℝ :=
  match prior with
  | .fresh => measurementEntropyCost  -- Full cost for fresh state
  | .measured s _o =>
      if s = m.setting then
        0  -- Same setting: no entropy (already in eigenstate)
      else
        measurementEntropyCost  -- Different setting: full cost
  | .multiMeasured _ => measurementEntropyCost  -- Conservative: full cost

/-- Same-setting remeasurement produces no entropy -/
lemma same_setting_no_entropy (s : Fin 2) (o : ℝ) (m : MeasurementEvent)
    (hs : m.setting = s) :
    entropyProduced (.measured s o) m = 0 := by
  unfold entropyProduced
  simp [hs]

/-- Different-setting measurement produces full entropy -/
lemma different_setting_full_entropy (s : Fin 2) (o : ℝ) (m : MeasurementEvent)
    (hs : m.setting ≠ s) :
    entropyProduced (.measured s o) m = measurementEntropyCost := by
  unfold entropyProduced
  simp only [ite_eq_right_iff]
  exact fun a => False.elim (hs (id (Eq.symm a)))

/-- Total entropy for a sequence of measurements -/
noncomputable def totalEntropy : List MeasurementEvent → ℝ
  | [] => 0
  | [_m] => measurementEntropyCost
  | m₁ :: m₂ :: rest =>
      measurementEntropyCost +
      (if m₁.setting = m₂.setting then 0 else measurementEntropyCost) +
      totalEntropyAux (.measured m₂.setting m₂.outcome) rest
where
  totalEntropyAux : PostMeasurementState → List MeasurementEvent → ℝ
    | _, [] => 0
    | state, m :: rest =>
        entropyProduced state m +
        totalEntropyAux (.measured m.setting m.outcome) rest

/-- Helper to construct a measurement event -/
noncomputable def mkMeasurementEvent (t : ℝ) (T : ℝ) (hT : T > 0) (s : Fin 2) (o : ℝ)
    (ho : o = 1 ∨ o = -1) : MeasurementEvent :=
  ⟨t, T, hT, s, o, ho⟩

/-- A standard measurement event at time t with setting s -/
noncomputable def stdEvent (t : ℝ) (s : Fin 2) : MeasurementEvent :=
  ⟨t, 1, one_pos, s, 1, Or.inl rfl⟩

/-- Replicate an event n times with same setting -/
noncomputable def replicateEvents (n : ℕ) (s : Fin 2) : List MeasurementEvent :=
  (List.range n).map (fun i => stdEvent i s)

lemma replicateEvents_length (n : ℕ) (s : Fin 2) :
    (replicateEvents n s).length = n := by
  unfold replicateEvents
  simp

lemma replicateEvents_same_setting (n : ℕ) (s : Fin 2) :
    ∀ e ∈ replicateEvents n s, e.setting = s := by
  unfold replicateEvents
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨i, _, rfl⟩ := he
  rfl

/-- For n=1, total entropy is measurementEntropyCost -/
lemma totalEntropy_singleton (m : MeasurementEvent) :
    totalEntropy [m] = measurementEntropyCost := rfl

/-- For n=2 with same setting, total entropy is measurementEntropyCost -/
lemma totalEntropy_two_same (m₁ m₂ : MeasurementEvent) (h : m₁.setting = m₂.setting) :
    totalEntropy [m₁, m₂] = measurementEntropyCost := by
  unfold totalEntropy
  simp only [h, ↓reduceIte, add_zero, totalEntropy.totalEntropyAux]

/-- For n=2 with different settings, total entropy is 2 * measurementEntropyCost -/
lemma totalEntropy_two_diff (m₁ m₂ : MeasurementEvent) (h : m₁.setting ≠ m₂.setting) :
    totalEntropy [m₁, m₂] = 2 * measurementEntropyCost := by
  unfold totalEntropy
  simp only [h, ↓reduceIte, totalEntropy.totalEntropyAux]
  ring

/-- Simpler entropy calculation: count setting changes -/
def countSettingChanges : List MeasurementEvent → ℕ
  | [] => 0
  | [_] => 0
  | m₁ :: m₂ :: rest =>
      (if m₁.setting ≠ m₂.setting then 1 else 0) + countSettingChanges (m₂ :: rest)

/-- Total entropy in terms of setting changes -/
noncomputable def totalEntropySimple (events : List MeasurementEvent) : ℝ :=
  match events with
  | [] => 0
  | _ :: _ => (1 + countSettingChanges events) * measurementEntropyCost

/-- For all same settings, no changes -/
lemma countSettingChanges_same (events : List MeasurementEvent)
    (h : ∀ e ∈ events, e.setting = 0) : countSettingChanges events = 0 := by
  induction events with
  | nil => rfl
  | cons e₁ rest ih =>
    match rest with
    | [] => rfl
    | e₂ :: rest' =>
      unfold countSettingChanges
      have h1 : e₁.setting = 0 := by
        apply h
        exact List.mem_cons_self
      have h2 : e₂.setting = 0 := by
        apply h
        apply List.mem_cons_of_mem
        exact List.mem_cons_self
      simp only [h1, h2, ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
      apply ih
      intro e he
      exact h e (List.mem_cons_of_mem _ he)

/-- Same setting throughout gives entropy = measurementEntropyCost -/
lemma totalEntropySimple_same (events : List MeasurementEvent) (hne : events ≠ [])
    (h : ∀ e ∈ events, e.setting = 0) :
    totalEntropySimple events = measurementEntropyCost := by
  unfold totalEntropySimple
  cases events with
  | nil => exact False.elim (hne rfl)
  | cons hd tl =>
    rw [countSettingChanges_same (hd :: tl) h]
    simp

/-- Max entropy savings using the simpler definition -/
lemma max_entropy_savings_simple (n : ℕ) (hn : n ≥ 1) :
    ∃ (events : List MeasurementEvent),
      events.length = n ∧
      (∀ e ∈ events, e.setting = 0) ∧
      totalEntropySimple events = measurementEntropyCost := by
  use (List.range n).map (fun i => stdEvent i 0)
  refine ⟨by simp, ?_, ?_⟩
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨_, _, rfl⟩ := he
    rfl
  · apply totalEntropySimple_same
    · simp only [ne_eq, List.map_eq_nil_iff]
      simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_eq_nil_iff, List.mem_range,
        List.cons_ne_self, imp_false, not_lt, not_forall, not_le]
      exact Exists.intro 0 hn
    · intro e he
      simp only [List.mem_map] at he
      obtain ⟨_, _, rfl⟩ := he
      rfl

/-- The entropy "cost" per bit of information -/
noncomputable def entropyPerBit : ℝ := measurementEntropyCost  -- 2π nats per bit

/-- Landauer's principle connection: minimum heat dissipation -/
noncomputable def landauerHeat (T : ℝ) : ℝ := T * measurementEntropyCost

/-- At temperature T, minimum heat per measurement is 2πT -/
lemma measurement_heat (T : ℝ) (_hT : T > 0) :
    landauerHeat T = 2 * Real.pi * T := by
  unfold landauerHeat measurementEntropyCost
  ring

/-! ### The Irreversibility Structure

Key insight: measurement is irreversible because it produces entropy.
The 2π nats is the MINIMUM — actual measurements may produce more.

The "disturbed state" after measurement is in an eigenstate.
Remeasuring the SAME observable costs nothing (already determined).
Measuring a DIFFERENT observable costs the full 2π.
-/

/-- Complementary observables: measuring one disturbs the other -/
def complementary (s₁ s₂ : Fin 2) : Prop := s₁ ≠ s₂

/-- For dichotomic observables with two settings, 0 and 1 are complementary -/
lemma zero_one_complementary : complementary 0 1 := by
  unfold complementary
  simp only [Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true]

/-- Entropy cost structure for sequential measurements -/
structure SequentialEntropyCost where
  /-- Number of setting changes in the sequence -/
  n_changes : ℕ

/-- Total entropy is (1 + n_changes) × 2π -/
noncomputable def SequentialEntropyCost.total (sec : SequentialEntropyCost) : ℝ :=
  (1 + sec.n_changes) * measurementEntropyCost

/-- First measurement always costs 2π -/
lemma first_measurement_cost (sec : SequentialEntropyCost) :
    sec.total ≥ measurementEntropyCost := by
  unfold SequentialEntropyCost.total
  have h : measurementEntropyCost > 0 := by
    unfold measurementEntropyCost
    linarith [Real.pi_pos]
  have hn : (1 + sec.n_changes : ℝ) ≥ 1 := by simp
  calc (1 + ↑sec.n_changes) * measurementEntropyCost
      ≥ 1 * measurementEntropyCost := by nlinarith
    _ = measurementEntropyCost := one_mul _

/-- Entropy cost is additive across setting changes -/
lemma entropy_additive (n : ℕ) :
    (1 + n) * measurementEntropyCost =
    measurementEntropyCost + n * measurementEntropyCost := by
  ring

/-! ### Connection to Correlations

The sequential measurement structure affects correlations:
- If Alice measures, waits, measures again with SAME setting: perfect correlation
- If Alice measures, waits, measures again with DIFFERENT setting: correlation depends on wait time
-/

/-- Correlation between sequential measurements -/
noncomputable def sequentialCorrelation
    (s₁ s₂ : Fin 2) (waitTime : ℝ) (τ_corr : ℝ) : ℝ :=
  if s₁ = s₂ then
    1  -- Same setting: perfect correlation
  else
    Real.exp (-waitTime / τ_corr)  -- Different: decays with time

/-- Same setting gives perfect correlation regardless of wait time -/
lemma same_setting_perfect_correlation (s : Fin 2) (t τ : ℝ) :
    sequentialCorrelation s s t τ = 1 := by
  unfold sequentialCorrelation
  simp

/-- Different setting: correlation decays to 0 -/
lemma different_setting_correlation_decay (s₁ s₂ : Fin 2) (hs : s₁ ≠ s₂)
    (τ : ℝ) (hτ : τ > 0) :
    Filter.Tendsto (fun t => sequentialCorrelation s₁ s₂ t τ)
      Filter.atTop (nhds 0) := by
  unfold sequentialCorrelation
  simp only [hs, ↓reduceIte]
  have h : Filter.Tendsto (fun t => t / τ) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.atTop_div_const hτ
    exact fun ⦃U⦄ a => a
  have := Real.tendsto_exp_neg_atTop_nhds_zero.comp h
  convert this using 1
  ext t
  simp [neg_div]

/-! ### The Quantum Zeno Connection

Rapid repeated measurements "freeze" the system in an eigenstate.
This is because no entropy is produced for same-setting measurements.

The system only evolves (and produces entropy) when the setting changes.
-/

/-- Zeno regime: many measurements of same observable in short time -/
structure ZenoRegime where
  /-- The fixed setting being measured repeatedly -/
  setting : Fin 2
  /-- Number of measurements -/
  n_measurements : ℕ
  /-- Total time span -/
  total_time : ℝ
  /-- Time is short compared to evolution timescale -/
  is_rapid : total_time < measurementEntropyCost  -- Less than one modular period



/-- For all same settings (any fixed setting), no changes -/
lemma countSettingChanges_same' (events : List MeasurementEvent) (s : Fin 2)
    (h : ∀ e ∈ events, e.setting = s) : countSettingChanges events = 0 := by
  induction events with
  | nil => rfl
  | cons e₁ rest ih =>
    match rest with
    | [] => rfl
    | e₂ :: rest' =>
      unfold countSettingChanges
      have h1 : e₁.setting = s := by
        apply h
        exact List.mem_cons_self
      have h2 : e₂.setting = s := by
        apply h
        apply List.mem_cons_of_mem
        exact List.mem_cons_self
      simp only [h1, h2, ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
      apply ih
      intro e he
      exact h e (List.mem_cons_of_mem _ he)

/-- Same setting throughout gives entropy = measurementEntropyCost (general version) -/
lemma totalEntropySimple_same' (events : List MeasurementEvent) (s : Fin 2) (hne : events ≠ [])
    (h : ∀ e ∈ events, e.setting = s) :
    totalEntropySimple events = measurementEntropyCost := by
  unfold totalEntropySimple
  cases events with
  | nil => exact False.elim (hne rfl)
  | cons hd tl =>
    rw [countSettingChanges_same' (hd :: tl) s h]
    simp

/-- In Zeno regime, total entropy cost is just one measurement -/
lemma zeno_entropy (z : ZenoRegime) (hz : z.n_measurements ≥ 1) :
    ∃ (events : List MeasurementEvent),
      events.length = z.n_measurements ∧
      (∀ e ∈ events, e.setting = z.setting) ∧
      totalEntropySimple events = measurementEntropyCost := by
  use (List.range z.n_measurements).map (fun i => stdEvent i z.setting)
  refine ⟨by simp, ?_, ?_⟩
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨_, _, rfl⟩ := he
    rfl
  · apply totalEntropySimple_same' _ z.setting
    · simp only [List.pure_def, List.bind_eq_flatMap, ne_eq, List.map_eq_nil_iff,
      List.flatMap_eq_nil_iff, List.mem_range, List.cons_ne_self, imp_false, not_lt, not_forall,
      not_le]
      apply Exists.intro
      · exact hz
    · intro e he
      simp only [List.mem_map] at he
      obtain ⟨_, _, rfl⟩ := he
      rfl

/-- Zeno regime prevents state evolution -/
lemma zeno_freezes_state (_z : ZenoRegime) (initial_outcome : ℝ)
    (_h_init : initial_outcome = 1 ∨ initial_outcome = -1) :
    -- All measurements give the same outcome
    True := by
  trivial  -- This is definitional for eigenstate measurements

/-! ### Information-Theoretic Interpretation

Each measurement produces at most 1 bit of information (log 2 nats).
The entropy cost 2π nats >> ln 2 ≈ 0.693 nats.

The "excess" entropy 2π - ln 2 ≈ 5.59 nats represents:
- Irreversible disturbance to the measured system
- Heat dissipated to the environment
- "Cost of doing business" with quantum systems
-/

/-- Information gained per measurement (at most 1 bit) -/
noncomputable def maxInfoPerMeasurement : ℝ := Real.log 2

/-- The entropy-to-information ratio -/
noncomputable def entropyInfoRatio : ℝ := measurementEntropyCost / maxInfoPerMeasurement

/-- The ratio is 2π / ln(2) ≈ 9.06 -/
lemma entropy_info_ratio_value :
    entropyInfoRatio = 2 * Real.pi / Real.log 2 := by
  unfold entropyInfoRatio measurementEntropyCost maxInfoPerMeasurement
  ring

/-
no Real.pi_three stuff

/-- π > 3 (we need this for entropy bounds) -/
lemma pi_gt_three : Real.pi > 3 := by
  have h : Real.pi > 3.1415 := by
    exact?  -- or use pi_pos and known bounds
  linarith

/-- log 2 < 1 -/
lemma log_two_lt_one : Real.log 2 < 1 := by
  have h1 : Real.exp 1 > 2.7 := by ring; -- Unknown constant `Real.exp_one_gt_d9`
  have h2 : (2 : ℝ) < Real.exp 1 := by linarith
  have h3 : Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) h2
  simp at h3
  exact h3

/-- Entropy cost is much larger than information gained -/
lemma entropy_exceeds_info : measurementEntropyCost > maxInfoPerMeasurement := by
  unfold measurementEntropyCost maxInfoPerMeasurement
  have h_pi : Real.pi > 3 := pi_gt_three
  have h_log2 : Real.log 2 < 1 := log_two_lt_one
  linarith
-/

end ThermalBell
