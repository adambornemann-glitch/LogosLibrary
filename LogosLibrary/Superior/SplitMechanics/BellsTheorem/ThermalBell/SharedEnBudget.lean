import LogosLibrary.Superior.SplitMechanics.BellsTheorem.TLHV

open ThermalBell BellTheorem ProbabilityTheory MeasureTheory

namespace ThermalBell

/-! ## Part 15: The Shared Entropy Budget

Key idea: For entangled states, the 2π entropy budget is SHARED, not duplicated.

- Separable state: Alice has 2π, Bob has 2π → independent deviations
- Entangled state: Total budget is 2π → correlated deviations

This constrains how the ε values can be distributed across the 4 CHSH terms.
-/

/-- An entropy budget structure -/
structure EntropyBudget where
  /-- Total available entropy (in natural units) -/
  total : ℝ
  /-- It's positive -/
  total_pos : total > 0

/-- The standard quantum budget: one modular period -/
noncomputable def quantumBudget : EntropyBudget where
  total := 2 * Real.pi
  total_pos := by linarith [Real.pi_pos]

/-- A separable budget: each party gets a full period -/
noncomputable def separableBudget : EntropyBudget where
  total := 4 * Real.pi  -- 2π + 2π
  total_pos := by linarith [Real.pi_pos]

/-- Budget ratio: entangled has half the separable budget -/
lemma budget_ratio : quantumBudget.total / separableBudget.total = 1 / 2 := by
  simp only [quantumBudget, separableBudget]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring


/-- A distribution of deviations across CHSH terms -/
structure DeviationDistribution where
  /-- The four ε values: ε₀₀, ε₀₁, ε₁₀, ε₁₁ -/
  ε : Fin 2 → Fin 2 → ℝ
  /-- All bounded by 1 -/
  bounded : ∀ i j, |ε i j| < 1


/-- The "total deviation" — sum of absolute values -/
noncomputable def DeviationDistribution.totalDeviation (D : DeviationDistribution) : ℝ :=
  |D.ε 0 0| + |D.ε 0 1| + |D.ε 1 0| + |D.ε 1 1|


/-- Maximum CHSH enhancement from a deviation distribution -/
noncomputable def DeviationDistribution.maxCHSHEnhancement (D : DeviationDistribution) : ℝ :=
  -- The thermal CHSH contribution: ε₀₁ - ε₀₀ + ε₁₀ + ε₁₁
  -- Maximized when signs align: |ε₀₁| + |ε₀₀| + |ε₁₀| + |ε₁₁|
  D.totalDeviation

/-- For separable states: each ε_ij factors as ε_A(i) * ε_B(j) -/
structure SeparableDeviation extends DeviationDistribution where
  /-- Alice's per-setting deviation -/
  ε_A : Fin 2 → ℝ
  /-- Bob's per-setting deviation -/
  ε_B : Fin 2 → ℝ
  /-- Factorization property -/
  factors : ∀ i j, ε i j = ε_A i * ε_B j
  /-- Individual bounds -/
  ε_A_bounded : ∀ i, |ε_A i| < 1
  ε_B_bounded : ∀ j, |ε_B j| < 1

/-- For separable deviations, the total deviation factors -/
lemma separable_total_factors (D : SeparableDeviation) :
    D.totalDeviation = (|D.ε_A 0| + |D.ε_A 1|) * (|D.ε_B 0| + |D.ε_B 1|) := by
  unfold DeviationDistribution.totalDeviation
  simp only [D.factors, abs_mul]
  ring

/-- The separable bound: if |ε_A i|, |ε_B j| ≤ δ, then total ≤ 4δ² -/
lemma separable_deviation_bound (D : SeparableDeviation) (δ : ℝ) (hδ : δ > 0)
    (hA : ∀ i, |D.ε_A i| ≤ δ) (hB : ∀ j, |D.ε_B j| ≤ δ) :
    D.totalDeviation ≤ 4 * δ^2 := by
  rw [separable_total_factors]
  have hA_sum : |D.ε_A 0| + |D.ε_A 1| ≤ 2 * δ := by linarith [hA 0, hA 1]
  have hB_sum : |D.ε_B 0| + |D.ε_B 1| ≤ 2 * δ := by linarith [hB 0, hB 1]
  have hA_nonneg : |D.ε_A 0| + |D.ε_A 1| ≥ 0 := by positivity
  calc (|D.ε_A 0| + |D.ε_A 1|) * (|D.ε_B 0| + |D.ε_B 1|)
      ≤ (2 * δ) * (2 * δ) := by apply mul_le_mul hA_sum hB_sum (by positivity) (by linarith)
    _ = 4 * δ^2 := by ring

/-- For entangled states: the ε values are constrained by a JOINT budget -/
structure EntangledDeviation extends DeviationDistribution where
  /-- The joint constraint: sum of |ε| bounded by budget-derived quantity -/
  joint_budget : ℝ
  budget_pos : joint_budget > 0
  /-- The constraint -/
  constrained : toDeviationDistribution.totalDeviation ≤ joint_budget

/-- The quantum budget gives joint_budget = 4 * ε_tsirelson -/
noncomputable def quantumEntangledDeviation (D : DeviationDistribution)
    (h : D.totalDeviation ≤ 4 * ε_tsirelson) : EntangledDeviation where
  toDeviationDistribution := D
  joint_budget := 4 * ε_tsirelson
  budget_pos := by unfold ε_tsirelson; have := Real.one_lt_sqrt_two; linarith
  constrained := h

/- Key comparison: separable vs entangled budget efficiency -/

/-- For separable with |ε_A|, |ε_B| ≤ ε_tsirelson, CHSH enhancement ≤ 4 * ε_tsirelson² -/
lemma separable_chsh_enhancement_bound (D : SeparableDeviation)
    (hA : ∀ i, |D.ε_A i| ≤ ε_tsirelson) (hB : ∀ j, |D.ε_B j| ≤ ε_tsirelson) :
    D.totalDeviation ≤ 4 * ε_tsirelson^2 := by
  have hpos : ε_tsirelson > 0 := by unfold ε_tsirelson; have := Real.one_lt_sqrt_two; linarith
  exact separable_deviation_bound D ε_tsirelson hpos hA hB

/-- For entangled, CHSH enhancement can be 4 * ε_tsirelson (linear, not quadratic!) -/
lemma entangled_chsh_enhancement_bound (D : EntangledDeviation)
    (h : D.joint_budget = 4 * ε_tsirelson) :
    D.totalDeviation ≤ 4 * ε_tsirelson := by
  rw [← h]; exact D.constrained

/-- The ratio: entangled can have enhancement / separable enhancement = 1/ε_tsirelson -/
lemma entangled_separable_ratio :
    (4 * ε_tsirelson) / (4 * ε_tsirelson^2) = 1 / ε_tsirelson := by
  have hpos : ε_tsirelson ≠ 0 := by unfold ε_tsirelson; have := Real.one_lt_sqrt_two; linarith
  field_simp

/-- Numerically: 1/ε_tsirelson ≈ 4.83 -/
lemma entangled_advantage : 1 / ε_tsirelson = 2 / (Real.sqrt 2 - 1) := by
  unfold ε_tsirelson
  field_simp

/-- Rationalize: 2/(√2-1) = 2(√2+1)/((√2-1)(√2+1)) = 2(√2+1)/1 = 2√2 + 2 -/
lemma entangled_advantage_rationalized : 1 / ε_tsirelson = 2 * Real.sqrt 2 + 2 := by
  unfold ε_tsirelson
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  have hne : Real.sqrt 2 - 1 ≠ 0 := by have := Real.one_lt_sqrt_two; linarith
  field_simp
  linarith

/-- This is exactly 2 + CHSH_quantum! The entangled advantage factor equals 2 + 2√2 -/
lemma entangled_advantage_is_sum : 1 / ε_tsirelson = CHSH_classical + CHSH_quantum := by
  rw [entangled_advantage_rationalized]
  unfold CHSH_classical CHSH_quantum
  ring

/- Physical interpretation:
    - Separable states: enhancement is O(ε²) — second order
    - Entangled states: enhancement is O(ε) — first order

    This is because entanglement allows the "budget" to be used coherently
    rather than independently. The quantum advantage IS the shared budget. -/

/-- The CHSH value for a separable deviation -/
noncomputable def separable_CHSH_bound (δ : ℝ) : ℝ := 2 + 4 * δ^2

/-- The CHSH value for an entangled deviation -/
noncomputable def entangled_CHSH_bound (δ : ℝ) : ℝ := 2 + 4 * δ

/-- At δ = ε_tsirelson: separable gives less than entangled -/
lemma separable_less_than_entangled :
    separable_CHSH_bound ε_tsirelson < entangled_CHSH_bound ε_tsirelson := by
  unfold separable_CHSH_bound entangled_CHSH_bound
  have hpos : ε_tsirelson > 0 := by unfold ε_tsirelson; have := Real.one_lt_sqrt_two; linarith
  have hlt1 : ε_tsirelson < 1 := by unfold ε_tsirelson; have := sqrt_two_lt_two; linarith
  have h : ε_tsirelson^2 < ε_tsirelson := by
    calc ε_tsirelson^2 = ε_tsirelson * ε_tsirelson := sq ε_tsirelson
      _ < ε_tsirelson * 1 := by apply mul_lt_mul_of_pos_left hlt1 hpos
      _ = ε_tsirelson := mul_one _
  linarith

/-- Separable states cannot reach Tsirelson bound -/
lemma separable_below_tsirelson :
    separable_CHSH_bound ε_tsirelson < 2 * Real.sqrt 2 := by
  have h1 := separable_less_than_entangled
  have h2 : entangled_CHSH_bound ε_tsirelson = 2 * Real.sqrt 2 := by
    unfold entangled_CHSH_bound
    exact ε_tsirelson_value
  linarith

/-- The gap between separable and entangled at ε_tsirelson -/
noncomputable def separable_entangled_gap : ℝ :=
  entangled_CHSH_bound ε_tsirelson - separable_CHSH_bound ε_tsirelson

lemma separable_entangled_gap_value :
    separable_entangled_gap = 4 * ε_tsirelson * (1 - ε_tsirelson) := by
  unfold separable_entangled_gap entangled_CHSH_bound separable_CHSH_bound
  ring

/-- The gap in terms of √2 — NOTE: no /2, the original had an error -/
lemma separable_entangled_gap_explicit :
    separable_entangled_gap = (Real.sqrt 2 - 1) * (3 - Real.sqrt 2) := by
  rw [separable_entangled_gap_value]
  unfold ε_tsirelson
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  have hsq : Real.sqrt 2 ^ 2 = 2 := by rw [sq]; exact h
  field_simp
  ring_nf

/-! ### Joint Integral Constraints -/

/-- A model with an integral (rather than pointwise) constraint on total deviation -/
structure IntegralConstrainedModel (Λ : Type*) [MeasurableSpace Λ] extends ThermalHVModel Λ where
  /-- The integral budget -/
  budget : ℝ
  budget_pos : budget > 0
  /-- The constraint: integral of total deviation is bounded -/
  integral_constraint : ∫ ω, (|deviation.ε 0 0 ω| + |deviation.ε 0 1 ω| +
                              |deviation.ε 1 0 ω| + |deviation.ε 1 1 ω|) ∂(μ₀ : Measure Λ) ≤ budget

variable {Λ : Type*} [MeasurableSpace Λ]
variable (M : IntegralConstrainedModel Λ)

/-- Integral constraint implies thermal CHSH bound -/
theorem integral_constraint_bounds_thermal :
    |M.CHSH_thermal| ≤ M.budget := by
  unfold ThermalHVModel.CHSH_thermal
  -- Integrability helpers
  have prod_ε_int : ∀ i j, Integrable (fun ω => M.A i ω * M.B j ω * M.deviation.ε i j ω) (M.μ₀ : Measure Λ) := by
    intro i j
    have hAB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω * M.B j ω‖ ≤ 1 := by
      filter_upwards [(M.A i).ae_pm_one, (M.B j).ae_pm_one] with ω hA hB
      rcases hA with hA | hA <;> rcases hB with hB | hB <;> simp [hA, hB]
    have hAB_memLp : MemLp (fun ω => M.A i ω * M.B j ω) ⊤ (M.μ₀ : Measure Λ) := by
      apply memLp_top_of_bound
      · exact (M.A i).measurable.aestronglyMeasurable.mul (M.B j).measurable.aestronglyMeasurable
      · exact hAB_bdd
    exact (M.deviation.integrable i j).mul_of_top_right hAB_memLp
  -- The combined integrand is integrable
  have h_comb_int : Integrable (fun ω => M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
                                         M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
                                         M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
                                         M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω) (M.μ₀ : Measure Λ) :=
    ((prod_ε_int 0 1).sub (prod_ε_int 0 0)).add (prod_ε_int 1 0) |>.add (prod_ε_int 1 1)
  -- Sum of |ε| is integrable
  have h_sum_int : Integrable (fun ω => |M.deviation.ε 0 0 ω| + |M.deviation.ε 0 1 ω| +
                                        |M.deviation.ε 1 0 ω| + |M.deviation.ε 1 1 ω|) (M.μ₀ : Measure Λ) :=
    (((M.deviation.integrable 0 0).abs.add (M.deviation.integrable 0 1).abs).add
      (M.deviation.integrable 1 0).abs).add (M.deviation.integrable 1 1).abs
  -- Pointwise bound: |A*B*ε| = |ε| for dichotomic A, B
  have h_pointwise : ∀ᵐ ω ∂(M.μ₀ : Measure Λ),
      |M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
       M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
       M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
       M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω| ≤
      |M.deviation.ε 0 0 ω| + |M.deviation.ε 0 1 ω| +
      |M.deviation.ε 1 0 ω| + |M.deviation.ε 1 1 ω| := by
    filter_upwards [(M.A 0).ae_pm_one, (M.A 1).ae_pm_one,
                    (M.B 0).ae_pm_one, (M.B 1).ae_pm_one] with ω hA0 hA1 hB0 hB1
    have h01 : |M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω| = |M.deviation.ε 0 1 ω| := by
      rw [abs_mul, abs_mul]; rcases hA0 with hA0 | hA0 <;> rcases hB1 with hB1 | hB1 <;> simp [hA0, hB1]
    have h00 : |M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω| = |M.deviation.ε 0 0 ω| := by
      rw [abs_mul, abs_mul]; rcases hA0 with hA0 | hA0 <;> rcases hB0 with hB0 | hB0 <;> simp [hA0, hB0]
    have h10 : |M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω| = |M.deviation.ε 1 0 ω| := by
      rw [abs_mul, abs_mul]; rcases hA1 with hA1 | hA1 <;> rcases hB0 with hB0 | hB0 <;> simp [hA1, hB0]
    have h11 : |M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω| = |M.deviation.ε 1 1 ω| := by
      rw [abs_mul, abs_mul]; rcases hA1 with hA1 | hA1 <;> rcases hB1 with hB1 | hB1 <;> simp [hA1, hB1]
    calc |M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
          M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
          M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
          M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω|
        ≤ |M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω| +
          |M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω| +
          |M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω| +
          |M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω| := by
            have t1 := abs_sub_abs_le_abs_sub (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω)
                                              (M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω)
            have t2 := abs_add (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
                                M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω)
                               (M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω)
            have t3 := abs_add (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
                                M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
                                M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω)
                               (M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω)
            have t4 := abs_sub (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω)
                               (M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω)
            linarith
      _ = |M.deviation.ε 0 1 ω| + |M.deviation.ε 0 0 ω| +
          |M.deviation.ε 1 0 ω| + |M.deviation.ε 1 1 ω| := by rw [h01, h00, h10, h11]
      _ = |M.deviation.ε 0 0 ω| + |M.deviation.ε 0 1 ω| +
          |M.deviation.ε 1 0 ω| + |M.deviation.ε 1 1 ω| := by ring
  -- Chain the inequalities
  calc |∫ ω, M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
            M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
            M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
            M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω ∂(M.μ₀ : Measure Λ)|
      ≤ ∫ ω, |M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
              M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
              M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
              M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω| ∂(M.μ₀ : Measure Λ) :=
          abs_integral_le_integral_abs
    _ ≤ ∫ ω, (|M.deviation.ε 0 0 ω| + |M.deviation.ε 0 1 ω| +
              |M.deviation.ε 1 0 ω| + |M.deviation.ε 1 1 ω|) ∂(M.μ₀ : Measure Λ) := by
          apply integral_mono_ae h_comb_int.abs h_sum_int h_pointwise
    _ ≤ M.budget := M.integral_constraint



namespace ThermalBell
