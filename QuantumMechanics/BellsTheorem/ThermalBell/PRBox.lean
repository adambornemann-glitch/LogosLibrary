import LogosLibrary.QuantumMechanics.BellsTheorem.TLHV

open ThermalBell BellTheorem

namespace ThermalBell
/-! ## Part 10: The PR-Box Limit and Why Tsirelson < 4

The Popescu-Rohrlich (PR) box achieves |S| = 4, the algebraic maximum.
In the thermal framework: 2 + 4ε = 4 ⟹ ε = 1/2.

But our CorrelationDeviation requires |ε| < 1 to keep 1 + ε > 0.
What happens as ε → 1/2? What breaks at ε = 1?
-/

/-- The ε value for a PR box -/
noncomputable def ε_PR : ℝ := 1/2

/-- PR box would require ε = 1/2 -/
lemma pr_box_epsilon : 2 + 4 * ε_PR = 4 := by
  unfold ε_PR
  ring

/-- The algebraic maximum of CHSH is 4 -/
def CHSH_algebraic_max : ℝ := 4

/-- Tsirelson is strictly less than the algebraic max -/
lemma tsirelson_lt_algebraic : 2 * Real.sqrt 2 < CHSH_algebraic_max := by
  unfold CHSH_algebraic_max
  have h : Real.sqrt 2 < 2 := sqrt_two_lt_two
  linarith

/-- The gap between Tsirelson and algebraic max -/
noncomputable def tsirelson_gap : ℝ := CHSH_algebraic_max - 2 * Real.sqrt 2

lemma tsirelson_gap_pos : tsirelson_gap > 0 := by
  unfold tsirelson_gap CHSH_algebraic_max
  have h : Real.sqrt 2 < 2 := sqrt_two_lt_two
  linarith

/-- The gap in terms of ε -/
lemma tsirelson_gap_epsilon : ε_PR - ε_tsirelson = tsirelson_gap / 4 := by
  unfold ε_PR ε_tsirelson tsirelson_gap CHSH_algebraic_max
  ring

/-- As ε → 1, the effective density 1 + ε can approach 0 -/
lemma density_positivity_constraint (ε : ℝ) (hε : |ε| < 1) (_ω : Λ) :
    1 + ε > 0 := by
  have h := abs_lt.mp hε
  linarith

/-- At ε = 1, density can be zero — measure degenerates -/
lemma density_at_boundary : (1 : ℝ) + (-1) = 0 := by ring

/-- The effective measure weight at a point -/
noncomputable def effectiveWeight (ε_val : ℝ) : ℝ := 1 + ε_val

/-- For PR box (ε = 1/2), the weight is still safely positive -/
lemma pr_weight_positive : effectiveWeight ε_PR > 0 := by
  unfold effectiveWeight ε_PR
  norm_num

/-- For PR box, the minimum weight (at ε = -1/2) is also positive -/
lemma pr_weight_min_positive : effectiveWeight (-ε_PR) > 0 := by
  unfold effectiveWeight ε_PR
  norm_num

/- So why can't we have a PR box? The constraint is more subtle.

    The issue: for PR-box correlations, the JOINT probability distribution
    P(a,b|x,y) must be non-signaling but the MARGINALS must be uniform.

    In the thermal model: ε(i,j,ω) affects the measure, but the
    response functions A_i(ω), B_j(ω) are still dichotomic (±1).

    The constraint comes from: the CORRELATION structure, not just the bound.
-/
variable {Λ : Type*} [MeasurableSpace Λ]

/-- For any ε, the pointwise CHSH is still ±2 -/
lemma pointwise_chsh_still_pm_two (M : ThermalHVModel Λ) (ω : Λ)
    (hA₀ : M.A 0 ω = 1 ∨ M.A 0 ω = -1)
    (hA₁ : M.A 1 ω = 1 ∨ M.A 1 ω = -1)
    (hB₀ : M.B 0 ω = 1 ∨ M.B 0 ω = -1)
    (hB₁ : M.B 1 ω = 1 ∨ M.B 1 ω = -1) :
    M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω +
    M.A 1 ω * M.B 0 ω + M.A 1 ω * M.B 1 ω = 2 ∨
    M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω +
    M.A 1 ω * M.B 0 ω + M.A 1 ω * M.B 1 ω = -2 := by
  rcases hA₀ with hA₀ | hA₀ <;> rcases hA₁ with hA₁ | hA₁ <;>
  rcases hB₀ with hB₀ | hB₀ <;> rcases hB₁ with hB₁ | hB₁ <;>
  simp [hA₀, hA₁, hB₀, hB₁] <;> ring_nf <;> simp

/- The key insight: to get S > 2, we need the thermal weights (1 + ε)
    to be CORRELATED with the pointwise CHSH value.

    If CHSH_pointwise(ω) = +2 and we want S > 2, we need:
    - More weight where CHSH = +2
    - Less weight where CHSH = -2

    This correlation between ε and the hidden variable is exactly
    what "measurement dependence" means.
-/

/-- The thermal enhancement requires sign correlation -/
lemma thermal_enhancement_mechanism (M : ThermalHVModel Λ) :
    -- For S > 2, we need ε to be positively correlated with CHSH_pointwise
    M.CHSH > 2 → M.CHSH_thermal > 0 := by
  intro hS
  have h := CHSH_decomposition M
  have hcl := CHSH_classical_bound M
  -- |S_classical| ≤ 2, so S_classical ≤ 2
  have hcl' : M.CHSH_classical ≤ 2 := (abs_le.mp hcl).2
  linarith

/-- The thermal enhancement has a maximum rate per unit ε -/
lemma thermal_rate_bound (M : ThermalHVModel Λ) (ε_max : ℝ) (hε_pos : ε_max > 0)
    (hε_sup : ∀ i j ω, |M.deviation.ε i j ω| ≤ ε_max) :
    M.CHSH_thermal ≤ 4 * ε_max := by
  have h := CHSH_thermal_bound M ε_max hε_sup
  have h' := abs_le.mp (le_of_eq (abs_of_nonneg (by linarith : 4 * ε_max ≥ 0)))
  exact (abs_le.mp h).2

/- The fundamental limit: even with perfect correlation between ε and CHSH_pointwise,
    we can only get S_thermal ≤ 4 * ε_max.

    Combined with S_classical ≤ 2 (which can be saturated), we get S ≤ 2 + 4ε_max.

    For S = 4 (PR box), we'd need ε_max = 1/2.

    But KMS constrains ε_max ≤ ε_tsirelson = (√2-1)/2 ≈ 0.207 < 1/2.

    This is WHY Tsirelson < 4: the modular periodicity prevents
    strong enough measurement dependence to reach the PR box.
-/

/-- The hierarchy of bounds -/
theorem bounds_hierarchy :
    2 < 2 * Real.sqrt 2 ∧ 2 * Real.sqrt 2 < 4 := by
  constructor
  · have h : Real.sqrt 2 > 1 := Real.one_lt_sqrt_two
    linarith
  · have h : Real.sqrt 2 < 2 := sqrt_two_lt_two
    linarith

/-- The corresponding ε hierarchy -/
theorem epsilon_hierarchy :
    (0 : ℝ) < ε_tsirelson ∧ ε_tsirelson < ε_PR ∧ ε_PR < 1 := by
  unfold ε_tsirelson ε_PR
  constructor
  · have h : Real.sqrt 2 > 1 := Real.one_lt_sqrt_two
    linarith
  constructor
  · have h : Real.sqrt 2 < 2 := sqrt_two_lt_two
    linarith
  · norm_num

end ThermalBell
