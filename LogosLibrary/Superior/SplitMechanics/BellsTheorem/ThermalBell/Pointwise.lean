import LogosLibrary.Superior.SplitMechanics.BellsTheorem.ThermalBell.SharedEnBudget

open ThermalBell BellTheorem ProbabilityTheory MeasureTheory

namespace ThermalBell

/-- The ε value a separable model needs to achieve a given CHSH value -/
noncomputable def separable_ε_for_CHSH (S : ℝ) : ℝ := Real.sqrt ((S - 2) / 4)

/-- The ε value an entangled model needs to achieve a given CHSH value -/
noncomputable def entangled_ε_for_CHSH (S : ℝ) : ℝ := (S - 2) / 4

/-- Separable needs √ε_tsirelson to reach Tsirelson, entangled needs ε_tsirelson -/
theorem separable_needs_more_ε_for_tsirelson :
    separable_ε_for_CHSH (2 * Real.sqrt 2) = Real.sqrt ε_tsirelson := by
  unfold separable_ε_for_CHSH ε_tsirelson
  congr 1
  have h : 2 * Real.sqrt 2 - 2 = 2 * (Real.sqrt 2 - 1) := by ring
  rw [h]
  ring

/-- √ε_tsirelson > ε_tsirelson (separable needs bigger individual ε) -/
theorem sqrt_ε_tsirelson_gt : Real.sqrt ε_tsirelson > ε_tsirelson := by
  have hpos : ε_tsirelson > 0 := by unfold ε_tsirelson; have := Real.one_lt_sqrt_two; linarith
  have hlt1 : ε_tsirelson < 1 := by unfold ε_tsirelson; have := sqrt_two_lt_two; linarith
  have hsqrt_pos : Real.sqrt ε_tsirelson > 0 := Real.sqrt_pos.mpr hpos
  have hsqrt_lt1 : Real.sqrt ε_tsirelson < 1 := by
    have h := Real.sqrt_lt_sqrt (le_of_lt hpos) hlt1
    rwa [Real.sqrt_one] at h
  calc ε_tsirelson
      = (Real.sqrt ε_tsirelson)^2 := (Real.sq_sqrt (le_of_lt hpos)).symm
    _ = Real.sqrt ε_tsirelson * Real.sqrt ε_tsirelson := sq (Real.sqrt ε_tsirelson)
    _ < Real.sqrt ε_tsirelson * 1 := by apply mul_lt_mul_of_pos_left hsqrt_lt1 hsqrt_pos
    _ = Real.sqrt ε_tsirelson := mul_one _

variable {Λ : Type*} [MeasurableSpace Λ]

/-- Pointwise bound implies integral bound -/
theorem pointwise_implies_integral (M : ThermalHVModel Λ) (δ : ℝ)
    (h : ∀ i j ω, |M.deviation.ε i j ω| ≤ δ) :
    ∫ ω, (|M.deviation.ε 0 0 ω| + |M.deviation.ε 0 1 ω| +
          |M.deviation.ε 1 0 ω| + |M.deviation.ε 1 1 ω|) ∂(M.μ₀ : Measure Λ) ≤ 4 * δ := by
  -- Pointwise bound
  have h_pw : ∀ ω, |M.deviation.ε 0 0 ω| + |M.deviation.ε 0 1 ω| +
                   |M.deviation.ε 1 0 ω| + |M.deviation.ε 1 1 ω| ≤ 4 * δ := by
    intro ω
    have h00 := h 0 0 ω
    have h01 := h 0 1 ω
    have h10 := h 1 0 ω
    have h11 := h 1 1 ω
    linarith
  -- Integrability
  have h_int : Integrable (fun ω => |M.deviation.ε 0 0 ω| + |M.deviation.ε 0 1 ω| +
                                    |M.deviation.ε 1 0 ω| + |M.deviation.ε 1 1 ω|) (M.μ₀ : Measure Λ) :=
    (((M.deviation.integrable 0 0).abs.add (M.deviation.integrable 0 1).abs).add
      (M.deviation.integrable 1 0).abs).add (M.deviation.integrable 1 1).abs
  -- Apply integral bound
  calc ∫ ω, (|M.deviation.ε 0 0 ω| + |M.deviation.ε 0 1 ω| +
            |M.deviation.ε 1 0 ω| + |M.deviation.ε 1 1 ω|) ∂(M.μ₀ : Measure Λ)
      ≤ ∫ ω, (4 * δ) ∂(M.μ₀ : Measure Λ) := by
          apply integral_mono h_int (integrable_const _)
          intro ω
          exact h_pw ω
    _ = 4 * δ := by simp [integral_const, measureReal_univ_eq_one]


/-- Entangled ε needed to reach Tsirelson -/
theorem entangled_ε_for_tsirelson :
    entangled_ε_for_CHSH (2 * Real.sqrt 2) = ε_tsirelson := by
  unfold entangled_ε_for_CHSH ε_tsirelson
  ring

/-- Entangled is √(1/ε_tsirelson) ≈ 2.2x more efficient than separable -/
theorem entangled_efficiency_ratio :
    separable_ε_for_CHSH (2 * Real.sqrt 2) / entangled_ε_for_CHSH (2 * Real.sqrt 2) =
    Real.sqrt (1 / ε_tsirelson) := by
  rw [separable_needs_more_ε_for_tsirelson, entangled_ε_for_tsirelson]
  have hpos : ε_tsirelson > 0 := by unfold ε_tsirelson; have := Real.one_lt_sqrt_two; linarith
  simp only [one_div, Real.sqrt_inv]
  exact Real.sqrt_div_self

/-- Alternative form: ratio = 1 / √ε_tsirelson -/
theorem entangled_efficiency_ratio' :
    separable_ε_for_CHSH (2 * Real.sqrt 2) / entangled_ε_for_CHSH (2 * Real.sqrt 2) =
    1 / Real.sqrt ε_tsirelson := by
  rw [entangled_efficiency_ratio]
  have hpos : ε_tsirelson > 0 := by unfold ε_tsirelson; have := Real.one_lt_sqrt_two; linarith
  simp only [one_div, Real.sqrt_inv]

/-- The efficiency ratio squared is 1/ε_tsirelson = 2 + 2√2 (from SharedEnBudget!) -/
theorem efficiency_ratio_squared :
    (separable_ε_for_CHSH (2 * Real.sqrt 2) / entangled_ε_for_CHSH (2 * Real.sqrt 2))^2 =
    1 / ε_tsirelson := by
  rw [entangled_efficiency_ratio]
  have hpos : ε_tsirelson > 0 := by unfold ε_tsirelson; have := Real.one_lt_sqrt_two; linarith
  have h := Real.sq_sqrt (by positivity : 1 / ε_tsirelson ≥ 0)
  rw [sq] at h ⊢
  rw [h]
