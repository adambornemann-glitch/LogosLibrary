import LogosLibrary.Superior.SplitMechanics.BellsTheorem.TLHV.SettingDependent
open MeasureTheory
namespace ThermalBell

/-! ## Part 2: Decomposing the CHSH Value  -/

variable {Λ : Type*} [MeasurableSpace Λ]

/-- The "classical" part: what you'd get with ε = 0 -/
noncomputable def ThermalHVModel.CHSH_classical (M : ThermalHVModel Λ) : ℝ :=
  ∫ ω, (M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω +
        M.A 1 ω * M.B 0 ω + M.A 1 ω * M.B 1 ω) ∂(M.μ₀ : Measure Λ)

/-- The thermal correction: the ε-dependent terms -/
noncomputable def ThermalHVModel.CHSH_thermal (M : ThermalHVModel Λ) : ℝ :=
  ∫ ω, (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
        M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
        M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
        M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ)


/-- The CHSH value decomposes into classical + thermal parts -/
lemma CHSH_decomposition (M : ThermalHVModel Λ) :
    M.CHSH = M.CHSH_classical + M.CHSH_thermal := by
  simp only [ThermalHVModel.CHSH, ThermalHVModel.correlation,
             ThermalHVModel.CHSH_classical, ThermalHVModel.CHSH_thermal]
  have h_expand : ∀ i j, ∫ ω, M.A i ω * M.B j ω * (1 + M.deviation.ε i j ω) ∂(M.μ₀ : Measure Λ) =
      ∫ ω, M.A i ω * M.B j ω ∂(M.μ₀ : Measure Λ) +
      ∫ ω, M.A i ω * M.B j ω * M.deviation.ε i j ω ∂(M.μ₀ : Measure Λ) := by
    intro i j
    have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω‖ ≤ 1 := by
      filter_upwards [(M.A i).ae_pm_one] with ω hω
      rcases hω with h | h <;> simp [h]
    have hB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.B j ω‖ ≤ 1 := by
      filter_upwards [(M.B j).ae_pm_one] with ω hω
      rcases hω with h | h <;> simp [h]
    have hAB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω * M.B j ω‖ ≤ 1 := by
      filter_upwards [hA_bdd, hB_bdd] with ω hA hB
      calc ‖M.A i ω * M.B j ω‖
          = ‖M.A i ω‖ * ‖M.B j ω‖ := norm_mul _ _
        _ ≤ 1 * 1 := by apply mul_le_mul hA hB (norm_nonneg _) (by linarith)
        _ = 1 := by ring
    have h_int1 : Integrable (fun ω => M.A i ω * M.B j ω) (M.μ₀ : Measure Λ) := by
      apply Integrable.mono (integrable_const (1 : ℝ))
      · exact ((M.A i).measurable.mul (M.B j).measurable).aestronglyMeasurable
      · filter_upwards [hAB_bdd] with ω hω
        simp only [norm_one]
        exact hω
    have h_int2 : Integrable (fun ω => M.A i ω * M.B j ω * M.deviation.ε i j ω) (M.μ₀ : Measure Λ) := by
      have hAB_memLp : MemLp (fun ω => M.A i ω * M.B j ω) ⊤ (M.μ₀ : Measure Λ) := by
        apply memLp_top_of_bound
        · exact ((M.A i).measurable.mul (M.B j).measurable).aestronglyMeasurable
        · exact hAB_bdd
      have h := Integrable.mul_of_top_left (M.deviation.integrable i j) hAB_memLp
      simp only at h
      convert h using 1
      ext ω
      simp only [Pi.mul_apply]
      ring
    rw [← integral_add h_int1 h_int2]
    congr 1
    ext ω
    ring
  have int_AB : ∀ i j, Integrable (fun ω => M.A i ω * M.B j ω) (M.μ₀ : Measure Λ) := by
    intro i j
    have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω‖ ≤ 1 := by
      filter_upwards [(M.A i).ae_pm_one] with ω hω
      rcases hω with h | h <;> simp [h]
    have hB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.B j ω‖ ≤ 1 := by
      filter_upwards [(M.B j).ae_pm_one] with ω hω
      rcases hω with h | h <;> simp [h]
    have hAB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω * M.B j ω‖ ≤ 1 := by
      filter_upwards [hA_bdd, hB_bdd] with ω hA hB
      calc ‖M.A i ω * M.B j ω‖
          = ‖M.A i ω‖ * ‖M.B j ω‖ := norm_mul _ _
        _ ≤ 1 * 1 := by apply mul_le_mul hA hB (norm_nonneg _) (by linarith)
        _ = 1 := by ring
    apply Integrable.mono (integrable_const (1 : ℝ))
    · exact ((M.A i).measurable.mul (M.B j).measurable).aestronglyMeasurable
    · filter_upwards [hAB_bdd] with ω hω
      simp only [norm_one]
      exact hω
  have int_ABε : ∀ i j, Integrable (fun ω => M.A i ω * M.B j ω * M.deviation.ε i j ω) (M.μ₀ : Measure Λ) := by
    intro i j
    have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω‖ ≤ 1 := by
      filter_upwards [(M.A i).ae_pm_one] with ω hω
      rcases hω with h | h <;> simp [h]
    have hB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.B j ω‖ ≤ 1 := by
      filter_upwards [(M.B j).ae_pm_one] with ω hω
      rcases hω with h | h <;> simp [h]
    have hAB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω * M.B j ω‖ ≤ 1 := by
      filter_upwards [hA_bdd, hB_bdd] with ω hA hB
      calc ‖M.A i ω * M.B j ω‖
          = ‖M.A i ω‖ * ‖M.B j ω‖ := norm_mul _ _
        _ ≤ 1 * 1 := by apply mul_le_mul hA hB (norm_nonneg _) (by linarith)
        _ = 1 := by ring
    have hAB_memLp : MemLp (fun ω => M.A i ω * M.B j ω) ⊤ (M.μ₀ : Measure Λ) := by
      apply memLp_top_of_bound
      · exact ((M.A i).measurable.mul (M.B j).measurable).aestronglyMeasurable
      · exact hAB_bdd
    have h := Integrable.mul_of_top_left (M.deviation.integrable i j) hAB_memLp
    simp only at h
    convert h using 1
    ext ω
    ring_nf
    simp only [Pi.mul_apply]
    exact Eq.symm (CommMonoid.mul_comm (M.deviation.ε i j ω) ((M.A i).toFun ω * (M.B j).toFun ω))
  rw [h_expand 0 1, h_expand 0 0, h_expand 1 0, h_expand 1 1]
  -- Combine the classical integrals
  have h_classical : ∫ ω, M.A 0 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ) -
               ∫ ω, M.A 0 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ) +
               ∫ ω, M.A 1 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ) +
               ∫ ω, M.A 1 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ) =
              ∫ ω, (M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω +
                    M.A 1 ω * M.B 0 ω + M.A 1 ω * M.B 1 ω) ∂(M.μ₀ : Measure Λ) := by
    have h1 : ∫ ω, M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ) =
              ∫ ω, M.A 0 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ) - ∫ ω, M.A 0 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ) :=
      integral_sub (int_AB 0 1) (int_AB 0 0)
    have h2 : ∫ ω, (M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω + M.A 1 ω * M.B 0 ω) ∂(M.μ₀ : Measure Λ) =
              ∫ ω, M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ) + ∫ ω, M.A 1 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ) :=
      integral_add ((int_AB 0 1).sub (int_AB 0 0)) (int_AB 1 0)
    have h3 : ∫ ω, (M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω + M.A 1 ω * M.B 0 ω + M.A 1 ω * M.B 1 ω) ∂(M.μ₀ : Measure Λ) =
              ∫ ω, (M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω + M.A 1 ω * M.B 0 ω) ∂(M.μ₀ : Measure Λ) +
              ∫ ω, M.A 1 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ) :=
      integral_add (((int_AB 0 1).sub (int_AB 0 0)).add (int_AB 1 0)) (int_AB 1 1)
    linarith [h1, h2, h3]
  have h_thermal : ∫ ω, M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω ∂(M.μ₀ : Measure Λ) -
               ∫ ω, M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω ∂(M.μ₀ : Measure Λ) +
               ∫ ω, M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω ∂(M.μ₀ : Measure Λ) +
               ∫ ω, M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω ∂(M.μ₀ : Measure Λ) =
              ∫ ω, (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
                    M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
                    M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
                    M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ) := by
    have h1 : ∫ ω, M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω - M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω ∂(M.μ₀ : Measure Λ) =
              ∫ ω, M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω ∂(M.μ₀ : Measure Λ) -
              ∫ ω, M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω ∂(M.μ₀ : Measure Λ) :=
      integral_sub (int_ABε 0 1) (int_ABε 0 0)
    have h2 : ∫ ω, (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω - M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
                    M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω) ∂(M.μ₀ : Measure Λ) =
              ∫ ω, M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω - M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω ∂(M.μ₀ : Measure Λ) +
              ∫ ω, M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω ∂(M.μ₀ : Measure Λ) :=
      integral_add ((int_ABε 0 1).sub (int_ABε 0 0)) (int_ABε 1 0)
    have h3 : ∫ ω, (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω - M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
                    M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω + M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ) =
              ∫ ω, (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω - M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
                    M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω) ∂(M.μ₀ : Measure Λ) +
              ∫ ω, M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω ∂(M.μ₀ : Measure Λ) :=
      integral_add (((int_ABε 0 1).sub (int_ABε 0 0)).add (int_ABε 1 0)) (int_ABε 1 1)
    linarith [h1, h2, h3]
  calc _ = (∫ ω, M.A 0 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ) -
           ∫ ω, M.A 0 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ) +
           ∫ ω, M.A 1 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ) +
           ∫ ω, M.A 1 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ)) +
          (∫ ω, M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω ∂(M.μ₀ : Measure Λ) -
           ∫ ω, M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω ∂(M.μ₀ : Measure Λ) +
           ∫ ω, M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω ∂(M.μ₀ : Measure Λ) +
           ∫ ω, M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω ∂(M.μ₀ : Measure Λ)) := by ring
    _ = _ := by rw [h_classical, h_thermal]

/-- The classical part satisfies |S_classical| ≤ 2 -/
lemma CHSH_classical_bound (M : ThermalHVModel Λ) :
    |M.CHSH_classical| ≤ 2 := by
  simp only [ThermalHVModel.CHSH_classical]
  -- The integrand is bounded by 2 pointwise (almost everywhere)
  have h_pointwise : ∀ᵐ ω ∂(M.μ₀ : Measure Λ),
      |M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω +
       M.A 1 ω * M.B 0 ω + M.A 1 ω * M.B 1 ω| ≤ 2 := by
    have hA0 := (M.A 0).ae_pm_one
    have hA1 := (M.A 1).ae_pm_one
    have hB0 := (M.B 0).ae_pm_one
    have hB1 := (M.B 1).ae_pm_one
    filter_upwards [hA0, hA1, hB0, hB1] with ω hA0ω hA1ω hB0ω hB1ω
    -- Rewrite as A₀(B₁ - B₀) + A₁(B₀ + B₁)
    have h_eq : M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω +
                M.A 1 ω * M.B 0 ω + M.A 1 ω * M.B 1 ω =
                M.A 0 ω * (M.B 1 ω - M.B 0 ω) + M.A 1 ω * (M.B 0 ω + M.B 1 ω) := by ring
    rw [h_eq]
    -- When B₀ = B₁: first term = 0, second term = ±2
    -- When B₀ = -B₁: first term = ±2, second term = 0
    rcases hB0ω with hB0_pos | hB0_neg <;> rcases hB1ω with hB1_pos | hB1_neg <;>
    rcases hA0ω with hA0_pos | hA0_neg <;> rcases hA1ω with hA1_pos | hA1_neg <;>
    simp_all only [Fin.isValue] <;> norm_num
  -- Integrability
  have h_int : Integrable (fun ω => M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω +
                                    M.A 1 ω * M.B 0 ω + M.A 1 ω * M.B 1 ω) (M.μ₀ : Measure Λ) := by
    have hA_bdd : ∀ i, ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω‖ ≤ 1 := fun i => by
      filter_upwards [(M.A i).ae_pm_one] with ω hω
      rcases hω with h | h <;> simp [h]
    have hB_bdd : ∀ j, ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.B j ω‖ ≤ 1 := fun j => by
      filter_upwards [(M.B j).ae_pm_one] with ω hω
      rcases hω with h | h <;> simp [h]
    have hAB_int : ∀ i j, Integrable (fun ω => M.A i ω * M.B j ω) (M.μ₀ : Measure Λ) := by
      intro i j
      have hAB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω * M.B j ω‖ ≤ 1 := by
        filter_upwards [hA_bdd i, hB_bdd j] with ω hA hB
        calc ‖M.A i ω * M.B j ω‖ = ‖M.A i ω‖ * ‖M.B j ω‖ := norm_mul _ _
          _ ≤ 1 * 1 := by apply mul_le_mul hA hB (norm_nonneg _) (by linarith)
          _ = 1 := by ring
      apply Integrable.mono (integrable_const (1 : ℝ))
      · exact ((M.A i).measurable.mul (M.B j).measurable).aestronglyMeasurable
      · filter_upwards [hAB_bdd] with ω hω; simp only [norm_one]; exact hω
    have h := ((hAB_int 0 1).sub (hAB_int 0 0)).add ((hAB_int 1 0).add (hAB_int 1 1))
    convert h using 1
    ext ω
    simp only [Fin.isValue, Pi.add_apply, Pi.sub_apply]
    ring

  -- The integral of a bounded function is bounded
  calc |∫ ω, (M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω +
              M.A 1 ω * M.B 0 ω + M.A 1 ω * M.B 1 ω) ∂(M.μ₀ : Measure Λ)|
      ≤ ∫ ω, |M.A 0 ω * M.B 1 ω - M.A 0 ω * M.B 0 ω +
              M.A 1 ω * M.B 0 ω + M.A 1 ω * M.B 1 ω| ∂(M.μ₀ : Measure Λ) :=
          abs_integral_le_integral_abs
    _ ≤ ∫ ω, (2 : ℝ) ∂(M.μ₀ : Measure Λ) := by
          apply integral_mono_ae
          · exact h_int.abs
          · exact integrable_const 2
          · exact h_pointwise
    _ = 2 * ((M.μ₀ : Measure Λ) Set.univ).toReal := by
          rw [integral_const]
          simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul, measure_univ,
            ENNReal.toReal_one, mul_one]
    _ = 2 := by simp [measure_univ]


/-- The thermal part is bounded by the sup-norm of ε -/
lemma CHSH_thermal_bound (M : ThermalHVModel Λ) (ε_max : ℝ) --(hε_max : 0 ≤ ε_max)
    (hε_sup : ∀ i j ω, |M.deviation.ε i j ω| ≤ ε_max) :
    |M.CHSH_thermal| ≤ 4 * ε_max := by
  simp only [ThermalHVModel.CHSH_thermal]
  -- a.e. bounds on A and B
  have hA_bdd : ∀ i, ∀ᵐ ω ∂(M.μ₀ : Measure Λ), |M.A i ω| ≤ 1 := fun i => by
    filter_upwards [(M.A i).ae_pm_one] with ω hω
    rcases hω with h | h <;> simp [h]
  have hB_bdd : ∀ j, ∀ᵐ ω ∂(M.μ₀ : Measure Λ), |M.B j ω| ≤ 1 := fun j => by
    filter_upwards [(M.B j).ae_pm_one] with ω hω
    rcases hω with h | h <;> simp [h]
  -- The integrand is bounded by 4 * ε_max a.e.
  have h_pointwise : ∀ᵐ ω ∂(M.μ₀ : Measure Λ),
      |M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
       M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
       M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
       M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω| ≤ 4 * ε_max := by
    filter_upwards [hA_bdd 0, hA_bdd 1, hB_bdd 0, hB_bdd 1] with ω hA0 hA1 hB0 hB1
    have h_term_bound : ∀ i j, |M.A i ω * M.B j ω * M.deviation.ε i j ω| ≤ ε_max := by
      intro i j
      have hε := hε_sup i j ω
      have hA : |M.A i ω| ≤ 1 := by fin_cases i <;> assumption
      have hB : |M.B j ω| ≤ 1 := by fin_cases j <;> assumption
      calc |M.A i ω * M.B j ω * M.deviation.ε i j ω|
          = |M.A i ω| * |M.B j ω| * |M.deviation.ε i j ω| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * 1 * ε_max := by
            apply mul_le_mul (mul_le_mul hA hB (abs_nonneg _) (by linarith)) hε (abs_nonneg _)
            linarith
        _ = ε_max := by ring
    calc |M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
          M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
          M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
          M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω|
        ≤ |M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω| +
          |M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω| +
          |M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω| +
          |M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω| := by
            have h1 := abs_add (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
                                M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
                                M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω)
                               (M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω)
            have h2 := abs_add (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
                                M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω)
                               (M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω)
            have h3 := abs_sub (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω)
                               (M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω)
            linarith
      _ ≤ ε_max + ε_max + ε_max + ε_max := by
          linarith [h_term_bound 0 1, h_term_bound 0 0, h_term_bound 1 0, h_term_bound 1 1]
      _ = 4 * ε_max := by ring
  -- Integrability
  have h_int : Integrable (fun ω => M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
                                    M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
                                    M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
                                    M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω) (M.μ₀ : Measure Λ) := by
    have hABε_int : ∀ i j, Integrable (fun ω => M.A i ω * M.B j ω * M.deviation.ε i j ω) (M.μ₀ : Measure Λ) := by
      intro i j
      have hAB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω * M.B j ω‖ ≤ 1 := by
        filter_upwards [hA_bdd i, hB_bdd j] with ω hA hB
        rw [Real.norm_eq_abs, abs_mul]
        calc |M.A i ω| * |M.B j ω| ≤ 1 * 1 := by
              apply mul_le_mul hA hB (abs_nonneg _) (by linarith)
          _ = 1 := by ring
      have hAB_memLp : MemLp (fun ω => M.A i ω * M.B j ω) ⊤ (M.μ₀ : Measure Λ) := by
        apply memLp_top_of_bound
        · exact ((M.A i).measurable.mul (M.B j).measurable).aestronglyMeasurable
        · convert hAB_bdd using 1
      have h := Integrable.mul_of_top_left (M.deviation.integrable i j) hAB_memLp
      simp only at h
      convert h using 1
      ext ω ; simp only [Pi.mul_apply] ; ring_nf
    have h := ((hABε_int 0 1).sub (hABε_int 0 0)).add ((hABε_int 1 0).add (hABε_int 1 1))
    convert h using 1
    ext ω; simp only [Fin.isValue, Pi.add_apply, Pi.sub_apply] ; ring
  -- The integral is bounded
  calc |∫ ω, (M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
              M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
              M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
              M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ)|
      ≤ ∫ ω, |M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
              M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
              M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
              M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω| ∂(M.μ₀ : Measure Λ) :=
          abs_integral_le_integral_abs
    _ ≤ ∫ ω, (4 * ε_max) ∂(M.μ₀ : Measure Λ) := by
          apply integral_mono_ae
          · exact h_int.abs
          · exact integrable_const _
          · exact h_pointwise
    _ = 4 * ε_max * ((M.μ₀ : Measure Λ) Set.univ).toReal := by
          rw [integral_const]
          simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul, measure_univ,
            ENNReal.toReal_one, mul_one]
    _ = 4 * ε_max := by simp [measure_univ]



/-- **Main Theorem**: The thermal CHSH bound -/
lemma thermal_CHSH_bound (M : ThermalHVModel Λ) (ε_max : ℝ) --(hε_max : 0 ≤ ε_max)
    (hε_sup : ∀ i j ω, |M.deviation.ε i j ω| ≤ ε_max) :
    |M.CHSH| ≤ 2 + 4 * ε_max := by
  calc |M.CHSH|
      = |M.CHSH_classical + M.CHSH_thermal| := by rw [CHSH_decomposition]
    _ ≤ |M.CHSH_classical| + |M.CHSH_thermal| := abs_add _ _
    _ ≤ 2 + 4 * ε_max := by
        have h1 := CHSH_classical_bound M
        have h2 := CHSH_thermal_bound M ε_max hε_sup
        linarith

end ThermalBell
