import LogosLibrary.QuantumMechanics.BellsTheorem.ThermalBell

open MeasureTheory

namespace ThermalBell

/-! ## Part 14: The No-Signaling Constraint-/
variable {Λ : Type*} [MeasurableSpace Λ]


/-- Alice's marginal expectation for setting i, when Bob uses setting j -/
noncomputable def aliceMarginal (M : ThermalHVModel Λ) (i j : Fin 2) : ℝ :=
  ∫ ω, M.A i ω * (1 + M.deviation.ε i j ω) ∂(M.μ₀ : Measure Λ)

/-- Bob's marginal expectation for setting j, when Alice uses setting i -/
noncomputable def bobMarginal (M : ThermalHVModel Λ) (i j : Fin 2) : ℝ :=
  ∫ ω, M.B j ω * (1 + M.deviation.ε i j ω) ∂(M.μ₀ : Measure Λ)

/-- No-signaling for Alice: her marginal is independent of Bob's setting -/
def noSignalingAlice (M : ThermalHVModel Λ) : Prop :=
  ∀ i : Fin 2, aliceMarginal M i 0 = aliceMarginal M i 1

/-- No-signaling for Bob: his marginal is independent of Alice's setting -/
def noSignalingBob (M : ThermalHVModel Λ) : Prop :=
  ∀ j : Fin 2, bobMarginal M 0 j = bobMarginal M 1 j

/-- Full no-signaling: both directions -/
def noSignaling (M : ThermalHVModel Λ) : Prop :=
  noSignalingAlice M ∧ noSignalingBob M

/-- The no-signaling constraint on ε for Alice -/
lemma noSignaling_alice_constraint (M : ThermalHVModel Λ) :
    noSignalingAlice M ↔
    ∀ i : Fin 2, ∫ ω, M.A i ω * M.deviation.ε i 0 ω ∂(M.μ₀ : Measure Λ) =
                ∫ ω, M.A i ω * M.deviation.ε i 1 ω ∂(M.μ₀ : Measure Λ) := by
  unfold noSignalingAlice aliceMarginal
  constructor
  · intro h i
    have hi := h i
    have hA_int : Integrable (M.A i).toFun (M.μ₀ : Measure Λ) := (M.A i).integrable
    have hAε0_int : Integrable (fun ω => M.A i ω * M.deviation.ε i 0 ω) (M.μ₀ : Measure Λ) := by
      have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω‖ ≤ 1 := by
        filter_upwards [(M.A i).ae_pm_one] with ω hω
        rcases hω with h | h <;> simp [h]
      have hA_memLp : MemLp (M.A i).toFun ⊤ (M.μ₀ : Measure Λ) := by
        apply memLp_top_of_bound
        · exact (M.A i).measurable.aestronglyMeasurable
        · exact hA_bdd
      exact (M.deviation.integrable i 0).mul_of_top_right hA_memLp
    have hAε1_int : Integrable (fun ω => M.A i ω * M.deviation.ε i 1 ω) (M.μ₀ : Measure Λ) := by
      have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω‖ ≤ 1 := by
        filter_upwards [(M.A i).ae_pm_one] with ω hω
        rcases hω with h | h <;> simp [h]
      have hA_memLp : MemLp (M.A i).toFun ⊤ (M.μ₀ : Measure Λ) := by
        apply memLp_top_of_bound
        · exact (M.A i).measurable.aestronglyMeasurable
        · exact hA_bdd
      exact (M.deviation.integrable i 1).mul_of_top_right hA_memLp
    have h0 : ∫ ω, M.A i ω * (1 + M.deviation.ε i 0 ω) ∂(M.μ₀ : Measure Λ) =
              ∫ ω, M.A i ω ∂(M.μ₀ : Measure Λ) + ∫ ω, M.A i ω * M.deviation.ε i 0 ω ∂(M.μ₀ : Measure Λ) := by
      rw [← integral_add hA_int hAε0_int]
      congr 1; ext ω; ring
    have h1 : ∫ ω, M.A i ω * (1 + M.deviation.ε i 1 ω) ∂(M.μ₀ : Measure Λ) =
              ∫ ω, M.A i ω ∂(M.μ₀ : Measure Λ) + ∫ ω, M.A i ω * M.deviation.ε i 1 ω ∂(M.μ₀ : Measure Λ) := by
      rw [← integral_add hA_int hAε1_int]
      congr 1; ext ω; ring
    rw [h0, h1] at hi
    linarith
  · intro h i
    have hi := h i
    have hA_int : Integrable (M.A i).toFun (M.μ₀ : Measure Λ) := (M.A i).integrable
    have hAε0_int : Integrable (fun ω => M.A i ω * M.deviation.ε i 0 ω) (M.μ₀ : Measure Λ) := by
      have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω‖ ≤ 1 := by
        filter_upwards [(M.A i).ae_pm_one] with ω hω
        rcases hω with h | h <;> simp [h]
      have hA_memLp : MemLp (M.A i).toFun ⊤ (M.μ₀ : Measure Λ) := by
        apply memLp_top_of_bound
        · exact (M.A i).measurable.aestronglyMeasurable
        · exact hA_bdd
      exact (M.deviation.integrable i 0).mul_of_top_right hA_memLp
    have hAε1_int : Integrable (fun ω => M.A i ω * M.deviation.ε i 1 ω) (M.μ₀ : Measure Λ) := by
      have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω‖ ≤ 1 := by
        filter_upwards [(M.A i).ae_pm_one] with ω hω
        rcases hω with h | h <;> simp [h]
      have hA_memLp : MemLp (M.A i).toFun ⊤ (M.μ₀ : Measure Λ) := by
        apply memLp_top_of_bound
        · exact (M.A i).measurable.aestronglyMeasurable
        · exact hA_bdd
      exact (M.deviation.integrable i 1).mul_of_top_right hA_memLp
    have h0 : ∫ ω, M.A i ω * (1 + M.deviation.ε i 0 ω) ∂(M.μ₀ : Measure Λ) =
              ∫ ω, M.A i ω ∂(M.μ₀ : Measure Λ) + ∫ ω, M.A i ω * M.deviation.ε i 0 ω ∂(M.μ₀ : Measure Λ) := by
      rw [← integral_add hA_int hAε0_int]
      congr 1; ext ω; ring
    have h1 : ∫ ω, M.A i ω * (1 + M.deviation.ε i 1 ω) ∂(M.μ₀ : Measure Λ) =
              ∫ ω, M.A i ω ∂(M.μ₀ : Measure Λ) + ∫ ω, M.A i ω * M.deviation.ε i 1 ω ∂(M.μ₀ : Measure Λ) := by
      rw [← integral_add hA_int hAε1_int]
      congr 1; ext ω; ring
    rw [h0, h1]
    linarith

/-- No-signaling constraint in difference form -/
def noSignalingDiff (M : ThermalHVModel Λ) : Prop :=
  (∀ i : Fin 2, ∫ ω, M.A i ω * (M.deviation.ε i 0 ω - M.deviation.ε i 1 ω) ∂(M.μ₀ : Measure Λ) = 0) ∧
  (∀ j : Fin 2, ∫ ω, M.B j ω * (M.deviation.ε 0 j ω - M.deviation.ε 1 j ω) ∂(M.μ₀ : Measure Λ) = 0)

/-- A sufficient condition: ε is independent of the "other" setting -/
def settingIndependent (M : ThermalHVModel Λ) : Prop :=
  (∀ i : Fin 2, ∀ ω, M.deviation.ε i 0 ω = M.deviation.ε i 1 ω) ∧
  (∀ j : Fin 2, ∀ ω, M.deviation.ε 0 j ω = M.deviation.ε 1 j ω)

/-- Setting independence implies no-signaling -/
lemma settingIndependent_implies_noSignaling (M : ThermalHVModel Λ)
    (h : settingIndependent M) : noSignaling M := by
  unfold settingIndependent at h
  obtain ⟨hA, hB⟩ := h
  constructor
  · unfold noSignalingAlice aliceMarginal
    intro i
    congr 1
    ext ω
    rw [hA i ω]
  · unfold noSignalingBob bobMarginal
    intro j
    congr 1
    ext ω
    rw [hB j ω]

/- The converse is NOT true in general: no-signaling allows more freedom -/
-- (We won't prove this formally, but note it)

/-- A no-signaling thermal model -/
structure NoSignalingThermalModel (Λ : Type*) [MeasurableSpace Λ] extends ThermalHVModel Λ where
  no_signaling : noSignaling toThermalHVModel


/-! ### Consequences of No-Signaling

No-signaling constrains the ε structure. What does this mean for CHSH?
-/

/-- The "signaling potential" - measures how much ε could signal -/
noncomputable def signalingPotentialAlice (M : ThermalHVModel Λ) (i : Fin 2) : ℝ :=
  |∫ ω, M.A i ω * (M.deviation.ε i 0 ω - M.deviation.ε i 1 ω) ∂(M.μ₀ : Measure Λ)|

noncomputable def signalingPotentialBob (M : ThermalHVModel Λ) (j : Fin 2) : ℝ :=
  |∫ ω, M.B j ω * (M.deviation.ε 0 j ω - M.deviation.ε 1 j ω) ∂(M.μ₀ : Measure Λ)|

/-- No-signaling means zero signaling potential -/
lemma noSignaling_iff_zero_potential (M : ThermalHVModel Λ) :
    noSignaling M ↔
    (∀ i, signalingPotentialAlice M i = 0) ∧ (∀ j, signalingPotentialBob M j = 0) := by
  unfold noSignaling noSignalingAlice noSignalingBob
  unfold signalingPotentialAlice signalingPotentialBob
  unfold aliceMarginal bobMarginal
  constructor
  · intro ⟨hA, hB⟩
    constructor
    · intro i
      have hi := hA i
      have hA_int : Integrable (M.A i).toFun (M.μ₀ : Measure Λ) := (M.A i).integrable
      have hAε0_int : Integrable (fun ω => M.A i ω * M.deviation.ε i 0 ω) (M.μ₀ : Measure Λ) := by
        have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω‖ ≤ 1 := by
          filter_upwards [(M.A i).ae_pm_one] with ω hω
          rcases hω with h | h <;> simp [h]
        have hA_memLp : MemLp (M.A i).toFun ⊤ (M.μ₀ : Measure Λ) := by
          apply memLp_top_of_bound
          · exact (M.A i).measurable.aestronglyMeasurable
          · exact hA_bdd
        exact (M.deviation.integrable i 0).mul_of_top_right hA_memLp
      have hAε1_int : Integrable (fun ω => M.A i ω * M.deviation.ε i 1 ω) (M.μ₀ : Measure Λ) := by
        have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω‖ ≤ 1 := by
          filter_upwards [(M.A i).ae_pm_one] with ω hω
          rcases hω with h | h <;> simp [h]
        have hA_memLp : MemLp (M.A i).toFun ⊤ (M.μ₀ : Measure Λ) := by
          apply memLp_top_of_bound
          · exact (M.A i).measurable.aestronglyMeasurable
          · exact hA_bdd
        exact (M.deviation.integrable i 1).mul_of_top_right hA_memLp
      have h0 : ∫ ω, M.A i ω * (1 + M.deviation.ε i 0 ω) ∂(M.μ₀ : Measure Λ) =
                ∫ ω, M.A i ω ∂(M.μ₀ : Measure Λ) + ∫ ω, M.A i ω * M.deviation.ε i 0 ω ∂(M.μ₀ : Measure Λ) := by
        rw [← integral_add hA_int hAε0_int]
        congr 1; ext ω; ring
      have h1 : ∫ ω, M.A i ω * (1 + M.deviation.ε i 1 ω) ∂(M.μ₀ : Measure Λ) =
                ∫ ω, M.A i ω ∂(M.μ₀ : Measure Λ) + ∫ ω, M.A i ω * M.deviation.ε i 1 ω ∂(M.μ₀ : Measure Λ) := by
        rw [← integral_add hA_int hAε1_int]
        congr 1; ext ω; ring
      rw [h0, h1] at hi
      have hdiff : ∫ ω, M.A i ω * M.deviation.ε i 0 ω ∂(M.μ₀ : Measure Λ) -
                   ∫ ω, M.A i ω * M.deviation.ε i 1 ω ∂(M.μ₀ : Measure Λ) = 0 := by linarith
      rw [← integral_sub hAε0_int hAε1_int] at hdiff
      simp only [abs_eq_zero]
      convert hdiff using 1
      congr 1; ext ω; ring
    · intro j
      have hj := hB j
      have hB_int : Integrable (M.B j).toFun (M.μ₀ : Measure Λ) := (M.B j).integrable
      have hBε0_int : Integrable (fun ω => M.B j ω * M.deviation.ε 0 j ω) (M.μ₀ : Measure Λ) := by
        have hB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.B j ω‖ ≤ 1 := by
          filter_upwards [(M.B j).ae_pm_one] with ω hω
          rcases hω with h | h <;> simp [h]
        have hB_memLp : MemLp (M.B j).toFun ⊤ (M.μ₀ : Measure Λ) := by
          apply memLp_top_of_bound
          · exact (M.B j).measurable.aestronglyMeasurable
          · exact hB_bdd
        exact (M.deviation.integrable 0 j).mul_of_top_right hB_memLp
      have hBε1_int : Integrable (fun ω => M.B j ω * M.deviation.ε 1 j ω) (M.μ₀ : Measure Λ) := by
        have hB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.B j ω‖ ≤ 1 := by
          filter_upwards [(M.B j).ae_pm_one] with ω hω
          rcases hω with h | h <;> simp [h]
        have hB_memLp : MemLp (M.B j).toFun ⊤ (M.μ₀ : Measure Λ) := by
          apply memLp_top_of_bound
          · exact (M.B j).measurable.aestronglyMeasurable
          · exact hB_bdd
        exact (M.deviation.integrable 1 j).mul_of_top_right hB_memLp
      have h0 : ∫ ω, M.B j ω * (1 + M.deviation.ε 0 j ω) ∂(M.μ₀ : Measure Λ) =
                ∫ ω, M.B j ω ∂(M.μ₀ : Measure Λ) + ∫ ω, M.B j ω * M.deviation.ε 0 j ω ∂(M.μ₀ : Measure Λ) := by
        rw [← integral_add hB_int hBε0_int]
        congr 1; ext ω; ring
      have h1 : ∫ ω, M.B j ω * (1 + M.deviation.ε 1 j ω) ∂(M.μ₀ : Measure Λ) =
                ∫ ω, M.B j ω ∂(M.μ₀ : Measure Λ) + ∫ ω, M.B j ω * M.deviation.ε 1 j ω ∂(M.μ₀ : Measure Λ) := by
        rw [← integral_add hB_int hBε1_int]
        congr 1; ext ω; ring
      rw [h0, h1] at hj
      have hdiff : ∫ ω, M.B j ω * M.deviation.ε 0 j ω ∂(M.μ₀ : Measure Λ) -
                   ∫ ω, M.B j ω * M.deviation.ε 1 j ω ∂(M.μ₀ : Measure Λ) = 0 := by linarith
      rw [← integral_sub hBε0_int hBε1_int] at hdiff
      simp only [abs_eq_zero]
      convert hdiff using 1
      congr 1; ext ω; ring
  · intro ⟨hA, hB⟩
    constructor
    · intro i
      have hi := hA i
      simp only [abs_eq_zero] at hi
      have hA_int : Integrable (M.A i).toFun (M.μ₀ : Measure Λ) := (M.A i).integrable
      have hAε0_int : Integrable (fun ω => M.A i ω * M.deviation.ε i 0 ω) (M.μ₀ : Measure Λ) := by
        have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω‖ ≤ 1 := by
          filter_upwards [(M.A i).ae_pm_one] with ω hω
          rcases hω with h | h <;> simp [h]
        have hA_memLp : MemLp (M.A i).toFun ⊤ (M.μ₀ : Measure Λ) := by
          apply memLp_top_of_bound
          · exact (M.A i).measurable.aestronglyMeasurable
          · exact hA_bdd
        exact (M.deviation.integrable i 0).mul_of_top_right hA_memLp
      have hAε1_int : Integrable (fun ω => M.A i ω * M.deviation.ε i 1 ω) (M.μ₀ : Measure Λ) := by
        have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω‖ ≤ 1 := by
          filter_upwards [(M.A i).ae_pm_one] with ω hω
          rcases hω with h | h <;> simp [h]
        have hA_memLp : MemLp (M.A i).toFun ⊤ (M.μ₀ : Measure Λ) := by
          apply memLp_top_of_bound
          · exact (M.A i).measurable.aestronglyMeasurable
          · exact hA_bdd
        exact (M.deviation.integrable i 1).mul_of_top_right hA_memLp
      have hdiff : ∫ ω, M.A i ω * (M.deviation.ε i 0 ω - M.deviation.ε i 1 ω) ∂(M.μ₀ : Measure Λ) = 0 := hi
      have hsub : ∫ ω, M.A i ω * M.deviation.ε i 0 ω - M.A i ω * M.deviation.ε i 1 ω ∂(M.μ₀ : Measure Λ) = 0 := by
        convert hdiff using 1; congr 1; ext ω; ring
      rw [integral_sub hAε0_int hAε1_int] at hsub
      have h0 : ∫ ω, M.A i ω * (1 + M.deviation.ε i 0 ω) ∂(M.μ₀ : Measure Λ) =
                ∫ ω, M.A i ω ∂(M.μ₀ : Measure Λ) + ∫ ω, M.A i ω * M.deviation.ε i 0 ω ∂(M.μ₀ : Measure Λ) := by
        rw [← integral_add hA_int hAε0_int]
        congr 1; ext ω; ring
      have h1 : ∫ ω, M.A i ω * (1 + M.deviation.ε i 1 ω) ∂(M.μ₀ : Measure Λ) =
                ∫ ω, M.A i ω ∂(M.μ₀ : Measure Λ) + ∫ ω, M.A i ω * M.deviation.ε i 1 ω ∂(M.μ₀ : Measure Λ) := by
        rw [← integral_add hA_int hAε1_int]
        congr 1; ext ω; ring
      rw [h0, h1]
      linarith
    · intro j
      have hj := hB j
      simp only [abs_eq_zero] at hj
      have hB_int : Integrable (M.B j).toFun (M.μ₀ : Measure Λ) := (M.B j).integrable
      have hBε0_int : Integrable (fun ω => M.B j ω * M.deviation.ε 0 j ω) (M.μ₀ : Measure Λ) := by
        have hB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.B j ω‖ ≤ 1 := by
          filter_upwards [(M.B j).ae_pm_one] with ω hω
          rcases hω with h | h <;> simp [h]
        have hB_memLp : MemLp (M.B j).toFun ⊤ (M.μ₀ : Measure Λ) := by
          apply memLp_top_of_bound
          · exact (M.B j).measurable.aestronglyMeasurable
          · exact hB_bdd
        exact (M.deviation.integrable 0 j).mul_of_top_right hB_memLp
      have hBε1_int : Integrable (fun ω => M.B j ω * M.deviation.ε 1 j ω) (M.μ₀ : Measure Λ) := by
        have hB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.B j ω‖ ≤ 1 := by
          filter_upwards [(M.B j).ae_pm_one] with ω hω
          rcases hω with h | h <;> simp [h]
        have hB_memLp : MemLp (M.B j).toFun ⊤ (M.μ₀ : Measure Λ) := by
          apply memLp_top_of_bound
          · exact (M.B j).measurable.aestronglyMeasurable
          · exact hB_bdd
        exact (M.deviation.integrable 1 j).mul_of_top_right hB_memLp
      have hdiff : ∫ ω, M.B j ω * (M.deviation.ε 0 j ω - M.deviation.ε 1 j ω) ∂(M.μ₀ : Measure Λ) = 0 := hj
      have hsub : ∫ ω, M.B j ω * M.deviation.ε 0 j ω - M.B j ω * M.deviation.ε 1 j ω ∂(M.μ₀ : Measure Λ) = 0 := by
        convert hdiff using 1; congr 1; ext ω; ring
      rw [integral_sub hBε0_int hBε1_int] at hsub
      have h0 : ∫ ω, M.B j ω * (1 + M.deviation.ε 0 j ω) ∂(M.μ₀ : Measure Λ) =
                ∫ ω, M.B j ω ∂(M.μ₀ : Measure Λ) + ∫ ω, M.B j ω * M.deviation.ε 0 j ω ∂(M.μ₀ : Measure Λ) := by
        rw [← integral_add hB_int hBε0_int]
        congr 1; ext ω; ring
      have h1 : ∫ ω, M.B j ω * (1 + M.deviation.ε 1 j ω) ∂(M.μ₀ : Measure Λ) =
                ∫ ω, M.B j ω ∂(M.μ₀ : Measure Λ) + ∫ ω, M.B j ω * M.deviation.ε 1 j ω ∂(M.μ₀ : Measure Λ) := by
        rw [← integral_add hB_int hBε1_int]
        congr 1; ext ω; ring
      rw [h0, h1]
      linarith



/-! ### Balanced Models and Constant Deviations -/

/-- A model has balanced marginals if ∫ A_i dμ₀ = 0 and ∫ B_j dμ₀ = 0 -/
def BalancedMarginals (M : ThermalHVModel Λ) : Prop :=
  (∀ i : Fin 2, ∫ ω, M.A i ω ∂(M.μ₀ : Measure Λ) = 0) ∧
  (∀ j : Fin 2, ∫ ω, M.B j ω ∂(M.μ₀ : Measure Λ) = 0)

/-- A deviation is constant if ε_{i,j}(ω) doesn't depend on ω -/
def ConstantDeviation (M : ThermalHVModel Λ) : Prop :=
  ∀ i j : Fin 2, ∃ c : ℝ, ∀ ω, M.deviation.ε i j ω = c

/-- For balanced models with constant deviation, no-signaling is automatic -/
theorem balanced_constant_noSignaling (M : ThermalHVModel Λ)
    (hBal : BalancedMarginals M)
    (hConst : ConstantDeviation M) :
    noSignaling M := by
  obtain ⟨hA_bal, hB_bal⟩ := hBal
  constructor
  · -- Alice's no-signaling
    intro i
    unfold aliceMarginal
    -- Get the constants for ε_{i,0} and ε_{i,1}
    obtain ⟨c₀, hc₀⟩ := hConst i 0
    obtain ⟨c₁, hc₁⟩ := hConst i 1
    -- Rewrite the integrals using the constants
    have h0 : ∫ ω, M.A i ω * (1 + M.deviation.ε i 0 ω) ∂(M.μ₀ : Measure Λ) =
              ∫ ω, M.A i ω * (1 + c₀) ∂(M.μ₀ : Measure Λ) := by
      congr 1; ext ω; rw [hc₀]
    have h1 : ∫ ω, M.A i ω * (1 + M.deviation.ε i 1 ω) ∂(M.μ₀ : Measure Λ) =
              ∫ ω, M.A i ω * (1 + c₁) ∂(M.μ₀ : Measure Λ) := by
      congr 1; ext ω; rw [hc₁]
    rw [h0, h1]
    -- Factor out the constants
    have hA_int : Integrable (M.A i).toFun (M.μ₀ : Measure Λ) := (M.A i).integrable
    have expand0 : ∫ ω, M.A i ω * (1 + c₀) ∂(M.μ₀ : Measure Λ) =
                   (1 + c₀) * ∫ ω, M.A i ω ∂(M.μ₀ : Measure Λ) := by
      rw [← MeasureTheory.integral_const_mul]
      congr 1; ext ω; ring
    have expand1 : ∫ ω, M.A i ω * (1 + c₁) ∂(M.μ₀ : Measure Λ) =
                   (1 + c₁) * ∫ ω, M.A i ω ∂(M.μ₀ : Measure Λ) := by
      rw [← MeasureTheory.integral_const_mul]
      congr 1; ext ω; ring
    rw [expand0, expand1, hA_bal i]
    ring
  · -- Bob's no-signaling (symmetric argument)
    intro j
    unfold bobMarginal
    obtain ⟨c₀, hc₀⟩ := hConst 0 j
    obtain ⟨c₁, hc₁⟩ := hConst 1 j
    have h0 : ∫ ω, M.B j ω * (1 + M.deviation.ε 0 j ω) ∂(M.μ₀ : Measure Λ) =
              ∫ ω, M.B j ω * (1 + c₀) ∂(M.μ₀ : Measure Λ) := by
      congr 1; ext ω; rw [hc₀]
    have h1 : ∫ ω, M.B j ω * (1 + M.deviation.ε 1 j ω) ∂(M.μ₀ : Measure Λ) =
              ∫ ω, M.B j ω * (1 + c₁) ∂(M.μ₀ : Measure Λ) := by
      congr 1; ext ω; rw [hc₁]
    rw [h0, h1]
    have hB_int : Integrable (M.B j).toFun (M.μ₀ : Measure Λ) := (M.B j).integrable
    have expand0 : ∫ ω, M.B j ω * (1 + c₀) ∂(M.μ₀ : Measure Λ) =
                   (1 + c₀) * ∫ ω, M.B j ω ∂(M.μ₀ : Measure Λ) := by
      rw [← MeasureTheory.integral_const_mul]
      congr 1; ext ω; ring
    have expand1 : ∫ ω, M.B j ω * (1 + c₁) ∂(M.μ₀ : Measure Λ) =
                   (1 + c₁) * ∫ ω, M.B j ω ∂(M.μ₀ : Measure Λ) := by
      rw [← MeasureTheory.integral_const_mul]
      congr 1; ext ω; ring
    rw [expand0, expand1, hB_bal j]
    ring

/-! ### The CHSH-Aligned Sign Pattern -/

/-- The CHSH-aligned sign pattern: ε₀₀ = ε₁₁ = -ε₀₁ = -ε₁₀ -/
def CHSHAlignedPattern (ε : Fin 2 → Fin 2 → Λ → ℝ) (δ : ℝ) : Prop :=
  (∀ ω, ε 0 0 ω = δ) ∧
  (∀ ω, ε 1 1 ω = δ) ∧
  (∀ ω, ε 0 1 ω = -δ) ∧
  (∀ ω, ε 1 0 ω = -δ)

/-- CHSH-aligned pattern implies constant deviation -/
lemma chshAligned_constant (M : ThermalHVModel Λ) (δ : ℝ)
    (h : CHSHAlignedPattern M.deviation.ε δ) :
    ConstantDeviation M := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨δ, h.1⟩
  · exact ⟨-δ, h.2.2.1⟩
  · exact ⟨-δ, h.2.2.2⟩
  · exact ⟨δ, h.2.1⟩

/-- For the CHSH expression S = E₀₁ - E₀₀ + E₁₀ + E₁₁, the thermal part with
    CHSH-aligned pattern gives a specific structure -/
lemma chshAligned_thermal_contribution (M : ThermalHVModel Λ) (δ : ℝ)
    (h : CHSHAlignedPattern M.deviation.ε δ) :
    M.CHSH_thermal = -δ * (∫ ω, M.A 0 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ))
                   - δ * (∫ ω, M.A 0 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ))
                   - δ * (∫ ω, M.A 1 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ))
                   + δ * (∫ ω, M.A 1 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ)) := by
  unfold ThermalHVModel.CHSH_thermal
  -- Helper for integrability of products of ±1 functions
  have prod_integrable : ∀ i j, Integrable (fun ω => M.A i ω * M.B j ω) (M.μ₀ : Measure Λ) := by
    intro i j
    apply Integrable.mono' (integrable_const 1)
    · exact (M.A i).measurable.aestronglyMeasurable.mul (M.B j).measurable.aestronglyMeasurable
    · filter_upwards [(M.A i).ae_pm_one, (M.B j).ae_pm_one] with ω hA hB
      rcases hA with hA | hA <;> rcases hB with hB | hB <;> simp [hA, hB]
  have int01 := prod_integrable 0 1
  have int00 := prod_integrable 0 0
  have int10 := prod_integrable 1 0
  have int11 := prod_integrable 1 1
  -- Helper for integrability of products with ε
  have prod_ε_integrable : ∀ i j, Integrable (fun ω => M.A i ω * M.B j ω * M.deviation.ε i j ω) (M.μ₀ : Measure Λ) := by
    intro i j
    have hAB := prod_integrable i j
    have hAB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A i ω * M.B j ω‖ ≤ 1 := by
      filter_upwards [(M.A i).ae_pm_one, (M.B j).ae_pm_one] with ω hA hB
      rcases hA with hA | hA <;> rcases hB with hB | hB <;> simp [hA, hB]
    have hAB_memLp : MemLp (fun ω => M.A i ω * M.B j ω) ⊤ (M.μ₀ : Measure Λ) := by
      apply memLp_top_of_bound
      · exact (M.A i).measurable.aestronglyMeasurable.mul (M.B j).measurable.aestronglyMeasurable
      · exact hAB_bdd
    exact (M.deviation.integrable i j).mul_of_top_right hAB_memLp
  -- Rewrite each term individually
  have eq01 : ∫ ω, M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω ∂(M.μ₀ : Measure Λ) =
              -δ * ∫ ω, M.A 0 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ) := by
    rw [← MeasureTheory.integral_const_mul]; congr 1; ext ω; rw [h.2.2.1 ω]; ring
  have eq00 : ∫ ω, M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω ∂(M.μ₀ : Measure Λ) =
              δ * ∫ ω, M.A 0 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ) := by
    rw [← MeasureTheory.integral_const_mul]; congr 1; ext ω; rw [h.1 ω]; ring
  have eq10 : ∫ ω, M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω ∂(M.μ₀ : Measure Λ) =
              -δ * ∫ ω, M.A 1 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ) := by
    rw [← MeasureTheory.integral_const_mul]; congr 1; ext ω; rw [h.2.2.2 ω]; ring
  have eq11 : ∫ ω, M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω ∂(M.μ₀ : Measure Λ) =
              δ * ∫ ω, M.A 1 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ) := by
    rw [← MeasureTheory.integral_const_mul]; congr 1; ext ω; rw [h.2.1 ω]; ring
  -- Split the main integral and substitute
  rw [integral_add, integral_add, integral_sub]
  · rw [eq01, eq00, eq10, eq11]; ring
  · exact prod_ε_integrable 0 1
  · exact prod_ε_integrable 0 0
  · exact (prod_ε_integrable 0 1).sub (prod_ε_integrable 0 0)
  · exact prod_ε_integrable 1 0
  · exact ((prod_ε_integrable 0 1).sub (prod_ε_integrable 0 0)).add (prod_ε_integrable 1 0)
  · exact prod_ε_integrable 1 1

/-- Simplified form: thermal contribution factors as -δ times a "CHSH-like" classical sum -/
lemma chshAligned_thermal_factored (M : ThermalHVModel Λ) (δ : ℝ)
    (h : CHSHAlignedPattern M.deviation.ε δ) :
    M.CHSH_thermal = -δ * (∫ ω, M.A 0 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ)
                         + ∫ ω, M.A 0 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ)
                         + ∫ ω, M.A 1 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ)
                         - ∫ ω, M.A 1 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ)) := by
  rw [chshAligned_thermal_contribution M δ h]
  ring

/-- The "anti-CHSH" classical sum that appears in the thermal factor -/
noncomputable def antiCHSH_classical (M : ThermalHVModel Λ) : ℝ :=
  ∫ ω, M.A 0 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ)
  + ∫ ω, M.A 0 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ)
  + ∫ ω, M.A 1 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ)
  - ∫ ω, M.A 1 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ)

variable (M : ThermalHVModel Λ)

/-- With CHSH-aligned pattern: S_thermal = -δ * antiCHSH -/
lemma chshAligned_thermal_eq (δ : ℝ)
    (h : CHSHAlignedPattern M.deviation.ε δ) :
    M.CHSH_thermal = -δ * antiCHSH_classical M := by
  rw [chshAligned_thermal_factored M δ h]
  unfold antiCHSH_classical
  linarith

/-- The antiCHSH is bounded by 2 (same argument as classical CHSH) -/
lemma antiCHSH_classical_bound :
    |antiCHSH_classical M| ≤ 2 := by
  unfold antiCHSH_classical
  -- Integrability of products
  have prod_integrable : ∀ i j, Integrable (fun ω => M.A i ω * M.B j ω) (M.μ₀ : Measure Λ) := by
    intro i j
    apply Integrable.mono' (integrable_const 1)
    · exact (M.A i).measurable.aestronglyMeasurable.mul (M.B j).measurable.aestronglyMeasurable
    · filter_upwards [(M.A i).ae_pm_one, (M.B j).ae_pm_one] with ω hA hB
      rcases hA with hA | hA <;> rcases hB with hB | hB <;> simp [hA, hB]
  have h1 := prod_integrable 0 1
  have h2 := prod_integrable 0 0
  have h3 := prod_integrable 1 0
  have h4 := prod_integrable 1 1
  -- Integrability of the combined expression
  have h_int : Integrable (fun ω => M.A 0 ω * M.B 1 ω + M.A 0 ω * M.B 0 ω +
                                    M.A 1 ω * M.B 0 ω - M.A 1 ω * M.B 1 ω) (M.μ₀ : Measure Λ) :=
    ((h1.add h2).add h3).sub h4
  -- Combine into single integral
  have h_combine : ∫ ω, M.A 0 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ)
                 + ∫ ω, M.A 0 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ)
                 + ∫ ω, M.A 1 ω * M.B 0 ω ∂(M.μ₀ : Measure Λ)
                 - ∫ ω, M.A 1 ω * M.B 1 ω ∂(M.μ₀ : Measure Λ)
                 = ∫ ω, (M.A 0 ω * M.B 1 ω + M.A 0 ω * M.B 0 ω +
                         M.A 1 ω * M.B 0 ω - M.A 1 ω * M.B 1 ω) ∂(M.μ₀ : Measure Λ) := by
    have eq1 : (fun ω => M.A 0 ω * M.B 1 ω + M.A 0 ω * M.B 0 ω + M.A 1 ω * M.B 0 ω - M.A 1 ω * M.B 1 ω)
             = (fun ω => M.A 0 ω * M.B 1 ω + M.A 0 ω * M.B 0 ω + M.A 1 ω * M.B 0 ω)
             - (fun ω => M.A 1 ω * M.B 1 ω) := by ext ω; simp only [Fin.isValue, Pi.sub_apply]
    have eq2 : (fun ω => M.A 0 ω * M.B 1 ω + M.A 0 ω * M.B 0 ω + M.A 1 ω * M.B 0 ω)
             = (fun ω => M.A 0 ω * M.B 1 ω + M.A 0 ω * M.B 0 ω)
             + (fun ω => M.A 1 ω * M.B 0 ω) := by ext ω; simp only [Fin.isValue, Pi.add_apply]
    have eq3 : (fun ω => M.A 0 ω * M.B 1 ω + M.A 0 ω * M.B 0 ω)
             = (fun ω => M.A 0 ω * M.B 1 ω)
             + (fun ω => M.A 0 ω * M.B 0 ω) := by ext ω; simp only [Fin.isValue, Pi.add_apply]
    have hint12 : Integrable ((fun ω => M.A 0 ω * M.B 1 ω) + (fun ω => M.A 0 ω * M.B 0 ω)) (M.μ₀ : Measure Λ) :=
      h1.add h2
    have hint123 : Integrable (((fun ω => M.A 0 ω * M.B 1 ω) + (fun ω => M.A 0 ω * M.B 0 ω)) +
                               (fun ω => M.A 1 ω * M.B 0 ω)) (M.μ₀ : Measure Λ) :=
      hint12.add h3
    rw [eq1, eq2, eq3]
    rw [integral_sub' hint123 h4]
    rw [integral_add' hint12 h3]
    rw [integral_add' h1 h2]

  rw [h_combine]
  -- The pointwise value is ±2
  have h_pointwise : ∀ᵐ ω ∂(M.μ₀ : Measure Λ),
      |M.A 0 ω * M.B 1 ω + M.A 0 ω * M.B 0 ω + M.A 1 ω * M.B 0 ω - M.A 1 ω * M.B 1 ω| ≤ 2 := by
    filter_upwards [(M.A 0).ae_pm_one, (M.A 1).ae_pm_one, (M.B 0).ae_pm_one, (M.B 1).ae_pm_one]
      with ω hA0 hA1 hB0 hB1
    rcases hA0 with hA0 | hA0 <;> rcases hA1 with hA1 | hA1 <;>
    rcases hB0 with hB0 | hB0 <;> rcases hB1 with hB1 | hB1 <;>
    simp [hA0, hA1, hB0, hB1] <;> norm_num
  -- Use triangle inequality and probability measure
  calc |∫ ω, (M.A 0 ω * M.B 1 ω + M.A 0 ω * M.B 0 ω +
              M.A 1 ω * M.B 0 ω - M.A 1 ω * M.B 1 ω) ∂(M.μ₀ : Measure Λ)|
      ≤ ∫ ω, |M.A 0 ω * M.B 1 ω + M.A 0 ω * M.B 0 ω +
              M.A 1 ω * M.B 0 ω - M.A 1 ω * M.B 1 ω| ∂(M.μ₀ : Measure Λ) := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (2 : ℝ) ∂(M.μ₀ : Measure Λ) := by
        apply integral_mono_ae h_int.abs (integrable_const 2) h_pointwise
    _ = 2 := by simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]

/-- With CHSH-aligned pattern, |S_thermal| ≤ 2|δ| -/
lemma chshAligned_thermal_bound (δ : ℝ)
    (h : CHSHAlignedPattern M.deviation.ε δ) :
    |M.CHSH_thermal| ≤ 2 * |δ| := by
  rw [chshAligned_thermal_eq M δ h]
  simp only [neg_mul, abs_neg, abs_mul]
  calc |δ| * |antiCHSH_classical M|
      ≤ |δ| * 2 := by apply mul_le_mul_of_nonneg_left (antiCHSH_classical_bound M) (abs_nonneg _)
    _ = 2 * |δ| := by ring

/-- The full CHSH with aligned pattern: S = S_classical - δ * antiCHSH -/
lemma chshAligned_full (δ : ℝ)
    (h : CHSHAlignedPattern M.deviation.ε δ) :
    M.CHSH = M.CHSH_classical - δ * antiCHSH_classical M := by
  have := CHSH_decomposition M
  rw [chshAligned_thermal_eq M δ h] at this
  linarith

/-- When antiCHSH = -2 and δ > 0, the thermal contribution is +2δ (maximally enhancing) -/
lemma chshAligned_maximal_enhancement (δ : ℝ) (_hδ : δ > 0)
    (h : CHSHAlignedPattern M.deviation.ε δ)
    (h_anti : antiCHSH_classical M = -2) :
    M.CHSH_thermal = 2 * δ := by
  rw [chshAligned_thermal_eq M δ h, h_anti]
  ring

/-- The maximum CHSH value with aligned pattern when S_classical = 2 and antiCHSH = -2 -/
lemma chshAligned_achieves_bound (δ : ℝ) (_hδ : δ > 0)
    (h : CHSHAlignedPattern M.deviation.ε δ)
    (h_classical : M.CHSH_classical = 2)
    (h_anti : antiCHSH_classical M = -2) :
    M.CHSH = 2 + 2 * δ := by
  rw [chshAligned_full M δ h, h_classical, h_anti]
  ring

/-- CHSH-aligned pattern on a balanced model satisfies no-signaling -/
theorem chshAligned_balanced_noSignaling (δ : ℝ)
    (h : CHSHAlignedPattern M.deviation.ε δ)
    (hBal : BalancedMarginals M) :
    noSignaling M := by
  exact balanced_constant_noSignaling M hBal (chshAligned_constant M δ h)

/-- Key result: No-signaling models can achieve S = 2 + 2δ with the aligned pattern -/
theorem noSignaling_achievable_bound (δ : ℝ) (hδ : δ > 0)
    (h : CHSHAlignedPattern M.deviation.ε δ)
    (hBal : BalancedMarginals M)
    (h_classical : M.CHSH_classical = 2)
    (h_anti : antiCHSH_classical M = -2) :
    noSignaling M ∧ M.CHSH = 2 + 2 * δ := by
  constructor
  · exact chshAligned_balanced_noSignaling M δ h hBal
  · exact chshAligned_achieves_bound M δ hδ h h_classical h_anti

/-! ### Does No-Signaling Tighten the Bound?

The CHSH-aligned constant pattern achieves S = 2 + 2δ.
The general thermal bound is S ≤ 2 + 4ε_max.

Question: Can a no-signaling model with |ε| ≤ δ achieve S = 2 + 4δ?

The no-signaling constraint is: ∫ A_i · (ε_{i,0} - ε_{i,1}) dμ₀ = 0
This allows ε_{i,0} ≠ ε_{i,1} as long as the A_i-weighted difference vanishes.

For the thermal CHSH: S_thermal = ∫ (A₀B₁ε₀₁ - A₀B₀ε₀₀ + A₁B₀ε₁₀ + A₁B₁ε₁₁) dμ₀

To maximize this, we want ε to be positively correlated with the CHSH integrand.
-/

/-- The gap between general bound and constant-pattern bound -/
lemma constant_pattern_gap (δ : ℝ) (_hδ : δ > 0) :
    (2 + 4 * δ) - (2 + 2 * δ) = 2 * δ := by ring


/-! ### The CHSH-Optimal Non-Constant Pattern

To maximize S_thermal = ∫ (A₀B₁ε₀₁ - A₀B₀ε₀₀ + A₁B₀ε₁₀ + A₁B₁ε₁₁) dμ₀,
we want each term to contribute maximally.

The optimal choice: ε_{i,j}(ω) = δ · (sign of coefficient in CHSH) · A_i(ω) · B_j(ω)

Since A, B ∈ {±1}, this gives |ε| = δ and each term contributes +δ to the integral.
-/

/-- The CHSH-optimal pattern: ε correlates with A*B to maximize thermal contribution -/
def CHSHOptimalPattern (M : ThermalHVModel Λ) (δ : ℝ) : Prop :=
  (∀ ω, M.deviation.ε 0 0 ω = -δ * M.A 0 ω * M.B 0 ω) ∧  -- coefficient is -1 in CHSH
  (∀ ω, M.deviation.ε 0 1 ω = δ * M.A 0 ω * M.B 1 ω) ∧   -- coefficient is +1 in CHSH
  (∀ ω, M.deviation.ε 1 0 ω = δ * M.A 1 ω * M.B 0 ω) ∧   -- coefficient is +1 in CHSH
  (∀ ω, M.deviation.ε 1 1 ω = δ * M.A 1 ω * M.B 1 ω)     -- coefficient is +1 in CHSH

/-- The optimal pattern has |ε| ≤ |δ| pointwise (always true) -/
lemma chshOptimal_bounded (δ : ℝ)
    (h : CHSHOptimalPattern M δ) :
    ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ∀ i j, |M.deviation.ε i j ω| = |δ| := by
  filter_upwards [(M.A 0).ae_pm_one, (M.A 1).ae_pm_one, (M.B 0).ae_pm_one, (M.B 1).ae_pm_one]
    with ω hA0 hA1 hB0 hB1
  intro i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]; rw [h.1 ω, abs_mul, abs_mul, abs_neg]
    rcases hA0 with hA0 | hA0 <;> rcases hB0 with hB0 | hB0 <;> simp [hA0, hB0]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]; rw [h.2.1 ω, abs_mul, abs_mul]
    rcases hA0 with hA0 | hA0 <;> rcases hB1 with hB1 | hB1 <;> simp [hA0, hB1]
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta]; rw [h.2.2.1 ω, abs_mul, abs_mul]
    rcases hA1 with hA1 | hA1 <;> rcases hB0 with hB0 | hB0 <;> simp [hA1, hB0]
  · simp only [Fin.mk_one, Fin.isValue]; rw [h.2.2.2 ω, abs_mul, abs_mul]
    rcases hA1 with hA1 | hA1 <;> rcases hB1 with hB1 | hB1 <;> simp [hA1, hB1]

/-- The thermal contribution with the optimal pattern -/
lemma chshOptimal_thermal (δ : ℝ)
    (h : CHSHOptimalPattern M δ) :
    M.CHSH_thermal = 4 * δ := by
  unfold ThermalHVModel.CHSH_thermal
  -- Each term becomes δ * (A_i B_j)² = δ (with appropriate sign handling)
  have eq00 : ∀ ω, M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω = -δ * (M.A 0 ω)^2 * (M.B 0 ω)^2 := by
    intro ω; rw [h.1 ω]; ring
  have eq01 : ∀ ω, M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω = δ * (M.A 0 ω)^2 * (M.B 1 ω)^2 := by
    intro ω; rw [h.2.1 ω]; ring
  have eq10 : ∀ ω, M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω = δ * (M.A 1 ω)^2 * (M.B 0 ω)^2 := by
    intro ω; rw [h.2.2.1 ω]; ring
  have eq11 : ∀ ω, M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω = δ * (M.A 1 ω)^2 * (M.B 1 ω)^2 := by
    intro ω; rw [h.2.2.2 ω]; ring
  -- The integrand simplifies using A² = B² = 1 a.e.
  have integrand_eq : ∀ᵐ ω ∂(M.μ₀ : Measure Λ),
      M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
      M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
      M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
      M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω = 4 * δ := by
    filter_upwards [(M.A 0).ae_pm_one, (M.A 1).ae_pm_one, (M.B 0).ae_pm_one, (M.B 1).ae_pm_one]
      with ω hA0 hA1 hB0 hB1
    rw [eq00, eq01, eq10, eq11]
    rcases hA0 with hA0 | hA0 <;> rcases hA1 with hA1 | hA1 <;>
    rcases hB0 with hB0 | hB0 <;> rcases hB1 with hB1 | hB1 <;>
    simp [hA0, hA1, hB0, hB1] <;> ring
  calc ∫ ω, M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
           M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
           M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
           M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω ∂(M.μ₀ : Measure Λ)
      = ∫ ω, (4 * δ) ∂(M.μ₀ : Measure Λ) := integral_congr_ae integrand_eq
    _ = 4 * δ := by simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]


/-- A weaker balance condition: sums of marginals vanish -/
def SumBalancedMarginals (M : ThermalHVModel Λ) : Prop :=
  (∫ ω, M.A 0 ω ∂(M.μ₀ : Measure Λ)) + (∫ ω, M.A 1 ω ∂(M.μ₀ : Measure Λ)) = 0 ∧
  (∫ ω, M.B 0 ω ∂(M.μ₀ : Measure Λ)) + (∫ ω, M.B 1 ω ∂(M.μ₀ : Measure Λ)) = 0

/-- Balanced marginals implies sum-balanced marginals -/
lemma balanced_implies_sumBalanced (hBal : BalancedMarginals M) : SumBalancedMarginals M := by
  obtain ⟨hA, hB⟩ := hBal
  constructor
  · rw [hA 0, hA 1]; ring
  · rw [hB 0, hB 1]; ring


/-- Alice's no-signaling constraint for optimal pattern, i=0 case -/
lemma chshOptimal_alice_constraint_0 (δ : ℝ)
    (h : CHSHOptimalPattern M δ) :
    ∫ ω, M.A 0 ω * (M.deviation.ε 0 0 ω - M.deviation.ε 0 1 ω) ∂(M.μ₀ : Measure Λ) =
    -δ * ((∫ ω, M.B 0 ω ∂(M.μ₀ : Measure Λ)) + (∫ ω, M.B 1 ω ∂(M.μ₀ : Measure Λ))) := by
  have h_diff : ∀ ω, M.deviation.ε 0 0 ω - M.deviation.ε 0 1 ω = -δ * M.A 0 ω * (M.B 0 ω + M.B 1 ω) := by
    intro ω; rw [h.1 ω, h.2.1 ω]; ring
  calc ∫ ω, M.A 0 ω * (M.deviation.ε 0 0 ω - M.deviation.ε 0 1 ω) ∂(M.μ₀ : Measure Λ)
      = ∫ ω, -δ * (M.A 0 ω)^2 * (M.B 0 ω + M.B 1 ω) ∂(M.μ₀ : Measure Λ) := by
        congr 1; ext ω; rw [h_diff ω]; ring
    _ = ∫ ω, -δ * (M.B 0 ω + M.B 1 ω) ∂(M.μ₀ : Measure Λ) := by
        apply integral_congr_ae
        filter_upwards [(M.A 0).ae_pm_one] with ω hA
        rcases hA with hA | hA <;> simp [hA]
    _ = -δ * ((∫ ω, M.B 0 ω ∂(M.μ₀ : Measure Λ)) + (∫ ω, M.B 1 ω ∂(M.μ₀ : Measure Λ))) := by
        rw [MeasureTheory.integral_const_mul, integral_add (M.B 0).integrable (M.B 1).integrable]

/-- Alice's no-signaling constraint for optimal pattern, i=1 case -/
lemma chshOptimal_alice_constraint_1 (δ : ℝ)
    (h : CHSHOptimalPattern M δ) :
    ∫ ω, M.A 1 ω * (M.deviation.ε 1 0 ω - M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ) =
    δ * ((∫ ω, M.B 0 ω ∂(M.μ₀ : Measure Λ)) - (∫ ω, M.B 1 ω ∂(M.μ₀ : Measure Λ))) := by
  have h_diff : ∀ ω, M.deviation.ε 1 0 ω - M.deviation.ε 1 1 ω = δ * M.A 1 ω * (M.B 0 ω - M.B 1 ω) := by
    intro ω; rw [h.2.2.1 ω, h.2.2.2 ω]; ring
  calc ∫ ω, M.A 1 ω * (M.deviation.ε 1 0 ω - M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ)
      = ∫ ω, δ * (M.A 1 ω)^2 * (M.B 0 ω - M.B 1 ω) ∂(M.μ₀ : Measure Λ) := by
        congr 1; ext ω; rw [h_diff ω]; ring
    _ = ∫ ω, δ * (M.B 0 ω - M.B 1 ω) ∂(M.μ₀ : Measure Λ) := by
        apply integral_congr_ae
        filter_upwards [(M.A 1).ae_pm_one] with ω hA
        rcases hA with hA | hA <;> simp [hA]
    _ = δ * ((∫ ω, M.B 0 ω ∂(M.μ₀ : Measure Λ)) - (∫ ω, M.B 1 ω ∂(M.μ₀ : Measure Λ))) := by
        rw [MeasureTheory.integral_const_mul, integral_sub (M.B 0).integrable (M.B 1).integrable]

/-- Bob's no-signaling constraint for optimal pattern, j=0 case -/
lemma chshOptimal_bob_constraint_0 (δ : ℝ)
    (h : CHSHOptimalPattern M δ) :
    ∫ ω, M.B 0 ω * (M.deviation.ε 0 0 ω - M.deviation.ε 1 0 ω) ∂(M.μ₀ : Measure Λ) =
    -δ * ((∫ ω, M.A 0 ω ∂(M.μ₀ : Measure Λ)) + (∫ ω, M.A 1 ω ∂(M.μ₀ : Measure Λ))) := by
  have h_diff : ∀ ω, M.deviation.ε 0 0 ω - M.deviation.ε 1 0 ω = -δ * M.B 0 ω * (M.A 0 ω + M.A 1 ω) := by
    intro ω; rw [h.1 ω, h.2.2.1 ω]; ring
  calc ∫ ω, M.B 0 ω * (M.deviation.ε 0 0 ω - M.deviation.ε 1 0 ω) ∂(M.μ₀ : Measure Λ)
      = ∫ ω, -δ * (M.B 0 ω)^2 * (M.A 0 ω + M.A 1 ω) ∂(M.μ₀ : Measure Λ) := by
        congr 1; ext ω; rw [h_diff ω]; ring
    _ = ∫ ω, -δ * (M.A 0 ω + M.A 1 ω) ∂(M.μ₀ : Measure Λ) := by
        apply integral_congr_ae
        filter_upwards [(M.B 0).ae_pm_one] with ω hB
        rcases hB with hB | hB <;> simp [hB]
    _ = -δ * ((∫ ω, M.A 0 ω ∂(M.μ₀ : Measure Λ)) + (∫ ω, M.A 1 ω ∂(M.μ₀ : Measure Λ))) := by
        rw [MeasureTheory.integral_const_mul, integral_add (M.A 0).integrable (M.A 1).integrable]

/-- Bob's no-signaling constraint for optimal pattern, j=1 case -/
lemma chshOptimal_bob_constraint_1 (δ : ℝ)
    (h : CHSHOptimalPattern M δ) :
    ∫ ω, M.B 1 ω * (M.deviation.ε 0 1 ω - M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ) =
    δ * ((∫ ω, M.A 0 ω ∂(M.μ₀ : Measure Λ)) - (∫ ω, M.A 1 ω ∂(M.μ₀ : Measure Λ))) := by
  have h_diff : ∀ ω, M.deviation.ε 0 1 ω - M.deviation.ε 1 1 ω = δ * M.B 1 ω * (M.A 0 ω - M.A 1 ω) := by
    intro ω; rw [h.2.1 ω, h.2.2.2 ω]; ring
  calc ∫ ω, M.B 1 ω * (M.deviation.ε 0 1 ω - M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ)
      = ∫ ω, δ * (M.B 1 ω)^2 * (M.A 0 ω - M.A 1 ω) ∂(M.μ₀ : Measure Λ) := by
        congr 1; ext ω; rw [h_diff ω]; ring
    _ = ∫ ω, δ * (M.A 0 ω - M.A 1 ω) ∂(M.μ₀ : Measure Λ) := by
        apply integral_congr_ae
        filter_upwards [(M.B 1).ae_pm_one] with ω hB
        rcases hB with hB | hB <;> simp [hB]
    _ = δ * ((∫ ω, M.A 0 ω ∂(M.μ₀ : Measure Λ)) - (∫ ω, M.A 1 ω ∂(M.μ₀ : Measure Λ))) := by
        rw [MeasureTheory.integral_const_mul, integral_sub (M.A 0).integrable (M.A 1).integrable]


/-- Alice's no-signaling for optimal pattern implies sum constraint -/
lemma chshOptimal_alice_noSignaling_sum (δ : ℝ) (hδ : δ ≠ 0)
    (h : CHSHOptimalPattern M δ)
    (hNS : noSignalingAlice M) :
    (∫ ω, M.B 0 ω ∂(M.μ₀ : Measure Λ)) + (∫ ω, M.B 1 ω ∂(M.μ₀ : Measure Λ)) = 0 := by
  have h0 := hNS 0
  unfold aliceMarginal at h0
  -- The constraint from noSignaling_alice_constraint says the integral of A_i * (ε_i0 - ε_i1) = 0
  have hconstr := chshOptimal_alice_constraint_0 M δ h
  -- From h0, we get that the two marginals are equal, hence their difference is 0
  have hdiff : ∫ ω, M.A 0 ω * (M.deviation.ε 0 0 ω - M.deviation.ε 0 1 ω) ∂(M.μ₀ : Measure Λ) = 0 := by
    have hA_int : Integrable (M.A 0).toFun (M.μ₀ : Measure Λ) := (M.A 0).integrable
    have hε0_int : Integrable (fun ω => M.A 0 ω * M.deviation.ε 0 0 ω) (M.μ₀ : Measure Λ) := by
      have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A 0 ω‖ ≤ 1 := by
        filter_upwards [(M.A 0).ae_pm_one] with ω hω
        rcases hω with h | h <;> simp [h]
      have hA_memLp : MemLp (M.A 0).toFun ⊤ (M.μ₀ : Measure Λ) := by
        apply memLp_top_of_bound
        · exact (M.A 0).measurable.aestronglyMeasurable
        · exact hA_bdd
      exact (M.deviation.integrable 0 0).mul_of_top_right hA_memLp
    have hε1_int : Integrable (fun ω => M.A 0 ω * M.deviation.ε 0 1 ω) (M.μ₀ : Measure Λ) := by
      have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A 0 ω‖ ≤ 1 := by
        filter_upwards [(M.A 0).ae_pm_one] with ω hω
        rcases hω with h | h <;> simp [h]
      have hA_memLp : MemLp (M.A 0).toFun ⊤ (M.μ₀ : Measure Λ) := by
        apply memLp_top_of_bound
        · exact (M.A 0).measurable.aestronglyMeasurable
        · exact hA_bdd
      exact (M.deviation.integrable 0 1).mul_of_top_right hA_memLp
    have h1_int : Integrable (fun ω => M.A 0 ω * (1 + M.deviation.ε 0 0 ω)) (M.μ₀ : Measure Λ) := by
      convert hA_int.add hε0_int using 1; ext ω; simp only [Fin.isValue, Pi.add_apply]; ring
    have h2_int : Integrable (fun ω => M.A 0 ω * (1 + M.deviation.ε 0 1 ω)) (M.μ₀ : Measure Λ) := by
      convert hA_int.add hε1_int using 1; ext ω; simp only [Fin.isValue, Pi.add_apply]; ring
    have hsub : ∫ ω, M.A 0 ω * (1 + M.deviation.ε 0 0 ω) - M.A 0 ω * (1 + M.deviation.ε 0 1 ω) ∂(M.μ₀ : Measure Λ) = 0 := by
      rw [integral_sub h1_int h2_int, h0, sub_self]
    convert hsub using 1
    congr 1; ext ω; ring
  rw [hconstr] at hdiff
  have hne : -δ ≠ 0 := neg_ne_zero.mpr hδ
  exact (mul_eq_zero.mp hdiff).resolve_left hne

/-- Alice's no-signaling for optimal pattern implies difference constraint -/
lemma chshOptimal_alice_noSignaling_diff (δ : ℝ) (hδ : δ ≠ 0)
    (h : CHSHOptimalPattern M δ)
    (hNS : noSignalingAlice M) :
    (∫ ω, M.B 0 ω ∂(M.μ₀ : Measure Λ)) - (∫ ω, M.B 1 ω ∂(M.μ₀ : Measure Λ)) = 0 := by
  have h1 := hNS 1
  unfold aliceMarginal at h1
  have hconstr := chshOptimal_alice_constraint_1 M δ h
  have hdiff : ∫ ω, M.A 1 ω * (M.deviation.ε 1 0 ω - M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ) = 0 := by
    have hA_int : Integrable (M.A 1).toFun (M.μ₀ : Measure Λ) := (M.A 1).integrable
    have hε0_int : Integrable (fun ω => M.A 1 ω * M.deviation.ε 1 0 ω) (M.μ₀ : Measure Λ) := by
      have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A 1 ω‖ ≤ 1 := by
        filter_upwards [(M.A 1).ae_pm_one] with ω hω
        rcases hω with h | h <;> simp [h]
      have hA_memLp : MemLp (M.A 1).toFun ⊤ (M.μ₀ : Measure Λ) := by
        apply memLp_top_of_bound
        · exact (M.A 1).measurable.aestronglyMeasurable
        · exact hA_bdd
      exact (M.deviation.integrable 1 0).mul_of_top_right hA_memLp
    have hε1_int : Integrable (fun ω => M.A 1 ω * M.deviation.ε 1 1 ω) (M.μ₀ : Measure Λ) := by
      have hA_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.A 1 ω‖ ≤ 1 := by
        filter_upwards [(M.A 1).ae_pm_one] with ω hω
        rcases hω with h | h <;> simp [h]
      have hA_memLp : MemLp (M.A 1).toFun ⊤ (M.μ₀ : Measure Λ) := by
        apply memLp_top_of_bound
        · exact (M.A 1).measurable.aestronglyMeasurable
        · exact hA_bdd
      exact (M.deviation.integrable 1 1).mul_of_top_right hA_memLp
    have h1_int : Integrable (fun ω => M.A 1 ω * (1 + M.deviation.ε 1 0 ω)) (M.μ₀ : Measure Λ) := by
      convert hA_int.add hε0_int using 1; ext ω; simp only [Fin.isValue, Pi.add_apply] ;ring
    have h2_int : Integrable (fun ω => M.A 1 ω * (1 + M.deviation.ε 1 1 ω)) (M.μ₀ : Measure Λ) := by
      convert hA_int.add hε1_int using 1; ext ω; simp only [Fin.isValue, Pi.add_apply]; ring
    have hsub : ∫ ω, M.A 1 ω * (1 + M.deviation.ε 1 0 ω) - M.A 1 ω * (1 + M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ) = 0 := by
      rw [integral_sub h1_int h2_int, h1, sub_self]
    convert hsub using 1
    congr 1; ext ω; ring
  rw [hconstr] at hdiff
  have hne : δ ≠ 0 := hδ
  exact (mul_eq_zero.mp hdiff).resolve_left hne

/-- Alice's no-signaling for optimal pattern forces B marginals to vanish -/
lemma chshOptimal_alice_noSignaling_forces_B_balanced (δ : ℝ) (hδ : δ ≠ 0)
    (h : CHSHOptimalPattern M δ)
    (hNS : noSignalingAlice M) :
    (∀ j : Fin 2, ∫ ω, M.B j ω ∂(M.μ₀ : Measure Λ) = 0) := by
  have hsum := chshOptimal_alice_noSignaling_sum M δ hδ h hNS
  have hdiff := chshOptimal_alice_noSignaling_diff M δ hδ h hNS
  intro j
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]; linarith
  · simp only [Fin.mk_one, Fin.isValue]; linarith

/-- Bob's no-signaling for optimal pattern implies sum constraint -/
lemma chshOptimal_bob_noSignaling_sum (δ : ℝ) (hδ : δ ≠ 0)
    (h : CHSHOptimalPattern M δ)
    (hNS : noSignalingBob M) :
    (∫ ω, M.A 0 ω ∂(M.μ₀ : Measure Λ)) + (∫ ω, M.A 1 ω ∂(M.μ₀ : Measure Λ)) = 0 := by
  have h0 := hNS 0
  unfold bobMarginal at h0
  have hconstr := chshOptimal_bob_constraint_0 M δ h
  have hdiff : ∫ ω, M.B 0 ω * (M.deviation.ε 0 0 ω - M.deviation.ε 1 0 ω) ∂(M.μ₀ : Measure Λ) = 0 := by
    have hB_int : Integrable (M.B 0).toFun (M.μ₀ : Measure Λ) := (M.B 0).integrable
    have hε0_int : Integrable (fun ω => M.B 0 ω * M.deviation.ε 0 0 ω) (M.μ₀ : Measure Λ) := by
      have hB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.B 0 ω‖ ≤ 1 := by
        filter_upwards [(M.B 0).ae_pm_one] with ω hω
        rcases hω with h | h <;> simp [h]
      have hB_memLp : MemLp (M.B 0).toFun ⊤ (M.μ₀ : Measure Λ) := by
        apply memLp_top_of_bound
        · exact (M.B 0).measurable.aestronglyMeasurable
        · exact hB_bdd
      exact (M.deviation.integrable 0 0).mul_of_top_right hB_memLp
    have hε1_int : Integrable (fun ω => M.B 0 ω * M.deviation.ε 1 0 ω) (M.μ₀ : Measure Λ) := by
      have hB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.B 0 ω‖ ≤ 1 := by
        filter_upwards [(M.B 0).ae_pm_one] with ω hω
        rcases hω with h | h <;> simp [h]
      have hB_memLp : MemLp (M.B 0).toFun ⊤ (M.μ₀ : Measure Λ) := by
        apply memLp_top_of_bound
        · exact (M.B 0).measurable.aestronglyMeasurable
        · exact hB_bdd
      exact (M.deviation.integrable 1 0).mul_of_top_right hB_memLp
    have h1_int : Integrable (fun ω => M.B 0 ω * (1 + M.deviation.ε 0 0 ω)) (M.μ₀ : Measure Λ) := by
      convert hB_int.add hε0_int using 1; ext ω; simp only [Fin.isValue, Pi.add_apply]; ring
    have h2_int : Integrable (fun ω => M.B 0 ω * (1 + M.deviation.ε 1 0 ω)) (M.μ₀ : Measure Λ) := by
      convert hB_int.add hε1_int using 1; ext ω; simp only [Fin.isValue, Pi.add_apply]; ring
    have hsub : ∫ ω, M.B 0 ω * (1 + M.deviation.ε 0 0 ω) - M.B 0 ω * (1 + M.deviation.ε 1 0 ω) ∂(M.μ₀ : Measure Λ) = 0 := by
      rw [integral_sub h1_int h2_int, h0, sub_self]
    convert hsub using 1
    congr 1; ext ω; ring
  rw [hconstr] at hdiff
  have hne : -δ ≠ 0 := neg_ne_zero.mpr hδ
  exact (mul_eq_zero.mp hdiff).resolve_left hne

/-- Bob's no-signaling for optimal pattern implies difference constraint -/
lemma chshOptimal_bob_noSignaling_diff (δ : ℝ) (hδ : δ ≠ 0)
    (h : CHSHOptimalPattern M δ)
    (hNS : noSignalingBob M) :
    (∫ ω, M.A 0 ω ∂(M.μ₀ : Measure Λ)) - (∫ ω, M.A 1 ω ∂(M.μ₀ : Measure Λ)) = 0 := by
  have h1 := hNS 1
  unfold bobMarginal at h1
  have hconstr := chshOptimal_bob_constraint_1 M δ h
  have hdiff : ∫ ω, M.B 1 ω * (M.deviation.ε 0 1 ω - M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ) = 0 := by
    have hB_int : Integrable (M.B 1).toFun (M.μ₀ : Measure Λ) := (M.B 1).integrable
    have hε0_int : Integrable (fun ω => M.B 1 ω * M.deviation.ε 0 1 ω) (M.μ₀ : Measure Λ) := by
      have hB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.B 1 ω‖ ≤ 1 := by
        filter_upwards [(M.B 1).ae_pm_one] with ω hω
        rcases hω with h | h <;> simp [h]
      have hB_memLp : MemLp (M.B 1).toFun ⊤ (M.μ₀ : Measure Λ) := by
        apply memLp_top_of_bound
        · exact (M.B 1).measurable.aestronglyMeasurable
        · exact hB_bdd
      exact (M.deviation.integrable 0 1).mul_of_top_right hB_memLp
    have hε1_int : Integrable (fun ω => M.B 1 ω * M.deviation.ε 1 1 ω) (M.μ₀ : Measure Λ) := by
      have hB_bdd : ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ‖M.B 1 ω‖ ≤ 1 := by
        filter_upwards [(M.B 1).ae_pm_one] with ω hω
        rcases hω with h | h <;> simp [h]
      have hB_memLp : MemLp (M.B 1).toFun ⊤ (M.μ₀ : Measure Λ) := by
        apply memLp_top_of_bound
        · exact (M.B 1).measurable.aestronglyMeasurable
        · exact hB_bdd
      exact (M.deviation.integrable 1 1).mul_of_top_right hB_memLp
    have h1_int : Integrable (fun ω => M.B 1 ω * (1 + M.deviation.ε 0 1 ω)) (M.μ₀ : Measure Λ) := by
      convert hB_int.add hε0_int using 1; ext ω; simp only [Fin.isValue, Pi.add_apply]; ring
    have h2_int : Integrable (fun ω => M.B 1 ω * (1 + M.deviation.ε 1 1 ω)) (M.μ₀ : Measure Λ) := by
      convert hB_int.add hε1_int using 1; ext ω; simp only [Fin.isValue, Pi.add_apply]; ring
    have hsub : ∫ ω, M.B 1 ω * (1 + M.deviation.ε 0 1 ω) - M.B 1 ω * (1 + M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ) = 0 := by
      rw [integral_sub h1_int h2_int, h1, sub_self]
    convert hsub using 1
    congr 1; ext ω; ring
  rw [hconstr] at hdiff
  exact (mul_eq_zero.mp hdiff).resolve_left hδ

/-- Bob's no-signaling for optimal pattern forces A marginals to vanish -/
lemma chshOptimal_bob_noSignaling_forces_A_balanced (δ : ℝ) (hδ : δ ≠ 0)
    (h : CHSHOptimalPattern M δ)
    (hNS : noSignalingBob M) :
    (∀ i : Fin 2, ∫ ω, M.A i ω ∂(M.μ₀ : Measure Λ) = 0) := by
  have hsum := chshOptimal_bob_noSignaling_sum M δ hδ h hNS
  have hdiff := chshOptimal_bob_noSignaling_diff M δ hδ h hNS
  intro i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]; linarith
  · simp only [Fin.mk_one, Fin.isValue]; linarith

/-- Full no-signaling + optimal pattern implies balanced marginals -/
theorem chshOptimal_noSignaling_implies_balanced (δ : ℝ) (hδ : δ ≠ 0)
    (h : CHSHOptimalPattern M δ)
    (hNS : noSignaling M) :
    BalancedMarginals M := by
  obtain ⟨hNS_A, hNS_B⟩ := hNS
  exact ⟨chshOptimal_bob_noSignaling_forces_A_balanced M δ hδ h hNS_B,
         chshOptimal_alice_noSignaling_forces_B_balanced M δ hδ h hNS_A⟩

/-- No-signaling models can achieve the full thermal bound -/
theorem noSignaling_achieves_full_bound (δ : ℝ) (_hδ : |δ| < 1)
    (h : CHSHOptimalPattern M δ)
    (_hNS : noSignaling M)
    (h_classical : M.CHSH_classical = 2) :
    M.CHSH = 2 + 4 * δ := by
  have h_thermal := chshOptimal_thermal M δ h
  have h_decomp := CHSH_decomposition M
  linarith

end ThermalBell
