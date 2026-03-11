/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: BellsTheorem/ThermalBell/Constraints.lean
-/
import LogosLibrary.Superior.SplitMechanics.ThermalBell.Geometry
/-!
# Thermal Bell — No-Signaling & Quantum Compatibility Constraints

Factored integrability helpers, no-signaling conditions, CHSH-optimal
and CHSH-aligned deviation patterns, and the quantum compatibility
constraint (E_C ≠ 0 at extreme angles).

## Main Results

* `chshOptimal_thermal` — optimal pattern gives S_thermal = 4δ
* `chshOptimal_noSignaling_implies_balanced` — NS + optimal ⟹ balanced
* `quantum_compatible_constraint` — |E_Q| = 1 with E_C = 0 is impossible
* `E_C_nonzero_at_extremes` — hidden variables must be correlated at θ = 0
-/

open MeasureTheory ProbabilityTheory Set Real BellTheorem
open scoped ENNReal NNReal BigOperators

namespace ThermalBell

variable {Λ : Type*} [MeasurableSpace Λ]

/-! ## Section 1: Factored Integrability Helpers

These lemmas eliminate ~500 lines of boilerplate from the old codebase.
-/

/-- A ±1 response function is bounded in L∞. -/
lemma dichotomic_memLp {μ : Measure Λ} (f : ResponseFunction Λ μ) :
    MemLp f.toFun ⊤ μ :=
  memLp_top_of_bound f.measurable.aestronglyMeasurable 1
    (by filter_upwards [f.ae_pm_one] with ω hω; rcases hω with h | h <;> simp [h])

/-- The product A·B of two ±1 functions is in L∞. -/
lemma dichotomic_prod_memLp {μ : Measure Λ} (A B : ResponseFunction Λ μ) :
    MemLp (fun ω => A ω * B ω) ⊤ μ :=
  memLp_top_of_bound
    (A.measurable.aestronglyMeasurable.mul B.measurable.aestronglyMeasurable) 1
    (by filter_upwards [A.ae_pm_one, B.ae_pm_one] with ω hA hB
        rcases hA with hA | hA <;> rcases hB with hB | hB <;> simp [hA, hB])

/-- Product of two response functions is integrable. -/
lemma prod_integrable {μ : Measure Λ} [IsFiniteMeasure μ] (A B : ResponseFunction Λ μ) :
    Integrable (fun ω => A ω * B ω) μ :=
  Integrable.mono' (integrable_const 1)
    (A.measurable.aestronglyMeasurable.mul B.measurable.aestronglyMeasurable)
    (by filter_upwards [A.ae_pm_one, B.ae_pm_one] with ω hA hB
        rcases hA with hA | hA <;> rcases hB with hB | hB <;> simp [hA, hB])

/-- Product A·B·ε is integrable when ε is integrable and A,B are ±1. -/
lemma prod_ε_integrable {μ : Measure Λ} (A B : ResponseFunction Λ μ)
    (hε : Integrable ε μ) : Integrable (fun ω => A ω * B ω * ε ω) μ :=
  (hε.mul_of_top_right (dichotomic_prod_memLp A B)).congr
    (by filter_upwards with ω; ring_nf; rfl)

/-- |A·B| = 1 a.e. for dichotomic A, B. -/
lemma abs_mul_dichotomic_ae {μ : Measure Λ} (A B : ResponseFunction Λ μ) :
    ∀ᵐ ω ∂μ, |A ω * B ω| = 1 := by
  filter_upwards [A.ae_pm_one, B.ae_pm_one] with ω hA hB
  rcases hA with hA | hA <;> rcases hB with hB | hB <;> simp [hA, hB]

/-- |A·B·ε| = |ε| a.e. for dichotomic A, B. -/
lemma abs_ABε_eq_abs_ε {μ : Measure Λ} (A B : ResponseFunction Λ μ) (ε : Λ → ℝ) :
    ∀ᵐ ω ∂μ, |A ω * B ω * ε ω| = |ε ω| := by
  filter_upwards [abs_mul_dichotomic_ae A B] with ω h
  rw [abs_mul, h, one_mul]

/-- A·ε is integrable when A is ±1 and ε is integrable. -/
lemma response_mul_integrable {μ : Measure Λ} (A : ResponseFunction Λ μ)
    (hε : Integrable ε μ) : Integrable (fun ω => A ω * ε ω) μ :=
  (hε.mul_of_top_right (dichotomic_memLp A)).congr
    (by filter_upwards with ω; ring_nf; rfl)

/-! ## Section 2: No-Signaling -/

variable (M : ThermalHVModel Λ)

/-- Alice's marginal for settings (i,j). -/
noncomputable def aliceMarginal (i j : Fin 2) : ℝ :=
  ∫ ω, M.A i ω * (1 + M.deviation.ε i j ω) ∂(M.μ₀ : Measure Λ)

/-- Bob's marginal for settings (i,j). -/
noncomputable def bobMarginal (i j : Fin 2) : ℝ :=
  ∫ ω, M.B j ω * (1 + M.deviation.ε i j ω) ∂(M.μ₀ : Measure Λ)

def noSignalingAlice : Prop := ∀ i, aliceMarginal M i 0 = aliceMarginal M i 1
def noSignalingBob : Prop := ∀ j, bobMarginal M 0 j = bobMarginal M 1 j
def noSignaling : Prop := noSignalingAlice M ∧ noSignalingBob M

/-- Balanced marginals: ∫ A_i dμ₀ = 0, ∫ B_j dμ₀ = 0. -/
def BalancedMarginals : Prop :=
  (∀ i : Fin 2, ∫ ω, M.A i ω ∂(M.μ₀ : Measure Λ) = 0) ∧
  (∀ j : Fin 2, ∫ ω, M.B j ω ∂(M.μ₀ : Measure Λ) = 0)

/-! ## Section 3: CHSH Deviation Patterns -/

/-- CHSH-aligned constant pattern: ε₀₀ = ε₁₁ = δ, ε₀₁ = ε₁₀ = −δ. -/
def CHSHAlignedPattern (ε : Fin 2 → Fin 2 → Λ → ℝ) (δ : ℝ) : Prop :=
  (∀ ω, ε 0 0 ω = δ) ∧ (∀ ω, ε 1 1 ω = δ) ∧
  (∀ ω, ε 0 1 ω = -δ) ∧ (∀ ω, ε 1 0 ω = -δ)

/-- CHSH-optimal pattern: ε correlates with A·B to maximize S_thermal. -/
def CHSHOptimalPattern (δ : ℝ) : Prop :=
  (∀ ω, M.deviation.ε 0 0 ω = -δ * M.A 0 ω * M.B 0 ω) ∧
  (∀ ω, M.deviation.ε 0 1 ω = δ * M.A 0 ω * M.B 1 ω) ∧
  (∀ ω, M.deviation.ε 1 0 ω = δ * M.A 1 ω * M.B 0 ω) ∧
  (∀ ω, M.deviation.ε 1 1 ω = δ * M.A 1 ω * M.B 1 ω)

/-- **Optimal pattern gives S_thermal = 4δ.** -/
theorem chshOptimal_thermal (δ : ℝ) (h : CHSHOptimalPattern M δ) :
    M.CHSH_thermal = 4 * δ := by
  unfold ThermalHVModel.CHSH_thermal
  have integrand_eq : ∀ᵐ ω ∂(M.μ₀ : Measure Λ),
      M.A 0 ω * M.B 1 ω * M.deviation.ε 0 1 ω -
      M.A 0 ω * M.B 0 ω * M.deviation.ε 0 0 ω +
      M.A 1 ω * M.B 0 ω * M.deviation.ε 1 0 ω +
      M.A 1 ω * M.B 1 ω * M.deviation.ε 1 1 ω = 4 * δ := by
    filter_upwards [(M.A 0).ae_pm_one, (M.A 1).ae_pm_one,
                    (M.B 0).ae_pm_one, (M.B 1).ae_pm_one] with ω hA0 hA1 hB0 hB1
    rw [h.2.1 ω, h.1 ω, h.2.2.1 ω, h.2.2.2 ω]
    rcases hA0 with hA0 | hA0 <;> rcases hA1 with hA1 | hA1 <;>
    rcases hB0 with hB0 | hB0 <;> rcases hB1 with hB1 | hB1 <;>
    simp [hA0, hA1, hB0, hB1] <;> ring
  calc ∫ ω, _ ∂(M.μ₀ : Measure Λ)
      = ∫ ω, (4 * δ) ∂(M.μ₀ : Measure Λ) := integral_congr_ae integrand_eq
    _ = 4 * δ := by simp [integral_const, MeasureTheory.probReal_univ]

/-- Optimal pattern has |ε| = |δ| a.e. -/

lemma chshOptimal_bounded (δ : ℝ) (h : CHSHOptimalPattern M δ) :
    ∀ᵐ ω ∂(M.μ₀ : Measure Λ), ∀ i j, |M.deviation.ε i j ω| = |δ| := by
  filter_upwards [(M.A 0).ae_pm_one, (M.A 1).ae_pm_one,
                  (M.B 0).ae_pm_one, (M.B 1).ae_pm_one] with ω hA0 hA1 hB0 hB1
  intro i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
  · rw [h.1 ω, abs_mul, abs_mul, abs_neg]
    rcases hA0 with hA0 | hA0 <;> rcases hB0 with hB0 | hB0 <;> simp [hA0, hB0]
  · rw [h.2.1 ω, abs_mul, abs_mul]
    rcases hA0 with hA0 | hA0 <;> rcases hB1 with hB1 | hB1 <;> simp [hA0, hB1]
  · rw [h.2.2.1 ω, abs_mul, abs_mul]
    rcases hA1 with hA1 | hA1 <;> rcases hB0 with hB0 | hB0 <;> simp [hA1, hB0]
  · rw [h.2.2.2 ω, abs_mul, abs_mul]
    rcases hA1 with hA1 | hA1 <;> rcases hB1 with hB1 | hB1 <;> simp [hA1, hB1]

/-! ## Section 4: No-Signaling + Optimal ⟹ Balanced

The key constraint propagation: if ε has CHSH-optimal form and the model
satisfies no-signaling, then all marginals must vanish.
-/

/-- Alice i=0 constraint for optimal pattern. -/
private lemma alice_constraint_0 (δ : ℝ) (h : CHSHOptimalPattern M δ) :
    ∫ ω, M.A 0 ω * (M.deviation.ε 0 0 ω - M.deviation.ε 0 1 ω) ∂(M.μ₀ : Measure Λ) =
    -δ * ((∫ ω, M.B 0 ω ∂(M.μ₀ : Measure Λ)) + (∫ ω, M.B 1 ω ∂(M.μ₀ : Measure Λ))) := by
  calc ∫ ω, M.A 0 ω * (M.deviation.ε 0 0 ω - M.deviation.ε 0 1 ω) ∂(M.μ₀ : Measure Λ)
      = ∫ ω, -δ * (M.B 0 ω + M.B 1 ω) ∂(M.μ₀ : Measure Λ) := by
        apply integral_congr_ae
        filter_upwards [(M.A 0).ae_pm_one] with ω hA
        rw [h.1 ω, h.2.1 ω]; rcases hA with hA | hA <;> simp [hA] <;> ring
    _ = -δ * ((∫ ω, M.B 0 ω ∂_) + (∫ ω, M.B 1 ω ∂_)) := by
        trans ∫ ω, (-δ * M.B 0 ω + -δ * M.B 1 ω) ∂(M.μ₀ : Measure Λ)
        · congr 1; ext ω; ring
        · rw [integral_add ((M.B 0).integrable.const_mul _)
                           ((M.B 1).integrable.const_mul _),
              integral_const_mul, integral_const_mul]; ring

/-- Alice i=1 constraint for optimal pattern. -/
private lemma alice_constraint_1 (δ : ℝ) (h : CHSHOptimalPattern M δ) :
    ∫ ω, M.A 1 ω * (M.deviation.ε 1 0 ω - M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ) =
    δ * ((∫ ω, M.B 0 ω ∂(M.μ₀ : Measure Λ)) - (∫ ω, M.B 1 ω ∂(M.μ₀ : Measure Λ))) := by
  calc ∫ ω, M.A 1 ω * (M.deviation.ε 1 0 ω - M.deviation.ε 1 1 ω) ∂(M.μ₀ : Measure Λ)
      = ∫ ω, δ * (M.B 0 ω - M.B 1 ω) ∂(M.μ₀ : Measure Λ) := by
        apply integral_congr_ae
        filter_upwards [(M.A 1).ae_pm_one] with ω hA
        rw [h.2.2.1 ω, h.2.2.2 ω]; rcases hA with hA | hA <;> simp [hA] <;> ring
    _ = δ * ((∫ ω, M.B 0 ω ∂_) - (∫ ω, M.B 1 ω ∂_)) := by
        trans ∫ ω, (δ * M.B 0 ω - δ * M.B 1 ω) ∂(M.μ₀ : Measure Λ)
        · congr 1; ext ω; ring
        · rw [integral_sub ((M.B 0).integrable.const_mul _)
                           ((M.B 1).integrable.const_mul _),
              integral_const_mul, integral_const_mul]; ring

/-- Extract the no-signaling integral equation from marginal equality. -/
private lemma ns_to_integral_eq {μ : Measure Λ} (A : ResponseFunction Λ μ)
    (ε₀ ε₁ : Λ → ℝ) (hε₀ : Integrable ε₀ μ) (hε₁ : Integrable ε₁ μ)
    (h : ∫ ω, A ω * (1 + ε₀ ω) ∂μ = ∫ ω, A ω * (1 + ε₁ ω) ∂μ) :
    ∫ ω, A ω * (ε₀ ω - ε₁ ω) ∂μ = 0 := by
  have h0 : ∫ ω, A ω * (1 + ε₀ ω) ∂μ =
      ∫ ω, A ω ∂μ + ∫ ω, A ω * ε₀ ω ∂μ := by
    rw [← integral_add A.integrable (response_mul_integrable A hε₀)]
    congr 1; ext ω; ring
  have h1 : ∫ ω, A ω * (1 + ε₁ ω) ∂μ =
      ∫ ω, A ω ∂μ + ∫ ω, A ω * ε₁ ω ∂μ := by
    rw [← integral_add A.integrable (response_mul_integrable A hε₁)]
    congr 1; ext ω; ring
  rw [h0, h1] at h
  have hsub : ∫ ω, A ω * ε₀ ω ∂μ - ∫ ω, A ω * ε₁ ω ∂μ = 0 := by linarith
  rw [← integral_sub (response_mul_integrable A hε₀) (response_mul_integrable A hε₁)] at hsub
  convert hsub using 1; congr 1; ext ω; ring

/-- **No-signaling + optimal ⟹ balanced marginals.** -/
theorem chshOptimal_noSignaling_implies_balanced (δ : ℝ) (hδ : δ ≠ 0)
    (h : CHSHOptimalPattern M δ) (hNS : noSignaling M) :
    BalancedMarginals M := by
  obtain ⟨hNS_A, hNS_B⟩ := hNS
  -- Alice's NS forces B marginals to vanish
  have hB_bal : ∀ j : Fin 2, ∫ ω, M.B j ω ∂(M.μ₀ : Measure Λ) = 0 := by
    have h_sum : (∫ ω, M.B 0 ω ∂(M.μ₀ : Measure Λ)) +
             (∫ ω, M.B 1 ω ∂(M.μ₀ : Measure Λ)) = 0 := by
      have := ns_to_integral_eq (M.A 0) _ _ (M.deviation.integrable 0 0)
              (M.deviation.integrable 0 1) (hNS_A 0)
      rw [alice_constraint_0 M δ h] at this
      exact (mul_eq_zero.mp this).resolve_left (neg_ne_zero.mpr hδ)
    have h_diff : (∫ ω, M.B 0 ω ∂(M.μ₀ : Measure Λ)) -
                  (∫ ω, M.B 1 ω ∂(M.μ₀ : Measure Λ)) = 0 := by
      have := ns_to_integral_eq (M.A 1) _ _ (M.deviation.integrable 1 0)
               (M.deviation.integrable 1 1) (hNS_A 1)
      rw [alice_constraint_1 M δ h] at this
      exact (mul_eq_zero.mp this).resolve_left hδ
    intro j; fin_cases j <;> grind only
  -- Bob's NS forces A marginals to vanish (symmetric argument)
  have hA_bal : ∀ i : Fin 2, ∫ ω, M.A i ω ∂(M.μ₀ : Measure Λ) = 0 := by
    have h_sum : (∫ ω, M.A 0 ω ∂(M.μ₀ : Measure Λ)) +
                 (∫ ω, M.A 1 ω ∂(M.μ₀ : Measure Λ)) = 0 := by
      have : ∫ ω, M.B 0 ω * (M.deviation.ε 0 0 ω - M.deviation.ε 1 0 ω)
          ∂(M.μ₀ : Measure Λ) = 0 :=
        ns_to_integral_eq (M.B 0) _ _ (M.deviation.integrable 0 0)
          (M.deviation.integrable 1 0) (hNS_B 0)
      have heq : ∫ ω, M.B 0 ω * (M.deviation.ε 0 0 ω - M.deviation.ε 1 0 ω)
          ∂(M.μ₀ : Measure Λ) =
          -δ * ((∫ ω, M.A 0 ω ∂(M.μ₀ : Measure Λ)) +
                (∫ ω, M.A 1 ω ∂(M.μ₀ : Measure Λ))) := by
        calc ∫ ω, M.B 0 ω * (M.deviation.ε 0 0 ω - M.deviation.ε 1 0 ω )
                ∂(M.μ₀ : Measure Λ)
            = ∫ ω, -δ * (M.A 0 ω + M.A 1 ω) ∂(M.μ₀ : Measure Λ) := by
              apply integral_congr_ae
              filter_upwards [(M.B 0).ae_pm_one] with ω hB
              rw [h.1 ω, h.2.2.1 ω]; rcases hB with hB | hB <;> simp [hB] <;> ring
          _ = -δ * ((∫ ω, M.A 0 ω ∂(M.μ₀ : Measure Λ)) +
                    (∫ ω, M.A 1 ω ∂(M.μ₀ : Measure Λ))) := by
              trans ∫ ω, (-δ * M.A 0 ω + -δ * M.A 1 ω) ∂(M.μ₀ : Measure Λ)
              · congr 1; ext ω; ring
              · rw [integral_add ((M.A 0).integrable.const_mul _)
                                 ((M.A 1).integrable.const_mul _),
                    integral_const_mul, integral_const_mul]; ring
      rw [heq] at this
      exact (mul_eq_zero.mp this).resolve_left (neg_ne_zero.mpr hδ)
    have h_diff : (∫ ω, M.A 0 ω ∂(M.μ₀ : Measure Λ)) -
                  (∫ ω, M.A 1 ω ∂(M.μ₀ : Measure Λ)) = 0 := by
      have : ∫ ω, M.B 1 ω * (M.deviation.ε 0 1 ω - M.deviation.ε 1 1 ω)
          ∂(M.μ₀ : Measure Λ) = 0 :=
        ns_to_integral_eq (M.B 1) _ _ (M.deviation.integrable 0 1)
          (M.deviation.integrable 1 1) (hNS_B 1)
      have heq : ∫ ω, M.B 1 ω * (M.deviation.ε 0 1 ω - M.deviation.ε 1 1 ω)
          ∂(M.μ₀ : Measure Λ) =
          δ * ((∫ ω, M.A 0 ω ∂(M.μ₀ : Measure Λ)) -
               (∫ ω, M.A 1 ω ∂(M.μ₀ : Measure Λ))) := by
        calc ∫ ω, M.B 1 ω * (M.deviation.ε 0 1 ω - M.deviation.ε 1 1 ω)
                ∂(M.μ₀ : Measure Λ)
            = ∫ ω, δ * (M.A 0 ω - M.A 1 ω) ∂(M.μ₀ : Measure Λ) := by
              apply integral_congr_ae
              filter_upwards [(M.B 1).ae_pm_one] with ω hB
              rw [h.2.1 ω, h.2.2.2 ω]; rcases hB with hB | hB <;> simp [hB] <;> ring
          _ = δ * ((∫ ω, M.A 0 ω ∂(M.μ₀ : Measure Λ)) -
                   (∫ ω, M.A 1 ω ∂(M.μ₀ : Measure Λ))) := by
              trans ∫ ω, (δ * M.A 0 ω - δ * M.A 1 ω) ∂(M.μ₀ : Measure Λ)
              · congr 1; ext ω; ring
              · rw [integral_sub ((M.A 0).integrable.const_mul _)
                                 ((M.A 1).integrable.const_mul _),
                    integral_const_mul, integral_const_mul]; ring
      rw [heq] at this
      exact (mul_eq_zero.mp this).resolve_left hδ
    intro i; fin_cases i <;> grind only
  exact ⟨hA_bal, hB_bal⟩

/-! ## Section 5: Quantum Compatibility -/

/-- The quantum correlation function: E_Q(θ) = −cos(θ). -/
noncomputable def E_Q (θ : ℝ) : ℝ := -Real.cos θ

/-- Classical correlation: ∫ AB dμ₀. -/
noncomputable def E_C (μ₀ : Measure Λ) (A B : Λ → ℝ) : ℝ := ∫ ω, A ω * B ω ∂μ₀

/-- Thermal correction: ∫ ABε dμ₀. -/
noncomputable def E_thermal (μ₀ : Measure Λ) (A B ε : Λ → ℝ) : ℝ :=
  ∫ ω, A ω * B ω * ε ω ∂μ₀

/-- Full thermal correlation: E_C + E_thermal. -/
noncomputable def E_full (μ₀ : Measure Λ) [IsProbabilityMeasure μ₀]
    (A B ε : Λ → ℝ) : ℝ := E_C μ₀ A B + E_thermal μ₀ A B ε

/-- Quantum compatibility: E_full = E_Q. -/
def quantum_compatible (μ₀ : Measure Λ) [IsProbabilityMeasure μ₀]
    (A B ε : Λ → ℝ) (θ : ℝ) : Prop := E_full μ₀ A B ε = E_Q θ

/-- |∫ ABε| < 1 when A,B are ±1 and |ε| < 1. -/
lemma abs_integral_ABε_lt_one (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A B : ResponseFunction Λ μ) (ε : Λ → ℝ)
    (hε_bound : ∀ ω, |ε ω| < 1) (hε_int : Integrable ε μ) :
    |∫ ω, A ω * B ω * ε ω ∂μ| < 1 := by
  have h_int := prod_ε_integrable A B hε_int
  calc |∫ ω, A ω * B ω * ε ω ∂μ|
      ≤ ∫ ω, |A ω * B ω * ε ω| ∂μ := abs_integral_le_integral_abs
    _ = ∫ ω, |ε ω| ∂μ := integral_congr_ae (abs_ABε_eq_abs_ε A B ε)
    _ < 1 := by
        have h_gap : ∀ ω, |ε ω| < 1 := hε_bound
        have h_gap_pos : ∀ ω, 0 < 1 - |ε ω| := fun ω => by linarith [h_gap ω]
        have h_int_gap := ((integrable_const 1).sub hε_int.abs)
        have h_pos : 0 < ∫ ω, (1 - |ε ω|) ∂μ := by
          rw [integral_pos_iff_support_of_nonneg (fun ω => le_of_lt (h_gap_pos ω)) h_int_gap]
          rw [show Function.support (fun ω => 1 - |ε ω|) = Set.univ from by
            ext ω; simp [ne_of_gt (h_gap_pos ω)]]
          simp
        have h_expand : ∫ ω, (1 - |ε ω|) ∂μ = 1 - ∫ ω, |ε ω| ∂μ := by
          have hsub := integral_sub (integrable_const (1 : ℝ)) hε_int.abs
          simp only [integral_const, MeasureTheory.probReal_univ, smul_eq_mul, one_mul] at hsub
          linarith
        linarith

/-- **Quantum compatibility constraint**: if E_C = 0 and |E_Q| = 1,
    the model is incompatible (the thermal correction can't reach ±1). -/
theorem quantum_compatible_constraint (μ₀ : Measure Λ) [IsProbabilityMeasure μ₀]
    (A B : ResponseFunction Λ μ₀) (ε : Λ → ℝ)
    (hε_bounded : ∀ ω, |ε ω| < 1) (hε_int : Integrable ε μ₀)
    (h_E_C_zero : E_C μ₀ A B = 0) (θ : ℝ) (h_E_Q_one : |E_Q θ| = 1) :
    ¬ quantum_compatible μ₀ A B ε θ := by
  intro h_compat
  unfold quantum_compatible E_full at h_compat
  rw [h_E_C_zero, zero_add] at h_compat
  have : |∫ ω, A ω * B ω * ε ω ∂μ₀| = 1 := by
    show |E_thermal μ₀ A B ε| = 1; rw [h_compat]; exact h_E_Q_one
  linarith [abs_integral_ABε_lt_one μ₀ A B ε hε_bounded hε_int]

/-- **At θ = 0 (E_Q = −1) or θ = π (E_Q = 1), E_C cannot be zero.** -/
theorem E_C_nonzero_at_extremes (μ₀ : Measure Λ) [IsProbabilityMeasure μ₀]
    (A B : ResponseFunction Λ μ₀) (ε : Λ → ℝ)
    (hε_bounded : ∀ ω, |ε ω| < 1) (hε_int : Integrable ε μ₀)
    (h_compat : quantum_compatible μ₀ A B ε 0) : E_C μ₀ A B ≠ 0 := by
  intro h_zero
  exact quantum_compatible_constraint μ₀ A B ε hε_bounded hε_int h_zero 0
    (by unfold E_Q; simp [Real.cos_zero]) h_compat

/-- At θ = 0, minimum |E_C| ≥ 1 − ε_max. -/
lemma classical_correlation_lower_bound (ε_max : ℝ) (hε' : ε_max < 1) :
    ∀ E_C E_th : ℝ, E_C + E_th = -1 → |E_th| ≤ ε_max → |E_C| ≥ 1 - ε_max := by
  intro E_C E_th h_sum h_th
  have h_bounds := abs_le.mp h_th
  rw [show E_C = -1 - E_th from by linarith]
  rw [abs_of_neg (by linarith [h_bounds.2])]
  linarith [h_bounds.1]

end ThermalBell
