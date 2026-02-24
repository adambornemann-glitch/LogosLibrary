/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.CrossMeasure
/-!
# Functional Domain

This file defines the functional domain `{ψ : ∫|f|² dμ_ψ < ∞}` where `f(A)ψ` is defined,
and establishes that it forms a submodule of `H`.

## Main definitions

* `functionalDomain`: The set `{ψ : ∫|f|² dμ_ψ < ∞}` where `f(A)ψ` is defined
* `functionalDomainSubmodule`: The functional domain as a `Submodule ℂ H`

## Main results

* `functionalDomain_zero_mem`: `0 ∈ dom(f(A))`
* `functionalDomain_smul_mem`: Closed under scalar multiplication
* `functionalDomain_add_mem`: Closed under addition
* `functionalDomain_inter`: Intersection property
* `functionalDomain_mul_bound`: Product domain inclusion
* `functionalDomain_of_bounded`: Bounded functions have full domain
* `functionalDomain_id_iff`: Identity domain iff finite second moment

## Tags

functional domain, spectral measure, domain of operator
-/

namespace FunctionalCalculus

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory InnerProductSpace Complex QuantumMechanics.Cayley SpectralBridge.Resolvent SpectralBridge.Bochner QuantumMechanics.Generators ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## Functional Domain Definition
-/

/-- The domain of f(A) consists of vectors with finite f-moment. -/
def functionalDomain (μ : H → Measure ℝ) (f : ℝ → ℂ) : Set H :=
  {ψ : H | Integrable (fun s => ‖f s‖^2) (μ ψ)}

/-!
## Integrability Axiom
-/


/-- The parallelogram law for spectral scalar measures:
    `μ_{x+y}(B) + μ_{x-y}(B) = 2μ_x(B) + 2μ_y(B)`.-/
lemma spectral_scalar_measure_parallelogram (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (x y : H) (B : Set ℝ) (hB : MeasurableSet B) :
    spectral_scalar_measure E (x + y) hE B + spectral_scalar_measure E (x - y) hE B =
    (2 : ENNReal) • spectral_scalar_measure E x hE B + (2 : ENNReal) • spectral_scalar_measure E y hE B := by

  simp only [spectral_scalar_measure_apply E hE _ B hB]

  have hx_nn : 0 ≤ (⟪E B x, x⟫_ℂ).re := spectral_measure_inner_nonneg E hE B hB x
  have hy_nn : 0 ≤ (⟪E B y, y⟫_ℂ).re := spectral_measure_inner_nonneg E hE B hB y
  have hxy_nn : 0 ≤ (⟪E B (x + y), x + y⟫_ℂ).re := spectral_measure_inner_nonneg E hE B hB (x + y)
  have hxy'_nn : 0 ≤ (⟪E B (x - y), x - y⟫_ℂ).re := spectral_measure_inner_nonneg E hE B hB (x - y)

  have h_cpx : ⟪E B (x + y), x + y⟫_ℂ + ⟪E B (x - y), x - y⟫_ℂ =
               2 * ⟪E B x, x⟫_ℂ + 2 * ⟪E B y, y⟫_ℂ := by
    simp only [map_add, map_sub, inner_add_left, inner_add_right,
               inner_sub_left, inner_sub_right]
    ring

  have h_real : (⟪E B (x + y), x + y⟫_ℂ).re + (⟪E B (x - y), x - y⟫_ℂ).re =
                2 * (⟪E B x, x⟫_ℂ).re + 2 * (⟪E B y, y⟫_ℂ).re := by
    calc (⟪E B (x + y), x + y⟫_ℂ).re + (⟪E B (x - y), x - y⟫_ℂ).re
        = (⟪E B (x + y), x + y⟫_ℂ + ⟪E B (x - y), x - y⟫_ℂ).re := by simp [Complex.add_re]
      _ = (2 * ⟪E B x, x⟫_ℂ + 2 * ⟪E B y, y⟫_ℂ).re := by rw [h_cpx]
      _ = 2 * (⟪E B x, x⟫_ℂ).re + 2 * (⟪E B y, y⟫_ℂ).re := by
            simp only [Complex.add_re, Complex.mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]

  rw [← ENNReal.ofReal_add hxy_nn hxy'_nn]
  rw [h_real]
  rw [ENNReal.ofReal_add (by linarith) (by linarith)]
  simp only [Nat.ofNat_nonneg, ENNReal.ofReal_mul, ENNReal.ofReal_ofNat, smul_eq_mul]

/-- The spectral scalar measure of a sum is dominated by the sum of measures:
    `μ_{x+y}(B) ≤ 2μ_x(B) + 2μ_y(B)`.

    This follows immediately from the parallelogram law and nonnegativity of `μ_{x-y}`. -/
lemma spectral_scalar_measure_add_le (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (x y : H) (B : Set ℝ) (hB : MeasurableSet B) :
    spectral_scalar_measure E (x + y) hE B ≤
    (2 : ENNReal) • spectral_scalar_measure E x hE B + (2 : ENNReal) • spectral_scalar_measure E y hE B := by
  have h_para := spectral_scalar_measure_parallelogram E hE x y B hB
  calc spectral_scalar_measure E (x + y) hE B
      ≤ spectral_scalar_measure E (x + y) hE B + spectral_scalar_measure E (x - y) hE B :=
          le_add_of_nonneg_right (zero_le _)
    _ = (2 : ENNReal) • spectral_scalar_measure E x hE B + (2 : ENNReal) • spectral_scalar_measure E y hE B := by exact h_para



/-- Integrability transfers through measure domination: if `f` is integrable against
    `μ_x` and `μ_y`, then it's integrable against `μ_{x+y}`.

    Proof: By the parallelogram law, `μ_{x+y} ≤ 2μ_x + 2μ_y`, so
    `∫|f|² dμ_{x+y} ≤ 2∫|f|² dμ_x + 2∫|f|² dμ_y < ∞`. -/
lemma spectral_integral_add_bound (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (x y : H) (f : ℝ → ℂ)
    (hx : Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E x hE))
    (hy : Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E y hE)) :
    Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E (x + y) hE) := by
  -- The dominating measure
  let μ_dom := (2 : ENNReal) • spectral_scalar_measure E x hE + (2 : ENNReal) • spectral_scalar_measure E y hE

  -- f is integrable against the dominating measure
  have h_int_dom : Integrable (fun s => ‖f s‖^2) μ_dom := by
    simp only [μ_dom]
    -- Integrable against sum = integrable against both
    --rw [Measure.add_comm]  -- might not need this
    apply Integrable.add_measure

    · exact hx.smul_measure ENNReal.ofNat_ne_top
    · exact hy.smul_measure ENNReal.ofNat_ne_top

  have h_le : spectral_scalar_measure E (x + y) hE ≤ μ_dom := Measure.le_iff.mpr fun B hB => by
    simp only [μ_dom, Measure.add_apply, Measure.smul_apply]
    exact spectral_scalar_measure_add_le E hE x y B hB

  -- Transfer integrability via domination
  exact Integrable.mono_measure h_int_dom h_le


/-!
## Basic Membership Lemmas
-/

/-- Helper: zero is in the functional domain -/
lemma functionalDomain_zero_mem (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ) :
    (0 : H) ∈ functionalDomain (spectral_scalar_measure E · hE) f := by
  simp only [functionalDomain, Set.mem_setOf_eq]
  rw [spectral_scalar_measure_zero_eq E hE]
  exact integrable_zero_measure

/-- Helper: scalar multiples preserve functional domain -/
lemma functionalDomain_smul_mem (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f : ℝ → ℂ) (c : ℂ) (ψ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    c • ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f := by
  simp only [functionalDomain, Set.mem_setOf_eq] at hψ ⊢
  rw [spectral_scalar_measure_smul_eq E hE hE_univ c ψ]
  exact Integrable.smul_measure hψ ENNReal.coe_ne_top

/-- Helper: sums preserve functional domain -/
lemma functionalDomain_add_mem (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f : ℝ → ℂ) (x y : H)
    (hx : x ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hy : y ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    x + y ∈ functionalDomain (spectral_scalar_measure E · hE) f := by
  simp only [functionalDomain, Set.mem_setOf_eq] at hx hy ⊢
  exact spectral_integral_add_bound E hE x y f hx hy

/-!
## Submodule Structure
-/

/-- The functional domain is a submodule -/
def functionalDomainSubmodule' (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f : ℝ → ℂ) : Submodule ℂ H where
  carrier := functionalDomain (spectral_scalar_measure E · hE) f
  zero_mem' := functionalDomain_zero_mem E hE f
  add_mem' := fun hx hy => functionalDomain_add_mem E hE f _ _ hx hy
  smul_mem' := fun c _ hψ => functionalDomain_smul_mem E hE hE_univ f c _ hψ

/-!
## Auxiliary Lemmas for Domain Properties
-/

/-- If `ψ` is in the functional domain for both `f` and `g`, then `ψ` is in the
    functional domain for `f + g`. Uses the bound `‖f + g‖² ≤ 2‖f‖² + 2‖g‖²`. -/
lemma functionalDomain_inter_aux (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f g : ℝ → ℂ) (ψ : H)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf : Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E ψ hE))
    (hg : Integrable (fun s => ‖g s‖^2) (spectral_scalar_measure E ψ hE)) :
    Integrable (fun s => ‖f s + g s‖^2) (spectral_scalar_measure E ψ hE) := by

  have h_bound : ∀ s, ‖f s + g s‖^2 ≤ 2 * ‖f s‖^2 + 2 * ‖g s‖^2 := fun s => by
    have h1 : ‖f s + g s‖ ≤ ‖f s‖ + ‖g s‖ := norm_add_le _ _
    have h2 : ‖f s + g s‖^2 ≤ (‖f s‖ + ‖g s‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : 2 * ‖f s‖ * ‖g s‖ ≤ ‖f s‖^2 + ‖g s‖^2 := two_mul_le_add_sq _ _
    calc ‖f s + g s‖^2 ≤ (‖f s‖ + ‖g s‖)^2 := h2
      _ = ‖f s‖^2 + 2 * ‖f s‖ * ‖g s‖ + ‖g s‖^2 := by ring
      _ ≤ 2 * ‖f s‖^2 + 2 * ‖g s‖^2 := by linarith

  have h_int_bound : Integrable (fun s => 2 * ‖f s‖^2 + 2 * ‖g s‖^2) _ :=
    (hf.const_mul 2).add (hg.const_mul 2)

  apply Integrable.mono' h_int_bound
  · exact ((hf_meas.add hg_meas).norm.pow_const 2).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact h_bound s

/-- If `f` is bounded by `M` and `ψ` is in the functional domain for `g`, then
    `ψ` is in the functional domain for `f * g`. Uses `‖fg‖² ≤ M²·‖g‖²`. -/
lemma functionalDomain_mul_bound_aux (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f g : ℝ → ℂ) (M : ℝ) (ψ : H)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_bound : ∀ s, ‖f s‖ ≤ M)
    (hg : Integrable (fun s => ‖g s‖^2) (spectral_scalar_measure E ψ hE)) :
    Integrable (fun s => ‖f s * g s‖^2) (spectral_scalar_measure E ψ hE) := by
  have h_bound : ∀ s, ‖f s * g s‖^2 ≤ M^2 * ‖g s‖^2 := fun s => by
    rw [norm_mul, mul_pow]
    apply mul_le_mul_of_nonneg_right
    · exact pow_le_pow_left₀ (norm_nonneg _) (hf_bound s) 2
    · exact sq_nonneg _
  have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hf_bound 0)
  have h_int_bound : Integrable (fun s => M^2 * ‖g s‖^2) _ := hg.const_mul (M^2)
  refine Integrable.mono' h_int_bound ?_ ?_
  · exact ((hf_meas.mul hg_meas).norm.pow_const 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall ?_
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact h_bound s

/-- Any vector `ψ` is in the functional domain for a bounded function `f`.
    Since `‖f‖ ≤ M` implies `‖f‖² ≤ M²`, and the spectral measure is finite,
    the integral `∫ ‖f‖² dμ_ψ ≤ M² · μ_ψ(ℝ) < ∞`. -/
lemma functionalDomain_of_bounded_aux (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f : ℝ → ℂ) (M : ℝ) (ψ : H)
    (hf_meas : Measurable f)
    (hf : ∀ s, ‖f s‖ ≤ M) :
    Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E ψ hE) := by
  haveI : IsFiniteMeasure (spectral_scalar_measure E ψ hE) :=
    spectral_scalar_measure_finite E hE hE_univ ψ
  refine Integrable.of_bound ?_ (M^2) ?_
  · exact (hf_meas.norm.pow_const 2).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hf s) 2

/-!
## Main Domain Theorems
-/

/-- Intersection of functional domains -/
lemma functionalDomain_inter (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f g : ℝ → ℂ)
    (hf_meas : Measurable f) (hg_meas : Measurable g) :
    functionalDomain (spectral_scalar_measure E · hE) f ∩
    functionalDomain (spectral_scalar_measure E · hE) g ⊆
    functionalDomain (spectral_scalar_measure E · hE) (fun s => f s + g s) := by
  intro ψ ⟨hf, hg⟩
  simp only [functionalDomain, Set.mem_setOf_eq] at hf hg ⊢
  exact functionalDomain_inter_aux E hE f g ψ hf_meas hg_meas hf hg

/-- Product bound for functional domains -/
lemma functionalDomain_mul_bound (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f g : ℝ → ℂ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_bdd : ∃ M, ∀ s, ‖f s‖ ≤ M) :
    functionalDomain (spectral_scalar_measure E · hE) g ⊆
    functionalDomain (spectral_scalar_measure E · hE) (fun s => f s * g s) := by
  intro ψ hg
  simp only [functionalDomain, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨M, hM⟩ := hf_bdd
  exact functionalDomain_mul_bound_aux E hE f g M ψ hf_meas hg_meas hM hg

/-- Bounded functions always give full domain -/
lemma functionalDomain_of_bounded (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f : ℝ → ℂ)
    (hf_meas : Measurable f)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) (ψ : H) :
    ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f := by
  simp only [functionalDomain, Set.mem_setOf_eq]
  obtain ⟨M, hM⟩ := hf
  exact functionalDomain_of_bounded_aux E hE hE_univ f M ψ hf_meas hM

/-- Indicator functions are bounded -/
lemma indicator_bounded (B : Set ℝ) :
    ∃ M : ℝ, ∀ s, ‖Set.indicator B (1 : ℝ → ℂ) s‖ ≤ M := by
  use 1
  intro s
  by_cases hs : s ∈ B
  · simp [Set.indicator_of_mem hs]
  · simp [Set.indicator_of_notMem hs]

/-- Identity function is in the domain iff finite second moment -/
lemma functionalDomain_id_iff (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (ψ : H) :
    ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun s => (s : ℂ)) ↔
    Integrable (fun s => s^2) (spectral_scalar_measure E ψ hE) := by
  simp only [functionalDomain, Set.mem_setOf_eq]
  constructor
  · intro h
    convert h using 2
    simp_all only [norm_real, Real.norm_eq_abs, sq_abs]
  · intro h
    convert h using 2
    simp_all only [norm_real, Real.norm_eq_abs, sq_abs]

/-!
## Main Submodule Definition
-/

/-- Domain as submodule -/
def functionalDomainSubmodule (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f : ℝ → ℂ) : Submodule ℂ H where
  carrier := functionalDomain (spectral_scalar_measure E · hE) f
  zero_mem' := functionalDomain_zero_mem E hE f
  add_mem' := fun hx hy => functionalDomain_add_mem E hE f _ _ hx hy
  smul_mem' := fun c _ hψ => functionalDomain_smul_mem E hE hE_univ f c _ hψ

end FunctionalCalculus
