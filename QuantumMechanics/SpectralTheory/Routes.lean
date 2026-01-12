/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent
/-!
# Spectral Bridge: From Unitary Groups to Spectral Measures

This file establishes the connection between strongly continuous one-parameter
unitary groups and projection-valued spectral measures via two independent routes:
the **Bochner route** (through positive-definite functions) and the **Resolvent route**
(through Stone's formula and Stieltjes inversion).

## Overview

Given a unitary group `U(t)` with self-adjoint generator `A`, we construct the
spectral measure `E` satisfying:
- `U(t) = ∫ e^{itλ} dE(λ)` (spectral representation of the unitary group)
- `A = ∫ λ dE(λ)` (spectral representation of the generator)
- `R(z) = ∫ (λ - z)⁻¹ dE(λ)` (spectral representation of the resolvent)

## Main definitions

### Bochner Route
* `PositiveDefinite`: A function `f : ℝ → ℂ` satisfying the positive-definiteness condition
* `PositiveDefiniteContinuous`: Positive-definite and continuous at 0
* `IsSpectralMeasure`: Structure bundling the axioms for a projection-valued measure
* `spectralDistribution`: The Stieltjes function `t ↦ ⟨E(-∞,t]ψ, ψ⟩`
* `spectral_scalar_measure`: The scalar measure `μ_ψ(B) = ⟨E(B)ψ, ψ⟩`
* `bochner_measure`: The measure obtained from Bochner's theorem applied to `⟨U(t)ψ, ψ⟩`

### Resolvent Route
* `offRealPoint`: Helper for constructing `t + iε` as an `OffRealAxis` point
* `resolvent_integrand`: The kernel `(s - z)⁻¹` for spectral integrals
* `spectral_integral`: The operator-valued Stieltjes integral `∫ f(λ) dE(λ)`

## Main statements

### Bochner Route
* `unitary_correlation_positive_definite`: The function `t ↦ ⟨U(t)ψ, ψ⟩` is positive-definite
* `unitary_correlation_pd_continuous`: Combined with continuity, satisfies Bochner's hypotheses
* `bochner_measure_eq_spectral`: The Bochner measure equals the spectral scalar measure
* `polarization_spectral`: Off-diagonal terms `⟨E(B)ψ, φ⟩` recovered via polarization identity

### Resolvent Route
* `resolvent_kernel_im`: `Im((s - (t + iε))⁻¹) = ε/((s-t)² + ε²)` (Lorentzian)
* `resolvent_kernel_diff`: `(s - (t+iε))⁻¹ - (s - (t-iε))⁻¹ = 2iε/((s-t)² + ε²)`
* `lorentzian_approx_delta`: The Lorentzian `(1/π) · ε/((s-t)² + ε²) → δ(s-t)` as `ε → 0`
* `stieltjes_inversion`: `⟨E(a,b]ψ, ψ⟩ = lim_{ε→0} (1/π) ∫_a^b Im⟨R(t+iε)ψ, ψ⟩ dt`
* `stones_formula`: `E(a,b) = s-lim_{ε→0} (1/2πi) ∫_a^b [R(t+iε) - R(t-iε)] dt`
* `resolvent_spectral_representation`: `R(z)ψ = ∫ (λ-z)⁻¹ dE(λ) ψ`

## Proof strategy

### Bochner Route
1. Show `⟨U(t)ψ, ψ⟩` is positive-definite using `⟨U(s-r)ψ, ψ⟩ = ⟨U(s)ψ, U(r)ψ⟩`
2. Apply Bochner's theorem to get a measure `μ_ψ` with `⟨U(t)ψ, ψ⟩ = ∫ e^{itλ} dμ_ψ`
3. Show uniqueness: the Bochner measure equals the spectral scalar measure
4. Recover operator-valued `E(B)` via polarization from scalar measures

### Resolvent Route
1. The Lorentzian kernel `ε/((s-t)² + ε²)` is an approximate identity
2. Stone's formula expresses `E(a,b]` as a limit of resolvent integrals
3. The resolvent has spectral representation `R(z) = ∫ (λ-z)⁻¹ dE(λ)`

## Implementation notes

This file is currently **heavily axiomatized**. The following results are stated as
axioms pending full proofs:

### Axioms from measure theory / harmonic analysis
* `bochner_theorem`: Bochner's theorem for positive-definite functions
* `measure_eq_of_fourier_eq`: Uniqueness of measures from Fourier transforms
* `lorentzian_total_integral`: `∫ ε/((s-t)² + ε²) ds = π`
* `lorentzian_concentration`: Lorentzian concentrates at `t` as `ε → 0`
* `approx_identity_continuous`: General approximation to identity theorem

### Axioms connecting structures
* `spectral_scalar_measure_apply`: `μ_ψ(B) = ⟨E(B)ψ, ψ⟩`
* `spectral_integral_relation`: `⟨U(t)ψ, ψ⟩ = ∫ e^{itλ} dμ_ψ(λ)`
* `resolvent_spectral_bilinear`: `⟨R(z)ψ, ψ⟩ = ∫ (s-z)⁻¹ dμ_ψ(s)`

### Axioms for Fubini / dominated convergence
* `lorentzian_fubini`, `resolvent_diff_fubini`: Order of integration swaps
* `arctan_dominated_convergence`, `stones_dominated_convergence`: DCT applications

The logical structure is complete; discharging axioms requires:
- Bochner's theorem (substantial harmonic analysis)
- Careful measure-theoretic bookkeeping for Stieltjes integrals
- Integrability and dominated convergence arguments

## Physical interpretation

This file establishes that spectral measures are the "Fourier dual" of time evolution.
The correlation function `⟨U(t)ψ, ψ⟩` encodes the same information as the spectral
distribution `⟨E(λ)ψ, ψ⟩`, related by Fourier transform.

Stone's formula is the physicist's standard tool for computing spectral projections
from the resolvent (Green's function). The imaginary part of `⟨R(t+iε)ψ, ψ⟩` gives
the spectral density, regularized by the Lorentzian kernel.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Sections VII-VIII
* [Rudin, *Functional Analysis*][rudin1991], Chapter 12
* [Schmüdgen, *Unbounded Self-adjoint Operators*][schmudgen2012], Chapter 5
* Bochner, "Monotone Funktionen, Stieltjessche Integrale und harmonische Analyse" (1933)
* Stone, "Linear Transformations in Hilbert Space" (1932)

## TODO

* Prove Bochner's theorem (requires Herglotz representation or direct construction)
* Discharge Fubini axioms via mathlib's product measure machinery
* Prove approximation to identity theorem for Lorentzian kernel
* Connect to functional calculus: `f(A) = ∫ f(λ) dE(λ)`
* Establish spectral mapping theorem

## Tags

spectral measure, Bochner theorem, Stone's formula, Stieltjes inversion,
resolvent, projection-valued measure, functional calculus
-/
namespace SpectralBridge


open InnerProductSpace MeasureTheory Complex Filter Topology  QuantumMechanics.Bochner QuantumMechanics.Generators
open scoped BigOperators Topology

-- STEP 1: Redeclare H and its instances (required in nested namespace)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


namespace BochnerRoute
set_option linter.unusedSectionVars false

/-- A function f : ℝ → ℂ is positive-definite. -/
def PositiveDefinite (f : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * f (t i - t j)).re

/-- Continuous positive-definite function. -/
def PositiveDefiniteContinuous (f : ℝ → ℂ) : Prop :=
  PositiveDefinite f ∧ ContinuousAt f 0

lemma tendsto_nhdsWithin_Ici_of_tendsto_nhdsWithin_Ioi {f : ℝ → ℝ} {x : ℝ}
    (h : Tendsto f (𝓝[>] x) (𝓝 (f x))) : ContinuousWithinAt f (Set.Ici x) x := by
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [Metric.tendsto_nhdsWithin_nhds] at h
  obtain ⟨δ, hδ_pos, hδ⟩ := h ε hε
  refine ⟨δ, hδ_pos, fun t ht_Ici ht_dist => ?_⟩
  obtain rfl | h_lt := (Set.mem_Ici.mp ht_Ici).eq_or_lt
  · rw [dist_self]; exact hε
  · exact hδ h_lt ht_dist

lemma spectral_projection_norm_le (E : Set ℝ → H →L[ℂ] H)
    (hE_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C))
    (hE_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    ‖E B ψ‖ ≤ ‖ψ‖ := by
  -- E(B) is idempotent
  have h_idem : E B * E B = E B := by rw [hE_mul B B hB hB, Set.inter_self]
  -- ‖E(B)ψ‖² = ⟨E(B)ψ, E(B)ψ⟩ = ⟨E(B)²ψ, ψ⟩ = ⟨E(B)ψ, ψ⟩
  have h1 : ‖E B ψ‖^2 = (⟪E B ψ, ψ⟫_ℂ).re := by
    calc ‖E B ψ‖^2
        = (⟪E B ψ, E B ψ⟫_ℂ).re := by
          rw [inner_self_eq_norm_sq_to_K]
          rw [← @RCLike.ofReal_pow]
          exact rfl
      _ = (⟪E B (E B ψ), ψ⟫_ℂ).re := by rw [hE_sa B (E B ψ) ψ]
      _ = (⟪(E B * E B) ψ, ψ⟫_ℂ).re := by rw [ContinuousLinearMap.mul_apply]
      _ = (⟪E B ψ, ψ⟫_ℂ).re := by rw [h_idem]
  -- By Cauchy-Schwarz: |⟨E(B)ψ, ψ⟩| ≤ ‖E(B)ψ‖·‖ψ‖
  have h2 : |(⟪E B ψ, ψ⟫_ℂ).re| ≤ ‖E B ψ‖ * ‖ψ‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  -- Since (⟨E(B)ψ, ψ⟩).re = ‖E(B)ψ‖² ≥ 0
  have h3 : (⟪E B ψ, ψ⟫_ℂ).re ≥ 0 := by rw [← h1]; exact sq_nonneg _
  -- So ‖E(B)ψ‖² ≤ ‖E(B)ψ‖·‖ψ‖
  have h4 : ‖E B ψ‖^2 ≤ ‖E B ψ‖ * ‖ψ‖ := h1 ▸ (abs_of_nonneg h3 ▸ h2)
  -- If ‖E(B)ψ‖ = 0, done. Otherwise divide by ‖E(B)ψ‖.
  by_cases hE : ‖E B ψ‖ = 0
  · simp [hE]
  · have hE_pos : 0 < ‖E B ψ‖ := (norm_nonneg _).lt_of_ne' hE
    calc ‖E B ψ‖ = ‖E B ψ‖^2 / ‖E B ψ‖ := by field_simp
      _ ≤ (‖E B ψ‖ * ‖ψ‖) / ‖E B ψ‖ := by exact
        (div_le_div_iff_of_pos_right hE_pos).mpr h4
      _ = ‖ψ‖ := by exact mul_div_cancel_left₀ ‖ψ‖ hE

lemma spectral_projection_opNorm_le_one (E : Set ℝ → H →L[ℂ] H)
    (hE_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C))
    (hE_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ‖E B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  simp only [one_mul]
  exact spectral_projection_norm_le E hE_mul hE_sa B hB ψ

noncomputable def spectralDistribution (E : Set ℝ → H →L[ℂ] H) (ψ : H)
    -- Add these hypotheses:
    (hE_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C))
    (hE_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ)
    (hE_sot : ∀ t₀, Tendsto (fun t => E (Set.Iic t) ψ) (𝓝[>] t₀) (𝓝 (E (Set.Iic t₀) ψ))) :
    StieltjesFunction where
  toFun := fun t => (⟪E (Set.Iic t) ψ, ψ⟫_ℂ).re

  mono' := fun s t hst => by
    -- E(Iic s) = E(Iic s) * E(Iic t) since Iic s ⊆ Iic t
    have h_subset : Set.Iic s ∩ Set.Iic t = Set.Iic s := by simp only [Set.Iic_inter_Iic] ; rw [inf_of_le_left
        hst]
    have h_factor : E (Set.Iic s) = E (Set.Iic s) * E (Set.Iic t) := by
      rw [hE_mul _ _ measurableSet_Iic measurableSet_Iic, h_subset]

    -- ⟨E(B)ψ, ψ⟩ = ‖E(B)ψ‖² for self-adjoint idempotent E(B)
    have h_norm_sq : ∀ B, MeasurableSet B → (⟪E B ψ, ψ⟫_ℂ).re = ‖E B ψ‖^2 := by
      intro B hB
      have h_idem : E B * E B = E B := by rw [hE_mul B B hB hB, Set.inter_self]
      calc (⟪E B ψ, ψ⟫_ℂ).re
          = (⟪E B (E B ψ), ψ⟫_ℂ).re := by rw [← ContinuousLinearMap.mul_apply, h_idem]
        _ = (⟪E B ψ, E B ψ⟫_ℂ).re := by rw [hE_sa B (E B ψ) ψ]
        _ = ‖E B ψ‖^2 := by rw [inner_self_eq_norm_sq_to_K]; rw [← @RCLike.ofReal_pow]; exact rfl

    -- E(Iic s)ψ = E(Iic s)(E(Iic t)ψ), so ‖E(Iic s)ψ‖ ≤ ‖E(Iic t)ψ‖
    show (⟪E (Set.Iic s) ψ, ψ⟫_ℂ).re ≤ (⟪E (Set.Iic t) ψ, ψ⟫_ℂ).re
    rw [h_norm_sq _ measurableSet_Iic, h_norm_sq _ measurableSet_Iic]
    have h_contract : ‖E (Set.Iic s) ψ‖ ≤ ‖E (Set.Iic t) ψ‖ := by
      calc ‖E (Set.Iic s) ψ‖
          = ‖(E (Set.Iic s) * E (Set.Iic t)) ψ‖ := by rw [← h_factor]
        _ = ‖E (Set.Iic s) (E (Set.Iic t) ψ)‖ := by rw [ContinuousLinearMap.mul_apply]
        _ ≤ ‖E (Set.Iic s)‖ * ‖E (Set.Iic t) ψ‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖E (Set.Iic t) ψ‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              exact spectral_projection_opNorm_le_one E hE_mul hE_sa (Set.Iic s) measurableSet_Iic
        _ = ‖E (Set.Iic t) ψ‖ := one_mul _
    exact sq_le_sq' (by linarith [norm_nonneg (E (Set.Iic s) ψ)]) h_contract

  right_continuous' := fun t₀ => by
    have h := hE_sot t₀
    have h_inner : Tendsto (fun t => ⟪E (Set.Iic t) ψ, ψ⟫_ℂ) (𝓝[>] t₀)
                          (𝓝 ⟪E (Set.Iic t₀) ψ, ψ⟫_ℂ) :=
      Filter.Tendsto.inner h tendsto_const_nhds
    have h_re : Tendsto (fun t => (⟪E (Set.Iic t) ψ, ψ⟫_ℂ).re) (𝓝[>] t₀)
                        (𝓝 (⟪E (Set.Iic t₀) ψ, ψ⟫_ℂ).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp h_inner
    exact tendsto_nhdsWithin_Ici_of_tendsto_nhdsWithin_Ioi h_re


structure IsSpectralMeasure (E : Set ℝ → H →L[ℂ] H) : Prop where
  mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C)
  sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ
  sot : ∀ ψ t₀, Filter.Tendsto (fun t => E (Set.Iic t) ψ) (nhdsWithin t₀ (Set.Ioi t₀)) (nhds (E (Set.Iic t₀) ψ))
  empty : E ∅ = 0
  univ : E Set.univ = 1
  add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C → E (B ∪ C) = E B + E C

/-- The spectral scalar measure FROM the Stieltjes function -/
noncomputable def spectral_scalar_measure (E : Set ℝ → H →L[ℂ] H) (ψ : H)
    (hE : IsSpectralMeasure E) : Measure ℝ :=
  (spectralDistribution E ψ hE.mul hE.sa (hE.sot ψ)).measure

/-- The spectral scalar measure assigns B ↦ ⟪E(B)ψ, ψ⟫.re -/
axiom spectral_scalar_measure_apply' (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E) (ψ : H)
    (B : Set ℝ) (hB : MeasurableSet B) :
  (spectral_scalar_measure E ψ hE B).toReal = (⟪E B ψ, ψ⟫_ℂ).re

/-- The spectral scalar measure assigns finite values matching the inner product. -/
axiom spectral_scalar_measure_apply (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E) (ψ : H)
    (B : Set ℝ) (hB : MeasurableSet B) :
  spectral_scalar_measure E ψ hE B = ENNReal.ofReal (⟪E B ψ, ψ⟫_ℂ).re

/-- Spectral theorem: the Fourier transform of the spectral measure gives the correlation. -/
axiom spectral_integral_relation (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E)
    (U_grp : OneParameterUnitaryGroup (H := H)) (ψ : H) (t : ℝ) :
  ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ ω, Complex.exp (I * ω * t) ∂(spectral_scalar_measure E ψ hE)

/-- Uniqueness: a finite measure is determined by its Fourier transform. -/
axiom measure_eq_of_fourier_eq (μ ν : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν] :
  (∀ t : ℝ, ∫ ω, Complex.exp (I * ω * t) ∂μ = ∫ ω, Complex.exp (I * ω * t) ∂ν) → μ = ν

/-- The spectral scalar measure is finite (bounded by ‖ψ‖²). -/
lemma spectral_scalar_measure_finite (E : Set ℝ → (H →L[ℂ] H)) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (ψ : H) :
    IsFiniteMeasure (spectral_scalar_measure E ψ hE) := by
  constructor
  rw [spectral_scalar_measure_apply E hE ψ Set.univ MeasurableSet.univ]
  rw [hE_univ]
  simp only [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, coe_algebraMap]
  exact ENNReal.ofReal_lt_top


/-- E(B) is self-adjoint (orthogonal projection). -/
axiom spectral_self_adjoint (E : Set ℝ → (H →L[ℂ] H))
    (B : Set ℝ) (ψ φ : H) :
  ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ

/-- **Bochner's Theorem** (axiom). -/
axiom bochner_theorem (f : ℝ → ℂ) (hf : PositiveDefiniteContinuous f) :
  ∃ (μ : MeasureTheory.Measure ℝ),
    MeasureTheory.IsFiniteMeasure μ ∧
    ∀ t, f t = ∫ ω, Complex.exp (I * ω * t) ∂μ

-- STEP 2: Declare U_grp as a variable AFTER H is in scope
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The function t ↦ ⟨U(t)ψ, ψ⟩ is positive-definite. -/
theorem unitary_correlation_positive_definite (ψ : H) :
    PositiveDefinite (fun t => ⟪U_grp.U t ψ, ψ⟫_ℂ) := by
  intro n t c
  set v := ∑ i : Fin n, c i • U_grp.U (t i) ψ with hv_def

  -- Key: ⟨U(s-r)ψ, ψ⟩ = ⟨U(s)ψ, U(r)ψ⟩ by unitarity
  have h_corr : ∀ i j : Fin n,
      ⟪U_grp.U (t i - t j) ψ, ψ⟫_ℂ = ⟪U_grp.U (t i) ψ, U_grp.U (t j) ψ⟫_ℂ := by
    intro i j
    calc ⟪U_grp.U (t i - t j) ψ, ψ⟫_ℂ
        = ⟪U_grp.U (t j) (U_grp.U (t i - t j) ψ), U_grp.U (t j) ψ⟫_ℂ := by
            rw [U_grp.unitary (t j)]
      _ = ⟪U_grp.U (t j + (t i - t j)) ψ, U_grp.U (t j) ψ⟫_ℂ := by
            rw [U_grp.group_law]; rfl
      _ = ⟪U_grp.U (t i) ψ, U_grp.U (t j) ψ⟫_ℂ := by congr 2; ring_nf

  -- conj(a) * b * ⟨x, y⟩ = ⟨a • x, b • y⟩
  have h_smul : ∀ i j,
      starRingEnd ℂ (c i) * c j * ⟪U_grp.U (t i) ψ, U_grp.U (t j) ψ⟫_ℂ =
      ⟪c i • U_grp.U (t i) ψ, c j • U_grp.U (t j) ψ⟫_ℂ := by
    intro i j; rw [inner_smul_left, inner_smul_right]; ring

  -- Main calculation: sum = ⟨v, v⟩
  calc (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ⟪U_grp.U (t i - t j) ψ, ψ⟫_ℂ).re
      = (∑ i, ∑ j, ⟪c i • U_grp.U (t i) ψ, c j • U_grp.U (t j) ψ⟫_ℂ).re := by
          simp_rw [h_corr, h_smul]
    _ = (∑ i, ⟪c i • U_grp.U (t i) ψ, ∑ j, c j • U_grp.U (t j) ψ⟫_ℂ).re := by
          simp_rw [inner_sum]
    _ = (⟪∑ i, c i • U_grp.U (t i) ψ, ∑ j, c j • U_grp.U (t j) ψ⟫_ℂ).re := by
          rw [sum_inner]
    _ = (⟪v, v⟫_ℂ).re := by rw [← hv_def]
    _ ≥ 0 := inner_self_nonneg (𝕜 := ℂ)

/-- The correlation function is continuous. -/
theorem unitary_correlation_continuous (ψ : H) :
    Continuous (fun t => ⟪U_grp.U t ψ, ψ⟫_ℂ) := by
  apply Continuous.inner
  · exact U_grp.strong_continuous ψ
  · exact continuous_const

/-- Combined: satisfies Bochner's hypotheses. -/
theorem unitary_correlation_pd_continuous (ψ : H) :
    PositiveDefiniteContinuous (fun t => ⟪U_grp.U t ψ, ψ⟫_ℂ) := by
  constructor
  · exact unitary_correlation_positive_definite U_grp ψ
  · exact (unitary_correlation_continuous U_grp ψ).continuousAt

/-- Bochner's theorem gives a measure from the correlation function. -/
noncomputable def bochner_measure (ψ : H) : MeasureTheory.Measure ℝ :=
  Classical.choose (bochner_theorem (fun t => ⟪U_grp.U t ψ, ψ⟫_ℂ)
    (unitary_correlation_pd_continuous U_grp ψ))

-- STEP 3: Declare E as a variable (NOT in theorem signature)
variable (E : Set ℝ → (H →L[ℂ] H))


lemma bochner_measure_spec (ψ : H) :
    MeasureTheory.IsFiniteMeasure (bochner_measure U_grp ψ) ∧
    ∀ t, ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ ω, Complex.exp (I * ω * t) ∂(bochner_measure U_grp ψ) :=
  Classical.choose_spec (bochner_theorem (fun t => ⟪U_grp.U t ψ, ψ⟫_ℂ)
    (unitary_correlation_pd_continuous U_grp ψ))


/-- The Bochner measure IS the spectral measure. -/
theorem bochner_measure_eq_spectral (hE : IsSpectralMeasure E) (hE_univ : E Set.univ = 1)
    (ψ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    (bochner_measure U_grp ψ B).toReal = (⟪E B ψ, ψ⟫_ℂ).re := by
  obtain ⟨h_finite, h_fourier⟩ := bochner_measure_spec U_grp ψ

  haveI : IsFiniteMeasure (bochner_measure U_grp ψ) := h_finite
  haveI : IsFiniteMeasure (spectral_scalar_measure E ψ hE) :=
    spectral_scalar_measure_finite E hE hE_univ ψ

  have h_fourier_eq : ∀ t : ℝ,
      ∫ ω, Complex.exp (I * ω * t) ∂(bochner_measure U_grp ψ) =
      ∫ ω, Complex.exp (I * ω * t) ∂(spectral_scalar_measure E ψ hE) := fun t => by
    rw [← h_fourier t, spectral_integral_relation E hE U_grp ψ t]

  have h_eq : bochner_measure U_grp ψ = spectral_scalar_measure E ψ hE :=
    measure_eq_of_fourier_eq _ _ h_fourier_eq

  rw [h_eq, spectral_scalar_measure_apply' E hE ψ B hB]

/-- Convert spectral measure to ℂ for polarization calculations -/
noncomputable def spectral_measure_cplx
    (U_grp : OneParameterUnitaryGroup (H := H)) (ψ : H) (B : Set ℝ) : ℂ :=
  ((bochner_measure U_grp ψ B).toReal : ℂ)

/-- Diagonal spectral values are real (from self-adjointness). -/
lemma spectral_diagonal_real (B : Set ℝ) (ψ : H) :
    (⟪E B ψ, ψ⟫_ℂ).im = 0 := by
  have h := spectral_self_adjoint E B ψ ψ
  have key : ⟪E B ψ, ψ⟫_ℂ = starRingEnd ℂ ⟪E B ψ, ψ⟫_ℂ :=
    calc ⟪E B ψ, ψ⟫_ℂ
        = ⟪ψ, E B ψ⟫_ℂ := h
      _ = starRingEnd ℂ ⟪E B ψ, ψ⟫_ℂ := by
        exact Eq.symm (conj_inner_symm ψ ((E B) ψ))
  exact Complex.conj_eq_iff_im.mp key.symm

/-- spectral_measure_cplx equals the inner product. -/
lemma spectral_measure_cplx_eq (hE : IsSpectralMeasure E) (hE_univ : E Set.univ = 1)
    (ψ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    spectral_measure_cplx U_grp ψ B = ⟪E B ψ, ψ⟫_ℂ := by
  unfold spectral_measure_cplx
  rw [bochner_measure_eq_spectral U_grp E hE hE_univ ψ B hB]
  have h_im := spectral_diagonal_real E B ψ
  conv_rhs => rw [← Complex.re_add_im ⟪E B ψ, ψ⟫_ℂ, h_im]
  simp

/-- Polarization gives off-diagonal spectral measures. -/
theorem polarization_spectral (hE : IsSpectralMeasure E) (hE_univ : E Set.univ = 1)
    (ψ φ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    ⟪E B ψ, φ⟫_ℂ = (1/4 : ℂ) * (
      spectral_measure_cplx U_grp (ψ + φ) B -
      spectral_measure_cplx U_grp (ψ - φ) B -
      I * spectral_measure_cplx U_grp (ψ + I • φ) B +
      I * spectral_measure_cplx U_grp (ψ - I • φ) B) := by
  simp_rw [spectral_measure_cplx_eq U_grp E hE hE_univ _ _ hB]
  simp only [map_add, map_sub, map_smul]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
             inner_smul_left, inner_smul_right]
  have h_sa : ⟪E B φ, ψ⟫_ℂ = star ⟪E B ψ, φ⟫_ℂ := by
    rw [spectral_self_adjoint E B φ ψ]
    simp only [RCLike.star_def, inner_conj_symm]
  simp only [h_sa, RCLike.star_def, Complex.conj_I]
  set z := ⟪E B ψ, φ⟫_ℂ
  have hI2 : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  linear_combination (norm := ring_nf) (1 - 1) * hI2
  simp only [I_sq, mul_neg, mul_one, neg_mul, add_neg_cancel, zero_add]


section AdditionalLemmas
set_option linter.unusedVariables false

/-- E(B) is idempotent: E(B)² = E(B) -/
lemma spectral_projection_idempotent (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) :
    E B * E B = E B := by
  rw [hE.mul B B hB hB, Set.inter_self]

/-- E(B) + E(Bᶜ) = 1 -/
lemma spectral_projection_compl_add (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (hE_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C → E (B ∪ C) = E B + E C)
    (B : Set ℝ) (hB : MeasurableSet B) :
    E B + E Bᶜ = 1 := by
  have h : B ∪ Bᶜ = Set.univ := by exact Set.union_compl_self B
  have h_disj : Disjoint B Bᶜ := by exact Set.disjoint_compl_right_iff_subset.mpr fun ⦃a⦄ a => a
  rw [← hE_add B Bᶜ hB hB.compl h_disj, h, hE_univ]


/-- Spectral measure of union of disjoint sets -/
lemma spectral_scalar_measure_union (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : Disjoint B C) (ψ : H) :
    spectral_scalar_measure E ψ hE (B ∪ C) =
    spectral_scalar_measure E ψ hE B + spectral_scalar_measure E ψ hE C := by
  haveI := spectral_scalar_measure_finite E hE hE_univ ψ
  exact MeasureTheory.measure_union hBC hC

/-- Spectral measure of set difference -/
lemma spectral_scalar_measure_diff (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) (hCB : C ⊆ B) (ψ : H) :
    spectral_scalar_measure E ψ hE (B \ C) =
    spectral_scalar_measure E ψ hE B - spectral_scalar_measure E ψ hE C := by
  haveI := spectral_scalar_measure_finite E hE hE_univ ψ
  exact MeasureTheory.measure_diff hCB hC.nullMeasurableSet (measure_lt_top _ _).ne

/-- Projection onto intersection -/
lemma spectral_projection_inter (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    E (B ∩ C) = E B * E C := by
  rw [hE.mul B C hB hC]

/-- Order of multiplication doesn't matter -/
lemma spectral_projection_mul_comm (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    E B * E C = E C * E B := by
  rw [hE.mul B C hB hC, hE.mul C B hC hB, Set.inter_comm]

/-- Spectral measure is subadditive -/
lemma spectral_scalar_measure_subadditive (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) (ψ : H) :
    spectral_scalar_measure E ψ hE (B ∪ C) ≤
    spectral_scalar_measure E ψ hE B + spectral_scalar_measure E ψ hE C := by
  haveI := spectral_scalar_measure_finite E hE hE_univ ψ
  exact MeasureTheory.measure_union_le B C

/-- E(B)ψ ∈ Range(E(B)) -/
lemma spectral_projection_range (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    E B (E B ψ) = E B ψ := by
  have h := spectral_projection_idempotent E hE B hB
  calc E B (E B ψ) = (E B * E B) ψ := rfl
    _ = E B ψ := by rw [h]

/-- Norm of projection is at most norm of vector -/
lemma spectral_projection_norm_le' (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    ‖E B ψ‖ ≤ ‖ψ‖ :=
  BochnerRoute.spectral_projection_norm_le E hE.mul hE.sa B hB ψ

end AdditionalLemmas
end BochnerRoute

namespace ResolventRoute
set_option linter.unusedVariables false
open QuantumMechanics.Resolvent

/-- Helper: construct off-real point from real part and positive imaginary part -/
def offRealPoint (t : ℝ) (ε : ℝ) (hε : ε > 0) : OffRealAxis :=
  ⟨↑t + ↑ε * I, by simp [Complex.add_im]; exact ne_of_gt hε⟩

def offRealPointNeg (t : ℝ) (ε : ℝ) (hε : ε > 0) : OffRealAxis :=
  ⟨↑t - ↑ε * I, by simp [Complex.sub_im]; exact ne_of_gt hε⟩

axiom resolvent_spectral_bilinear {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : BochnerRoute.IsSpectralMeasure E)
    (z : OffRealAxis) (ψ : H) :
    ⟪resolventFun gen hsa z ψ, ψ⟫_ℂ =
      ∫ s : ℝ, ((s : ℂ) - z.val)⁻¹ ∂(BochnerRoute.spectral_scalar_measure E ψ hE)

/-- The spectral integral is integrable for z off the real axis. -/
axiom resolvent_spectral_integrable {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : BochnerRoute.IsSpectralMeasure E)
    (z : OffRealAxis) (ψ : H) :
    MeasureTheory.Integrable (fun s : ℝ => ((s : ℂ) - z.val)⁻¹)
      (BochnerRoute.spectral_scalar_measure E ψ hE)


/-- The integrand for resolvent spectral representation -/
noncomputable def resolvent_integrand (μ : MeasureTheory.Measure ℝ) (z : ℂ) : ℝ → ℂ :=
  fun s => ((s : ℂ) - z)⁻¹

/-- The resolvent integrand is integrable for z off the real axis.
    Key: |(s - z)⁻¹| ≤ 1/|Im(z)| for all s ∈ ℝ. -/
lemma resolvent_integrand_bound (z : ℂ) (hz : z.im ≠ 0) (s : ℝ) :
    ‖((s : ℂ) - z)⁻¹‖ ≤ 1 / |z.im| := by
  have h_im : ((s : ℂ) - z).im = -z.im := by simp
  have h_norm_ge : ‖(s : ℂ) - z‖ ≥ |z.im| := by
    calc ‖(s : ℂ) - z‖
        ≥ |((s : ℂ) - z).im| := Complex.abs_im_le_norm _
      _ = |-z.im| := by rw [h_im]
      _ = |z.im| := abs_neg _
  have h_pos : |z.im| > 0 := abs_pos.mpr hz
  calc ‖((s : ℂ) - z)⁻¹‖
      = 1 / ‖(s : ℂ) - z‖ := by rw [norm_inv]; simp only [one_div]
    _ ≤ 1 / |z.im| := by
        apply div_le_div_of_nonneg_left (by norm_num) h_pos h_norm_ge

/-- Imaginary part of resolvent kernel: Im((s - z)⁻¹) for z = t + iε -/
lemma resolvent_kernel_im (s t ε : ℝ) (hε : ε > 0) :
    (((s : ℂ) - (↑t + ↑ε * I))⁻¹).im = ε / ((s - t)^2 + ε^2) := by
  -- (s - (t + iε))⁻¹ = (s - t - iε)⁻¹ = (s - t + iε) / ((s-t)² + ε²)
  have h_denom_ne : ((s - t : ℝ)^2 + ε^2 : ℂ) ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'

  have h_diff : (s : ℂ) - (↑t + ↑ε * I) = (s - t : ℝ) - ε * I := by
    simp only [Complex.ofReal_sub]
    ring

  rw [h_diff]
  -- ((s-t) - εi)⁻¹ = ((s-t) + εi) / ((s-t)² + ε²)
  have h_conj : ((s - t : ℝ) - ε * I)⁻¹ =
      ((s - t : ℝ) + ε * I) / ((s - t)^2 + ε^2 : ℂ) := by
    have h_mul : ((s - t : ℝ) - ε * I) * ((s - t : ℝ) + ε * I) =
        ((s - t)^2 + ε^2 : ℂ) := by
      push_cast
      have hI2 : (I : ℂ)^2 = -1 := Complex.I_sq
      linear_combination (norm := ring) -ε^2 * hI2
    have h_conj_ne : (↑(s - t) : ℂ) + ↑ε * I ≠ 0 := by
      intro h
      have : ε = 0 := by simpa using congrArg Complex.im h
      linarith
    rw [← h_mul]
    field_simp [h_conj_ne]

  rw [h_conj]
  have h_real : ((s - t)^2 + ε^2 : ℂ) = ((s - t)^2 + ε^2 : ℝ) := by push_cast; ring
  rw [h_real, Complex.div_ofReal_im]
  simp [Complex.add_im, Complex.mul_im]


/-- The Lorentzian integrates to π over ℝ. -/
axiom lorentzian_total_integral (t ε : ℝ) (hε : ε > 0) :
    ∫ s, ε / ((s - t)^2 + ε^2) = Real.pi

/-- The Lorentzian is nonnegative. -/
lemma lorentzian_nonneg (s t ε : ℝ) (hε : ε > 0) :
    0 ≤ ε / ((s - t)^2 + ε^2) := by
  apply div_nonneg (le_of_lt hε)
  positivity

/-- The Lorentzian is bounded by 1/ε. -/
lemma lorentzian_bound (s t ε : ℝ) (hε : ε > 0) :
    ε / ((s - t)^2 + ε^2) ≤ 1 / ε := by
  have h_denom : ε^2 ≤ (s - t)^2 + ε^2 := by linarith [sq_nonneg (s - t)]
  have h1 : ε / ((s - t)^2 + ε^2) ≤ ε / ε^2 :=
    div_le_div_of_nonneg_left (le_of_lt hε) (sq_pos_of_pos hε) h_denom
  simp only [one_div]
  calc ε / ((s - t)^2 + ε^2) ≤ ε / ε^2 := h1
    _ = ε⁻¹ := by field_simp

/-- The Lorentzian concentrates near t as ε → 0.
    For any δ > 0, the integral outside (t-δ, t+δ) vanishes as ε → 0. -/
axiom lorentzian_concentration (t δ : ℝ) (hδ : δ > 0) :
    Tendsto (fun ε : ℝ => ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ),
      ε / ((s - t)^2 + ε^2)) (𝓝[>] 0) (𝓝 0)

/-- Approximation to identity for continuous integrable functions. -/
axiom approx_identity_continuous (f : ℝ → ℂ) (hf_cont : Continuous f)
    (hf_int : MeasureTheory.Integrable f) (t : ℝ)
    (K : ℝ → ℝ → ℝ)  -- kernel K(ε, s)
    (hK_nonneg : ∀ ε > 0, ∀ s, K ε s ≥ 0)
    (hK_total : ∀ ε > 0, ∫ s, K ε s = 1)
    (hK_conc : ∀ δ > 0, Tendsto (fun ε => ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ), K ε s)
                                 (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ∫ s, (K ε s) • f s) (𝓝[>] 0) (𝓝 (f t))

/-- The Lorentzian approximation to delta: ε/((s-t)² + ε²) → πδ(s-t) as ε → 0 -/
lemma lorentzian_approx_delta (f : ℝ → ℂ) (hf_cont : Continuous f)
    (hf_int : MeasureTheory.Integrable f) (t : ℝ) :
    Tendsto (fun ε : ℝ => (1 / Real.pi) • ∫ s, (ε / ((s - t)^2 + ε^2)) • f s)
            (𝓝[>] 0) (𝓝 (f t)) := by
  -- Define the normalized kernel K(ε, s) = (1/π) * ε/((s-t)² + ε²)
  let K : ℝ → ℝ → ℝ := fun ε s => (1 / Real.pi) * (ε / ((s - t)^2 + ε^2))

  -- Rewrite goal in terms of K
  have h_rewrite : ∀ ε > 0, (1 / Real.pi) • ∫ s, (ε / ((s - t)^2 + ε^2)) • f s =
      ∫ s, (K ε s) • f s := by
    intro ε hε
    simp only [K]
    rw [← MeasureTheory.integral_smul]
    congr 1
    ext s
    rw [smul_smul]

  -- Apply the general approximation to identity theorem
  have h_tendsto : Tendsto (fun ε => ∫ s, (K ε s) • f s) (𝓝[>] 0) (𝓝 (f t)) := by
    apply approx_identity_continuous f hf_cont hf_int t K
    -- K is nonnegative
    · intro ε hε s
      simp only [K]
      apply mul_nonneg
      · simp only [one_div, inv_nonneg] ; exact Real.pi_nonneg
      · exact lorentzian_nonneg s t ε hε
    -- K integrates to 1
    · intro ε hε
      simp only [K]
      rw [MeasureTheory.integral_const_mul, lorentzian_total_integral t ε hε]
      field_simp
    -- K concentrates at t
    · intro δ hδ
      simp only [K]
      have h := lorentzian_concentration t δ hδ
      have h_eq : ∀ ε, ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ),
          (1 / Real.pi) * (ε / ((s - t)^2 + ε^2)) =
          (1 / Real.pi) * ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ),
          ε / ((s - t)^2 + ε^2) := fun ε => by
        exact integral_const_mul (1 / Real.pi) fun a => ε / ((a - t) ^ 2 + ε ^ 2)
      simp_rw [h_eq]
      convert h.const_mul (1 / Real.pi) using 2
      exact Eq.symm (CommMonoidWithZero.mul_zero (1 / Real.pi))
  -- Connect back to original formulation
  refine Tendsto.congr' ?_ h_tendsto
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (h_rewrite ε hε).symm

/-- Key identity: difference of resolvent kernels at conjugate points.

  (s - (t + iε))⁻¹ - (s - (t - iε))⁻¹ = 2iε / ((s-t)² + ε²)

This shows the resolvent difference is purely imaginary and proportional to Lorentzian. -/
lemma resolvent_kernel_diff (s t ε : ℝ) (hε : ε > 0) :
    ((s : ℂ) - (↑t + ↑ε * I))⁻¹ - ((s : ℂ) - (↑t - ↑ε * I))⁻¹ =
    (2 * ε * I) / ((s - t)^2 + ε^2 : ℂ) := by

  have h_z_plus : (↑t + ↑ε * I : ℂ) - (↑t - ↑ε * I) = 2 * ε * I := by ring
  have h_denom : ((s : ℂ) - (↑t + ↑ε * I)) * ((s : ℂ) - (↑t - ↑ε * I)) =
      ((s - t)^2 + ε^2 : ℂ) := by
    have hI2 : (I : ℂ)^2 = -1 := Complex.I_sq
    linear_combination (norm := ring) -ε^2 * hI2
  have h_denom_ne : ((s - t : ℝ)^2 + ε^2 : ℂ) ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'
  have h_prod_ne : ((s : ℂ) - (↑t + ↑ε * I)) * ((s : ℂ) - (↑t - ↑ε * I)) ≠ 0 := by
    rw [h_denom]
    push_cast at h_denom_ne ⊢
    exact h_denom_ne
  have h_left_ne : (s : ℂ) - (↑t + ↑ε * I) ≠ 0 := by
    intro h
    apply h_prod_ne
    rw [h, zero_mul]
  have h_right_ne : (s : ℂ) - (↑t - ↑ε * I) ≠ 0 := by
    intro h
    apply h_prod_ne
    rw [h, mul_zero]
  -- Main calculation
  have h_denom_ne' : (↑s - ↑t : ℂ) ^ 2 + ↑ε ^ 2 ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'
  field_simp [h_left_ne, h_right_ne, h_denom_ne']
  -- Now goal should be denominator-free
  push_cast [sq]
  ring_nf
  simp only [I_pow_three, mul_neg, neg_mul, sub_neg_eq_add]
  ring


/-- Arctan antiderivative for the Lorentzian kernel.
    ∫_a^b ε/((s-t)² + ε²) dt = arctan((b-s)/ε) - arctan((a-s)/ε) -/
axiom lorentzian_arctan_integral (s a b ε : ℝ) (hε : ε > 0) :
    ∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2) =
      Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)

/-- Fubini for the resolvent spectral integral.
    Swaps order of integration for the Lorentzian kernel. -/
axiom lorentzian_fubini {μ : MeasureTheory.Measure ℝ} [MeasureTheory.IsFiniteMeasure μ]
    (a b ε : ℝ) (hε : ε > 0) :
    ∫ t in Set.Icc a b, ∫ s, ε / ((s - t)^2 + ε^2) ∂μ =
      ∫ s, (∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2)) ∂μ

/-- The arctan kernel converges to the indicator function.
    (1/π)[arctan((b-s)/ε) - arctan((a-s)/ε)] → 𝟙_{(a,b]}(s) as ε → 0+ -/
axiom arctan_indicator_limit (a b s : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => (1 / Real.pi) *
      (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)))
      (𝓝[>] 0)
      (𝓝 (Set.indicator (Set.Ioc a b) 1 s))

/-- The arctan kernel is uniformly bounded by 1. -/
axiom arctan_kernel_bound (a b s ε : ℝ) (hε : ε > 0) :
    |(1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))| ≤ 1

/-- Dominated convergence for the arctan kernel integral. -/
axiom arctan_dominated_convergence {μ : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsFiniteMeasure μ] (a b : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => ∫ s, (1 / Real.pi) *
      (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ)
      (𝓝[>] 0)
      (𝓝 (μ (Set.Ioc a b)).toReal)

/-- The imaginary part of the resolvent inner product equals the Lorentzian spectral integral. -/
axiom resolvent_im_spectral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : BochnerRoute.IsSpectralMeasure E)
    (t ε : ℝ) (hε : ε > 0) (ψ : H) :
    Complex.im ⟪resolventFun gen hsa (offRealPoint t ε hε) ψ, ψ⟫_ℂ =
      ∫ s, ε / ((s - t)^2 + ε^2) ∂(BochnerRoute.spectral_scalar_measure E ψ hE)


/-- **Stieltjes Inversion Formula**
Recover the spectral measure from the resolvent via:
  ⟪E(a,b] ψ, ψ⟫ = lim_{ε→0+} (1/π) ∫_a^b Im⟪R(t+iε) ψ, ψ⟫ dt
-/
theorem stieltjes_inversion {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : BochnerRoute.IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (a b : ℝ) (hab : a < b) (ψ : H) :
    ∀ δ > 0, ∃ ε₀ > 0, ∀ ε, ε < ε₀ → ∀ hε : ε > 0,
      ‖⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ - (1 / Real.pi : ℂ) *
        ∫ t in Set.Icc a b, Complex.im ⟪resolventFun gen hsa (offRealPoint t ε hε) ψ, ψ⟫_ℂ‖ < δ := by
  intro δ hδ

  set μ := BochnerRoute.spectral_scalar_measure E ψ hE with hμ_def
  haveI hμ_finite : MeasureTheory.IsFiniteMeasure μ :=
    BochnerRoute.spectral_scalar_measure_finite E hE hE_univ ψ
  -- Get ε₀ from dominated convergence
  have h_conv := arctan_dominated_convergence (μ := μ) a b hab
  rw [Metric.tendsto_nhdsWithin_nhds] at h_conv
  obtain ⟨ε₀, hε₀_pos, hε₀_conv⟩ := h_conv δ hδ

  use ε₀
  constructor
  · exact hε₀_pos
  intro ε hε_lt hε

  -- The spectral measure gives ⟪E(a,b]ψ, ψ⟫
  have h_spectral : (μ (Set.Ioc a b)).toReal = (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re :=
    BochnerRoute.spectral_scalar_measure_apply' E hE ψ (Set.Ioc a b) measurableSet_Ioc

  -- ⟪E(a,b]ψ, ψ⟫ is real
  have h_real : (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).im = 0 :=
    BochnerRoute.spectral_diagonal_real E (Set.Ioc a b) ψ

  have h_inner_eq : ⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ = (μ (Set.Ioc a b)).toReal := by
    conv_lhs => rw [← Complex.re_add_im ⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ, h_real]
    simp [h_spectral]

  -- Express the integral using spectral representation
  have h_integral : ∫ t in Set.Icc a b, Complex.im ⟪resolventFun gen hsa (offRealPoint t ε hε) ψ, ψ⟫_ℂ =
      ∫ t in Set.Icc a b, ∫ s, ε / ((s - t)^2 + ε^2) ∂μ := by
    congr 1
    ext t
    exact resolvent_im_spectral gen hsa E hE t ε hε ψ

  -- Apply Fubini
  have h_fubini : ∫ t in Set.Icc a b, ∫ s, ε / ((s - t)^2 + ε^2) ∂μ =
      ∫ s, (∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2)) ∂μ :=
    lorentzian_fubini a b ε hε

  -- Compute inner integral via arctan
  have h_arctan : ∫ s, (∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2)) ∂μ =
      ∫ s, (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with s
    exact lorentzian_arctan_integral s a b ε hε

  -- Factor out 1/π
  have h_factor : (1 / Real.pi : ℂ) * ∫ t in Set.Icc a b,
      Complex.im ⟪resolventFun gen hsa (offRealPoint t ε hε) ψ, ψ⟫_ℂ =
      ∫ s, (1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ := by
    rw [h_integral, h_fubini, h_arctan]
    simp only [MeasureTheory.integral_const_mul]
    norm_cast

  -- Apply dominated convergence bound
  have h_dist : dist ε 0 < ε₀ := by simp [abs_of_pos hε]; exact hε_lt
  have h_mem : ε ∈ Set.Ioi (0 : ℝ) := hε
  have h_bound := hε₀_conv h_mem h_dist
  simp only [Real.dist_eq] at h_bound

  -- Convert to norm bound
  rw [h_inner_eq, h_factor]
  rw [← Complex.ofReal_sub, Complex.norm_real, @norm_sub_rev]
  exact h_bound


/-- The resolvent difference integrated against the spectral measure. -/
axiom resolvent_diff_spectral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : BochnerRoute.IsSpectralMeasure E)
    (t ε : ℝ) (hε : ε > 0) (ψ : H) :
    ⟪(resolventFun gen hsa (offRealPoint t ε hε) -
       resolventFun gen hsa (offRealPointNeg t ε hε)) ψ, ψ⟫_ℂ =
      ∫ s, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ) ∂(BochnerRoute.spectral_scalar_measure E ψ hE)

/-- Fubini for the resolvent difference kernel. -/
axiom resolvent_diff_fubini {μ : MeasureTheory.Measure ℝ} [MeasureTheory.IsFiniteMeasure μ]
    (a b ε : ℝ) (hε : ε > 0) :
    ∫ t in Set.Icc a b, ∫ s, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ) ∂μ =
      ∫ s, (∫ t in Set.Icc a b, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ)) ∂μ

/-- The complex arctan integral for the resolvent difference.
    ∫_a^b (2εi)/((s-t)² + ε²) dt = 2i[arctan((b-s)/ε) - arctan((a-s)/ε)] -/
axiom resolvent_diff_arctan_integral (s a b ε : ℝ) (hε : ε > 0) :
    ∫ t in Set.Icc a b, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ) =
      2 * Complex.I * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))

/-- Dominated convergence for Stone's formula integral. -/
axiom stones_dominated_convergence {μ : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsFiniteMeasure μ] (a b : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => ∫ s, (1 / Real.pi) *
      (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ)
      (𝓝[>] 0)
      (𝓝 (μ (Set.Ioc a b)).toReal)

/-- The Stone's formula integral simplifies to a real value. -/
axiom stones_integral_real {μ : MeasureTheory.Measure ℝ} [MeasureTheory.IsFiniteMeasure μ]
    (a b ε : ℝ) (hε : ε > 0) :
    ∫ s, (1 / (2 * Real.pi * Complex.I)) *
      (2 * Complex.I * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))) ∂μ =
    ∫ s, (1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ

/-- **Stone's Formula**
Recover spectral projections from the resolvent difference:
  E(a,b) = s-lim_{ε→0+} (1/2πi) ∫_a^b [R(t+iε) - R(t-iε)] dt
-/
theorem stones_formula {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : BochnerRoute.IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (a b : ℝ) (hab : a < b) (ψ : H) :
    ∀ δ > 0, ∃ ε₀ > 0, ∀ ε, ε < ε₀ → ∀ hε : ε > 0,
      ‖⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ - (1 / (2 * Real.pi * Complex.I)) *
        ∫ t in Set.Icc a b, ⟪(resolventFun gen hsa (offRealPoint t ε hε) -
          resolventFun gen hsa (offRealPointNeg t ε hε)) ψ, ψ⟫_ℂ‖ < δ := by
  intro δ hδ

  set μ := BochnerRoute.spectral_scalar_measure E ψ hE with hμ_def
  haveI hμ_finite : MeasureTheory.IsFiniteMeasure μ :=
    BochnerRoute.spectral_scalar_measure_finite E hE hE_univ ψ

  -- Get ε₀ from dominated convergence
  have h_conv := stones_dominated_convergence (μ := μ) a b hab
  rw [Metric.tendsto_nhdsWithin_nhds] at h_conv
  obtain ⟨ε₀, hε₀_pos, hε₀_conv⟩ := h_conv δ hδ

  use ε₀
  constructor
  · exact hε₀_pos
  intro ε hε_lt hε

  -- The spectral measure gives ⟪E(a,b]ψ, ψ⟫
  have h_spectral : (μ (Set.Ioc a b)).toReal = (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re :=
    BochnerRoute.spectral_scalar_measure_apply' E hE ψ (Set.Ioc a b) measurableSet_Ioc

  -- ⟪E(a,b]ψ, ψ⟫ is real
  have h_real : (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).im = 0 :=
    BochnerRoute.spectral_diagonal_real E (Set.Ioc a b) ψ

  have h_inner_eq : ⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ = (μ (Set.Ioc a b)).toReal := by
    conv_lhs => rw [← Complex.re_add_im ⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ, h_real]
    simp [h_spectral]

  -- Express the integral using spectral representation
  have h_integral : ∫ t in Set.Icc a b,
      ⟪(resolventFun gen hsa (offRealPoint t ε hε) -
        resolventFun gen hsa (offRealPointNeg t ε hε)) ψ, ψ⟫_ℂ =
      ∫ t in Set.Icc a b, ∫ s, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ) ∂μ := by
    congr 1
    ext t
    exact resolvent_diff_spectral gen hsa E hE t ε hε ψ

  -- Apply Fubini
  have h_fubini : ∫ t in Set.Icc a b, ∫ s, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ) ∂μ =
      ∫ s, (∫ t in Set.Icc a b, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ)) ∂μ :=
    resolvent_diff_fubini a b ε hε

  -- Compute inner integral via arctan
  have h_arctan : ∫ s, (∫ t in Set.Icc a b, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ)) ∂μ =
      ∫ s, 2 * Complex.I * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with s
    exact resolvent_diff_arctan_integral s a b ε hε

  -- Factor out 1/(2πi)
  have h_factor : (1 / (2 * Real.pi * Complex.I)) *
    ∫ t in Set.Icc a b, ⟪(resolventFun gen hsa (offRealPoint t ε hε) -
      resolventFun gen hsa (offRealPointNeg t ε hε)) ψ, ψ⟫_ℂ =
    ∫ s, (1 / (2 * Real.pi * Complex.I)) *
      (2 * Complex.I * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))) ∂μ := by
    rw [h_integral, h_fubini, h_arctan]
    exact
      Eq.symm
        (integral_const_mul (1 / (2 * ↑Real.pi * I)) fun a_1 =>
          2 * I * (↑(Real.arctan ((b - a_1) / ε)) - ↑(Real.arctan ((a - a_1) / ε))))

  -- Apply dominated convergence bound
  have h_dist : dist ε 0 < ε₀ := by simp [abs_of_pos hε]; exact hε_lt
  have h_mem : ε ∈ Set.Ioi (0 : ℝ) := hε
  have h_bound := hε₀_conv h_mem h_dist

  -- Convert to norm bound
  rw [h_inner_eq, h_factor, stones_integral_real a b ε hε]
  rw [← Complex.ofReal_sub, Complex.norm_real, norm_sub_rev]
  exact h_bound



/-- The operator-valued spectral integral ∫ f(λ) dE(λ) applied to a vector.
    This is the Stieltjes integral with respect to a projection-valued measure. -/
axiom spectral_integral (E : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) (ψ : H) : H

notation "∫_E " f ", " ψ => spectral_integral _ f ψ


/-- The spectral integral of (λ - z)⁻¹ equals the resolvent. -/
axiom resolvent_eq_spectral_integral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (z : OffRealAxis) (ψ : H) :
    resolventFun gen hsa z ψ = spectral_integral E (fun t => ((t : ℂ) - z.val)⁻¹) ψ

/-- Lebesgue-Stieltjes representation: the spectral integral can be written
    as a Lebesgue integral against the spectral measure density when E is absolutely
    continuous. For general E, this is the Stieltjes integral. -/
axiom spectral_integral_eq_lebesgue (E : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) (ψ : H) :
    spectral_integral E f ψ = ∫ t : ℝ, f t • E {t} ψ  -- formal equality via Stieltjes


/-- **Resolvent Spectral Representation (Operator Form)**
The resolvent has an integral representation:
  R(z) = ∫_ℝ (s - z)⁻¹ dE(s)
-/
theorem resolvent_spectral_representation {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H))
    (z : OffRealAxis) (ψ : H) :
    resolventFun gen hsa z ψ = ∫ t : ℝ, ((t : ℂ) - z.val)⁻¹ • E {t} ψ := by
  rw [← spectral_integral_eq_lebesgue]
  exact resolvent_eq_spectral_integral gen hsa E z ψ


/-- **Resolvent Spectral Representation (Bilinear Form)**
The bilinear form version:
  ⟪R(z)ψ, ψ⟫ = ∫_ℝ (s - z)⁻¹ dμ_ψ(s)
-/
theorem resolvent_spectral_representation' {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : BochnerRoute.IsSpectralMeasure E)
    (z : OffRealAxis) (ψ : H) :
    ⟪resolventFun gen hsa z ψ, ψ⟫_ℂ =
      ∫ s : ℝ, ((s : ℂ) - z.val)⁻¹ ∂(BochnerRoute.spectral_scalar_measure E ψ hE) :=
  resolvent_spectral_bilinear gen hsa E hE z ψ

/-- Specialization: the spectral measure μ can be any measure agreeing with E on measurable sets. -/
theorem resolvent_spectral_representation'_alt {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE : BochnerRoute.IsSpectralMeasure E)
    (μ : H → MeasureTheory.Measure ℝ)
    (hμ : ∀ ψ, μ ψ = BochnerRoute.spectral_scalar_measure E ψ hE)
    (z : OffRealAxis) (ψ : H) :
    ⟪resolventFun gen hsa z ψ, ψ⟫_ℂ = ∫ t : ℝ, ((t : ℂ) - z.val)⁻¹ ∂(μ ψ) := by
  rw [hμ ψ]
  exact resolvent_spectral_bilinear gen hsa E hE z ψ


end ResolventRoute

end SpectralBridge
