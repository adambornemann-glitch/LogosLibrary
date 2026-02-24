/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.PositiveDefinite
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.SpectralMeasure

/-!
# Connecting Unitary Groups to Spectral Measures

This file establishes the connection between strongly continuous one-parameter
unitary groups and projection-valued spectral measures via Bochner's theorem.

Given a unitary group `U(t)` with self-adjoint generator `A`, we show that the
correlation function `t ↦ ⟨U(t)ψ, ψ⟩` is positive-definite and continuous,
hence by Bochner's theorem is the Fourier transform of a measure. This measure
equals the spectral scalar measure `μ_ψ(B) = ⟨E(B)ψ, ψ⟩`.

## Main definitions

* `IsSpectralMeasureFor`: A spectral measure `E` associated to a unitary group `U`
* `bochner_measure`: The measure obtained from Bochner's theorem applied to `⟨U(t)ψ, ψ⟩`
* `spectral_measure_cplx`: Complex-valued version of the spectral measure for polarization

## Main statements

* `unitary_correlation_positive_definite`: `t ↦ ⟨U(t)ψ, ψ⟩` is positive-definite
* `unitary_correlation_continuous`: `t ↦ ⟨U(t)ψ, ψ⟩` is continuous
* `unitary_correlation_pd_continuous`: Combined, satisfies Bochner's hypotheses
* `bochner_measure_eq_spectral`: The Bochner measure equals the spectral scalar measure
* `polarization_spectral`: Off-diagonal terms `⟨E(B)ψ, φ⟩` recovered via polarization

## Proof strategy

1. Show `⟨U(t)ψ, ψ⟩` is positive-definite using `⟨U(s-r)ψ, ψ⟩ = ⟨U(s)ψ, U(r)ψ⟩`
2. Apply Bochner's theorem to get a measure `μ_ψ` with `⟨U(t)ψ, ψ⟩ = ∫ e^{itλ} dμ_ψ`
3. Show uniqueness: the Bochner measure equals the spectral scalar measure
4. Recover operator-valued `E(B)` via polarization from scalar measures

## Physical interpretation

This establishes that spectral measures are the "Fourier dual" of time evolution.
The correlation function `⟨U(t)ψ, ψ⟩` encodes the same information as the spectral
distribution `⟨E(λ)ψ, ψ⟩`, related by Fourier transform.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Sections VII-VIII
* Bochner, "Monotone Funktionen, Stieltjessche Integrale und harmonische Analyse" (1933)

## Tags

spectral measure, Bochner theorem, unitary group, positive-definite, polarization
-/

namespace SpectralBridge.Bochner

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]


/-! ### The bridge: spectral measure FOR a unitary group -/

/-- `E` is the spectral measure associated to the unitary group `U_grp`.

This means E satisfies the spectral measure axioms AND the Fourier transform
of the spectral scalar measure gives the unitary correlation function:
`⟨U(t)ψ, ψ⟩ = ∫ e^{itλ} dμ_ψ(λ)` -/
structure IsSpectralMeasureFor (E : Set ℝ → H →L[ℂ] H)
    (U_grp : OneParameterUnitaryGroup (H := H)) : Prop extends IsSpectralMeasure E where
  spectral_representation : ∀ ψ t,
    ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ ω, exp (I * ω * t) ∂(spectral_scalar_measure E ψ toIsSpectralMeasure)

/-! ### Unitary correlation functions are positive-definite -/

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The function t ↦ ⟨U(t)ψ, ψ⟩ is positive-definite.

This is the key insight: unitarity implies `⟨U(s-r)ψ, ψ⟩ = ⟨U(s)ψ, U(r)ψ⟩`,
so the quadratic form becomes `‖∑ᵢ cᵢU(tᵢ)ψ‖² ≥ 0`. -/
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

/-- The correlation function t ↦ ⟨U(t)ψ, ψ⟩ is continuous. -/
theorem unitary_correlation_continuous (ψ : H) :
    Continuous (fun t => ⟪U_grp.U t ψ, ψ⟫_ℂ) := by
  apply Continuous.inner
  · exact U_grp.strong_continuous ψ
  · exact continuous_const

/-- Combined: the correlation function satisfies Bochner's hypotheses. -/
theorem unitary_correlation_pd_continuous (ψ : H) :
    PositiveDefiniteContinuous (fun t => ⟪U_grp.U t ψ, ψ⟫_ℂ) := by
  constructor
  · exact unitary_correlation_positive_definite U_grp ψ
  · exact (unitary_correlation_continuous U_grp ψ).continuousAt

/-! ### The Bochner measure -/

/-- The measure obtained from Bochner's theorem applied to the unitary correlation function. -/
noncomputable def bochner_measure (ψ : H) : Measure ℝ :=
  Classical.choose (bochner_theorem (fun t => ⟪U_grp.U t ψ, ψ⟫_ℂ)
    (unitary_correlation_pd_continuous U_grp ψ))

/-- Properties of the Bochner measure: finite and Fourier representation. -/
lemma bochner_measure_spec (ψ : H) :
    IsFiniteMeasure (bochner_measure U_grp ψ) ∧
    ∀ t, ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ ω, exp (I * ω * t) ∂(bochner_measure U_grp ψ) :=
  Classical.choose_spec (bochner_theorem (fun t => ⟪U_grp.U t ψ, ψ⟫_ℂ)
    (unitary_correlation_pd_continuous U_grp ψ))

/-! ### The Bochner measure equals the spectral measure -/

/-- **Main theorem**: The Bochner measure equals the spectral scalar measure.

This shows that the measure obtained from Bochner's theorem is exactly the
spectral scalar measure `μ_ψ(B) = ⟨E(B)ψ, ψ⟩`. The proof uses uniqueness
of measures determined by their Fourier transforms. -/
theorem bochner_measure_eq_spectral (hE : IsSpectralMeasureFor E U_grp) (hE_univ : E Set.univ = 1)
    (ψ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    (bochner_measure U_grp ψ B).toReal = (⟪E B ψ, ψ⟫_ℂ).re := by
  obtain ⟨h_finite, h_fourier⟩ := bochner_measure_spec U_grp ψ

  haveI : IsFiniteMeasure (bochner_measure U_grp ψ) := h_finite
  haveI : IsFiniteMeasure (spectral_scalar_measure E ψ hE.toIsSpectralMeasure) :=
    spectral_scalar_measure_finite E hE.toIsSpectralMeasure hE_univ ψ

  have h_fourier_eq : ∀ t : ℝ,
      ∫ ω, exp (I * ω * t) ∂(bochner_measure U_grp ψ) =
      ∫ ω, exp (I * ω * t) ∂(spectral_scalar_measure E ψ hE.toIsSpectralMeasure) := fun t => by
    rw [← h_fourier t, hE.spectral_representation ψ t]

  have h_eq : bochner_measure U_grp ψ = spectral_scalar_measure E ψ hE.toIsSpectralMeasure :=
    measure_eq_of_fourier_eq _ _ h_fourier_eq

  rw [h_eq, spectral_scalar_measure_apply' E hE.toIsSpectralMeasure ψ B hB]

/-! ### Polarization identity for off-diagonal spectral measures -/

/-- Complex-valued version of the spectral measure for polarization calculations. -/
noncomputable def spectral_measure_cplx
    (U_grp : OneParameterUnitaryGroup (H := H)) (ψ : H) (B : Set ℝ) : ℂ :=
  ((bochner_measure U_grp ψ B).toReal : ℂ)

/-- The complex spectral measure equals `⟨E(B)ψ, ψ⟩`. -/
lemma spectral_measure_cplx_eq (hE : IsSpectralMeasureFor E U_grp) (hE_univ : E Set.univ = 1)
    (ψ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    spectral_measure_cplx U_grp ψ B = ⟪E B ψ, ψ⟫_ℂ := by
  unfold spectral_measure_cplx
  rw [bochner_measure_eq_spectral U_grp hE hE_univ ψ B hB]
  have h_im := spectral_diagonal_real hE.toIsSpectralMeasure B ψ
  conv_rhs => rw [← Complex.re_add_im ⟪E B ψ, ψ⟫_ℂ, h_im]
  simp


/-- **Polarization identity**: Off-diagonal spectral measures recovered from diagonal ones. -/
theorem polarization_spectral (hE : IsSpectralMeasureFor E U_grp) (hE_univ : E Set.univ = 1)
    (ψ φ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    ⟪E B ψ, φ⟫_ℂ = (1/4 : ℂ) * (
      spectral_measure_cplx U_grp (ψ + φ) B -
      spectral_measure_cplx U_grp (ψ - φ) B -
      I * spectral_measure_cplx U_grp (ψ + I • φ) B +
      I * spectral_measure_cplx U_grp (ψ - I • φ) B) := by
  -- Step 1: Explicitly convert each spectral_measure_cplx to inner product
  have eq1 : spectral_measure_cplx U_grp (ψ + φ) B = ⟪E B (ψ + φ), ψ + φ⟫_ℂ :=
    spectral_measure_cplx_eq U_grp hE hE_univ (ψ + φ) B hB
  have eq2 : spectral_measure_cplx U_grp (ψ - φ) B = ⟪E B (ψ - φ), ψ - φ⟫_ℂ :=
    spectral_measure_cplx_eq U_grp hE hE_univ (ψ - φ) B hB
  have eq3 : spectral_measure_cplx U_grp (ψ + I • φ) B = ⟪E B (ψ + I • φ), ψ + I • φ⟫_ℂ :=
    spectral_measure_cplx_eq U_grp hE hE_univ (ψ + I • φ) B hB
  have eq4 : spectral_measure_cplx U_grp (ψ - I • φ) B = ⟪E B (ψ - I • φ), ψ - I • φ⟫_ℂ :=
    spectral_measure_cplx_eq U_grp hE hE_univ (ψ - I • φ) B hB
  rw [eq1, eq2, eq3, eq4]
  -- Step 2: Expand E B (ψ ± φ) using linearity
  simp only [map_add, map_sub, map_smul]
  -- Step 3: Expand all inner products
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
             inner_smul_left, inner_smul_right]
  -- Step 4: Use self-adjointness to replace ⟨E B φ, ψ⟩ with conj(⟨E B ψ, φ⟩)
  have h_sa : ⟪E B φ, ψ⟫_ℂ = starRingEnd ℂ ⟪E B ψ, φ⟫_ℂ := by
    rw [hE.toIsSpectralMeasure.sa B φ ψ, inner_conj_symm]
  rw [h_sa]
  -- Step 5: Set z = ⟨E B ψ, φ⟩ and compute
  set z := ⟪E B ψ, φ⟫_ℂ with hz
  -- The RHS simplifies to z by the polarization identity
  -- After expansion: (1/4) * (4z) = z
  -- We need to handle conj(z) = starRingEnd ℂ z
  apply Complex.ext
    <;> simp only [one_div, conj_I, neg_mul, sub_neg_eq_add, mul_re, inv_re,
      re_ofNat, normSq_ofNat, div_self_mul_self', add_re, sub_re, conj_re, I_re, neg_re, zero_mul,
      I_im, conj_im, mul_neg, one_mul, zero_add, zero_sub, neg_neg, add_im, neg_im, mul_im,
      neg_add_rev, neg_zero, sub_im, neg_sub, inv_im, im_ofNat, zero_div, sub_zero]
    <;> ring



end SpectralBridge.Bochner
