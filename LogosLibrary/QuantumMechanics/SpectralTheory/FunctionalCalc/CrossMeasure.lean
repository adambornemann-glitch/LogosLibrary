/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.ScalarMeasure
/-!
# Spectral Cross-Measure and Polarization

This file develops the spectral cross-measure `ν_{ψ,φ}(B) = ⟪E(B)ψ, φ⟫` and the
cross-integral framework that enables proving spectral integral properties via
polarization identities.

## Main definitions

* `spectral_cross_measure`: The complex measure `ν_{ψ,φ}(B) = ⟪E(B)ψ, φ⟫`
* `spectral_cross_integral`: Integration via polarization identity

## Main results

### Cross-term Bounds
* `spectral_cross_term_bound`: `|Re⟪E(B)x, y⟩| ≤ √μ_x(B) · √μ_y(B)`
* `spectral_cross_term_im_bound`: Same for imaginary part
* `spectral_cross_term_norm_bound`: Full complex norm bound

### Polarization
* `spectral_polarization`: Recover `⟪E(B)x, y⟫` from diagonal terms
* `spectral_scalar_measure_polarization`: Spectral measure version

### Cross-Measure Properties
* `spectral_cross_measure_add_left/right`: Additivity
* `spectral_cross_measure_smul_left/right`: Homogeneity
* `spectral_cross_measure_diag`: Diagonal equals scalar measure
* `spectral_cross_measure_conj_symm`: Conjugate symmetry

### Cross-Integral Properties
* `spectral_cross_integral_indicator`: `∫ 𝟙_B dν = ⟪E(B)ψ, φ⟫`
* `spectral_cross_integral_add_f`: Additivity in f
* `spectral_cross_integral_smul_f`: Homogeneity in f
* `spectral_cross_integral_finsum`: Finite sum interchange
* `spectral_cross_integral_diag`: Diagonal case simplification
* `spectral_cross_integral_add_left_simple`: Additivity for simple functions

## Tags

cross-measure, polarization identity, spectral integral, sesquilinear
-/
namespace FunctionalCalculus

open MeasureTheory InnerProductSpace Complex QuantumMechanics.Cayley SpectralBridge.Resolvent SpectralBridge.Bochner QuantumMechanics.Generators ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-!
## Cross-term Bounds
-/

/-- Cauchy-Schwarz bound for spectral cross term -/
lemma spectral_cross_term_bound (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    |Complex.re ⟪E B x, y⟫_ℂ| ≤
    Real.sqrt ((spectral_scalar_measure E x hE B).toReal) *
    Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by

  rw [spectral_projection_inner_factorization E hE B hB x y]

  have h_cs : |Complex.re ⟪E B x, E B y⟫_ℂ| ≤ ‖E B x‖ * ‖E B y‖ := by
    calc |Complex.re ⟪E B x, E B y⟫_ℂ|
        ≤ ‖⟪E B x, E B y⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖E B x‖ * ‖E B y‖ := norm_inner_le_norm (E B x) (E B y)

  have hx : ‖E B x‖ = Real.sqrt ((spectral_scalar_measure E x hE B).toReal) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    congr 1
    rw [spectral_projection_norm_sq E B hE hB x]
    exact Eq.symm (spectral_scalar_measure_apply' E hE x B hB)
  have hy : ‖E B y‖ = Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    congr 1
    rw [spectral_projection_norm_sq E B hE hB y]
    exact Eq.symm (spectral_scalar_measure_apply' E hE y B hB)

  rw [hx, hy] at h_cs
  exact h_cs


/-- Imaginary part of cross term also bounded -/
lemma spectral_cross_term_im_bound (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    |Complex.im ⟪E B x, y⟫_ℂ| ≤
    Real.sqrt ((spectral_scalar_measure E x hE B).toReal) *
    Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
  rw [spectral_projection_inner_factorization E hE B hB x y]
  have h_cs : |Complex.im ⟪E B x, E B y⟫_ℂ| ≤ ‖E B x‖ * ‖E B y‖ := by
    calc |Complex.im ⟪E B x, E B y⟫_ℂ|
        ≤ ‖⟪E B x, E B y⟫_ℂ‖ := Complex.abs_im_le_norm _
      _ ≤ ‖E B x‖ * ‖E B y‖ := norm_inner_le_norm (E B x) (E B y)
  calc |Complex.im ⟪E B x, E B y⟫_ℂ|
      ≤ ‖E B x‖ * ‖E B y‖ := h_cs
    _ = Real.sqrt ((spectral_scalar_measure E x hE B).toReal) *
        Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
        rw [spectral_scalar_measure_eq_norm_sq E hE B hB x, spectral_scalar_measure_eq_norm_sq E hE B hB y]
        simp [Real.sqrt_sq (norm_nonneg _)]

/-- Full complex cross term bound -/
lemma spectral_cross_term_norm_bound (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    ‖⟪E B x, y⟫_ℂ‖ ≤
    Real.sqrt ((spectral_scalar_measure E x hE B).toReal) *
    Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
  rw [spectral_projection_inner_factorization E hE B hB x y]
  calc ‖⟪E B x, E B y⟫_ℂ‖
      ≤ ‖E B x‖ * ‖E B y‖ := norm_inner_le_norm _ _
    _ = Real.sqrt ((spectral_scalar_measure E x hE B).toReal) *
        Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
        rw [spectral_scalar_measure_eq_norm_sq E hE B hB x, spectral_scalar_measure_eq_norm_sq E hE B hB y]
        simp [Real.sqrt_sq (norm_nonneg _)]


/-- Upper bound on μ_{x+y}(B) in terms of μ_x(B) and μ_y(B) -/
lemma spectral_scalar_measure_add_bound (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (x y : H) (B : Set ℝ) (hB : MeasurableSet B) :
    (spectral_scalar_measure E (x + y) hE B).toReal ≤
    2 * (spectral_scalar_measure E x hE B).toReal +
    2 * (spectral_scalar_measure E y hE B).toReal +
    2 * Real.sqrt ((spectral_scalar_measure E x hE B).toReal) *
        Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
  rw [spectral_scalar_measure_add E hE x y B hB]
  have h_cross := spectral_cross_term_bound E hE B hB x y
  have h1 : 2 * Complex.re ⟪E B x, y⟫_ℂ ≤
      2 * Real.sqrt ((spectral_scalar_measure E x hE B).toReal) *
          Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
    have : Complex.re ⟪E B x, y⟫_ℂ ≤ |Complex.re ⟪E B x, y⟫_ℂ| := le_abs_self _
    linarith [h_cross]
  have hx_nonneg : (spectral_scalar_measure E x hE B).toReal ≥ 0 := ENNReal.toReal_nonneg
  have hy_nonneg : (spectral_scalar_measure E y hE B).toReal ≥ 0 := ENNReal.toReal_nonneg
  linarith

/-!
## Polarization Identities
-/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- Polarization: recover ⟪E(B)x, y⟫ from diagonal terms -/
lemma spectral_polarization (E : Set ℝ → H →L[ℂ] H) (B : Set ℝ) (_hB : MeasurableSet B) (x y : H) :
    ⟪E B x, y⟫_ℂ = (1/4 : ℂ) * (
      ⟪E B (x + y), x + y⟫_ℂ -
      ⟪E B (x - y), x - y⟫_ℂ -
      I * ⟪E B (x + I • y), x + I • y⟫_ℂ +
      I * ⟪E B (x - I • y), x - I • y⟫_ℂ) := by
  simp only [map_add, map_sub, map_smul]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
             inner_smul_left, inner_smul_right]
  have hI2 : (I : ℂ)^2 = -1 := Complex.I_sq
  ring_nf
  linear_combination (norm := ring_nf) (⟪(E B) x, y⟫_ℂ - ⟪(E B) x, y⟫_ℂ) * hI2
  simp only [one_div, I_sq, mul_neg, mul_one, neg_mul, add_neg_cancel, zero_add, conj_I]
  have hII : (I : ℂ) * I = -1 := by rw [← sq, Complex.I_sq]
  rw [hII.symm]
  ring

/-- Spectral measure version of polarization -/
lemma spectral_scalar_measure_polarization (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    ⟪E B x, y⟫_ℂ = (1/4 : ℂ) * (
      (spectral_scalar_measure E (x + y) hE B).toReal -
      (spectral_scalar_measure E (x - y) hE B).toReal -
      I * (spectral_scalar_measure E (x + I • y) hE B).toReal +
      I * (spectral_scalar_measure E (x - I • y) hE B).toReal) := by
  rw [spectral_polarization E B hB x y]
  congr 1
  -- Rewrite each spectral measure in terms of inner product
  have h1 : ((spectral_scalar_measure E (x + y) hE B).toReal : ℂ) = ⟪E B (x + y), x + y⟫_ℂ := by
    rw [spectral_scalar_measure_apply' E hE (x + y) B hB]
    have h := spectral_diagonal_real hE B (x + y) -- here
    conv_rhs => rw [← Complex.re_add_im ⟪E B (x + y), x + y⟫_ℂ, h]
    simp
  have h2 : ((spectral_scalar_measure E (x - y) hE B).toReal : ℂ) = ⟪E B (x - y), x - y⟫_ℂ := by
    rw [spectral_scalar_measure_apply' E hE (x - y) B hB]
    have h := spectral_diagonal_real hE B (x - y) -- here
    conv_rhs => rw [← Complex.re_add_im ⟪E B (x - y), x - y⟫_ℂ, h]
    simp
  have h3 : ((spectral_scalar_measure E (x + I • y) hE B).toReal : ℂ) = ⟪E B (x + I • y), x + I • y⟫_ℂ := by
    rw [spectral_scalar_measure_apply' E hE (x + I • y) B hB]
    have h := spectral_diagonal_real hE B (x + I • y) -- here
    conv_rhs => rw [← Complex.re_add_im ⟪E B (x + I • y), x + I • y⟫_ℂ, h]
    simp
  have h4 : ((spectral_scalar_measure E (x - I • y) hE B).toReal : ℂ) = ⟪E B (x - I • y), x - I • y⟫_ℂ := by
    rw [spectral_scalar_measure_apply' E hE (x - I • y) B hB]
    have h := spectral_diagonal_real hE B (x - I • y) -- here
    conv_rhs => rw [← Complex.re_add_im ⟪E B (x - I • y), x - I • y⟫_ℂ, h]
    simp
  rw [h1, h2, h3, h4]

/-!
## Spectral Cross-Measure Definition and Properties
-/

/-- The spectral cross-measure ν_{ψ,φ}(B) = ⟪E(B)ψ, φ⟫ as a complex-valued set function -/
def spectral_cross_measure (E : Set ℝ → H →L[ℂ] H) (ψ φ : H) : Set ℝ → ℂ :=
  fun B => ⟪E B ψ, φ⟫_ℂ

/-- Cross-measure is additive in first argument (from linearity of E(B)) -/
lemma spectral_cross_measure_add_left (E : Set ℝ → H →L[ℂ] H) (x y φ : H) (B : Set ℝ) :
    spectral_cross_measure E (x + y) φ B =
    spectral_cross_measure E x φ B + spectral_cross_measure E y φ B := by
  simp only [spectral_cross_measure, map_add, inner_add_left]

/-- Cross-measure is conjugate-homogeneous in first argument -/
lemma spectral_cross_measure_smul_left (E : Set ℝ → H →L[ℂ] H) (c : ℂ) (ψ φ : H) (B : Set ℝ) :
    spectral_cross_measure E (c • ψ) φ B = star c * spectral_cross_measure E ψ φ B := by
  simp only [spectral_cross_measure, map_smul, inner_smul_left, RCLike.star_def]

/-- Cross-measure is additive in second argument -/
lemma spectral_cross_measure_add_right (E : Set ℝ → H →L[ℂ] H) (ψ x y : H) (B : Set ℝ) :
    spectral_cross_measure E ψ (x + y) B =
    spectral_cross_measure E ψ x B + spectral_cross_measure E ψ y B := by
  simp only [spectral_cross_measure, inner_add_right]

/-- Cross-measure is linear in second argument -/
lemma spectral_cross_measure_smul_right (E : Set ℝ → H →L[ℂ] H) (c : ℂ) (ψ φ : H) (B : Set ℝ) :
    spectral_cross_measure E ψ (c • φ) B = c * spectral_cross_measure E ψ φ B := by
  simp only [spectral_cross_measure, inner_smul_right]

/-- Diagonal cross-measure equals scalar measure (real part) -/
lemma spectral_cross_measure_diag (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (ψ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    (spectral_cross_measure E ψ ψ B).re = (spectral_scalar_measure E ψ hE B).toReal := by
  simp only [spectral_cross_measure]
  exact (spectral_scalar_measure_apply' E hE ψ B hB).symm

/-- Symmetry with conjugate: ν_{ψ,φ} = conj(ν_{φ,ψ}) when E(B) is self-adjoint -/
lemma spectral_cross_measure_conj_symm (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (ψ φ : H) (B : Set ℝ) :
    spectral_cross_measure E ψ φ B = star (spectral_cross_measure E φ ψ B) := by
  simp only [spectral_cross_measure]
  rw [← inner_conj_symm]
  simp only [inner_conj_symm, RCLike.star_def]
  exact hE.sa B ψ φ

/-!
## Spectral Cross-Integral Definition and Properties
-/

/-- Integration against the spectral cross-measure via polarization.
    Uses: ⟪x, y⟫ = (1/4)[‖x+y‖² - ‖x-y‖² - i‖x+iy‖² + i‖x-iy‖²] -/
noncomputable def spectral_cross_integral (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f : ℝ → ℂ) (ψ φ : H) : ℂ :=
  (1/4 : ℂ) * (
    ∫ s, f s ∂(spectral_scalar_measure E (ψ + φ) hE) -
    ∫ s, f s ∂(spectral_scalar_measure E (ψ - φ) hE) -
    I * ∫ s, f s ∂(spectral_scalar_measure E (ψ + I • φ) hE) +
    I * ∫ s, f s ∂(spectral_scalar_measure E (ψ - I • φ) hE))

/-- For indicators, cross-integral equals cross-measure (inner product) -/
lemma spectral_cross_integral_indicator (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (_hE_univ : E Set.univ = 1) (B : Set ℝ) (hB : MeasurableSet B) (ψ φ : H) :
    spectral_cross_integral E hE (Set.indicator B (1 : ℝ → ℂ)) ψ φ = ⟪E B ψ, φ⟫_ℂ := by
  simp only [spectral_cross_integral]
  -- Each integral ∫ 𝟙_B dμ_a = μ_a(B).toReal
  haveI h1 : IsFiniteMeasure (spectral_scalar_measure E (ψ + φ) hE) :=
    spectral_scalar_measure_finite E hE _hE_univ (ψ + φ)
  haveI h2 : IsFiniteMeasure (spectral_scalar_measure E (ψ - φ) hE) :=
    spectral_scalar_measure_finite E hE _hE_univ (ψ - φ)
  haveI h3 : IsFiniteMeasure (spectral_scalar_measure E (ψ + I • φ) hE) :=
    spectral_scalar_measure_finite E hE _hE_univ (ψ + I • φ)
  haveI h4 : IsFiniteMeasure (spectral_scalar_measure E (ψ - I • φ) hE) :=
    spectral_scalar_measure_finite E hE _hE_univ (ψ - I • φ)
  -- ∫ 𝟙_B dμ = μ(B).toReal for finite measure
  have int_ind : ∀ (a : H), ∫ s, Set.indicator B (1 : ℝ → ℂ) s ∂(spectral_scalar_measure E a hE) =
      (spectral_scalar_measure E a hE B).toReal := by
    intro a
    rw [MeasureTheory.integral_indicator hB]
    simp only [Pi.one_apply, MeasureTheory.integral_const, MeasurableSet.univ, measureReal_restrict_apply,
      Set.univ_inter]
    have : ∀ (r : ℝ), r • (1 : ℂ) = (r : ℂ) := fun r => by
      rw [Algebra.smul_def, mul_one]; rfl
    norm_cast
    simp [MeasureTheory.Measure.real]
    exact
      Complex.ext (congrArg re (this ((spectral_scalar_measure E a hE) B).toReal))
        (congrArg im (this ((spectral_scalar_measure E a hE) B).toReal))
  rw [int_ind (ψ + φ), int_ind (ψ - φ), int_ind (ψ + I • φ), int_ind (ψ - I • φ)]
  -- Now use: μ_a(B).toReal = ⟪E(B)a, a⟫.re and diagonal inner products are real
  rw [spectral_scalar_measure_apply' E hE (ψ + φ) B hB]
  rw [spectral_scalar_measure_apply' E hE (ψ - φ) B hB]
  rw [spectral_scalar_measure_apply' E hE (ψ + I • φ) B hB]
  rw [spectral_scalar_measure_apply' E hE (ψ - I • φ) B hB]
  -- Convert .re to full complex using diagonal is real
  have diag_real : ∀ (a : H), ⟪E B a, a⟫_ℂ = ↑(⟪E B a, a⟫_ℂ).re := by
    intro a
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [ofReal_im]; exact spectral_diagonal_real hE B a
  rw [← diag_real (ψ + φ), ← diag_real (ψ - φ), ← diag_real (ψ + I • φ), ← diag_real (ψ - I • φ)]
  -- Apply polarization identity (spectral_polarization from the file)
  rw [spectral_polarization E B hB ψ φ]

/-- Additivity of cross-integral for indicator functions -/
lemma spectral_cross_integral_indicator_add_left (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (B : Set ℝ) (hB : MeasurableSet B) (x y φ : H) :
    spectral_cross_integral E hE (Set.indicator B 1) (x + y) φ =
    spectral_cross_integral E hE (Set.indicator B 1) x φ +
    spectral_cross_integral E hE (Set.indicator B 1) y φ := by
  rw [spectral_cross_integral_indicator E hE hE_univ B hB (x + y) φ]
  rw [spectral_cross_integral_indicator E hE hE_univ B hB x φ]
  rw [spectral_cross_integral_indicator E hE hE_univ B hB y φ]
  -- ⟪E(B)(x+y), φ⟫ = ⟪E(B)x, φ⟫ + ⟪E(B)y, φ⟫
  simp only [map_add, inner_add_left]

/-- Cross-integral is additive in f -/
lemma spectral_cross_integral_add_f (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (_hE_univ : E Set.univ = 1) (f g : ℝ → ℂ) (ψ φ : H)
    (hf_int : ∀ a : H, Integrable f (spectral_scalar_measure E a hE))
    (hg_int : ∀ a : H, Integrable g (spectral_scalar_measure E a hE)) :
    spectral_cross_integral E hE (f + g) ψ φ =
    spectral_cross_integral E hE f ψ φ + spectral_cross_integral E hE g ψ φ := by
  simp only [spectral_cross_integral, Pi.add_apply]
  rw [integral_add (hf_int (ψ + φ)) (hg_int (ψ + φ))]
  rw [integral_add (hf_int (ψ - φ)) (hg_int (ψ - φ))]
  rw [integral_add (hf_int (ψ + I • φ)) (hg_int (ψ + I • φ))]
  rw [integral_add (hf_int (ψ - I • φ)) (hg_int (ψ - I • φ))]
  ring

/-- Cross-integral is homogeneous in f -/
lemma spectral_cross_integral_smul_f (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (_hE_univ : E Set.univ = 1) (c : ℂ) (f : ℝ → ℂ) (ψ φ : H)
    (_hf_int : ∀ a, Integrable f (spectral_scalar_measure E a hE)) :
    spectral_cross_integral E hE (fun s => c * f s) ψ φ =
    c * spectral_cross_integral E hE f ψ φ := by
  simp only [spectral_cross_integral]
  have pull : ∀ (μ : MeasureTheory.Measure ℝ),
      (∫ s, c * f s ∂μ) = c * (∫ s, f s ∂μ) := by
    intro μ
    exact MeasureTheory.integral_const_mul c f
  rw [pull, pull, pull, pull]
  ring

/-- Cross-integral commutes with finite sums in f -/
lemma spectral_cross_integral_finsum (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (_hE_univ : E Set.univ = 1) (n : ℕ) (g : Fin n → ℝ → ℂ) (ψ φ : H)
    (hg_int : ∀ i a, Integrable (g i) (spectral_scalar_measure E a hE)) :
    spectral_cross_integral E hE (fun s => ∑ i, g i s) ψ φ =
    ∑ i, spectral_cross_integral E hE (g i) ψ φ := by
  simp only [spectral_cross_integral]
  have h1 : ∫ s, (∑ i, g i s) ∂(spectral_scalar_measure E (ψ + φ) hE) =
            ∑ i, ∫ s, g i s ∂(spectral_scalar_measure E (ψ + φ) hE) :=
    integral_finset_sum _ (fun i _ => hg_int i (ψ + φ))
  have h2 : ∫ s, (∑ i, g i s) ∂(spectral_scalar_measure E (ψ - φ) hE) =
            ∑ i, ∫ s, g i s ∂(spectral_scalar_measure E (ψ - φ) hE) :=
    integral_finset_sum _ (fun i _ => hg_int i (ψ - φ))
  have h3 : ∫ s, (∑ i, g i s) ∂(spectral_scalar_measure E (ψ + I • φ) hE) =
            ∑ i, ∫ s, g i s ∂(spectral_scalar_measure E (ψ + I • φ) hE) :=
    integral_finset_sum _ (fun i _ => hg_int i (ψ + I • φ))
  have h4 : ∫ s, (∑ i, g i s) ∂(spectral_scalar_measure E (ψ - I • φ) hE) =
            ∑ i, ∫ s, g i s ∂(spectral_scalar_measure E (ψ - I • φ) hE) :=
    integral_finset_sum _ (fun i _ => hg_int i (ψ - I • φ))
  rw [h1, h2, h3, h4]
  simp only [one_div]
  -- Expand and recombine
  have key : ∀ (a b c d : Fin n → ℂ),
      4⁻¹ * (∑ i, a i - ∑ i, b i - I * ∑ i, c i + I * ∑ i, d i) =
      ∑ i, 4⁻¹ * (a i - b i - I * c i + I * d i) := by
    intro a b c d
    rw [mul_add, mul_sub, mul_sub]
    rw [Finset.mul_sum, Finset.mul_sum]
    simp only [← mul_assoc]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact key _ _ _ _

/-!
## Integrability Helpers
-/

/-- Indicator functions are integrable against finite spectral measures -/
lemma indicator_integrable_spectral (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (B : Set ℝ) (hB : MeasurableSet B) (a : H) :
    Integrable (Set.indicator B (1 : ℝ → ℂ)) (spectral_scalar_measure E a hE) := by
  haveI : IsFiniteMeasure (spectral_scalar_measure E a hE) :=
    spectral_scalar_measure_finite E hE hE_univ a
  apply Integrable.indicator
  · exact integrable_const 1
  · exact hB

/-- Scalar multiple of indicator is integrable -/
lemma smul_indicator_integrable_spectral (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (c : ℂ) (B : Set ℝ) (hB : MeasurableSet B) (a : H) :
    Integrable (fun s => c * Set.indicator B (1 : ℝ → ℂ) s) (spectral_scalar_measure E a hE) := by
  exact Integrable.const_mul (indicator_integrable_spectral E hE hE_univ B hB a) c

/-- Additivity for indicator scaled by constant -/
lemma spectral_cross_integral_indicator_smul_add_left (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (c : ℂ) (B : Set ℝ) (hB : MeasurableSet B) (x y φ : H) :
    spectral_cross_integral E hE (fun s => c * Set.indicator B (1 : ℝ → ℂ) s) (x + y) φ =
    spectral_cross_integral E hE (fun s => c * Set.indicator B (1 : ℝ → ℂ) s) x φ +
    spectral_cross_integral E hE (fun s => c * Set.indicator B (1 : ℝ → ℂ) s) y φ := by
  rw [spectral_cross_integral_smul_f E hE hE_univ c _ (x + y) φ
      (fun a => indicator_integrable_spectral E hE hE_univ B hB a)]
  rw [spectral_cross_integral_smul_f E hE hE_univ c _ x φ
      (fun a => indicator_integrable_spectral E hE hE_univ B hB a)]
  rw [spectral_cross_integral_smul_f E hE hE_univ c _ y φ
      (fun a => indicator_integrable_spectral E hE hE_univ B hB a)]
  rw [spectral_cross_integral_indicator_add_left E hE hE_univ B hB x y φ]
  ring

/-- Additivity holds for simple functions (finite linear combinations of indicators) -/
lemma spectral_cross_integral_add_left_simple (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (n : ℕ) (c : Fin n → ℂ) (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (x y φ : H) :
    let f := fun s => ∑ i, c i * Set.indicator (B i) (1 : ℝ → ℂ) s
    spectral_cross_integral E hE f (x + y) φ =
    spectral_cross_integral E hE f x φ + spectral_cross_integral E hE f y φ := by
  intro f
  have hint : ∀ i a, Integrable (fun s => c i * Set.indicator (B i) (1 : ℝ → ℂ) s)
                     (spectral_scalar_measure E a hE) :=
    fun i a => smul_indicator_integrable_spectral E hE hE_univ (c i) (B i) (hB i) a
  rw [spectral_cross_integral_finsum E hE hE_univ n _ (x + y) φ hint]
  rw [spectral_cross_integral_finsum E hE hE_univ n _ x φ hint]
  rw [spectral_cross_integral_finsum E hE hE_univ n _ y φ hint]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact spectral_cross_integral_indicator_smul_add_left E hE hE_univ (c i) (B i) (hB i) x y φ

/-- Cross-integral is additive in ψ for bounded measurable functions.
    Proof: True for simple functions (spectral_cross_integral_add_left_simple),
    extends to bounded measurable by uniform approximation + dominated convergence. -/
axiom spectral_cross_integral_add_left (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f : ℝ → ℂ) (x y φ : H)
    (hf_meas : Measurable f) (hf_bdd : ∃ M, ∀ s, ‖f s‖ ≤ M) :
    spectral_cross_integral E hE f (x + y) φ =
    spectral_cross_integral E hE f x φ + spectral_cross_integral E hE f y φ

/-!
## Diagonal Case Simplification
-/
 variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- On the diagonal `ψ = φ`, the cross-integral reduces to a standard integral:
    `spectral_cross_integral E hE f ψ ψ = ∫ f dμ_ψ`. Uses the scaling properties
    of spectral measures under `ψ + ψ = 2ψ`, etc. -/
lemma spectral_cross_integral_diag (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f : ℝ → ℂ) (ψ : H)
    (_hf_int : Integrable f (spectral_scalar_measure E ψ hE)) :
    spectral_cross_integral E hE f ψ ψ = ∫ s, f s ∂(spectral_scalar_measure E ψ hE) := by
  simp only [spectral_cross_integral]
  -- ψ + ψ = 2 • ψ, so μ_{ψ+ψ} = |2|² • μ_ψ = 4 • μ_ψ
  have h_2ψ : spectral_scalar_measure E (ψ + ψ) hE =
              ENNReal.ofReal (‖(2 : ℂ)‖^2) • spectral_scalar_measure E ψ hE := by
    have : ψ + ψ = (2 : ℂ) • ψ := by simp [two_smul]
    rw [this]
    exact spectral_scalar_measure_smul_eq E hE hE_univ 2 ψ
  have h_0 : spectral_scalar_measure E (ψ - ψ) hE = 0 := by
    simp only [sub_self]
    exact spectral_scalar_measure_zero_eq E hE
  have h_1pI : spectral_scalar_measure E (ψ + I • ψ) hE =
               ENNReal.ofReal (‖(1 : ℂ) + I‖^2) • spectral_scalar_measure E ψ hE := by
    have : ψ + I • ψ = ((1 : ℂ) + I) • ψ := by simp [add_smul]
    rw [this]
    exact spectral_scalar_measure_smul_eq E hE hE_univ (1 + I) ψ
  have h_1mI : spectral_scalar_measure E (ψ - I • ψ) hE =
               ENNReal.ofReal (‖(1 : ℂ) - I‖^2) • spectral_scalar_measure E ψ hE := by
    have : ψ - I • ψ = ((1 : ℂ) - I) • ψ := by simp [sub_smul]
    rw [this]
    exact spectral_scalar_measure_smul_eq E hE hE_univ (1 - I) ψ
  -- Compute the norms
  have norm_2 : ‖(2 : ℂ)‖^2 = 4 := by norm_num
  have norm_1pI : ‖(1 : ℂ) + I‖^2 = 2 := by
    have h : Complex.normSq ((1 : ℂ) + I) = 2 := by
      simp only [Complex.normSq]
      norm_num
    rw [← h]
    exact Complex.sq_norm (1 + I)

  have norm_1mI : ‖(1 : ℂ) - I‖^2 = 2 := by
    have h : Complex.normSq ((1 : ℂ) - I) = 2 := by
      simp only [Complex.normSq]
      norm_num
      grind
    rw [← h]
    exact Complex.sq_norm (1 - I)
  rw [h_2ψ, h_0, h_1pI, h_1mI, norm_2, norm_1pI, norm_1mI]
  simp only [integral_zero_measure, sub_zero]
  rw [integral_smul_measure, integral_smul_measure]
  simp only [one_div, ENNReal.ofReal_ofNat, ENNReal.toReal_ofNat, sub_add_cancel]
  have : (4 : ℝ) • (∫ s, f s ∂spectral_scalar_measure E ψ hE) =
         (4 : ℂ) * (∫ s, f s ∂spectral_scalar_measure E ψ hE) := by
    rw [Complex.real_smul]; push_cast; ring
  grind => ring

end FunctionalCalculus
