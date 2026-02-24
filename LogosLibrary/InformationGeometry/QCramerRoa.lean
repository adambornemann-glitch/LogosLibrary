/-
Copyright (c) 2026 Information Geometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann & co.
-/
import LogosLibrary.InformationGeometry.Fisher.StatisticalManifold
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
/-!
# The Cramér–Rao Bound

The **Cramér–Rao inequality** establishes the fundamental precision limit
for statistical estimation: the variance of any unbiased estimator is
bounded below by the inverse Fisher information.

For a scalar parameter θ and unbiased estimator T with E_θ[T] = τ(θ):
  **Var_θ(T) ≥ (dτ/dθ)² / I(θ)**

where I(θ) is the Fisher information. Equality holds iff T is an
**efficient estimator** (attains the bound).

## Main definitions

* `RegularStatisticalModel.variance` — variance of a random variable under P_θ
* `RegularStatisticalModel.covariance` — covariance of two random variables
* `IsUnbiasedEstimator` — E_θ[T] = τ(θ) for all θ
* `IsRegularEstimator` — estimator with regularity for differentiation

## Main results

* `covariance_score_identity` — Cov_θ(T, sᵢ) = ∂ᵢE_θ[T]
* `integral_mul_sq_le` — Cauchy–Schwarz for density-weighted integrals
* `cramerRao_scalar` — the scalar Cramér–Rao bound
* `cramerRao_saturated` — equality characterization

## Proof strategy

The key steps are:
1. **Differentiate the unbiasedness constraint** E_θ[T] = τ(θ) to get
   ∫ T · ∂ᵢp dμ = ∂ᵢτ (the Leibniz–unbiasedness identity)
2. **Rewrite** using `∂ᵢp = sᵢ · p` a.e. to get `∫ T · sᵢ · p dμ = ∂ᵢτ`
3. **Recognise** that `E[sᵢ] = 0` makes this equal to `Cov_θ(T, sᵢ)`
4. **Apply Cauchy–Schwarz** to `(T − E[T])` and `sᵢ` in `L²(P_θ)`
5. **Identify** `E[(T − E[T])²] = Var(T)` and `E[sᵢ²] = I(θ)`
6. **Rearrange** to get `Var(T) ≥ (∂τ)² / I(θ)`

The inequality is tight iff `T − E[T]` and `sᵢ` are linearly dependent
in `L²(P_θ)`, i.e. `T = a + b · sᵢ` a.e. for constants `a`, `b`.

## Connection to thermodynamics

The Cramér–Rao bound is a statement about information geometry: the
Fisher metric measures the "stiffness" of the statistical manifold.
Lower variance requires higher Fisher information, which means the
distributions are more distinguishable — exactly the regime where
entropy production (in measurement) is maximised.

Fisher information `I(θ) = ∫ (∂ log p)² p dμ` has the same form as
entropy production rate in irreversible thermodynamics: both measure
the cost of change.  The Cramér–Rao bound can therefore be read as a
thermodynamic uncertainty relation: the precision of any measurement
is bounded by the entropy cost of making it.

## References

* C. R. Rao, "Information and accuracy attainable in the estimation of
  statistical parameters", *Bull. Calcutta Math. Soc.* **37** (1945), 81–91.
* H. Cramér, *Mathematical Methods of Statistics*, Princeton, 1946.
* S. Amari, *Information Geometry and Its Applications*, §3.1, 2016.
-/

noncomputable section

open MeasureTheory ENNReal Real Set Filter Finset Metric

open scoped Topology

namespace InformationGeometry

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace RegularStatisticalModel

variable (M : RegularStatisticalModel n Ω)

/-! ### Variance and covariance -/

/-- The **variance** of a random variable `T : Ω → ℝ` under the
model distribution `P_θ`:
  `Var_θ(T) = E_θ[(T − E_θ[T])²] = E_θ[T²] − E_θ[T]²` -/
def variance {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (T : Ω → ℝ) : ℝ :=
  M.toStatisticalModel.expectation hθ (fun ω => (T ω) ^ 2) -
    (M.toStatisticalModel.expectation hθ T) ^ 2

/-- The **covariance** of random variables `T, U` under `P_θ`:
  `Cov_θ(T, U) = E_θ[TU] − E_θ[T] E_θ[U]` -/
def covariance {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (T U : Ω → ℝ) : ℝ :=
  M.toStatisticalModel.expectation hθ (fun ω => T ω * U ω) -
    M.toStatisticalModel.expectation hθ T *
    M.toStatisticalModel.expectation hθ U

/-! ### Estimators -/

/-- An estimator `T` is **unbiased** for the parameter function `τ` if
  `E_θ[T] = τ(θ)` for all `θ ∈ Θ`. -/
def IsUnbiasedEstimator (T : Ω → ℝ) (τ : ParamSpace n → ℝ) :
    Prop :=
  ∀ (θ : ParamSpace n) (hθ : θ ∈ M.paramDomain),
    M.toStatisticalModel.expectation hθ T = τ θ

/-- A **regular estimator** satisfies the technical conditions needed
to apply the Cramér–Rao bound:
- measurability,
- square-integrability under `P_θ`,
- integrability under `P_θ`,
- a dominated-convergence bound for differentiating `∫ T · p dμ`. -/
structure IsRegularEstimator (T : Ω → ℝ) : Prop where
  measurable : Measurable T
  square_integrable :
    ∀ (θ : ParamSpace n) (_hθ : θ ∈ M.paramDomain),
      Integrable (fun ω => T ω ^ 2 * M.density θ ω)
        M.refMeasure
  integrable :
    ∀ (θ : ParamSpace n) (_hθ : θ ∈ M.paramDomain),
      Integrable (fun ω => T ω * M.density θ ω)
        M.refMeasure
  has_deriv_bound :
    ∃ (B : Ω → ℝ),
      Integrable B M.refMeasure ∧
      ∀ (θ : ParamSpace n) (_hθ : θ ∈ M.paramDomain), ∀ ω,
        ‖T ω‖ *
          ‖fderiv ℝ (fun θ' => M.density θ' ω) θ‖ ≤ B ω

/-- `Var(T) = E[(T − μ)²]` where `μ = E[T]`, expressed as a
density-weighted integral of the centred square. -/
theorem variance_eq_centered {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (T : Ω → ℝ)
    (hReg : M.IsRegularEstimator T) :
    M.variance hθ T =
      ∫ ω, (T ω - M.toStatisticalModel.expectation hθ T) ^ 2 *
        M.density θ ω ∂M.refMeasure := by
  simp only [variance, StatisticalModel.expectation]
  -- set AFTER simp so E_T names the unfolded integral
  set E_T := ∫ ω, T ω * M.density θ ω ∂M.refMeasure with hE_def
  suffices h : ∫ ω, (T ω - E_T) ^ 2 * M.density θ ω ∂M.refMeasure =
      ∫ ω, T ω ^ 2 * M.density θ ω ∂M.refMeasure - E_T ^ 2 by linarith
  -- Named component functions so integral_add/sub can unify
  set f₁ : Ω → ℝ := fun ω => T ω ^ 2 * M.density θ ω
  set f₂ : Ω → ℝ := fun ω => 2 * E_T * (T ω * M.density θ ω)
  set f₃ : Ω → ℝ := fun ω => E_T ^ 2 * M.density θ ω
  have hf₁ : Integrable f₁ M.refMeasure :=
    hReg.square_integrable θ hθ
  have hf₂ : Integrable f₂ M.refMeasure :=
    (hReg.integrable θ hθ).const_mul _
  have hf₃ : Integrable f₃ M.refMeasure :=
    (M.toStatisticalModel.integrable hθ).const_mul _
  -- (T − E_T)²p = f₁ − f₂ + f₃
  have h1 : ∫ ω, (T ω - E_T) ^ 2 * M.density θ ω
      ∂M.refMeasure =
      ∫ ω, (f₁ ω - f₂ ω + f₃ ω) ∂M.refMeasure :=
    integral_congr_ae
      (ae_of_all _ fun ω => by simp only [f₁, f₂, f₃]; ring)
  -- Term-mode: full unifier matches (f₁ - f₂) + f₃
  -- against Pi.add
  have h2 : ∫ ω, (f₁ ω - f₂ ω + f₃ ω) ∂M.refMeasure =
      ∫ ω, (f₁ ω - f₂ ω) ∂M.refMeasure +
      ∫ ω, f₃ ω ∂M.refMeasure :=
    integral_add (hf₁.sub hf₂) hf₃
  have h3 : ∫ ω, (f₁ ω - f₂ ω) ∂M.refMeasure =
      ∫ ω, f₁ ω ∂M.refMeasure -
      ∫ ω, f₂ ω ∂M.refMeasure :=
    integral_sub hf₁ hf₂
  rw [h1, h2, h3]
  -- Unfold f's, pull constants, normalize, fold ∫ Tp back to E_T
  simp only [f₁, f₂, f₃, integral_const_mul,
      M.toStatisticalModel.density_integral_one θ hθ, ← hE_def]
  ring

/-! ### Leibniz rule for estimator integrals

The map `θ ↦ ∫ T(ω) · p(θ, ω) dμ` has Fréchet derivative
`∫ T(ω) • D_θ p(θ₀, ω) dμ` at `θ₀ ∈ Θ`.  This parallels
`hasFDerivAt_integral_density` from `Score.lean` but with the
extra factor of `T`.  The proof applies
`hasFDerivAt_integral_of_dominated_of_fderiv_le` to
`F(θ, ω) = T(ω) · p(θ, ω)`, using:
- `D_θ F = T(ω) • D_θ p` (since `T` is θ-independent),
- `‖T(ω) • D_θ p‖ = ‖T(ω)‖ · ‖D_θ p‖ ≤ B(ω)` from
  `IsRegularEstimator.has_deriv_bound`. -/

/-- Leibniz rule for `θ ↦ ∫ T · p(θ, ·) dμ`. -/
theorem hasFDerivAt_integral_T_density
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain)
    (T : Ω → ℝ) (hReg : M.IsRegularEstimator T) :
    HasFDerivAt
      (fun θ => ∫ ω, T ω * M.density θ ω ∂M.refMeasure)
      (∫ ω, T ω •
        fderiv ℝ (fun θ' => M.density θ' ω) θ₀
        ∂M.refMeasure)
      θ₀ := by
  obtain ⟨B, hB_int, hB_bound⟩ := hReg.has_deriv_bound
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp M.isOpen_paramDomain θ₀ hθ₀
  -- const_smul produces •, our goal has *; prove • version
  -- then convert
  suffices h : HasFDerivAt
      (fun θ => ∫ ω, T ω • M.density θ ω ∂M.refMeasure)
      (∫ ω, T ω •
        fderiv ℝ (fun θ' => M.density θ' ω) θ₀
        ∂M.refMeasure)
      θ₀ by
    simp only [smul_eq_mul] at h; exact h
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    hε
    -- (hF_meas) ∀ᶠ θ in 𝓝 θ₀, AEStronglyMeasurable (T • p θ) μ
    (eventually_of_mem (Metric.ball_mem_nhds θ₀ hε)
      (fun θ hθ =>
        (hReg.measurable.aestronglyMeasurable
          (μ := M.refMeasure)).smul
          (M.toStatisticalModel.density_measurable θ
            (hball hθ)).aestronglyMeasurable))
    -- (hF_int) Integrable (T • p θ₀) μ
    ((hReg.integrable θ₀ hθ₀).congr
      (ae_of_all _ (fun ω =>
        (smul_eq_mul (T ω) (M.density θ₀ ω)).symm)))
    -- (hF'_meas) AEStronglyMeasurable (T • D_θ p(θ₀, ·)) μ
    ((hReg.measurable.aestronglyMeasurable
      (μ := M.refMeasure)).smul
      (M.density_fderiv_aestronglyMeasurable θ₀ hθ₀))
    -- (h_bound) ∀ᵐ ω, ∀ θ ∈ ball θ₀ ε, ‖T ω • D_θ p‖ ≤ B ω
    (ae_of_all _ (fun ω θ hθ => by
      rw [norm_smul]; exact hB_bound θ (hball hθ) ω))
    -- (bound_integrable) Integrable B μ
    hB_int
    -- (h_diff) ∀ᵐ ω, ∀ θ ∈ ball θ₀ ε,
    --   HasFDerivAt (· • p) (· • D_θ p) θ
    (ae_of_all _ (fun ω θ hθ =>
      (M.toStatisticalModel.density_differentiableAt
        (hball hθ) ω).hasFDerivAt.const_smul (T ω)))

/-! ### Evaluating the Leibniz derivative on basis vectors -/

/-- Evaluating the Fréchet derivative `∫ T • D_θ p dμ` on the basis
vector `eᵢ` yields `∫ T · ∂ᵢp dμ`.

This uses the CLM integral-evaluation exchange:
`(∫ φ dμ)(v) = ∫ φ(v) dμ` for integrable `φ`. -/
theorem integral_T_smul_fderiv_apply
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain)
    (T : Ω → ℝ) (hReg : M.IsRegularEstimator T)
    (i : Fin n) :
    (∫ ω, T ω •
      fderiv ℝ (fun θ' => M.density θ' ω) θ₀
      ∂M.refMeasure) (EuclideanSpace.single i 1) =
    ∫ ω, T ω * M.partialDensity θ₀ i ω
      ∂M.refMeasure := by
  -- (∫ T • D_θ p dμ)(eᵢ) = ∫ (T • D_θ p)(eᵢ) dμ
  -- = ∫ T · (D_θ p)(eᵢ) dμ = ∫ T · ∂ᵢp dμ
  rw [ContinuousLinearMap.integral_apply]
  · -- (T ω • fderiv)(eᵢ) = T ω * fderiv(eᵢ) = T ω * ∂ᵢp
    congr 1
  · -- Integrability of ω ↦ T ω • fderiv p(θ₀, ω)
    -- Follows from the derivative bound
    obtain ⟨B, hB_int, hB_bound⟩ := hReg.has_deriv_bound
    exact Integrable.mono' hB_int
      ((hReg.measurable.aestronglyMeasurable
        (μ := M.refMeasure)).smul
        (M.density_fderiv_aestronglyMeasurable θ₀ hθ₀))
      (ae_of_all _ (fun ω => by
        rw [norm_smul]; exact hB_bound θ₀ hθ₀ ω))


/-! ### The covariance–score identity -/

/-- **Key lemma.**  For a regular estimator, differentiating
`E_θ[T] = ∫ T · p dμ` in direction `eᵢ` gives:
  `∫ T(ω) · ∂ᵢp(θ, ω) dμ = ∂ᵢ(E_θ[T])`

This is the Leibniz derivative evaluated on `eᵢ`, combined with
the fact that `HasFDerivAt` pins the `fderiv`. -/
theorem integral_T_partialDensity_eq
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain)
    (T : Ω → ℝ) (hReg : M.IsRegularEstimator T)
    (i : Fin n) :
    ∫ ω, T ω * M.partialDensity θ₀ i ω ∂M.refMeasure =
      fderiv ℝ
        (fun θ => ∫ ω, T ω * M.density θ ω ∂M.refMeasure)
        θ₀ (EuclideanSpace.single i 1) := by
  -- Leibniz gives: fderiv (∫ T·p) = ∫ T • D_θ p
  have hL := M.hasFDerivAt_integral_T_density hθ₀ T hReg
  rw [hL.fderiv]
  exact (M.integral_T_smul_fderiv_apply hθ₀ T hReg i).symm

/-- The integral of `T · ∂ᵢp` equals `∫ T · sᵢ · p` a.e.,
since `∂ᵢp = sᵢ · p` wherever `p > 0`. -/
theorem integral_T_partialDensity_eq_T_score
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain)
    (T : Ω → ℝ) (i : Fin n) :
    ∫ ω, T ω * M.partialDensity θ₀ i ω ∂M.refMeasure =
      ∫ ω, T ω * M.score θ₀ i ω * M.density θ₀ ω
        ∂M.refMeasure := by
  apply integral_congr_ae
  filter_upwards
    [M.toStatisticalModel.density_pos_ae θ₀ hθ₀]
    with ω hω
  simp only [partialDensity, score]
  have hp_ne : M.density θ₀ ω ≠ 0 := ne_of_gt hω
  field_simp

/-- **Covariance–Score Identity.**

For a regular unbiased estimator `T` with `E_θ[T] = τ(θ)`:
  `Cov_θ(T, sᵢ) = ∂ᵢτ(θ)`

**Proof.**
- `Cov(T, sᵢ) = E[T · sᵢ] − E[T] · E[sᵢ] = E[T · sᵢ]`
  since `E[sᵢ] = 0`.
- `E[T · sᵢ] = ∫ T · sᵢ · p dμ = ∫ T · ∂ᵢp dμ` (a.e. rewrite).
- `∫ T · ∂ᵢp dμ = ∂ᵢ(∫ T · p dμ)` (Leibniz).
- `∂ᵢ(∫ T · p dμ) = ∂ᵢ(E[T]) = ∂ᵢ(τ(θ))` (unbiasedness).  -/
theorem covariance_score_eq_deriv_target
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (T : Ω → ℝ)
    (τ : ParamSpace n → ℝ)
    (hReg : M.IsRegularEstimator T)
    (hUnbiased : M.IsUnbiasedEstimator T τ)
    (_hτ_diff : DifferentiableAt ℝ τ θ)
    (i : Fin n) :
    M.covariance hθ T (M.score θ i) =
      fderiv ℝ τ θ (EuclideanSpace.single i 1) := by
  -- Step 1: Cov(T, sᵢ) = E[T·sᵢ] − E[T]·E[sᵢ]
  --       = E[T·sᵢ] − E[T]·0
  simp only [covariance]
  have hE_score : M.toStatisticalModel.expectation hθ
      (fun ω => M.score θ i ω) = 0 :=
    M.score_expectation_eq_zero' hθ i
  rw [hE_score, mul_zero, sub_zero]
  -- Goal: ∫ (T · sᵢ) · p dμ = fderiv τ θ (eᵢ)
  -- Step 2: ∫ T·sᵢ·p dμ = ∫ T·∂ᵢp dμ  (by ∂ᵢp = sᵢ·p a.e.)
  rw [show (fun ω => T ω * M.score θ i ω) =
    (fun ω => T ω * M.score θ i ω) from rfl]
  -- The expectation form is ∫ (T·sᵢ) * p dμ
  simp only [StatisticalModel.expectation]
  -- Rewrite the integrand: T·sᵢ·p = T·∂ᵢp  a.e.
  rw [show ∫ ω, T ω * M.score θ i ω * M.density θ ω
      ∂M.refMeasure =
    ∫ ω, T ω * M.partialDensity θ i ω ∂M.refMeasure from
    (M.integral_T_partialDensity_eq_T_score hθ T i).symm]
  -- Step 3: ∫ T·∂ᵢp dμ = ∂ᵢ(∫ T·p dμ)  (Leibniz)
  rw [M.integral_T_partialDensity_eq hθ T hReg i]
  -- Step 4: ∂ᵢ(∫ T·p dμ) = ∂ᵢτ  (unbiasedness)
  -- ∫ T·p dμ = E[T] = τ(θ) near θ, so their fderivs agree.
  congr 1
  -- Need: fderiv (θ ↦ ∫ T·p(θ,·) dμ) = fderiv τ
  -- Since ∫ T·p(θ,·) dμ = τ(θ) for all θ ∈ Θ (unbiasedness),
  -- the two functions agree on a neighbourhood of θ.
  apply Filter.EventuallyEq.fderiv_eq
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp M.isOpen_paramDomain θ hθ
  exact eventually_of_mem (Metric.ball_mem_nhds θ hε)
    (fun θ' hθ' => hUnbiased θ' (hball hθ'))


/-! ### Estimator–score cross-integrability -/

/-- **Cross-integrability of an estimator with the score:**
  `T · sᵢ · p ∈ L¹(μ)`.

Uses AM–GM: `|T · sᵢ| ≤ ½(T² + sᵢ²)`, hence
  `|T · sᵢ| · p ≤ ½(T² · p + sᵢ² · p)`
and both summands are integrable — the first by
`hReg.square_integrable`, the second by `hSq`. -/
theorem estimator_score_integrable
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (T : Ω → ℝ) (hReg : M.IsRegularEstimator T)
    (hSq : M.ScoreSqIntegrableModel θ) (i : Fin n) :
    Integrable
      (fun ω => T ω * M.score θ i ω * M.density θ ω)
      M.refMeasure := by
  -- Dominating function: ½(T²p + sᵢ²p)
  apply Integrable.mono'
    (((hReg.square_integrable θ hθ).add (hSq i)).div_const 2)
  · -- AEStronglyMeasurable: product of measurable functions
    exact ((hReg.measurable.aestronglyMeasurable
      (μ := M.refMeasure)).mul
      (M.score_aestronglyMeasurable hθ i)).mul
      (M.toStatisticalModel.density_measurable θ
        hθ).aestronglyMeasurable
  · -- Pointwise bound via AM–GM
    apply ae_of_all; intro ω
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (M.density_nonneg θ hθ ω)]
    have hp : 0 ≤ M.density θ ω :=
      M.density_nonneg θ hθ ω
    calc |T ω| * |M.score θ i ω| * M.density θ ω
          = (|T ω| * |M.score θ i ω|) *
              M.density θ ω := by ring
        _ ≤ ((T ω ^ 2 +
              M.score θ i ω ^ 2) / 2) *
              M.density θ ω := by
            apply mul_le_mul_of_nonneg_right _ hp
            have h : 0 ≤ (|T ω| -
              |M.score θ i ω|) ^ 2 := sq_nonneg _
            nlinarith [sq_abs (T ω),
                       sq_abs (M.score θ i ω)]
        _ = (T ω ^ 2 * M.density θ ω +
              M.score θ i ω ^ 2 *
              M.density θ ω) / 2 := by
            ring

/-! ### Centred estimator integrability -/

/-- **Square-integrability of a centred estimator:**
  `(T − c)² · p ∈ L¹(μ)`.

Expands as `T²p − 2c(Tp) + c²p`; all three terms are integrable
from `hReg.square_integrable`, `hReg.integrable`, and
`M.integrable` respectively. -/
theorem centered_sq_integrable
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (T : Ω → ℝ) (hReg : M.IsRegularEstimator T)
    (c : ℝ) :
    Integrable
      (fun ω => (T ω - c) ^ 2 * M.density θ ω)
      M.refMeasure := by
  -- (T − c)²p = T²p − 2c·Tp + c²·p
  have heq : ∀ ω, (T ω - c) ^ 2 * M.density θ ω =
      T ω ^ 2 * M.density θ ω -
      2 * c * (T ω * M.density θ ω) +
      c ^ 2 * M.density θ ω := fun ω => by ring
  simp_rw [heq]
  exact ((hReg.square_integrable θ hθ).sub
    ((hReg.integrable θ hθ).const_mul (2 * c))).add
    ((M.toStatisticalModel.integrable hθ).const_mul (c ^ 2))

/-- **Cross-integrability of a centred estimator with the score:**
  `(T − c) · sᵢ · p ∈ L¹(μ)`.

Expands as `T·sᵢ·p − c·sᵢ·p`; the first term is integrable by
`estimator_score_integrable`, the second by
`score_integrable_wrt_density`. -/
theorem centered_score_integrable
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (T : Ω → ℝ) (hReg : M.IsRegularEstimator T)
    (hSq : M.ScoreSqIntegrableModel θ)
    (c : ℝ) (i : Fin n) :
    Integrable
      (fun ω => (T ω - c) * M.score θ i ω *
        M.density θ ω)
      M.refMeasure := by
  -- (T − c)·sᵢ·p = T·sᵢ·p − c·(sᵢ·p)
  have heq : ∀ ω,
      (T ω - c) * M.score θ i ω * M.density θ ω =
      T ω * M.score θ i ω * M.density θ ω -
      c * (M.score θ i ω * M.density θ ω) :=
    fun ω => by ring
  simp_rw [heq]
  exact (M.estimator_score_integrable hθ T hReg hSq i).sub
    ((M.score_integrable_wrt_density hθ i).const_mul c)

/-! ### Shared lemma: centred estimator × score integral

This computation appears in both `cramerRao_scalar` and the
equality characterisation `cramerRao_saturated`.  We extract it
to avoid duplication.

The result is:
  `∫ (T − E[T]) · sᵢ · p dμ = ∂ᵢτ(θ)` -/

/-- The integral of the centred estimator times the score times
the density equals the derivative of the target:
  `∫ (T(ω) − E_θ[T]) · sᵢ(θ,ω) · p(θ,ω) dμ = ∂ᵢτ(θ)`.

**Proof.** Expand `(T − E[T]) · sᵢ · p = T · sᵢ · p − E[T] · sᵢ · p`.
The first integral equals `∂ᵢτ` by the covariance–score identity.
The second vanishes because `∫ sᵢ · p = 0`. -/
theorem centered_estimator_score_integral
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (T : Ω → ℝ)
    (τ : ParamSpace n → ℝ)
    (hReg : M.IsRegularEstimator T)
    (hUnbiased : M.IsUnbiasedEstimator T τ)
    (hτ_diff : DifferentiableAt ℝ τ θ)
    (hSq : M.ScoreSqIntegrableModel θ)
    (i : Fin n) :
    ∫ ω, (T ω - M.toStatisticalModel.expectation hθ T) *
      M.score θ i ω * M.density θ ω ∂M.refMeasure =
    fderiv ℝ τ θ (EuclideanSpace.single i 1) := by
  set μ_T := M.toStatisticalModel.expectation hθ T
  -- (T−μ)·sᵢ·p = T·sᵢ·p − μ·sᵢ·p
  have hexpand : ∀ ω,
      (T ω - μ_T) * M.score θ i ω * M.density θ ω =
      T ω * M.score θ i ω * M.density θ ω -
      μ_T * (M.score θ i ω * M.density θ ω) := by
    intro ω; ring
  simp_rw [hexpand]
  rw [integral_sub
    (M.estimator_score_integrable hθ T hReg hSq i)
    ((M.score_integrable_wrt_density hθ i).const_mul μ_T)]
  rw [integral_const_mul,
      M.score_expectation_eq_zero hθ i, mul_zero, sub_zero]
  -- ∫ T·sᵢ·p = Cov(T, sᵢ) (since E[sᵢ]=0) = ∂ᵢτ
  have hcov :=
    M.covariance_score_eq_deriv_target hθ T τ hReg
      hUnbiased hτ_diff i
  simp only [covariance, StatisticalModel.expectation] at hcov
  rw [M.score_expectation_eq_zero hθ i] at hcov
  simp only [mul_zero, sub_zero] at hcov
  exact hcov

/-! ### Cauchy–Schwarz: equality characterisation -/

/-- Equality in Cauchy–Schwarz holds iff `f` and `g` are
proportional in `L²(P_θ)`: there exist `α, β` not both zero
with `α f + β g = 0` a.e.

Equivalently (when `∫ g²p > 0`): `f = (B/C) · g` a.e.
where `B = ∫ fgp`, `C = ∫ g²p`. -/
theorem integral_mul_sq_eq_iff
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (f g : Ω → ℝ)
    (hf : Integrable (fun ω => f ω ^ 2 * M.density θ ω)
      M.refMeasure)
    (hg : Integrable (fun ω => g ω ^ 2 * M.density θ ω)
      M.refMeasure)
    (hfg : Integrable
      (fun ω => f ω * g ω * M.density θ ω)
      M.refMeasure)
    (hC_pos : 0 < ∫ ω, g ω ^ 2 * M.density θ ω
      ∂M.refMeasure) :
    (∫ ω, f ω * g ω * M.density θ ω ∂M.refMeasure) ^ 2 =
      (∫ ω, f ω ^ 2 * M.density θ ω ∂M.refMeasure) *
      (∫ ω, g ω ^ 2 * M.density θ ω ∂M.refMeasure) ↔
    ∃ c : ℝ, ∀ᵐ ω ∂M.refMeasure,
      f ω = c * g ω := by
  set A := ∫ ω, f ω ^ 2 * M.density θ ω ∂M.refMeasure
  set B := ∫ ω, f ω * g ω * M.density θ ω ∂M.refMeasure
  set C := ∫ ω, g ω ^ 2 * M.density θ ω ∂M.refMeasure
  constructor
  · -- Forward: B² = AC ⟹ f = (B/C)·g a.e.
    intro heq
    use B / C
    have hC_ne : C ≠ 0 := ne_of_gt hC_pos
    -- Q(−B/C) = A − B²/C = 0
    have hQ_zero : ∫ ω, (f ω + (-B / C) * g ω) ^ 2 *
        M.density θ ω ∂M.refMeasure = 0 := by
      set t := -B / C
      set q₁ : Ω → ℝ := fun ω =>
        f ω ^ 2 * M.density θ ω
      set q₂ : Ω → ℝ := fun ω =>
        2 * t * (f ω * g ω * M.density θ ω)
      set q₃ : Ω → ℝ := fun ω =>
        t ^ 2 * (g ω ^ 2 * M.density θ ω)
      have hq₁ : Integrable q₁ M.refMeasure := hf
      have hq₂ : Integrable q₂ M.refMeasure :=
        hfg.const_mul _
      have hq₃ : Integrable q₃ M.refMeasure :=
        hg.const_mul _
      have h1 : ∫ ω, (f ω + t * g ω) ^ 2 *
          M.density θ ω ∂M.refMeasure =
          ∫ ω, (q₁ ω + q₂ ω + q₃ ω)
            ∂M.refMeasure :=
        integral_congr_ae
          (ae_of_all _ fun ω => by
            simp only [q₁, q₂, q₃]; ring)
      have h2 : ∫ ω, (q₁ ω + q₂ ω + q₃ ω)
          ∂M.refMeasure =
          ∫ ω, (q₁ ω + q₂ ω) ∂M.refMeasure +
          ∫ ω, q₃ ω ∂M.refMeasure :=
        integral_add (hq₁.add hq₂) hq₃
      have h3 : ∫ ω, (q₁ ω + q₂ ω) ∂M.refMeasure =
          ∫ ω, q₁ ω ∂M.refMeasure +
          ∫ ω, q₂ ω ∂M.refMeasure :=
        integral_add hq₁ hq₂
      rw [h1, h2, h3]
      simp only [q₁, q₂, q₃, integral_const_mul]
      -- Goal: A + 2*t*B + t²*C = 0
      have key : A + 2 * t * B + t ^ 2 * C =
          (A * C - B ^ 2) / C := by
        simp only [t]; field_simp; ring
      rw [key, heq, sub_self, zero_div]
    -- (f + tg)²p ≥ 0 pointwise and integrates to 0 ⟹ = 0 a.e.
    have hnn : ∀ ω, 0 ≤ (f ω + (-B / C) * g ω) ^ 2 *
        M.density θ ω :=
      fun ω => mul_nonneg (sq_nonneg _)
        (M.density_nonneg θ hθ ω)
    have h_ae := (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all _ hnn)
      (by -- integrability of (f + tg)²p
        have : ∀ ω, (f ω + (-B / C) * g ω) ^ 2 *
            M.density θ ω =
          f ω ^ 2 * M.density θ ω +
          (2 * (-B / C) * (f ω * g ω * M.density θ ω) +
           (-B / C) ^ 2 *
            (g ω ^ 2 * M.density θ ω)) :=
          fun ω => by ring
        simp_rw [this]
        exact hf.add
          ((hfg.const_mul _).add (hg.const_mul _)))).mp
      hQ_zero
    -- f + (−B/C)g = 0 a.e. ⟹ f = (B/C)g a.e.
    filter_upwards [h_ae,
      M.toStatisticalModel.density_pos_ae θ hθ]
      with ω hprod hpos
    have hp_ne : M.density θ ω ≠ 0 := ne_of_gt hpos
    have hsq : (f ω + (-B / C) * g ω) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact h
      · exact absurd h hp_ne
    have hsum : f ω + -B / C * g ω = 0 :=
      mul_self_eq_zero.mp (by rw [sq] at hsq; exact hsq)
    linear_combination hsum
  · -- Backward: f = c·g a.e. ⟹ B² = AC
    intro ⟨c, hcg⟩
    have hB : B = c * C := by
      simp only [B, C]
      calc ∫ ω, f ω * g ω * M.density θ ω
            ∂M.refMeasure
          = ∫ ω, c * (g ω ^ 2 * M.density θ ω)
            ∂M.refMeasure :=
            integral_congr_ae
              (hcg.mono fun ω h => by simp; rw [h]; ring)
        _ = c * ∫ ω, g ω ^ 2 * M.density θ ω
            ∂M.refMeasure := by
            rw [integral_const_mul]
    have hA : A = c ^ 2 * C := by
      simp only [A, C]
      calc ∫ ω, f ω ^ 2 * M.density θ ω
            ∂M.refMeasure
          = ∫ ω, c ^ 2 * (g ω ^ 2 * M.density θ ω)
            ∂M.refMeasure :=
            integral_congr_ae
              (hcg.mono fun ω h => by simp; rw [h]; ring)
        _ = c ^ 2 * ∫ ω, g ω ^ 2 * M.density θ ω
            ∂M.refMeasure := by
            rw [integral_const_mul]
    rw [hB, hA]; ring


/-! ### Cauchy–Schwarz for density-weighted integrals -/

/-- **Cauchy–Schwarz inequality** for density-weighted integrals:
  `(∫ f · g · p dμ)² ≤ (∫ f² · p dμ) · (∫ g² · p dμ)`

**Proof** (discriminant method).
For all `t ∈ ℝ`, `∫ (f + t g)² · p dμ ≥ 0` since the integrand is
pointwise nonneg.  Expanding gives `A + 2tB + t²C ≥ 0` where
`A = ∫ f²p`, `B = ∫ fgp`, `C = ∫ g²p`.  If `C > 0`, specialising
at `t = −B/C` yields `A − B²/C ≥ 0`, hence `B² ≤ AC`.  If `C = 0`,
then `g²p = 0` a.e.; since `p > 0` a.e. this gives `g = 0` a.e.,
hence `B = 0` and `B² = 0 ≤ AC = 0`. -/
theorem integral_mul_sq_le
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (f g : Ω → ℝ)
    (hf : Integrable (fun ω => f ω ^ 2 * M.density θ ω)
      M.refMeasure)
    (hg : Integrable (fun ω => g ω ^ 2 * M.density θ ω)
      M.refMeasure)
    (hfg : Integrable
      (fun ω => f ω * g ω * M.density θ ω)
      M.refMeasure) :
    (∫ ω, f ω * g ω * M.density θ ω ∂M.refMeasure) ^ 2 ≤
      (∫ ω, f ω ^ 2 * M.density θ ω ∂M.refMeasure) *
      (∫ ω, g ω ^ 2 * M.density θ ω
        ∂M.refMeasure) := by
  -- Abbreviations
  set A := ∫ ω, f ω ^ 2 * M.density θ ω ∂M.refMeasure
  set B := ∫ ω, f ω * g ω * M.density θ ω ∂M.refMeasure
  set C := ∫ ω, g ω ^ 2 * M.density θ ω ∂M.refMeasure
  -- Show: B² ≤ A · C
  -- Key fact: ∀ t, ∫ (f + t·g)² · p ≥ 0
  have hQ : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * C := by
    intro t
    have hint : 0 ≤ ∫ ω, (f ω + t * g ω) ^ 2 *
        M.density θ ω ∂M.refMeasure :=
      integral_nonneg (fun ω => mul_nonneg (sq_nonneg _)
        (M.density_nonneg θ hθ ω))
    -- ∫ (f+tg)²·p = A + 2tB + t²C
    have hexpand : ∫ ω, (f ω + t * g ω) ^ 2 *
          M.density θ ω ∂M.refMeasure =
          A + 2 * t * B + t ^ 2 * C := by
        have heq : ∀ ω, (f ω + t * g ω) ^ 2 *
            M.density θ ω =
          f ω ^ 2 * M.density θ ω +
          (2 * t * (f ω * g ω * M.density θ ω) +
           t ^ 2 * (g ω ^ 2 * M.density θ ω)) :=
          fun ω => by ring
        simp_rw [heq]
        have h1 : ∫ ω, f ω ^ 2 * M.density θ ω +
            (2 * t * (f ω * g ω * M.density θ ω) +
            t ^ 2 * (g ω ^ 2 * M.density θ ω))
            ∂M.refMeasure =
            ∫ ω, f ω ^ 2 * M.density θ ω
              ∂M.refMeasure +
            ∫ ω, (2 * t * (f ω * g ω * M.density θ ω) +
              t ^ 2 * (g ω ^ 2 * M.density θ ω))
              ∂M.refMeasure :=
          integral_add hf
            ((hfg.const_mul _).add (hg.const_mul _))
        have h2 : ∫ ω,
            (2 * t * (f ω * g ω * M.density θ ω) +
            t ^ 2 * (g ω ^ 2 * M.density θ ω))
            ∂M.refMeasure =
            ∫ ω, 2 * t * (f ω * g ω * M.density θ ω)
              ∂M.refMeasure +
            ∫ ω, t ^ 2 * (g ω ^ 2 * M.density θ ω)
              ∂M.refMeasure :=
          integral_add (hfg.const_mul _) (hg.const_mul _)
        rw [h1, h2, integral_const_mul, integral_const_mul]
        ring
    linarith [hexpand ▸ hint]
  -- Case split on C
  by_cases hC : C = 0
  · -- Case C = 0: g²p = 0 a.e., so gp = 0 a.e., so B = 0
    have hg_sq_zero : ∀ᵐ ω ∂M.refMeasure,
        g ω ^ 2 * M.density θ ω = 0 := by
      have hnn : ∀ ω, 0 ≤ g ω ^ 2 * M.density θ ω :=
        fun ω => mul_nonneg (sq_nonneg _)
          (M.density_nonneg θ hθ ω)
      exact (integral_eq_zero_iff_of_nonneg_ae
        (ae_of_all _ hnn) hg).mp hC
    -- g = 0 a.e. (since p > 0 a.e.)
    have hg_zero : ∀ᵐ ω ∂M.refMeasure, g ω = 0 := by
      filter_upwards [hg_sq_zero,
        M.toStatisticalModel.density_pos_ae θ hθ]
        with ω hprod hpos
      have hp_ne : M.density θ ω ≠ 0 := ne_of_gt hpos
      have hsq : g ω ^ 2 = 0 := by
        rcases mul_eq_zero.mp hprod with h | h
        · exact h
        · exact absurd h hp_ne
      exact pow_eq_zero_iff (n := 2) (by omega) |>.mp hsq
    -- B = ∫ f·g·p = ∫ f·0·p = 0
    have hB : B = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hg_zero] with ω hω
      simp [hω]
    rw [hB, hC]; ring_nf; rfl
  · -- Case C > 0
    have hC_pos : 0 < C := by
      rcases (integral_nonneg (fun ω =>
        mul_nonneg (sq_nonneg (g ω))
          (M.density_nonneg θ hθ ω))).lt_or_eq with h | h
      · exact h
      · exact absurd h.symm hC
    -- Specialise Q at t = −B/C
    -- A + 2·(−B/C)·B + (−B/C)²·C ≥ 0
    -- = A − 2B²/C + B²/C = A − B²/C ≥ 0
    -- Hence A·C ≥ B²
    suffices h : B ^ 2 ≤ A * C by linarith
    rw [← sub_nonneg]
    have hC_ne : C ≠ 0 := ne_of_gt hC_pos
    have h_eq : A * C - B ^ 2 =
        C * (A + 2 * (-B / C) * B +
          (-B / C) ^ 2 * C) := by
      field_simp; ring
    linarith [mul_nonneg (le_of_lt hC_pos) (hQ (-B / C))]

/-! ### The Cramér–Rao bound -/

/-- **The Cramér–Rao inequality** (scalar case).

For a regular unbiased estimator `T` of a differentiable parameter
function `τ`, with `g_{ii}(θ) = E_θ[sᵢ²] > 0`:

  **Var_θ(T) ≥ (∂ᵢτ(θ))² / g_{ii}(θ)**

**Proof.**
Apply Cauchy–Schwarz to `f = T − τ(θ)` (the centred estimator) and
`g = sᵢ` (the `i`-th score) in the density-weighted inner product:

  `(∫ (T−τ) · sᵢ · p)² ≤ (∫ (T−τ)² · p) · (∫ sᵢ² · p)`
  `= Var(T) · g_{ii}(θ)`.

The LHS equals `(∂ᵢτ)²` by the covariance–score identity (since
`E[sᵢ] = 0` makes the centering irrelevant).  Dividing by
`g_{ii} > 0` gives the bound.  -/
theorem cramerRao_scalar
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (T : Ω → ℝ)
    (τ : ParamSpace n → ℝ)
    (hReg : M.IsRegularEstimator T)
    (hUnbiased : M.IsUnbiasedEstimator T τ)
    (hτ_diff : DifferentiableAt ℝ τ θ)
    (i : Fin n)
    (hSq : M.ScoreSqIntegrableModel θ)
    (hFisher_pos : 0 < M.fisherMatrix θ i i) :
    M.variance hθ T ≥
      (fderiv ℝ τ θ (EuclideanSpace.single i 1)) ^ 2 /
        M.fisherMatrix θ i i := by
  -- Abbreviate
  set μ_T := M.toStatisticalModel.expectation hθ T
  set dτ := fderiv ℝ τ θ (EuclideanSpace.single i 1)
  set Iii := M.fisherMatrix θ i i
  -- The cross integral = dτ (extracted lemma)
  have h_cross :
      ∫ ω, (T ω - μ_T) * M.score θ i ω *
        M.density θ ω ∂M.refMeasure = dτ :=
    M.centered_estimator_score_integral hθ T τ hReg
      hUnbiased hτ_diff hSq i
  -- ∫ (T−μ)²·p = Var(T)
  have h_var :
      ∫ ω, (T ω - μ_T) ^ 2 * M.density θ ω
        ∂M.refMeasure = M.variance hθ T :=
    (variance_eq_centered M hθ T hReg).symm
  -- ∫ sᵢ²·p = g_{ii}
  have h_fisher :
      ∫ ω, M.score θ i ω ^ 2 * M.density θ ω
        ∂M.refMeasure = Iii :=
    (M.fisherMatrix_diag_eq_score_sq i).symm
  -- Cauchy–Schwarz:
  --   (∫ (T−μ)·sᵢ·p)² ≤ (∫ (T−μ)²·p)·(∫ sᵢ²·p)
  have hCS := M.integral_mul_sq_le hθ
    (fun ω => T ω - μ_T) (M.score θ i)
    (M.centered_sq_integrable hθ T hReg μ_T)
    (hSq i)
    (M.centered_score_integrable hθ T hReg hSq μ_T i)
  -- Substitute known values
  rw [h_cross, h_var, h_fisher] at hCS
  -- hCS : dτ² ≤ Var(T) · Iii
  -- Goal : Var(T) ≥ dτ² / Iii
  exact (div_le_iff₀ hFisher_pos).mpr hCS

/-- **Cramér–Rao: equality characterisation.**

Equality holds in the Cramér–Rao bound iff `T` is an **efficient
estimator**: `T(ω) = a + b · sᵢ(θ, ω)` a.e. for constants `a, b`.

This is equivalent to `T − E[T]` being proportional to `sᵢ` in
`L²(P_θ)`, i.e. equality in the Cauchy–Schwarz step.

When equality holds, `a = τ(θ)` and `b = (∂ᵢτ) / g_{ii}(θ)`. -/
theorem cramerRao_saturated
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (T : Ω → ℝ)
    (τ : ParamSpace n → ℝ)
    (hReg : M.IsRegularEstimator T)
    (hUnbiased : M.IsUnbiasedEstimator T τ)
    (hτ_diff : DifferentiableAt ℝ τ θ)
    (i : Fin n)
    (hSq : M.ScoreSqIntegrableModel θ)
    (hFisher_pos : 0 < M.fisherMatrix θ i i) :
    M.variance hθ T =
      (fderiv ℝ τ θ (EuclideanSpace.single i 1)) ^ 2 /
        M.fisherMatrix θ i i ↔
    ∃ (a b : ℝ), ∀ᵐ ω ∂M.refMeasure,
      T ω = a + b * M.score θ i ω := by
  -- Common abbreviations
  set μ_T := M.toStatisticalModel.expectation hθ T
  set dτ := fderiv ℝ τ θ (EuclideanSpace.single i 1)
  set Iii := M.fisherMatrix θ i i
  have hIii_ne : Iii ≠ 0 := ne_of_gt hFisher_pos
  -- The three shared identities
  have h_cross :
      ∫ ω, (T ω - μ_T) * M.score θ i ω *
        M.density θ ω ∂M.refMeasure = dτ :=
    M.centered_estimator_score_integral hθ T τ hReg
      hUnbiased hτ_diff hSq i
  have h_var :
      ∫ ω, (T ω - μ_T) ^ 2 * M.density θ ω
        ∂M.refMeasure = M.variance hθ T :=
    (variance_eq_centered M hθ T hReg).symm
  have h_fisher :
      ∫ ω, M.score θ i ω ^ 2 * M.density θ ω
        ∂M.refMeasure = Iii :=
    (M.fisherMatrix_diag_eq_score_sq i).symm
  have hC_pos : 0 < ∫ ω, M.score θ i ω ^ 2 *
      M.density θ ω ∂M.refMeasure := by
    rw [h_fisher]; exact hFisher_pos
  -- Integrability witnesses for Cauchy–Schwarz
  have hf_int :=
    M.centered_sq_integrable hθ T hReg μ_T
  have hg_int := hSq i
  have hfg_int :=
    M.centered_score_integrable hθ T hReg hSq μ_T i
  constructor
  · -- Forward: Var = dτ²/Iii ⟹ efficient
    intro heq
    -- heq: Var(T) = dτ²/Iii, i.e. Var · Iii = dτ²
    -- Recover equality in Cauchy–Schwarz form: B² = A·C
    have hCS_eq :
        (∫ ω, (T ω - μ_T) * M.score θ i ω *
          M.density θ ω ∂M.refMeasure) ^ 2 =
        (∫ ω, (T ω - μ_T) ^ 2 * M.density θ ω
          ∂M.refMeasure) *
        (∫ ω, M.score θ i ω ^ 2 * M.density θ ω
          ∂M.refMeasure) := by
      rw [h_cross, h_var, h_fisher, heq]
      field_simp
    -- Apply the equality characterisation of Cauchy–Schwarz
    obtain ⟨c, hc⟩ := (M.integral_mul_sq_eq_iff hθ
      (fun ω => T ω - μ_T) (M.score θ i)
      hf_int hg_int hfg_int hC_pos).mp hCS_eq
    -- T − μ = c · sᵢ a.e. ⟹ T = μ + c · sᵢ a.e.
    exact ⟨μ_T, c, hc.mono (fun ω h => by linarith)⟩
  · -- Backward: efficient ⟹ Var = dτ²/Iii
    intro ⟨a, b, hab⟩
    -- E[T] = a (since E[sᵢ] = 0 and T = a + b·sᵢ a.e.)
    have hE_T :
        M.toStatisticalModel.expectation hθ T = a := by
      simp only [StatisticalModel.expectation]
      -- Rewrite T·p = (a + b·sᵢ)·p = a·p + b·(sᵢ·p) a.e.
      have hsplit : ∀ᵐ ω ∂M.refMeasure,
          T ω * M.density θ ω =
          a * M.density θ ω +
          b * (M.score θ i ω * M.density θ ω) :=
        hab.mono (fun ω h => by rw [h]; ring)
      rw [integral_congr_ae hsplit,
          integral_add
            ((M.toStatisticalModel.integrable hθ).const_mul a)
            ((M.score_integrable_wrt_density hθ i).const_mul
              b),
          integral_const_mul, integral_const_mul,
          M.toStatisticalModel.density_integral_one θ hθ,
          M.score_expectation_eq_zero hθ i]
      ring
    -- Var(T) = b²·Iii
    have hVar : M.variance hθ T = b ^ 2 * Iii := by
      rw [variance_eq_centered M hθ T hReg, hE_T]
      -- T − a = b·sᵢ a.e., so (T−a)²·p = b²·sᵢ²·p a.e.
      have hae : ∀ᵐ ω ∂M.refMeasure,
          (T ω - a) ^ 2 * M.density θ ω =
          b ^ 2 *
            (M.score θ i ω ^ 2 * M.density θ ω) :=
        hab.mono (fun ω h => by rw [h]; ring)
      rw [integral_congr_ae hae, integral_const_mul,
          h_fisher]
    -- dτ = b·Iii
    -- From covariance–score identity + T = a + b·sᵢ:
    --   dτ = Cov(T, sᵢ) = E[T·sᵢ] (since E[sᵢ]=0)
    --      = E[(a+b·sᵢ)·sᵢ] = a·E[sᵢ] + b·E[sᵢ²]
    --      = 0 + b·Iii = b·Iii
    have hdτ : dτ = b * Iii := by
      rw [show dτ = fderiv ℝ τ θ
        (EuclideanSpace.single i 1) from rfl]
      rw [← M.covariance_score_eq_deriv_target hθ T τ hReg
            hUnbiased hτ_diff i]
      simp only [covariance, StatisticalModel.expectation]
      rw [M.score_expectation_eq_zero hθ i,
          mul_zero, sub_zero]
      -- Rewrite T·sᵢ·p using T = a + b·sᵢ a.e.
      have hae : ∀ᵐ ω ∂M.refMeasure,
          T ω * M.score θ i ω * M.density θ ω =
          a * (M.score θ i ω * M.density θ ω) +
          b * (M.score θ i ω ^ 2 *
            M.density θ ω) :=
        hab.mono (fun ω h => by rw [h]; ring)
      rw [integral_congr_ae hae,
          integral_add
            ((M.score_integrable_wrt_density hθ i).const_mul
              a)
            ((hSq i).const_mul b),
          integral_const_mul, integral_const_mul,
          M.score_expectation_eq_zero hθ i,
          h_fisher]
      ring
    rw [hVar, hdτ]
    field_simp

end RegularStatisticalModel

end InformationGeometry
