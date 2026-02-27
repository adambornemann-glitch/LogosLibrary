import LogosLibrary.InformationGeometry.CramerRao.Basic

noncomputable section

open MeasureTheory ENNReal Real Set Filter Finset Metric

open scoped Topology

namespace InformationGeometry

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace RegularStatisticalModel

variable (M : RegularStatisticalModel n Ω)

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

end RegularStatisticalModel
end InformationGeometry
