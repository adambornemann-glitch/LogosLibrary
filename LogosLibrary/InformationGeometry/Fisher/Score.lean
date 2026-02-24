/-
Copyright (c) 2026 Information Geometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann & co.
-/
import LogosLibrary.InformationGeometry.Fisher.StatisticalModel
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.MetricSpace.Basic
--import Mathlib.Analysis.NormedSpace.ContinuousLinearMap becomes
import Mathlib.Analysis.Normed.Operator.Basic
-- Add these for measurability of vector-valued functions:
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
/-!
# The Score Function

The **score function** is the gradient of the log-density with respect to
the parameter.  Its key property — vanishing expectation under the model —
is the seed from which the entire Fisher information metric grows.

## Main results

* `RegularStatisticalModel.hasFDerivAt_integral_density` — differentiation
  under the integral sign for `θ ↦ ∫ ω, p(θ, ω) dμ`, justified by the
  dominated-convergence regularity of `RegularStatisticalModel`.
* `RegularStatisticalModel.integral_partialDensity_eq_zero` — the integral
  of each partial derivative `∂ᵢ p(θ, ·)` vanishes:
  `∫ ω, ∂ᵢ p(θ, ω) dμ = 0`.
* `RegularStatisticalModel.integral_score_density_eq_zero` —
  `∫ ω, sᵢ(θ, ω) · p(θ, ω) dμ = 0`, i.e. `E_θ[scoreᵢ] = 0`.

## Proof strategy

The argument is the classical one:

1. **Normalisation** gives `∫ ω, p(θ, ω) dμ = 1` for all `θ ∈ Θ`.
2. **Differentiating** both sides in direction `eᵢ`: the RHS is constant
   so its derivative is `0`.
3. **Leibniz rule** (differentiation under the integral sign): the LHS
   derivative equals `∫ ω, ∂ᵢ p(θ, ω) dμ`, justified by
   `hasFDerivAt_integral_of_dominated_of_fderiv_le` from
   `Mathlib.Analysis.Calculus.ParametricIntegral` together with the
   integrable derivative bound from `RegularStatisticalModel`.
4. **Score identity**: `∂ᵢ p(θ, ω) = sᵢ(θ, ω) · p(θ, ω)` a.e.,
   so `∫ sᵢ · p dμ = ∫ ∂ᵢp dμ = 0`.

This is the first genuine exchange of limits in the development.  Every
subsequent result (Fisher metric, Cramér–Rao, …) traces back to it.

## References

* S. Amari, *Information Geometry and Its Applications*, §2.1, 2016.
-/

noncomputable section

open MeasureTheory ENNReal Real Set Filter Topology Metric

namespace InformationGeometry

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace RegularStatisticalModel

variable (M : RegularStatisticalModel n Ω)

/-! ### Auxiliary lemmas -/

/-- Every `θ ∈ Θ` has a ball contained in `Θ` (since `Θ` is open). -/
private theorem exists_ball_subset {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) :
    ∃ ε > 0, Metric.ball θ ε ⊆ M.paramDomain :=
  Metric.isOpen_iff.mp M.isOpen_paramDomain θ hθ

/-- The density at any parameter near `θ₀` is `AEStronglyMeasurable`.
This is the `∀ᶠ` version needed by the parametric integral lemma. -/
private theorem ae_density_meas_near {θ₀ : ParamSpace n}
    (hθ₀ : θ₀ ∈ M.paramDomain) :
    ∀ᶠ θ in 𝓝 θ₀,
      AEStronglyMeasurable (M.density θ) M.refMeasure := by
  obtain ⟨ε, hε, hball⟩ := M.exists_ball_subset hθ₀
  exact eventually_of_mem (Metric.ball_mem_nhds θ₀ hε)
    (fun θ hθ => (M.toStatisticalModel.density_measurable θ
      (hball hθ)).aestronglyMeasurable
        (μ := M.refMeasure))


/-- The Fréchet derivative `θ ↦ fderiv ℝ (· ↦ p(·, ω)) θ` at `θ₀`
is `AEStronglyMeasurable` in `ω`.

This is needed as a hypothesis for
`hasFDerivAt_integral_of_dominated_of_fderiv_le`. We obtain it from
the derivative bound: the derivative is dominated by an integrable
function, so it is integrable, hence `AEStronglyMeasurable`. -/
private theorem fderiv_aestronglyMeasurable
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain) :
    AEStronglyMeasurable
      (fun ω => fderiv ℝ (fun θ' => M.density θ' ω) θ₀)
      M.refMeasure :=
  M.density_fderiv_aestronglyMeasurable θ₀ hθ₀



/-! ### Differentiation under the integral sign -/

/-- **Leibniz integral rule.** Under `RegularStatisticalModel` conditions,
the map `θ ↦ ∫ ω, p(θ, ω) dμ` has Fréchet derivative
`∫ ω, D_θ p(θ₀, ω) dμ` at `θ₀ ∈ Θ`.

This is the load-bearing application of
`hasFDerivAt_integral_of_dominated_of_fderiv_le`. -/
theorem hasFDerivAt_integral_density
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain) :
    HasFDerivAt
      (fun θ => ∫ ω, M.density θ ω ∂M.refMeasure)
      (∫ ω, fderiv ℝ (fun θ' => M.density θ' ω) θ₀
        ∂M.refMeasure)
      θ₀ := by
  obtain ⟨ε, hε, hball⟩ := M.exists_ball_subset hθ₀
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    hε
    -- (hF_meas) ∀ᶠ θ in 𝓝 θ₀, AEStronglyMeasurable (p θ) μ
    (M.ae_density_meas_near hθ₀)
    -- (hF_int) Integrable (p θ₀) μ
    (M.toStatisticalModel.integrable hθ₀)
    -- (hF'_meas) AEStronglyMeasurable (D_θ p(θ₀, ·)) μ
    (M.fderiv_aestronglyMeasurable hθ₀)
    -- (h_bound) ∀ᵐ ω, ∀ θ ∈ ball θ₀ ε, ‖D_θ p(θ,ω)‖ ≤ B(ω)
    (ae_of_all _ (fun ω θ hθ =>
      M.density_fderiv_norm_le θ (hball hθ) ω))
    -- (bound_integrable) Integrable B μ
    M.derivBound_integrable
    -- (h_diff) ∀ᵐ ω, ∀ θ ∈ ball θ₀ ε, HasFDerivAt (· ↦ p(·,ω)) …
    (ae_of_all _ (fun ω θ hθ =>
      (M.toStatisticalModel.density_differentiableAt
        (hball hθ) ω).hasFDerivAt))

/-- The derivative of the normalisation integral `θ ↦ ∫ p(θ,·) dμ`
is identically zero, since that integral is the constant `1`. -/
theorem fderiv_integral_density_eq_zero
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain) :
    fderiv ℝ (fun θ => ∫ ω, M.density θ ω ∂M.refMeasure)
      θ₀ = 0 := by
  -- θ ↦ ∫ p(θ,·) dμ  =ᶠ  θ ↦ 1  near θ₀.
  have hcong : (fun θ => ∫ ω, M.density θ ω ∂M.refMeasure)
      =ᶠ[𝓝 θ₀] fun _ => (1 : ℝ) := by
    obtain ⟨ε, hε, hball⟩ := M.exists_ball_subset hθ₀
    exact eventually_of_mem (Metric.ball_mem_nhds θ₀ hε)
      (fun θ hθ =>
        M.toStatisticalModel.density_integral_one θ
          (hball hθ))
  -- Two functions that agree locally have the same fderiv.
  rw [Filter.EventuallyEq.fderiv_eq hcong]
  exact fderiv_const_apply 1

/-! ### Integral of partial derivatives vanishes -/

/-- The Bochner integral of the Fréchet derivative of the density
is zero: `∫ ω, D_θ p(θ₀, ω) dμ = 0`.

This is the ContinuousLinearMap version; the component version
`integral_partialDensity_eq_zero` follows by evaluation on `eᵢ`. -/
theorem integral_fderiv_density_eq_zero
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain) :
    ∫ ω, fderiv ℝ (fun θ' => M.density θ' ω) θ₀
      ∂M.refMeasure = 0 := by
  -- Leibniz: fderiv (∫ p dμ) θ₀ = ∫ (fderiv p) dμ
  have hL := (M.hasFDerivAt_integral_density hθ₀).fderiv
  -- Constant: fderiv (∫ p dμ) θ₀ = 0
  have hZ := M.fderiv_integral_density_eq_zero hθ₀
  -- Combine: ∫ (fderiv p) dμ = fderiv (∫ p dμ) θ₀ = 0
  rw [← hL, hZ]

/-- For each coordinate direction `i`, the integral of the `i`-th
partial derivative of the density vanishes:
  `∫ ω, ∂ᵢ p(θ, ω) dμ = 0`.

This is obtained by evaluating `integral_fderiv_density_eq_zero` on the
standard basis vector `eᵢ`. -/
theorem integral_partialDensity_eq_zero
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain)
    (i : Fin n) :
    ∫ ω, M.partialDensity θ₀ i ω ∂M.refMeasure = 0 := by
  have h := M.integral_fderiv_density_eq_zero hθ₀
  simp only [partialDensity]
  -- Use: (∫ φ dμ)(v) = ∫ (φ v) dμ
  rw [← ContinuousLinearMap.integral_apply _ (EuclideanSpace.single i 1)]
  · rw [h]
    simp
  · -- Integrability of fderiv
    refine ⟨M.fderiv_aestronglyMeasurable hθ₀, ?_⟩
    -- ∫⁻ ‖fderiv‖ < ∞
    calc
      ∫⁻ ω, ‖fderiv ℝ (fun θ' => M.density θ' ω) θ₀‖₊ ∂M.refMeasure
        ≤ ∫⁻ ω, ‖M.derivBound ω‖₊ ∂M.refMeasure := by
          apply lintegral_mono
          intro ω
          simp only
          apply ENNReal.coe_le_coe.mpr
          rw [Real.nnnorm_of_nonneg (M.derivBound_nonneg ω)]
          have h := M.density_fderiv_norm_le θ₀ hθ₀ ω
          exact h
      _ < ∞ := by
          have := M.derivBound_integrable.hasFiniteIntegral
          exact this

/-! ### Score has vanishing expectation -/

/-- The `i`-th partial derivative of the density equals the score
times the density: `∂ᵢ p(θ, ω) = sᵢ(θ, ω) · p(θ, ω)` whenever
`p(θ, ω) > 0`. -/
theorem partialDensity_eq_score_mul_density
    {θ₀ : ParamSpace n} (i : Fin n) (ω : Ω)
    (hpos : 0 < M.density θ₀ ω) :
    M.partialDensity θ₀ i ω =
      M.score θ₀ i ω * M.density θ₀ ω := by
  simp only [score, partialDensity]
  exact (div_mul_cancel₀ _ (ne_of_gt hpos)).symm

/-- `∂ᵢ p(θ, ω) = sᵢ(θ, ω) · p(θ, ω)` holds a.e. under the
reference measure. -/
theorem partialDensity_eq_score_mul_density_ae
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain)
    (i : Fin n) :
    ∀ᵐ ω ∂M.refMeasure,
      M.partialDensity θ₀ i ω =
        M.score θ₀ i ω * M.density θ₀ ω := by
  filter_upwards [M.toStatisticalModel.density_pos_ae θ₀ hθ₀]
    with ω hω
  exact M.partialDensity_eq_score_mul_density i ω hω

/-- **The fundamental identity of the score function.**
The expectation of the `i`-th score component under the model
distribution vanishes:
  `E_θ[sᵢ] = ∫ ω, sᵢ(θ, ω) · p(θ, ω) dμ = 0`.

This follows from:
  `∫ sᵢ · p dμ = ∫ ∂ᵢp dμ = 0`
where the first equality uses `∂ᵢ p = sᵢ · p` (a.e.) and
the second is `integral_partialDensity_eq_zero`. -/
theorem score_expectation_eq_zero
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain)
    (i : Fin n) :
    ∫ ω, M.score θ₀ i ω * M.density θ₀ ω
      ∂M.refMeasure = 0 := by
  -- sᵢ · p = (∂ᵢp / p) · p = ∂ᵢp  a.e. (where p > 0)
  have hae := M.partialDensity_eq_score_mul_density_ae hθ₀ i
  -- ∫ sᵢ · p dμ = ∫ ∂ᵢp dμ  (by a.e. equality)
  rw [integral_congr_ae (hae.mono (fun ω h => h.symm))]
  exact M.integral_partialDensity_eq_zero hθ₀ i

/-- The score expectation in the `StatisticalModel.expectation` form:
  `E_θ[sᵢ] = 0`. -/
theorem score_expectation_eq_zero'
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain)
    (i : Fin n) :
    M.toStatisticalModel.expectation hθ₀
      (fun ω => M.score θ₀ i ω) = 0 := by
  exact M.score_expectation_eq_zero hθ₀ i

/-! ### Integrability of the score under the model -/

/-- The `i`-th partial derivative of the density is integrable
w.r.t. the reference measure. This follows from the derivative
bound: `‖∂ᵢp(θ, ω)‖ ≤ ‖D_θ p(θ, ω)‖ ≤ B(ω)`. -/
theorem partialDensity_integrable
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain)
    (i : Fin n) :
    Integrable (M.partialDensity θ₀ i) M.refMeasure := by
  apply Integrable.mono M.derivBound_integrable
  · -- AEStronglyMeasurable: partial derivative is measurable
    -- since it is a continuous linear image of the fderiv
    apply AEStronglyMeasurable.apply_continuousLinearMap
    exact M.fderiv_aestronglyMeasurable hθ₀
  · -- ‖∂ᵢp(θ₀, ω)‖ ≤ B(ω) a.e.
    apply ae_of_all
    intro ω
    simp only [partialDensity]
    calc ‖fderiv ℝ (fun θ' => M.density θ' ω) θ₀
            (EuclideanSpace.single i 1)‖
        ≤ ‖fderiv ℝ (fun θ' => M.density θ' ω) θ₀‖ *
            ‖EuclideanSpace.single i (1 : ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (fun θ' => M.density θ' ω) θ₀‖ *
            1 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [EuclideanSpace.norm_single]
          simp
      _ = ‖fderiv ℝ (fun θ' => M.density θ' ω) θ₀‖ :=
          mul_one _
      _ ≤ M.derivBound ω :=
          M.density_fderiv_norm_le θ₀ hθ₀ ω
      _ = ‖M.derivBound ω‖ := by
          rw [Real.norm_eq_abs,
              abs_of_nonneg (M.derivBound_nonneg ω)]

/-- The `i`-th partial derivative of the density is
`AEStronglyMeasurable` w.r.t. the reference measure.

The partial derivative is defined as a continuous linear map
evaluation of the Fréchet derivative, and `AEStronglyMeasurable`
is preserved under CLM application. -/
theorem partialDensity_aestronglyMeasurable
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain)
    (i : Fin n) :
    AEStronglyMeasurable (M.partialDensity θ₀ i) M.refMeasure := by
  -- partialDensity is CLM evaluation: ω ↦ (fderiv p)(eᵢ)
  -- AEStronglyMeasurable is preserved under CLM application
  apply AEStronglyMeasurable.apply_continuousLinearMap
  exact M.fderiv_aestronglyMeasurable hθ₀

/-- The `i`-th score component is integrable under the model
distribution `P_θ`, i.e., `∫ |sᵢ(θ, ω)| · p(θ, ω) dμ < ∞`.

This follows from square-integrability of the score plus
integrability of the density (Cauchy–Schwarz). -/
theorem score_integrable_wrt_density
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain)
    (i : Fin n) :
    Integrable (fun ω => M.score θ₀ i ω * M.density θ₀ ω)
      M.refMeasure := by
  -- sᵢ · p = ∂ᵢp  a.e. (where p > 0),
  -- and ∂ᵢp is integrable, so sᵢ · p is integrable.
  exact (M.partialDensity_integrable hθ₀ i).congr
    (M.partialDensity_eq_score_mul_density_ae hθ₀ i)

/-! ### Vector-valued score -/

/-- The full score vector `s(θ, ω) ∈ ℝⁿ`, whose `i`-th component
is `sᵢ(θ, ω) = ∂ᵢ log p(θ, ω)`. -/
def scoreVec (θ : ParamSpace n) (ω : Ω) :
    ParamSpace n :=
  fun i => M.score θ i ω

/-- Each component of the score vector has vanishing expectation. -/
theorem scoreVec_expectation_eq_zero
    {θ₀ : ParamSpace n} (hθ₀ : θ₀ ∈ M.paramDomain)
    (i : Fin n) :
    ∫ ω, M.scoreVec θ₀ ω i * M.density θ₀ ω
      ∂M.refMeasure = 0 := by
  simp only [scoreVec]
  exact M.score_expectation_eq_zero hθ₀ i

end RegularStatisticalModel

end InformationGeometry
