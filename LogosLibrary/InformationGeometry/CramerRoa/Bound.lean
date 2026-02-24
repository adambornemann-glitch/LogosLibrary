import LogosLibrary.InformationGeometry.CramerRoa.CauchySchwarz

noncomputable section

open MeasureTheory ENNReal Real Set Filter Finset Metric

open scoped Topology

namespace InformationGeometry

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace RegularStatisticalModel

variable (M : RegularStatisticalModel n Ω)

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
