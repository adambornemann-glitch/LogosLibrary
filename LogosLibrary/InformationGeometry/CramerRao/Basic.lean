/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: CramerRao/Basic.lean
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
  simp only [f₁, f₂, f₃]-- unused: integral_const_mul, M.toStatisticalModel.density_integral_one θ hθ, ← hE_def
  ring_nf;
  -- Pull constants out of the middle integral
  have mid : ∫ ω, E_T * T ω * M.density θ ω * 2 ∂M.refMeasure =
      2 * E_T * ∫ ω, T ω * M.density θ ω ∂M.refMeasure := by
    rw [show (fun ω => E_T * T ω * M.density θ ω * 2) =
        (fun ω => (2 * E_T) * (T ω * M.density θ ω)) from by ext; ring]
    exact MeasureTheory.integral_const_mul _ _
  -- Pull constant out of the last integral, use ∫ p = 1
  have last : ∫ ω, E_T ^ 2 * M.density θ ω ∂M.refMeasure = E_T ^ 2 := by
    trans (E_T ^ 2 * ∫ ω, M.density θ ω ∂M.refMeasure)
    · exact MeasureTheory.integral_const_mul (E_T ^ 2) (M.density θ)
    · rw [M.toStatisticalModel.density_integral_one θ hθ]; ring
  rw [mid, hE_def, last]
  ring

  end RegularStatisticalModel
  end InformationGeometry
