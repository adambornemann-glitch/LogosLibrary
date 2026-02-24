/-
Copyright (c) 2026 Information Geometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann & co.
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
--import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Statistical Models

A **statistical model** is a smooth parametric family of probability
distributions on a measurable space. This is the foundational object
of information geometry: the parameter space becomes a smooth manifold,
and the Fisher information equips it with a canonical Riemannian metric.

## Main definitions

* `InformationGeometry.StatisticalModel` — a smooth `n`-parameter family of
  probability densities on a sample space `Ω`, relative to a σ-finite
  reference measure.
* `StatisticalModel.measure` — the probability measure at parameter `θ`.
* `StatisticalModel.logDensity` — the log-likelihood `log p(ω | θ)`.
* `InformationGeometry.RegularStatisticalModel` — a statistical model
  equipped with the dominated-convergence regularity needed to define the
  Fisher information and differentiate under the integral sign.

## Design decisions

**Parameter space.** We model the parameter space as an open subset of
`EuclideanSpace ℝ (Fin n)`.  This keeps the first formalization concrete
while remaining compatible with Mathlib's `ContDiffOn`, `fderiv`, and
inner-product-space infrastructure. A future generalization to abstract
smooth manifolds can wrap this via charts.

**Density codomain.** The density is `ℝ`-valued (not `ℝ≥0∞`), because the
calculus layer — `log`, `fderiv`, inner products — is native to `ℝ`.
The bridge to measure theory uses `ENNReal.ofReal`. Nonnegativity is
carried as a field.

**Regularity.** The base `StatisticalModel` carries only smoothness of
`θ ↦ p(θ, ω)` per `ω` and measurability per `θ`. The heavier conditions
required for the Fisher metric (dominated convergence bounds, square-
integrability of the score) are isolated in `RegularStatisticalModel`,
following the Mathlib pattern of layered typeclasses.

**Field `𝕜`.** The density/score layer is intrinsically real. The
*geometric* layer (Fisher metric as an inner product on tangent spaces)
will be parametrized over `𝕜 : Type* [RCLike 𝕜]` in `FisherMetric.lean`,
so that the same definitions recover the classical Fisher metric at
`𝕜 = ℝ` and the quantum Fisher metric at `𝕜 = ℂ`.

## References

* S. Amari, *Information Geometry and Its Applications*, Springer, 2016.
* S. Amari, H. Nagaoka, *Methods of Information Geometry*, AMS, 2000.
* N. N. Čencov, *Statistical Decision Rules and Optimal Inference*, AMS, 1982.
* R. A. Fisher, "On the mathematical foundations of theoretical statistics",
  *Phil. Trans. Roy. Soc. London A* **222** (1922), 309–368.
-/

noncomputable section

open MeasureTheory ENNReal Real Set Filter

open scoped Topology

namespace InformationGeometry

/-! ### The parameter space -/

/-- Notation alias for the `n`-dimensional real Euclidean parameter space. -/
abbrev ParamSpace (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-! ### Statistical model -/

/-- A `StatisticalModel n Ω` is a smooth `n`-parameter family of probability
densities on a measurable space `Ω`, specified relative to a σ-finite
reference (dominating) measure.

The density `p : Θ → Ω → ℝ` is required to be:
- **nonneg** and **a.e. positive** for each parameter in the domain,
- **measurable** in `ω` for each `θ`,
- **smooth** (`C^∞`) in `θ` for each `ω`,
- **normalised**: `∫ ω, p(θ, ω) dμ = 1` for each `θ` in the domain. -/
structure StatisticalModel (n : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- Open parameter domain `Θ ⊆ ℝⁿ`. -/
  paramDomain : Set (ParamSpace n)
  /-- `Θ` is open in `ℝⁿ`. -/
  isOpen_paramDomain : IsOpen paramDomain
  /-- `Θ` is nonempty. -/
  nonempty_paramDomain : paramDomain.Nonempty
  /-- Reference (dominating) measure on the sample space. -/
  refMeasure : Measure Ω
  /-- The reference measure is σ-finite. -/
  sigmaFinite_refMeasure : SigmaFinite refMeasure
  /-- The density `p(θ, ω)` with respect to `refMeasure`. -/
  density : ParamSpace n → Ω → ℝ
  /-- `p(θ, ω) ≥ 0` for all `θ ∈ Θ` and `ω`. -/
  density_nonneg : ∀ θ ∈ paramDomain, ∀ ω, 0 ≤ density θ ω
  /-- `ω ↦ p(θ, ω)` is measurable for each `θ ∈ Θ`. -/
  density_measurable : ∀ θ ∈ paramDomain, Measurable (density θ)
  /-- `∫ ω, p(θ, ω) dμ = 1` for each `θ ∈ Θ`. -/
  density_integral_one :
    ∀ θ ∈ paramDomain, ∫ ω, density θ ω ∂refMeasure = 1
  /-- `p(θ, ω) > 0` for `μ`-a.e. `ω`, for each `θ ∈ Θ`.
  This is equivalent to the model being mutually absolutely continuous
  with the reference measure. -/
  density_pos_ae :
    ∀ θ ∈ paramDomain, ∀ᵐ ω ∂refMeasure, 0 < density θ ω
  /-- `θ ↦ p(θ, ω)` is `C^∞` on `Θ` for each `ω`. -/
  density_smooth :
    ∀ ω, ContDiffOn ℝ ⊤ (fun θ => density θ ω) paramDomain

attribute [instance] StatisticalModel.sigmaFinite_refMeasure

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace StatisticalModel

variable (M : StatisticalModel n Ω)

/-! ### Integrability -/

/-- The density at any `θ ∈ Θ` is integrable with respect to the reference
measure.  Follows from `density_integral_one`: the Bochner integral of a
non-integrable function is `0`, but ours equals `1`. -/
theorem integrable {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) :
    Integrable (M.density θ) M.refMeasure := by
  by_contra h
  have h1 := M.density_integral_one θ hθ
  rw [integral_undef h] at h1
  exact one_ne_zero h1.symm

/-- The density at `θ ∈ Θ` is `AEStronglyMeasurable`. -/
theorem aestronglyMeasurable {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) :
    AEStronglyMeasurable (M.density θ) M.refMeasure :=
  (M.density_measurable θ hθ).aestronglyMeasurable
    (μ := M.refMeasure)

/-! ### The induced probability measure -/

/-- The probability measure on `Ω` induced by parameter `θ`:
  `P_θ = p(θ, ·) dμ`. -/
def measure {θ : ParamSpace n} (_hθ : θ ∈ M.paramDomain) :
    Measure Ω :=
  M.refMeasure.withDensity (fun ω => ENNReal.ofReal (M.density θ ω))

/-- `M.measure hθ` is a probability measure. -/
theorem isProbabilityMeasure {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) :
    IsProbabilityMeasure (M.measure hθ) := by
  constructor
  show M.refMeasure.withDensity
    (fun ω => ENNReal.ofReal (M.density θ ω))
    Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  -- Goal: ∫⁻ ω, ofReal (p θ ω) ∂μ = 1
  -- Step 1: bridge Bochner ↔ lintegral for nonneg f
  have hnn : 0 ≤ᵐ[M.refMeasure] M.density θ :=
    ae_of_all _ (M.density_nonneg θ hθ)
  have hm : AEStronglyMeasurable (M.density θ)
      M.refMeasure :=
    (M.density_measurable θ hθ).aestronglyMeasurable
      (μ := M.refMeasure)
  have h_bridge :=
    integral_eq_lintegral_of_nonneg_ae hnn hm
  rw [M.density_integral_one θ hθ] at h_bridge
  -- h_bridge : 1 = (∫⁻ ω, ofReal (p θ ω) ∂μ).toReal
  -- Step 2: lintegral ≠ ⊤ from integrability
  have h_ne_top :
      ∫⁻ ω, ENNReal.ofReal (M.density θ ω)
        ∂M.refMeasure ≠ ⊤ := ne_of_lt <|
    lt_of_le_of_lt
      (lintegral_ofReal_le_lintegral_enorm _)
      (M.integrable hθ).hasFiniteIntegral
  -- Step 3: toReal L = 1 ∧ L ≠ ⊤ ⟹ L = 1
  rw [← ENNReal.ofReal_toReal h_ne_top,
      h_bridge.symm, ofReal_one]

/-! ### Log-density (log-likelihood) -/

/-- The log-density `log p(θ, ω)`, defined for all `θ` and `ω`.
Where `p(θ, ω) ≤ 0` this returns `0` by `Real.log`'s junk value,
but the a.e.-positivity guarantee makes this harmless. -/
def logDensity (θ : ParamSpace n) (ω : Ω) : ℝ :=
  Real.log (M.density θ ω)

/-- `ω ↦ log p(θ, ω)` is `AEMeasurable` for `θ ∈ Θ`. -/
theorem logDensity_aemeasurable {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) :
    AEMeasurable (M.logDensity θ) M.refMeasure :=
  -- `Measurable.log` composes log-measurability with `density_measurable`.
  ((M.density_measurable θ hθ).log).aemeasurable

/-- The fundamental identity `exp (log p(θ, ω)) = p(θ, ω)` holds
a.e. under the reference measure for `θ ∈ Θ`. -/
theorem exp_logDensity_eq_ae {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) :
    ∀ᵐ ω ∂M.refMeasure, Real.exp (M.logDensity θ ω) =
      M.density θ ω := by
  filter_upwards [M.density_pos_ae θ hθ] with ω hω
  exact Real.exp_log hω

/-! ### Expectation under the model -/

/-- Expectation of `f` under `P_θ`.  This is notation-friendly sugar
for `∫ ω, f ω ∂M.measure hθ`, expressed in the density form
`∫ ω, f ω * p(θ, ω) dμ` which is often more convenient for proofs. -/
def expectation {θ : ParamSpace n} (_hθ : θ ∈ M.paramDomain)
    (f : Ω → ℝ) : ℝ :=
  ∫ ω, f ω * M.density θ ω ∂M.refMeasure

@[simp]
theorem expectation_const_one {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) :
    M.expectation hθ (fun _ => 1) = 1 := by
  simp only [expectation, one_mul]
  exact M.density_integral_one θ hθ

/-! ### Smoothness helpers -/

/-- The density is continuous in `θ` on the domain, for each `ω`. -/
theorem density_continuousOn (ω : Ω) :
    ContinuousOn (fun θ => M.density θ ω) M.paramDomain :=
  (M.density_smooth ω).continuousOn

/-- The density is differentiable in `θ` at each interior point,
for each `ω`. Since `Θ` is open, membership suffices. -/
theorem density_differentiableAt {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (ω : Ω) :
    DifferentiableAt ℝ (fun θ' => M.density θ' ω) θ := by
  exact ((M.density_smooth ω).differentiableOn le_top).differentiableAt
    (M.isOpen_paramDomain.mem_nhds hθ)

/-! ### Identifiability -/

/-- A statistical model is **identifiable** if the map `θ ↦ P_θ` is
injective: distinct parameters yield distinct distributions. -/
def Identifiable : Prop :=
  ∀ ⦃θ₁ θ₂⦄, θ₁ ∈ M.paramDomain → θ₂ ∈ M.paramDomain →
    (∀ᵐ ω ∂M.refMeasure, M.density θ₁ ω = M.density θ₂ ω) →
    θ₁ = θ₂

end StatisticalModel

/-! ### Regular statistical models -/

/-- A `RegularStatisticalModel` extends `StatisticalModel` with the
analytic regularity needed to define the Fisher information metric:

1. A **dominating function** for the parameter-derivatives of the density,
   ensuring that differentiation under the integral sign is justified via
   dominated convergence.
2. **Square-integrability** of the score function
   `∂ᵢ log p(θ, ω)` = `∂ᵢ p(θ, ω) / p(θ, ω)`, which guarantees
   that the Fisher information matrix has finite entries.

These conditions are automatically satisfied by exponential families
and by any parametric family with compactly supported parameter domain
and continuous, bounded derivatives. -/
structure RegularStatisticalModel (n : ℕ) (Ω : Type*)
    [MeasurableSpace Ω] extends StatisticalModel n Ω where
  /-- Integrable upper bound on `‖∂_θ p(θ, ω)‖` uniform in `θ`. -/
  derivBound : Ω → ℝ
  /-- The bound is integrable w.r.t. the reference measure. -/
  derivBound_integrable :
    Integrable derivBound refMeasure
  /-- The bound is nonneg. -/
  derivBound_nonneg : ∀ ω, 0 ≤ derivBound ω
  /-- `‖D_θ p(θ, ω)‖ ≤ B(ω)` for all `θ ∈ Θ` and all `ω`. -/
  density_fderiv_norm_le :
    ∀ θ ∈ paramDomain, ∀ ω,
      ‖fderiv ℝ (fun θ' => density θ' ω) θ‖ ≤ derivBound ω
  /-- For each direction `i`, the score component
  `∂ᵢ log p(θ, ·)` is square-integrable under `P_θ`.
  Equivalently, `E_θ[(∂ᵢ p / p)²] < ∞`. -/
  score_sq_integrable :
    ∀ θ ∈ paramDomain, ∀ i : Fin n,
      Integrable
        (fun ω => ((fderiv ℝ (fun θ' => density θ' ω) θ
            (EuclideanSpace.single i 1)) /
              density θ ω) ^ 2)
        refMeasure
  /-- The Fréchet derivative of the density is ae strongly measurable -/
  density_fderiv_aestronglyMeasurable :
    ∀ θ ∈ paramDomain,
      AEStronglyMeasurable
        (fun ω => fderiv ℝ (fun θ' => density θ' ω) θ)
        refMeasure

namespace RegularStatisticalModel

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (M : RegularStatisticalModel n Ω)

/-- The `i`-th partial derivative of the density at `(θ, ω)`. -/
def partialDensity (θ : ParamSpace n) (i : Fin n) (ω : Ω) : ℝ :=
  fderiv ℝ (fun θ' => M.density θ' ω) θ
    (EuclideanSpace.single i 1)

/-- The `i`-th component of the score function at `(θ, ω)`:
  `sᵢ(θ, ω) = ∂ᵢ log p(θ, ω) = (∂ᵢ p(θ, ω)) / p(θ, ω)`. -/
def score (θ : ParamSpace n) (i : Fin n) (ω : Ω) : ℝ :=
  M.partialDensity θ i ω / M.density θ ω

/-- The score is square-integrable under the model distribution. -/
theorem score_memLp {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (i : Fin n) :
    Integrable (fun ω => M.score θ i ω ^ 2) M.refMeasure := by
  exact M.score_sq_integrable θ hθ i

end RegularStatisticalModel

end InformationGeometry
