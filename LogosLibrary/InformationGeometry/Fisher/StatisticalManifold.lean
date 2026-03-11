/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Fisher/StatisticalManifold.lean
-/
import LogosLibrary.InformationGeometry.Fisher.FisherMetric

/-!
# Statistical Manifolds

A **statistical manifold** is a smooth manifold whose points index a
family of probability distributions, equipped with the Fisher–Rao
metric as its canonical Riemannian structure.  This file assembles the
construction: a `RegularStatisticalModel` with smooth Fisher entries
gives rise to a `StatisticalManifold` carrying a `RiemannianMetric`.

## Main definitions

* `InformationGeometry.StatisticalManifold` —
  a regular statistical model with global score-injectivity, score
  square-integrability, and smooth Fisher matrix entries; i.e., the
  full package needed for the Fisher–Rao metric to be a well-defined
  Riemannian metric on the parameter space.
* `StatisticalManifold.fisherMetric` — the Fisher–Rao Riemannian metric.
* `StatisticalManifold.fisherInnerProduct` — the Fisher inner product
  `⟨v, w⟩_θ = g_θ(v, w)` at a specified parameter.
* `StatisticalManifold.fisherDist` — the infinitesimal Fisher distance
  `‖v‖_θ = √(g_θ(v, v))`.

## Main results

* `fisherMetric_isRiemannian` — the Fisher metric is symmetric,
  positive definite, and smooth (holds by construction).
* `fisherInnerProduct_eq_expectation` — the inner product of tangent
  vectors equals the covariance of the corresponding directional scores:
  `⟨v, w⟩_θ = E_θ[⟨v, s⟩ · ⟨w, s⟩]`.
* `fisherInnerProduct_eq_sum` — matrix expansion
  `⟨v, w⟩_θ = ∑_{ij} vᵢ wⱼ g_{ij}(θ)`.
* `fisherDist_eq_zero_iff` — `‖v‖_θ = 0 ⟺ v = 0`.

## Design notes

The `StatisticalManifold` structure is intentionally thin: it is a
`RegularStatisticalModel` satisfying `SmoothFisherModel`, with no
additional data.  Every geometric quantity (metric, connection,
curvature, geodesics) is derived, not stored.  This follows the
Mathlib principle of lean structures with rich APIs.

The **dimension** of the manifold is the natural number `n`, which
is the number of parameters.  The tangent space at each point is
canonically `ParamSpace n = EuclideanSpace ℝ (Fin n)`.

## Future work

* `KLDivergence.lean` — the Fisher metric as the Hessian of the
  KL divergence: `D_KL(p_θ ‖ p_{θ+δ}) ≈ ½ δᵀ G(θ) δ`.
* `CramerRao.lean` — the Cramér–Rao inequality
  `Cov_θ(T) ≥ G(θ)⁻¹` for unbiased estimators `T`.
* `Connections.lean` — the α-connections and the dually flat
  structure of exponential/mixture families.
* `Chentsov.lean` — uniqueness of the Fisher metric among all
  metrics invariant under sufficient statistics (Markov morphisms).

## References

* S. Amari, *Information Geometry and Its Applications*, Ch. 2–3, 2016.
* S. Amari, H. Nagaoka, *Methods of Information Geometry*, AMS, 2000.
* N. N. Čencov, *Statistical Decision Rules and Optimal Inference*,
  AMS, 1982.
* L. L. Campbell, "An extended Čencov characterization of the
  information metric", *Proc. Amer. Math. Soc.* **98** (1986), 135–141.
-/

noncomputable section

open MeasureTheory ENNReal Real Set Filter Finset

open scoped Topology

namespace InformationGeometry

/-! ### The statistical manifold -/

/-- A `StatisticalManifold n Ω` is a regular statistical model on
`Ω` with `n` parameters, satisfying the global regularity conditions
that make the Fisher–Rao metric a genuine Riemannian metric on the
parameter space:

1. **Score-injectivity** at every `θ ∈ Θ` (positive definiteness),
2. **Score square-integrability** under the model at every `θ ∈ Θ`
   (finite Fisher entries),
3. **Smooth dependence** of the Fisher matrix on `θ` (Riemannian
   smoothness).

The `StatisticalManifold` is the setting in which one can define
geodesics, curvature, and prove the major theorems of information
geometry (Cramér–Rao, Chentsov, etc.). -/
structure StatisticalManifold (n : ℕ) (Ω : Type*)
    [MeasurableSpace Ω] extends
    RegularStatisticalModel n Ω where
  /-- Score-injectivity at every parameter. -/
  scoreInjective_everywhere :
    ∀ θ ∈ paramDomain,
      toRegularStatisticalModel.ScoreInjective θ
  /-- Score square-integrability under the model, everywhere. -/
  scoreSqIntegrable_everywhere :
    ∀ θ ∈ paramDomain,
      toRegularStatisticalModel.ScoreSqIntegrableModel θ
  /-- Integrability of the directional-score bilinear integrand. -/
  directionalScoreIntegrable_everywhere :
    ∀ θ ∈ paramDomain, ∀ w : ParamSpace n,
      Integrable
        (fun ω =>
          toRegularStatisticalModel.directionalScore θ w ω *
          toRegularStatisticalModel.directionalScore θ w ω *
          density θ ω) refMeasure
  /-- Each Fisher matrix entry varies `C^∞`-ly in `θ`. -/
  fisherMatrix_smooth_everywhere :
    ∀ i j : Fin n,
      ContDiffOn ℝ ⊤
        (fun θ => toRegularStatisticalModel.fisherMatrix θ i j)
        paramDomain

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace StatisticalManifold

variable (S : StatisticalManifold n Ω)

/-! ### Access to the underlying structures -/

/-- The underlying `RegularStatisticalModel`. -/
abbrev model : RegularStatisticalModel n Ω :=
  S.toRegularStatisticalModel

/-- The parameter domain `Θ ⊆ ℝⁿ`. -/
abbrev domain : Set (ParamSpace n) := S.paramDomain

/-- The dimension of the manifold. -/
def dim : ℕ := n

/-! ### The SmoothFisherModel instance -/

/-- A `StatisticalManifold` automatically satisfies
`SmoothFisherModel`. -/
def smoothFisherModel :
    S.model.SmoothFisherModel where
  scoreSqIntegrable := S.scoreSqIntegrable_everywhere
  scoreInjective := S.scoreInjective_everywhere
  directionalScoreIntegrable :=
    S.directionalScoreIntegrable_everywhere
  fisherMatrix_smooth := S.fisherMatrix_smooth_everywhere

/-! ### The Fisher–Rao metric -/

/-- The Fisher–Rao metric on the statistical manifold. -/
def fisherMetric : RiemannianMetric n :=
  S.model.fisherRiemannianMetric S.smoothFisherModel

/-- The Fisher metric matrix at `θ` is the Fisher information
matrix of the underlying model. -/
@[simp]
theorem fisherMetric_matrix (θ : ParamSpace n) (i j : Fin n) :
    S.fisherMetric.metricMatrix θ i j =
      S.model.fisherMatrix θ i j :=
  rfl

/-- The Fisher metric is symmetric at every parameter. -/
theorem fisherMetric_symm {θ : ParamSpace n}
    (hθ : θ ∈ S.domain) (i j : Fin n) :
    S.fisherMetric.metricMatrix θ i j =
      S.fisherMetric.metricMatrix θ j i :=
  S.fisherMetric.metricMatrix_symm θ hθ i j

/-- The Fisher metric is positive definite at every parameter. -/
theorem fisherMetric_pos_def {θ : ParamSpace n}
    (hθ : θ ∈ S.domain) {v : ParamSpace n} (hv : v ≠ 0) :
    0 < S.fisherMetric.eval θ v v :=
  S.fisherMetric.eval_pos hθ hv

/-- Each Fisher metric entry is smooth on the domain. -/
theorem fisherMetric_smooth (i j : Fin n) :
    ContDiffOn ℝ ⊤ (fun θ => S.fisherMetric.metricMatrix θ i j)
      S.domain :=
  S.fisherMetric.metricMatrix_smooth i j

/-! ### The Fisher inner product -/

/-- The **Fisher inner product** on tangent vectors at `θ`:
  `⟨v, w⟩_θ = g_θ(v, w) = E_θ[⟨v, s⟩ · ⟨w, s⟩]`. -/
def fisherInnerProduct {θ : ParamSpace n}
    (_hθ : θ ∈ S.domain)
    (v w : ParamSpace n) : ℝ :=
  S.fisherMetric.eval θ v w

/-- The inner product equals the Fisher bilinear form. -/
theorem fisherInnerProduct_eq_bilin {θ : ParamSpace n}
    (hθ : θ ∈ S.domain)
    (v w : ParamSpace n) :
    S.fisherInnerProduct hθ v w =
      S.model.fisherBilin θ v w := by
  simp only [fisherInnerProduct, RiemannianMetric.eval,
    fisherMetric_matrix]
  exact (S.model.fisherBilin_eq_sum_fisherMatrix hθ
    (S.scoreSqIntegrable_everywhere θ hθ) v w).symm

/-- The inner product is the expected product of directional scores:
  `⟨v, w⟩_θ = ∫ ⟨v, s(θ,ω)⟩ · ⟨w, s(θ,ω)⟩ · p(θ,ω) dμ(ω)`. -/
theorem fisherInnerProduct_eq_expectation {θ : ParamSpace n}
    (hθ : θ ∈ S.domain)
    (v w : ParamSpace n) :
    S.fisherInnerProduct hθ v w =
      ∫ ω, S.model.directionalScore θ v ω *
        S.model.directionalScore θ w ω *
        S.density θ ω ∂S.refMeasure := by
  rw [S.fisherInnerProduct_eq_bilin hθ]
  rfl

/-- The inner product expands as a double sum over Fisher matrix
entries:
  `⟨v, w⟩_θ = ∑_{i,j} vᵢ wⱼ g_{ij}(θ)`. -/
theorem fisherInnerProduct_eq_sum {θ : ParamSpace n}
    (hθ : θ ∈ S.domain)
    (v w : ParamSpace n) :
    S.fisherInnerProduct hθ v w =
      ∑ i : Fin n, ∑ j : Fin n,
        v i * w j * S.model.fisherMatrix θ i j := by
  rfl

/-- The Fisher inner product is symmetric. -/
theorem fisherInnerProduct_symm {θ : ParamSpace n}
    (hθ : θ ∈ S.domain)
    (v w : ParamSpace n) :
    S.fisherInnerProduct hθ v w =
      S.fisherInnerProduct hθ w v :=
  S.fisherMetric.eval_symm hθ v w

/-- The Fisher inner product is positive definite. -/
theorem fisherInnerProduct_pos {θ : ParamSpace n}
    (hθ : θ ∈ S.domain)
    {v : ParamSpace n} (hv : v ≠ 0) :
    0 < S.fisherInnerProduct hθ v v :=
  S.fisherMetric_pos_def hθ hv

/-- The Fisher inner product is nonneg. -/
theorem fisherInnerProduct_nonneg {θ : ParamSpace n}
    (hθ : θ ∈ S.domain)
    (v : ParamSpace n) :
    0 ≤ S.fisherInnerProduct hθ v v :=
  S.fisherMetric.eval_nonneg hθ v

/-! ### The Fisher norm -/

/-- The **Fisher norm** of a tangent vector at `θ`:
  `‖v‖_θ = √(g_θ(v, v))`. -/
def fisherNorm {θ : ParamSpace n}
    (hθ : θ ∈ S.domain) (v : ParamSpace n) : ℝ :=
  Real.sqrt (S.fisherInnerProduct hθ v v)

/-- The Fisher norm is nonneg. -/
theorem fisherNorm_nonneg {θ : ParamSpace n}
    (hθ : θ ∈ S.domain) (v : ParamSpace n) :
    0 ≤ S.fisherNorm hθ v :=
  Real.sqrt_nonneg _

/-- `‖v‖_θ = 0 ⟺ v = 0`. -/
theorem fisherNorm_eq_zero_iff {θ : ParamSpace n}
    (hθ : θ ∈ S.domain) (v : ParamSpace n) :
    S.fisherNorm hθ v = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [fisherNorm, Real.sqrt_eq_zero
      (S.fisherInnerProduct_nonneg hθ v)] at h
    exact S.model.fisherBilin_pos_def hθ
      (S.scoreInjective_everywhere θ hθ)
      (S.directionalScoreIntegrable_everywhere θ hθ)
      (by rwa [S.fisherInnerProduct_eq_bilin hθ] at h)
  · intro h; subst h
    simp [fisherNorm, fisherInnerProduct,
      RiemannianMetric.eval]

/-- Strict positivity for nonzero vectors. -/
theorem fisherNorm_pos {θ : ParamSpace n}
    (hθ : θ ∈ S.domain)
    {v : ParamSpace n} (hv : v ≠ 0) :
    0 < S.fisherNorm hθ v :=
  lt_of_le_of_ne (S.fisherNorm_nonneg hθ v)
    (Ne.symm (fun h => hv
      ((S.fisherNorm_eq_zero_iff hθ v).mp h)))

/-! ### Identifiability -/

/-- A statistical manifold is automatically identifiable in a
local sense: score-injectivity at `θ` implies that infinitesimally
different parameters yield different distributions.

More precisely, if `δθ ≠ 0` then the directional score `⟨δθ, s⟩`
is not a.e. zero, meaning the density changes nontrivially in
direction `δθ`. -/
theorem infinitesimally_identifiable {θ : ParamSpace n}
    (hθ : θ ∈ S.domain) {δ : ParamSpace n} (hδ : δ ≠ 0) :
    ¬(∀ᵐ ω ∂S.refMeasure,
      S.model.directionalScore θ δ ω = 0) :=
  fun h => hδ (S.scoreInjective_everywhere θ hθ δ h)

/-! ### Relationship between Fisher metric and KL divergence

The Fisher metric arises as the Hessian of the KL divergence:
  `D_KL(p_θ ‖ p_{θ+ε·v}) = ½ ε² g_θ(v,v) + O(ε³)`.

This is the deep geometric reason the Fisher metric is the
*unique* (up to scale) monotone metric on statistical manifolds
(Chentsov's theorem). The formal proof requires additional
smoothness conditions and Taylor expansion machinery and is
deferred to `KLDivergence.lean`.

For now we record the *definition* of the KL divergence
and state the key theorem as an axiom to be discharged later. -/

/-- The **Kullback–Leibler divergence** from `P_{θ₁}` to `P_{θ₂}`:
  `D_KL(θ₁ ‖ θ₂) = ∫ p(θ₁, ω) · log(p(θ₁, ω) / p(θ₂, ω)) dμ(ω)`.

This is nonneg by Gibbs' inequality (Jensen + concavity of `log`)
and zero iff `P_{θ₁} = P_{θ₂}` a.e. -/
def klDivergence (θ₁ θ₂ : ParamSpace n) : ℝ :=
  ∫ ω, S.density θ₁ ω *
    Real.log (S.density θ₁ ω / S.density θ₂ ω)
    ∂S.refMeasure

/-- `D_KL(θ ‖ θ) = 0`. -/
theorem klDivergence_self {θ : ParamSpace n}
    (_hθ : θ ∈ S.domain) :
    S.klDivergence θ θ = 0 := by
  simp only [klDivergence]
  simp [mul_zero, MeasureTheory.integral_zero]

end StatisticalManifold

end InformationGeometry
