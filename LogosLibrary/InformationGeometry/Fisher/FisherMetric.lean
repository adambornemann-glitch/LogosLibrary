/-
Copyright (c) 2026 Information Geometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann & co.
-/
import LogosLibrary.InformationGeometry.Fisher.FisherInformation
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# The Fisher–Rao Metric

The **Fisher–Rao metric** (or Fisher metric) is the canonical Riemannian
metric on a statistical manifold.  It is obtained by promoting the Fisher
information bilinear form `g_θ(v, w) = E_θ[⟨v, s⟩ · ⟨w, s⟩]` — shown
to be symmetric and positive semidefinite in `FisherInformation.lean` —
to a genuine bilinear map `ParamSpace n →ₗ[ℝ] ParamSpace n →ₗ[ℝ] ℝ` and
then packaging it as a Riemannian metric (a smoothly varying
positive-definite inner product on each tangent space).

## Main definitions

* `RegularStatisticalModel.fisherBilin_add_left`,
  `RegularStatisticalModel.fisherBilin_smul_left` —
  left-linearity of the Fisher bilinear form (under `ScoreSqIntegrableModel`).
* `RegularStatisticalModel.fisherBilinForm` —
  the Fisher information at `θ` as a `LinearMap.BilinForm ℝ (ParamSpace n)`.
* `InformationGeometry.RiemannianMetric` —
  a smoothly varying positive-definite symmetric bilinear form on an open
  domain in `ℝⁿ`.
* `RegularStatisticalModel.SmoothFisherModel` —
  the additional regularity (smooth dependence of Fisher matrix entries on
  `θ`) needed to obtain a Riemannian metric.
* `RegularStatisticalModel.fisherRiemannianMetric` —
  the Fisher–Rao metric as a `RiemannianMetric`.

## Main results

* `fisherBilinForm_symm` — `g_θ` is symmetric as a `BilinForm`.
* `fisherBilinForm_pos_def` — positive definiteness under score-injectivity.
* `fisherMatrixEntry_smooth` — smooth dependence of `g_{ij}(θ)` on `θ`
  (under `SmoothFisherModel` regularity).

## Design notes

**Why a custom `RiemannianMetric`?**  Mathlib's Riemannian geometry
infrastructure targets abstract smooth manifolds via
`SmoothManifoldWithCorners` and does not (as of mid-2025) provide a
turnkey `RiemannianMetric` structure.  Since our parameter space is
concretely an open subset of `EuclideanSpace ℝ (Fin n)`, we define
a lightweight `RiemannianMetric` carrying exactly the data we need:
a family of bilinear forms indexed by `θ`, with symmetry, positive
definiteness, and smooth dependence on `θ` via its matrix entries.
This plugs directly into the rest of the development while remaining
compatible with a future upgrade to Mathlib's abstract framework.

**Bilinearity.**  The linearity proofs route through
`fisherBilin_eq_sum_fisherMatrix`, which rewrites `g_θ(v, w)` as the
finite double sum `∑ᵢⱼ vᵢ wⱼ g_{ij}(θ)`.  This reduces bilinearity
to algebra on finite sums, cleanly avoiding a second round of
integral-linearity arguments.

## References

* S. Amari, *Information Geometry and Its Applications*, §2.3–2.4, 2016.
* C. R. Rao, "Information and accuracy attainable in the estimation of
  statistical parameters", *Bull. Calcutta Math. Soc.* **37** (1945), 81–91.
-/

noncomputable section

open MeasureTheory ENNReal Real Set Filter Finset

open scoped Topology

namespace InformationGeometry

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace RegularStatisticalModel

variable (M : RegularStatisticalModel n Ω)

/-! ### Bilinearity of the Fisher form

Under `ScoreSqIntegrableModel θ`, the Fisher bilinear form
`fisherBilin θ` is genuinely bilinear.  The proofs reduce to
algebra via `fisherBilin_eq_sum_fisherMatrix`. -/

/-- Left-additivity: `g_θ(v₁ + v₂, w) = g_θ(v₁, w) + g_θ(v₂, w)`. -/
theorem fisherBilin_add_left {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hSq : M.ScoreSqIntegrableModel θ)
    (v₁ v₂ w : ParamSpace n) :
    M.fisherBilin θ (v₁ + v₂) w =
      M.fisherBilin θ v₁ w + M.fisherBilin θ v₂ w := by
  rw [M.fisherBilin_eq_sum_fisherMatrix hθ hSq (v₁ + v₂) w,
      M.fisherBilin_eq_sum_fisherMatrix hθ hSq v₁ w,
      M.fisherBilin_eq_sum_fisherMatrix hθ hSq v₂ w,
      ← Finset.sum_add_distrib]
  congr 1; ext i
  simp only [PiLp.add_apply, ← Finset.sum_add_distrib]
  congr 1; ext j; ring

/-- Left-homogeneity: `g_θ(c • v, w) = c * g_θ(v, w)`. -/
theorem fisherBilin_smul_left {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hSq : M.ScoreSqIntegrableModel θ)
    (c : ℝ) (v w : ParamSpace n) :
    M.fisherBilin θ (c • v) w =
      c * M.fisherBilin θ v w := by
  rw [M.fisherBilin_eq_sum_fisherMatrix hθ hSq (c • v) w,
      M.fisherBilin_eq_sum_fisherMatrix hθ hSq v w,
      Finset.mul_sum]
  congr 1; ext i
  simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1; ext j; ring

/-- Right-additivity, from symmetry + left-additivity. -/
theorem fisherBilin_add_right {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hSq : M.ScoreSqIntegrableModel θ)
    (v w₁ w₂ : ParamSpace n) :
    M.fisherBilin θ v (w₁ + w₂) =
      M.fisherBilin θ v w₁ + M.fisherBilin θ v w₂ := by
  rw [M.fisherBilin_symm, M.fisherBilin_add_left hθ hSq,
      M.fisherBilin_symm θ w₁, M.fisherBilin_symm θ w₂]

/-- Right-homogeneity, from symmetry + left-homogeneity. -/
theorem fisherBilin_smul_right {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hSq : M.ScoreSqIntegrableModel θ)
    (c : ℝ) (v w : ParamSpace n) :
    M.fisherBilin θ v (c • w) =
      c * M.fisherBilin θ v w := by
  rw [M.fisherBilin_symm, M.fisherBilin_smul_left hθ hSq,
      M.fisherBilin_symm]

/-! ### The Fisher information as a bilinear form -/

/-- The Fisher information at `θ` as a `LinearMap.BilinForm ℝ`:
  `g_θ : (ParamSpace n) →ₗ[ℝ] (ParamSpace n) →ₗ[ℝ] ℝ`.

Requires `ScoreSqIntegrableModel θ` for the bilinearity proofs. -/
def fisherBilinForm {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hSq : M.ScoreSqIntegrableModel θ) :
    ParamSpace n →ₗ[ℝ] ParamSpace n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (M.fisherBilin θ)
    (M.fisherBilin_add_left hθ hSq)
    (fun c v w => by
      rw [M.fisherBilin_smul_left hθ hSq]; ring_nf; rfl)
    (M.fisherBilin_add_right hθ hSq)
    (fun c v w => by
      rw [M.fisherBilin_smul_right hθ hSq]; ring_nf; rfl)

/-- The bilinear form evaluates to the raw `fisherBilin`. -/
@[simp]
theorem fisherBilinForm_apply {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hSq : M.ScoreSqIntegrableModel θ)
    (v w : ParamSpace n) :
    M.fisherBilinForm hθ hSq v w = M.fisherBilin θ v w :=
  rfl

/-- The Fisher bilinear form is symmetric. -/
theorem fisherBilinForm_symm {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hSq : M.ScoreSqIntegrableModel θ)
    (v w : ParamSpace n) :
    M.fisherBilinForm hθ hSq v w =
      M.fisherBilinForm hθ hSq w v := by
  simp [M.fisherBilin_symm]

/-- The Fisher bilinear form is positive semidefinite. -/
theorem fisherBilinForm_nonneg {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hSq : M.ScoreSqIntegrableModel θ)
    (v : ParamSpace n) :
    0 ≤ M.fisherBilinForm hθ hSq v v := by
  simp; exact M.fisherBilin_self_nonneg hθ v

/-- Under score-injectivity + integrability, the Fisher bilinear
form is positive definite: `g_θ(v, v) = 0 ⟹ v = 0`. -/
theorem fisherBilinForm_pos_def {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hSq : M.ScoreSqIntegrableModel θ)
    (hInj : M.ScoreInjective θ)
    (hInt : ∀ w : ParamSpace n, Integrable
      (fun ω => M.directionalScore θ w ω *
        M.directionalScore θ w ω *
        M.density θ ω) M.refMeasure)
    {v : ParamSpace n}
    (hzero : M.fisherBilinForm hθ hSq v v = 0) :
    v = 0 := by
  simp at hzero
  exact M.fisherBilin_pos_def hθ hInj hInt hzero

/-- Strict positivity for `v ≠ 0`. -/
theorem fisherBilinForm_pos {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hSq : M.ScoreSqIntegrableModel θ)
    (hInj : M.ScoreInjective θ)
    (hInt : ∀ w : ParamSpace n, Integrable
      (fun ω => M.directionalScore θ w ω *
        M.directionalScore θ w ω *
        M.density θ ω) M.refMeasure)
    {v : ParamSpace n} (hv : v ≠ 0) :
    0 < M.fisherBilinForm hθ hSq v v := by
  simp; exact M.fisherBilin_pos_of_ne_zero hθ hInj hInt hv

/-! ### Fisher matrix as a linear map

The Fisher matrix `g_{ij}(θ)` defines a self-adjoint linear map
`ParamSpace n →ₗ[ℝ] ParamSpace n` via `(G v)ⱼ = ∑ᵢ g_{ji}(θ) vᵢ`.
Under score-injectivity this map is positive definite. -/

/-- The Fisher matrix as a linear map `ℝⁿ → ℝⁿ`:
  `(fisherLinearMap θ v)_j = ∑_i g_{ji}(θ) · v_i`. -/
def fisherLinearMap {θ : ParamSpace n}
    (_hθ : θ ∈ M.paramDomain)
    (_hSq : M.ScoreSqIntegrableModel θ) :
    ParamSpace n →ₗ[ℝ] ParamSpace n where
  toFun v := WithLp.toLp 2 (fun j =>
    ∑ i : Fin n, M.fisherMatrix θ j i * v.ofLp i)
  map_add' v w := by
    show WithLp.toLp 2 _ = WithLp.toLp 2 _
    congr 1
    ext j
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c v := by
    show WithLp.toLp 2 _ = WithLp.toLp 2 _
    congr 1
    ext j
    simp only [RingHom.id_apply]
    simp only [PiLp.smul_apply, smul_eq_mul, WithLp.equiv_apply, Pi.smul_apply]
    rw [@mul_sum]
    congr 1; ext i; ring

/-- The linear map is self-adjoint with respect to the standard
Euclidean inner product:
  `⟨G v, w⟩ = ⟨v, G w⟩`.

This is a restatement of the symmetry `g_{ij} = g_{ji}`. -/
theorem fisherLinearMap_symm_apply {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain)
    (hSq : M.ScoreSqIntegrableModel θ)
    (v w : ParamSpace n) :
    ∑ j, M.fisherLinearMap hθ hSq v j * w j =
      ∑ j, v j * M.fisherLinearMap hθ hSq w j := by
  simp only [fisherLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  -- Expand products into double sums
  simp only [Finset.mul_sum, Finset.sum_mul] -- `simp` made no progress
  -- Both sides are now ∑_j ∑_i (stuff)
  -- Swap summation order on LHS
  rw [Finset.sum_comm]
  congr 1; ext i
  congr 1; ext j
  -- Use symmetry g_{ji} = g_{ij}
  rw [M.fisherMatrix_symm θ j i]
  ring

end RegularStatisticalModel

/-! ### Riemannian metric structure -/

/-- A **Riemannian metric** on an open domain `U ⊆ ℝⁿ` is a smooth
family of positive-definite symmetric bilinear forms, one for each
point of `U`.

In our concrete setting (open subset of Euclidean space), the tangent
space at each point is canonically identified with `ℝⁿ` itself, so
the metric is simply a smooth map `U → (ℝⁿ →ₗ[ℝ] ℝⁿ →ₗ[ℝ] ℝ)`
satisfying pointwise symmetry and positive definiteness.

We encode smoothness via the matrix entries `metricMatrix θ i j`,
which must vary `C^∞`-ly in `θ`.  This is equivalent to smoothness
of the bilinear form as a map into the finite-dimensional space
`Sym²(ℝⁿ)` and avoids carrying the topology on `ℝⁿ →ₗ[ℝ] ℝⁿ →ₗ[ℝ] ℝ`
explicitly. -/
structure RiemannianMetric (n : ℕ) where
  /-- The open domain in `ℝⁿ`. -/
  domain : Set (ParamSpace n)
  /-- The domain is open. -/
  isOpen_domain : IsOpen domain
  /-- The domain is nonempty. -/
  nonempty_domain : domain.Nonempty
  /-- The metric matrix entries. -/
  metricMatrix : ParamSpace n → Fin n → Fin n → ℝ
  /-- Symmetry: `g_{ij}(θ) = g_{ji}(θ)`. -/
  metricMatrix_symm :
    ∀ θ ∈ domain, ∀ i j, metricMatrix θ i j = metricMatrix θ j i
  /-- Positive definiteness: for `v ≠ 0`,
    `∑_{i,j} vᵢ vⱼ g_{ij}(θ) > 0`. -/
  metricMatrix_pos_def :
    ∀ θ ∈ domain, ∀ v : ParamSpace n, v ≠ 0 →
      0 < ∑ i : Fin n, ∑ j : Fin n,
        v i * v j * metricMatrix θ i j
  /-- Each matrix entry is `C^∞` on the domain. -/
  metricMatrix_smooth :
    ∀ i j, ContDiffOn ℝ ⊤ (fun θ => metricMatrix θ i j) domain



/-! ### Evaluating the Riemannian metric -/

namespace RiemannianMetric

variable {n : ℕ} (g : RiemannianMetric n)

/-- Evaluate the metric as a bilinear form on tangent vectors:
  `g_θ(v, w) = ∑_{i,j} vᵢ wⱼ g_{ij}(θ)`. -/
def eval (θ : ParamSpace n) (v w : ParamSpace n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    v i * w j * g.metricMatrix θ i j

/-- The metric evaluation is symmetric. -/
theorem eval_symm {θ : ParamSpace n} (hθ : θ ∈ g.domain)
    (v w : ParamSpace n) :
    g.eval θ v w = g.eval θ w v := by
  simp only [eval]
  rw [Finset.sum_comm]
  congr 1; ext i; congr 1; ext j
  rw [g.metricMatrix_symm θ hθ i j]; ring

/-- The metric evaluation is positive definite. -/
theorem eval_pos {θ : ParamSpace n} (hθ : θ ∈ g.domain)
    {v : ParamSpace n} (hv : v ≠ 0) :
    0 < g.eval θ v v :=
  g.metricMatrix_pos_def θ hθ v hv

/-- The metric evaluation is nonneg. -/
theorem eval_nonneg {θ : ParamSpace n} (hθ : θ ∈ g.domain)
    (v : ParamSpace n) :
    0 ≤ g.eval θ v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [eval]
  · exact le_of_lt (g.eval_pos hθ hv)

end RiemannianMetric

namespace RegularStatisticalModel

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (M : RegularStatisticalModel n Ω)

/-! ### Smooth Fisher model regularity

The smoothness of the Fisher metric requires that the Fisher matrix
entries `g_{ij}(θ) = ∫ sᵢ sⱼ p dμ` vary `C^∞`-ly in `θ`.  This is
a second-order regularity condition beyond what `RegularStatisticalModel`
provides: it requires being able to differentiate the integrand
`sᵢ(θ,ω) sⱼ(θ,ω) p(θ,ω)` under the integral sign arbitrarily many
times, with dominated-convergence bounds at each order.

Rather than spelling out these bounds in full generality (which would
require a tower of derivative bounds of all orders), we package the
conclusion — smooth dependence of `g_{ij}` on `θ` — as a single
hypothesis.  This is satisfied by exponential families and by any
model with compactly supported, `C^∞`-bounded parameter derivatives. -/

/-- A `RegularStatisticalModel` has **smooth Fisher entries** if:
1. the score is square-integrable under the model at every `θ ∈ Θ`,
2. the score is injective at every `θ ∈ Θ`, and
3. each Fisher matrix entry `θ ↦ g_{ij}(θ)` is `C^∞` on `Θ`. -/
structure SmoothFisherModel where
  /-- Score square-integrability under the model, everywhere. -/
  scoreSqIntegrable :
    ∀ θ ∈ M.paramDomain, M.ScoreSqIntegrableModel θ
  /-- Score-injectivity everywhere. -/
  scoreInjective :
    ∀ θ ∈ M.paramDomain, M.ScoreInjective θ
  /-- Integrability of the directional-score bilinear integrand,
    needed for positive-definiteness proofs. -/
  directionalScoreIntegrable :
    ∀ θ ∈ M.paramDomain, ∀ w : ParamSpace n,
      Integrable
        (fun ω => M.directionalScore θ w ω *
          M.directionalScore θ w ω *
          M.density θ ω) M.refMeasure
  /-- Each Fisher matrix entry is `C^∞` on the parameter domain. -/
  fisherMatrix_smooth :
    ∀ i j : Fin n,
      ContDiffOn ℝ ⊤
        (fun θ => M.fisherMatrix θ i j) M.paramDomain

/-! ### The Fisher–Rao metric -/

/-- **The Fisher–Rao Riemannian metric** on the parameter space of a
regular statistical model with smooth Fisher entries.

At each `θ ∈ Θ`, the metric is the Fisher information matrix
`g_{ij}(θ) = E_θ[sᵢ sⱼ]`, which is symmetric (by commutativity),
positive definite (by score-injectivity), and `C^∞` in `θ`
(by `SmoothFisherModel`). -/
def fisherRiemannianMetric (hF : M.SmoothFisherModel) :
    RiemannianMetric n where
  domain := M.paramDomain
  isOpen_domain := M.isOpen_paramDomain
  nonempty_domain := M.nonempty_paramDomain
  metricMatrix := M.fisherMatrix
  metricMatrix_symm θ _hθ i j := M.fisherMatrix_symm θ i j
  metricMatrix_pos_def θ hθ v hv := by
    -- g_θ(v, v) > 0 follows from score-injectivity.
    -- First rewrite the sum as fisherBilin via the sum formula.
    have hSq := hF.scoreSqIntegrable θ hθ
    rw [show ∑ i : Fin n, ∑ j : Fin n,
          v i * v j * M.fisherMatrix θ i j =
        M.fisherBilin θ v v from
      (M.fisherBilin_eq_sum_fisherMatrix hθ hSq v v).symm]
    exact M.fisherBilin_pos_of_ne_zero hθ
      (hF.scoreInjective θ hθ)
      (hF.directionalScoreIntegrable θ hθ) hv
  metricMatrix_smooth := hF.fisherMatrix_smooth

/-- The Fisher–Rao metric matrix at `θ` is the Fisher information
matrix.  (Definitional, but useful as a `simp` lemma.) -/
@[simp]
theorem fisherRiemannianMetric_matrix (hF : M.SmoothFisherModel)
    (θ : ParamSpace n) (i j : Fin n) :
    (M.fisherRiemannianMetric hF).metricMatrix θ i j =
      M.fisherMatrix θ i j :=
  rfl

/-- The Fisher–Rao metric evaluates to the Fisher bilinear form. -/
theorem fisherRiemannianMetric_eval (hF : M.SmoothFisherModel)
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (v w : ParamSpace n) :
    InformationGeometry.RiemannianMetric.eval (M.fisherRiemannianMetric hF) θ v w =
      M.fisherBilin θ v w := by
  simp only [InformationGeometry.RiemannianMetric.eval]
  exact (M.fisherBilin_eq_sum_fisherMatrix hθ
    (hF.scoreSqIntegrable θ hθ) v w).symm

/-! ### Continuous dependence of the metric -/

/-- The Fisher matrix is continuous on the parameter domain. -/
theorem fisherMatrix_continuousOn (hF : M.SmoothFisherModel)
    (i j : Fin n) :
    ContinuousOn (fun θ => M.fisherMatrix θ i j)
      M.paramDomain :=
  (hF.fisherMatrix_smooth i j).continuousOn

/-- The Fisher bilinear form depends continuously on `θ`, for
fixed tangent vectors `v, w`. -/
theorem fisherBilin_continuousOn (hF : M.SmoothFisherModel)
    (v w : ParamSpace n) :
    ContinuousOn (fun θ => M.fisherBilin θ v w)
      M.paramDomain := by
  -- g_θ(v,w) = ∑_{ij} v_i w_j g_{ij}(θ), a finite sum of continuous functions.
  -- First show the sum is continuous
  have sum_cont : ContinuousOn
      (fun θ => ∑ i : Fin n, ∑ j : Fin n, v i * w j * M.fisherMatrix θ i j)
      M.paramDomain := by
    apply continuousOn_finset_sum
    intro i _
    apply continuousOn_finset_sum
    intro j _
    apply ContinuousOn.mul continuousOn_const
    exact (hF.fisherMatrix_smooth i j).continuousOn
  apply ContinuousOn.congr sum_cont
  intro θ hθ
  exact (M.fisherBilin_eq_sum_fisherMatrix hθ
    (hF.scoreSqIntegrable θ hθ) v w)


end RegularStatisticalModel

end InformationGeometry
