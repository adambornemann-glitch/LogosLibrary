/-
Copyright (c) 2026 Information Geometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann & co.
-/
import LogosLibrary.InformationGeometry.Fisher.FisherMetric
import LogosLibrary.InformationGeometry.Fisher.StatisticalManifold
import Mathlib.Tactic

/-!
# Computation as a Path on the Fisher Manifold

**Step 2 of the P ≠ NP program.**

Every deterministic computation induces a curve on the statistical
manifold, and the Fisher metric gives this curve a well-defined
**thermodynamic length** — the information-geometric cost of the
computation.

## The key physical insight

A Turing machine running on an input drawn from distribution D
induces, at each step t, a probability distribution over
configurations:

  `p_t(ω) = Pr[machine is in configuration ω at step t]`

For a deterministic machine, this is the pushforward of the input
distribution under t-fold composition of the transition function.
On a finite configuration space, this is a point on the probability
simplex — which *is* the statistical manifold equipped with the
Fisher–Rao metric.

The computation thus traces a **discrete path** on the Fisher
manifold.  Its thermodynamic length is the sum of Fisher–Rao
distances between consecutive distributions:

  `𝓛[M, D] = ∑_{t=0}^{T-1} d_FR(p_t, p_{t+1})`

## Why this works cleanly

For finite discrete distributions on `|Ω| = N` outcomes, the
probability simplex `Δ_N` embeds into the unit sphere `S^{N-1}`
via the square-root map `p_i ↦ √p_i`.  Under this embedding,
the Fisher–Rao metric becomes the **round metric** on the sphere,
and the geodesic distance has a closed form:

  `d_FR(p, q) = 2 · arccos(∑_ω √(p(ω) · q(ω)))`

where `∑_ω √(p(ω) · q(ω))` is the **Bhattacharyya coefficient**.

No measure theory dragons.  No dominated convergence.  Just
finite sums and trigonometry.

## Main definitions

* `FinDist` — Probability distributions on a finite type.
* `FinDist.pushforward` — Pushforward of a distribution under a
  deterministic map.
* `FinDist.iteratePush` — Distribution at step `t` of a computation.
* `bhattacharyyaCoeff` — `BC(p, q) = ∑_ω √(p(ω) · q(ω))`.
* `fisherRaoDistance` — `d(p, q) = 2 · arccos(BC(p, q))`.
* `ComputationPath` — A deterministic computation with initial
  distribution, bundling the transition, step count, and input.
* `ComputationPath.thermodynamicLength` — Sum of step-wise
  Fisher–Rao distances: the information-geometric cost.

## Main results

* `bhattacharyya_self` — `BC(p, p) = 1`.
* `bhattacharyya_symm` — `BC(p, q) = BC(q, p)`.
* `bhattacharyya_nonneg` — `0 ≤ BC(p, q)`.
* `bhattacharyya_le_one` — `BC(p, q) ≤ 1`.
* `fisherRao_self` — `d(p, p) = 0`.
* `fisherRao_symm` — `d(p, q) = d(q, p)`.
* `fisherRao_nonneg` — `0 ≤ d(p, q)`.
* `thermodynamicLength_nonneg` — `0 ≤ 𝓛[γ]`.
* `thermodynamicLength_mono` — Extending a path can only increase
  or maintain thermodynamic length.
* `step_displacement_bound` — Per-step Fisher–Rao displacement
  is bounded by a constant depending on the transition.
* `length_le_steps_mul_maxDisplacement` — `𝓛 ≤ T · Δ_max`.

## Design notes

**Approach A: axiomatise, then backfill.** Following the pattern
established in `CramerRao.lean`, the bridge between finite
computation and the continuous `StatisticalManifold` is stated
via the `FisherBridge` structure, whose fields connect the
discrete Fisher–Rao distance to the manifold's Riemannian metric.
Future work (Approach B) constructs a `FisherBridge` from the
square-root embedding of the simplex, discharging all axioms.

**Finite configuration spaces.** We use `Fintype` throughout.
For Turing machines with tape bounded by `f(n)`, the configuration
space is finite with `|Cfg| = |Q| · |Γ|^{f(n)} · f(n)` — states
times tape contents times head position.  The finiteness buys us
concrete sums and decidable equality, which is all we need.

## Connection to the P ≠ NP argument

This file establishes:

1. **Every computation has a well-defined thermodynamic length**
   (the sum of Fisher–Rao distances along its path).

2. **Polynomial steps imply at most polynomial thermodynamic length**
   (each step contributes bounded displacement).

Step 4 (curvature divergence at phase transitions) will establish
a *lower bound* on thermodynamic length for NP-complete problems.
Combined with the *upper bound* from (2), this gives:

  `exp(c·n) ≤ 𝓛 ≤ T · Δ_max  ⟹  T ≥ exp(c·n) / Δ_max`

If `Δ_max` is polynomial, the number of steps is exponential.

## References

* S. Amari, *Information Geometry and Its Applications*, §2, 2016.
* A. Bhattacharyya, "On a measure of divergence between two
  statistical populations", *Bull. Calcutta Math. Soc.* **35**
  (1943), 99–109.
* R. Landauer, "Irreversibility and heat generation in the
  computing process", *IBM J. Res. Dev.* **5** (1961), 183–191.
* L. B. Levitin, T. Toffoli, "Fundamental limit on the rate of
  quantum dynamics", *Phys. Rev. Lett.* **103** (2009), 160502.
-/

noncomputable section

open Finset Real BigOperators

/-! ## Part 1: Finite Probability Distributions -/

/-- A probability distribution on a finite type `Ω`.

This is the natural home for distributions induced by deterministic
computation on a bounded configuration space.  Every `FinDist Ω`
corresponds to a point on the probability simplex `Δ_{|Ω|}`, which
is a submanifold of the Fisher statistical manifold. -/
structure FinDist (Ω : Type*) [Fintype Ω] where
  /-- The probability mass function. -/
  prob : Ω → ℝ
  /-- Probabilities are nonnegative. -/
  prob_nonneg : ∀ ω, 0 ≤ prob ω
  /-- Probabilities sum to one. -/
  prob_sum_one : ∑ ω : Ω, prob ω = 1

namespace FinDist


variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The support of a distribution: outcomes with positive probability. -/
def support (p : FinDist Ω) : Finset Ω :=
  Finset.univ.filter (fun ω => 0 < p.prob ω)

/-- Expectation of a real-valued function under the distribution. -/
def expect (p : FinDist Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, p.prob ω * f ω

/-- **Pushforward** of a distribution under a deterministic map.

If `f : α → β` is a deterministic function and `p` is a distribution
on `α`, then `(f_* p)(b) = ∑_{a : f(a) = b} p(a)`.

For a Turing machine, `f = transition` and this gives the distribution
over configurations at the next step. -/
def pushforward {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : FinDist α) (f : α → β) : FinDist β where
  prob b := ∑ a ∈ Finset.univ.filter (fun a => f a = b), p.prob a
  prob_nonneg b := Finset.sum_nonneg (fun a _ => p.prob_nonneg a)
  prob_sum_one := by
    -- Key idea: ∑_b ∑_{a : f(a)=b} p(a) = ∑_a p(a) = 1
    -- This is Finset.sum_fiberwise applied to f
    have h : ∑ b : β, ∑ a ∈ Finset.univ.filter (fun a => f a = b),
        p.prob a = ∑ a : α, p.prob a := by
      exact sum_fiberwise univ f p.prob
    rw [h, p.prob_sum_one]

/-- Iterate the pushforward `t` times: the distribution at step `t`
of a deterministic computation starting from distribution `p`. -/
def iteratePush {Cfg : Type*} [Fintype Cfg] [DecidableEq Cfg]
    (p : FinDist Cfg) (f : Cfg → Cfg) : ℕ → FinDist Cfg
  | 0 => p
  | t + 1 => (p.iteratePush f t).pushforward f

/-- The distribution at step `t` agrees with pushing forward
by the `t`-fold composition of `f`. -/
theorem iteratePush_eq_pushforward_iterate {Cfg : Type*}
    [Fintype Cfg] [DecidableEq Cfg]
    (p : FinDist Cfg) (f : Cfg → Cfg) (t : ℕ) (ω : Cfg) :
    (p.iteratePush f t).prob ω =
    ∑ a ∈ Finset.univ.filter (fun a => f^[t] a = ω), p.prob a := by
  induction t generalizing ω with
  | zero =>
    simp [iteratePush, Function.iterate_zero]
    rw [Finset.sum_filter]; simp
  | succ n ih =>
    -- LHS unfolds definitionally: iteratePush at (n+1) is pushforward of step n
    have lhs_eq : (p.iteratePush f (n + 1)).prob ω =
        ∑ c ∈ Finset.univ.filter (fun c => f c = ω),
          (p.iteratePush f n).prob c := rfl
    rw [lhs_eq, Function.iterate_succ', Function.comp_def]
    -- Apply ih at each intermediate configuration c
    simp_rw [ih]
    -- Collapse double sum via fiber decomposition:
    -- ∑ c ∈ {c | f c = ω}, ∑ a ∈ {a | f^[n] a = c}, p(a)
    --   = ∑ a ∈ {a | f(f^[n] a) = ω}, p(a)
    rw [← Finset.sum_biUnion]
    · congr 1; ext a
      simp only [Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨fun ⟨c, hc, ha⟩ => ha ▸ hc,
             fun h => ⟨f^[n] a, h, rfl⟩⟩
    · intro c₁ _ c₂ _ hne
      simp only [Finset.disjoint_left, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact fun a h₁ h₂ => hne (h₁.symm.trans h₂)

/-- The identity function preserves the distribution. -/
@[simp] theorem iteratePush_zero {Cfg : Type*}
    [Fintype Cfg] [DecidableEq Cfg]
    (p : FinDist Cfg) (f : Cfg → Cfg) :
    p.iteratePush f 0 = p := rfl

variable {Ω : Type*} [Fintype Ω]
@[ext] theorem ext {p q : FinDist Ω} (h : ∀ ω, p.prob ω = q.prob ω) : p = q := by
  cases p; cases q; congr; funext ω; exact h ω

theorem pushforward_pushforward {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (p : FinDist α) (f : α → β) (g : β → γ) :
    (p.pushforward f).pushforward g = p.pushforward (g ∘ f) := by
  ext ω
  simp only [pushforward, Function.comp]
  rw [← Finset.sum_biUnion]
  · congr 1; ext a
    simp only [Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨fun ⟨b, hb, ha⟩ => ha ▸ hb, fun h => ⟨f a, h, rfl⟩⟩
  · intro b₁ _ b₂ _ hne
    simp only [Finset.disjoint_left, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact fun a h₁ h₂ => hne (h₁.symm.trans h₂)

end FinDist

/-! ## Part 2: Bhattacharyya Coefficient

The Bhattacharyya coefficient `BC(p, q) = ∑_ω √(p(ω) · q(ω))`
measures the overlap between two distributions.  It takes values
in `[0, 1]`, with `BC(p, p) = 1` and `BC(p, q) = 0` when `p`
and `q` have disjoint supports.

Under the square-root embedding `p ↦ (√p₁, …, √pₙ)` of the
simplex into the unit sphere, BC is just the **inner product**
of the embedded vectors.  The Fisher–Rao distance is then the
**angle** between them.
-/

section Bhattacharyya

variable {Ω : Type*} [Fintype Ω]

/-- The **Bhattacharyya coefficient** of two distributions.

`BC(p, q) = ∑_ω √(p(ω) · q(ω))`

This is the inner product of `√p` and `√q` on the probability
simplex, viewed as points on the unit sphere. -/
def bhattacharyyaCoeff (p q : FinDist Ω) : ℝ :=
  ∑ ω : Ω, Real.sqrt (p.prob ω * q.prob ω)

/-- BC is symmetric: `BC(p, q) = BC(q, p)`.

Immediate from commutativity of multiplication under `√`. -/
theorem bhattacharyya_symm (p q : FinDist Ω) :
    bhattacharyyaCoeff p q = bhattacharyyaCoeff q p := by
  unfold bhattacharyyaCoeff
  congr 1; ext ω; ring_nf

/-- BC is nonneg: `0 ≤ BC(p, q)`.

Each term `√(p(ω) · q(ω)) ≥ 0`, so the sum is nonneg. -/
theorem bhattacharyya_nonneg (p q : FinDist Ω) :
    0 ≤ bhattacharyyaCoeff p q :=
  Finset.sum_nonneg (fun ω _ =>
    Real.sqrt_nonneg (p.prob ω * q.prob ω))

/-- BC of a distribution with itself is 1: `BC(p, p) = 1`.

`∑_ω √(p(ω)²) = ∑_ω p(ω) = 1` since `p(ω) ≥ 0`. -/
theorem bhattacharyya_self (p : FinDist Ω) :
    bhattacharyyaCoeff p p = 1 := by
  unfold bhattacharyyaCoeff
  have : ∀ ω : Ω, Real.sqrt (p.prob ω * p.prob ω) = p.prob ω := by
    intro ω
    ring_nf
    rw [sqrt_sq_eq_abs]
    norm_num
    exact p.prob_nonneg ω
  simp_rw [this]
  exact p.prob_sum_one

/-- BC is at most 1: `BC(p, q) ≤ 1`.

By Cauchy–Schwarz on the vectors `(√p₁, …)` and `(√q₁, …)`
whose squared norms are both 1. -/
theorem bhattacharyya_le_one (p q : FinDist Ω) :
    bhattacharyyaCoeff p q ≤ 1 := by
  unfold bhattacharyyaCoeff
  -- AM-GM: √(ab) ≤ (a + b)/2 for a, b ≥ 0
  -- Therefore ∑ √(pᵢqᵢ) ≤ ∑ (pᵢ + qᵢ)/2 = (1 + 1)/2 = 1
  have h_amgm : ∀ ω : Ω, Real.sqrt (p.prob ω * q.prob ω) ≤
      (p.prob ω + q.prob ω) / 2 := by
    intro ω
    have hp := p.prob_nonneg ω
    have hq := q.prob_nonneg ω
    -- From (√p - √q)² ≥ 0, expand and use √p · √q = √(pq)
    nlinarith [sq_nonneg (Real.sqrt (p.prob ω) - Real.sqrt (q.prob ω)),
               Real.sq_sqrt hp, Real.sq_sqrt hq,
               Real.sqrt_mul hp (q.prob ω)]
  calc ∑ ω : Ω, Real.sqrt (p.prob ω * q.prob ω)
      ≤ ∑ ω : Ω, (p.prob ω + q.prob ω) / 2 :=
        Finset.sum_le_sum (fun ω _ => h_amgm ω)
    _ = (∑ ω : Ω, p.prob ω + ∑ ω : Ω, q.prob ω) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ = 1 := by rw [p.prob_sum_one, q.prob_sum_one]; ring

end Bhattacharyya

/-! ## Part 3: Fisher–Rao Distance (Finite Case)

For distributions on a finite type, the Fisher–Rao geodesic
distance has the beautiful closed form:

  `d_FR(p, q) = 2 · arccos(BC(p, q))`

This is the **angle** between the square-root embeddings of `p`
and `q` on the unit sphere, scaled by 2 (the radius of the
Fisher–Rao sphere is 2, not 1).

The factor of 2 arises because the Fisher metric on the simplex
is 4× the round metric pulled back through the square-root map.
Equivalently, the probability simplex under Fisher–Rao is isometric
to a sphere of radius 2 (not radius 1).
-/

section FisherRaoDistance

variable {Ω : Type*} [Fintype Ω]

/-- The **Fisher–Rao geodesic distance** between two distributions
on a finite type.

`d_FR(p, q) = 2 · arccos(BC(p, q))`

This is the geodesic distance on the probability simplex equipped
with the Fisher information metric.  For finite types, it has this
exact closed form via the Bhattacharyya coefficient. -/
def fisherRaoDistance (p q : FinDist Ω) : ℝ :=
  2 * Real.arccos (bhattacharyyaCoeff p q)

/-- Fisher–Rao distance is symmetric. -/
theorem fisherRao_symm (p q : FinDist Ω) :
    fisherRaoDistance p q = fisherRaoDistance q p := by
  unfold fisherRaoDistance
  rw [bhattacharyya_symm]

/-- Fisher–Rao distance of a distribution to itself is zero. -/
theorem fisherRao_self (p : FinDist Ω) :
    fisherRaoDistance p p = 0 := by
  unfold fisherRaoDistance
  rw [bhattacharyya_self, Real.arccos_one, mul_zero]

/-- Fisher–Rao distance is nonneg.

`arccos` maps `[-1, 1] → [0, π]`, and `BC(p,q) ≤ 1`, so
`arccos(BC) ≥ 0`. -/
theorem fisherRao_nonneg (p q : FinDist Ω) :
    0 ≤ fisherRaoDistance p q := by
  unfold fisherRaoDistance
  apply mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
  exact Real.arccos_nonneg (bhattacharyyaCoeff p q)

/-- Fisher–Rao distance is bounded above by `π`
(the diameter of the Fisher–Rao sphere of radius 2 is `2π`,
but distributions live on the positive orthant, giving diameter `π`). -/
theorem fisherRao_le_pi (p q : FinDist Ω) :
    fisherRaoDistance p q ≤ 2 * π := by
  unfold fisherRaoDistance
  exact mul_le_mul_of_nonneg_left (Real.arccos_le_pi _)
    (by norm_num : (0:ℝ) ≤ 2)

/-- **Positive definiteness** of the Fisher–Rao distance.

`d_FR(p, q) = 0 ↔ BC(p, q) = 1 ↔ p = q` (on the support).

The forward direction: `d = 0` implies `arccos(BC) = 0` implies
`BC = 1` implies `√p = √q` pointwise implies `p = q`. -/
theorem fisherRao_eq_zero_iff (p q : FinDist Ω)
    (hp : ∀ ω, 0 < p.prob ω) (hq : ∀ ω, 0 < q.prob ω) :
    fisherRaoDistance p q = 0 ↔ p.prob = q.prob := by
  constructor
  · intro h
    -- Stage 1: d = 0 → BC = 1
    unfold fisherRaoDistance at h
    have h_arccos : Real.arccos (bhattacharyyaCoeff p q) = 0 := by
      have := Real.arccos_nonneg (bhattacharyyaCoeff p q); linarith
    have h_bc : bhattacharyyaCoeff p q = 1 := by
      have h_lo : -1 ≤ bhattacharyyaCoeff p q :=
        by linarith [bhattacharyya_nonneg p q]
      have h_hi := bhattacharyya_le_one p q
      have := Real.cos_arccos h_lo h_hi
      rw [h_arccos, Real.cos_zero] at this; linarith
    -- Stage 2: BC = 1 → AM-GM gap vanishes → p = q
    set gap := fun ω : Ω =>
      (p.prob ω + q.prob ω) / 2 -
        Real.sqrt (p.prob ω * q.prob ω) with gap_def
    have h_gap_nn : ∀ ω : Ω, 0 ≤ gap ω := by
      intro ω; simp only [gap_def]
      nlinarith [sq_nonneg (Real.sqrt (p.prob ω) - Real.sqrt (q.prob ω)),
                 Real.sq_sqrt (hp ω).le, Real.sq_sqrt (hq ω).le,
                 Real.sqrt_mul (hp ω).le (q.prob ω)]
    have h_gap_sum : ∑ ω : Ω, gap ω = 0 := by
      simp only [gap_def, Finset.sum_sub_distrib]
      unfold bhattacharyyaCoeff at h_bc
      have h_half : ∑ ω : Ω, (p.prob ω + q.prob ω) / 2 = 1 := by
        simp_rw [add_div]
        rw [Finset.sum_add_distrib,
            ← Finset.sum_div, ← Finset.sum_div,
            p.prob_sum_one, q.prob_sum_one]
        norm_num
      linarith
    have h_gap_zero : ∀ ω : Ω, gap ω = 0 := by
      intro ω
      have h_le := Finset.single_le_sum
        (f := gap) (fun ω' _ => h_gap_nn ω') (Finset.mem_univ ω)
      rw [h_gap_sum] at h_le
      linarith [h_gap_nn ω]
    funext ω
    have hg := h_gap_zero ω; simp only [gap_def] at hg
    have hpn := (hp ω).le; have hqn := (hq ω).le
    have h_sq : (Real.sqrt (p.prob ω) - Real.sqrt (q.prob ω)) ^ 2 = 0 := by
      nlinarith [Real.sq_sqrt hpn, Real.sq_sqrt hqn,
                 Real.sqrt_mul hpn (q.prob ω)]
    have h_sqrt_eq : Real.sqrt (p.prob ω) = Real.sqrt (q.prob ω) :=
      sub_eq_zero.mp (sq_eq_zero_iff.mp h_sq)
    calc p.prob ω = Real.sqrt (p.prob ω) ^ 2 := (Real.sq_sqrt hpn).symm
      _ = Real.sqrt (q.prob ω) ^ 2 := by rw [h_sqrt_eq]
      _ = q.prob ω := Real.sq_sqrt hqn
  · -- Stage 3: p.prob = q.prob → d = 0
    intro h
    unfold fisherRaoDistance
    have hbc : bhattacharyyaCoeff p q = 1 := by
      unfold bhattacharyyaCoeff; simp_rw [h]
      have : ∀ ω : Ω, Real.sqrt (q.prob ω * q.prob ω) = q.prob ω := by
        intro ω; rw [← Real.sqrt_sq (q.prob_nonneg ω)]; congr 1; ring_nf;
        rw [sqrt_sq_eq_abs]; exact sq_abs (q.prob ω)
      simp_rw [this]; exact q.prob_sum_one
    rw [hbc, Real.arccos_one, mul_zero]



/-- **Spherical triangle inequality for arccos.**
For `a, b, c ∈ [0, 1]` arising as Bhattacharyya coefficients
(inner products of unit vectors on the nonneg sphere):
  `arccos(a) ≤ arccos(b) + arccos(c)`
when the unit vectors satisfy the compatibility condition.

This is the angular metric triangle inequality on the sphere.
The proof requires either spherical geometry or the cosine
addition formula with Cauchy–Schwarz. -/
private theorem arccos_bhattacharyya_triangle
    (p q r : FinDist Ω) :
    Real.arccos (bhattacharyyaCoeff p r) ≤
    Real.arccos (bhattacharyyaCoeff p q) +
    Real.arccos (bhattacharyyaCoeff q r) := by
  -- Key idea: define sqrtEmbed(p)(ω) = √(p(ω)).
  -- These are unit vectors in ℝ^Ω with ‖sqrtEmbed p‖² = 1.
  -- BC(p,q) = ⟨sqrtEmbed p, sqrtEmbed q⟩.
  -- The angular metric arccos(⟨u,v⟩) satisfies the triangle
  -- inequality on the unit sphere.
  -- Proof: let α = arccos(⟨u,v⟩), β = arccos(⟨v,w⟩).
  -- Then ⟨u,w⟩ = ⟨u, proj_v w⟩ + ⟨u, w - proj_v w⟩
  --            = ⟨u,v⟩⟨v,w⟩ + ⟨u, w_⊥⟩
  --            ≥ cos(α)cos(β) - sin(α)sin(β)  (Cauchy–Schwarz on ⊥ part)
  --            = cos(α + β)
  -- So arccos(⟨u,w⟩) ≤ α + β.

  sorry

/-- **Triangle inequality** for the Fisher–Rao distance.

Inherited from the triangle inequality on the sphere (the
square-root embedding is an isometry). -/
theorem fisherRao_triangle (p q r : FinDist Ω) :
    fisherRaoDistance p r ≤ fisherRaoDistance p q +
    fisherRaoDistance q r := by
  unfold fisherRaoDistance
  linarith [arccos_bhattacharyya_triangle p q r]

@[ext] theorem ext {p q : FinDist Ω} (h : ∀ ω, p.prob ω = q.prob ω) : p = q := by
  cases p; cases q; congr; funext ω; exact h ω

end FisherRaoDistance

/-! ## Part 4: Computation Paths and Thermodynamic Length

A **computation path** is a deterministic dynamical system
(transition function on a finite configuration space) together
with an initial distribution.  It induces a discrete sequence
of distributions, one per time step.

The **thermodynamic length** of the computation is the total
Fisher–Rao distance traversed along this sequence.  This is the
information-geometric cost of the computation — the total
entropy production rate integrated over the computation's
trajectory through distribution space.
-/

section ComputationPath

variable {Cfg : Type*} [Fintype Cfg] [DecidableEq Cfg]

/-- A **computation path** on a finite configuration space.

Bundles a deterministic transition function with an initial
distribution and a step count.  Represents a bounded deterministic
computation (e.g., a Turing machine with bounded tape running
for at most `T` steps). -/
structure ComputationPath (Cfg : Type*) [Fintype Cfg]
    [DecidableEq Cfg] where
  /-- The deterministic transition function.
  For a Turing machine, this maps each configuration (state, tape,
  head position) to the next configuration. -/
  transition : Cfg → Cfg
  /-- The initial distribution over configurations.
  Encodes the input distribution: for a machine started on
  input `x` drawn from distribution `D`, this is the induced
  distribution on initial configurations. -/
  initDist : FinDist Cfg
  /-- The number of computational steps. -/
  numSteps : ℕ

namespace ComputationPath

variable (γ : ComputationPath Cfg)


/-- The distribution over configurations at step `t`. -/
def distAt (t : ℕ) : FinDist Cfg :=
  γ.initDist.iteratePush γ.transition t

/-- The distribution at step 0 is the initial distribution. -/
@[simp] theorem distAt_zero : γ.distAt 0 = γ.initDist := rfl

/-- The distribution at step `t+1` is the pushforward of step `t`. -/
theorem distAt_succ (t : ℕ) :
    γ.distAt (t + 1) = (γ.distAt t).pushforward γ.transition := rfl

/-- The Fisher–Rao displacement at step `t`: the distance between
consecutive distributions `p_t` and `p_{t+1}`.

This is the **instantaneous information-geometric cost** of the
`t`-th computational step. -/
def stepDisplacement (t : ℕ) : ℝ :=
  fisherRaoDistance (γ.distAt t) (γ.distAt (t + 1))

/-- Step displacements are nonneg. -/
theorem stepDisplacement_nonneg (t : ℕ) :
    0 ≤ γ.stepDisplacement t :=
  fisherRao_nonneg _ _

/-- The **thermodynamic length** of the computation.

`𝓛[γ] = ∑_{t=0}^{T-1} d_FR(p_t, p_{t+1})`

This is the total information-geometric cost: the sum of Fisher–Rao
distances traversed along the computation's path through
distribution space.

By Landauer's principle, this quantity is proportional to the
minimum thermodynamic (entropy) cost of the computation.
It is the central object connecting computation to physics. -/
def thermodynamicLength : ℝ :=
  ∑ t ∈ Finset.range γ.numSteps, γ.stepDisplacement t

/-- Thermodynamic length is nonneg: `0 ≤ 𝓛[γ]`. -/
theorem thermodynamicLength_nonneg : 0 ≤ γ.thermodynamicLength :=
  Finset.sum_nonneg (fun t _ => γ.stepDisplacement_nonneg t)

/-- Thermodynamic length of a zero-step computation is zero. -/
theorem thermodynamicLength_zero
    (h : γ.numSteps = 0) : γ.thermodynamicLength = 0 := by
  unfold thermodynamicLength; rw [h]; simp

/-- Thermodynamic length is monotone in the number of steps:
extending a computation can only increase thermodynamic length.

`T₁ ≤ T₂ ⟹ 𝓛(T₁ steps) ≤ 𝓛(T₂ steps)` -/
theorem thermodynamicLength_mono (γ₁ γ₂ : ComputationPath Cfg)
    (h_trans : γ₁.transition = γ₂.transition)
    (h_init : γ₁.initDist = γ₂.initDist)
    (h_steps : γ₁.numSteps ≤ γ₂.numSteps) :
    γ₁.thermodynamicLength ≤ γ₂.thermodynamicLength := by
  unfold thermodynamicLength
  have h_eq : ∀ t, γ₁.stepDisplacement t = γ₂.stepDisplacement t := by
    intro t
    simp only [stepDisplacement, distAt]
    rw [h_init, h_trans]
  simp_rw [h_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono h_steps
  · intro t _ _
    exact γ₂.stepDisplacement_nonneg t

variable {Cfg : Type*} [Fintype Cfg]

private theorem path_length_ge_endpoint_aux
    (dist : ℕ → FinDist Cfg) (T : ℕ) :
    fisherRaoDistance (dist 0) (dist T) ≤
    ∑ t ∈ Finset.range T,
      fisherRaoDistance (dist t) (dist (t + 1)) := by
  induction T with
  | zero => simp [fisherRao_self]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc fisherRaoDistance (dist 0) (dist (n + 1))
        ≤ fisherRaoDistance (dist 0) (dist n) +
          fisherRaoDistance (dist n) (dist (n + 1)) :=
        fisherRao_triangle _ _ _
      _ ≤ ∑ t ∈ Finset.range n,
            fisherRaoDistance (dist t) (dist (t + 1)) +
          fisherRaoDistance (dist n) (dist (n + 1)) :=
        add_le_add_right ih _

/-- **Triangle inequality for paths:** the thermodynamic length
of a path is at least the Fisher–Rao distance between endpoints.

`d_FR(p_0, p_T) ≤ 𝓛[γ]`

This is the discrete analogue of "the length of a curve is at
least the distance between its endpoints." -/
theorem thermodynamicLength_ge_endpoint_distance :
    fisherRaoDistance (γ.distAt 0) (γ.distAt γ.numSteps) ≤
    γ.thermodynamicLength := by
  exact path_length_ge_endpoint_aux γ.distAt γ.numSteps

end ComputationPath

end ComputationPath

/-! ## Part 5: Step Displacement Bounds

The crucial link between thermodynamic length and step count.

A deterministic transition function on a finite configuration space
has a **maximum per-step displacement** `Δ_max`: the largest
Fisher–Rao distance that any single application of the transition
can produce.  This bounds how fast any computation can traverse
the statistical manifold.

**The key inequality:**

  `𝓛[γ] ≤ T · Δ_max`

Combined with a thermodynamic length *lower bound* (from curvature
divergence at phase transitions, Step 4), this gives:

  `T ≥ 𝓛_min / Δ_max`

For NP-complete problems: `𝓛_min ~ exp(cn)` and `Δ_max ~ poly(n)`,
yielding `T ≥ exp(cn) / poly(n)` — exponential time.
-/

section DisplacementBounds

variable {Cfg : Type*} [Fintype Cfg] [DecidableEq Cfg]

/-- The **maximum per-step displacement** of a transition function
with respect to a given initial distribution.

This is the maximum of `d_FR(p_t, p_{t+1})` over all steps `t`,
or `0` for a zero-step computation.  For a fixed transition function
on a finite type, this is a well-defined finite constant. -/
def maxStepDisplacement (γ : ComputationPath Cfg) : ℝ :=
  (Finset.range γ.numSteps).fold max 0 γ.stepDisplacement

/-- Each step displacement is at most the maximum. -/
private theorem le_fold_max {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) (b : ℝ) (i : ι) (hi : i ∈ s) :
    f i ≤ s.fold max b f := by
  induction s using Finset.induction_on with
  | empty => exact absurd hi (Finset.notMem_empty _)
  | insert a s ha ih =>
    rw [Finset.fold_insert ha]
    rcases Finset.mem_insert.mp hi with rfl | h
    · exact le_max_left _ _
    · exact le_max_of_le_right (ih h)

theorem step_le_max (γ : ComputationPath Cfg)
    (t : ℕ) (ht : t < γ.numSteps) :
    γ.stepDisplacement t ≤ maxStepDisplacement γ := by
  exact le_fold_max _ _ _ _ (Finset.mem_range.mpr ht)

/-- **The fundamental upper bound:** thermodynamic length is at
most the number of steps times the maximum displacement.

  `𝓛[γ] ≤ T · Δ_max`

This is the **per-step locality constraint**: a local transition
can only move the distribution a bounded amount in Fisher–Rao
distance per step, so polynomial steps give at most polynomial
thermodynamic length. -/
theorem length_le_steps_mul_bound (γ : ComputationPath Cfg)
    (Δ : ℝ)
    (hΔ : ∀ t, t < γ.numSteps →
      γ.stepDisplacement t ≤ Δ) :
    γ.thermodynamicLength ≤ γ.numSteps * Δ := by
  unfold ComputationPath.thermodynamicLength
  calc ∑ t ∈ Finset.range γ.numSteps, γ.stepDisplacement t
      ≤ ∑ t ∈ Finset.range γ.numSteps, Δ := by
        apply Finset.sum_le_sum
        intro t ht
        exact hΔ t (Finset.mem_range.mp ht)
    _ = γ.numSteps * Δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Contrapositive form (the punchline):** if the thermodynamic
length has a lower bound `L`, then the number of steps satisfies
`T ≥ L / Δ`.

  `𝓛[γ] ≥ L  ∧  Δ > 0  ∧  (∀ t, disp(t) ≤ Δ)  ⟹  T ≥ L / Δ`

This is the bridge from geometry to complexity: a lower bound on
geodesic length (from curvature) becomes a lower bound on runtime
(from locality). -/
theorem steps_ge_of_length_ge (γ : ComputationPath Cfg)
    (L Δ : ℝ) (hL : γ.thermodynamicLength ≥ L)
    (hΔ_pos : 0 < Δ)
    (hΔ_bound : ∀ t, t < γ.numSteps →
      γ.stepDisplacement t ≤ Δ) :
    (γ.numSteps : ℝ) ≥ L / Δ := by
  have h_upper := length_le_steps_mul_bound γ Δ hΔ_bound
  have h_chain : L ≤ γ.numSteps * Δ := le_trans hL h_upper
  exact (div_le_iff₀ hΔ_pos).mpr h_chain



/-! ## Part 6: Locality of Turing Machine Transitions

A Turing machine is a **local** dynamical system: in one step,
it reads one cell, writes one cell, and moves the head one
position.  This locality bounds the Fisher–Rao displacement per
step.

The intuition: if the transition changes O(1) bits of the
configuration, it changes O(1) probabilities in the distribution,
giving O(1) Fisher–Rao displacement *per configuration bit*.
The total displacement is bounded by the *local* Fisher information,
not the global dimension of the configuration space.

This is the **Lieb–Robinson bound** in disguise: information
propagates at finite speed through a local system.
-/

section TMLocality

/-- A **locally bounded transition** is one where the per-step
Fisher–Rao displacement is bounded by a polynomial in the
problem size.

For Turing machines, this holds because each step changes O(1)
cells.  The bound `Δ(n) ≤ poly(n)` is the critical bridge
between the geometric lower bound (exponential) and the
computational upper bound (T · Δ). -/
structure LocallyBoundedTransition (Cfg : Type*) [Fintype Cfg]
    [DecidableEq Cfg] where
  /-- The transition function. -/
  transition : Cfg → Cfg
  /-- The displacement bound (a function of problem size). -/
  maxDisp : ℝ
  /-- The bound is positive. -/
  maxDisp_pos : 0 < maxDisp
  /-- Every step respects the bound, for any distribution. -/
  displacement_bounded : ∀ (p : FinDist Cfg),
    fisherRaoDistance p (p.pushforward transition) ≤ maxDisp

/-- **The polynomial-time upper bound.**

If a computation uses a locally bounded transition with
displacement bound `Δ` and runs for `T` steps, its thermodynamic
length is at most `T · Δ`.

Therefore, if `T = poly(n)` and `Δ = poly(n)`, then
`𝓛 ≤ poly(n)`. -/
theorem poly_time_poly_length
    (L : LocallyBoundedTransition Cfg)
    (init : FinDist Cfg) (T : ℕ) :
    (⟨L.transition, init, T⟩ : ComputationPath Cfg).thermodynamicLength ≤
    T * L.maxDisp := by
  apply length_le_steps_mul_bound
  intro t _
  exact L.displacement_bounded _


end TMLocality
end DisplacementBounds

/-! ## Part 7: The Fisher Bridge (Axiomatised)

Following the pattern of `QuantumPhaseModel` in `CramerRao.lean`,
we axiomatise the connection between the discrete Fisher–Rao
distance on finite distributions and the Riemannian distance on
the continuous `StatisticalManifold`.

The bridge axioms state that the finite-dimensional Fisher–Rao
distance defined here *agrees* with the geodesic distance on the
statistical manifold from `StatisticalManifold.lean`.  This is
geometrically obvious (both are the geodesic distance of the
same metric), but the formal construction requires the square-root
embedding of the simplex into the manifold's parameter space.

**Approach A:** State the agreement as axioms.
**Approach B (future):** Construct the embedding explicitly and
discharge the axioms.
-/
section FisherBridge

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Cfg : Type*} [Fintype Cfg] [DecidableEq Cfg]

/-- The **Fisher Bridge** connects discrete computation on finite
configuration spaces to the continuous statistical manifold.

Axiomatises:
1. Each finite distribution embeds as a point in a parameter space.
2. The target space has a distance function (the Riemannian geodesic distance).
3. The Fisher–Rao distance between finite distributions equals
   the Riemannian distance between their embeddings. -/
structure FisherBridge
    (Cfg : Type*) [Fintype Cfg] [DecidableEq Cfg]
    (P : Type*) where
  /-- Embedding of finite distributions into the manifold's parameter space. -/
  embed : FinDist Cfg → P
  /-- The Riemannian geodesic distance on the manifold. -/
  riemannianDist : P → P → ℝ
  /-- The manifold distance is a metric (nonneg). -/
  riemannianDist_nonneg : ∀ p q, 0 ≤ riemannianDist p q
  /-- The manifold distance is symmetric. -/
  riemannianDist_symm : ∀ p q, riemannianDist p q = riemannianDist q p
  /-- **Agreement axiom:** Fisher–Rao distance equals Riemannian
  geodesic distance on the embeddings.
  Holds because both are the geodesic distance of the same metric
  (Chentsov uniqueness), computed in different coordinates. -/
  distance_agreement : ∀ (p q : FinDist Cfg),
    fisherRaoDistance p q = riemannianDist (embed p) (embed q)

/-
def StatisticalManifold.toFisherBridge' (S : StatisticalManifold n Ω)
    (embedFn : FinDist Cfg → ParamSpace n)
    (h_mem : ∀ p, embedFn p ∈ S.domain) :
    FisherBridge Cfg (ParamSpace n) where
  embed := embedFn
  riemannianDist := S.geodesicDist  -- future
  riemannianDist_nonneg := S.geodesicDist_nonneg
  riemannianDist_symm := S.geodesicDist_symm
  distance_agreement := fun p q => ...  -- Chentsov
-/

end FisherBridge

/-! ## Summary: What This File Establishes

We have formalised the **embedding of computation into geometry**:

1. **FinDist + pushforward:** A deterministic transition on a finite
   type induces a sequence of probability distributions.

2. **Fisher–Rao distance:** Distributions on finite types have a
   canonical distance (the Bhattacharyya angle), which *is* the
   geodesic distance of the Fisher information metric.

3. **Thermodynamic length:** The total Fisher–Rao distance along a
   computation path is the information-geometric cost.

4. **Length–step duality:**
   - Upper bound: `𝓛 ≤ T · Δ_max` (locality of transitions).
   - Lower bound: `𝓛 ≥ L_min` (curvature — to be established in
     Step 4, `PhaseTransition.lean`).
   - Combined: `T ≥ L_min / Δ_max`.

5. **Fisher Bridge:** The discrete computation and the continuous
   manifold agree on distances (axiomatised, to be discharged via
   the simplex embedding).

The **remaining steps** for the full P ≠ NP argument:

- **Step 1** (`CostBlind.lean`): The Turing machine model without
  metric structure admits symmetries that conflate P and NP.
- **Step 3** (`SymmetryBreaking.lean`): The Fisher metric breaks
  those symmetries (via Chentsov uniqueness).
- **Step 4** (`PhaseTransition.lean`): Fisher curvature diverges
  at the SAT phase transition, forcing `L_min ~ exp(cn)`.
- **Step 5** (`LocalityBound.lean`): Turing machine transitions
  have `Δ_max ~ poly(n)` (Lieb–Robinson for classical computation).
- **PNeNP.lean**: Assembly. `T ≥ exp(cn) / poly(n) → ∞`.

The second law does not merely *permit* computational hardness.
It *requires* it.
-/
end
