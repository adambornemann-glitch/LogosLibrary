/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_3/HolderMetric/Metric.lean
-/
import LogosLibrary.StochasticCalculus.Stage_3.HolderMetric.Triangle
/-!
# MetricSpace instance for the Hölder rough path space

## Overview

This file assembles the `MetricSpace` instance on `RoughPathOn V γ a b`
from the components proved in `Defs.lean` and `Triangle.lean`:

- `dist := roughPathDist`
- `dist_self` from `roughPathDist_self`
- `dist_comm` from `roughPathDist_symm`
- `dist_triangle` from `roughPathDist_triangle`
- `eq_of_dist_eq_zero` from `roughPathDist_eq_zero_iff`

## The γ > 0 hypothesis

The separation axiom (`dist = 0 ⟹ eq`) requires `γ > 0`. For `γ ≤ 0`,
the Hölder seminorm `sup ‖·‖ / |·|^γ` does not separate points (when
`γ < 0` it diverges; when `γ = 0` it only sees `sup ‖·‖` which can
vanish without pointwise vanishing of the quotient).

Mathematically, rough paths always have `γ ∈ (1/4, 1/2]` (or more
generally `γ > 0`), so this hypothesis is harmless. We carry it as
a variable throughout.

## The PseudoMetricSpace layer

Mathlib's `MetricSpace` extends `PseudoMetricSpace`. We build the
pseudo-metric first (which does *not* need separation), then upgrade.
This is the standard Mathlib pattern.

## What Stage 4 consumes

```lean
instance : MetricSpace (RoughPathOn V γ a b) := ...

-- Then Stage 4 can write:
-- `dist X cY` instead of `roughPathDist X cY`
-- `Metric.ball X r` for open balls
-- `CauchySeq` for Cauchy sequences
-- `CompleteSpace` (from Complete.lean)
```

## References

* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., §8.1
-/

open NormedTensorSquare Real Set

noncomputable section

namespace StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]

/-! ### PseudoMetricSpace (no separation required) -/

/-- `PseudoMetricSpace` on `RoughPathOn V γ a b`.

This does not require `γ > 0` — the triangle inequality, symmetry,
and `dist_self = 0` all hold for any `γ`. Only separation needs `γ > 0`.

We use this as an intermediate step; Stage 4 will use the full
`MetricSpace` instance below. -/
noncomputable instance roughPathOn_pseudoMetricSpace
    {γ a b : ℝ} :
    PseudoMetricSpace (RoughPathOn V γ a b) where
  dist := roughPathDist
  dist_self := roughPathDist_self
  dist_comm := roughPathDist_symm
  dist_triangle := roughPathDist_triangle
  edist_dist := fun _ _ => rfl

/-- `dist` is definitionally `roughPathDist`. -/
@[simp] lemma roughPathOn_dist_eq {γ a b : ℝ}
    (X cY : RoughPathOn V γ a b) :
    dist X cY = roughPathDist X cY := rfl

/-! ### MetricSpace (requires γ > 0 for separation) -/

/-- **`MetricSpace` on `RoughPathOn V γ a b`** for `γ > 0`.

This is the main result of Phase 3.1 (together with completeness).
It provides the full metric space structure needed for Stage 4's
Banach fixed-point theorem.

The construction upgrades the `PseudoMetricSpace` by supplying the
separation axiom `dist X cY = 0 → X = cY`, which requires `γ > 0`. -/
noncomputable def roughPathOn_metricSpace
    {γ a b : ℝ} (hγ : 0 < γ) :
    MetricSpace (RoughPathOn V γ a b) where
  eq_of_dist_eq_zero := fun {X cY} h =>
    (roughPathDist_eq_zero_iff X cY hγ).mp h


/-! ### Convenience API -/

variable {γ a b : ℝ} (hγ : 0 < γ)

/-- `dist` decomposes into level-1 and level-2 components. -/
lemma roughPathOn_dist_decomp
    (X cY : RoughPathOn V γ a b) :
    dist X cY = holderDist₁ X cY + (holderDist₂ X cY) ^ (1/2 : ℝ) := rfl

/-- `dist` is nonneg (already from PseudoMetricSpace, but useful to state). -/
lemma roughPathOn_dist_nonneg
    (X cY : RoughPathOn V γ a b) :
    0 ≤ dist X cY :=
  roughPathDist_nonneg X cY

/-- `dist` controls level-1 pointwise differences.

This is the lemma Stage 4 uses most: it converts metric-space
hypotheses (`dist Xⁿ X → 0`) into pointwise convergence of the
level-1 increments. -/
lemma roughPathOn_dist_controls_x
    (X cY : RoughPathOn V γ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s < t) (htb : t ≤ b) :
    ‖X.x s t - cY.x s t‖ ≤ dist X cY * |t - s| ^ γ :=
  roughPathDist_controls₁ X cY has hst htb

/-- `dist` controls level-2 pointwise differences (with quadratic scaling).

  `‖𝕏(s,t) − 𝕐(s,t)‖ ≤ dist(X, cY)² · |t−s|^{2γ}` -/
lemma roughPathOn_dist_controls_area
    (X cY : RoughPathOn V γ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s < t) (htb : t ≤ b) :
    ‖X.area s t - cY.area s t‖ ≤ dist X cY ^ 2 * |t - s| ^ (2 * γ) :=
  roughPathDist_controls₂ X cY has hst htb

/-- `dist` is controlled by explicit level-wise bounds.

This is the converse direction: if you have pointwise Hölder bounds
on each level, you can bound the distance. Needed for showing
convergence in Stage 4. -/
lemma roughPathOn_dist_le_of_bounds
    (X cY : RoughPathOn V γ a b) {M₁ M₂ : ℝ}
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ s t, a ≤ s → s < t → t ≤ b →
      ‖X.x s t - cY.x s t‖ ≤ M₁ * |t - s| ^ γ)
    (h₂ : ∀ s t, a ≤ s → s < t → t ≤ b →
      ‖X.area s t - cY.area s t‖ ≤ M₂ * |t - s| ^ (2 * γ)) :
    dist X cY ≤ M₁ + M₂ ^ (1/2 : ℝ) := by
  simp only [roughPathOn_dist_eq]
  unfold roughPathDist
  gcongr
  · exact holderDist₁_le_of_bound X cY hM₁ h₁
  · exact holderDist₂_nonneg X cY
  · exact holderDist₂_le_of_bound X cY hM₂ h₂

end StochCalc
