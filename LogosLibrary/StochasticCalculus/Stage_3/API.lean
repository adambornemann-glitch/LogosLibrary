/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_3/API.lean
-/
import LogosLibrary.StochasticCalculus.Stage_3.HolderMetric.Metric
import LogosLibrary.StochasticCalculus.Stage_3.HolderMetric.Complete
import LogosLibrary.StochasticCalculus.Stage_3.Geometric.Closed
/-!
# Stage 3 API — The Space of Rough Paths

Bundled interface for Stage 4 (RDE existence / Universal Limit Theorem).

## What this file provides

### 1. Complete metric space on rough paths
- `RoughPathOn V γ a b` — the type (Hölder constant existentially quantified)
- `roughPathOn_metricSpace` — the `MetricSpace` instance (requires `γ > 0`)
- `roughPathOn_completeSpace` — the `CompleteSpace` instance

### 2. Distance–pointwise bridge
- `roughPathOn_dist_controls_x` — `dist` → level-1 pointwise bound
- `roughPathOn_dist_controls_area` — `dist` → level-2 pointwise bound (d² scaling)
- `roughPathOn_dist_le_of_bounds` — level-wise pointwise bounds → `dist` bound

### 3. Coercion from parametrised type
- `RoughPath.toOn` — forget the explicit Hölder constant `C`

### 4. Geometric rough paths
- `GeometricRoughPathOn V γ a b` — the bundled type
- `IsGeometric` — the predicate
- `isGeometric_of_tendsto` — closedness under limits
- `geometricRoughPathOn_completeSpace` — completeness

### 5. Sequential completeness (direct form)
- `roughPathOn_cauchySeq_tendsto` — Cauchy sequences converge
- `geometricRoughPathOn_cauchySeq_tendsto` — geometric Cauchy sequences converge

## How Stage 4 uses this

```lean
-- Install the metric space
variable (hγ : 0 < γ)
letI := roughPathOn_metricSpace (V := V) hγ

-- 1. The Picard map Φ : ControlledPath → ControlledPath
--    (from Stage 2's rough_integral_closure)

-- 2. Φ is a contraction on a small interval [a, a + δ]:
--    dist (Φ Y₁) (Φ Y₂) ≤ λ · dist Y₁ Y₂  with λ < 1
--    Uses: roughPathOn_dist_le_of_bounds to bound the output distance
--          roughPathOn_dist_controls_x/area to bound integrands

-- 3. Banach fixed-point in the complete space:
--    roughPathOn_completeSpace gives CompleteSpace
--    → ∃! Y, Φ Y = Y

-- 4. For geometric rough paths:
--    geometricRoughPathOn_completeSpace gives the geometric version
--    The solution to dY = f(Y) d𝐗 with geometric 𝐗 is geometric
```

## Design decisions

* **`roughPathOn_metricSpace` is a `def`, not an `instance`.**
  It requires `hγ : 0 < γ` which the typeclass system cannot synthesize.
  Stage 4 should use `letI` to install it locally.

* **Distance is `d₁ + √d₂`** (Hölder form, not p-variation).
  This makes completeness trivial but requires the Hölder↔p-var
  equivalence (Phase 3.4, deferred) for the canonical ULT statement.

* **Geometric is a closed subtype, not a quotient.**
  The metric is inherited via `MetricSpace.induced`. This means
  `dist` on `GeometricRoughPathOn` is definitionally the same as
  `dist` on the underlying `RoughPathOn`.

## References

* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., §2, §8
* Lyons, T., *Differential equations driven by rough signals* (1998)
-/

open NormedTensorSquare Real Set Filter Topology

noncomputable section

namespace StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]

/-! ### Re-exports: types -/

-- RoughPathOn V γ a b           (from Defs.lean)
-- GeometricRoughPathOn V γ a b  (from Geometric/Defs.lean)
-- RoughPath.toOn                (from Defs.lean)

/-! ### Re-exports: metric structure -/

-- roughPathOn_metricSpace        (from Metric.lean)
-- roughPathOn_completeSpace      (from Complete.lean)
-- roughPathOn_pseudoMetricSpace  (from Metric.lean, always available)

/-! ### Re-exports: geometric structure -/

-- IsGeometric                    (from Geometric/Defs.lean)
-- isGeometric_of_tendsto         (from Geometric/Closed.lean)
-- geometricRoughPathOn_metricSpace   (from Geometric/Closed.lean)
-- geometricRoughPathOn_completeSpace (from Geometric/Closed.lean)

/-! ### Bundled setup helpers

These help Stage 4 install the metric space cleanly. -/

/-- Install the full metric + complete space structure in one go.

Usage in Stage 4:
```
  variable (hγ : 0 < γ)
  letI := roughPathOn_metricComplete (V := V) hγ
  -- now MetricSpace and CompleteSpace are both available
```
-/
structure RoughPathOnMetricComplete (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedTensorSquare V]
    (γ a b : ℝ) [CompleteSpace V] [CompleteSpace (T₂ V)] where
  hγ : 0 < γ
  metricSpace : MetricSpace (RoughPathOn V γ a b) :=
    roughPathOn_metricSpace hγ
  completeSpace : @CompleteSpace (RoughPathOn V γ a b) metricSpace.toUniformSpace := by
    convert roughPathOn_completeSpace hγ

/-! ### Summary of the Stage 3 → Stage 4 interface

Stage 4 imports this file and uses:

```lean
-- 0. Install metric structure
variable (hγ : 0 < γ)
letI : MetricSpace (RoughPathOn V γ a b) := roughPathOn_metricSpace hγ
haveI : CompleteSpace (RoughPathOn V γ a b) := roughPathOn_completeSpace hγ

-- 1. Convert parametrised rough paths
let 𝐗_on := 𝐗.toOn   -- RoughPath V γ C a b → RoughPathOn V γ a b

-- 2. Bound the distance from pointwise estimates
have h_dist := roughPathOn_dist_le_of_bounds hγ 𝐗 𝐘 hM₁ hM₂ h₁ h₂

-- 3. Extract pointwise estimates from distance
have h_x := roughPathOn_dist_controls_x hγ 𝐗 𝐘 has hst htb
have h_area := roughPathOn_dist_controls_area hγ 𝐗 𝐘 has hst htb

-- 4. Completeness for Banach fixed-point
-- (automatic from the CompleteSpace instance)

-- 5. Cauchy sequences converge (explicit form)
obtain ⟨𝐗_lim, h_conv⟩ := roughPathOn_cauchySeq_tendsto hγ 𝐗seq hCauchy

-- 6. Geometric version (for chain rule, Stratonovich)
letI : MetricSpace (GeometricRoughPathOn V γ a b) :=
  geometricRoughPathOn_metricSpace hγ
haveI : CompleteSpace (GeometricRoughPathOn V γ a b) :=
  geometricRoughPathOn_completeSpace hγ

-- 7. Closedness of geometric condition (for Picard on geometric paths)
have := isGeometric_of_tendsto 𝐗seq 𝐗_lim h_conv h_geom

-- 8. Lévy area decomposition (for Itô formula)
have := 𝐗.area_eq_half_tprod_add_levyArea hg has hst htb
```
-/

end StochCalc
