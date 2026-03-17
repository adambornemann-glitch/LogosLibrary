/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_3/HolderMetric/Triangle.lean
-/
import LogosLibrary.StochasticCalculus.Stage_3.HolderMetric.Defs
/-!
# Triangle inequality for the Hölder rough path distance

## Overview

We prove the triangle inequality

  `d(X, cZ) ≤ d(X, cY) + d(cY, cZ)`

for the Hölder rough path distance `d = d₁ + d₂^{1/2}`.

## Structure of the proof

The argument decomposes cleanly:

1. **Level-1 triangle** (`holderDist₁_triangle`):
   For each `(s, t)`, the norm triangle inequality gives
   `‖X₁(s,t) − X₃(s,t)‖ / |t−s|^γ ≤ d₁(X, cY) + d₁(cY, cZ)`.
   Taking `sSup`: `d₁(X, cZ) ≤ d₁(X, cY) + d₁(cY, cZ)`.

2. **Level-2 triangle** (`holderDist₂_triangle`):
   Identical argument for the area component.

3. **Square root triangle** (`rpow_half_triangle`):
   For `a, b ≥ 0`: `(a + b)^{1/2} ≤ a^{1/2} + b^{1/2}`.
   This is the concavity of `t ↦ t^{1/2}`, equivalently
   `√(a + b) ≤ √a + √b`. Combined with step 2:
   `d₂(X, cZ)^{1/2} ≤ d₂(X, cY)^{1/2} + d₂(cY, cZ)^{1/2}`.

4. **Combined** (`roughPathDist_triangle`): add steps 1 and 3.

## The sSup dance

Each level-$k$ triangle inequality requires showing that
`sSup S₁₃ ≤ sSup S₁₂ + sSup S₂₃` where `Sᵢⱼ` is the quotient
set for `(Xᵢ, Xⱼ)`. The strategy:

- Show every element of `S₁₃` is `≤ sSup S₁₂ + sSup S₂₃`
  (using pointwise triangle + `le_csSup` for each summand).
- Apply `csSup_le` to conclude.
- Handle the empty-set edge case (when `a = b`).

## References

* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., §8.1
-/

open NormedTensorSquare Real Set

noncomputable section

namespace StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]
variable {γ a b : ℝ}

/-! ### Auxiliary: square root triangle inequality

  `(a + b)^{1/2} ≤ a^{1/2} + b^{1/2}`  for `a, b ≥ 0`

This is the sub-additivity of `t ↦ t^{1/2}`, equivalently the
concavity inequality. We prove it by squaring both sides. -/

/-- Square root is sub-additive: `√(a + b) ≤ √a + √b` for `a, b ≥ 0`.
Stated in `rpow` form for compatibility with the rest of the development. -/
lemma rpow_half_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ (1/2 : ℝ) ≤ x ^ (1/2 : ℝ) + y ^ (1/2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have hsx := Real.sqrt_nonneg x
  have hsy := Real.sqrt_nonneg y
  rw [← Real.sqrt_sq (add_nonneg hsx hsy)]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg hsx hsy]

/-! ### Level-1 triangle inequality -/

/-- **Level-1 triangle inequality**: `d₁(X, cZ) ≤ d₁(X, cY) + d₁(cY, cZ)`.

Proof: for each `(s, t)` with `a ≤ s < t ≤ b`,
```
  ‖X(s,t) − Z(s,t)‖ / |t−s|^γ
    ≤ (‖X(s,t) − Y(s,t)‖ + ‖Y(s,t) − Z(s,t)‖) / |t−s|^γ
    = ‖X(s,t) − Y(s,t)‖ / |t−s|^γ + ‖Y(s,t) − Z(s,t)‖ / |t−s|^γ
    ≤ d₁(X, cY) + d₁(cY, cZ)
```
Then take `sSup`. -/
theorem holderDist₁_triangle (X cY cZ : RoughPathOn V γ a b) :
    holderDist₁ X cZ ≤ holderDist₁ X cY + holderDist₁ cY cZ := by
  apply holderDist₁_le_of_bound
  · exact add_nonneg (holderDist₁_nonneg X cY) (holderDist₁_nonneg cY cZ)
  · intro s t has hst htb
    have hts_nn : 0 ≤ |t - s| ^ γ := rpow_nonneg (abs_nonneg _) _
    calc ‖X.x s t - cZ.x s t‖
        = ‖(X.x s t - cY.x s t) + (cY.x s t - cZ.x s t)‖ := by
          congr 1; abel
      _ ≤ ‖X.x s t - cY.x s t‖ + ‖cY.x s t - cZ.x s t‖ :=
          norm_add_le _ _
      _ ≤ holderDist₁ X cY * |t - s| ^ γ + holderDist₁ cY cZ * |t - s| ^ γ := by
          gcongr
          · exact holderDist₁_controls X cY has hst htb
          · exact holderDist₁_controls cY cZ has hst htb
      _ = (holderDist₁ X cY + holderDist₁ cY cZ) * |t - s| ^ γ := by ring

/-! ### Level-2 triangle inequality -/

/-- **Level-2 triangle inequality**: `d₂(X, cZ) ≤ d₂(X, cY) + d₂(cY, cZ)`. -/
theorem holderDist₂_triangle (X cY cZ : RoughPathOn V γ a b) :
    holderDist₂ X cZ ≤ holderDist₂ X cY + holderDist₂ cY cZ := by
  apply holderDist₂_le_of_bound
  · exact add_nonneg (holderDist₂_nonneg X cY) (holderDist₂_nonneg cY cZ)
  · intro s t has hst htb
    calc ‖X.area s t - cZ.area s t‖
        = ‖(X.area s t - cY.area s t) + (cY.area s t - cZ.area s t)‖ := by
          congr 1; abel
      _ ≤ ‖X.area s t - cY.area s t‖ + ‖cY.area s t - cZ.area s t‖ :=
          norm_add_le _ _
      _ ≤ holderDist₂ X cY * |t - s| ^ (2 * γ) +
          holderDist₂ cY cZ * |t - s| ^ (2 * γ) := by
          gcongr
          · exact holderDist₂_controls X cY has hst htb
          · exact holderDist₂_controls cY cZ has hst htb
      _ = (holderDist₂ X cY + holderDist₂ cY cZ) * |t - s| ^ (2 * γ) := by ring

/-! ### Square root of level-2 triangle -/

/-- **√d₂ triangle**: `d₂(X, cZ)^{1/2} ≤ d₂(X, cY)^{1/2} + d₂(cY, cZ)^{1/2}`.

This combines the level-2 triangle with sub-additivity of `√`. -/
theorem holderDist₂_rpow_half_triangle (X cY cZ : RoughPathOn V γ a b) :
    (holderDist₂ X cZ) ^ (1/2 : ℝ) ≤
      (holderDist₂ X cY) ^ (1/2 : ℝ) + (holderDist₂ cY cZ) ^ (1/2 : ℝ) := by
  calc (holderDist₂ X cZ) ^ (1/2 : ℝ)
      ≤ (holderDist₂ X cY + holderDist₂ cY cZ) ^ (1/2 : ℝ) :=
        rpow_le_rpow (holderDist₂_nonneg X cZ)
          (holderDist₂_triangle X cY cZ) (by norm_num : (0:ℝ) ≤ 1/2)
    _ ≤ _ := rpow_half_add_le (holderDist₂_nonneg X cY) (holderDist₂_nonneg cY cZ)

/-! ### Combined triangle inequality -/

/-- **The triangle inequality for the Hölder rough path distance.**

  `d(X, cZ) ≤ d(X, cY) + d(cY, cZ)`

where `d = d₁ + d₂^{1/2}`. -/
theorem roughPathDist_triangle (X cY cZ : RoughPathOn V γ a b) :
    roughPathDist X cZ ≤ roughPathDist X cY + roughPathDist cY cZ := by
  unfold roughPathDist
  -- Goal: d₁(X,cZ) + d₂(X,cZ)^½ ≤ (d₁(X,cY) + d₂(X,cY)^½) + (d₁(cY,cZ) + d₂(cY,cZ)^½)
  -- Rearrange RHS: = (d₁(X,cY) + d₁(cY,cZ)) + (d₂(X,cY)^½ + d₂(cY,cZ)^½)
  -- Then apply level-1 triangle + √d₂ triangle.
  have h₁ := holderDist₁_triangle X cY cZ
  have h₂ := holderDist₂_rpow_half_triangle X cY cZ
  linarith

/-! ### Corollaries -/

/-- `d₁` satisfies the triangle inequality in the weak form needed for
the separation argument: if `d = 0` then `d₁ = 0`. -/
lemma holderDist₁_eq_zero_of_roughPathDist_eq_zero
    (X cY : RoughPathOn V γ a b)
    (h : roughPathDist X cY = 0) :
    holderDist₁ X cY = 0 := by
  have h₁ := holderDist₁_nonneg X cY
  have h₂ := rpow_nonneg (holderDist₂_nonneg X cY) (1/2 : ℝ)
  linarith [show holderDist₁ X cY + (holderDist₂ X cY) ^ (1/2 : ℝ) = 0 from h]

/-- Similarly, `d = 0` implies `d₂ = 0`. -/
lemma holderDist₂_eq_zero_of_roughPathDist_eq_zero
    (X cY : RoughPathOn V γ a b)
    (h : roughPathDist X cY = 0) :
    holderDist₂ X cY = 0 := by
  have h₁ := holderDist₁_nonneg X cY
  have h₂ := rpow_nonneg (holderDist₂_nonneg X cY) (1/2 : ℝ)
  have hsum : holderDist₁ X cY + (holderDist₂ X cY) ^ (1/2 : ℝ) = 0 := h
  have hsqrt_zero : (holderDist₂ X cY) ^ (1/2 : ℝ) = 0 := by linarith
  -- √d₂ = 0 implies d₂ = 0
  rwa [← Real.sqrt_eq_rpow, Real.sqrt_eq_zero (holderDist₂_nonneg X cY)] at hsqrt_zero

/-- **Separation**: `d(X, cY) = 0 ↔ X = cY`, assuming `γ > 0`.

This packages the separation axiom for `Metric.lean`. -/
theorem roughPathDist_eq_zero_iff (X cY : RoughPathOn V γ a b) (hγ : 0 < γ) :
    roughPathDist X cY = 0 ↔ X = cY := by
  constructor
  · intro h
    unfold roughPathDist at h
    have hd₁_nn := holderDist₁_nonneg X cY
    have hd₂_nn := holderDist₂_nonneg X cY
    have hd₂_sqrt_nn : 0 ≤ (holderDist₂ X cY) ^ (1/2 : ℝ) := rpow_nonneg hd₂_nn _
    -- d₁ + √d₂ = 0 with both nonneg forces each to vanish
    have hd₁ : holderDist₁ X cY = 0 := le_antisymm (by linarith) hd₁_nn
    have hd₂_sqrt : (holderDist₂ X cY) ^ (1/2 : ℝ) = 0 :=
      le_antisymm (by linarith) hd₂_sqrt_nn
    -- √d₂ = 0 implies d₂ = 0 (contrapositive: d₂ > 0 ⟹ d₂^(1/2) > 0)
    have hd₂ : holderDist₂ X cY = 0 := by
      by_contra hne
      exact absurd hd₂_sqrt
        (ne_of_gt (rpow_pos_of_pos (lt_of_le_of_ne hd₂_nn (Ne.symm hne)) _))
    -- Pointwise equality on the domain
    have hx := eq_x_of_holderDist₁_zero X cY hγ hd₁
    have ha := eq_area_of_holderDist₂_zero X cY hγ hd₂
    -- Extend to full function equality via the default axiom
    apply RoughPathOn.ext
    · ext s t
      by_cases h_dom : a ≤ s ∧ s ≤ t ∧ t ≤ b
      · exact hx s t h_dom.1 h_dom.2.1 h_dom.2.2
      · rw [X.x_default s t h_dom, cY.x_default s t h_dom]
    · ext s t
      by_cases h_dom : a ≤ s ∧ s ≤ t ∧ t ≤ b
      · exact ha s t h_dom.1 h_dom.2.1 h_dom.2.2
      · rw [X.area_default s t h_dom, cY.area_default s t h_dom]
  · rintro rfl
    exact roughPathDist_self _

end StochCalc
