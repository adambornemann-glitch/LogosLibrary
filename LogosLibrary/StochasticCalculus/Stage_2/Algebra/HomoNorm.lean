/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_2/Algebra/HomoNorm.lean
-/
import LogosLibrary.StochasticCalculus.Stage_2.Algebra.GroupLike
/-!
# Homogeneous Norm and Metric on G⁽²⁾(V)

## Overview

The **homogeneous norm** on the free step-2 nilpotent group `G⁽²⁾(V)` is

    ‖g‖_{cc} = max(‖x‖, ‖Anti(𝕏)‖^{1/2})

where `g = (x, 𝕏)` is a group-like element. The `1/2` exponent on the area
reflects **parabolic scaling**: area scales as length², so taking the square
root brings it to the same homogeneity as the level-1 component.

The associated left-invariant **metric** is

    d(g, h) = ‖g⁻¹ · h‖_{cc}

This is a quasi-metric: it satisfies a quasi-triangle inequality

    d(g, k) ≤ C · (d(g, h) + d(h, k))

with a universal constant `C`. (In fact, for the step-2 nilpotent group,
one can show `C = 4` suffices.) For a genuine metric, one could take the
Carnot–Carathéodory distance, but the quasi-metric is equivalent and much
easier to work with in a formalization.

## Key results

* `homoNorm` — the homogeneous norm definition
* `homoNorm_nonneg` — non-negativity
* `homoNorm_eq_zero_iff` — positive definiteness
* `homoNorm_inv` — `‖g⁻¹‖ = ‖g‖`
* `homoNorm_mul_le` — quasi-triangle: `‖g · h‖ ≤ C(‖g‖ + ‖h‖)`
* `norm_x_le_homoNorm` — level-1 bound: `‖x‖ ≤ ‖g‖_{cc}`
* `norm_area_le_homoNorm_sq` — level-2 bound: `‖A‖ ≤ ‖g‖_{cc}²`
* `roughDist` — the left-invariant quasi-metric
* `roughDist_self`, `roughDist_symm`, `roughDist_triangle` — quasi-metric axioms

## Why not a genuine metric?

The Carnot–Carathéodory distance — defined as the infimum of lengths of
horizontal paths connecting two points — is a genuine metric, and it is
equivalent to our `homoNorm`. But proving the triangle inequality for it
requires a compactness argument (existence of geodesics), which is heavy
formalization work for no analytical payoff: every estimate in rough path
theory uses the quasi-metric, not the CC distance. We therefore work with
the quasi-metric throughout.

## Design notes

The norm uses `Anti(𝕏)` (the Lévy area) rather than `𝕏` itself. This is
because for group-like elements, `𝕏 = ½(x ⊗ x) + A`, so `‖𝕏‖` conflates
the level-1 data (via `x ⊗ x`) with the genuinely new level-2 data `A`.
The homogeneous norm cleanly separates the two scales.

We prove both "extraction" bounds: `‖x‖ ≤ ‖g‖_{cc}` and `‖A‖ ≤ ‖g‖_{cc}²`.
These are used everywhere in the rough path estimates — the first in bounding
increments, the second in bounding area terms.

## References

* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Chapter 2
* Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Ch. 8
-/

open NormedTensorSquare StochCalc.TruncTensor₂ StochCalc.GroupLike₂ Real

noncomputable section

namespace StochCalc

namespace GroupLike₂

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]

/-! ## The homogeneous norm -/

/-- The **homogeneous norm** on `G⁽²⁾(V)`:

    `‖g‖_{cc} = max(‖x‖, ‖Anti(𝕏)‖^{1/2})`

The square root on the area reflects parabolic scaling: under the dilation
`δ_λ(x, A) = (λx, λ²A)`, both terms scale as `λ`. -/
def homoNorm (g : GroupLike₂ V) : ℝ :=
  max ‖g.x‖ (‖area g‖ ^ (2⁻¹ : ℝ))

/-! ## Basic properties -/

lemma homoNorm_nonneg (g : GroupLike₂ V) : 0 ≤ homoNorm g :=
  le_max_of_le_left (norm_nonneg _)

lemma norm_x_le_homoNorm (g : GroupLike₂ V) :
    ‖g.x‖ ≤ homoNorm g :=
  le_max_left _ _

lemma norm_area_sqrt_le_homoNorm (g : GroupLike₂ V) :
    ‖area g‖ ^ (2⁻¹ : ℝ) ≤ homoNorm g :=
  le_max_right _ _

/-- **Level-2 extraction bound**: `‖area(g)‖ ≤ ‖g‖_{cc}²`.

This is the "unsquare-rooted" version: from `‖A‖^{1/2} ≤ N` we get `‖A‖ ≤ N²`.
Used in every rough path estimate involving the area. -/
lemma norm_area_le_homoNorm_sq (g : GroupLike₂ V) :
    ‖area g‖ ≤ homoNorm g ^ 2 := by
  have h := norm_area_sqrt_le_homoNorm g
  have hA := norm_nonneg (area g)
  calc ‖area g‖
      = (‖area g‖ ^ (2⁻¹ : ℝ)) ^ (2 : ℕ) := by
          rw [← rpow_natCast (‖area g‖ ^ (2⁻¹ : ℝ)) 2, ← rpow_mul hA,
              show (2⁻¹ : ℝ) * (↑(2 : ℕ) : ℝ) = 1 from by norm_num, rpow_one]
    _ ≤ homoNorm g ^ 2 := pow_le_pow_left₀ (rpow_nonneg hA _) h 2

/-- **Level-2 extraction, full area**: `‖𝕏‖ ≤ ½‖x‖² + ‖g‖_{cc}²`.

Combines the group-like reconstruction `𝕏 = ½(x⊗x) + A` with the extraction bounds. -/
lemma norm_𝕏_le (g : GroupLike₂ V) :
    ‖g.𝕏‖ ≤ (2⁻¹ : ℝ) * ‖g.x‖ ^ 2 + homoNorm g ^ 2 := by
  rw [g.𝕏_eq]
  calc ‖(2⁻¹ : ℝ) • (g.x ⊗ₜ g.x) + area g‖
      ≤ ‖(2⁻¹ : ℝ) • (g.x ⊗ₜ g.x)‖ + ‖area g‖ := norm_add_le _ _
    _ ≤ (2⁻¹ : ℝ) * ‖g.x ⊗ₜ g.x‖ + ‖area g‖ := by
        gcongr
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (2⁻¹ : ℝ) * (‖g.x‖ * ‖g.x‖) + ‖area g‖ := by
        gcongr; exact norm_tprod_le g.x g.x
    _ = (2⁻¹ : ℝ) * ‖g.x‖ ^ 2 + ‖area g‖ := by ring_nf
    _ ≤ (2⁻¹ : ℝ) * ‖g.x‖ ^ 2 + homoNorm g ^ 2 := by
        gcongr; exact norm_area_le_homoNorm_sq g

/-! ## Positive definiteness -/

/-- `‖g‖_{cc} = 0` if and only if `g = e` (the identity). -/
lemma homoNorm_eq_zero_iff (g : GroupLike₂ V) :
    homoNorm g = 0 ↔ g = e := by
  constructor
  · intro h
    have hx : ‖g.x‖ = 0 := by
      have := norm_x_le_homoNorm g; linarith [norm_nonneg g.x]
    have hA_sqrt : ‖area g‖ ^ (2⁻¹ : ℝ) = 0 := by
      have := norm_area_sqrt_le_homoNorm g
      linarith [rpow_nonneg (norm_nonneg (area g)) (2⁻¹ : ℝ)]
    have hA : ‖area g‖ = 0 := by
      by_contra h'
      have : 0 < ‖area g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h')
      linarith [rpow_pos_of_pos this (2⁻¹ : ℝ)]
    exact ext_area (norm_eq_zero.mp hx)
      ((norm_eq_zero.mp hA).trans e_area.symm)
  · intro h
    rw [h]; simp [homoNorm, norm_zero, Real.zero_rpow (by norm_num : (2⁻¹ : ℝ) ≠ 0)]

/-! ## Symmetry: ‖g⁻¹‖ = ‖g‖ -/

/-- The homogeneous norm is symmetric under inversion. -/
lemma homoNorm_inv (g : GroupLike₂ V) :
    homoNorm g⁻¹ = homoNorm g := by
  simp only [homoNorm, inv_x', inv_area g, norm_neg]

/-! ## Quasi-triangle inequality

The main analytical estimate:

    `‖g · h‖_{cc} ≤ C · (‖g‖_{cc} + ‖h‖_{cc})`

The constant `C` arises because the area of a product has a cross-term:

    `A_{gh} = A_g + Anti(x_g ⊗ x_h) + A_h`

and `‖Anti(x ⊗ y)‖^{1/2}` cannot be bounded by `‖x‖^{1/2} + ‖y‖^{1/2}`
(wrong homogeneity). Instead, `‖Anti(x ⊗ y)‖ ≤ ‖x‖·‖y‖ ≤ N_g · N_h`
and `(a + b + c)^{1/2} ≤ a^{1/2} + b^{1/2} + c^{1/2}`, giving an
extra factor. For step-2 groups, `C = 4` suffices. -/

/-- **Quasi-triangle inequality**: `‖g · h‖_{cc} ≤ 4 · (‖g‖_{cc} + ‖h‖_{cc})`.

The proof bounds each component of `g · h`:
- Level 1: `‖x + y‖ ≤ ‖x‖ + ‖y‖ ≤ N_g + N_h`
- Level 2: `‖A_g + Anti(x⊗y) + A_h‖ ≤ ‖A_g‖ + ‖x‖·‖y‖ + ‖A_h‖ ≤ N_g² + N_g·N_h + N_h²`
  and `(N_g² + N_g N_h + N_h²)^{1/2} ≤ 2(N_g + N_h)` since
  `N_g² + N_g N_h + N_h² ≤ (N_g + N_h)² + N_g N_h ≤ 2(N_g + N_h)²`. -/
theorem homoNorm_mul_le (g h : GroupLike₂ V) :
    homoNorm (g * h) ≤ 4 * (homoNorm g + homoNorm h) := by
  set Ng := homoNorm g
  set Nh := homoNorm h
  have hNg : 0 ≤ Ng := homoNorm_nonneg g
  have hNh : 0 ≤ Nh := homoNorm_nonneg h
  -- Bound level-1
  have h1 : ‖(g * h).x‖ ≤ Ng + Nh := by
    rw [mul_x']
    calc ‖g.x + h.x‖ ≤ ‖g.x‖ + ‖h.x‖ := norm_add_le _ _
      _ ≤ Ng + Nh := add_le_add (norm_x_le_homoNorm g) (norm_x_le_homoNorm h)
  -- Bound level-2 area norm
  have h2_area : ‖area (g * h)‖ ≤ Ng ^ 2 + Ng * Nh + Nh ^ 2 := by
    rw [mul_area]
    calc ‖area g + anti (g.x ⊗ₜ h.x) + area h‖
        ≤ ‖area g‖ + ‖anti (g.x ⊗ₜ h.x)‖ + ‖area h‖ := by
          calc _ ≤ ‖area g + anti (g.x ⊗ₜ h.x)‖ + ‖area h‖ := norm_add_le _ _
            _ ≤ (‖area g‖ + ‖anti (g.x ⊗ₜ h.x)‖) + ‖area h‖ := by
                gcongr; exact norm_add_le _ _
      _ ≤ Ng ^ 2 + Ng * Nh + Nh ^ 2 := by
          have hAg := norm_area_le_homoNorm_sq g
          have hAh := norm_area_le_homoNorm_sq h
          have hanti : ‖anti (g.x ⊗ₜ h.x)‖ ≤ ‖g.x‖ * ‖h.x‖ :=
            (norm_anti_le _).trans (norm_tprod_le g.x h.x)
          have hcross : ‖g.x‖ * ‖h.x‖ ≤ Ng * Nh :=
            mul_le_mul (norm_x_le_homoNorm g) (norm_x_le_homoNorm h)
              (norm_nonneg _) hNg
          linarith
  -- Bound the square root of the area
  have h2_sqrt : ‖area (g * h)‖ ^ (2⁻¹ : ℝ) ≤ 2 * (Ng + Nh) := by
    have h_bound : Ng ^ 2 + Ng * Nh + Nh ^ 2 ≤ (2 * (Ng + Nh)) ^ 2 := by nlinarith
    have hle : ‖area (g * h)‖ ≤ (2 * (Ng + Nh)) ^ 2 := h2_area.trans h_bound
    have hb : 0 ≤ 2 * (Ng + Nh) := by linarith
    calc ‖area (g * h)‖ ^ (2⁻¹ : ℝ)
        ≤ ((2 * (Ng + Nh)) ^ 2) ^ (2⁻¹ : ℝ) :=
          rpow_le_rpow (norm_nonneg _) hle (by positivity)
      _ = 2 * (Ng + Nh) := by
          rw [← rpow_natCast (2 * (Ng + Nh)) 2, ← rpow_mul hb,
              show ((2 : ℕ) : ℝ) * (2⁻¹ : ℝ) = 1 from by norm_num, rpow_one]
  -- Combine: homoNorm = max(‖x‖, ‖A‖^{1/2})
  unfold homoNorm
  calc max ‖(g * h).x‖ (‖area (g * h)‖ ^ (2⁻¹ : ℝ))
      ≤ max (Ng + Nh) (2 * (Ng + Nh)) := by
        apply max_le_max h1 h2_sqrt
    _ = 2 * (Ng + Nh) := by
        rw [max_eq_right]; linarith
    _ ≤ 4 * (Ng + Nh) := by linarith

/-! ## The left-invariant quasi-metric -/

/-- The **left-invariant quasi-metric** on `G⁽²⁾(V)`:

    `d(g, h) = ‖g⁻¹ · h‖_{cc}`

This is a quasi-metric (satisfies a quasi-triangle inequality with constant `C`)
and is left-invariant: `d(k·g, k·h) = d(g, h)`. -/
def roughDist (g h : GroupLike₂ V) : ℝ :=
  homoNorm (g⁻¹ * h)

lemma roughDist_self (g : GroupLike₂ V) :
    roughDist g g = 0 := by
  simp [roughDist, homoNorm_eq_zero_iff]
  exact inv_mul g

lemma roughDist_nonneg (g h : GroupLike₂ V) :
    0 ≤ roughDist g h :=
  homoNorm_nonneg _

lemma roughDist_eq_zero_iff (g h : GroupLike₂ V) :
    roughDist g h = 0 ↔ g = h := by
  rw [roughDist, homoNorm_eq_zero_iff]
  exact inv_mul_eq_one

/-- Symmetry: `d(g, h) = d(h, g)`.

Proof: `‖g⁻¹ h‖ = ‖(g⁻¹ h)⁻¹‖ = ‖h⁻¹ g‖`. -/
lemma roughDist_symm (g h : GroupLike₂ V) :
    roughDist g h = roughDist h g := by
  simp only [roughDist]
  rw [← homoNorm_inv (g⁻¹ * h), mul_inv_rev]
  rw [@InvolutiveInv.inv_inv]

/-- Quasi-triangle inequality: `d(g, k) ≤ C · (d(g, h) + d(h, k))`. -/
lemma roughDist_triangle (g h k : GroupLike₂ V) :
    roughDist g k ≤ 4 * (roughDist g h + roughDist h k) := by
  simp only [roughDist]
  -- g⁻¹ k = (g⁻¹ h) · (h⁻¹ k)
  have : g⁻¹ * k = (g⁻¹ * h) * (h⁻¹ * k) := by group
  rw [this]
  exact homoNorm_mul_le _ _

/-- Left invariance: `d(k·g, k·h) = d(g, h)`. -/
lemma roughDist_left_invariant (k g h : GroupLike₂ V) :
    roughDist (k * g) (k * h) = roughDist g h := by
  simp only [roughDist]
  congr 1; group

/-! ## Hölder-type regularity with respect to homoNorm

When we define rough paths, we need `homoNorm(𝐗(s,t)) ≤ ω(s,t)` for some
control `ω`. The extraction bounds tell us what this means for each level:

* Level 1: `‖X_{s,t}‖ ≤ ω(s,t)` — the path increment is controlled
* Level 2: `‖A_{s,t}‖ ≤ ω(s,t)²` — the area is controlled at double order

For a `γ`-Hölder rough path with `ω(s,t) = C|t-s|^γ`:
* Level 1: `‖X_{s,t}‖ ≤ C|t-s|^γ`
* Level 2: `‖A_{s,t}‖ ≤ C²|t-s|^{2γ}`

These are precisely the regularity conditions in `RoughPath/Defs.lean`. -/

/-- If the homoNorm is bounded by a control, so is the level-1 component. -/
lemma norm_x_le_of_homoNorm_le {g : GroupLike₂ V} {C : ℝ}
    (h : homoNorm g ≤ C) : ‖g.x‖ ≤ C :=
  le_trans (norm_x_le_homoNorm g) h

/-- If the homoNorm is bounded by a control, the area is bounded by its square. -/
lemma norm_area_le_of_homoNorm_le {g : GroupLike₂ V} {C : ℝ}
    (hC : 0 ≤ C) (h : homoNorm g ≤ C) : ‖area g‖ ≤ C ^ 2 := by
  calc ‖area g‖ ≤ homoNorm g ^ 2 := norm_area_le_homoNorm_sq g
    _ ≤ C ^ 2 := by
        apply sq_le_sq'
        · linarith [homoNorm_nonneg g]
        · exact h

/-! ## Norm of the difference element

Used in the rough path metric: `d(𝐗(s,t), 𝐘(s,t)) = ‖𝐗(s,t)⁻¹ · 𝐘(s,t)‖_{cc}`. -/

/-- The level-1 component of the difference is the difference of level-1 components. -/
lemma homoNorm_inv_mul_x (g h : GroupLike₂ V) :
    (g⁻¹ * h).x = h.x - g.x :=
  inv_mul_x g h

/-- Bound on the difference homoNorm in terms of component differences. -/
lemma roughDist_le_of_bounds {g h : GroupLike₂ V}
    {C₁ C₂ : ℝ} (_hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (h₁ : ‖h.x - g.x‖ ≤ C₁)
    (h₂ : ‖area (g⁻¹ * h)‖ ≤ C₂) :
    roughDist g h ≤ max C₁ (C₂ ^ (2⁻¹ : ℝ)) := by
  simp only [roughDist, homoNorm]
  apply max_le_max
  · rw [inv_mul_x]; exact h₁
  · gcongr

end GroupLike₂

end StochCalc
