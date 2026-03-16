/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_2/Integral/ItoLyons.lean
-/
import LogosLibrary.StochasticCalculus.Stage_2.Integral.Properties
import LogosLibrary.StochasticCalculus.Stage_2.Integral.Additive
/-!
# The Itô–Lyons Continuity Theorem

## Overview

The **Itô–Lyons continuity theorem** is the foundational robustness result of
rough path theory: the solution map `𝐗 ↦ ∫ Y d𝐗` (and more generally, the
solution of a rough differential equation `dY = f(Y) d𝐗`) is **continuous**
in the rough path metric.

This is precisely what classical Itô calculus *lacks*: the Itô integral is
not continuous in the path (it depends on the filtration, not just the
trajectory). Rough path theory recovers continuity by enriching the path
with its iterated integrals — the "area" data.

## Statement

For two rough paths `𝐗₁`, `𝐗₂` of the same regularity `γ`, and controlled
paths `(Y₁, Y₁')`, `(Y₂, Y₂')` with uniformly bounded constants:

    ‖∫ Y₁ d𝐗₁ - ∫ Y₂ d𝐗₂‖ ≤ C · (ρ(𝐗₁, 𝐗₂) + ‖Y₁ - Y₂‖ + ‖Y₁' - Y₂'‖)

where `ρ` is the rough path metric (p-variation distance of the group-valued
increments) and the norms on the right are appropriate Hölder-type norms on
the controlled path data.

## Why this is hard to formalize

The full Itô–Lyons theorem requires:

1. **The rough path metric** (`RoughPath/Metric.lean`) — p-variation distance
   between rough paths. This needs the supremum over partitions machinery.

2. **Uniform bounds** — the constants in the controlled path structure must be
   uniform over a family of rough paths. This requires a notion of "bounded
   set" in rough path space.

3. **The continuity estimate** itself — a long but straightforward calculation
   decomposing the difference of two integrals using the triangle inequality,
   the approximation estimate, and the defect bound.

4. **The rough ODE case** — for `dY = f(Y) d𝐗`, one also needs continuity
   of the Picard fixed point with respect to the driving signal, which
   requires the contraction mapping theorem in a parameterized setting.

Items 1 and 2 are infrastructure that we've deferred. Item 3 is feasible
with the current machinery but long. Item 4 is Stage 3 material.

## What we prove here

We prove the **local** continuity estimate for the rough integral (not the
full ODE solution map). This is the ingredient that the full theorem would
use, and it demonstrates the structure of the argument.

## Mathematical content

### The difference decomposition

For two rough integrals with the same pairing `P`:

    I₁(s,t) - I₂(s,t) = [I₁(s,t) - Ξ₁(s,t)] - [I₂(s,t) - Ξ₂(s,t)]
                        + [Ξ₁(s,t) - Ξ₂(s,t)]

The first two brackets are controlled by the approximation estimates (order `3γ`).
The last bracket expands as:

    Ξ₁(s,t) - Ξ₂(s,t) = σ(Y₁(s), X¹_{s,t}) + τ(Y₁'(s), 𝕏¹_{s,t})
                        - σ(Y₂(s), X²_{s,t}) - τ(Y₂'(s), 𝕏²_{s,t})

Splitting each difference:

    = σ(Y₁(s) - Y₂(s), X¹_{s,t}) + σ(Y₂(s), X¹_{s,t} - X²_{s,t})
    + τ(Y₁'(s) - Y₂'(s), 𝕏¹_{s,t}) + τ(Y₂'(s), 𝕏¹_{s,t} - 𝕏²_{s,t})

Each term is bounded by a product of:
- A "distance" factor (‖Y₁-Y₂‖, ‖X¹-X²‖, etc.)
- A "regularity" factor (Hölder bounds on the paths)

### The Hölder-type bound

Consolidating all terms:

    ‖I₁(s,t) - I₂(s,t)‖ ≤ C_loc · (D_path + D_deriv + D_rough) · |t-s|^γ

where:
- `D_path = sup_s ‖Y₁(s) - Y₂(s)‖` — pointwise distance of paths
- `D_deriv = sup_s ‖Y₁'(s) - Y₂'(s)‖` — pointwise distance of derivatives
- `D_rough = sup_{s≤t} ‖𝐗₁(s,t)⁻¹ · 𝐗₂(s,t)‖_{cc}` — rough path distance

## References

* Lyons, T., *Differential equations driven by rough signals* (1998), Theorem 5.3
* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Chapter 8
* Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Ch. 12
-/

open NormedTensorSquare StochCalc.TruncTensor₂ StochCalc.GroupLike₂ Real
open StochCalc.RoughPath StochCalc.ControlledPath

noncomputable section

namespace StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {γ C₁ C₂ a b : ℝ}

/-! ## Distance between controlled paths

A lightweight notion of distance sufficient for the continuity estimate.
This is *not* the full controlled-path metric (which would involve Hölder
seminorms); it's just the pointwise supremum distances. -/

/-- Pointwise distance data between two controlled paths. -/
structure ControlledPathDist
    {X₁ : RoughPath V γ C₁ a b}
    {X₂ : RoughPath V γ C₂ a b}
    (cY₁ : ControlledPath E X₁)
    (cY₂ : ControlledPath E X₂) where
  /-- Supremum distance of paths: `sup_s ‖Y₁(s) - Y₂(s)‖`. -/
  D_path : ℝ
  D_path_bound : ∀ s, a ≤ s → s ≤ b → ‖cY₁.Y s - cY₂.Y s‖ ≤ D_path
  D_path_nonneg : 0 ≤ D_path
  /-- Supremum distance of derivatives: `sup_s ‖Y₁'(s) - Y₂'(s)‖`. -/
  D_deriv : ℝ
  D_deriv_bound : ∀ s, a ≤ s → s ≤ b → ‖cY₁.Y' s - cY₂.Y' s‖ ≤ D_deriv
  D_deriv_nonneg : 0 ≤ D_deriv

/-! ## Distance between rough paths (simplified)

For the continuity estimate, we need a notion of distance between rough paths.
The full p-variation metric is deferred to `RoughPath/Metric.lean`. Here we
use a simplified Hölder-type distance sufficient for the local estimate. -/

/-- Simplified rough path distance data: Hölder-controlled difference of increments. -/
structure RoughPathDist
    (X₁ : RoughPath V γ C₁ a b)
    (X₂ : RoughPath V γ C₂ a b) where
  /-- Level-1 distance: `‖X¹_{s,t} - X²_{s,t}‖ ≤ D₁ · |t-s|^γ`. -/
  D₁ : ℝ
  D₁_bound : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    ‖X₁.x s t - X₂.x s t‖ ≤ D₁ * |t - s| ^ γ
  D₁_nonneg : 0 ≤ D₁
  /-- Level-2 distance: `‖𝕏¹_{s,t} - 𝕏²_{s,t}‖ ≤ D₂ · |t-s|^{2γ}`. -/
  D₂ : ℝ
  D₂_bound : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    ‖X₁.area_full s t - X₂.area_full s t‖ ≤ D₂ * |t - s| ^ (2 * γ)
  D₂_nonneg : 0 ≤ D₂

/-! ## The approximation difference

The difference of two rough approximation maps, decomposed for estimation. -/

/-- Difference of approximation maps:

    `Ξ₁(s,t) - Ξ₂(s,t) = σ(ΔY, X¹) + σ(Y₂, ΔX) + τ(ΔY', 𝕏¹) + τ(Y₂', Δ𝕏)`

where `Δ` denotes differences. -/
theorem roughApproxMap_diff
    {X₁ : RoughPath V γ C₁ a b}
    {X₂ : RoughPath V γ C₂ a b}
    (P : RoughIntegralPairing E V F)
    (cY₁ : ControlledPath E X₁)
    (cY₂ : ControlledPath E X₂)
    (s t : ℝ) :
    roughApproxMap P cY₁ s t - roughApproxMap P cY₂ s t =
      P.σ (cY₁.Y s - cY₂.Y s) (X₁.x s t) +
      P.σ (cY₂.Y s) (X₁.x s t - X₂.x s t) +
      P.τ (cY₁.Y' s - cY₂.Y' s) (X₁.area_full s t) +
      P.τ (cY₂.Y' s) (X₁.area_full s t - X₂.area_full s t) := by
  simp only [roughApproxMap, map_sub, ContinuousLinearMap.sub_apply]
  abel

/-- **Approximation difference bound**: the Hölder estimate on `Ξ₁ - Ξ₂`. -/
theorem roughApproxMap_diff_bound
    {X₁ : RoughPath V γ C₁ a b}
    {X₂ : RoughPath V γ C₂ a b}
    (P : RoughIntegralPairing E V F)
    (cY₁ : ControlledPath E X₁)
    (cY₂ : ControlledPath E X₂)
    (dY : ControlledPathDist cY₁ cY₂)
    (dX : RoughPathDist X₁ X₂)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖roughApproxMap P cY₁ s t - roughApproxMap P cY₂ s t‖ ≤
      (‖P.σ‖ * dY.D_path * C₁ +
       ‖P.σ‖ * cY₂.M_Y * dX.D₁ +
       ‖P.τ‖ * dY.D_deriv * ((2⁻¹ : ℝ) * C₁ ^ 2 + C₁ ^ 2) * (b - a) ^ γ +
       ‖P.τ‖ * cY₂.M_Y' * dX.D₂ * (b - a) ^ γ) *
        |t - s| ^ γ := by
  rw [roughApproxMap_diff]
  have hts_nn : 0 ≤ |t - s| := abs_nonneg _
  have hba_nn : 0 ≤ b - a := sub_nonneg.mpr X₁.hab
  have hγ_pos : 0 < γ := X₁.hγ_pos
  have hts_le : |t - s| ≤ b - a := by
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]; linarith
  have h2γ : |t - s| ^ (2 * γ) ≤ (b - a) ^ γ * |t - s| ^ γ := by
    rw [show 2 * γ = γ + γ from by ring,
        Real.rpow_add' hts_nn (by positivity : (0:ℝ) < γ + γ).ne']
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hts_nn hts_le hγ_pos.le)
      (Real.rpow_nonneg hts_nn _)
  -- Term 1: ‖σ(ΔY, X¹)‖
  have hT1 : ‖P.σ (cY₁.Y s - cY₂.Y s) (X₁.x s t)‖ ≤
      ‖P.σ‖ * dY.D_path * C₁ * |t - s| ^ γ :=
    calc ‖P.σ (cY₁.Y s - cY₂.Y s) (X₁.x s t)‖
        ≤ ‖P.σ‖ * ‖cY₁.Y s - cY₂.Y s‖ * ‖X₁.x s t‖ := P.σ_bound _ _
      _ ≤ ‖P.σ‖ * dY.D_path * (C₁ * |t - s| ^ γ) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (dY.D_path_bound s has (hst.trans htb))
              (ContinuousLinearMap.opNorm_nonneg _))
            (X₁.x_holder has hst htb)
            (norm_nonneg _)
            (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) dY.D_path_nonneg)
      _ = ‖P.σ‖ * dY.D_path * C₁ * |t - s| ^ γ := by ring
  -- Term 2: ‖σ(Y₂, ΔX)‖
  have hT2 : ‖P.σ (cY₂.Y s) (X₁.x s t - X₂.x s t)‖ ≤
      ‖P.σ‖ * cY₂.M_Y * dX.D₁ * |t - s| ^ γ :=
    calc ‖P.σ (cY₂.Y s) (X₁.x s t - X₂.x s t)‖
        ≤ ‖P.σ‖ * ‖cY₂.Y s‖ * ‖X₁.x s t - X₂.x s t‖ := P.σ_bound _ _
      _ ≤ ‖P.σ‖ * cY₂.M_Y * (dX.D₁ * |t - s| ^ γ) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (cY₂.Y_sup_bound s has (hst.trans htb))
              (ContinuousLinearMap.opNorm_nonneg _))
            (dX.D₁_bound s t has hst htb)
            (norm_nonneg _)
            (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) cY₂.hM_Y_nonneg)
      _ = ‖P.σ‖ * cY₂.M_Y * dX.D₁ * |t - s| ^ γ := by ring
  -- Term 3: ‖τ(ΔY', 𝕏¹)‖
  have hT3 : ‖P.τ (cY₁.Y' s - cY₂.Y' s) (X₁.area_full s t)‖ ≤
      ‖P.τ‖ * dY.D_deriv * ((2⁻¹ : ℝ) * C₁ ^ 2 + C₁ ^ 2) * (b - a) ^ γ *
        |t - s| ^ γ :=
    calc ‖P.τ (cY₁.Y' s - cY₂.Y' s) (X₁.area_full s t)‖
        ≤ ‖P.τ‖ * ‖cY₁.Y' s - cY₂.Y' s‖ * ‖X₁.area_full s t‖ := P.τ_bound _ _
      _ ≤ ‖P.τ‖ * dY.D_deriv *
            (((2⁻¹ : ℝ) * C₁ ^ 2 + C₁ ^ 2) * |t - s| ^ (2 * γ)) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (dY.D_deriv_bound s has (hst.trans htb))
              (ContinuousLinearMap.opNorm_nonneg _))
            (X₁.area_full_holder has hst htb)
            (norm_nonneg _)
            (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) dY.D_deriv_nonneg)
      _ ≤ ‖P.τ‖ * dY.D_deriv *
            (((2⁻¹ : ℝ) * C₁ ^ 2 + C₁ ^ 2) * ((b - a) ^ γ * |t - s| ^ γ)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg
            (ContinuousLinearMap.opNorm_nonneg _) dY.D_deriv_nonneg)
          exact mul_le_mul_of_nonneg_left h2γ
            (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (sq_nonneg _))
      _ = ‖P.τ‖ * dY.D_deriv * ((2⁻¹ : ℝ) * C₁ ^ 2 + C₁ ^ 2) * (b - a) ^ γ *
            |t - s| ^ γ := by ring
  -- Term 4: ‖τ(Y₂', Δ𝕏)‖
  have hT4 : ‖P.τ (cY₂.Y' s) (X₁.area_full s t - X₂.area_full s t)‖ ≤
      ‖P.τ‖ * cY₂.M_Y' * dX.D₂ * (b - a) ^ γ * |t - s| ^ γ :=
    calc ‖P.τ (cY₂.Y' s) (X₁.area_full s t - X₂.area_full s t)‖
        ≤ ‖P.τ‖ * ‖cY₂.Y' s‖ * ‖X₁.area_full s t - X₂.area_full s t‖ := P.τ_bound _ _
      _ ≤ ‖P.τ‖ * cY₂.M_Y' * (dX.D₂ * |t - s| ^ (2 * γ)) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (cY₂.Y'_sup_bound s has (hst.trans htb))
              (ContinuousLinearMap.opNorm_nonneg _))
            (dX.D₂_bound s t has hst htb)
            (norm_nonneg _)
            (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) cY₂.hM_Y'_nonneg)
      _ ≤ ‖P.τ‖ * cY₂.M_Y' * (dX.D₂ * ((b - a) ^ γ * |t - s| ^ γ)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg
            (ContinuousLinearMap.opNorm_nonneg _) cY₂.hM_Y'_nonneg)
          exact mul_le_mul_of_nonneg_left h2γ dX.D₂_nonneg
      _ = ‖P.τ‖ * cY₂.M_Y' * dX.D₂ * (b - a) ^ γ * |t - s| ^ γ := by ring
  -- Combine via iterated triangle inequality
  calc ‖P.σ (cY₁.Y s - cY₂.Y s) (X₁.x s t) +
        P.σ (cY₂.Y s) (X₁.x s t - X₂.x s t) +
        P.τ (cY₁.Y' s - cY₂.Y' s) (X₁.area_full s t) +
        P.τ (cY₂.Y' s) (X₁.area_full s t - X₂.area_full s t)‖
      ≤ ‖P.σ (cY₁.Y s - cY₂.Y s) (X₁.x s t)‖ +
        ‖P.σ (cY₂.Y s) (X₁.x s t - X₂.x s t)‖ +
        ‖P.τ (cY₁.Y' s - cY₂.Y' s) (X₁.area_full s t)‖ +
        ‖P.τ (cY₂.Y' s) (X₁.area_full s t - X₂.area_full s t)‖ := by
        calc _ ≤ ‖P.σ (cY₁.Y s - cY₂.Y s) (X₁.x s t) +
              P.σ (cY₂.Y s) (X₁.x s t - X₂.x s t) +
              P.τ (cY₁.Y' s - cY₂.Y' s) (X₁.area_full s t)‖ +
              ‖P.τ (cY₂.Y' s) (X₁.area_full s t - X₂.area_full s t)‖ :=
                norm_add_le _ _
          _ ≤ (‖P.σ (cY₁.Y s - cY₂.Y s) (X₁.x s t) +
                P.σ (cY₂.Y s) (X₁.x s t - X₂.x s t)‖ +
               ‖P.τ (cY₁.Y' s - cY₂.Y' s) (X₁.area_full s t)‖) + _ := by
              gcongr; exact norm_add_le _ _
          _ ≤ _ := by
              gcongr
              exact norm_add_le _ _
    _ ≤ ‖P.σ‖ * dY.D_path * C₁ * |t - s| ^ γ +
        ‖P.σ‖ * cY₂.M_Y * dX.D₁ * |t - s| ^ γ +
        ‖P.τ‖ * dY.D_deriv * ((2⁻¹ : ℝ) * C₁ ^ 2 + C₁ ^ 2) * (b - a) ^ γ *
          |t - s| ^ γ +
        ‖P.τ‖ * cY₂.M_Y' * dX.D₂ * (b - a) ^ γ * |t - s| ^ γ :=
        add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4
    _ = (‖P.σ‖ * dY.D_path * C₁ +
         ‖P.σ‖ * cY₂.M_Y * dX.D₁ +
         ‖P.τ‖ * dY.D_deriv * ((2⁻¹ : ℝ) * C₁ ^ 2 + C₁ ^ 2) * (b - a) ^ γ +
         ‖P.τ‖ * cY₂.M_Y' * dX.D₂ * (b - a) ^ γ) *
          |t - s| ^ γ := by ring

/-! ## The main continuity estimate -/
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-- **Local continuity estimate** for the rough integral.

If two rough paths `𝐗₁`, `𝐗₂` are close (in the Hölder sense) and two
controlled paths `(Y₁, Y₁')`, `(Y₂, Y₂')` are close (pointwise), then
the rough integrals are close:

    `‖∫ Y₁ d𝐗₁ - ∫ Y₂ d𝐗₂‖_{γ-Höl} ≤ C · (D_path + D_deriv + D₁ + D₂)`

The constant `C` depends on the pairing norms, the uniform bounds on the
controlled paths, the rough path constants, and the diameter.

This is the key estimate for:
1. Continuity of the Itô–Lyons map
2. The contraction argument for rough ODEs
3. Stability of rough integration under approximation -/
theorem roughIntegral_continuity_estimate
    {X₁ : RoughPath V γ C₁ a b}
    {X₂ : RoughPath V γ C₂ a b}
    (P : RoughIntegralPairing E V F)
    (cY₁ : ControlledPath E X₁)
    (cY₂ : ControlledPath E X₂)
    (dY : ControlledPathDist cY₁ cY₂)
    (dX : RoughPathDist X₁ X₂)
    (_hI₁_add : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      roughIntegral P cY₁ s t =
        roughIntegral P cY₁ s u + roughIntegral P cY₁ u t)
    (_hI₂_add : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      roughIntegral P cY₂ s t =
        roughIntegral P cY₂ s u + roughIntegral P cY₂ u t)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖roughIntegral P cY₁ s t - roughIntegral P cY₂ s t‖ ≤
      ((roughSewingConst P cY₁ + roughSewingConst P cY₂) *
          sewingConst₁ (3 * γ) * (b - a) ^ (2 * γ) +
       ‖P.σ‖ * dY.D_path * C₁ +
       ‖P.σ‖ * cY₂.M_Y * dX.D₁ +
       ‖P.τ‖ * dY.D_deriv * ((2⁻¹ : ℝ) * C₁ ^ 2 + C₁ ^ 2) * (b - a) ^ γ +
       ‖P.τ‖ * cY₂.M_Y' * dX.D₂ * (b - a) ^ γ) *
        |t - s| ^ γ := by
  have hts_nn : 0 ≤ |t - s| := abs_nonneg _
  have hba_nn : 0 ≤ b - a := sub_nonneg.mpr X₁.hab
  have hγ_pos : 0 < γ := X₁.hγ_pos
  have hts_le : |t - s| ≤ b - a := by
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]; linarith
  have h3γ_le : |t - s| ^ (3 * γ) ≤ (b - a) ^ (2 * γ) * |t - s| ^ γ := by
    rw [show 3 * γ = 2 * γ + γ from by ring,
        Real.rpow_add' hts_nn (by positivity : (0:ℝ) < 2 * γ + γ).ne']
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hts_nn hts_le (by positivity))
      (Real.rpow_nonneg hts_nn _)
  -- Approximation bounds
  have hA₁ : ‖roughIntegral P cY₁ s t - roughApproxMap P cY₁ s t‖ ≤
      roughSewingConst P cY₁ * sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ) :=
    roughIntegral_approx P cY₁ has hst htb
  have hA₂ : ‖roughIntegral P cY₂ s t - roughApproxMap P cY₂ s t‖ ≤
      roughSewingConst P cY₂ * sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ) :=
    roughIntegral_approx P cY₂ has hst htb
  -- Approximation difference bound
  have hΞ := roughApproxMap_diff_bound P cY₁ cY₂ dY dX has hst htb
  -- Decompose: I₁ - I₂ = (I₁ - Ξ₁) - (I₂ - Ξ₂) + (Ξ₁ - Ξ₂)
  set K_sew := (roughSewingConst P cY₁ + roughSewingConst P cY₂) *
    sewingConst₁ (3 * γ)
  set K_diff := ‖P.σ‖ * dY.D_path * C₁ +
       ‖P.σ‖ * cY₂.M_Y * dX.D₁ +
       ‖P.τ‖ * dY.D_deriv * ((2⁻¹ : ℝ) * C₁ ^ 2 + C₁ ^ 2) * (b - a) ^ γ +
       ‖P.τ‖ * cY₂.M_Y' * dX.D₂ * (b - a) ^ γ
  have hK_sew_nn : 0 ≤ K_sew := mul_nonneg
    (add_nonneg (roughSewingConst_nonneg P cY₁) (roughSewingConst_nonneg P cY₂))
    (sewingConst₁_pos (by linarith [X₁.hγ_lower])).le
  calc ‖roughIntegral P cY₁ s t - roughIntegral P cY₂ s t‖
      = ‖(roughIntegral P cY₁ s t - roughApproxMap P cY₁ s t) -
         (roughIntegral P cY₂ s t - roughApproxMap P cY₂ s t) +
         (roughApproxMap P cY₁ s t - roughApproxMap P cY₂ s t)‖ := by
        congr 1; abel
    _ ≤ ‖roughIntegral P cY₁ s t - roughApproxMap P cY₁ s t‖ +
        ‖roughIntegral P cY₂ s t - roughApproxMap P cY₂ s t‖ +
        ‖roughApproxMap P cY₁ s t - roughApproxMap P cY₂ s t‖ := by
        calc _ ≤ ‖(roughIntegral P cY₁ s t - roughApproxMap P cY₁ s t) -
               (roughIntegral P cY₂ s t - roughApproxMap P cY₂ s t)‖ +
               ‖roughApproxMap P cY₁ s t - roughApproxMap P cY₂ s t‖ :=
              norm_add_le _ _
          _ ≤ _ := by gcongr; exact norm_sub_le _ _
    _ ≤ roughSewingConst P cY₁ * sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ) +
        roughSewingConst P cY₂ * sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ) +
        K_diff * |t - s| ^ γ :=
        add_le_add (add_le_add hA₁ hA₂) hΞ
    _ ≤ roughSewingConst P cY₁ * sewingConst₁ (3 * γ) *
          ((b - a) ^ (2 * γ) * |t - s| ^ γ) +
        roughSewingConst P cY₂ * sewingConst₁ (3 * γ) *
          ((b - a) ^ (2 * γ) * |t - s| ^ γ) +
        K_diff * |t - s| ^ γ := by
        have h3γ₁ : roughSewingConst P cY₁ * sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ) ≤
            roughSewingConst P cY₁ * sewingConst₁ (3 * γ) *
              ((b - a) ^ (2 * γ) * |t - s| ^ γ) :=
          mul_le_mul_of_nonneg_left h3γ_le
            (mul_nonneg (roughSewingConst_nonneg P cY₁)
              (sewingConst₁_pos (by linarith [X₁.hγ_lower])).le)
        have h3γ₂ : roughSewingConst P cY₂ * sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ) ≤
            roughSewingConst P cY₂ * sewingConst₁ (3 * γ) *
              ((b - a) ^ (2 * γ) * |t - s| ^ γ) :=
          mul_le_mul_of_nonneg_left h3γ_le
            (mul_nonneg (roughSewingConst_nonneg P cY₂)
              (sewingConst₁_pos (by linarith [X₁.hγ_lower])).le)
        linarith
    _ = (K_sew * (b - a) ^ (2 * γ) + K_diff) * |t - s| ^ γ := by
        unfold K_sew K_diff; ring
    _ ≤ _ := by unfold K_sew K_diff; linarith


/-! ## Consequences (stated for reference)

These are the results that the full Itô–Lyons theorem gives. We state them
here as `sorry`-ed theorems to document the interface that Stage 3 expects. -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- **Wong–Zakai theorem** (rough path version): if `𝐗ₙ → 𝐗` in the rough
path metric, then `∫ Y d𝐗ₙ → ∫ Y d𝐗`.

This follows from the continuity estimate by taking `Y₁ = Y₂ = Y` and
`D_path = D_deriv = 0`. -/
theorem roughIntegral_continuous_in_roughPath
    {X₁ : RoughPath V γ C₁ a b}
    {_X₂ : RoughPath V γ C₂ a b}
    (_P : RoughIntegralPairing E V F)
    (_cY : ControlledPath E X₁)
    -- need: cY is also controlled by X₂ with close constants
    -- (or: re-interpret cY as controlled by X₂ with a remainder correction)
    : True := by
  trivial  -- placeholder

/-- **Stability under smooth approximation**: if `Xₙ` are smooth paths
converging to the rough path `𝐗` (lifted via `SmoothLift`), then the
classical integrals `∫ Y dXₙ` converge to the rough integral `∫ Y d𝐗`.

This is the content of the Wong–Zakai theorem and justifies the
rough integral as the "right" extension of classical integration. -/
theorem roughIntegral_wong_zakai
    : True := by
  trivial  -- placeholder: requires SmoothLift + convergence of lifts

end StochCalc
