/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: YoungIntegration/Integral/Properties.lean
-/
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.Integral.Def

noncomputable section

open Real Set Filter Finset

namespace StochCalc

/-! ### Basic properties -/

section BasicProperties

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The Young integral vanishes on the diagonal. -/
theorem youngIntegral_diag
    {X : ℝ → ℝ} {Y : ℝ → E} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ)
    {s : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ s s = 0 :=
  sewingMap₂_diag (youngApprox_sewingCondition₂ hX hY hγδ) has hsb

/-- **The Young–Loève estimate**: the left-point Riemann sum approximation
is accurate to order `|t - s|^{γ+δ}`:

  `‖∫_s^t Y dX - (X(t) - X(s)) • Y(s)‖ ≤ C_{γ,δ} · C_X · C_Y · |t-s|^{γ+δ}`

where `C_{γ,δ} = 1 / (2^{γ+δ} · (1 - 2^{-(γ+δ-1)}))` is the sewing constant.

This is a direct application of `sewingMap₂_dist_le`. -/
theorem youngIntegral_approx
    {X : ℝ → ℝ} {Y : ℝ → E} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ s t -
      (X t - X s) • Y s‖ ≤
    sewingConst₂ δ γ * (C_X * C_Y) * |t - s| ^ (γ + δ) := by
  unfold youngIntegral
  have hcomm : δ + γ = γ + δ := add_comm δ γ
  refine le_trans
    (sewingMap₂_dist_le (youngApprox_sewingCondition₂ hX hY hγδ) has hst htb) ?_
  simp only [one_rpow, mul_one, hcomm]
  -- Goal: C_X * C_Y * sewingConst₂ δ γ * (2⁻¹) ^ (γ + δ) * |t - s| ^ (γ + δ) ≤
  --       sewingConst₂ δ γ * (C_X * C_Y) * |t - s| ^ (γ + δ)
  calc C_X * C_Y * sewingConst₂ δ γ * (2 : ℝ)⁻¹ ^ (γ + δ) * |t - s| ^ (γ + δ)
      ≤ sewingConst₂ δ γ * (C_X * C_Y) * |t - s| ^ (γ + δ) := by
        have h2 : (2 : ℝ)⁻¹ ^ (γ + δ) ≤ 1 :=
          (rpow_lt_one (by positivity) (by norm_num : (2:ℝ)⁻¹ < 1) (by linarith)).le
        have hK : 0 ≤ C_X * C_Y := mul_nonneg hX.C_nonneg hY.C_nonneg
        have hsc : 0 ≤ sewingConst₂ δ γ := (sewingConst₂_pos (by linarith)).le
        have hts : 0 ≤ |t - s| ^ (γ + δ) := rpow_nonneg (abs_nonneg _) _
        nlinarith [mul_le_of_le_one_right (mul_nonneg (mul_nonneg hK hsc) hts) h2]

/-- **Additivity**: `∫_s^t Y dX = ∫_s^u Y dX + ∫_u^t Y dX`. -/
theorem youngIntegral_additive
    {X : ℝ → ℝ} {Y : ℝ → E} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ s t =
      youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ s u +
      youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ u t := by
  -- Direct application of sewingMap₂_additive.
  -- The only work is unfolding the definition and applying the Layer 2 result.
  unfold_projs
  exact sewingMap₂_additive (youngApprox_sewingCondition₂ hX hY hγδ) has hsu hut htb

end BasicProperties

end StochCalc
