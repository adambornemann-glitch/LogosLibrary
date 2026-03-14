/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: YoungIntegration/Integral/Regular.lean
-/
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.Integral.Properties

noncomputable section

open Real Set Filter Finset

namespace StochCalc

/-! ### Regularity: the indefinite integral has finite p-variation -/

section Regularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Increment bound**: the Young integral has Hölder-like increments.

  `‖∫_s^t Y dX‖ ≤ (‖Y‖_∞ · C_X + C_{γ,δ} · C_X · C_Y · diam^δ) · |t-s|^γ`

This follows from the triangle inequality:
  `‖I(s,t)‖ ≤ ‖I(s,t) - Ξ(s,t)‖ + ‖Ξ(s,t)‖`
  `≤ C_{γ,δ} · C_X · C_Y · |t-s|^{γ+δ} + |X(t) - X(s)| · ‖Y(s)‖`
  `≤ C_{γ,δ} · C_X · C_Y · |t-s|^{γ+δ} + C_X · |t-s|^γ · ‖Y‖_∞`
  `≤ (C_X · ‖Y‖_∞ + C_{γ,δ} · C_X · C_Y · diam^δ) · |t-s|^γ`

This means the indefinite integral `t ↦ ∫_a^t Y dX` is `γ`-Hölder, and hence
has finite `1/γ`-variation = `p`-variation. The integral inherits the regularity
of the integrator `X`, not the integrand `Y`. -/
theorem youngIntegral_increment_bound
    {X : ℝ → ℝ} {Y : ℝ → E} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ)
    {Y_sup : ℝ} (hY_sup : ∀ s, a ≤ s → s ≤ b → ‖Y s‖ ≤ Y_sup)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ s t‖ ≤
      (C_X * Y_sup + sewingConst₂ δ γ * C_X * C_Y * (b - a) ^ δ) *
        |t - s| ^ γ := by
  set I := youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ
  have hts_nn : 0 ≤ |t - s| := abs_nonneg _
  have hts_le : |t - s| ≤ b - a := by
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]; linarith
  calc ‖I s t‖
      = ‖(I s t - (X t - X s) • Y s) + (X t - X s) • Y s‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖I s t - (X t - X s) • Y s‖ + ‖(X t - X s) • Y s‖ :=
        norm_add_le _ _
    _ ≤ sewingConst₂ δ γ * (C_X * C_Y) * |t - s| ^ (γ + δ) +
        C_X * |t - s| ^ γ * Y_sup := by
        apply add_le_add
        · exact youngIntegral_approx hX hY hγδ has hst htb
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul
            (hX.holder_bound s t has hst htb)
            (hY_sup s has (hst.trans htb))
            (norm_nonneg _)
            (mul_nonneg hX.C_nonneg (rpow_nonneg hts_nn _))
    _ ≤ (C_X * Y_sup + sewingConst₂ δ γ * C_X * C_Y * (b - a) ^ δ) *
          |t - s| ^ γ := by
        rw [add_mul, add_comm (C_X * Y_sup * |t - s| ^ γ)]
        apply add_le_add
        · -- Split |t-s|^{γ+δ} = |t-s|^δ · |t-s|^γ, bound |t-s|^δ ≤ (b-a)^δ
          rw [show γ + δ = δ + γ from add_comm γ δ,
              rpow_add' hts_nn (show δ + γ ≠ 0 from by linarith)]
          have hδ_le : |t - s| ^ δ ≤ (b - a) ^ δ :=
            rpow_le_rpow hts_nn hts_le hY.γ_pos.le
          have hsc_nn : 0 ≤ sewingConst₂ δ γ :=
            (sewingConst₂_pos (by linarith)).le
          have hCK_nn : 0 ≤ C_X * C_Y := mul_nonneg hX.C_nonneg hY.C_nonneg
          have hγ_nn : 0 ≤ |t - s| ^ γ := rpow_nonneg hts_nn _
          nlinarith [mul_le_mul_of_nonneg_left hδ_le
            (mul_nonneg (mul_nonneg hsc_nn hCK_nn) hγ_nn)]
        · exact le_of_eq (by ring)

/-- **p-variation bound**: the indefinite integral `t ↦ ∫_a^t Y dX`
has finite `p`-variation with `p = 1/γ`.

  `‖∫ Y dX‖_{p-var; [a,b]} ≤ C · (‖Y‖_∞ · ‖X‖_{p-var} + ‖Y‖_{q-var} · ‖X‖_{p-var})`

This is *essential* for later stages: it shows the Young integral preserves
the regularity class, which is what allows Picard iteration for Young ODEs. -/
theorem youngIntegral_pvar_bound
    {X : ℝ → ℝ} {Y : ℝ → E} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ)
    {Y_sup : ℝ} (hY_sup : ∀ s, a ≤ s → s ≤ b → ‖Y s‖ ≤ Y_sup) :
    IsHolderOn (fun t => youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ a t)
      γ (C_X * Y_sup + sewingConst₂ δ γ * C_X * C_Y * (b - a) ^ δ) a b where
  γ_pos := hX.γ_pos
  γ_le_one := hX.γ_le_one
  C_nonneg := by
    apply add_nonneg
    · exact mul_nonneg hX.C_nonneg
        (le_trans (norm_nonneg (Y a)) (hY_sup a le_rfl hX.hab))
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (sewingConst₂_pos (by linarith)).le hX.C_nonneg) hY.C_nonneg)
        (rpow_nonneg (sub_nonneg.mpr hX.hab) _)
  hab := hX.hab
  holder_bound := by
    intro s t has hst htb
    -- I(a, t) - I(a, s) = I(a, s) + I(s, t) - I(a, s) = I(s, t)
    have hadd := youngIntegral_additive hX hY hγδ
      (le_refl a) has hst htb
    rw [show youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ a t -
        youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ a s =
        youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ s t from by
      rw [hadd]; abel]
    exact youngIntegral_increment_bound hX hY hγδ hY_sup has hst htb

end Regularity

end StochCalc
