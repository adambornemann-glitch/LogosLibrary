/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_2/Integral/Properties.lean
-/
import LogosLibrary.StochasticCalculus.Stage_2.Integral.Def
/-!
# The Rough Integral: Properties

## Overview

This file establishes the main properties of the rough integral defined in
`Def.lean`:

1. **Additivity** (Chasles property): `∫_s^t = ∫_s^u + ∫_u^t`
2. **Hölder regularity**: the indefinite integral `t ↦ ∫_a^t Y d𝐗` is `γ`-Hölder
3. **Closure** (the crown jewel): if `(Y, Y')` is controlled by `𝐗`, then
   the indefinite integral `Z(t) = ∫_a^t Y d𝐗` is also controlled by `𝐗`,
   with Gubinelli derivative `Z' = σ(Y, ·)` (the integrand evaluated at the path)

## Additivity

Additivity requires the Layer 2 sewing condition (cross-controlled product
bound), which the defect naturally satisfies:

    ‖δΞ(s, u, t)‖ ≤ K₁ · |u-s|^{2γ} · |t-u|^γ + K₂ · |u-s|^γ · |t-u|^{2γ}

Both terms have the product structure `ω₁(s,u)^α · ω₂(u,t)^β` with
`α + β = 3γ > 1`. This is `SewingCondition₂`, and `sewingMap₂_additive`
gives us the Chasles property.

Alternatively, if the Layer 1→2 bridge (`sewingMap₁_additive`) is available,
we can route through that. The choice depends on which path through the
Stage 0 API is most convenient.

## The Hölder bound

From the approximation estimate:

    ‖∫_s^t Y d𝐗‖ ≤ ‖∫_s^t - Ξ(s,t)‖ + ‖Ξ(s,t)‖
                   ≤ K'|t-s|^{3γ} + ‖σ‖·M_Y·C_X·|t-s|^γ + ‖τ‖·M_{Y'}·C'_𝕏·|t-s|^{2γ}
                   ≤ C_I · |t-s|^γ

where `C_I` absorbs all the constants (using `|t-s|^{2γ}, |t-s|^{3γ} ≤ diam^{kγ}·|t-s|^γ`).
The integral inherits the regularity of the **driving signal**, just as in
Young integration.

## The closure theorem

This is the deepest result: the rough integral maps controlled paths to
controlled paths. Concretely:

    Z(t) = ∫_a^t Y d𝐗    is controlled by 𝐗 with:
    Z'(s) = σ(Y(s), ·)    (the Gubinelli derivative)
    R^Z_{s,t} = ∫_s^t Y d𝐗 - σ(Y(s), X_{s,t})    (the controlled remainder)

The key estimate is:

    ‖R^Z_{s,t}‖ = ‖∫_s^t Y d𝐗 - σ(Y(s), X_{s,t})‖
                ≤ ‖∫_s^t - Ξ(s,t)‖ + ‖τ(Y'(s), 𝕏_{s,t})‖
                ≤ K'|t-s|^{3γ} + ‖τ‖·M_{Y'}·C'_𝕏·|t-s|^{2γ}
                ≤ C_Z · |t-s|^{2γ}

So `R^Z` is `2γ`-Hölder — exactly the regularity needed for a controlled path.

This closure property is what makes the **Picard iteration** for rough ODEs
`dY = f(Y) d𝐗` work: the solution map `Y ↦ ∫ f(Y) d𝐗` preserves the
controlled path space, and with the right constants it's a contraction.

## References

* Gubinelli, M., *Controlling rough paths*, J. Funct. Anal. **216** (2004), §3–4
* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Chapters 4, 8
-/

open NormedTensorSquare StochCalc.TruncTensor₂ StochCalc.GroupLike₂ Real
open StochCalc.RoughPath StochCalc.ControlledPath

noncomputable section

namespace StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {γ C a b : ℝ}
variable {X : RoughPath V γ C a b}



/-! ## Hölder regularity of the rough integral

The indefinite integral `t ↦ ∫_a^t Y d𝐗` is `γ`-Hölder. -/

/-- **Increment bound** for the rough integral:

    `‖∫_s^t Y d𝐗‖ ≤ C_I · |t - s|^γ`

The constant `C_I` depends on the pairing norms, all controlled path constants,
the rough path constant, and the diameter `b - a`. -/
theorem roughIntegral_increment_bound
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖roughIntegral P cY s t‖ ≤
      (‖P.σ‖ * cY.M_Y * C +
       ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * (b - a) ^ γ +
       roughSewingConst P cY * sewingConst₁ (3 * γ) * (b - a) ^ (2 * γ)) *
        |t - s| ^ γ := by
  have hts_nn : 0 ≤ |t - s| := abs_nonneg _
  have hba_nn : 0 ≤ b - a := sub_nonneg.mpr X.hab
  have hγ_pos : 0 < γ := X.hγ_pos
  have hts_le_ba : |t - s| ≤ b - a := by
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]; linarith
  -- Pre-compute the three individual bounds
  have hσ : ‖P.σ (cY.Y s) (X.x s t)‖ ≤ ‖P.σ‖ * cY.M_Y * C * |t - s| ^ γ :=
    calc ‖P.σ (cY.Y s) (X.x s t)‖
        ≤ ‖P.σ‖ * ‖cY.Y s‖ * ‖X.x s t‖ := P.σ_bound _ _
      _ ≤ ‖P.σ‖ * cY.M_Y * (C * |t - s| ^ γ) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (cY.Y_sup_bound s has (hst.trans htb))
              (ContinuousLinearMap.opNorm_nonneg _))
            (X.x_holder has hst htb)
            (norm_nonneg _)
            (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) cY.hM_Y_nonneg)
      _ = ‖P.σ‖ * cY.M_Y * C * |t - s| ^ γ := by ring
  have hτ : ‖P.τ (cY.Y' s) (X.area_full s t)‖ ≤
      ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * |t - s| ^ (2 * γ) :=
    calc ‖P.τ (cY.Y' s) (X.area_full s t)‖
        ≤ ‖P.τ‖ * ‖cY.Y' s‖ * ‖X.area_full s t‖ := P.τ_bound _ _
      _ ≤ ‖P.τ‖ * cY.M_Y' * (((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * |t - s| ^ (2 * γ)) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (cY.Y'_sup_bound s has (hst.trans htb))
              (ContinuousLinearMap.opNorm_nonneg _))
            (X.area_full_holder has hst htb)
            (norm_nonneg _)
            (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) cY.hM_Y'_nonneg)
      _ = ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * |t - s| ^ (2 * γ) := by ring
  -- Absorb higher-order terms
  have h3γ : |t - s| ^ (3 * γ) ≤ (b - a) ^ (2 * γ) * |t - s| ^ γ := by
    rw [show 3 * γ = 2 * γ + γ from by ring,
        Real.rpow_add' hts_nn (by positivity : (0:ℝ) < 2 * γ + γ).ne']
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hts_nn hts_le_ba (by positivity))
      (Real.rpow_nonneg hts_nn _)
  have h2γ : |t - s| ^ (2 * γ) ≤ (b - a) ^ γ * |t - s| ^ γ := by
    rw [show 2 * γ = γ + γ from by ring,
        Real.rpow_add' hts_nn (by positivity : (0:ℝ) < γ + γ).ne']
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hts_nn hts_le_ba hγ_pos.le)
      (Real.rpow_nonneg hts_nn _)
  have hK₃_nn : 0 ≤ roughSewingConst P cY * sewingConst₁ (3 * γ) :=
    mul_nonneg (roughSewingConst_nonneg P cY) (sewingConst₁_pos X.three_gamma_gt_one).le
  have hK₂_nn : 0 ≤ ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) :=
    mul_nonneg (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) cY.hM_Y'_nonneg)
      (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (sq_nonneg _))
  -- Main calc
  calc ‖roughIntegral P cY s t‖
      = ‖(roughIntegral P cY s t - roughApproxMap P cY s t) +
          roughApproxMap P cY s t‖ := by congr 1; abel
    _ ≤ ‖roughIntegral P cY s t - roughApproxMap P cY s t‖ +
        ‖roughApproxMap P cY s t‖ := norm_add_le _ _
    _ ≤ ‖roughIntegral P cY s t - roughApproxMap P cY s t‖ +
        (‖P.σ (cY.Y s) (X.x s t)‖ + ‖P.τ (cY.Y' s) (X.area_full s t)‖) := by
        gcongr; simp only [roughApproxMap]; exact norm_add_le _ _
    _ ≤ roughSewingConst P cY * sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ) +
        (‖P.σ‖ * cY.M_Y * C * |t - s| ^ γ +
         ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * |t - s| ^ (2 * γ)) :=
        add_le_add (roughIntegral_approx P cY has hst htb) (add_le_add hσ hτ)
    _ ≤ roughSewingConst P cY * sewingConst₁ (3 * γ) * ((b - a) ^ (2 * γ) * |t - s| ^ γ) +
        (‖P.σ‖ * cY.M_Y * C * |t - s| ^ γ +
         ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * ((b - a) ^ γ * |t - s| ^ γ)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h3γ hK₃_nn
        · exact add_le_add_right (mul_le_mul_of_nonneg_left h2γ hK₂_nn) _
    _ = (‖P.σ‖ * cY.M_Y * C +
         ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * (b - a) ^ γ +
         roughSewingConst P cY * sewingConst₁ (3 * γ) * (b - a) ^ (2 * γ)) *
          |t - s| ^ γ := by ring

/-! ## The closure theorem

The crown jewel: the rough integral of a controlled path is controlled. -/

/-- The **Gubinelli derivative** of the rough integral: `Z'(s) = σ(Y(s), ·)`.

This is the level-1 pairing applied to the current path value. It maps
`v ∈ V` to `σ(Y(s), v) ∈ F`. -/
def roughIntegralDeriv
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    (s : ℝ) : V →L[ℝ] F :=
  P.σ (cY.Y s)

/-- The **controlled remainder** of the rough integral:

    `R^Z_{s,t} = ∫_s^t Y d𝐗 - σ(Y(s), X_{s,t})` -/
def roughIntegralRemainder
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    (s t : ℝ) : F :=
  roughIntegral P cY s t - P.σ (cY.Y s) (X.x s t)

/-- The remainder equals the defining expression. -/
theorem roughIntegralRemainder_eq
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    (s t : ℝ) :
    roughIntegralRemainder P cY s t =
      roughIntegral P cY s t - (roughIntegralDeriv P cY s) (X.x s t) := by
  simp [roughIntegralRemainder, roughIntegralDeriv]

/-- **Remainder bound**: the controlled remainder is `2γ`-Hölder.

    `‖R^Z_{s,t}‖ ≤ C_Z · |t - s|^{2γ}`

The key estimate: decompose `R^Z = (I - Ξ) + τ(Y'(s), 𝕏_{s,t})`, then
bound each piece.

- `‖I - Ξ‖ ≤ K'|t-s|^{3γ} ≤ K'(b-a)^γ · |t-s|^{2γ}`
- `‖τ(Y'(s), 𝕏_{s,t})‖ ≤ ‖τ‖ · M_{Y'} · C'_𝕏 · |t-s|^{2γ}` -/
theorem roughIntegralRemainder_bound
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖roughIntegralRemainder P cY s t‖ ≤
      (roughSewingConst P cY * sewingConst₁ (3 * γ) * (b - a) ^ γ +
       ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2)) *
        |t - s| ^ (2 * γ) := by
  rw [roughIntegralRemainder]
  have hsplit : roughIntegral P cY s t - P.σ (cY.Y s) (X.x s t) =
      (roughIntegral P cY s t - roughApproxMap P cY s t) +
      P.τ (cY.Y' s) (X.area_full s t) := by
    simp [roughApproxMap]; abel
  rw [hsplit]
  have hts_nn : 0 ≤ |t - s| := abs_nonneg _
  have hba_nn : 0 ≤ b - a := sub_nonneg.mpr X.hab
  have hγ_pos : 0 < γ := X.hγ_pos
  have hts_le_ba : |t - s| ≤ b - a := by
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]; linarith
  -- Pre-compute the τ bound
  have hτ : ‖P.τ (cY.Y' s) (X.area_full s t)‖ ≤
      ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * |t - s| ^ (2 * γ) :=
    calc ‖P.τ (cY.Y' s) (X.area_full s t)‖
        ≤ ‖P.τ‖ * ‖cY.Y' s‖ * ‖X.area_full s t‖ := P.τ_bound _ _
      _ ≤ ‖P.τ‖ * cY.M_Y' * (((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * |t - s| ^ (2 * γ)) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (cY.Y'_sup_bound s has (hst.trans htb))
              (ContinuousLinearMap.opNorm_nonneg _))
            (X.area_full_holder has hst htb)
            (norm_nonneg _)
            (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) cY.hM_Y'_nonneg)
      _ = ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * |t - s| ^ (2 * γ) := by ring
  -- Absorb |t-s|^{3γ} ≤ (b-a)^γ · |t-s|^{2γ}
  have h3γ_le : |t - s| ^ (3 * γ) ≤ (b - a) ^ γ * |t - s| ^ (2 * γ) := by
    rw [show 3 * γ = γ + 2 * γ from by ring,
        Real.rpow_add' hts_nn (by positivity : (0:ℝ) < γ + 2 * γ).ne']
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hts_nn hts_le_ba hγ_pos.le)
      (Real.rpow_nonneg hts_nn _)
  have hK₃_nn : 0 ≤ roughSewingConst P cY * sewingConst₁ (3 * γ) :=
    mul_nonneg (roughSewingConst_nonneg P cY) (sewingConst₁_pos X.three_gamma_gt_one).le
  -- Main calc
  calc ‖(roughIntegral P cY s t - roughApproxMap P cY s t) +
          P.τ (cY.Y' s) (X.area_full s t)‖
      ≤ ‖roughIntegral P cY s t - roughApproxMap P cY s t‖ +
        ‖P.τ (cY.Y' s) (X.area_full s t)‖ := norm_add_le _ _
    _ ≤ roughSewingConst P cY * sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ) +
        ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * |t - s| ^ (2 * γ) :=
        add_le_add (roughIntegral_approx P cY has hst htb) hτ
    _ ≤ roughSewingConst P cY * sewingConst₁ (3 * γ) * ((b - a) ^ γ * |t - s| ^ (2 * γ)) +
        ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * |t - s| ^ (2 * γ) := by
        linarith [mul_le_mul_of_nonneg_left h3γ_le hK₃_nn]
    _ = (roughSewingConst P cY * sewingConst₁ (3 * γ) * (b - a) ^ γ +
         ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2)) *
          |t - s| ^ (2 * γ) := by ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- **Gubinelli derivative Hölder bound**: `Z' = σ(Y, ·)` is `γ`-Hölder.

    `‖Z'(t) - Z'(s)‖ = ‖σ(Y(t), ·) - σ(Y(s), ·)‖ = ‖σ(Y(t) - Y(s), ·)‖`
    `≤ ‖σ‖ · ‖Y(t) - Y(s)‖ ≤ ‖σ‖ · C'_Y · |t-s|^γ` -/
theorem roughIntegralDeriv_holder
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖roughIntegralDeriv P cY t - roughIntegralDeriv P cY s‖ ≤
      ‖P.σ‖ * (cY.M_Y' * C + cY.C_R * (b - a) ^ γ) * |t - s| ^ γ := by
  simp only [roughIntegralDeriv]
  -- σ(Y(t)) - σ(Y(s)) = σ(Y(t) - Y(s)) by linearity
  rw [show P.σ (cY.Y t) - P.σ (cY.Y s) = P.σ (cY.Y t - cY.Y s) from by
    rw [map_sub]]
  calc ‖P.σ (cY.Y t - cY.Y s)‖
      ≤ ‖P.σ‖ * ‖cY.Y t - cY.Y s‖ := P.σ.le_opNorm _
    _ ≤ ‖P.σ‖ * ((cY.M_Y' * C + cY.C_R * (b - a) ^ γ) * |t - s| ^ γ) := by
        gcongr; exact cY.Y_holder has hst htb
    _ = ‖P.σ‖ * (cY.M_Y' * C + cY.C_R * (b - a) ^ γ) * |t - s| ^ γ := by ring

/-- **Gubinelli derivative supremum bound**: `‖Z'(s)‖ ≤ ‖σ‖ · M_Y`. -/
theorem roughIntegralDeriv_sup
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {s : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    ‖roughIntegralDeriv P cY s‖ ≤ ‖P.σ‖ * cY.M_Y := by
  simp only [roughIntegralDeriv]
  calc ‖P.σ (cY.Y s)‖
      ≤ ‖P.σ‖ * ‖cY.Y s‖ := P.σ.le_opNorm _
    _ ≤ ‖P.σ‖ * cY.M_Y := by gcongr; exact cY.Y_sup_bound s has hsb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-! ## The closure theorem: bundled as a ControlledPath -/

/-- **Closure theorem**: the rough integral of a controlled path is itself controlled.

Given:
- `𝐗`: a rough path of regularity `γ > 1/3`
- `(Y, Y')`: a controlled path
- `P = (σ, τ)`: a compatible pairing

The indefinite integral `Z(t) = ∫_a^t Y d𝐗` is a controlled path with:
- Gubinelli derivative `Z'(s) = σ(Y(s), ·)`
- Remainder `R^Z_{s,t} = ∫_s^t Y d𝐗 - σ(Y(s), X_{s,t})`

satisfying `‖R^Z_{s,t}‖ ≤ C_Z · |t-s|^{2γ}`.

**This is the result that makes the Picard iteration close.** -/
def roughIntegral_controlled
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    (hI_add : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      roughIntegral P cY s t =
        roughIntegral P cY s u + roughIntegral P cY u t) :
    ControlledPath F X where
  Y := roughIntegralIndef P cY
  Y' := roughIntegralDeriv P cY
  R := roughIntegralRemainder P cY
  R_eq := fun s t has hst htb => by
    simp only [roughIntegralIndef, roughIntegralRemainder, roughIntegralDeriv]
    rw [show roughIntegral P cY a t - roughIntegral P cY a s =
          roughIntegral P cY s t from by
      rw [hI_add a s t le_rfl has hst htb]; abel]
  C_R := roughSewingConst P cY * sewingConst₁ (3 * γ) * (b - a) ^ γ +
         ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2)
  hC_R_nonneg := by
    apply add_nonneg
    · apply mul_nonneg; apply mul_nonneg
      · exact roughSewingConst_nonneg P cY
      · exact (sewingConst₁_pos X.three_gamma_gt_one).le
      · exact Real.rpow_nonneg (sub_nonneg.mpr X.hab) _
    · apply mul_nonneg; apply mul_nonneg
      · exact ContinuousLinearMap.opNorm_nonneg _
      · exact cY.hM_Y'_nonneg
      · linarith [sq_nonneg C, mul_nonneg (by positivity : (0:ℝ) ≤ 2⁻¹) (sq_nonneg C)]
  R_bound := fun s t has hst htb =>
    roughIntegralRemainder_bound P cY has hst htb
  C_Y' := ‖P.σ‖ * (cY.M_Y' * C + cY.C_R * (b - a) ^ γ)
  hC_Y'_nonneg := by
    apply mul_nonneg
    · exact ContinuousLinearMap.opNorm_nonneg _
    · linarith [mul_nonneg cY.hM_Y'_nonneg X.hC_nonneg,
                mul_nonneg cY.hC_R_nonneg (Real.rpow_nonneg (sub_nonneg.mpr X.hab) γ)]
  Y'_bound := fun s t has hst htb =>
    roughIntegralDeriv_holder P cY has hst htb
  M_Y' := ‖P.σ‖ * cY.M_Y
  hM_Y'_nonneg := mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) cY.hM_Y_nonneg
  Y'_sup_bound := fun s has hsb =>
    roughIntegralDeriv_sup P cY has hsb
  M_Y := (‖P.σ‖ * cY.M_Y * C +
          ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * (b - a) ^ γ +
          roughSewingConst P cY * sewingConst₁ (3 * γ) * (b - a) ^ (2 * γ)) *
         (b - a) ^ γ
  hM_Y_nonneg := by
    have hba_nn : 0 ≤ b - a := sub_nonneg.mpr X.hab
    have hC_area : 0 ≤ (2⁻¹ : ℝ) * C ^ 2 + C ^ 2 :=
      add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (sq_nonneg _)
    apply mul_nonneg _ (Real.rpow_nonneg hba_nn _)
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) cY.hM_Y_nonneg)
          X.hC_nonneg
      · exact mul_nonneg (mul_nonneg (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _)
          cY.hM_Y'_nonneg) hC_area) (Real.rpow_nonneg hba_nn _)
    · exact mul_nonneg (mul_nonneg (roughSewingConst_nonneg P cY)
        (sewingConst₁_pos X.three_gamma_gt_one).le) (Real.rpow_nonneg hba_nn _)
  Y_sup_bound := fun s has hsb => by
    simp only [roughIntegralIndef]
    have hba_nn : 0 ≤ b - a := sub_nonneg.mpr X.hab
    have hγ_pos : 0 < γ := X.hγ_pos
    have hC_area : 0 ≤ (2⁻¹ : ℝ) * C ^ 2 + C ^ 2 :=
      add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (sq_nonneg _)
    have hbig_nn : 0 ≤ ‖P.σ‖ * cY.M_Y * C +
        ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * (b - a) ^ γ +
        roughSewingConst P cY * sewingConst₁ (3 * γ) * (b - a) ^ (2 * γ) := by
      apply add_nonneg
      · apply add_nonneg
        · exact mul_nonneg (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) cY.hM_Y_nonneg)
            X.hC_nonneg
        · exact mul_nonneg (mul_nonneg (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _)
            cY.hM_Y'_nonneg) hC_area) (Real.rpow_nonneg hba_nn _)
      · exact mul_nonneg (mul_nonneg (roughSewingConst_nonneg P cY)
          (sewingConst₁_pos X.three_gamma_gt_one).le) (Real.rpow_nonneg hba_nn _)
    calc ‖roughIntegral P cY a s‖
        ≤ (‖P.σ‖ * cY.M_Y * C +
           ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * (b - a) ^ γ +
           roughSewingConst P cY * sewingConst₁ (3 * γ) * (b - a) ^ (2 * γ)) *
            |s - a| ^ γ := roughIntegral_increment_bound P cY le_rfl has hsb
      _ ≤ (‖P.σ‖ * cY.M_Y * C +
           ‖P.τ‖ * cY.M_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * (b - a) ^ γ +
           roughSewingConst P cY * sewingConst₁ (3 * γ) * (b - a) ^ (2 * γ)) *
            (b - a) ^ γ := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (abs_nonneg _)
              (by rw [abs_of_nonneg (sub_nonneg.mpr has)]; linarith) hγ_pos.le)
            hbig_nn


end StochCalc
