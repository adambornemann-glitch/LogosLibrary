/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_2/Integral/Def.lean
-/
import LogosLibrary.StochasticCalculus.Stage_2.Integral.Defect
/-!
# The Rough Integral: Definition

## Overview

This is a thin wrapper: the rough integral is defined as the output of
`sewingMap₁` applied to the rough integral approximation map `Ξ(s,t)`.
All the analytical work was done in `Defect.lean`; this file just names
the result and provides the basic API.

## Definition

Given:
- A rough path `𝐗` of regularity `γ > 1/3`
- A controlled path `(Y, Y')` with remainder `R^Y`
- A pairing `P = (σ, τ)` satisfying the compatibility condition

The **rough integral** is:

    ∫_s^t Y d𝐗 := sewingMap₁(Ξ)(s, t)

where `Ξ(s,t) = σ(Y(s), X_{s,t}) + τ(Y'(s), 𝕏_{s,t})` is the rough
approximation from `Defect.lean`.

## What this file provides

- `roughIntegral` — the definition
- `roughIntegral_diag` — vanishes on the diagonal
- `roughIntegral_approx` — the 3γ-order approximation estimate
- `roughIntegral_unique` — uniqueness among additive functionals

Additivity, Hölder regularity, and closure (the output is controlled)
are deferred to `Properties.lean`.

## References

* Gubinelli, M., *Controlling rough paths*, J. Funct. Anal. **216** (2004)
* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Chapter 4
-/

open NormedTensorSquare StochCalc.TruncTensor₂ StochCalc.GroupLike₂ Real
open StochCalc.RoughPath StochCalc.ControlledPath

noncomputable section

namespace StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {γ C a b : ℝ}
variable {X : RoughPath V γ C a b}

/-! ## The sewing constant for the rough integral -/

/-- The **defect constant** `K` appearing in the sewing condition.
This depends on the pairing norms, the controlled path constants, and
the rough path Hölder constant. -/
def roughSewingConst
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X) : ℝ :=
  ‖P.σ‖ * cY.C_R * C + ‖P.τ‖ * cY.C_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2)

theorem roughSewingConst_nonneg
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X) :
    0 ≤ roughSewingConst P cY := by
  unfold roughSewingConst
  apply add_nonneg
  · exact mul_nonneg (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _)
      cY.hC_R_nonneg) X.hC_nonneg
  · apply mul_nonneg
    · exact mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) cY.hC_Y'_nonneg
    · linarith [sq_nonneg C, mul_nonneg (by positivity : (0:ℝ) ≤ 2⁻¹) (sq_nonneg C)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-! ## Definition of the rough integral -/

/-- The **rough integral** of a controlled path `(Y, Y')` against a rough path `𝐗`,
with respect to a pairing `P = (σ, τ)`.

    `∫_s^t Y d𝐗 := sewingMap₁(Ξ)(s, t)`

where `Ξ(s,t) = σ(Y(s), X_{s,t}) + τ(Y'(s), 𝕏_{s,t})`.

This is the unique additive functional that approximates `Ξ` to order `3γ`. -/
def roughIntegral
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    (s t : ℝ) : F :=
  sewingMap₁ (roughApproxMap P cY) (3 * γ) (roughSewingConst P cY) a b
    (roughApprox_sewingCondition₁ P cY) s t

/-! ## Basic properties -/

/-- The rough integral vanishes on the diagonal: `∫_s^s Y d𝐗 = 0`. -/
theorem roughIntegral_diag
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {s : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    roughIntegral P cY s s = 0 :=
  sewingMap₁_diag (roughApprox_sewingCondition₁ P cY) has hsb

/-- **The rough approximation estimate**: the integral is close to the
approximation map at order `3γ`.

    `‖∫_s^t Y d𝐗 - σ(Y(s), X_{s,t}) - τ(Y'(s), 𝕏_{s,t})‖ ≤ K' · |t-s|^{3γ}`

This is the rough analogue of the Young–Loève estimate. -/
theorem roughIntegral_approx
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖roughIntegral P cY s t - roughApproxMap P cY s t‖ ≤
      roughSewingConst P cY * sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ) :=
  sewingMap₁_dist_le (roughApprox_sewingCondition₁ P cY) has hst htb

/-- The approximation estimate, expanded: the integral is close to
`σ(Y(s), X_{s,t}) + τ(Y'(s), 𝕏_{s,t})`. -/
theorem roughIntegral_approx'
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖roughIntegral P cY s t -
      P.σ (cY.Y s) (X.x s t) - P.τ (cY.Y' s) (X.area_full s t)‖ ≤
      roughSewingConst P cY * sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ) := by
  have h : roughIntegral P cY s t - roughApproxMap P cY s t =
      roughIntegral P cY s t -
        P.σ (cY.Y s) (X.x s t) - P.τ (cY.Y' s) (X.area_full s t) := by
    simp [roughApproxMap]; abel
  rw [← h]
  exact roughIntegral_approx P cY has hst htb

/-- **Uniqueness**: any additive functional with a super-linear approximation
bound must equal the rough integral.

This is the same uniqueness principle as in Young integration (Stage 1),
one level up: characterise the integral by its approximation behaviour. -/
theorem roughIntegral_unique
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {J : ℝ → ℝ → F} {C' : ℝ}
    (hJ_add : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      J s t = J s u + J u t)
    (hJ_bound : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖J s t - roughApproxMap P cY s t‖ ≤ C' * |t - s| ^ (3 * γ))
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    J s t = roughIntegral P cY s t :=
  sewingMap₁_unique (roughApprox_sewingCondition₁ P cY)
    hJ_add hJ_bound has hst htb

/-! ## Convenience: the integral as a difference

The rough integral `∫_s^t` can be expressed as a difference of the
indefinite integral `t ↦ ∫_a^t`. This is useful for Hölder bounds. -/

/-- The **indefinite rough integral**: `t ↦ ∫_a^t Y d𝐗`. -/
def roughIntegralIndef
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    (t : ℝ) : F :=
  roughIntegral P cY a t

/-- The indefinite integral starts at zero. -/
theorem roughIntegralIndef_base
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X) :
    roughIntegralIndef P cY a = 0 :=
  roughIntegral_diag P cY le_rfl X.hab

end StochCalc
