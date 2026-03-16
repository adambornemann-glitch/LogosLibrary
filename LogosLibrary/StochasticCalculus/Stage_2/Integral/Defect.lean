/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_2/Integral/Defect.lean
-/
import LogosLibrary.StochasticCalculus.Stage_2.Controlled.Defs
/-!
# The Rough Integral: Approximation Map and Defect

## Overview

This file contains the **analytical heart** of rough path integration: the
computation of the defect of the rough integral approximation and the
verification that it satisfies the sewing condition.

Given a controlled path `(Y, Y')` driven by a rough path `𝐗`, the rough
integral approximation is:

    Ξ(s, t) = σ(Y(s), X_{s,t}) + τ(Y'(s), 𝕏_{s,t})

where `σ` pairs the path value with the level-1 increment and `τ` pairs the
Gubinelli derivative with the level-2 area. The defect `δΞ(s, u, t)` consists
of three terms, each bounded at order `|t - s|^{3γ}`:

**Term 1** — Derivative variation × increment:
    `(Y'(s) - Y'(u)) · X_{u,t}`  bounded by  `C_{Y'} · C_X · |u-s|^γ · |t-u|^γ`

**Term 2** — Path value × cross-term:
    `σ(Y(s), X_{s,u} ⊗ₜ X_{u,t})`  bounded by  `M_σ · M_Y · C_X² · |u-s|^γ · |t-u|^γ`

**Term 3** — Path variation × area:
    `τ(Y'(s) - Y'(u), 𝕏_{u,t})`  bounded by  `M_τ · C_{Y'} · C_𝕏 · |u-s|^γ · |t-u|^{2γ}`

All three terms have total Hölder order `≥ 2γ > 1` (in fact `≥ 3γ`), so the
sewing lemma from Stage 0 converges.

## The pairing problem

The rough integral requires two pairings:
- `σ : E → V → F` — how path values act on increments (produces the integral output)
- `τ : (V →L[ℝ] E) → T₂(V) → F` — how Gubinelli derivatives act on areas

In the standard theory with `E = L(V, W)`:
- `σ(Y(s), v) = Y(s)(v)` — application
- `τ(Y'(s), 𝕏) = Y'(s) ∘ 𝕏` — extension to the tensor product

We axiomatize these pairings as parameters: continuous bilinear maps with
norm bounds. This keeps the file general while isolating the one piece that
depends on the specific algebraic setup.

## The convergence mechanism

The total defect bound is:

    ‖δΞ(s, u, t)‖ ≤ K · |t - s|^{3γ}

with `3γ > 1` (from `γ > 1/3`). This is exactly `SewingCondition₁` with
`θ = 3γ`, so the sewing machine from Stage 0 produces the rough integral.

The condition `3γ > 1` is **sharp**: for `γ = 1/3` (the boundary), the
sewing lemma fails — this is the regime where one needs level-3 rough paths.

## Dependencies

This file imports and uses:
- **Stage 0**: `SewingCondition₁`, `sewingMap₁` (the sewing machine)
- **Stage 1**: Young integration (for the remainder term, if needed)
- **Stage 2/Algebra**: Chen's identity, norm bounds
- **Stage 2/Controlled**: The controlled path structure and its estimates

## References

* Gubinelli, M., *Controlling rough paths*, J. Funct. Anal. **216** (2004), §3
* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Chapter 4
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

/-! ## The pairing structure

We axiomatize the two pairings needed for rough integration. In practice,
these come from the algebraic structure of the integrand space. -/

/-- The data needed to define a rough integral: two continuous bilinear pairings
that describe how the integrand interacts with the rough path data. -/
structure RoughIntegralPairing
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedTensorSquare V]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- **Level-1 pairing**: `σ(y, v)` pairs a path value `y ∈ E` with an
  increment `v ∈ V` to produce an integral value in `F`.
  In the standard case `E = L(V, F)`, this is just application: `σ(y, v) = y(v)`. -/
  σ : E →L[ℝ] V →L[ℝ] F
  /-- **Level-2 pairing**: `τ(φ, 𝕏)` pairs a Gubinelli derivative `φ ∈ L(V, E)`
  with an area element `𝕏 ∈ T₂(V)` to produce an integral value in `F`.
  In the standard case, this is the extension of `φ` to `V ⊗ V`. -/
  τ : (V →L[ℝ] E) →L[ℝ] (T₂ V) →L[ℝ] F
  /-- **Compatibility**: `σ(φ(v), w) = τ(φ, v ⊗ₜ w)` for pure tensors.
  This is the key algebraic condition linking the two pairings. It ensures
  that the level-1 and level-2 contributions are consistent. -/
  compat : ∀ (φ : V →L[ℝ] E) (v w : V),
    σ (φ v) w = τ φ (v ⊗ₜ w)

namespace RoughIntegralPairing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedTensorSquare V]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Operator norm bound for the level-1 pairing. -/
theorem σ_bound (P : RoughIntegralPairing E V F) (y : E) (v : V) :
    ‖P.σ y v‖ ≤ ‖P.σ‖ * ‖y‖ * ‖v‖ := by
  calc ‖P.σ y v‖
      ≤ ‖P.σ y‖ * ‖v‖ := (P.σ y).le_opNorm v
    _ ≤ (‖P.σ‖ * ‖y‖) * ‖v‖ := by gcongr; exact P.σ.le_opNorm y
    _ = ‖P.σ‖ * ‖y‖ * ‖v‖ := by ring

/-- Operator norm bound for the level-2 pairing. -/
theorem τ_bound (P : RoughIntegralPairing E V F) (φ : V →L[ℝ] E) (𝕏 : T₂ V) :
    ‖P.τ φ 𝕏‖ ≤ ‖P.τ‖ * ‖φ‖ * ‖𝕏‖ := by
  calc ‖P.τ φ 𝕏‖
      ≤ ‖P.τ φ‖ * ‖𝕏‖ := (P.τ φ).le_opNorm 𝕏
    _ ≤ (‖P.τ‖ * ‖φ‖) * ‖𝕏‖ := by gcongr; exact P.τ.le_opNorm φ
    _ = ‖P.τ‖ * ‖φ‖ * ‖𝕏‖ := by ring

end RoughIntegralPairing

/-! ## The rough integral approximation map -/

variable {X : RoughPath V γ C a b}

/-- The **rough integral approximation map**:

    `Ξ(s, t) = σ(Y(s), X_{s,t}) + τ(Y'(s), 𝕏_{s,t})`

This is the left-point Riemann sum with a second-order area correction.
The first term is the "Young" part; the second is the "rough" correction
that is needed because `γ ≤ 1/2`. -/
def roughApproxMap
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    (s t : ℝ) : F :=
  P.σ (cY.Y s) (X.x s t) + P.τ (cY.Y' s) (X.area_full s t)

/-! ## The defect computation

This is the algebraic core. The defect `δΞ(s, u, t) = Ξ(s,t) - Ξ(s,u) - Ξ(u,t)`
decomposes into three identifiable terms. -/

/-- The **defect** of the rough integral approximation. -/
def roughDefect
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    (s u t : ℝ) : F :=
  roughApproxMap P cY s t - roughApproxMap P cY s u - roughApproxMap P cY u t


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- **Corrected defect identity** with explicit signs:

    δΞ(s, u, t) = -σ(R^Y_{s,u}, X_{u,t}) + τ(Y'(s) - Y'(u), 𝕏_{u,t})

The minus sign on the remainder term is a consequence of the sign convention
`R(s,u) = Y(u) - Y(s) - Y'(s)·X_{s,u}`. -/
theorem roughDefect_eq
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    roughDefect P cY s u t =
      -(P.σ (cY.R s u) (X.x u t)) +
      P.τ (cY.Y' s - cY.Y' u) (X.area_full u t) := by
  simp only [roughDefect, roughApproxMap]
  -- Step 1: Substitute Y(u) = Y(s) + Y'(s)·X_{s,u} + R(s,u)
  rw [cY.taylor has hsu (hut.trans htb)]
  -- Step 2: Substitute Chen level 1 and level 2
  rw [X.x_additive has hsu hut htb, X.area_full_chen has hsu hut htb]
  -- Step 3: Fully expand CLM linearity in both arguments
  simp only [map_add, map_sub,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  -- Step 4: The compatibility condition cancels the cross-term
  rw [P.compat (cY.Y' s) (X.x s u) (X.x u t)]
  -- Step 5: Everything that remains is pure additive group arithmetic
  abel

/-! ## The defect bound

Each term in the defect is bounded at order `3γ`:
- `‖σ(R(s,u), X_{u,t})‖ ≤ ‖σ‖ · C_R · C_X · |u-s|^{2γ} · |t-u|^γ`
  which is `O(|t-s|^{3γ})` since `|u-s|, |t-u| ≤ |t-s|`
- `‖τ(Y'(s)-Y'(u), 𝕏_{u,t})‖ ≤ ‖τ‖ · C_{Y'} · C'_𝕏 · |u-s|^γ · |t-u|^{2γ}`
  which is also `O(|t-s|^{3γ})` -/

/-- **Defect bound**: `‖δΞ(s, u, t)‖ ≤ K · |t - s|^{3γ}`.

The constant `K` depends on the pairing norms, the controlled path constants,
and the rough path constants. -/
theorem roughDefect_bound
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    ‖roughDefect P cY s u t‖ ≤
      (‖P.σ‖ * cY.C_R * C + ‖P.τ‖ * cY.C_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2)) *
        |t - s| ^ (3 * γ) := by
  rw [roughDefect_eq P cY has hsu hut htb]
  -- Preliminaries
  have hγ_pos : 0 < γ := by linarith [X.hγ_lower]
  have hts_nn : 0 ≤ |t - s| := abs_nonneg _
  have hus_nn : 0 ≤ |u - s| := abs_nonneg _
  have htu_nn : 0 ≤ |t - u| := abs_nonneg _
  have hus_le : |u - s| ≤ |t - s| := by
    rw [abs_of_nonneg (sub_nonneg.mpr hsu), abs_of_nonneg (sub_nonneg.mpr (hsu.trans hut))]
    linarith
  have htu_le : |t - u| ≤ |t - s| := by
    rw [abs_of_nonneg (sub_nonneg.mpr hut), abs_of_nonneg (sub_nonneg.mpr (hsu.trans hut))]
    linarith
  have h3γ : |t - s| ^ (2 * γ) * |t - s| ^ γ = |t - s| ^ (3 * γ) := by
    rw [show 3 * γ = 2 * γ + γ from by ring,
        Real.rpow_add' hts_nn (by positivity : (0 : ℝ) < 2 * γ + γ).ne']
  have h3γ' : |t - s| ^ γ * |t - s| ^ (2 * γ) = |t - s| ^ (3 * γ) := by
    rw [mul_comm]; exact h3γ
  -- Bound term 1: ‖σ(R(s,u), X_{u,t})‖
  have hT1 : ‖P.σ (cY.R s u) (X.x u t)‖ ≤
      ‖P.σ‖ * cY.C_R * C * |t - s| ^ (3 * γ) :=
    calc ‖P.σ (cY.R s u) (X.x u t)‖
        ≤ ‖P.σ‖ * ‖cY.R s u‖ * ‖X.x u t‖ := P.σ_bound _ _
      _ ≤ ‖P.σ‖ * (cY.C_R * |u - s| ^ (2 * γ)) * (C * |t - u| ^ γ) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (cY.R_bound s u has hsu (hut.trans htb))
              (ContinuousLinearMap.opNorm_nonneg _))
            (X.x_holder (has.trans hsu) hut htb)
            (norm_nonneg _)
            (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _)
              (mul_nonneg cY.hC_R_nonneg (Real.rpow_nonneg hus_nn _)))
      _ = ‖P.σ‖ * cY.C_R * C * (|u - s| ^ (2 * γ) * |t - u| ^ γ) := by ring
      _ ≤ ‖P.σ‖ * cY.C_R * C * (|t - s| ^ (2 * γ) * |t - s| ^ γ) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg
            (ContinuousLinearMap.opNorm_nonneg _) cY.hC_R_nonneg) X.hC_nonneg)
          exact mul_le_mul (Real.rpow_le_rpow hus_nn hus_le (by positivity))
            (Real.rpow_le_rpow htu_nn htu_le hγ_pos.le)
            (Real.rpow_nonneg htu_nn _) (Real.rpow_nonneg hts_nn _)
      _ = ‖P.σ‖ * cY.C_R * C * |t - s| ^ (3 * γ) := by rw [h3γ]
  -- Bound term 2: ‖τ(Y'(s) - Y'(u), 𝕏_{u,t})‖
  have hT2 : ‖P.τ (cY.Y' s - cY.Y' u) (X.area_full u t)‖ ≤
      ‖P.τ‖ * cY.C_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * |t - s| ^ (3 * γ) :=
    calc ‖P.τ (cY.Y' s - cY.Y' u) (X.area_full u t)‖
        ≤ ‖P.τ‖ * ‖cY.Y' s - cY.Y' u‖ * ‖X.area_full u t‖ := P.τ_bound _ _
      _ ≤ ‖P.τ‖ * (cY.C_Y' * |u - s| ^ γ) *
            (((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * |t - u| ^ (2 * γ)) := by
          have h1 : ‖cY.Y' s - cY.Y' u‖ ≤ cY.C_Y' * |u - s| ^ γ := by
            rw [norm_sub_rev]; exact cY.Y'_bound s u has hsu (hut.trans htb)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left h1 (ContinuousLinearMap.opNorm_nonneg _))
            (X.area_full_holder (has.trans hsu) hut htb)
            (norm_nonneg _)
            (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _)
              (mul_nonneg cY.hC_Y'_nonneg (Real.rpow_nonneg hus_nn _)))
      _ = ‖P.τ‖ * cY.C_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) *
            (|u - s| ^ γ * |t - u| ^ (2 * γ)) := by ring
      _ ≤ ‖P.τ‖ * cY.C_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) *
            (|t - s| ^ γ * |t - s| ^ (2 * γ)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg
            (ContinuousLinearMap.opNorm_nonneg _) cY.hC_Y'_nonneg)
            (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (sq_nonneg _)))
          exact mul_le_mul (Real.rpow_le_rpow hus_nn hus_le hγ_pos.le)
            (Real.rpow_le_rpow htu_nn htu_le (by positivity))
            (Real.rpow_nonneg htu_nn _) (Real.rpow_nonneg hts_nn _)
      _ = ‖P.τ‖ * cY.C_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) *
            |t - s| ^ (3 * γ) := by rw [h3γ']
  -- Combine via triangle inequality
  calc ‖-(P.σ (cY.R s u) (X.x u t)) + P.τ (cY.Y' s - cY.Y' u) (X.area_full u t)‖
      ≤ ‖P.σ (cY.R s u) (X.x u t)‖ +
        ‖P.τ (cY.Y' s - cY.Y' u) (X.area_full u t)‖ := by
        calc _ ≤ ‖-(P.σ (cY.R s u) (X.x u t))‖ + _ := norm_add_le _ _
          _ = _ := by rw [norm_neg]
    _ ≤ ‖P.σ‖ * cY.C_R * C * |t - s| ^ (3 * γ) +
        ‖P.τ‖ * cY.C_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * |t - s| ^ (3 * γ) :=
        add_le_add hT1 hT2
    _ = (‖P.σ‖ * cY.C_R * C + ‖P.τ‖ * cY.C_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2)) *
          |t - s| ^ (3 * γ) := by ring

/-! ## Verification of the sewing condition

The defect bound gives `SewingCondition₁` with `θ = 3γ > 1`. -/

/-- The rough integral approximation satisfies the Layer 1 sewing condition
with exponent `θ = 3γ > 1`.

This is the key analytical result: it unlocks the sewing lemma from Stage 0
and produces the rough integral. -/
theorem roughApprox_sewingCondition₁
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X) :
    SewingCondition₁
      (roughApproxMap P cY)
      (3 * γ)
      (‖P.σ‖ * cY.C_R * C + ‖P.τ‖ * cY.C_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2))
      a b where
  vanish_diag := fun s => by
    simp only [roughApproxMap]
    have h := X.diag_global s
    have hx : X.x s s = 0 := by simp [RoughPath.x, h, GroupLike₂.e_x]
    have h𝕏 : X.area_full s s = 0 := by simp [RoughPath.area_full, h, GroupLike₂.e_𝕏]
    rw [hx, h𝕏, map_zero, map_zero, add_zero]
  one_lt_theta := by linarith [X.hγ_lower]
  K_nonneg := by
    apply add_nonneg
    · exact mul_nonneg (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) cY.hC_R_nonneg) X.hC_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) cY.hC_Y'_nonneg
      · linarith [sq_nonneg C, mul_nonneg (by positivity : (0:ℝ) ≤ 2⁻¹) (sq_nonneg C)]
  hab := X.hab
  defect_bound := fun s u t has hsu hut htb =>
    roughDefect_bound P cY has hsu hut htb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
/-! ## The rough integral exists!

Combining the sewing condition with the sewing lemma from Stage 0. -/

/-- **The rough integral exists**: given a controlled path and a pairing,
the sewing lemma produces a unique additive functional approximating `Ξ`.

This is the culmination of the entire programme:
- Stage 0 provides the sewing machine
- Stage 1 provides the Young integral (used internally)
- Stage 2 provides the algebraic structure and controlled path framework

The output is a two-parameter map `I(s,t)` satisfying:
1. `I(s,s) = 0`
2. `I(s,t) = I(s,u) + I(u,t)` (additivity)
3. `‖I(s,t) - Ξ(s,t)‖ ≤ K' · |t-s|^{3γ}` (approximation)
4. `I` is unique among additive functionals with such a bound -/
theorem rough_integral_exists
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X) :
    ∃ I : ℝ → ℝ → F,
      -- Diagonal
      (∀ s, a ≤ s → s ≤ b → I s s = 0) ∧
      -- Approximation bound
      (∀ s t, a ≤ s → s ≤ t → t ≤ b →
        ‖I s t - roughApproxMap P cY s t‖ ≤
          (‖P.σ‖ * cY.C_R * C + ‖P.τ‖ * cY.C_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2)) *
            sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ)) ∧
      -- Uniqueness: any additive functional with a 3γ-order bound agrees with I
      (∀ (J : ℝ → ℝ → F) (C' : ℝ),
        (∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → J s t = J s u + J u t) →
        (∀ s t, a ≤ s → s ≤ t → t ≤ b →
          ‖J s t - roughApproxMap P cY s t‖ ≤ C' * |t - s| ^ (3 * γ)) →
        ∀ s t, a ≤ s → s ≤ t → t ≤ b → J s t = I s t) := by
  have hSC := roughApprox_sewingCondition₁ P cY
  exact ⟨sewingMap₁ (roughApproxMap P cY) (3 * γ) _ a b hSC,
    fun s has hsb => sewingMap₁_diag hSC has hsb,
    fun s t has hst htb => sewingMap₁_dist_le hSC has hst htb,
    fun J C' hJ_add hJ_bound s t has hst htb =>
      sewingMap₁_unique hSC hJ_add hJ_bound has hst htb⟩

/-! ## The rough integral approximation estimate

The key quantitative bound: the rough integral is close to the approximation
`σ(Y(s), X_{s,t}) + τ(Y'(s), 𝕏_{s,t})` at order `3γ`. This is used in:
- Proving the integral is `γ`-Hölder
- Proving the integral output is itself a controlled path
- The Picard contraction argument -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- **Rough integral approximation estimate**:

    `‖∫_s^t Y d𝐗 - σ(Y(s), X_{s,t}) - τ(Y'(s), 𝕏_{s,t})‖ ≤ K · |t-s|^{3γ}`

This is the rough analogue of the Young–Loève estimate from Stage 1.
The three-gamma order means the approximation is "super-linear" —
better than what additivity alone would give. -/
theorem roughIntegral_approx_bound
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {I : ℝ → ℝ → F}
    (hI : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖I s t - roughApproxMap P cY s t‖ ≤
        (‖P.σ‖ * cY.C_R * C + ‖P.τ‖ * cY.C_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2)) *
          sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ))
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖I s t - P.σ (cY.Y s) (X.x s t) - P.τ (cY.Y' s) (X.area_full s t)‖ ≤
      (‖P.σ‖ * cY.C_R * C + ‖P.τ‖ * cY.C_Y' * ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2)) *
        sewingConst₁ (3 * γ) * |t - s| ^ (3 * γ) := by
  -- roughApproxMap P cY s t = σ(Y(s), X_{s,t}) + τ(Y'(s), 𝕏_{s,t}) by definition
  have h : I s t - roughApproxMap P cY s t =
      I s t - P.σ (cY.Y s) (X.x s t) - P.τ (cY.Y' s) (X.area_full s t) := by
    simp [roughApproxMap]; abel
  rw [← h]
  exact hI s t has hst htb


end StochCalc
