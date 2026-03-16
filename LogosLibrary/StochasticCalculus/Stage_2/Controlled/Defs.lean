/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_2/Controlled/Defs.lean
-/
import LogosLibrary.StochasticCalculus.Stage_2.RoughPath.Defs
import LogosLibrary.StochasticCalculus.Stage_1.API
/-!
# Gubinelli Controlled Rough Paths

## Overview

A path `Y : [a,b] → E` is **controlled by a rough path** `X` if its increments
are "explained" by the rough path up to a well-behaved remainder:

    Y(t) - Y(s) = Y'(s) · X_{s,t} + R^Y_{s,t}

where:
- `Y' : [a,b] → L(V, E)` is the **Gubinelli derivative** — a `γ`-Hölder function
  describing how `Y` responds to the driving signal `X`
- `R^Y_{s,t}` is the **controlled remainder** — a `2γ`-Hölder two-parameter function
- `X_{s,t}` is the level-1 increment of the rough path

The key insight: `R^Y` is `2γ`-Hölder, and integrating it against the `γ`-Hölder
path `X` requires `2γ + γ = 3γ > 1` — which holds precisely when `γ > 1/3`.
This is the analytical engine that makes rough integration work.

## Why this formulation?

In Lyons' original framework, rough integration is defined directly via the
Universal Limit Theorem. In Gubinelli's framework (2004), one first identifies
the *class of integrands* — controlled paths — and then the integral is a
straightforward application of the sewing lemma with approximation

    Ξ(s,t) = Y(s) · X_{s,t} + Y'(s) · 𝕏_{s,t}

The defect of this approximation involves `R^Y` integrated against `X` (a Young
integral, handled by Stage 1) plus `(Y'(u) - Y'(s)) · 𝕏_{u,t}` (bounded at
order `3γ`). The total defect is `O(|t-s|^{3γ})` with `3γ > 1`, so the sewing
machine converges.

This formulation is dramatically cleaner for formalization because:
1. The sewing lemma is already built (Stage 0)
2. The Young integral is already built (Stage 1)
3. The algebraic structure is already built (this stage)
4. The controlled path structure isolates the analytical content

## Design decisions

**The Gubinelli derivative `Y'` maps `V → E`.** More precisely, `Y'(s)` is a
continuous linear map `V →L[ℝ] E`. This is because `Y'(s) · X_{s,t}` must
produce an element of `E` from the `V`-valued increment `X_{s,t}`.

**Boundedness of `Y` is recorded separately.** The controlled path structure
gives Hölder regularity of `Y`, but the *supremum* bound `‖Y‖_∞ ≤ M` is needed
as a separate hypothesis in the rough integral estimates. We store it as a
field rather than deriving it (which would require compactness of [a,b]).

**Explicit constants everywhere.** The Picard iteration for rough ODEs needs to
track how the constants of the output controlled path depend on the input.
Every bound carries its explicit constant.

## Mathematical content

### The controlled path decomposition

    Y(t) = Y(s) + Y'(s) · X_{s,t} + R^Y_{s,t}

This is a first-order Taylor expansion of `Y` along the rough path `X`:
- `Y'(s)` plays the role of the derivative
- `X_{s,t}` plays the role of `Δt`
- `R^Y_{s,t}` is the remainder, controlled at order `(Δt)^{2γ}` rather than `(Δt)^2`

### Regularity of the Gubinelli derivative

    ‖Y'(t) - Y'(s)‖ ≤ C_{Y'} · |t - s|^γ

The derivative itself is `γ`-Hölder. This means `Y'` is as rough as the driving
path — it is part of the "controlled" world, not the "smooth" world.

### Regularity of the remainder

    ‖R^Y_{s,t}‖ ≤ C_R · |t - s|^{2γ}

This is `2γ`-Hölder — twice the regularity of the path. This improved regularity
is the entire point: it's what allows the Young integral of `R^Y` against `X`
to converge (since `2γ + γ = 3γ > 1`).

### Regularity of Y itself

From the decomposition:
    ‖Y(t) - Y(s)‖ ≤ ‖Y'(s)‖ · ‖X_{s,t}‖ + ‖R^Y_{s,t}‖
                   ≤ M_{Y'} · C_X · |t-s|^γ + C_R · |t-s|^{2γ}
                   ≤ (M_{Y'} · C_X + C_R · diam^γ) · |t-s|^γ

So `Y` is `γ`-Hölder — it inherits the regularity of the driving signal.

## References

* Gubinelli, M., *Controlling rough paths*, J. Funct. Anal. **216** (2004), 86–140
* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Chapters 4, 7
* Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Ch. 12
-/

open NormedTensorSquare StochCalc.TruncTensor₂ StochCalc.GroupLike₂ Real
open StochCalc.RoughPath

noncomputable section

namespace StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

variable {γ C a b : ℝ} {X : RoughPath V γ C a b}

/-! ## The controlled path structure -/

/-- A **Gubinelli controlled rough path**: a path `Y` whose increments are
explained by a rough path `X` up to a `2γ`-Hölder remainder.

The decomposition is: `Y(t) - Y(s) = Y'(s) · X_{s,t} + R(s,t)`

where `Y'` is the Gubinelli derivative (a `γ`-Hölder `L(V,E)`-valued path)
and `R` is the controlled remainder (`2γ`-Hölder). -/
structure ControlledPath
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : RoughPath V γ C a b) where
  /-- The path itself: `Y : [a,b] → E`. -/
  Y : ℝ → E
  /-- The **Gubinelli derivative**: `Y' : [a,b] → L(V, E)`.
  This is the "instantaneous linear response" of `Y` to the driving signal. -/
  Y' : ℝ → (V →L[ℝ] E)
  /-- The **controlled remainder**: `R(s,t) = Y(t) - Y(s) - Y'(s) · X_{s,t}`. -/
  R : ℝ → ℝ → E
  /-- The remainder equals the defining expression. -/
  R_eq : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    R s t = Y t - Y s - Y' s (X.x s t)
  /-- The remainder constant. -/
  C_R : ℝ
  /-- The remainder constant is non-negative. -/
  hC_R_nonneg : 0 ≤ C_R
  /-- **Remainder regularity**: `R` is `2γ`-Hölder. -/
  R_bound : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    ‖R s t‖ ≤ C_R * |t - s| ^ (2 * γ)
  /-- The derivative Hölder constant. -/
  C_Y' : ℝ
  /-- The derivative Hölder constant is non-negative. -/
  hC_Y'_nonneg : 0 ≤ C_Y'
  /-- **Derivative regularity**: `Y'` is `γ`-Hölder. -/
  Y'_bound : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    ‖Y' t - Y' s‖ ≤ C_Y' * |t - s| ^ γ
  /-- The supremum bound on the derivative. -/
  M_Y' : ℝ
  /-- The supremum bound is non-negative. -/
  hM_Y'_nonneg : 0 ≤ M_Y'
  /-- **Supremum bound on Y'**: `‖Y'(s)‖ ≤ M_{Y'}` for `s ∈ [a,b]`. -/
  Y'_sup_bound : ∀ s, a ≤ s → s ≤ b → ‖Y' s‖ ≤ M_Y'
  /-- The supremum bound on `Y`. -/
  M_Y : ℝ
  /-- The supremum bound is non-negative. -/
  hM_Y_nonneg : 0 ≤ M_Y
  /-- **Supremum bound on Y**: `‖Y(s)‖ ≤ M_Y` for `s ∈ [a,b]`. -/
  Y_sup_bound : ∀ s, a ≤ s → s ≤ b → ‖Y s‖ ≤ M_Y

namespace ControlledPath

/-! ## The remainder -/

/-- The remainder vanishes on the diagonal: `R(s,s) = 0`. -/
theorem R_diag (cY : ControlledPath E X) {s : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    cY.R s s = 0 := by
  rw [cY.R_eq s s has le_rfl hsb, X.x_diag has hsb, map_zero, sub_self, sub_zero]

/-- The decomposition identity: `Y(t) - Y(s) = Y'(s) · X_{s,t} + R(s,t)`. -/
theorem decomposition (cY : ControlledPath E X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    cY.Y t - cY.Y s = cY.Y' s (X.x s t) + cY.R s t := by
  rw [cY.R_eq s t has hst htb]; abel

/-- Rearranged: `Y(t) = Y(s) + Y'(s) · X_{s,t} + R(s,t)`. -/
theorem taylor (cY : ControlledPath E X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    cY.Y t = cY.Y s + cY.Y' s (X.x s t) + cY.R s t := by
  rw [cY.R_eq s t has hst htb]; abel

/-! ## Hölder regularity of Y

The path `Y` itself is `γ`-Hölder — it inherits the regularity of
the driving signal `X`. -/

/-- **Y is `γ`-Hölder**: `‖Y(t) - Y(s)‖ ≤ C'_Y · |t-s|^γ`. -/
theorem Y_holder (cY : ControlledPath E X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖cY.Y t - cY.Y s‖ ≤
      (cY.M_Y' * C + cY.C_R * (b - a) ^ γ) * |t - s| ^ γ := by
  rw [cY.decomposition has hst htb]
  have hts_nn : 0 ≤ |t - s| := abs_nonneg _
  have hγ_pos : 0 < γ := by linarith [X.hγ_lower]
  have hts_le : |t - s| ≤ b - a := by
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]; linarith
  have hts_γ_le : |t - s| ^ γ ≤ (b - a) ^ γ :=
    Real.rpow_le_rpow hts_nn hts_le hγ_pos.le
  have h2γ : |t - s| ^ (2 * γ) = |t - s| ^ γ * |t - s| ^ γ := by
    rw [show 2 * γ = γ + γ from by ring,
        Real.rpow_add' hts_nn (by positivity : (0 : ℝ) < γ + γ).ne']
  calc ‖cY.Y' s (X.x s t) + cY.R s t‖
      ≤ ‖cY.Y' s (X.x s t)‖ + ‖cY.R s t‖ := norm_add_le _ _
    _ ≤ ‖cY.Y' s‖ * ‖X.x s t‖ + cY.C_R * |t - s| ^ (2 * γ) := by
        gcongr
        · exact (cY.Y' s).le_opNorm _
        · exact cY.R_bound s t has hst htb
    _ ≤ cY.M_Y' * (C * |t - s| ^ γ) + cY.C_R * |t - s| ^ (2 * γ) := by
        have h := mul_le_mul
          (cY.Y'_sup_bound s has (hst.trans htb))
          (X.x_holder has hst htb)
          (norm_nonneg _)
          cY.hM_Y'_nonneg
        linarith
    _ = cY.M_Y' * C * |t - s| ^ γ + cY.C_R * (|t - s| ^ γ * |t - s| ^ γ) := by
        rw [h2γ]; ring
    _ ≤ cY.M_Y' * C * |t - s| ^ γ + cY.C_R * ((b - a) ^ γ * |t - s| ^ γ) := by
        gcongr; exact cY.hC_R_nonneg
    _ = (cY.M_Y' * C + cY.C_R * (b - a) ^ γ) * |t - s| ^ γ := by ring

/-! ## The remainder's "defect" identity

When we compute the defect of the rough integral approximation, the
remainder's behaviour under Chen's identity plays a central role.

The key identity:
  R(s,t) = R(s,u) + R(u,t) + [Y'(u) - Y'(s)] · X_{u,t}

This comes from the decomposition at three points and Chen's identity. -/

/-- **Remainder defect identity**: `R(s,t) - R(s,u) - R(u,t) = (Y'(u) - Y'(s)) · X_{u,t}`.

This is the "almost additivity" of the remainder: it fails to be additive by
a term involving the variation of `Y'` times the path increment. -/
theorem R_defect (cY : ControlledPath E X)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    cY.R s t - cY.R s u - cY.R u t = (cY.Y' u - cY.Y' s) (X.x u t) := by
  rw [cY.R_eq s t has (hsu.trans hut) htb,
      cY.R_eq s u has hsu (hut.trans htb),
      cY.R_eq u t (has.trans hsu) hut htb]
  -- LHS: (Yt - Ys - Y's·X_{st}) - (Yu - Ys - Y's·X_{su}) - (Yt - Yu - Y'u·X_{ut})
  -- = Y's·X_{su} + Y'u·X_{ut} - Y's·X_{st}
  -- = Y's·(X_{su} - X_{st}) + Y'u·X_{ut}
  -- = -Y's·X_{ut} + Y'u·X_{ut}         (by Chen₁: X_{st} = X_{su} + X_{ut})
  -- = (Y'u - Y's)·X_{ut}
  have hchen := X.x_additive has hsu hut htb
  simp only [ContinuousLinearMap.sub_apply]
  rw [hchen]
  simp only [map_add]
  abel

/-- **Remainder defect bound**: `‖R(s,t) - R(s,u) - R(u,t)‖ ≤ C_{Y'} · C_X · |u-s|^γ · |t-u|^γ`.

This is the cross-controlled product bound that the rough integral defect uses. -/
theorem R_defect_bound (cY : ControlledPath E X)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    ‖cY.R s t - cY.R s u - cY.R u t‖ ≤
      cY.C_Y' * C * |u - s| ^ γ * |t - u| ^ γ := by
  rw [cY.R_defect has hsu hut htb]
  calc ‖(cY.Y' u - cY.Y' s) (X.x u t)‖
      ≤ ‖cY.Y' u - cY.Y' s‖ * ‖X.x u t‖ :=
        (cY.Y' u - cY.Y' s).le_opNorm _
    _ ≤ (cY.C_Y' * |u - s| ^ γ) * (C * |t - u| ^ γ) := by
        have h := mul_le_mul
          (cY.Y'_bound s u has hsu (hut.trans htb))
          (X.x_holder (has.trans hsu) hut htb)
          (norm_nonneg _)
          (mul_nonneg cY.hC_Y'_nonneg (rpow_nonneg (abs_nonneg _) _))
        linarith
    _ = cY.C_Y' * C * |u - s| ^ γ * |t - u| ^ γ := by ring

/-! ## The rough integral approximation map

This is what `Integral/Defect.lean` will use: the approximation

    Ξ(s,t) = Y(s) · X_{s,t} + Y'(s) · 𝕏_{s,t}

and the defect of this approximation is O(|t-s|^{3γ}). -/

/-- The **rough integral approximation**: `Ξ(s,t) = Y(s) · X_{s,t} + Y'(s) · 𝕏_{s,t}`.

This is the left-point Riemann sum with a second-order correction from the area.
The Young approximation `Y(s) · X_{s,t}` alone has defect `O(|t-s|^{2γ})`, which
doesn't converge for `γ ≤ 1/2`. The area correction `Y'(s) · 𝕏_{s,t}` improves
the defect to `O(|t-s|^{3γ})`, which converges for `γ > 1/3`. -/
def roughApprox (cY : ControlledPath E X)
    (σ : E →L[ℝ] (T₂ V) →L[ℝ] E)
    (s t : ℝ) : E :=
  cY.Y' s (X.x s t) + σ (cY.Y s) (X.area_full s t)

/-! ## Algebraic operations on controlled paths

Controlled paths form a module: sums and scalar multiples of controlled
paths are controlled. Composition with smooth functions also preserves
the controlled structure (with a modified derivative). -/

/-- **Sum of controlled paths**: if `Y₁` and `Y₂` are controlled by `X`,
so is `Y₁ + Y₂`, with Gubinelli derivative `Y₁' + Y₂'`. -/
def add (Y₁ Y₂ : ControlledPath E X) : ControlledPath E X where
  Y := fun s => Y₁.Y s + Y₂.Y s
  Y' := fun s => Y₁.Y' s + Y₂.Y' s
  R := fun s t => Y₁.R s t + Y₂.R s t
  R_eq := fun s t has hst htb => by
    rw [Y₁.R_eq s t has hst htb, Y₂.R_eq s t has hst htb]
    simp [ContinuousLinearMap.add_apply]
    abel
  R_bound := fun s t has hst htb => by
    calc ‖Y₁.R s t + Y₂.R s t‖
        ≤ ‖Y₁.R s t‖ + ‖Y₂.R s t‖ := norm_add_le _ _
      _ ≤ Y₁.C_R * |t - s| ^ (2 * γ) + Y₂.C_R * |t - s| ^ (2 * γ) := by
          gcongr
          · exact Y₁.R_bound s t has hst htb
          · exact Y₂.R_bound s t has hst htb
      _ = (Y₁.C_R + Y₂.C_R) * |t - s| ^ (2 * γ) := by ring
  C_R := Y₁.C_R + Y₂.C_R
  hC_R_nonneg := add_nonneg Y₁.hC_R_nonneg Y₂.hC_R_nonneg
  Y'_bound := fun s t has hst htb => by
    calc ‖(Y₁.Y' t + Y₂.Y' t) - (Y₁.Y' s + Y₂.Y' s)‖
        = ‖(Y₁.Y' t - Y₁.Y' s) + (Y₂.Y' t - Y₂.Y' s)‖ := by congr 1; abel
      _ ≤ ‖Y₁.Y' t - Y₁.Y' s‖ + ‖Y₂.Y' t - Y₂.Y' s‖ := norm_add_le _ _
      _ ≤ (Y₁.C_Y' + Y₂.C_Y') * |t - s| ^ γ := by
          have := Y₁.Y'_bound s t has hst htb
          have := Y₂.Y'_bound s t has hst htb
          nlinarith
  C_Y' := Y₁.C_Y' + Y₂.C_Y'
  hC_Y'_nonneg := add_nonneg Y₁.hC_Y'_nonneg Y₂.hC_Y'_nonneg
  Y'_sup_bound := fun s has hsb => by
    calc ‖Y₁.Y' s + Y₂.Y' s‖
        ≤ ‖Y₁.Y' s‖ + ‖Y₂.Y' s‖ := norm_add_le _ _
      _ ≤ Y₁.M_Y' + Y₂.M_Y' := add_le_add (Y₁.Y'_sup_bound s has hsb)
                                              (Y₂.Y'_sup_bound s has hsb)
  M_Y' := Y₁.M_Y' + Y₂.M_Y'
  hM_Y'_nonneg := add_nonneg Y₁.hM_Y'_nonneg Y₂.hM_Y'_nonneg
  Y_sup_bound := fun s has hsb => by
    calc ‖Y₁.Y s + Y₂.Y s‖
        ≤ ‖Y₁.Y s‖ + ‖Y₂.Y s‖ := norm_add_le _ _
      _ ≤ Y₁.M_Y + Y₂.M_Y := add_le_add (Y₁.Y_sup_bound s has hsb)
                                           (Y₂.Y_sup_bound s has hsb)
  M_Y := Y₁.M_Y + Y₂.M_Y
  hM_Y_nonneg := add_nonneg Y₁.hM_Y_nonneg Y₂.hM_Y_nonneg

/-- **Scalar multiple of a controlled path**: if `Y` is controlled by `X`,
so is `c • Y`, with Gubinelli derivative `c • Y'`. -/
def smul (c : ℝ) (cY : ControlledPath E X) : ControlledPath E X where
  Y := fun s => c • cY.Y s
  Y' := fun s => c • cY.Y' s
  R := fun s t => c • cY.R s t
  R_eq := fun s t has hst htb => by
    rw [cY.R_eq s t has hst htb]
    simp [smul_sub, ContinuousLinearMap.smul_apply]
  C_R := |c| * cY.C_R
  hC_R_nonneg := mul_nonneg (abs_nonneg c) cY.hC_R_nonneg
  R_bound := fun s t has hst htb => by
    rw [norm_smul, Real.norm_eq_abs]
    calc |c| * ‖cY.R s t‖
        ≤ |c| * (cY.C_R * |t - s| ^ (2 * γ)) := by
          gcongr; exact cY.R_bound s t has hst htb
      _ = (|c| * cY.C_R) * |t - s| ^ (2 * γ) := by ring
  C_Y' := |c| * cY.C_Y'
  hC_Y'_nonneg := mul_nonneg (abs_nonneg c) cY.hC_Y'_nonneg
  Y'_bound := fun s t has hst htb => by
    rw [show c • cY.Y' t - c • cY.Y' s = c • (cY.Y' t - cY.Y' s) from by
      simp [smul_sub]]
    rw [norm_smul, Real.norm_eq_abs]
    calc |c| * ‖cY.Y' t - cY.Y' s‖
        ≤ |c| * (cY.C_Y' * |t - s| ^ γ) := by
          gcongr; exact cY.Y'_bound s t has hst htb
      _ = (|c| * cY.C_Y') * |t - s| ^ γ := by ring
  M_Y' := |c| * cY.M_Y'
  hM_Y'_nonneg := mul_nonneg (abs_nonneg c) cY.hM_Y'_nonneg
  Y'_sup_bound := fun s has hsb => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (cY.Y'_sup_bound s has hsb) (abs_nonneg c)
  M_Y := |c| * cY.M_Y
  hM_Y_nonneg := mul_nonneg (abs_nonneg c) cY.hM_Y_nonneg
  Y_sup_bound := fun s has hsb => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (cY.Y_sup_bound s has hsb) (abs_nonneg c)

/-! ## The driving signal as a controlled path

The rough path `X` itself is controlled by itself, with Gubinelli
derivative `Y' = id` and remainder `R = 0`. More precisely, the
underlying path `t ↦ X_{a,t}` is controlled with `Y'(s) = id_V`
(the identity map). But this requires `E = V`.

In the general theory, for `f : V → L(V, E)`, the controlled path
`Y = f(X)` has Gubinelli derivative `Y' = Df(X)·f(X)`. We defer
this to `Controlled/Algebra.lean`. -/

/-- The **identity controlled path**: `X` controls itself.

When `E = V`, the path `t ↦ X_{a,t}` is controlled by `X` with
`Y'(s) = id_V` and `R(s,t) = 0`.

This is the base case for the Picard iteration. -/
def identity [CompleteSpace V] (X : RoughPath V γ C a b) : ControlledPath (E := V) X where
  Y := X.underlyingPath
  Y' := fun _ => ContinuousLinearMap.id ℝ V
  R := fun _ _ => 0
  R_eq := fun s t has hst htb => by
    simp only [ContinuousLinearMap.id_apply]
    rw [X.x_eq_underlyingPath_diff has hst htb]; abel
  C_R := 0
  hC_R_nonneg := le_refl 0
  R_bound := fun _ _ _ _ _ => by simp
  C_Y' := 0
  hC_Y'_nonneg := le_refl 0
  Y'_bound := fun _ _ _ _ _ => by simp
  M_Y' := ‖ContinuousLinearMap.id ℝ V‖
  hM_Y'_nonneg := norm_nonneg _
  Y'_sup_bound := fun _ _ _ => le_refl _
  M_Y := C * (b - a) ^ γ
  hM_Y_nonneg := mul_nonneg X.hC_nonneg (rpow_nonneg (sub_nonneg.mpr X.hab) _)
  Y_sup_bound := fun s has hsb => by
    -- ‖X.underlyingPath s‖ = ‖X.x a s‖ ≤ C * |s - a|^γ ≤ C * (b - a)^γ
    have h := X.x_holder (le_refl a) has hsb
    have hsa : |s - a| ≤ b - a := by
      rw [abs_of_nonneg (sub_nonneg.mpr has)]; linarith
    calc ‖X.underlyingPath s‖
        = ‖X.x a s‖ := by rfl
      _ ≤ C * |s - a| ^ γ := h
      _ ≤ C * (b - a) ^ γ := by
        have hγ_nn : 0 ≤ γ := by linarith [X.hγ_lower]
        exact mul_le_mul_of_nonneg_left
          (rpow_le_rpow (abs_nonneg _) hsa hγ_nn)
          X.hC_nonneg

end ControlledPath

end StochCalc
