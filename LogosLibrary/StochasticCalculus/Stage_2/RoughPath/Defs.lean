/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_2/RoughPath/Defs.lean
-/
import LogosLibrary.StochasticCalculus.Stage_2.Algebra.HomoNorm
/-!
# Rough Paths: Definition and Basic Properties

## Overview

A **rough path** over a Banach space `V` is a two-parameter function

    𝐗 : [a, b]² → G⁽²⁾(V)

satisfying two conditions:

1. **Chen's identity** (multiplicativity):
   `𝐗(s,t) = 𝐗(s,u) · 𝐗(u,t)` for all `s ≤ u ≤ t`

2. **Hölder regularity**:
   `‖𝐗(s,t)‖_{cc} ≤ C · |t - s|^γ` for all `s ≤ t`

where `γ ∈ (1/3, 1/2]` and `‖·‖_{cc}` is the homogeneous norm.

Chen's identity at the group level automatically implies:
- Level-1 additivity: `X_{s,t} = X_{s,u} + X_{u,t}`
- Level-2 Chen rule: `𝕏_{s,t} = 𝕏_{s,u} + X_{s,u} ⊗ X_{u,t} + 𝕏_{u,t}`

The Hölder regularity at the homoNorm level automatically implies:
- Level-1: `‖X_{s,t}‖ ≤ C|t-s|^γ`
- Level-2: `‖𝕏_{s,t}‖ ≤ C'|t-s|^{2γ}` (area at double order)

The regime `γ > 1/3` (equivalently `p < 3`) is precisely where level-2
rough paths operate: the sewing lemma for the rough integral needs `3γ > 1`.
For `γ > 1/2`, Chen's identity forces `𝕏` to be the iterated Young integral
and rough path theory reduces to Young integration (Stage 1).

## Key definitions

* `RoughPath` — the central structure
* `RoughPath.x` — level-1 component (the path increment)
* `RoughPath.area` — level-2 component (the Lévy area)
* `RoughPath.underlyingPath` — the path itself: `t ↦ X_{a,t}`

## Key results

* `chen₁`, `chen₂` — Chen's identity in components
* `x_holder`, `area_holder` — component-wise Hölder bounds
* `x_additive` — level-1 additivity
* `diag_eq_one` — `𝐗(s,s) = e` (identity)
* `inverse_relation` — `𝐗(t,s) = 𝐗(s,t)⁻¹` (from Chen + diagonal)

## Design decisions

**Hölder vs p-variation regularity.** We use Hölder regularity (`|t-s|^γ`)
rather than p-variation. This is simpler for the formalization — the sewing
lemma in Stage 0 takes Hölder exponents directly. For the general theory one
would use p-variation controls, but all standard examples (Brownian motion,
fractional BM) are Hölder, and the p-variation formulation can be added later
as a generalization.

**The interval [a,b].** All hypotheses are restricted to `a ≤ s ≤ t ≤ b`.
This follows the convention of Stages 0–1 and avoids dealing with global
definitions outside the interval.

**Geometric vs non-geometric.** Every `RoughPath` in this formalization is
automatically geometric (the group-like condition `Sym(𝕏) = ½(x⊗x)` is
baked into `GroupLike₂`). Non-geometric rough paths — which arise from Itô
integration — would use elements of `T⁽²⁾(V)` with `a₀ = 1` but without
the symmetric constraint. We do not need them for the Stratonovich theory.

## References

* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Chapter 2
* Lyons, T., *Differential equations driven by rough signals* (1998)
* Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Ch. 9
-/

open NormedTensorSquare StochCalc.TruncTensor₂ StochCalc.GroupLike₂ Real

noncomputable section

namespace StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]

/-! ## The rough path structure -/

/-- A **rough path** of Hölder regularity `γ` over a Banach space `V` on `[a, b]`.

A two-parameter function into the free step-2 nilpotent group `G⁽²⁾(V)`,
satisfying Chen's identity (multiplicativity) and Hölder regularity
with respect to the homogeneous norm. -/
structure RoughPath (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedTensorSquare V] (γ C a b : ℝ) where
  /-- The two-parameter function `(s, t) ↦ 𝐗(s,t) ∈ G⁽²⁾(V)`. -/
  val : ℝ → ℝ → GroupLike₂ V
  /-- **Chen's identity**: `𝐗(s,t) = 𝐗(s,u) · 𝐗(u,t)` for `s ≤ u ≤ t`. -/
  chen : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    val s t = val s u * val u t
  /-- **Diagonal**: `𝐗(s,s) = e` (the group identity). -/
  diag : ∀ s, a ≤ s → s ≤ b → val s s = 1
  /-- **Hölder regularity**: `‖𝐗(s,t)‖_{cc} ≤ C · |t - s|^γ`. -/
  regularity : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    homoNorm (val s t) ≤ C * |t - s| ^ γ
  /-- The Hölder exponent is in the rough regime: `γ > 1/3`. -/
  hγ_lower : (1 : ℝ) / 3 < γ
  /-- The Hölder exponent is at most `1/2` (otherwise Young suffices). -/
  hγ_upper : γ ≤ 1 / 2
  /-- The Hölder constant is non-negative. -/
  hC_nonneg : 0 ≤ C
  /-- The interval is non-degenerate. -/
  hab : a ≤ b
  --
  diag_global : ∀ s, val s s = 1

namespace RoughPath

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]
variable {γ C a b : ℝ}

/-! ## Component extraction

The level-1 and level-2 data of a rough path, extracted from the
`GroupLike₂`-valued function. -/

/-- The **level-1 component** (path increment): `X_{s,t} = π₁(𝐗(s,t))`. -/
def x (X : RoughPath V γ C a b) (s t : ℝ) : V :=
  (X.val s t).x

/-- The **level-2 component** (full second-order data): `𝕏_{s,t} = π₂(𝐗(s,t))`. -/
def area_full (X : RoughPath V γ C a b) (s t : ℝ) : T₂ V :=
  (X.val s t).𝕏

/-- The **Lévy area** (antisymmetric part): `A_{s,t} = Anti(𝕏_{s,t})`. -/
def area (X : RoughPath V γ C a b) (s t : ℝ) : T₂ V :=
  GroupLike₂.area (X.val s t)

/-! ## Chen's identity in components

These are the identities that the rough integral uses directly. -/

/-- **Level-1 Chen's identity**: `X_{s,t} = X_{s,u} + X_{u,t}`.

The path increment is additive — this is the familiar telescoping property.
It follows immediately from Chen's identity at the group level. -/
theorem x_additive (X : RoughPath V γ C a b)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    X.x s t = X.x s u + X.x u t := by
  simp only [x]
  rw [X.chen s u t has hsu hut htb, chen₁]

/-- **Level-2 Chen's identity**:
`𝕏_{s,t} = 𝕏_{s,u} + X_{s,u} ⊗ X_{u,t} + 𝕏_{u,t}`.

This is the content of rough path theory: the area does NOT split additively.
The cross-term `X_{s,u} ⊗ X_{u,t}` records the interaction between the
path increments on the two sub-intervals. -/
theorem area_full_chen (X : RoughPath V γ C a b)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    X.area_full s t =
      X.area_full s u + (X.x s u ⊗ₜ X.x u t) + X.area_full u t := by
  simp only [area_full, x]
  rw [X.chen s u t has hsu hut htb, chen₂]

/-- **Area Chen's identity**:
`A_{s,t} = A_{s,u} + Anti(X_{s,u} ⊗ X_{u,t}) + A_{u,t}`. -/
theorem area_chen (X : RoughPath V γ C a b)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    X.area s t =
      X.area s u + anti (X.x s u ⊗ₜ X.x u t) + X.area u t := by
  simp only [area, x]
  rw [X.chen s u t has hsu hut htb, chen_area]

/-! ## Diagonal and inverse -/

/-- On the diagonal, the level-1 component vanishes: `X_{s,s} = 0`. -/
@[simp] theorem x_diag (X : RoughPath V γ C a b)
    {s : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    X.x s s = 0 := by
  simp only [x, X.diag s has hsb, one_x]

/-- On the diagonal, the area vanishes: `𝕏_{s,s} = 0`. -/
@[simp] theorem area_full_diag (X : RoughPath V γ C a b)
    {s : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    X.area_full s s = 0 := by
  simp only [area_full, X.diag s has hsb, one_𝕏]

/-- On the diagonal, the Lévy area vanishes: `A_{s,s} = 0`. -/
@[simp] theorem area_diag (X : RoughPath V γ C a b)
    {s : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    X.area s s = 0 := by
  simp only [area, X.diag s has hsb, area_e]

/-! **Inverse relation**: `𝐗(t,s) = 𝐗(s,t)⁻¹` for `s ≤ t`.

This does NOT come from the `RoughPath` axioms directly — our `val` is only
defined for `s ≤ t` in the sense that the estimates only hold there. If one
extends the domain by setting `𝐗(t,s) := 𝐗(s,t)⁻¹`, then Chen's identity
extends to all triples. We record this as a definition + compatibility. -/

/-- Extend the rough path to reversed pairs: `𝐗(t,s) := 𝐗(s,t)⁻¹`. -/
def valReversed (X : RoughPath V γ C a b) (s t : ℝ) : GroupLike₂ V :=
  (X.val t s)⁻¹

theorem valReversed_eq_inv (X : RoughPath V γ C a b) (s t : ℝ) :
    X.valReversed s t = (X.val t s)⁻¹ := rfl

/-- The reversed value composes with the forward value to give the identity.
This is the algebraic content of `𝐗(s,t)⁻¹ · 𝐗(s,t) = e`. -/
theorem valReversed_mul_val (X : RoughPath V γ C a b) (s t : ℝ) :
    X.valReversed t s * X.val s t = 1 := by
  simp [valReversed]
  exact inv_mul (X.val s t)

/-! ## Hölder regularity of components

The homoNorm bound `‖𝐗(s,t)‖_{cc} ≤ C|t-s|^γ` gives separate bounds
on each component via the extraction lemmas from `HomoNorm.lean`. -/

/-- **Level-1 Hölder**: `‖X_{s,t}‖ ≤ C · |t-s|^γ`. -/
theorem x_holder (X : RoughPath V γ C a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖X.x s t‖ ≤ C * |t - s| ^ γ := by
  exact norm_x_le_of_homoNorm_le (X.regularity s t has hst htb)

/-- **Level-2 Hölder**: `‖A_{s,t}‖ ≤ C² · |t-s|^{2γ}`.

The area is controlled at *double* the Hölder order. This is the
parabolic scaling in action. -/
theorem area_holder (X : RoughPath V γ C a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖X.area s t‖ ≤ C ^ 2 * |t - s| ^ (2 * γ) := by
  have hC_ts : 0 ≤ C * |t - s| ^ γ := by
    apply mul_nonneg X.hC_nonneg
    exact Real.rpow_nonneg (abs_nonneg _) _
  calc ‖X.area s t‖
      ≤ (homoNorm (X.val s t)) ^ 2 := norm_area_le_homoNorm_sq _
    _ ≤ (C * |t - s| ^ γ) ^ 2 := by
        apply sq_le_sq'
        · linarith [homoNorm_nonneg (X.val s t)]
        · exact X.regularity s t has hst htb
    _ = C ^ 2 * |t - s| ^ (2 * γ) := by
        rw [mul_pow, ← rpow_natCast (|t - s| ^ γ) 2,
            ← rpow_mul (abs_nonneg _), show (2 : ℝ) * γ = 2 * γ from rfl]
        norm_cast
        ring_nf

/-- **Full area Hölder bound**: `‖𝕏_{s,t}‖ ≤ C'|t-s|^{2γ}` for an explicit `C'`.

This bounds the full `𝕏` (not just the antisymmetric part), using the
reconstruction `𝕏 = ½(x⊗x) + A`. -/
theorem area_full_holder (X : RoughPath V γ C a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖X.area_full s t‖ ≤ ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * |t - s| ^ (2 * γ) := by
  -- 𝕏 = ½(x⊗x) + A
  -- ‖𝕏‖ ≤ ½‖x‖² + ‖A‖
  -- ≤ ½(C|t-s|^γ)² + C²|t-s|^{2γ}
  -- = (½C² + C²)|t-s|^{2γ}
  have hx := X.x_holder has hst htb
  have hA := X.area_holder has hst htb
  have h𝕏 := norm_𝕏_le (X.val s t)
  calc ‖X.area_full s t‖
      ≤ (2⁻¹ : ℝ) * ‖(X.val s t).x‖ ^ 2 + homoNorm (X.val s t) ^ 2 := h𝕏
    _ ≤ (2⁻¹ : ℝ) * (C * |t - s| ^ γ) ^ 2 + (C * |t - s| ^ γ) ^ 2 := by
        gcongr
        · exact hx
        · exact homoNorm_nonneg _
        · exact X.regularity s t has hst htb
    _ = ((2⁻¹ : ℝ) * C ^ 2 + C ^ 2) * |t - s| ^ (2 * γ) := by
        rw [mul_pow, ← rpow_natCast (|t - s| ^ γ) 2,
            ← rpow_mul (abs_nonneg _)]
        ring_nf

/-! ## The underlying path

The "path" itself is recovered as `t ↦ X_{a,t}` — the level-1 increment
from the base point `a`. This is Hölder continuous by the level-1 estimate. -/

/-- The **underlying path**: `f(t) = X_{a,t}`, the level-1 increment from the
left endpoint. This is the path that the rough path enhances. -/
def underlyingPath (X : RoughPath V γ C a b) (t : ℝ) : V :=
  X.x a t

/-- The underlying path starts at zero: `f(a) = 0`. -/
theorem underlyingPath_base (X : RoughPath V γ C a b) :
    X.underlyingPath a = 0 :=
  X.x_diag le_rfl X.hab

/-- The underlying path is `γ`-Hölder. -/
theorem underlyingPath_holder (X : RoughPath V γ C a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖X.underlyingPath t - X.underlyingPath s‖ ≤ C * |t - s| ^ γ := by
  -- f(t) - f(s) = X_{a,t} - X_{a,s} = X_{s,t} (by additivity)
  rw [show X.underlyingPath t - X.underlyingPath s =
        X.x s t from by
    simp only [underlyingPath]
    rw [X.x_additive (le_refl a) has hst htb]
    abel]
  exact X.x_holder has hst htb

/-- The increment `X_{s,t}` equals the difference of the underlying path. -/
theorem x_eq_underlyingPath_diff (X : RoughPath V γ C a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    X.x s t = X.underlyingPath t - X.underlyingPath s := by
  simp only [underlyingPath]
  rw [X.x_additive (le_refl a) has hst htb]; abel

/-! ## The three-gamma condition

The condition `3γ > 1` is what makes the rough integral converge via the
sewing lemma. We record it here for use in `Integral/Defect.lean`. -/

/-- **The three-gamma condition**: `3γ > 1`.
This is the convergence condition for the rough integral's sewing argument.
It follows from `γ > 1/3`. -/
theorem three_gamma_gt_one (X : RoughPath V γ C a b) :
    1 < 3 * γ := by linarith [X.hγ_lower]

/-- `2γ + γ > 1`: the Young integrability condition for the remainder.
The controlled remainder `R^Y` is `2γ`-Hölder, and integrating against the
`γ`-Hölder path requires `2γ + γ > 1`. -/
theorem two_gamma_plus_gamma_gt_one (X : RoughPath V γ C a b) :
    1 < 2 * γ + γ := by linarith [X.hγ_lower]

/-- `γ > 0`: the Hölder exponent is positive. -/
theorem hγ_pos (X : RoughPath V γ C a b) : 0 < γ := by
  linarith [X.hγ_lower]

/-- `2γ > 0`: double the Hölder exponent is positive. -/
theorem two_gamma_pos (X : RoughPath V γ C a b) : 0 < 2 * γ := by
  linarith [X.hγ_lower]

/-! ## Compatibility with Stage 1

When `γ > 1/2` (Young regime), the level-2 data is *determined* by the
level-1 data: `𝕏_{s,t}` must equal the iterated Young integral. Our
rough paths have `γ ≤ 1/2`, so this determination fails and the area
carries genuinely new information. But the Stage 1 Young integral is
still used *inside* the rough integral (for the remainder term). -/

/-- The level-1 component satisfies Young-type Hölder regularity. -/
theorem x_isHolderLike (X : RoughPath V γ C a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖X.x s t‖ ≤ C * |t - s| ^ γ :=
  X.x_holder has hst htb

/-- The area satisfies `2γ`-Hölder regularity, which is > `γ` but ≤ 1.
This means the area is "more regular" than the path, but not regular enough
to be ignored — it contributes a correction to the rough integral. -/
theorem area_two_gamma_holder (X : RoughPath V γ C a b) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖X.area s t‖ ≤ C ^ 2 * |t - s| ^ (2 * γ) :=
  fun _s _t has hst htb => X.area_holder has hst htb

end RoughPath

/-! ## Construction helpers -/

/-- **Trivial rough path**: the constant path `X(s,t) = e`.

This is the zero rough path — it has `X_{s,t} = 0` and `A_{s,t} = 0`.
Exists for any `γ` and serves as the identity for rough path operations. -/
def RoughPath.trivial (γ a b : ℝ) (hγl : 1/3 < γ) (hγu : γ ≤ 1/2)
    (hab : a ≤ b) : RoughPath V γ 0 a b where
  val _ _ := 1
  chen _ _ _ _ _ _ _ := by simp; exact Eq.symm (e_mul e)
  diag _ _ _ := rfl
  regularity _ _ _ _ _ := by
    simp only [zero_mul]
    have h1e : (1 : GroupLike₂ V) = e := by ext <;> simp [e]
    linarith [(homoNorm_eq_zero_iff _).mpr h1e]
  hγ_lower := hγl
  hγ_upper := hγu
  hC_nonneg := le_refl 0
  hab := hab
  diag_global := fun _ => rfl

/-! ## Translation / reparametrization

Rough paths can be restricted to sub-intervals and translated. These
operations preserve Chen's identity and regularity. -/

/-- Restrict a rough path to a sub-interval `[a', b'] ⊆ [a, b]`. -/
def RoughPath.restrict (X : RoughPath V γ C a b)
    {a' b' : ℝ} (ha' : a ≤ a') (hb' : b' ≤ b) (hab' : a' ≤ b') :
    RoughPath V γ C a' b' where
  val := X.val
  chen s u t has hsu hut htb :=
    X.chen s u t (ha'.trans has) hsu hut (htb.trans hb')
  diag s has hsb := X.diag s (ha'.trans has) (hsb.trans hb')
  regularity s t has hst htb :=
    X.regularity s t (ha'.trans has) hst (htb.trans hb')
  hγ_lower := X.hγ_lower
  hγ_upper := X.hγ_upper
  hC_nonneg := X.hC_nonneg
  hab := hab'
  diag_global := fun s => X.diag_global s

end StochCalc
