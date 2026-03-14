/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: YoungIntegration/PVarCont.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.API
/-!
# p-Variation controls as Lipschitz controls

This file bridges the regularity theory of paths (Hölder continuity, p-variation)
to the control-function machinery of the Layer 2 sewing lemma.

## The key fact

If `X : ℝ → F` is `γ`-Hölder continuous with constant `C` on `[a, b]`, then the function

  `ω_X(s, t) := C ^ (1/γ) · |t - s|`

is a **Lipschitz control** in the sense of `LipControl`. More precisely, the `p`-variation
control (with `p = 1/γ`) satisfies

  `‖X‖_{p-var; [s,t]}^p  ≤  C^p · |t - s|^{γp}  ≤  C^p · diam^{γp - 1} · |t - s|`

so it is Lipschitz in interval length on any bounded domain.

## Why Lipschitz?

The Layer 2 sewing lemma needs `ω(s,t) ≤ L · (t - s)` to distribute the control
over dyadic sub-intervals: at level `n`, each piece gets `ω ≤ L · |t-s| / 2^n`,
giving the geometric decay `2^{-n(α+β-1)}`.

For Hölder paths this is automatic. For general finite `p`-variation paths one
needs the stronger hypothesis that the `p`-variation control is Lipschitz —
which is a separate (and interesting) question related to the continuity of
`t ↦ ‖X‖_{p-var; [a,t]}^p`. See `PVariation/TODO.lean`.

## Main results

* `holderControl_lipControl` — a `γ`-Hölder path gives a `LipControl` with
  `ω(s,t) = C^p · |t-s|^{γp}` and Lipschitz constant `C^p · diam^{γp-1}`.
* `holderControl_nonneg`, `holderControl_diag`, `holderControl_superadd` —
  the individual `LipControl` fields.

## References

* [Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Chapter 1]
* [Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*,
  Chapter 5 (p-variation)]
-/

noncomputable section

open Real Set Filter Finset

namespace StochCalc

/-! ### Hölder continuity -/

section Holder

variable {F : Type*} [NormedAddCommGroup F]

/-- A function `X` is `γ`-Hölder continuous with constant `C` on `[a, b]`. -/
structure IsHolderOn (X : ℝ → F) (γ C a b : ℝ) : Prop where
  /-- The exponent is positive. -/
  γ_pos : 0 < γ
  /-- The exponent is at most 1 (convention). -/
  γ_le_one : γ ≤ 1
  /-- The constant is nonneg. -/
  C_nonneg : 0 ≤ C
  /-- The interval is well-oriented. -/
  hab : a ≤ b
  /-- The Hölder bound: `‖X(t) - X(s)‖ ≤ C · |t - s|^γ`. -/
  holder_bound : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    ‖X t - X s‖ ≤ C * |t - s| ^ γ

end Holder

/-! ### The Hölder control function -/

section HolderControl

variable {F : Type*} [NormedAddCommGroup F]

/-- The **Hölder control function**: `ω_X(s, t) := C^p · |t - s|^{γp}`
where `p = 1/γ`, so `γp = 1` and this simplifies to `C^{1/γ} · |t - s|`.

However, we keep the general form `C^p · |t - s|^{γp}` for two reasons:
1. It matches the `p`-variation bound exactly.
2. For `γp > 1` (i.e., `p < 1/γ`), the control is *better* than Lipschitz.

The Lipschitz constant is `C^p · diam^{γp - 1}` when `γp ≥ 1`, which
on a bounded interval is finite. -/
def holderControl (C γ : ℝ) (p : ℝ) (s t : ℝ) : ℝ :=
  C ^ p * |t - s| ^ (γ * p)

/-- The Hölder control is nonneg for nonneg `C` and `s ≤ t`. -/
theorem holderControl_nonneg {C γ p : ℝ} (hC : 0 ≤ C) (_hγ : 0 < γ)
    (_hp : 0 < p) (s t : ℝ) :
    0 ≤ holderControl C γ p s t := by
  unfold holderControl
  apply mul_nonneg
  · exact rpow_nonneg hC p
  · exact rpow_nonneg (abs_nonneg _) _

/-- The Hölder control vanishes on the diagonal. -/
theorem holderControl_diag {C γ p : ℝ} (hγ : 0 < γ) (hp : 0 < p) (s : ℝ) :
    holderControl C γ p s s = 0 := by
  simp [holderControl, sub_self, abs_zero, zero_rpow (ne_of_gt (mul_pos hγ hp))]

/-- **Super-additivity** of the Hölder control when `γp ≥ 1`.

This is the key inequality: for `θ = γp ≥ 1`,
  `|t - s|^θ ≥ |u - s|^θ + |t - u|^θ`
whenever `s ≤ u ≤ t`. This is because `x ↦ x^θ` is convex for `θ ≥ 1`,
and `|t-s| = |u-s| + |t-u|`, so `(a+b)^θ ≥ a^θ + b^θ` for `a, b ≥ 0`.

For `γp = 1` (the natural exponent `p = 1/γ`), this is trivially an *equality*. -/
theorem holderControl_superadd {C γ p : ℝ} (hC : 0 ≤ C) (hγp : 1 ≤ γ * p)
    {s u t : ℝ} (hsu : s ≤ u) (hut : u ≤ t) :
    holderControl C γ p s u + holderControl C γ p u t ≤
      holderControl C γ p s t := by
  unfold holderControl
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (rpow_nonneg hC p)
  set θ := γ * p
  have hθ_pos : 0 < θ := lt_of_lt_of_le one_pos hγp
  have hθ1 : 0 ≤ θ - 1 := sub_nonneg.mpr hγp
  -- Since s ≤ u ≤ t, drop absolute values and split t - s
  rw [abs_of_nonneg (sub_nonneg.mpr hsu), abs_of_nonneg (sub_nonneg.mpr hut),
      abs_of_nonneg (sub_nonneg.mpr (hsu.trans hut)),
      show t - s = (u - s) + (t - u) from by ring]
  set a := u - s
  set b := t - u
  have ha_nn : 0 ≤ a := sub_nonneg.mpr hsu
  have hb_nn : 0 ≤ b := sub_nonneg.mpr hut
  -- Edge cases: if either piece is zero, 0^θ = 0 and it's trivial
  by_cases ha0 : a = 0
  · simp [ha0, zero_rpow hθ_pos.ne']
  · by_cases hb0 : b = 0
    · simp [hb0, zero_rpow hθ_pos.ne']
    · -- Main case: a, b > 0. Factor x^θ = x · x^{θ-1}.
      have ha_pos : 0 < a := lt_of_le_of_ne ha_nn (Ne.symm ha0)
      have hb_pos : 0 < b := lt_of_le_of_ne hb_nn (Ne.symm hb0)
      have hab_pos : 0 < a + b := add_pos ha_pos hb_pos
      have ha_eq : a ^ θ = a * a ^ (θ - 1) := by
        rw [show θ = 1 + (θ - 1) from by ring, rpow_add ha_pos, rpow_one]
        simp only [add_sub_cancel]
      have hb_eq : b ^ θ = b * b ^ (θ - 1) := by
        rw [show θ = 1 + (θ - 1) from by ring, rpow_add hb_pos, rpow_one]
        simp only [add_sub_cancel]
      have hab_eq : (a + b) ^ θ = (a + b) * (a + b) ^ (θ - 1) := by
        rw [show θ = 1 + (θ - 1) from by ring, rpow_add hab_pos, rpow_one]
        simp only [add_sub_cancel]
      rw [ha_eq, hb_eq, hab_eq]
      -- x^{θ-1} ≤ (a+b)^{θ-1} for each piece, then collect
      rw [add_mul]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (rpow_le_rpow ha_nn (le_add_of_nonneg_right hb_nn) hθ1) ha_nn
      · exact mul_le_mul_of_nonneg_left
          (rpow_le_rpow hb_nn (le_add_of_nonneg_left ha_nn) hθ1) hb_nn


/-- **Lipschitz bound**: on `[a, b]`, `holderControl C γ p s t ≤ L · (t - s)`
where `L = C^p · (b - a)^{γp - 1}`.

Proof: `C^p · |t-s|^{γp} = C^p · |t-s|^{γp-1} · |t-s| ≤ C^p · (b-a)^{γp-1} · |t-s|`.

When `γp = 1` (the natural exponent), the Lipschitz constant is just `C^p = C^{1/γ}`. -/
theorem holderControl_lip {C γ p a b : ℝ} (hC : 0 ≤ C) (hγp : 1 ≤ γ * p)
    (_hab : a ≤ b) {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    holderControl C γ p s t ≤ C ^ p * (b - a) ^ (γ * p - 1) * (t - s) := by
  unfold holderControl
  set θ := γ * p
  have hθ1 : 0 ≤ θ - 1 := sub_nonneg.mpr hγp
  have hts_nn : 0 ≤ t - s := sub_nonneg.mpr hst
  have hts_le : t - s ≤ b - a := by linarith
  rw [abs_of_nonneg hts_nn,
      show θ = (θ - 1) + 1 from by ring,
      rpow_add' hts_nn (by linarith : (θ - 1) + 1 ≠ 0),
      rpow_one, ← mul_assoc]
  -- Goal: C^p * (t-s)^{θ-1} * (t-s) ≤ C^p * (b-a)^{θ-1} * (t-s)
  apply mul_le_mul_of_nonneg_right _ hts_nn
  apply mul_le_mul_of_nonneg_left _ (rpow_nonneg hC p)
  simp only [sub_add_cancel]
  exact rpow_le_rpow hts_nn hts_le hθ1

/-- **The main bridge**: a `γ`-Hölder path defines a `LipControl`.

This packages `holderControl C γ p` (with `p = 1/γ`, so `γp = 1`)
as a `LipControl` on `[a, b]`. -/
def holderControl_lipControl {F : Type*} [NormedAddCommGroup F]
    {X : ℝ → F} {γ C a b : ℝ} (hX : IsHolderOn X γ C a b) :
    LipControl (holderControl C γ (1/γ)) a b where
  nonneg := fun s t _has _hst _htb =>
    holderControl_nonneg hX.C_nonneg hX.γ_pos (one_div_pos.mpr hX.γ_pos) s t
  diag := fun s => holderControl_diag hX.γ_pos (one_div_pos.mpr hX.γ_pos) s
  superadd := fun s u t _has hsu hut _htb => by
    apply holderControl_superadd hX.C_nonneg
    · rw [mul_one_div_cancel (ne_of_gt hX.γ_pos)]
    · exact hsu
    · exact hut
  lip_const := C ^ (1/γ) * (b - a) ^ (γ * (1/γ) - 1)
  lip_const_nonneg := by
    apply mul_nonneg (rpow_nonneg hX.C_nonneg _)
    rw [mul_one_div_cancel (ne_of_gt hX.γ_pos), sub_self]
    simp
  lip_bound := fun s t has hst htb =>
    holderControl_lip hX.C_nonneg
      (by rw [mul_one_div_cancel (ne_of_gt hX.γ_pos)])
      hX.hab has hst htb

end HolderControl

/-! ### Hölder paths give p-variation controls -/

section PVarBridge

variable {F : Type*} [NormedAddCommGroup F]

/-- The Hölder control bounds the actual increment:
`‖X(t) - X(s)‖^p ≤ holderControl C γ p s t` when `X` is `γ`-Hölder.

This is immediate: `‖X(t) - X(s)‖^p ≤ (C · |t-s|^γ)^p = C^p · |t-s|^{γp}`. -/
theorem holder_increment_le {X : ℝ → F} {γ C a b : ℝ}
    (hX : IsHolderOn X γ C a b) (p : ℝ) (hp : 0 < p) {s t : ℝ}
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖X t - X s‖ ^ p ≤ holderControl C γ p s t := by
  unfold holderControl
  calc ‖X t - X s‖ ^ p
      ≤ (C * |t - s| ^ γ) ^ p :=
        rpow_le_rpow (norm_nonneg _) (hX.holder_bound s t has hst htb) hp.le
    _ = C ^ p * (|t - s| ^ γ) ^ p :=
        mul_rpow hX.C_nonneg (rpow_nonneg (abs_nonneg _) _)
    _ = C ^ p * |t - s| ^ (γ * p) := by
        rw [← rpow_mul (abs_nonneg _)]


/- **Two-path Hölder control**: given `γ`-Hölder `X` with constant `C_X`
and `δ`-Hölder `Y` with constant `C_Y`, we get two `LipControl`s
with the crucial exponent relationship `1/q + 1/p = δ + γ > 1`.

This is the setup for `SewingCondition₂`: the two controls are
`ω₁ = holderControl C_Y δ (1/δ)` and `ω₂ = holderControl C_X γ (1/γ)`,
with `α = δ · (1/δ) = 1... `

Wait — the exponents in the sewing condition are `α = 1/q` and `β = 1/p`
where `q` is the variation exponent of `Y` and `p` of `X`. For Hölder paths,
`p = 1/γ` and `q = 1/δ`, so `α = δ` and `β = γ`, with `α + β = δ + γ > 1`.

But the controls are `ω₁(s,u) = C_Y^q · |u-s|^{δq} = C_Y^{1/δ} · |u-s|` and
similarly `ω₂(u,t) = C_X^{1/γ} · |t-u|`, both Lipschitz.

The defect bound becomes:
  `‖δΞ(s,u,t)‖ ≤ C_X · C_Y · |u-s|^δ · |t-u|^γ`
  `= C_X · C_Y · ω₁(s,u)^δ · ω₂(u,t)^γ / (C_Y^{1/δ})^δ · (C_X^{1/γ})^γ`
  `= (C_X · C_Y) / (C_Y · C_X) · ω₁^δ · ω₂^γ = ω₁^δ · ω₂^γ`

So in fact `K = 1` when we use the normalized controls! This is very clean. -/
-- (This is a documentation section; the actual construction is in Defect.lean.)

end PVarBridge

end StochCalc
