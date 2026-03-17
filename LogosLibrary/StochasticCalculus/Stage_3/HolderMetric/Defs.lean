/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_3/HolderMetric/Defs.lean
-/
import LogosLibrary.StochasticCalculus.Stage_2.API
/-!
# The Hölder rough path metric — Definitions

## Overview

This file defines the **unbundled rough path type** `RoughPathOn` and
the **Hölder rough path distance**. Together with `Triangle.lean`,
`Metric.lean`, and `Complete.lean`, this yields a complete metric space
on the space of rough paths — the key input for Stage 4 (Picard / ULT).

## The C-parametrisation problem

Stage 2's `RoughPath V γ C a b` bundles the Hölder constant `C` as a
type parameter. Two rough paths with `C₁ ≠ C₂` live in different types
and cannot be compared. For a metric space, we need all objects in one type.

**Solution:** `RoughPathOn V γ a b` uses existential bounds:
`∃ C, ∀ s t, ‖x(s,t)‖ ≤ C · |t−s|^γ`. A coercion from
`RoughPath V γ C a b` forgets the specific constant.

## The distance

We use the Hölder distance from Friz–Hairer, §8:

```
  d₁(X, cY) = sup_{s<t} ‖X(s,t) − Y(s,t)‖ / |t−s|^γ
  d₂(X, cY) = sup_{s<t} ‖𝕏(s,t) − 𝕐(s,t)‖ / |t−s|^{2γ}

  d(X, cY) = d₁ + d₂^{1/2}
```

The square root on `d₂` ensures correct homogeneity: under the natural
scaling `X ↦ λX` (which scales 𝕏 by λ²), both `d₁` and `d₂^{1/2}`
scale like |λ|.

We use `d₁ + d₂^{1/2}` rather than `(d₁² + d₂)^{1/2}` because the
triangle inequality is then immediate from the individual triangle
inequalities for `d₁` and `d₂^{1/2}` (using `√a + √b ≥ √(a+b)` would
go the wrong way for the latter form).

## Design decisions

- **`sSup` over `ℝ`** for the Hölder seminorms, not `iSup` in `ℝ≥0∞`.
  The `MetricSpace` typeclass needs `ℝ`-valued distance.

- **Degenerate case `a = b`**: the sup set is empty (no s < t in [a,a]),
  and we define `sSup ∅ = 0` via `Real.sSup_empty`. Distance is zero,
  and the metric space is a single point.

- **Strict inequality `s < t`** in the sup: this avoids dividing by zero.
  The value at `s = t` is determined by the diagonal conditions anyway.

## References

* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., §2.2, §8.1
-/

open NormedTensorSquare Real Set

noncomputable section

namespace StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]

/-! ### The unbundled rough path type -/

/-- A **rough path** on `[a, b]` with Hölder exponent `γ`, without a
specific Hölder constant in the type.

This is the type on which the metric space structure lives.

Fields:
- `x` : the level-1 path increment (V-valued)
- `area` : the level-2 "area" or "second iterated integral" (T₂ V-valued)
- `chen₁`, `chen₂` : Chen's relations (the algebraic identities)
- `x_diag`, `area_diag` : vanishing on the diagonal
- `x_bound`, `area_bound` : existentially quantified Hölder bounds -/
structure RoughPathOn (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedTensorSquare V] (γ : ℝ) (a b : ℝ) where
  /-- Level-1 increment: `X(s,t)` represents `X_t − X_s`. -/
  x : ℝ → ℝ → V
  /-- Level-2 area: `𝕏(s,t)` represents the "iterated integral"
  `∫_s^t (X_u − X_s) ⊗ dX_u`. -/
  area : ℝ → ℝ → T₂ V
  /-- Chen's identity, level 1: `X(s,t) = X(s,u) + X(u,t)`. -/
  chen₁ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    x s t = x s u + x u t
  /-- Chen's identity, level 2:
  `𝕏(s,t) = 𝕏(s,u) + 𝕏(u,t) + X(s,u) ⊗ X(u,t)`. -/
  chen₂ : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    area s t = area s u + area u t + x s u ⊗ₜ x u t
  /-- Level-1 diagonal: `X(s,s) = 0`. -/
  x_diag : ∀ s, a ≤ s → s ≤ b → x s s = 0
  /-- Level-2 diagonal: `𝕏(s,s) = 0`. -/
  area_diag : ∀ s, a ≤ s → s ≤ b → area s s = 0
  /-- Level-1 Hölder bound (existentially quantified). -/
  x_bound : ∃ C ≥ 0, ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    ‖x s t‖ ≤ C * |t - s| ^ γ
  /-- Level-2 Hölder bound (existentially quantified). -/
  area_bound : ∃ C ≥ 0, ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    ‖area s t‖ ≤ C * |t - s| ^ (2 * γ)
  /-- Outside the domain, level-1 defaults to zero. -/
  x_default : ∀ s t, ¬(a ≤ s ∧ s ≤ t ∧ t ≤ b) → x s t = 0
  /-- Outside the domain, level-2 defaults to zero. -/
  area_default : ∀ s t, ¬(a ≤ s ∧ s ≤ t ∧ t ≤ b) → area s t = 0

variable {γ a b : ℝ}

namespace RoughPathOn

/-- Extract a level-1 Hölder constant (via `Classical.choose`). -/
noncomputable def C₁ (X : RoughPathOn V γ a b) : ℝ :=
  X.x_bound.choose

lemma C₁_nonneg (X : RoughPathOn V γ a b) : 0 ≤ X.C₁ :=
  X.x_bound.choose_spec.1

lemma x_holder (X : RoughPathOn V γ a b) (s t : ℝ)
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖X.x s t‖ ≤ X.C₁ * |t - s| ^ γ :=
  X.x_bound.choose_spec.2 s t has hst htb

/-- Extract a level-2 Hölder constant. -/
noncomputable def C₂ (X : RoughPathOn V γ a b) : ℝ :=
  X.area_bound.choose

lemma C₂_nonneg (X : RoughPathOn V γ a b) : 0 ≤ X.C₂ :=
  X.area_bound.choose_spec.1

lemma area_holder (X : RoughPathOn V γ a b) (s t : ℝ)
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖X.area s t‖ ≤ X.C₂ * |t - s| ^ (2 * γ) :=
  X.area_bound.choose_spec.2 s t has hst htb

end RoughPathOn

/-! ### Coercion from the parametrised type -/

/-- Forget the explicit Hölder constant to obtain a `RoughPathOn`.

This is the bridge between Stage 2 (which works with `RoughPath V γ C a b`)
and Stage 3 (which needs all rough paths in one type). -/
def RoughPath.toOn (X : RoughPath V γ C a b) : RoughPathOn V γ a b where
  x := fun s t => if a ≤ s ∧ s ≤ t ∧ t ≤ b then X.x s t else 0
  area := fun s t => if a ≤ s ∧ s ≤ t ∧ t ≤ b then X.area_full s t else 0
  chen₁ := fun s u t has hsu hut htb => by
    have h₁ : a ≤ s ∧ s ≤ t ∧ t ≤ b := ⟨has, hsu.trans hut, htb⟩
    have h₂ : a ≤ s ∧ s ≤ u ∧ u ≤ b := ⟨has, hsu, hut.trans htb⟩
    have h₃ : a ≤ u ∧ u ≤ t ∧ t ≤ b := ⟨has.trans hsu, hut, htb⟩
    simp only [if_pos h₁, if_pos h₂, if_pos h₃]
    exact X.x_additive has hsu hut htb
  chen₂ := fun s u t has hsu hut htb => by
    have h₁ : a ≤ s ∧ s ≤ t ∧ t ≤ b := ⟨has, hsu.trans hut, htb⟩
    have h₂ : a ≤ s ∧ s ≤ u ∧ u ≤ b := ⟨has, hsu, hut.trans htb⟩
    have h₃ : a ≤ u ∧ u ≤ t ∧ t ≤ b := ⟨has.trans hsu, hut, htb⟩
    simp only [if_pos h₁, if_pos h₂, if_pos h₃]
    rw [X.area_full_chen has hsu hut htb]; abel
  x_diag := fun s has hsb => by
    have h : a ≤ s ∧ s ≤ s ∧ s ≤ b := ⟨has, le_rfl, hsb⟩
    simp [X.x_diag has hsb]
  area_diag := fun s has hsb => by
    have h : a ≤ s ∧ s ≤ s ∧ s ≤ b := ⟨has, le_rfl, hsb⟩
    simp [X.area_full_diag has hsb]
  x_bound := ⟨C, X.hC_nonneg, fun s t has hst htb => by
    have h : a ≤ s ∧ s ≤ t ∧ t ≤ b := ⟨has, hst, htb⟩
    simp only [if_pos h]; exact X.x_holder has hst htb⟩
  area_bound := ⟨(2⁻¹ : ℝ) * C ^ 2 + C ^ 2,
    add_nonneg (mul_nonneg (by positivity) (sq_nonneg C)) (sq_nonneg C),
    fun s t has hst htb => by
      have h : a ≤ s ∧ s ≤ t ∧ t ≤ b := ⟨has, hst, htb⟩
      simp only [if_pos h]; exact X.area_full_holder has hst htb⟩
  x_default := fun s t h => by simp [if_neg h]
  area_default := fun s t h => by simp [if_neg h]

/-! ### Hölder seminorms -/

/-- The set of normalised level-1 differences:
`{ ‖X₁(s,t) − X₂(s,t)‖ / |t−s|^γ | a ≤ s < t ≤ b }`.

This is a subset of `ℝ` whose `sSup` gives the level-1 Hölder distance. -/
def holderQuotientSet₁ (X cY : RoughPathOn V γ a b) : Set ℝ :=
  { q : ℝ | ∃ s t, a ≤ s ∧ s < t ∧ t ≤ b ∧ q = ‖X.x s t - cY.x s t‖ / |t - s| ^ γ }

/-- The set of normalised level-2 differences:
`{ ‖𝕏₁(s,t) − 𝕏₂(s,t)‖ / |t−s|^{2γ} | a ≤ s < t ≤ b }`. -/
def holderQuotientSet₂ (X cY : RoughPathOn V γ a b) : Set ℝ :=
  { q : ℝ | ∃ s t, a ≤ s ∧ s < t ∧ t ≤ b ∧
    q = ‖X.area s t - cY.area s t‖ / |t - s| ^ (2 * γ) }

/-- Every element of `holderQuotientSet₁` is nonneg. -/
lemma holderQuotientSet₁_nonneg (X cY : RoughPathOn V γ a b)
    {q : ℝ} (hq : q ∈ holderQuotientSet₁ X cY) : 0 ≤ q := by
  obtain ⟨s, t, _, hst, _, rfl⟩ := hq
  exact div_nonneg (norm_nonneg _) (rpow_nonneg (abs_nonneg _) _)

/-- Every element of `holderQuotientSet₂` is nonneg. -/
lemma holderQuotientSet₂_nonneg (X cY : RoughPathOn V γ a b)
    {q : ℝ} (hq : q ∈ holderQuotientSet₂ X cY) : 0 ≤ q := by
  obtain ⟨s, t, _, hst, _, rfl⟩ := hq
  exact div_nonneg (norm_nonneg _) (rpow_nonneg (abs_nonneg _) _)

/-- The quotient set₁ is bounded above by `C₁(X) + C₁(cY)`.
This is needed for `sSup` to be well-defined in `ℝ`. -/
lemma holderQuotientSet₁_bddAbove (X cY : RoughPathOn V γ a b) :
    BddAbove (holderQuotientSet₁ X cY) := by
  refine ⟨X.C₁ + cY.C₁, fun q hq => ?_⟩
  obtain ⟨s, t, has, hst, htb, rfl⟩ := hq
  have hst' : s ≤ t := hst.le
  have hts_pos : 0 < |t - s| ^ γ := by
    apply rpow_pos_of_pos
    simp only [abs_pos, ne_eq]
    linarith
  rw [div_le_iff₀ hts_pos]
  calc ‖X.x s t - cY.x s t‖
      ≤ ‖X.x s t‖ + ‖cY.x s t‖ := norm_sub_le _ _
    _ ≤ X.C₁ * |t - s| ^ γ + cY.C₁ * |t - s| ^ γ := by
        gcongr
        · exact X.x_holder s t has hst' htb
        · exact cY.x_holder s t has hst' htb
    _ = (X.C₁ + cY.C₁) * |t - s| ^ γ := by ring

/-- The quotient set₂ is bounded above. -/
lemma holderQuotientSet₂_bddAbove (X cY : RoughPathOn V γ a b) :
    BddAbove (holderQuotientSet₂ X cY) := by
  refine ⟨X.C₂ + cY.C₂, fun q hq => ?_⟩
  obtain ⟨s, t, has, hst, htb, rfl⟩ := hq
  have hst' : s ≤ t := hst.le
  have hts_pos : 0 < |t - s| ^ (2 * γ) := by
    apply rpow_pos_of_pos
    simp only [abs_pos, ne_eq]
    linarith
  rw [div_le_iff₀ hts_pos]
  calc ‖X.area s t - cY.area s t‖
      ≤ ‖X.area s t‖ + ‖cY.area s t‖ := norm_sub_le _ _
    _ ≤ X.C₂ * |t - s| ^ (2 * γ) + cY.C₂ * |t - s| ^ (2 * γ) := by
        gcongr
        · exact X.area_holder s t has hst' htb
        · exact cY.area_holder s t has hst' htb
    _ = (X.C₂ + cY.C₂) * |t - s| ^ (2 * γ) := by ring

/-- **Level-1 Hölder distance**: the Hölder seminorm of the difference
of the level-1 paths.

  `d₁(X, cY) = sup_{a ≤ s < t ≤ b} ‖X(s,t) − Y(s,t)‖ / |t−s|^γ`

Returns `0` when `a = b` (empty sup). -/
noncomputable def holderDist₁ (X cY : RoughPathOn V γ a b) : ℝ :=
  sSup (holderQuotientSet₁ X cY)

/-- **Level-2 Hölder distance**: the Hölder seminorm of the difference
of the level-2 areas.

  `d₂(X, cY) = sup_{a ≤ s < t ≤ b} ‖𝕏(s,t) − 𝕐(s,t)‖ / |t−s|^{2γ}`

Returns `0` when `a = b`. -/
noncomputable def holderDist₂ (X cY : RoughPathOn V γ a b) : ℝ :=
  sSup (holderQuotientSet₂ X cY)

/-- d₁ is nonneg. -/
lemma holderDist₁_nonneg (X cY : RoughPathOn V γ a b) :
    0 ≤ holderDist₁ X cY := by
  unfold holderDist₁
  by_cases h : (holderQuotientSet₁ X cY).Nonempty
  · exact le_csSup_of_le (holderQuotientSet₁_bddAbove X cY) h.some_mem
      (holderQuotientSet₁_nonneg X cY h.some_mem)
  · simp [Set.not_nonempty_iff_eq_empty.mp h, sSup_empty]

/-- d₂ is nonneg. -/
lemma holderDist₂_nonneg (X cY : RoughPathOn V γ a b) :
    0 ≤ holderDist₂ X cY := by
  unfold holderDist₂
  by_cases h : (holderQuotientSet₂ X cY).Nonempty
  · exact le_csSup_of_le (holderQuotientSet₂_bddAbove X cY) h.some_mem
      (holderQuotientSet₂_nonneg X cY h.some_mem)
  · simp [Set.not_nonempty_iff_eq_empty.mp h, sSup_empty]

/-- d₁ controls pointwise differences. -/
lemma holderDist₁_controls (X cY : RoughPathOn V γ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s < t) (htb : t ≤ b) :
    ‖X.x s t - cY.x s t‖ ≤ holderDist₁ X cY * |t - s| ^ γ := by
  have hts_pos : 0 < |t - s| ^ γ := by
    apply rpow_pos_of_pos
    simp only [abs_pos, ne_eq]
    linarith
  rw [← div_le_iff₀ hts_pos]
  exact le_csSup (holderQuotientSet₁_bddAbove X cY) ⟨s, t, has, hst, htb, rfl⟩

/-- d₂ controls pointwise differences. -/
lemma holderDist₂_controls (X cY : RoughPathOn V γ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s < t) (htb : t ≤ b) :
    ‖X.area s t - cY.area s t‖ ≤ holderDist₂ X cY * |t - s| ^ (2 * γ) := by
  have hts_pos : 0 < |t - s| ^ (2 * γ) := by
    apply rpow_pos_of_pos;
    simp only [abs_pos, ne_eq]
    linarith
  rw [← div_le_iff₀ hts_pos]
  exact le_csSup (holderQuotientSet₂_bddAbove X cY) ⟨s, t, has, hst, htb, rfl⟩

/-- d₁ is the *least* such controlling constant. -/
lemma holderDist₁_le_of_bound (X cY : RoughPathOn V γ a b) {M : ℝ}
    (hM_nonneg : 0 ≤ M)
    (hM : ∀ s t, a ≤ s → s < t → t ≤ b →
      ‖X.x s t - cY.x s t‖ ≤ M * |t - s| ^ γ) :
    holderDist₁ X cY ≤ M := by
  unfold holderDist₁
  by_cases h : (holderQuotientSet₁ X cY).Nonempty
  · apply csSup_le h
    rintro q ⟨s, t, has, hst, htb, rfl⟩
    have hts_pos : 0 < |t - s| ^ γ := by
      apply rpow_pos_of_pos; simp only [abs_pos, ne_eq]; linarith
    rw [div_le_iff₀ hts_pos]
    exact hM s t has hst htb
  · simp [Set.not_nonempty_iff_eq_empty.mp h, sSup_empty]
    exact hM_nonneg

/-- d₂ is the least controlling constant. -/
lemma holderDist₂_le_of_bound (X cY : RoughPathOn V γ a b) {M : ℝ}
    (hM_nonneg : 0 ≤ M)
    (hM : ∀ s t, a ≤ s → s < t → t ≤ b →
      ‖X.area s t - cY.area s t‖ ≤ M * |t - s| ^ (2 * γ)) :
    holderDist₂ X cY ≤ M := by
  unfold holderDist₂
  by_cases h : (holderQuotientSet₂ X cY).Nonempty
  · apply csSup_le h
    rintro q ⟨s, t, has, hst, htb, rfl⟩
    have hts_pos : 0 < |t - s| ^ (2 * γ) := by
      apply rpow_pos_of_pos; simp only [abs_pos, ne_eq]; linarith
    rw [div_le_iff₀ hts_pos]
    exact hM s t has hst htb
  · simp [Set.not_nonempty_iff_eq_empty.mp h, sSup_empty, hM_nonneg]

/-! ### The combined distance -/

/-- **The Hölder rough path distance.**

  `d(X, cY) = d₁(X, cY) + d₂(X, cY)^{1/2}`

The `d₂^{1/2}` term ensures correct scaling: under `X ↦ λX`
(level 1 scales by λ, level 2 by λ²), both summands scale by |λ|.

The additive form (rather than `(d₁² + d₂)^{1/2}`) makes the triangle
inequality immediate: it reduces to `d₁` triangle + `d₂^{1/2}` triangle,
and the latter follows from `√ being concave: √a + √b ≥ √(a+b)` applied
in the form `√(a+b) ≤ √a + √b`. -/
noncomputable def roughPathDist (X cY : RoughPathOn V γ a b) : ℝ :=
  holderDist₁ X cY + (holderDist₂ X cY) ^ (1/2 : ℝ)

/-- The combined distance is nonneg. -/
lemma roughPathDist_nonneg (X cY : RoughPathOn V γ a b) :
    0 ≤ roughPathDist X cY :=
  add_nonneg (holderDist₁_nonneg X cY)
    (rpow_nonneg (holderDist₂_nonneg X cY) _)

/-! ### Symmetry -/

/-- d₁ is symmetric. -/
lemma holderDist₁_symm (X cY : RoughPathOn V γ a b) :
    holderDist₁ X cY = holderDist₁ cY X := by
  unfold holderDist₁
  congr 1
  ext q
  simp only [holderQuotientSet₁, Set.mem_setOf_eq]
  constructor <;> (
    rintro ⟨s, t, has, hst, htb, rfl⟩
    exact ⟨s, t, has, hst, htb, by rw [norm_sub_rev]⟩)

/-- d₂ is symmetric. -/
lemma holderDist₂_symm (X cY : RoughPathOn V γ a b) :
    holderDist₂ X cY = holderDist₂ cY X := by
  unfold holderDist₂
  congr 1
  ext q
  simp only [holderQuotientSet₂, Set.mem_setOf_eq]
  constructor <;> (
    rintro ⟨s, t, has, hst, htb, rfl⟩
    exact ⟨s, t, has, hst, htb, by rw [norm_sub_rev]⟩)

/-- The combined distance is symmetric. -/
lemma roughPathDist_symm (X cY : RoughPathOn V γ a b) :
    roughPathDist X cY = roughPathDist cY X := by
  simp only [roughPathDist, holderDist₁_symm, holderDist₂_symm]

/-! ### Self-distance is zero -/

/-- d₁(X, X) = 0. -/
@[simp] lemma holderDist₁_self (X : RoughPathOn V γ a b) :
    holderDist₁ X X = 0 := by
  unfold holderDist₁
  apply le_antisymm
  · by_cases h : (holderQuotientSet₁ X X).Nonempty
    · apply csSup_le h
      rintro q ⟨s, t, _, _, _, rfl⟩
      simp
    · simp [Set.not_nonempty_iff_eq_empty.mp h, sSup_empty]
  · exact holderDist₁_nonneg X X

/-- d₂(X, X) = 0. -/
@[simp] lemma holderDist₂_self (X : RoughPathOn V γ a b) :
    holderDist₂ X X = 0 := by
  unfold holderDist₂
  apply le_antisymm
  · by_cases h : (holderQuotientSet₂ X X).Nonempty
    · apply csSup_le h
      rintro q ⟨s, t, _, _, _, rfl⟩
      simp
    · simp [Set.not_nonempty_iff_eq_empty.mp h, sSup_empty]
  · exact holderDist₂_nonneg X X

/-- d(X, X) = 0. -/
@[simp] lemma roughPathDist_self (X : RoughPathOn V γ a b) :
    roughPathDist X X = 0 := by
  simp [roughPathDist]

/-! ### Separation (d = 0 implies equality)

This is the hardest metric axiom. If `d(X, cY) = 0` then both
`d₁ = 0` and `d₂ = 0`, which means `X₁(s,t) = X₂(s,t)` and
`𝕏₁(s,t) = 𝕏₂(s,t)` for all `s < t`. For `s = t`, both vanish
by the diagonal conditions. This gives pointwise equality, hence
structural equality (possibly via `ext`). -/

/-- If `d₁ = 0` then the level-1 paths agree pointwise. -/
lemma eq_x_of_holderDist₁_zero (X cY : RoughPathOn V γ a b)
    (_hγ : 0 < γ)
    (h : holderDist₁ X cY = 0) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b → X.x s t = cY.x s t := by
  intro s t has hst htb
  rcases hst.eq_or_lt with rfl | hst'
  · rw [X.x_diag s has htb, cY.x_diag s has htb]
  · have := holderDist₁_controls X cY has hst' htb
    rw [h, zero_mul] at this
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm this (norm_nonneg _)))


/-- If `d₂ = 0` then the level-2 areas agree pointwise. -/
lemma eq_area_of_holderDist₂_zero (X cY : RoughPathOn V γ a b)
    (_hγ : 0 < γ)
    (h : holderDist₂ X cY = 0) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b → X.area s t = cY.area s t := by
  intro s t has hst htb
  rcases hst.eq_or_lt with rfl | hst'
  · rw [X.area_diag s has htb, cY.area_diag s has htb]
  · have := holderDist₂_controls X cY has hst' htb
    rw [h, zero_mul] at this
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm this (norm_nonneg _)))

/-- Extensionality: two rough paths with the same `x` and `area` are equal.
This requires `RoughPathOn` to be a structure with no proof-relevant fields
beyond `x` and `area`. -/
@[ext] theorem RoughPathOn.ext (X cY : RoughPathOn V γ a b)
    (hx : X.x = cY.x)
    (ha : X.area = cY.area) :
    X = cY := by
  cases X; cases cY
  simp only [mk.injEq] at *
  exact ⟨hx, ha⟩


/-! ### Bridge: d controls pointwise + d recoverable from pointwise

These are the lemmas that Stage 4's Itô–Lyons continuity theorem uses. -/

/-- The combined distance controls both levels simultaneously. -/
lemma roughPathDist_controls₁ (X cY : RoughPathOn V γ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s < t) (htb : t ≤ b) :
    ‖X.x s t - cY.x s t‖ ≤ roughPathDist X cY * |t - s| ^ γ := by
  calc ‖X.x s t - cY.x s t‖
      ≤ holderDist₁ X cY * |t - s| ^ γ := holderDist₁_controls X cY has hst htb
    _ ≤ roughPathDist X cY * |t - s| ^ γ := by
        gcongr
        exact le_add_of_nonneg_right (rpow_nonneg (holderDist₂_nonneg X cY) _)


/-- The combined distance controls the level-2 area differences. -/
lemma roughPathDist_controls₂ (X cY : RoughPathOn V γ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s < t) (htb : t ≤ b) :
    ‖X.area s t - cY.area s t‖ ≤ roughPathDist X cY ^ 2 * |t - s| ^ (2 * γ) := by
  have hd₂_nn := holderDist₂_nonneg X cY
  have key : holderDist₂ X cY ≤ roughPathDist X cY ^ 2 := by
    have hsqrt_le : Real.sqrt (holderDist₂ X cY) ≤ roughPathDist X cY := by
      rw [Real.sqrt_eq_rpow]
      exact le_add_of_nonneg_left (holderDist₁_nonneg X cY)
    calc holderDist₂ X cY
        = Real.sqrt (holderDist₂ X cY) ^ 2 := (Real.sq_sqrt hd₂_nn).symm
      _ ≤ roughPathDist X cY ^ 2 :=
          sq_le_sq' (by linarith [Real.sqrt_nonneg (holderDist₂ X cY)]) hsqrt_le
  calc ‖X.area s t - cY.area s t‖
      ≤ holderDist₂ X cY * |t - s| ^ (2 * γ) := holderDist₂_controls X cY has hst htb
    _ ≤ roughPathDist X cY ^ 2 * |t - s| ^ (2 * γ) :=
        mul_le_mul_of_nonneg_right key (rpow_nonneg (abs_nonneg _) _)

end StochCalc
