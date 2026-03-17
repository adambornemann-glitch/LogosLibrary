/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_3/Geometric/Defs.lean
-/
import LogosLibrary.StochasticCalculus.Stage_3.HolderMetric.Complete
/-!
# Geometric rough paths — Definitions

## Overview

A rough path `X = (X, 𝕏)` is **geometric** if its level-2 component
satisfies the symmetry condition

  `Sym(𝕏(s,t)) = ½ · X(s,t) ⊗ X(s,t)`

for all `s ≤ t` in `[a, b]`. Equivalently, `(1, X(s,t), 𝕏(s,t))`
lies in the free nilpotent Lie group `G⁽²⁾(V)` — the group-like
elements of the truncated tensor algebra `T⁽²⁾(V)`.

## Mathematical meaning

For a smooth path `x : [a,b] → V`, the iterated integral

  `𝕏(s,t) = ∫_s^t (x(u) − x(s)) ⊗ dx(u)`

automatically satisfies the geometric condition. This is because
integration by parts gives

  `𝕏(s,t) + τ(𝕏(s,t)) = X(s,t) ⊗ X(s,t)`

where `τ` is the swap. Taking the symmetric part:

  `Sym(𝕏(s,t)) = ½ (𝕏(s,t) + τ(𝕏(s,t))) = ½ X(s,t) ⊗ X(s,t)`

So geometric rough paths are precisely those that can be approximated
by smooth paths — they are the closure of smooth signatures in the
rough path topology.

## The Lévy area decomposition

Every rough path decomposes as

  `𝕏(s,t) = Sym(𝕏(s,t)) + Anti(𝕏(s,t))`

For a geometric rough path, `Sym(𝕏) = ½ X ⊗ X`, so:

  `𝕏(s,t) = ½ X(s,t) ⊗ X(s,t) + A(s,t)`

where `A(s,t) = Anti(𝕏(s,t))` is the **Lévy area** — the
antisymmetric part that encodes the genuinely "rough" information.

This decomposition is fundamental because:
1. The symmetric part is determined by the level-1 path
2. Only the Lévy area carries independent information
3. The Itô vs Stratonovich distinction is precisely a choice of Lévy area

## What this file provides

1. `IsGeometric` — predicate on `RoughPathOn`
2. `GeometricRoughPathOn` — bundled subtype
3. Lévy area decomposition: `𝕏 = ½ X ⊗ X + A`
4. Area norm bound from the geometric condition
5. Coercion to `RoughPathOn`

## What this does NOT provide (yet)

- Smooth paths are geometric (requires Young integral of smooth paths)
- Density of smooth geometric paths (requires approximation theory)
- The chain rule / Itô formula (requires Stage 4 + geometric structure)

## References

* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., §2.3, §9
* Lyons, T., *Differential equations driven by rough signals* (1998), §2
-/

open NormedTensorSquare Real Set

noncomputable section

namespace StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]
variable {γ a b : ℝ}

/-! ### The geometric condition -/

/-- A rough path is **geometric** if `Sym(𝕏(s,t)) = ½ X(s,t) ⊗ X(s,t)`
for all `(s, t)` in the domain.

This is the condition that the element `(1, X, 𝕏)` lies in the free
nilpotent Lie group `G⁽²⁾(V)`. -/
def IsGeometric (X : RoughPathOn V γ a b) : Prop :=
  ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    sym (X.area s t) = (2⁻¹ : ℝ) • (X.x s t ⊗ₜ X.x s t)

/-! ### Basic properties of geometric rough paths -/

/-- The geometric condition on the diagonal is automatic. -/
lemma isGeometric_diag (X : RoughPathOn V γ a b)
    (s : ℝ) (has : a ≤ s) (hsb : s ≤ b) :
    sym (X.area s s) = (2⁻¹ : ℝ) • (X.x s s ⊗ₜ X.x s s) := by
  rw [X.area_diag s has hsb, X.x_diag s has hsb]
  simp [sym, smul_zero, map_zero]

/-- For a geometric rough path, the area is determined by the level-1
path and the Lévy area:
  `𝕏(s,t) = ½ X(s,t) ⊗ X(s,t) + Anti(𝕏(s,t))` -/
lemma area_eq_of_isGeometric (X : RoughPathOn V γ a b) (hg : IsGeometric X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    X.area s t = (2⁻¹ : ℝ) • (X.x s t ⊗ₜ X.x s t) + anti (X.area s t) := by
  conv_lhs => rw [← sym_add_anti (X.area s t)]
  rw [hg s t has hst htb]

/-- Equivalent formulation: `𝕏 − ½ X ⊗ X` is antisymmetric. -/
lemma isGeometric_iff_anti (X : RoughPathOn V γ a b) :
    IsGeometric X ↔
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      X.area s t - (2⁻¹ : ℝ) • (X.x s t ⊗ₜ X.x s t) =
        anti (X.area s t) := by
  constructor
  · intro hg s t has hst htb
    have := area_eq_of_isGeometric X hg has hst htb
    rw [this] -- or: rw [this]; abel
    exact
      Eq.symm
        (eq_sub_of_add_eq'
          (congrArg (HAdd.hAdd (2⁻¹ • (NormedTensorSquare.tprod (X.x s t)) (X.x s t)))
            (congrArg anti (id (Eq.symm this)))))
  · intro h s t has hst htb
    have hanti := (h s t has hst htb).symm
    have hsym : sym (X.area s t) = X.area s t - anti (X.area s t) :=
      eq_sub_of_add_eq (sym_add_anti (X.area s t))
    rw [hsym, hanti, sub_sub_cancel]

/-- Equivalent formulation via the swap: `𝕏 + τ(𝕏) = X ⊗ X`.

This is often the most convenient form for computation.
It says: `𝕏(s,t) + 𝕏(s,t)ᵀ = X(s,t) ⊗ X(s,t)`. -/
lemma isGeometric_iff_swap (X : RoughPathOn V γ a b) :
    IsGeometric X ↔
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      X.area s t + swap (X.area s t) = X.x s t ⊗ₜ X.x s t := by
  constructor
  · intro hg s t has hst htb
    have hsym := hg s t has hst htb
    simp only [sym] at hsym
    have := smul_right_injective (T₂ V) (by norm_num : (2⁻¹ : ℝ) ≠ 0)
    exact this hsym
  · intro h s t has hst htb
    simp only [sym]
    rw [h s t has hst htb]

namespace RoughPathOn

/-! ### The Lévy area -/

/-- The **Lévy area** of a rough path: `A(s,t) = Anti(𝕏(s,t))`.

For a geometric rough path, this is the only part of the area that
is not determined by the level-1 path. -/
def levyArea (X : RoughPathOn V γ a b) (s t : ℝ) : T₂ V :=
  anti (X.area s t)

/-- The Lévy area is antisymmetric (by definition). -/
lemma levyArea_swap (X : RoughPathOn V γ a b) (s t : ℝ) :
    swap (X.levyArea s t) = -X.levyArea s t :=
  swap_anti _

/-- The Lévy area vanishes on the diagonal. -/
lemma levyArea_diag (X : RoughPathOn V γ a b)
    (s : ℝ) (has : a ≤ s) (hsb : s ≤ b) :
    X.levyArea s s = 0 := by
  simp [levyArea, X.area_diag s has hsb, anti, map_zero, smul_zero]

/-- The Lévy area satisfies a Hölder bound. -/
lemma levyArea_holder (X : RoughPathOn V γ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖X.levyArea s t‖ ≤ X.C₂ * |t - s| ^ (2 * γ) :=
  calc ‖X.levyArea s t‖
      = ‖anti (X.area s t)‖ := rfl
    _ ≤ ‖X.area s t‖ := norm_anti_le _
    _ ≤ X.C₂ * |t - s| ^ (2 * γ) := X.area_holder s t has hst htb

/-- For a geometric rough path, the full area is recovered from
the level-1 path and the Lévy area. -/
lemma area_eq_half_tprod_add_levyArea
    (X : RoughPathOn V γ a b) (hg : IsGeometric X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    X.area s t = (2⁻¹ : ℝ) • (X.x s t ⊗ₜ X.x s t) + X.levyArea s t :=
  area_eq_of_isGeometric X hg has hst htb


/-! ### Improved area bound for geometric rough paths

For a geometric rough path, the area satisfies a *better* bound:
  `‖𝕏(s,t)‖ ≤ ½ ‖X(s,t)‖² + ‖A(s,t)‖ ≤ ½ C₁² |t−s|^{2γ} + C_A |t−s|^{2γ}`

The symmetric part is controlled by the level-1 path (via cross-norm),
and the antisymmetric part has its own Hölder bound. -/
lemma area_bound_of_isGeometric (X : RoughPathOn V γ a b) (hg : IsGeometric X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖X.area s t‖ ≤
      (2⁻¹ : ℝ) * ‖X.x s t‖ ^ 2 + ‖X.levyArea s t‖ := by
  rw [area_eq_half_tprod_add_levyArea X hg has hst htb]
  calc ‖(2⁻¹ : ℝ) • ((tprod (X.x s t)) (X.x s t)) + X.levyArea s t‖
      ≤ ‖(2⁻¹ : ℝ) • ((tprod (X.x s t)) (X.x s t))‖ + ‖X.levyArea s t‖ :=
        norm_add_le _ _
    _ = 2⁻¹ * ‖(tprod (X.x s t)) (X.x s t)‖ + ‖X.levyArea s t‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ 2⁻¹ * (‖X.x s t‖ * ‖X.x s t‖) + ‖X.levyArea s t‖ := by
        gcongr; exact norm_tprod_le _ _
    _ = 2⁻¹ * ‖X.x s t‖ ^ 2 + ‖X.levyArea s t‖ := by
        rw [sq]

end RoughPathOn

/-! ### The bundled type -/

/-- A **geometric rough path** on `[a, b]`: a rough path satisfying
the geometric condition `Sym(𝕏) = ½ X ⊗ X`.

This is a subtype of `RoughPathOn`. The metric and completeness
are inherited (geometric is a closed condition — see `Closed.lean`). -/
structure GeometricRoughPathOn (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedTensorSquare V] (γ : ℝ) (a b : ℝ)
    extends RoughPathOn V γ a b where
  /-- The geometric condition. -/
  geometric : IsGeometric toRoughPathOn

namespace GeometricRoughPathOn

instance : Coe (GeometricRoughPathOn V γ a b) (RoughPathOn V γ a b) :=
  ⟨fun X => X.toRoughPathOn⟩

end GeometricRoughPathOn
/-- Coercion to `RoughPathOn`. -/
instance : Coe (GeometricRoughPathOn V γ a b) (RoughPathOn V γ a b) :=
  ⟨fun X => X.toRoughPathOn⟩

/-- Access the level-1 path. -/
def x (X : GeometricRoughPathOn V γ a b) : ℝ → ℝ → V := X.toRoughPathOn.x

/-- Access the area. -/
def area (X : GeometricRoughPathOn V γ a b) : ℝ → ℝ → T₂ V :=
  X.toRoughPathOn.area

/-- The area decomposition for geometric rough paths. -/
lemma area_decomp (X : GeometricRoughPathOn V γ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    X.area s t =
      (2⁻¹ : ℝ) • (X.x s t ⊗ₜ X.x s t) + X.levyArea s t :=
  RoughPathOn.area_eq_half_tprod_add_levyArea X.toRoughPathOn X.geometric has hst htb

/-- Extensionality for geometric rough paths: determined by the
underlying rough path. -/
@[ext] theorem ext (X cY : GeometricRoughPathOn V γ a b)
    (h : X.toRoughPathOn = cY.toRoughPathOn) : X = cY := by
  cases X; cases cY
  simp only [GeometricRoughPathOn.mk.injEq]
  exact h


/-! ### Consistency: geometric condition is compatible with Chen

If `X` is geometric and satisfies Chen₂, then the Lévy area
satisfies its own Chen-like identity. This is a consequence of
the shuffle relation. -/

/-- The Lévy area satisfies a modified Chen identity:
  `A(s,t) = A(s,u) + A(u,t) + Anti(X(s,u) ⊗ X(u,t))`

This follows from Chen₂ for the full area and the geometric condition.
The antisymmetric part of `X(s,u) ⊗ X(u,t)` is the "infinitesimal
area" swept out between the two increments. -/
lemma levyArea_chen
    (X : RoughPathOn V γ a b) (_hg : IsGeometric X)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    X.levyArea s t =
      X.levyArea s u + X.levyArea u t +
      anti ((tprod (X.x s u)) (X.x u t)) := by
  unfold RoughPathOn.levyArea
  rw [X.chen₂ s u t has hsu hut htb]
  simp only [anti, map_add, smul_add, smul_sub]
  abel

end StochCalc
