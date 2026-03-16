/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_2/Algebra/GroupLike.lean
-/
import LogosLibrary.StochasticCalculus.Stage_2.Algebra.TruncTensor2
/-!
# Group-Like Elements G⁽²⁾(V)

## Overview

An element `(1, x, 𝕏)` of the truncated tensor algebra `T⁽²⁾(V)` is
**group-like** if its level-2 component has symmetric part equal to `½(x ⊗ x)`:

    Sym(𝕏) = ½ · (x ⊗ₜ x)

Equivalently, `𝕏` decomposes as

    𝕏 = ½(x ⊗ x) + A,    A ∈ Λ²(V)

where `A = Anti(𝕏)` is the **Lévy area** — the antisymmetric (genuinely free)
part of the second-order data. The symmetric part is completely determined by
the level-1 data `x`, so the free parameters of a group-like element are
`(x, A) ∈ V × Λ²(V)`.

The group-like elements form a group under truncated multiplication. In the
`(x, 𝕏)` coordinates, the group law is:

    (x, 𝕏) · (y, 𝕐) = (x + y,  𝕏 + x ⊗ y + 𝕐)

which is the multiplication law of the **free step-2 nilpotent group** — a
generalization of the Heisenberg group. In the `(x, A)` coordinates:

    (x, A) · (y, B) = (x + y,  A + B + ½(x ⊗ y - y ⊗ x))

where the correction `½(x ⊗ y - y ⊗ x) = Anti(x ⊗ y)` is the infinitesimal
area swept by the concatenation.

## Key results

* `GroupLike₂.mul` — the group law, verified to preserve the group-like constraint
* `GroupLike₂.instGroup` — full group instance
* `GroupLike₂.toTrunc_mul` — coercion is a multiplicative homomorphism
* `GroupLike₂.area` — extraction of the Lévy area `A = Anti(𝕏)`
* `GroupLike₂.𝕏_eq` — reconstruction: `𝕏 = ½(x ⊗ x) + area`
* `GroupLike₂.mul_area` — area of a product: `A_{gh} = A_g + A_h + Anti(x ⊗ y)`

## Design

We represent `GroupLike₂` as a structure with fields `(x, 𝕏)` and a proof of
the symmetric constraint, *not* as `(x, A)` with reconstruction. The reason:
Chen's identity and the rough path structure are stated in terms of `𝕏`, not `A`.
The area is a derived quantity available via `GroupLike₂.area`.

The coercion `toTrunc : GroupLike₂ V → TruncTensor₂ V` inserts `a₀ = 1` and
allows us to reuse all the algebra from `TruncTensor2.lean` (associativity,
inverse formula, etc.) without reproving it.

## References

* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Chapter 2
* Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Ch. 7
-/

open NormedTensorSquare StochCalc.TruncTensor₂

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]

namespace StochCalc

/-! ## The type -/

/-- A **group-like element** of `T⁽²⁾(V)` at level 2.

An element `(1, x, 𝕏)` is group-like if `Sym(𝕏) = ½(x ⊗ₜ x)`.
This means the symmetric part of the area is determined by the path increment,
and only the antisymmetric part (the Lévy area) is free data. -/
structure GroupLike₂ (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedTensorSquare V] where
  /-- The level-1 component: the path increment `X_{s,t} ∈ V`. -/
  x : V
  /-- The level-2 component: the "area" `𝕏_{s,t} ∈ V ⊗ V`. -/
  𝕏 : T₂ V
  /-- The group-like constraint: `Sym(𝕏) = ½(x ⊗ x)`. -/
  sym_eq : sym 𝕏 = (2⁻¹ : ℝ) • (x ⊗ₜ x)

namespace GroupLike₂

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]

/-! ## Extensionality -/

@[ext] theorem ext {g h : GroupLike₂ V}
    (hx : g.x = h.x) (h𝕏 : g.𝕏 = h.𝕏) : g = h := by
  cases g; cases h; simp_all

/-! ## Coercion to T⁽²⁾(V)

The embedding `(x, 𝕏) ↦ (1, x, 𝕏)`. This allows us to reuse all the
algebra (associativity, inverse, norm estimates) from `TruncTensor2.lean`. -/

/-- Embed a group-like element into the truncated tensor algebra. -/
def toTrunc (g : GroupLike₂ V) : TruncTensor₂ V :=
  ⟨1, g.x, g.𝕏⟩

@[simp] theorem toTrunc_a₀ (g : GroupLike₂ V) : (toTrunc g).a₀ = 1 := rfl
@[simp] theorem toTrunc_a₁ (g : GroupLike₂ V) : (toTrunc g).a₁ = g.x := rfl
@[simp] theorem toTrunc_a₂ (g : GroupLike₂ V) : (toTrunc g).a₂ = g.𝕏 := rfl

/-- The coercion is injective. -/
theorem toTrunc_injective : Function.Injective (toTrunc (V := V)) := by
  intro g h hgh
  ext
  · exact congr_arg TruncTensor₂.a₁ hgh
  · exact congr_arg TruncTensor₂.a₂ hgh

/-! ## The Lévy area

The antisymmetric part of `𝕏` — the genuinely free data of a group-like element.
This is what physicists call the "signed area" and what probabilists call
"Lévy's stochastic area" in the context of Brownian motion. -/

/-- The **Lévy area**: `A = Anti(𝕏)`, the antisymmetric part of the level-2 data. -/
def area (g : GroupLike₂ V) : T₂ V := anti g.𝕏

/-- The symmetric part of `𝕏` is `½(x ⊗ x)` — just restating the constraint. -/
theorem sym_𝕏 (g : GroupLike₂ V) : sym g.𝕏 = (2⁻¹ : ℝ) • (g.x ⊗ₜ g.x) :=
  g.sym_eq

/-- **Reconstruction**: `𝕏 = ½(x ⊗ x) + area`. -/
theorem 𝕏_eq (g : GroupLike₂ V) :
    g.𝕏 = (2⁻¹ : ℝ) • (g.x ⊗ₜ g.x) + area g := by
  rw [area, ← g.sym_eq, sym_add_anti]

/-- A group-like element is determined by `(x, area)`. -/
theorem ext_area {g h : GroupLike₂ V}
    (hx : g.x = h.x) (hA : area g = area h) : g = h := by
  ext
  · exact hx
  · rw [g.𝕏_eq, h.𝕏_eq, hx, hA]

/-! ## The identity element -/

/-- The identity: `e = (0, 0)`.

The constraint `Sym(0) = ½(0 ⊗ 0)` is trivially satisfied since both sides are 0. -/
def e : GroupLike₂ V where
  x := 0
  𝕏 := 0
  sym_eq := by simp [sym, smul_zero]

@[simp] theorem e_x : (e : GroupLike₂ V).x = 0 := rfl
@[simp] theorem e_𝕏 : (e : GroupLike₂ V).𝕏 = 0 := rfl
@[simp] theorem e_area : area (e : GroupLike₂ V) = 0 := by simp [area, anti, smul_zero]

/-- The identity embeds to the unit of `T⁽²⁾(V)`. -/
theorem toTrunc_e : toTrunc (e : GroupLike₂ V) = TruncTensor₂.one := by
  ext <;> simp [toTrunc, TruncTensor₂.one]

/-! ## The group multiplication

The group law comes from truncated multiplication in `T⁽²⁾(V)`:

    (x, 𝕏) · (y, 𝕐) = (x + y,  𝕏 + x ⊗ₜ y + 𝕐)

The key obligation is showing the result is still group-like. -/

/-- **Auxiliary**: the product of two group-like elements satisfies the constraint.

We need: `Sym(𝕏 + x ⊗ y + 𝕐) = ½((x + y) ⊗ (x + y))`.

Proof sketch:
  LHS = Sym(𝕏) + Sym(x ⊗ y) + Sym(𝕐)
      = ½(x ⊗ x) + ½(x ⊗ y + y ⊗ x) + ½(y ⊗ y)

  RHS = ½((x + y) ⊗ (x + y))
      = ½(x ⊗ x + x ⊗ y + y ⊗ x + y ⊗ y)

These are equal by bilinearity. -/
private theorem mul_sym_eq (g h : GroupLike₂ V) :
    sym (g.𝕏 + (g.x ⊗ₜ h.x) + h.𝕏) =
      (2⁻¹ : ℝ) • ((g.x + h.x) ⊗ₜ (g.x + h.x)) := by
  -- Expand the RHS using bilinearity
  rw [tprod_add_left, tprod_add_right, tprod_add_right]
  -- RHS = ½(x⊗x + x⊗y + y⊗x + y⊗y)
  -- Expand the LHS using linearity of Sym
  -- sym distributes over addition (it's a linear map: ½(· + τ(·)))
  have sym_add : ∀ a b : T₂ V, sym (a + b) = sym a + sym b := by
    intro a b; simp [sym, smul_add, map_add]; abel
  rw [sym_add, sym_add, g.sym_eq, h.sym_eq, sym_tprod]
  -- LHS = ½(x⊗x) + ½(x⊗y + y⊗x) + ½(y⊗y)
  -- RHS = ½(x⊗x + x⊗y + y⊗x + y⊗y)
  simp only [smul_add]
  abel

/-- **Group multiplication**: `(x, 𝕏) · (y, 𝕐) = (x + y, 𝕏 + x ⊗ y + 𝕐)`. -/
def mul (g h : GroupLike₂ V) : GroupLike₂ V where
  x := g.x + h.x
  𝕏 := g.𝕏 + (g.x ⊗ₜ h.x) + h.𝕏
  sym_eq := mul_sym_eq g h

@[simp] theorem mul_x (g h : GroupLike₂ V) :
    (mul g h).x = g.x + h.x := rfl

@[simp] theorem mul_𝕏 (g h : GroupLike₂ V) :
    (mul g h).𝕏 = g.𝕏 + (g.x ⊗ₜ h.x) + h.𝕏 := rfl

/-- The coercion is a multiplicative homomorphism:
`toTrunc(g · h) = toTrunc(g) ⊗ₜₘ toTrunc(h)`. -/
theorem toTrunc_mul (g h : GroupLike₂ V) :
    toTrunc (mul g h) = TruncTensor₂.tmul (toTrunc g) (toTrunc h) := by
  apply TruncTensor₂.ext
  · simp
  · simp; abel
  · simp; abel

/-! ## The inverse

    (x, 𝕏)⁻¹ = (-x,  x ⊗ x - 𝕏)

We verify the group-like constraint for the inverse. -/

/-- **Auxiliary**: the inverse satisfies the constraint.

Need: `Sym(x ⊗ x - 𝕏) = ½((-x) ⊗ (-x)) = ½(x ⊗ x)`.

Proof: `Sym(x ⊗ x - 𝕏) = Sym(x ⊗ x) - Sym(𝕏) = (x ⊗ x) - ½(x ⊗ x) = ½(x ⊗ x)`.
And `(-x) ⊗ (-x) = x ⊗ x` by bilinearity. -/
private theorem inv_sym_eq (g : GroupLike₂ V) :
    sym ((g.x ⊗ₜ g.x) - g.𝕏) =
      (2⁻¹ : ℝ) • ((-g.x) ⊗ₜ (-g.x)) := by
  have h_neg : (-g.x) ⊗ₜ (-g.x) = g.x ⊗ₜ g.x := by
    rw [show -g.x = (-1 : ℝ) • g.x from by simp,
        tprod_smul_left, tprod_smul_right, smul_smul]
    simp
  have h_sub : sym ((g.x ⊗ₜ g.x) - g.𝕏) = sym (g.x ⊗ₜ g.x) - sym g.𝕏 := by
    simp only [sym, map_sub]; abel_nf
    module
  rw [h_neg, h_sub, sym_tprod_self, g.sym_eq, sub_eq_iff_eq_add, ← add_smul,
      show (2⁻¹ : ℝ) + 2⁻¹ = 1 from by norm_num, one_smul]


/-- **Group inverse**: `(x, 𝕏)⁻¹ = (-x, x ⊗ x - 𝕏)`. -/
def inv (g : GroupLike₂ V) : GroupLike₂ V where
  x := -g.x
  𝕏 := (g.x ⊗ₜ g.x) - g.𝕏
  sym_eq := inv_sym_eq g

@[simp] theorem inv_x (g : GroupLike₂ V) : (inv g).x = -g.x := rfl
@[simp] theorem inv_𝕏 (g : GroupLike₂ V) :
    (inv g).𝕏 = (g.x ⊗ₜ g.x) - g.𝕏 := rfl

/-- The coercion sends `inv` to `tinv`:
`toTrunc(g⁻¹) = tinv(toTrunc(g))`. -/
theorem toTrunc_inv (g : GroupLike₂ V) :
    toTrunc (inv g) = TruncTensor₂.tinv (toTrunc g) := by
  ext <;> simp [toTrunc, TruncTensor₂.tinv, inv]

/-! ## Group axioms

All proved by reducing to `TruncTensor₂` via `toTrunc_injective` and using
the already-proved algebra from `TruncTensor2.lean`. -/

/-- Associativity: `(g · h) · k = g · (h · k)`. -/
theorem mul_assoc (g h k : GroupLike₂ V) :
    mul (mul g h) k = mul g (mul h k) := by
  apply toTrunc_injective
  rw [toTrunc_mul, toTrunc_mul, toTrunc_mul, toTrunc_mul, TruncTensor₂.tmul_assoc]

/-- Left unit: `e · g = g`. -/
theorem e_mul (g : GroupLike₂ V) : mul e g = g := by
  apply toTrunc_injective
  rw [toTrunc_mul, toTrunc_e, TruncTensor₂.one_tmul]

/-- Right unit: `g · e = g`. -/
theorem mul_e (g : GroupLike₂ V) : mul g e = g := by
  apply toTrunc_injective
  rw [toTrunc_mul, toTrunc_e, TruncTensor₂.tmul_one]

/-- Left inverse: `g⁻¹ · g = e`. -/
theorem inv_mul (g : GroupLike₂ V) : mul (inv g) g = e := by
  apply toTrunc_injective
  rw [toTrunc_mul, toTrunc_inv, toTrunc_e,
      TruncTensor₂.tinv_tmul (toTrunc_a₀ g)]

/-- Right inverse: `g · g⁻¹ = e`. -/
theorem mul_inv (g : GroupLike₂ V) : mul g (inv g) = e := by
  apply toTrunc_injective
  rw [toTrunc_mul, toTrunc_inv, toTrunc_e,
      TruncTensor₂.tmul_tinv (toTrunc_a₀ g)]

/-- The inverse is an involution: `(g⁻¹)⁻¹ = g`. -/
theorem inv_inv (g : GroupLike₂ V) : inv (inv g) = g := by
  apply toTrunc_injective
  rw [toTrunc_inv, toTrunc_inv,
      TruncTensor₂.tinv_tinv (toTrunc_a₀ g)]

/-- Full group instance. -/
instance instGroup : Group (GroupLike₂ V) where
  mul := mul
  mul_assoc := mul_assoc
  one := e
  one_mul := e_mul
  mul_one := mul_e
  inv := inv
  inv_mul_cancel := inv_mul

/-! ## Simp lemmas for the group instance

Lean's `Group` API uses `*`, `1`, `⁻¹`. We connect these to our named operations. -/

@[simp] theorem group_mul_def (g h : GroupLike₂ V) : g * h = mul g h := rfl
@[simp] theorem group_one_def : (1 : GroupLike₂ V) = e := rfl
@[simp] theorem group_inv_def (g : GroupLike₂ V) : g⁻¹ = inv g := rfl

@[simp] theorem mul_x' (g h : GroupLike₂ V) : (g * h).x = g.x + h.x := rfl
@[simp] theorem mul_𝕏' (g h : GroupLike₂ V) :
    (g * h).𝕏 = g.𝕏 + (g.x ⊗ₜ h.x) + h.𝕏 := rfl
@[simp] theorem one_x : (1 : GroupLike₂ V).x = 0 := rfl
@[simp] theorem one_𝕏 : (1 : GroupLike₂ V).𝕏 = 0 := rfl
@[simp] theorem inv_x' (g : GroupLike₂ V) : g⁻¹.x = -g.x := rfl
@[simp] theorem inv_𝕏' (g : GroupLike₂ V) :
    g⁻¹.𝕏 = (g.x ⊗ₜ g.x) - g.𝕏 := rfl

/-! ## The Lévy area under group operations

These are the formulas that connect the group structure to the antisymmetric
geometry. They are used in `HomoNorm.lean` and `RoughPath/Defs.lean`. -/

/-- Area of a product: `A_{gh} = A_g + A_h + Anti(x_g ⊗ x_h)`.

The cross term `Anti(x ⊗ y) = ½(x ⊗ y - y ⊗ x)` is the infinitesimal
signed area swept by concatenating two increments. -/
theorem mul_area (g h : GroupLike₂ V) :
    area (g * h) = area g + anti (g.x ⊗ₜ h.x) + area h := by
  simp only [area, group_mul_def, mul_𝕏]
  -- anti(𝕏 + x⊗y + 𝕐) = anti(𝕏) + anti(x⊗y) + anti(𝕐)
  -- by linearity of anti
  simp only [anti]
  simp only [map_add, smul_add, smul_sub]
  abel

/-- Area of the identity is zero. -/
theorem area_e : area (1 : GroupLike₂ V) = 0 := by
  simp [area, anti, smul_zero]

/-- Area of an inverse: `A_{g⁻¹} = -A_g`.

Proof: `Anti(x ⊗ x - 𝕏) = Anti(x ⊗ x) - Anti(𝕏) = 0 - A = -A`. -/
theorem inv_area (g : GroupLike₂ V) :
    area g⁻¹ = -area g := by
  simp only [area, group_inv_def, inv_𝕏]
  simp only [anti]
  simp only [map_sub, smul_sub, swap_tprod]
  abel

/-! ## Construction helpers

Convenience constructors for building group-like elements from various inputs. -/

/-- Construct a group-like element from `(x, A)` where `A` is antisymmetric.

    `𝕏 := ½(x ⊗ x) + A`

The constraint `Sym(𝕏) = ½(x ⊗ x)` holds because `Sym(A) = 0` for
antisymmetric `A`. -/
def ofArea (x : V) (A : T₂ V) (hA : swap A = -A) : GroupLike₂ V where
  x := x
  𝕏 := (2⁻¹ : ℝ) • (x ⊗ₜ x) + A
  sym_eq := by
    have sym_add : ∀ a b : T₂ V, sym (a + b) = sym a + sym b := by
      intro a b; simp [sym, smul_add, map_add]; abel
    have h1 : sym ((2⁻¹ : ℝ) • (x ⊗ₜ x)) = (2⁻¹ : ℝ) • (x ⊗ₜ x) := by
      simp only [sym, map_smul, swap_tprod]; module
    have h2 : sym A = 0 := by
      simp only [sym, hA, add_neg_cancel, smul_zero]
    rw [sym_add, h1, h2, add_zero]

/-- Construct a group-like element with zero area: `𝕏 = ½(x ⊗ x)`.
This is the "symmetric" or "geometric" lift of a pure increment. -/
def ofSym (x : V) : GroupLike₂ V where
  x := x
  𝕏 := (2⁻¹ : ℝ) • (x ⊗ₜ x)
  sym_eq := by
    simp [sym, map_smul, swap_tprod, ← two_smul ℝ, smul_smul]

@[simp] theorem ofSym_x (x : V) : (ofSym x).x = x := rfl
@[simp] theorem ofSym_𝕏 (x : V) : (ofSym x).𝕏 = (2⁻¹ : ℝ) • (x ⊗ₜ x) := rfl

/-- The symmetric lift has zero area. -/
theorem ofSym_area (x : V) : area (ofSym x) = 0 := by
  simp [area, anti, ofSym, map_smul, swap_tprod, sub_self, smul_zero]

/-! ## Norm-related estimates

Basic norm bounds that `HomoNorm.lean` will build on. These use the
`normT` of `TruncTensor₂` as an intermediate. -/

/-- The norm of `x` is controlled by the `TruncTensor₂` norm. -/
theorem norm_x_le_normT (g : GroupLike₂ V) :
    ‖g.x‖ ≤ normT (toTrunc g) :=
    /-Function expected at
  normT
but this term has type
  ?m.9 -/
  norm_a₁_le (toTrunc g)

/-- The norm of `𝕏` is controlled by the `TruncTensor₂` norm. -/
theorem norm_𝕏_le_normT (g : GroupLike₂ V) :
    ‖g.𝕏‖ ≤ normT (toTrunc g) :=
  norm_a₂_le (toTrunc g)

/-- The norm of the area is controlled by `‖𝕏‖`. -/
theorem norm_area_le (g : GroupLike₂ V) :
    ‖area g‖ ≤ ‖g.𝕏‖ :=
  norm_anti_le g.𝕏

/-- Cross-norm bound on the area of a product: the new area contributed by
concatenation is bounded by `‖x‖ · ‖y‖`. -/
theorem norm_anti_tprod_le (g h : GroupLike₂ V) :
    ‖anti (g.x ⊗ₜ h.x)‖ ≤ ‖g.x‖ * ‖h.x‖ :=
  le_trans (norm_anti_le _) (norm_tprod_le g.x h.x)

/-! ## Chen's identity in components

These are the identities that `RoughPath/Defs.lean` uses. If `𝐗(s,t) = g`
and `𝐗(s,u) = g₁`, `𝐗(u,t) = g₂` with `g = g₁ · g₂` (Chen's identity),
then: -/

/-- **Level-1 Chen**: `X_{s,t} = X_{s,u} + X_{u,t}`. -/
theorem chen₁ (g₁ g₂ : GroupLike₂ V) :
    (g₁ * g₂).x = g₁.x + g₂.x := by simp

/-- **Level-2 Chen**: `𝕏_{s,t} = 𝕏_{s,u} + X_{s,u} ⊗ X_{u,t} + 𝕏_{u,t}`.

This is the *content* of rough path theory at level 2: the area does not split
additively — it has a correction from the tensor product of increments. -/
theorem chen₂ (g₁ g₂ : GroupLike₂ V) :
    (g₁ * g₂).𝕏 = g₁.𝕏 + (g₁.x ⊗ₜ g₂.x) + g₂.𝕏 := by simp

/-- **Area Chen**: the area correction is antisymmetric. -/
theorem chen_area (g₁ g₂ : GroupLike₂ V) :
    area (g₁ * g₂) = area g₁ + anti (g₁.x ⊗ₜ g₂.x) + area g₂ :=
  mul_area g₁ g₂

/-! ## The "difference" element `g⁻¹ · h`

In rough path theory, `d(𝐗, 𝐘)` involves `𝐗(s,t)⁻¹ · 𝐘(s,t)`.
We record the explicit formula for later use. -/

/-- Components of `g⁻¹ · h`. -/
theorem inv_mul_x (g h : GroupLike₂ V) :
    (g⁻¹ * h).x = h.x - g.x := by
  simp [sub_eq_add_neg, add_comm]

theorem inv_mul_𝕏 (g h : GroupLike₂ V) :
    (g⁻¹ * h).𝕏 = (g.x ⊗ₜ g.x) - g.𝕏 + ((-g.x) ⊗ₜ h.x) + h.𝕏 := by
  simp [mul, inv]

end GroupLike₂

end StochCalc
