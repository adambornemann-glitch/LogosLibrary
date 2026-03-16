/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_2/Axioms/NormedTwnsorSquare.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.API
import LogosLibrary.StochasticCalculus.Stage_1.API
/-!
# Axioms/NormedTensorSquare.lean

Axiomatization of V ⊗ V equipped with a cross-norm.

## Why this exists

Mathlib provides the algebraic tensor product `TensorProduct ℝ V V`
but does not (as of 2026) equip it with the projective tensor norm
satisfying `‖v ⊗ w‖ ≤ ‖v‖ * ‖w‖`. This single inequality is
load-bearing for every estimate in rough path theory.

We axiomatize the minimal interface that the projective tensor product
would provide. When Mathlib gains the projective norm, this file
becomes a single `instance` declaration and everything above is unchanged.

## What we axiomatize

1. A normed space `T₂ V` representing V ⊗ V
2. A continuous bilinear map `tprod : V → V → T₂ V` with cross-norm
3. A swap involution `τ : T₂ V → T₂ V` that is isometric and
   satisfies `τ(v ⊗ w) = w ⊗ v`

## What we derive (not axiomatize)

- Symmetric projection Sym = (id + τ)/2
- Antisymmetric projection Anti = (id - τ)/2
- The decomposition x = Sym(x) + Anti(x)
- Norm bounds ‖Sym(x)‖ ≤ ‖x‖, ‖Anti(x)‖ ≤ ‖x‖
- Idempotence, orthogonality of projections
-/
class NormedTensorSquare (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] where
  /-- The carrier type representing V ⊗ V. -/
  T₂ : outParam Type*
  [instNACG : NormedAddCommGroup T₂]
  [instNS : NormedSpace ℝ T₂]
  [instComplete : CompleteSpace T₂]
  /-- The continuous bilinear tensor product map.
  We curry: `tprod v` is the continuous linear map `w ↦ v ⊗ w`. -/
  tprod : V →L[ℝ] V →L[ℝ] T₂
  /-- **Cross-norm inequality.** This is the axiom that does all the work. -/
  cross_norm : ∀ v w, ‖(tprod v) w‖ ≤ ‖v‖ * ‖w‖
  /-- The swap (transposition) map τ : T₂ → T₂. -/
  swap : T₂ →L[ℝ] T₂
  /-- τ(v ⊗ w) = w ⊗ v. -/
  swap_tprod : ∀ v w, swap ((tprod v) w) = (tprod w) v
  /-- τ is an involution: τ² = id. -/
  swap_involutive : Function.Involutive swap
  /-- τ is an isometry. -/
  swap_isometry : ∀ x, ‖swap x‖ = ‖x‖

attribute [reducible, instance] NormedTensorSquare.instNACG
    NormedTensorSquare.instNS

attribute [instance] NormedTensorSquare.instComplete

namespace NormedTensorSquare

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]

/- Notation: `v ⊗ₜ w` for the tensor product of two vectors. -/
scoped notation:70 v " ⊗ₜ " w:71 => (tprod v) w

/-- Cross-norm, notation form. -/
lemma norm_tprod_le (v w : V) : ‖v ⊗ₜ w‖ ≤ ‖v‖ * ‖w‖ :=
  cross_norm v w

/-- Zero on either side. -/
@[simp] lemma tprod_zero (v : V) : v ⊗ₜ (0 : V) = 0 :=
  (tprod v).map_zero

@[simp] lemma zero_tprod (w : V) : (0 : V) ⊗ₜ w = 0 := by
  simp [show (tprod (0 : V)) = 0 from tprod.map_zero]

/-- Symmetric projection: Sym(x) = (x + τ(x)) / 2. -/
noncomputable def sym (x : T₂ V) : T₂ V := (2⁻¹ : ℝ) • (x + swap x)

/-- Antisymmetric projection: Anti(x) = (x - τ(x)) / 2. -/
noncomputable def anti (x : T₂ V) : T₂ V := (2⁻¹ : ℝ) • (x - swap x)

/-- Fundamental decomposition: x = Sym(x) + Anti(x). -/
lemma sym_add_anti (x : T₂ V) : sym x + anti x = x := by
  simp only [sym, anti, ← smul_add]
  simp only [add_add_sub_cancel, smul_add]  -- 2⁻¹ • (2 • x) = x
  module

/-- Sym is τ-invariant. -/
lemma swap_sym (x : T₂ V) : swap (sym x) = sym x := by
  simp only [sym, map_smul, map_add, swap_involutive x, add_comm]

/-- Anti is τ-skew. -/
lemma swap_anti (x : T₂ V) : swap (anti x) = -anti x := by
  simp only [anti, map_smul, map_sub, swap_involutive x]
  rw [← neg_sub x (swap x), smul_neg]

/-- Sym is idempotent. -/
lemma sym_sym (x : T₂ V) : sym (sym x) = sym x := by
  rw [sym, swap_sym, ← two_smul ℝ (sym x), smul_smul]
  norm_num; exact MulAction.one_smul (sym x)

/-- Anti is idempotent. -/
lemma anti_anti (x : T₂ V) : anti (anti x) = anti x := by
  rw [anti, swap_anti, sub_neg_eq_add, ← two_smul ℝ (anti x), smul_smul]
  norm_num; exact MulAction.one_smul (anti x)

/-- Sym and Anti are orthogonal. -/
lemma sym_anti (x : T₂ V) : sym (anti x) = 0 := by
  rw [sym, swap_anti, add_neg_cancel, smul_zero]

lemma anti_sym (x : T₂ V) : anti (sym x) = 0 := by
  rw [anti, swap_sym, sub_self, smul_zero]


/-- Norm bound on Sym. -/
lemma norm_sym_le (x : T₂ V) : ‖sym x‖ ≤ ‖x‖ := by
  simp only [sym]
  calc ‖(2⁻¹ : ℝ) • (x + swap x)‖
      = 2⁻¹ * ‖x + swap x‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ 2⁻¹ * (‖x‖ + ‖swap x‖) := by gcongr; exact norm_add_le _ _
    _ = 2⁻¹ * (‖x‖ + ‖x‖) := by rw [swap_isometry]
    _ = ‖x‖ := by ring

/-- Norm bound on Anti — same proof. -/
lemma norm_anti_le (x : T₂ V) : ‖anti x‖ ≤ ‖x‖ := by
  simp only [anti]
  calc ‖(2⁻¹ : ℝ) • (x - swap x)‖
      = 2⁻¹ * ‖x - swap x‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ 2⁻¹ * (‖x‖ + ‖swap x‖) := by gcongr; exact norm_sub_le _ _
    _ = ‖x‖ := by rw [swap_isometry]; ring

/-- Sym(v ⊗ w) = (v ⊗ w + w ⊗ v) / 2. -/
lemma sym_tprod (v w : V) :
    sym (v ⊗ₜ w) = (2⁻¹ : ℝ) • (v ⊗ₜ w + w ⊗ₜ v) := by
  simp [sym, swap_tprod]

/-- Anti(v ⊗ w) = (v ⊗ w - w ⊗ v) / 2. -/
lemma anti_tprod (v w : V) :
    anti (v ⊗ₜ w) = (2⁻¹ : ℝ) • (v ⊗ₜ w - w ⊗ₜ v) := by
  simp [anti, swap_tprod]

/-- The symmetric part of v ⊗ v is just v ⊗ v (it's already symmetric). -/
@[simp] lemma sym_tprod_self (v : V) :
    sym (v ⊗ₜ v) = v ⊗ₜ v := by
  simp [sym, swap_tprod, ← two_smul ℝ]

/-- The antisymmetric part of v ⊗ v vanishes. -/
@[simp] lemma anti_tprod_self (v : V) :
    anti (v ⊗ₜ v) = 0 := by
  simp [anti, swap_tprod, sub_self, smul_zero]

/-- Anti is skew-commutative on pure tensors. This is the algebraic
heart of the Lévy area: Anti(v ⊗ w) = -Anti(w ⊗ v). -/
lemma anti_tprod_comm (v w : V) :
    anti (v ⊗ₜ w) = -anti (w ⊗ₜ v) := by
  simp only [anti_tprod, smul_sub, neg_sub]

/-- Sym is commutative on pure tensors. -/
lemma sym_tprod_comm (v w : V) :
    sym (v ⊗ₜ w) = sym (w ⊗ₜ v) := by
  simp only [sym_tprod, add_comm]

/-- Bilinearity: tprod distributes over addition on the left. -/
lemma tprod_add_left (u v w : V) :
    (u + v) ⊗ₜ w = u ⊗ₜ w + v ⊗ₜ w := by
  simp [show tprod (u + v) = tprod u + tprod v from tprod.map_add u v,
        ContinuousLinearMap.add_apply]

/-- Bilinearity: tprod distributes over addition on the right. -/
lemma tprod_add_right (v w₁ w₂ : V) :
    v ⊗ₜ (w₁ + w₂) = v ⊗ₜ w₁ + v ⊗ₜ w₂ :=
  (tprod v).map_add w₁ w₂

/-- Scalar multiplication on the left. -/
lemma tprod_smul_left (c : ℝ) (v w : V) :
    (c • v) ⊗ₜ w = c • (v ⊗ₜ w) := by
  simp [show tprod (c • v) = c • tprod v from tprod.map_smul c v,
        ContinuousLinearMap.smul_apply]

/-- Scalar multiplication on the right. -/
lemma tprod_smul_right (c : ℝ) (v w : V) :
    v ⊗ₜ (c • w) = c • (v ⊗ₜ w) :=
  (tprod v).map_smul c w

/-- Convenience: ‖v ⊗ v‖ ≤ ‖v‖² -/
lemma norm_tprod_self_le (v : V) : ‖v ⊗ₜ v‖ ≤ ‖v‖ ^ 2 := by
  rw [sq]; exact cross_norm v v

end NormedTensorSquare
