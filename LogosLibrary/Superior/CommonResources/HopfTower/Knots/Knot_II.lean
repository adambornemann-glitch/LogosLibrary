/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Knots/Knot_II.lean
-/
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Defs
/-!
=====================================================================
## Part II: KNOT II — The Complex-Quaternionic Binding
=====================================================================

The embedding  S³ ↪ S⁷:

    (a, b, c, d)  ↦  (⟨a, b, 0, 0⟩, ⟨c, d, 0, 0⟩)

Two complex numbers, each promoted to a quaternion with zero
j and k parts.

Under this embedding:

    quatHopf₀(α, β) = (a²+b²) - (c²+d²) = hopfMap₃
    2·Re(quatHopfQ) = 2(ac+bd)            = hopfMap₁
    2·ImI(quatHopfQ) = 2(bc-ad)           = hopfMap₂
    ImJ(quatHopfQ) = 0                     (transverse)
    ImK(quatHopfQ) = 0                     (transverse)

This is the knot from HopfKnot.lean.  We reproduce the key
results with slightly streamlined proofs.
=====================================================================
-/
namespace HopfTower.Knots
open HopfTower.Defs Real

section KnotII

/-- First component of embedding -/
def embedα (a b : ℝ) : ℍℝ := ⟨a, b, 0, 0⟩
/-- Second component of embedding -/
def embedβ (c d : ℝ) : ℍℝ := ⟨c, d, 0, 0⟩

theorem normSq_embedα (a b : ℝ) : normSq (embedα a b) = a ^ 2 + b ^ 2 := by
  unfold normSq embedα; ring

theorem normSq_embedβ (c d : ℝ) : normSq (embedβ c d) = c ^ 2 + d ^ 2 := by
  unfold normSq embedβ; ring

/-- Sphere preservation: S³ ↪ S⁷ -/
theorem knotII_sphere (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    normSq (embedα a b) + normSq (embedβ c d) = 1 := by
  rw [normSq_embedα, normSq_embedβ]; linarith

/-- Explicit computation of α · β̄ -/
theorem quatHopfQ_embedded (a b c d : ℝ) :
    quatHopfQ (embedα a b) (embedβ c d) =
    (⟨a * c + b * d, b * c - a * d, 0, 0⟩ : ℍℝ) := by
  unfold quatHopfQ embedα embedβ qConj
  ext <;> simp; ring

/-- **THE COMPLEX-QUATERNIONIC BINDING** -/
theorem knotII_binding (a b c d : ℝ) :
    let α := embedα a b
    let β := embedβ c d
    let qH := quatHopfQ α β
    hopfMap₁ a b c d = 2 * qH.re
    ∧ hopfMap₂ a b c d = 2 * qH.imI
    ∧ hopfMap₃ a b c d = quatHopf₀ α β
    ∧ qH.imJ = 0
    ∧ qH.imK = 0 := by
  simp only
  rw [quatHopfQ_embedded]
  unfold quatHopf₀; rw [normSq_embedα, normSq_embedβ]
  refine ⟨?_, ?_, ?_, rfl, rfl⟩ <;>
  ring_nf
  unfold hopfMap₁ ; ring
  unfold hopfMap₂ ; ring
  unfold hopfMap₃ ; ring

/-- Fiber identity: fiberRotation = right multiply by s1Embed -/
theorem knotII_fiber (a b c d θ : ℝ) :
    let r := fiberRotation a b c d θ
    embedα r.1 r.2.1 = embedα a b * s1Embed θ ∧
    embedβ r.2.2.1 r.2.2.2 = embedβ c d * s1Embed θ := by
  refine ⟨?_, ?_⟩
  · unfold fiberRotation embedα s1Embed
    ext <;> simp only [QuaternionAlgebra.mk_mul_mk, neg_mul, one_mul, mul_zero, add_zero, mul_neg,
      mul_one, neg_zero, neg_neg, sub_zero, zero_mul, sub_self]; rfl
  · unfold fiberRotation embedβ s1Embed
    ext <;> simp only [QuaternionAlgebra.mk_mul_mk, neg_mul, one_mul, mul_zero, add_zero, mul_neg,
      mul_one, neg_zero, neg_neg, sub_zero, zero_mul, sub_self]; rfl

end KnotII

end HopfTower.Knots
