/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Knots/Knot_I.lean
-/
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Defs
/-!
=====================================================================
## Part I: KNOT I — The Real-Complex Binding
=====================================================================

The embedding  S¹ ↪ S³:

    (x, y)  ↦  (x, 0, y, 0)

This embeds a pair of REAL numbers as a pair of COMPLEX numbers
(each with zero imaginary part).  In the quaternion coordinates
(a, b, c, d) representing (z₁, z₂) = (a+bi, c+di):

    z₁ = x + 0·i = x     (pure real)
    z₂ = y + 0·i = y     (pure real)

Under this embedding:

    hopfMap₁(x, 0, y, 0) = 2(x·y + 0·0) = 2xy     = realHopf.2
    hopfMap₂(x, 0, y, 0) = 2(0·y - x·0) = 0        (transverse)
    hopfMap₃(x, 0, y, 0) = x² + 0 - y² - 0 = x²-y² = realHopf.1

The S¹ image sits inside S² as the equator where hopfMap₂ = 0.

The S⁰ fiber {±1} is the S¹ fiber restricted to {θ=0, θ=π}.
=====================================================================
-/
namespace HopfTower.Knots
open HopfTower.Defs Real

section KnotI

/-- **EMBEDDING PRESERVES SPHERE**: S¹ ↪ S³

    If x² + y² = 1 then x² + 0² + y² + 0² = 1. -/
theorem knotI_sphere (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    x ^ 2 + (0 : ℝ) ^ 2 + y ^ 2 + (0 : ℝ) ^ 2 = 1 := by
  linarith

/-- **FIRST COMPONENT MATCH**:  hopfMap₃(x,0,y,0) = (realHopf).1 = x²-y² -/
theorem knotI_component₁ (x y : ℝ) :
    hopfMap₃ x 0 y 0 = (realHopf x y).1 := by
  unfold hopfMap₃ realHopf; ring

/-- **SECOND COMPONENT MATCH**: hopfMap₁(x,0,y,0) = (realHopf).2 = 2xy -/
theorem knotI_component₂ (x y : ℝ) :
    hopfMap₁ x 0 y 0 = (realHopf x y).2 := by
  unfold hopfMap₁ realHopf; ring

/-- **TRANSVERSE VANISHING**: hopfMap₂(x,0,y,0) = 0

    The S¹ image sits inside S² as the equator.
    The "missing" coordinate is the one that requires
    imaginary parts — which we zeroed out.  -/
theorem knotI_transverse (x y : ℝ) :
    hopfMap₂ x 0 y 0 = 0 := by
  unfold hopfMap₂; ring

/-- **THE REAL-COMPLEX BINDING THEOREM**

    The real Hopf map is the restriction of the complex Hopf map
    under the embedding (x,y) ↦ (x, 0, y, 0).

    The two components of realHopf(x,y) appear as hopfMap₃ and
    hopfMap₁, with hopfMap₂ = 0 (the equatorial constraint). -/
theorem knotI_binding (x y : ℝ) :
    (realHopf x y).1 = hopfMap₃ x 0 y 0
    ∧ (realHopf x y).2 = hopfMap₁ x 0 y 0
    ∧ hopfMap₂ x 0 y 0 = 0 := by
  exact ⟨(knotI_component₁ x y).symm,
         (knotI_component₂ x y).symm,
         knotI_transverse x y⟩

/-- **S⁰ FIBER AS S¹ RESTRICTION**

    The S⁰ fiber {±1} acts on (x,y) by negation: (x,y) ↦ (-x,-y).

    Under the embedding, this is fiberRotation at θ = π:
      fiberRotation(x, 0, y, 0, π) = (-x, 0, -y, 0)

    The discrete fiber S⁰ = {0, π} ⊂ S¹ = [0, 2π).
    The real fiber is a SUBGROUP of the complex fiber.  -/
theorem knotI_fiber_at_pi (x y : ℝ) :
    fiberRotation x 0 y 0 Real.pi = (-x, 0, -y, 0) := by
  unfold fiberRotation
  simp [cos_pi, sin_pi]

/-- The identity element θ = 0 preserves the point -/
theorem knotI_fiber_at_zero (x y : ℝ) :
    fiberRotation x 0 y 0 0 = (x, 0, y, 0) := by
  unfold fiberRotation
  simp [cos_zero, sin_zero]

/-- The S⁰ fiber is exactly the restriction of S¹ to {0, π}:
    both θ = 0 and θ = π map the embedded pair back to an
    embedded pair (one with real coordinates). -/
theorem knotI_fiber_closure_zero (x y : ℝ) :
    let r := fiberRotation x 0 y 0 0
    r.2.1 = 0 ∧ r.2.2.2 = 0 := by
  simp [fiberRotation, cos_zero, sin_zero]

theorem knotI_fiber_closure_pi (x y : ℝ) :
    let r := fiberRotation x 0 y 0 Real.pi
    r.2.1 = 0 ∧ r.2.2.2 = 0 := by
  simp [fiberRotation, cos_pi, sin_pi]

/-- **GENERIC FIBER ROTATION LEAVES THE REAL SUBSPACE**

    For general θ ∉ {0, π}, fiberRotation(x, 0, y, 0, θ) has
    nonzero b and d components — it escapes the real embedding.

    This is WHY the real fiber is S⁰ (discrete) inside S¹ (continuous):
    only two values of θ keep the pair real. -/
theorem knotI_fiber_generic (x : ℝ) (hx : x ≠ 0) (θ : ℝ) (hθ : sin θ ≠ 0) :
    (fiberRotation x 0 0 0 θ).2.1 ≠ 0 := by
  unfold fiberRotation; simp;
  exact Decidable.not_imp_iff_and_not.mp fun a => hθ (a hx)

/-- **NORM IDENTITY SPECIALIZATION**

    The complex Hopf norm identity:
      hopfMap₁² + hopfMap₂² + hopfMap₃² = (a²+b²+c²+d²)²

    Under the embedding (x,0,y,0):
      (2xy)² + 0² + (x²-y²)² = (x²+y²)²

    Which is (realHopf.2)² + (realHopf.1)² = (x²+y²)²:
    the real Hopf norm identity. -/
theorem knotI_norm_identity (x y : ℝ) :
    (realHopf x y).1 ^ 2 + (realHopf x y).2 ^ 2 = (x ^ 2 + y ^ 2) ^ 2 := by
  unfold realHopf; ring

/-- On S¹, the real Hopf lands on S¹ -/
theorem knotI_sphere_to_sphere (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    (realHopf x y).1 ^ 2 + (realHopf x y).2 ^ 2 = 1 := by
  rw [knotI_norm_identity, h]; ring

end KnotI

end HopfTower.Knots
