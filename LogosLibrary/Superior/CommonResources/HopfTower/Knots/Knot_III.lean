/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Knots/Knot_III.lean
-/
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Defs
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_II
/-!
=====================================================================
## Part III: KNOT III — The Composed Embedding  S¹ ↪ S⁷
=====================================================================

Composing the two embeddings:

    (x, y) ──Knot I──→ (x, 0, y, 0) ──Knot II──→ (⟨x,0,0,0⟩, ⟨y,0,0,0⟩)

A pair of REALS becomes a pair of REAL QUATERNIONS.

Under this composed embedding, the quaternionic Hopf map
directly produces the real Hopf map:

    quatHopf₀(⟨x,0,0,0⟩, ⟨y,0,0,0⟩) = x² - y²  = realHopf.1
    quatHopfQ(⟨x,0,0,0⟩, ⟨y,0,0,0⟩) = ⟨xy, 0, 0, 0⟩

So:  2·Re(quatHopfQ) = 2xy = realHopf.2

The quaternionic Hopf map, restricted maximally, IS the complex
squaring map z ↦ z².  Three levels of the tower in one theorem.
=====================================================================
-/
namespace HopfTower.Knots
open HopfTower.Defs Real

section KnotIII

/-- The composed embedding: x ↦ ⟨x, 0, 0, 0⟩ (a real quaternion) -/
def embedReal (x : ℝ) : ℍℝ := ⟨x, 0, 0, 0⟩

/-- The composition factorizes correctly:
    embedReal x = embedα x 0 = embedβ x 0 -/
theorem embed_compose_α (x : ℝ) : embedReal x = embedα x 0 := rfl
theorem embed_compose_β (y : ℝ) : embedReal y = embedβ y 0 := rfl

/-- Norm squared of a real quaternion -/
theorem normSq_embedReal (x : ℝ) : normSq (embedReal x) = x ^ 2 := by
  unfold normSq embedReal; ring

/-- **SPHERE PRESERVATION**: S¹ ↪ S⁷

    If x² + y² = 1, the real quaternion pair is on S⁷. -/
theorem knotIII_sphere (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    normSq (embedReal x) + normSq (embedReal y) = 1 := by
  rw [normSq_embedReal, normSq_embedReal]; linarith

/-- Conjugate of a real quaternion is itself -/
theorem qConj_embedReal (y : ℝ) : qConj (embedReal y) = embedReal y := by
  unfold qConj embedReal; simp

/-- **QUATERNIONIC HOPF ON REALS: EXPLICIT**

    ⟨x,0,0,0⟩ · conj(⟨y,0,0,0⟩) = ⟨x,0,0,0⟩ · ⟨y,0,0,0⟩ = ⟨xy,0,0,0⟩

    The product of two real quaternions is real.
    This is just... multiplication of real numbers. -/
theorem quatHopfQ_real (x y : ℝ) :
    quatHopfQ (embedReal x) (embedReal y) = embedReal (x * y) := by
  unfold quatHopfQ embedReal qConj
  ext <;> simp only [neg_zero, QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, mul_neg, mul_one,
    neg_neg, sub_zero, zero_mul, sub_self]

/-- **THE COMPOSED BINDING: REAL FROM QUATERNIONIC**

    The quaternionic Hopf map, restricted to real quaternion pairs,
    IS the real Hopf map (= complex squaring).

    Three levels of the tower in one theorem:
      ℝ ↪ ℂ ↪ ℍ  produces  realHopf ← complexHopf ← quatHopf  -/
theorem knotIII_binding (x y : ℝ) :
    -- The real component gives realHopf.1
    quatHopf₀ (embedReal x) (embedReal y) = (realHopf x y).1
    ∧
    -- The quaternionic component gives realHopf.2 (via 2·Re)
    2 * (quatHopfQ (embedReal x) (embedReal y)).re = (realHopf x y).2
    ∧
    -- ALL three imaginary parts vanish
    (quatHopfQ (embedReal x) (embedReal y)).imI = 0
    ∧ (quatHopfQ (embedReal x) (embedReal y)).imJ = 0
    ∧ (quatHopfQ (embedReal x) (embedReal y)).imK = 0 := by
  rw [quatHopfQ_real]
  unfold quatHopf₀ realHopf embedReal normSq
  exact ⟨by ring, by ring, rfl, rfl, rfl⟩

/-- **FIBER RESTRICTION: S⁰ ⊂ S¹ ⊂ S³**

    The S⁰ fiber {±1} embeds into S³ as real unit quaternions:
      +1 ↦ ⟨1, 0, 0, 0⟩ = s1Embed(0) = identity
      -1 ↦ ⟨-1, 0, 0, 0⟩ = s1Embed(π)

    The real fiber ⊂ complex fiber ⊂ quaternionic fiber. -/
theorem knotIII_fiber_embed_pos :
    embedReal 1 = 1 := by
  unfold embedReal; ext <;> simp

theorem knotIII_fiber_embed_neg :
    embedReal (-1) = -1 := by
  unfold embedReal; ext <;> simp

theorem knotIII_fiber_is_s1_restrict :
    s1Embed 0 = 1 ∧ s1Embed Real.pi = -1 := by
  unfold s1Embed
  constructor <;> ext <;> simp [cos_zero, sin_zero, cos_pi, sin_pi]

/-- **THE S⁰ FIBER PRESERVES THE QUATERNIONIC HOPF MAP**

    Right-multiplying both components by ±1 (= embedReal(±1)):
      quatHopf₀(x·(±1), y·(±1)) = quatHopf₀(x, y)
      quatHopfQ(x·(±1), y·(±1)) = quatHopfQ(x, y)

    This is trivially true for +1.
    For -1, it follows from (-a)(-b)* = a·b*. -/
theorem knotIII_fiber_preserves_hopf_neg (α β : ℍℝ) :
    quatHopf₀ (α * (-1)) (β * (-1)) = quatHopf₀ α β ∧
    quatHopfQ (α * (-1)) (β * (-1)) = quatHopfQ α β := by
  constructor
  · -- quatHopf₀
    unfold quatHopf₀
    --simp only [mul_neg, mul_one]
    have h₁ : normSq (-α) = normSq α := by unfold normSq; simp;
    have h₂ : normSq (-β) = normSq β := by unfold normSq; simp;
    ring_nf
    rw [h₁, h₂]
  · -- quatHopfQ
    unfold quatHopfQ
    unfold qConj
    ext <;> simp <;> grind only


/-- **COMPOSITION COHERENCE**

    Applying Knot I then Knot II gives the same result as Knot III.

    Embed (x,y) via Knot I to (x,0,y,0), then via Knot II to
    (⟨x,0,0,0⟩, ⟨y,0,0,0⟩).  This equals (embedReal x, embedReal y).

    The square commutes:

        (x, y)
         │  ╲
    Knot I   Knot III
         │       ╲
      (x,0,y,0)  (embedReal x, embedReal y)
         │       ↗
       Knot II
-/
theorem composition_coherence (x y : ℝ) :
    embedα x 0 = embedReal x ∧ embedβ y 0 = embedReal y := by
  exact ⟨rfl, rfl⟩

end KnotIII


end HopfTower.Knots
