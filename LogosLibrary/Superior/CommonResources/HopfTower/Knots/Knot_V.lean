/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Knots/Knot_V.lean
-/
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Defs
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_III
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_IV
/-!
=====================================================================
## KNOT V — Composed Embeddings Through 𝕆
=====================================================================

The FULL composed embeddings:

  ℝ → ℂ → ℍ → 𝕆:  x ↦ ⟨x,0,0,0⟩ ↦ (⟨x,0,0,0⟩, 0)

  ℂ → ℍ → 𝕆:  (a,b) ↦ ⟨a,b,0,0⟩ ↦ (⟨a,b,0,0⟩, 0)

Each composition just stacks the embeddings.
The octonionic Hopf restricted maximally IS the real squaring map.

Four levels of the tower in one theorem.
=====================================================================
-/
namespace HopfTower.Knots
open HopfTower.Defs Real

section KnotV

/-- The composed embedding: real number → octonion
    x ↦ (⟨x, 0, 0, 0⟩, ⟨0,0,0,0⟩) -/
def embedRealOct (x : ℝ) : 𝕆ℝ := embedOct (embedReal x)

/-- The composed embedding: complex pair → octonion
    (a, b) ↦ (⟨a, b, 0, 0⟩, ⟨0,0,0,0⟩) -/
def embedCplxOct (a b : ℝ) : 𝕆ℝ := embedOct (embedα a b)

/-- Composition coherence: embedRealOct = embedOct ∘ embedReal -/
theorem embed_compose_real_oct (x : ℝ) :
    embedRealOct x = embedOct (embedReal x) := rfl

/-- Composition coherence: embedCplxOct = embedOct ∘ embedα -/
theorem embed_compose_cplx_oct (a b : ℝ) :
    embedCplxOct a b = embedOct (embedα a b) := rfl

/-- **THE MAXIMAL RESTRICTION: REAL FROM OCTONIONIC**

    The octonionic Hopf map, restricted to real octonion pairs,
    directly produces the real Hopf map.

    FOUR levels of the tower in one theorem:
    ℝ ↪ ℂ ↪ ℍ ↪ 𝕆  produces  realHopf ← cplxHopf ← quatHopf ← octHopf -/
theorem knotV_real_binding (x y : ℝ) :
    -- The real component gives realHopf.1
    octHopf₀ (embedRealOct x) (embedRealOct y) = (realHopf x y).1
    ∧
    -- Seven of eight octHopfO components vanish
    -- (only the real part of the left quaternion survives)
    (octHopfO (embedRealOct x) (embedRealOct y)).l.re = x * y
    ∧ (octHopfO (embedRealOct x) (embedRealOct y)).l.imI = 0
    ∧ (octHopfO (embedRealOct x) (embedRealOct y)).l.imJ = 0
    ∧ (octHopfO (embedRealOct x) (embedRealOct y)).l.imK = 0
    ∧ (octHopfO (embedRealOct x) (embedRealOct y)).r = 0 := by
  unfold embedRealOct
  have hb := knotIV_binding (embedReal x) (embedReal y)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- octHopf₀ = quatHopf₀ = realHopf.1
    rw [hb.1]
    unfold quatHopf₀ normSq embedReal realHopf
    ring
  · -- .l.re = x*y
    unfold octHopfO
    rw [octConj_embed, octMul_embed]
    unfold embedReal qConj
    simp
    exact ext_cauchy rfl
  · -- .l.imI = 0
    unfold octHopfO
    rw [octConj_embed, octMul_embed]
    unfold embedReal qConj
    simp
    exact EReal.coe_eq_zero.mp rfl
  · -- .l.imJ = 0
    unfold octHopfO
    rw [octConj_embed, octMul_embed]
    unfold embedReal qConj
    simp
    exact EReal.coe_eq_zero.mp rfl
  · -- .l.imK = 0
    unfold octHopfO
    rw [octConj_embed, octMul_embed]
    unfold embedReal qConj
    simp
    exact EReal.coe_eq_zero.mp rfl
  · -- .r = 0
    exact hb.2.2

/-- **SPHERE CHAIN**: S¹ ↪ S³ ↪ S⁷ ↪ S¹⁵

    Each embedding preserves the sphere constraint. -/
theorem sphere_chain (x y : ℝ) (hxy : x ^ 2 + y ^ 2 = 1) :
    -- S¹ ↪ S¹⁵
    octNormSq (embedRealOct x) + octNormSq (embedRealOct y) = 1 := by
  unfold embedRealOct
  rw [octNormSq_embed, octNormSq_embed]
  unfold normSq embedReal; linarith

end KnotV

end HopfTower.Knots
