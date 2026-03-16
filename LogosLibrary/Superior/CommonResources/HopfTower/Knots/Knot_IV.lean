/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Knots/Knot_IV.lean
-/
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Defs
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_III
/-!
=====================================================================
## Part IX: KNOT IV — The Quaternionic-Octonionic Binding
=====================================================================

The embedding  S⁷ ↪ S¹⁵:

    q  ↦  (q, 0)

A single quaternion, promoted to an octonion with zero
right component.  Same pattern: zero out the new
Cayley-Dickson coordinate.

Under this embedding:

    octHopf₀((p,0), (q,0)) = ‖p‖² - ‖q‖²     = quatHopf₀(p, q)
    octHopfO((p,0), (q,0)) = (p·conj(q), 0)    = embed(quatHopfQ(p,q))

The FOUR right-quaternion components vanish — the transverse
directions that the ℍ embedding doesn't see.

The S⁷ image sits inside S¹⁵ where the right coordinates = 0.
The S³ fiber (unit quaternions) sits inside the S⁷ fiber
(unit octonions) as the embedded subloop  q ↦ (q, 0).
=====================================================================
-/
namespace HopfTower.Knots
open HopfTower.Defs Real
section KnotIV

-- ═══════════════════════════════════════════════════════════════
-- The Octonionic Hopf Map:  S¹⁵ → S⁸
-- ═══════════════════════════════════════════════════════════════

/-- The real component of the octonionic Hopf map -/
noncomputable def octHopf₀ (α β : 𝕆ℝ) : ℝ := octNormSq α - octNormSq β

/-- The octonionic component of the octonionic Hopf map -/
def octHopfO (α β : 𝕆ℝ) : 𝕆ℝ := octMul α (octConj β)

-- ═══════════════════════════════════════════════════════════════
-- The Embedding  ℍ ↪ 𝕆
-- ═══════════════════════════════════════════════════════════════

/-- Embed a quaternion as an octonion: q ↦ (q, 0) -/
def embedOct (q : ℍℝ) : 𝕆ℝ := ⟨q, 0⟩

/-- **EMBEDDING PRESERVES NORM** -/
theorem octNormSq_embed (q : ℍℝ) : octNormSq (embedOct q) = normSq q := by
  unfold octNormSq embedOct
  simp [normSq_zero]

-- The key lemma: why the embedding works

/-- **QUATERNION MULTIPLICATION EMBEDS**

    (p, 0) · (q, 0) = (pq - conj(0)·0, 0·p + 0·conj(q)) = (pq, 0)

    The Cayley-Dickson twist vanishes when the right component is zero.
    This is WHY the quaternion subalgebra is associative inside 𝕆:
    we never invoke the twisted terms. -/
theorem octMul_embed (p q : ℍℝ) :
    octMul (embedOct p) (embedOct q) = embedOct (p * q) := by
  unfold octMul embedOct qConj
  ext <;> simp

/-- **CONJUGATION EMBEDS**

    conj(q, 0) = (conj(q), -0) = (conj(q), 0) = embed(conj(q))

    The conjugation of an embedded quaternion stays embedded. -/
theorem octConj_embed (q : ℍℝ) :
    octConj (embedOct q) = embedOct (qConj q) := by
  unfold octConj embedOct
  ext <;> simp

-- ═══════════════════════════════════════════════════════════════
-- KNOT IV: The Binding Theorem
-- ═══════════════════════════════════════════════════════════════

/-- **SPHERE PRESERVATION**: S⁷ ↪ S¹⁵

    If ‖p‖² + ‖q‖² = 1 then ‖(p,0)‖² + ‖(q,0)‖² = 1. -/
theorem knotIV_sphere (p q : ℍℝ) (h : normSq p + normSq q = 1) :
    octNormSq (embedOct p) + octNormSq (embedOct q) = 1 := by
  rw [octNormSq_embed, octNormSq_embed]; exact h

/-- **THE QUATERNIONIC-OCTONIONIC BINDING**

    The octonionic Hopf map, restricted to embedded quaternion pairs,
    IS the quaternionic Hopf map:

    octHopf₀((p,0), (q,0)) = quatHopf₀(p, q)
    octHopfO((p,0), (q,0)) = embed(quatHopfQ(p, q))

    With FOUR transverse components vanishing:
    the entire right-quaternion part of octHopfO is zero. -/
theorem knotIV_binding (p q : ℍℝ) :
    -- The real component matches
    octHopf₀ (embedOct p) (embedOct q) = quatHopf₀ p q
    ∧
    -- The octonionic component is an embedded quaternion
    octHopfO (embedOct p) (embedOct q) = embedOct (quatHopfQ p q)
    ∧
    -- Explicitly: the right quaternion vanishes (4 transverse components)
    (octHopfO (embedOct p) (embedOct q)).r = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · -- octHopf₀ = quatHopf₀
    unfold octHopf₀ quatHopf₀
    rw [octNormSq_embed, octNormSq_embed]
  · -- octHopfO = embed(quatHopfQ)
    unfold octHopfO quatHopfQ
    rw [octConj_embed, octMul_embed]
  · -- right component vanishes
    unfold octHopfO
    rw [octConj_embed, octMul_embed]
    rfl

/-- **EXPLICIT TRANSVERSE VANISHING**

    The four vanishing components spelled out:
    octHopfO(...).r.re = 0, .r.imI = 0, .r.imJ = 0, .r.imK = 0

    These are the four "extra" coordinates of S⁸ that
    the S⁴ image doesn't see. -/
theorem knotIV_transverse (p q : ℍℝ) :
    let h := octHopfO (embedOct p) (embedOct q)
    h.r.re = 0 ∧ h.r.imI = 0 ∧ h.r.imJ = 0 ∧ h.r.imK = 0 := by
  simp only
  have hr := (knotIV_binding p q).2.2
  constructor
  · exact congrArg QuaternionAlgebra.re hr
  constructor
  · exact congrArg QuaternionAlgebra.imI hr
  constructor
  · exact congrArg QuaternionAlgebra.imJ hr
  · exact congrArg QuaternionAlgebra.imK hr

/-- **FIBER EMBEDDING: S³ ↪ S⁷ AS A SUB-LOOP**

    The S³ fiber of the quaternionic Hopf map embeds into
    the S⁷ fiber of the octonionic Hopf map.

    Right-multiplying both components by an embedded unit quaternion:
      octMul (embedOct p) (embedOct u) = embedOct (p * u)

    The fiber action of S³ ⊂ S⁷ stays within the embedded subspace.

    CRITICAL SUBTLETY: S⁷ is NOT a group — it's a Moufang loop.
    The unit octonions are non-associative.  But S³ ⊂ S⁷ IS a
    group (since embedded quaternions multiply associatively). -/
theorem knotIV_fiber_embed (p q u : ℍℝ) (hu : normSq u = 1) :
    -- The fiber action stays embedded
    octMul (embedOct p) (embedOct u) = embedOct (p * u)
    ∧ octMul (embedOct q) (embedOct u) = embedOct (q * u)
    ∧
    -- The fiber action preserves the Hopf map
    octHopf₀ (embedOct (p * u)) (embedOct (q * u)) =
      octHopf₀ (embedOct p) (embedOct q) := by
  refine ⟨octMul_embed p u, octMul_embed q u, ?_⟩
  unfold octHopf₀
  rw [octNormSq_embed, octNormSq_embed, octNormSq_embed, octNormSq_embed]
  rw [normSq_mul, normSq_mul, hu, mul_one, mul_one]

/-- Fiber action preserves the octonionic Hopf component -/
theorem knotIV_fiber_hopfQ (p q u : ℍℝ) (_hu : normSq u = 1) :
    octHopfO (embedOct (p * u)) (embedOct (q * u)) =
    embedOct (p * u * qConj (q * u)) := by
  unfold octHopfO; rw [octConj_embed, octMul_embed]

end KnotIV
