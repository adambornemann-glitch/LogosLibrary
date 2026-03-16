/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Knots/Knot_IV.lean
-/
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Defs
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_III
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_IV
/-!
=====================================================================
## Part XII: NON-ASSOCIATIVITY — Why the Tower Ends
=====================================================================

The octonions are the LAST normed division algebra (Hurwitz, 1898)
and produce the LAST Hopf fibration (Adams, 1960).

The next Cayley-Dickson doubling — the sedenions 𝕊 = 𝕆 × 𝕆 —
has zero divisors.  The norm is no longer multiplicative.
The Hopf construction fails.

We prove non-associativity by explicit witness.  We also prove
that the embedded quaternion subalgebra IS associative — the
breakdown is genuinely new at the octonionic level.
=====================================================================
-/
namespace HopfTower.Properties
open HopfTower.Defs HopfTower.Knots Real

section NonAssociativity

/-- Basis octonions for the non-associativity witness.

    e₁ = (i, 0) — an embedded quaternion imaginary unit
    e₂ = (j, 0) — another embedded quaternion imaginary unit
    e₄ = (0, 1) — the NEW Cayley-Dickson imaginary unit -/
def oct_e1 : 𝕆ℝ := ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩
def oct_e2 : 𝕆ℝ := ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩
def oct_e4 : 𝕆ℝ := ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩

/-- **THE OCTONIONS ARE NOT ASSOCIATIVE**

    (e₁ · e₂) · e₄ ≠ e₁ · (e₂ · e₄)

    This is THE structural reason the tower ends.
    After one more Cayley-Dickson doubling (to sedenions),
    we lose the division algebra property entirely.

    The octonions are the precise boundary: non-associative
    but still alternative, still a division algebra,
    still normed.  The Goldilocks algebra. -/
theorem oct_not_associative :
    octMul (octMul oct_e1 oct_e2) oct_e4 ≠
    octMul oct_e1 (octMul oct_e2 oct_e4) := by
  unfold octMul oct_e1 oct_e2 oct_e4 qConj
  intro h
  have : (1 : ℝ) = -1 := by
    simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, mul_one, add_zero, mul_neg, neg_zero, neg_neg,
      sub_self, zero_add, sub_zero, QuaternionAlgebra.mk_sub_mk, QuaternionAlgebra.mk_add_mk,
      zero_sub, QuaternionAlgebra.neg_mk, QuaternionAlgebra.re_zero, QuaternionAlgebra.imI_zero,
      QuaternionAlgebra.imJ_zero, QuaternionAlgebra.imK_zero, 𝕆ℝ.mk.injEq,
      QuaternionAlgebra.mk.injEq, true_and] at h
    linarith
  linarith

/-- **BUT THE EMBEDDED QUATERNIONS ARE ASSOCIATIVE**

    For any three quaternions p, q, r:
      embed(p) · (embed(q) · embed(r)) = (embed(p) · embed(q)) · embed(r)

    Because embedded multiplication is just quaternion multiplication,
    and quaternions ARE associative. -/
theorem embedded_quaternions_associative (p q r : ℍℝ) :
    octMul (embedOct p) (octMul (embedOct q) (embedOct r)) =
    octMul (octMul (embedOct p) (embedOct q)) (embedOct r) := by
  rw [octMul_embed, octMul_embed, octMul_embed, octMul_embed, mul_assoc]

/-- **ALTERNATIVITY**: Left alternative law

    x · (x · y) = (x · x) · y  for any two octonions
    (when one of them is an embedded quaternion).

    Full alternativity for arbitrary octonions is a more substantial
    proof — here we verify it for the embedded subalgebra, where it
    follows from quaternion associativity. -/
theorem oct_left_alternative_embed (p : ℍℝ) (y : 𝕆ℝ) :
    octMul (embedOct p) (octMul (embedOct p) y) =
    octMul (octMul (embedOct p) (embedOct p)) y := by
  rw [octMul_embed]
  unfold octMul embedOct qConj
  ext <;> simp <;> ring

/-- **WHY THE SEDENIONS FAIL**

    The key property that makes Hopf fibrations possible is
    that the norm is multiplicative: ‖xy‖ = ‖x‖·‖y‖.

    For the octonions, this holds (they're a composition algebra).
    For the sedenions, it FAILS — there exist zero divisors.

    We can already see the mechanism: the Cayley-Dickson product
    of two embedded quaternion pairs gives a clean norm identity.
    But one more doubling introduces terms that don't cancel.

    The norm multiplicativity for embedded pairs: -/
theorem oct_norm_mul_embed (p q : ℍℝ) :
    octNormSq (octMul (embedOct p) (embedOct q)) =
    octNormSq (embedOct p) * octNormSq (embedOct q) := by
  rw [octMul_embed, octNormSq_embed, octNormSq_embed, octNormSq_embed]
  exact normSq_mul p q

end NonAssociativity

end HopfTower.Properties
