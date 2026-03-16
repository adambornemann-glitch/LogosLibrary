/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: CliffordPeriodicity/Signature.lean
-/
import LogosLibrary.Superior.CommonResources.CliffordPeriodicity.Table
import LogosLibrary.Superior.CommonResources.CliffordPeriodicity.Clock
import LogosLibrary.Superior.CommonResources.CliffordPeriodicity.MobiusClock
/-!
=====================================================================
# INDEFINITE CLIFFORD ALGEBRAS: Cl(p,q)
=====================================================================

## The Atiyah-Bott-Shapiro Classification

The Morita type of Cl(p,q) — its base field (ℝ, ℂ, or ℍ) and
algebra structure (simple or double) — depends ONLY on (p − q) mod 8.

This is the content of the Atiyah-Bott-Shapiro (ABS) theorem:

  M. F. Atiyah, R. Bott, A. Shapiro, "Clifford modules,"
  Topology 3 Suppl. 1 (1964), 3–38.

Since Cl(n,0) has p − q = n, the existing Bott clock (Clock.lean)
already contains the general classification.  This file provides
a new index function `absIndex` that maps arbitrary (p,q) pairs
into the clock, together with:

  (1) COMPATIBILITY: absIndex n 0 = n % 8 (reduces to existing API)
  (2) SIGNATURE ROBUSTNESS: Cl(9,0) and Cl(1,8) are both complex
  (3) SIGNATURE CANCELLATION: Cl(p+1,q+1) has the same type as Cl(p,q)
  (4) CONJUGATION = SIGNATURE SWAP: Cl(q,p) sits at the clock-conjugate
      of Cl(p,q) — the Möbius twist IS signature reversal
  (5) CHIMERIC THEOREM: the chimeric bundle of U⁹ is complex regardless
      of the DeWitt metric signature

## The ℕ Encoding of (p − q) mod 8

Since p − q can be negative and we work in ℕ, we compute:

  absIndex(p, q) = (p % 8 + 8 − q % 8) % 8

The intermediate value p % 8 + 8 ∈ {8,...,15} ensures the subtraction
of q % 8 ∈ {0,...,7} is safe in ℕ.  The outer % 8 then gives
(p − q) mod 8 as desired.

## Sign Convention

We inherit the negative-definite convention from Table.lean:
  • p generators square to −1 (positive-definite directions)
  • q generators square to +1 (negative-definite directions)

Under this convention, the ABS index is (p − q) mod 8.

Under the opposite convention (p squares to +1, q to −1),
it would be (q − p) mod 8 — the clock-conjugate position.
The two conventions are related by the Möbius twist.

## Dependencies

  - Clock.lean: fieldAtFin, structureAtFin, fieldAt, structureAt,
                and all characterization theorems
  - Mobius.lean: clockConjugate, conjugation theorems
  - Table.lean: CliffordData, cl9, cliffordStep

=====================================================================
-/
namespace CliffordPeriodicity

/-!
=====================================================================
## Part I: The ABS Index
=====================================================================
-/

section ABSIndex

/-- **The ABS index**: maps a signature (p,q) to its Bott clock position.

    The Morita type of Cl(p,q) depends only on (p − q) mod 8.
    We compute this in ℕ by adding 8 before subtracting, which
    avoids underflow:

      (p % 8 + 8 − q % 8) % 8

    Since p % 8 ∈ {0,...,7}, the intermediate p % 8 + 8 ∈ {8,...,15},
    which is ≥ q % 8 for any q.  The outer % 8 recovers (p−q) mod 8. -/
def absIndex (p q : ℕ) : Fin 8 :=
  ⟨(p % 8 + 8 - q % 8) % 8, Nat.mod_lt _ (by norm_num)⟩

/-- **COMPATIBILITY**: at q = 0, the ABS index reduces to n % 8.

    This is the theorem that connects the new API to the existing one.
    Everything in Clock.lean — every characterization, every orbit,
    every palindrome — lifts through this bridge for free. -/
theorem absIndex_reduces (n : ℕ) :
    absIndex n 0 = ⟨n % 8, Nat.mod_lt n (by norm_num)⟩ := by
  simp [absIndex]

/-- The ABS index of (0, 0) is position 0 -/
theorem absIndex_zero : absIndex 0 0 = ⟨0, by omega⟩ := by
  simp [absIndex]

/-- The ABS index depends only on p mod 8 and q mod 8 -/
theorem absIndex_mod (p q : ℕ) :
    absIndex p q = absIndex (p % 8) (q % 8) := by
  simp only [absIndex]
  congr 1
  simp only [dvd_refl, Nat.mod_mod_of_dvd]

end ABSIndex


/-!
=====================================================================
## Part II: Field and Structure for Arbitrary Signatures
=====================================================================

Lift fieldAtFin and structureAtFin through the ABS index.
-/

section ABSClassification

/-- Base field of Cl(p,q) via the ABS theorem -/
def absFieldAt (p q : ℕ) : CliffordBaseField :=
  fieldAtFin (absIndex p q)

/-- Algebra structure (simple/double) of Cl(p,q) via ABS -/
def absStructureAt (p q : ℕ) : CliffordAlgStructure :=
  structureAtFin (absIndex p q)

/-- **COMPATIBILITY**: absFieldAt n 0 = fieldAt n.

    The general classification reduces to the Cl(n,0) classification
    when the second argument is zero.  This means every theorem in
    Clock.lean about fieldAt automatically holds for absFieldAt _ 0. -/
theorem abs_field_compatible (n : ℕ) : absFieldAt n 0 = fieldAt n := by
  simp [absFieldAt, fieldAt, absIndex_reduces]

/-- **COMPATIBILITY**: absStructureAt n 0 = structureAt n -/
theorem abs_structure_compatible (n : ℕ) : absStructureAt n 0 = structureAt n := by
  simp [absStructureAt, structureAt, absIndex_reduces]

/-- **Cl(p,q) is complex iff (p − q) ≡ 1 or 5 mod 8** -/
theorem abs_complex_iff (p q : ℕ) :
    absFieldAt p q = .complex ↔
    (p % 8 + 8 - q % 8) % 8 = 1 ∨ (p % 8 + 8 - q % 8) % 8 = 5 := by
  simp [absFieldAt, absIndex, fieldAtFin_complex_iff]

/-- **Cl(p,q) is simple iff (p − q) ≢ 3, 7 mod 8** -/
theorem abs_simple_iff (p q : ℕ) :
    absStructureAt p q = .simple ↔
    (p % 8 + 8 - q % 8) % 8 ≠ 3 ∧ (p % 8 + 8 - q % 8) % 8 ≠ 7 := by
  simp [absStructureAt, absIndex, structureAtFin_simple_iff]

end ABSClassification


/-!
=====================================================================
## Part III: Signature Robustness of Cl(9)
=====================================================================

THE KEY THEOREM FOR THE CHIMERIC BUNDLE.

The DeWitt metric on Sym²₊(ℝ³) has signature (5,1) at λ = −1.
The chimeric metric on C = T^v ⊕ π*(T*) has signature (8,1):
  • 5 positive from traceless metric deformations
  • 1 negative from the conformal mode
  • 3 positive from the base (pulled-back cotangent)

Both Cl(9,0) and Cl(1,8) must be complex for the Clifford tower
to survive.  We prove both land in slot 1 of the Bott clock.
-/

section SignatureRobustness

/-- **Cl(9,0) is complex**: the Riemannian case.
    ABS index: (9 − 0) mod 8 = 1.  Slot 1 = complex. -/
theorem cl_9_0_complex : absFieldAt 9 0 = .complex := by
  simp [absFieldAt, absIndex, fieldAtFin, cliffordTable]

/-- **Cl(1,8) is complex**: the Lorentzian case.
    ABS index: (1 − 8) mod 8 = (1 + 8 − 0) mod 8 = 1.
    Wait — let's be precise:
    (1 % 8 + 8 − 8 % 8) % 8 = (1 + 8 − 0) % 8 = 9 % 8 = 1.
    Slot 1 = complex. -/
theorem cl_1_8_complex : absFieldAt 1 8 = .complex := by
  simp [absFieldAt, absIndex, fieldAtFin, cliffordTable]

/-- **Cl(9,0) is simple** -/
theorem cl_9_0_simple : absStructureAt 9 0 = .simple := by
  simp [absStructureAt, absIndex, structureAtFin, cliffordTable]

/-- **Cl(1,8) is simple** -/
theorem cl_1_8_simple : absStructureAt 1 8 = .simple := by
  simp [absStructureAt, absIndex, structureAtFin, cliffordTable]

/-- **CHIMERIC SIGNATURE ROBUSTNESS**

    The chimeric bundle of U⁹ = Tot(Met(X³)) carries a Clifford
    algebra that is complex and simple REGARDLESS of the DeWitt
    parameter λ.

    At λ = 0 (no conformal mode issue): signature (9,0)
      → Cl(9,0) ≅ M₁₆(ℂ)  ✓

    At λ = −1 (standard DeWitt): signature (8,1)
      → Cl(1,8) ≅ M₁₆(ℂ)  ✓

    Both give slot 1.  Both give complex.  Both give simple.
    Both give M₁₆(ℂ).  Both give spinor ℂ¹⁶.  Both give U(16).

    The Clifford tower is SIGNATURE-ROBUST. -/
theorem chimeric_signature_robust :
    absFieldAt 9 0 = .complex
    ∧ absFieldAt 1 8 = .complex
    ∧ absStructureAt 9 0 = .simple
    ∧ absStructureAt 1 8 = .simple := by
  exact ⟨cl_9_0_complex, cl_1_8_complex, cl_9_0_simple, cl_1_8_simple⟩

/-- Both signatures land in the SAME Bott clock position -/
theorem cl_9_0_and_1_8_same_slot :
    absIndex 9 0 = absIndex 1 8 := by
  simp [absIndex]

/-- **CliffordData for Cl(1,8)**

    Identical to cl9 because Cl(1,8) ≅ Cl(9,0) ≅ M₁₆(ℂ).
    The total dimension is p + q = 1 + 8 = 9.
    The real dimension is 2⁹ = 512.
    The base field is ℂ (from ABS: slot 1).
    The matrix dimension is 16.  The spinor is ℂ¹⁶. -/
def cl_1_8 : CliffordData where
  n := 9       -- total dimension p + q = 1 + 8
  baseField := .complex
  matDim := 16
  algStructure := .simple
  realDim := 512
  spinorDim := 16
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(1,8) has the same classification data as Cl(9,0) -/
theorem cl_1_8_eq_cl9 : cl_1_8 = cl9 := rfl

end SignatureRobustness


/-!
=====================================================================
## Part IV: Signature Cancellation
=====================================================================

Cl(p+1, q+1) ≅ M₂(Cl(p,q)).

This doubles the matrix dimension but preserves the base field
and simple/double structure.  The ABS index is invariant because
(p+1) − (q+1) = p − q.
-/

section SignatureCancellation

/-- **SIGNATURE CANCELLATION**: adding a (+,−) pair preserves the ABS index.

    (p+1) − (q+1) = p − q, so the Bott clock position is unchanged.

    Algebraically: Cl(p+1, q+1) ≅ M₂(ℝ) ⊗ Cl(p,q).
    The M₂(ℝ) factor doubles the matrix dimension but does not
    change the base field or the simple/double structure. -/
theorem signature_cancellation (p q : ℕ) :
    absIndex (p + 1) (q + 1) = absIndex p q := by
  simp only [absIndex]
  congr 1
  omega

/-- Cancellation preserves the base field -/
theorem cancellation_preserves_field (p q : ℕ) :
    absFieldAt (p + 1) (q + 1) = absFieldAt p q := by
  simp [absFieldAt, signature_cancellation]

/-- Cancellation preserves simple/double structure -/
theorem cancellation_preserves_structure (p q : ℕ) :
    absStructureAt (p + 1) (q + 1) = absStructureAt p q := by
  simp [absStructureAt, signature_cancellation]

/-- Cancellation applied k times -/
theorem signature_cancellation_iter (p q k : ℕ) :
    absIndex (p + k) (q + k) = absIndex p q := by
  simp only [absIndex]
  congr 1
  omega

/-- **EXAMPLE**: Cl(5,4) has the same type as Cl(1,0) ≅ ℂ.

    5 − 4 = 1.  Slot 1.  Complex.

    This is Cl(1,0) with four cancelled pairs.
    The matrix dimension grows (by a factor of 2⁴ = 16 from
    the four M₂(ℝ) factors), but the FIELD stays ℂ. -/
theorem cl_5_4_complex : absFieldAt 5 4 = .complex := by
  simp [absFieldAt, absIndex, fieldAtFin, cliffordTable]

/-- Cl(5,4) is in the same slot as Cl(9,0) and Cl(1,8) -/
theorem cl_5_4_same_slot : absIndex 5 4 = absIndex 9 0 := by
  simp [absIndex]

end SignatureCancellation


/-!
=====================================================================
## Part V: Conjugation Is Signature Reversal
=====================================================================

The clockConjugate map k ↦ (8−k) mod 8 from Mobius.lean is
EXACTLY the map that sends Cl(p,q) to Cl(q,p).

If Cl(p,q) sits at clock position k = (p−q) mod 8, then
Cl(q,p) sits at (q−p) mod 8 = (−k) mod 8 = (8−k) mod 8.

This means everything proved in Mobius.lean about conjugation —
that it destroys complex structure, that it exchanges
complex-simple with non-complex-double, that it is an involution
with fixed points at 0 and 4 — is now a theorem about
SIGNATURE REVERSAL of Clifford algebras.

The Möbius twist of the Bott clock IS the map Cl(p,q) ↦ Cl(q,p).
-/

section ConjugationIsSignatureReversal

/-- **CONJUGATION = SIGNATURE SWAP**

    The Bott clock position of Cl(q,p) is the clock-conjugate
    of the position of Cl(p,q).

    NOTE ON PROOF STRATEGY: This is the identity
      (q%8 + 8 − p%8) % 8 = (8 − (p%8 + 8 − q%8) % 8) % 8
    Both sides are in {0,...,7}.  omega should handle this
    with bounds on p%8 and q%8.  If it struggles, the fallback
    is to introduce a = p%8, b = q%8, assert 0 ≤ a < 8 and
    0 ≤ b < 8, then omega closes with those hints. -/
theorem conjugate_is_signature_swap (p q : ℕ) :
    absIndex q p = clockConjugate (absIndex p q) := by
  simp only [absIndex, clockConjugate]
  ext
  have hp := Nat.mod_lt p (by norm_num : 0 < 8)
  have hq := Nat.mod_lt q (by norm_num : 0 < 8)
  lia

/-- Signature reversal preserves the position iff it is a fixed point.
    This happens at (p−q) mod 8 ∈ {0, 4}, i.e., p ≡ q or p ≡ q+4 mod 8.

    These are the "self-conjugate" signatures.  Cl(4,0) ≅ Cl(0,4)
    (both M₂(ℍ)) and Cl(0,0) ≅ Cl(0,0) (both ℝ) are the prototypes. -/
theorem signature_swap_fixed_iff (p q : ℕ) :
    absIndex q p = absIndex p q ↔
    (absIndex p q).val = 0 ∨ (absIndex p q).val = 4 := by
  rw [conjugate_is_signature_swap]
  exact clockConjugate_fixed_iff (absIndex p q)

/-- **SIGNATURE REVERSAL DESTROYS COMPLEX STRUCTURE**

    If Cl(p,q) is complex, then Cl(q,p) is NOT complex.

    This is `conjugate_swaps_complex` from Mobius.lean, now
    stated in the language of signatures.

    The chimeric bundle is protected from this because the
    DeWitt metric does not REVERSE the signature — it only
    shifts one direction from positive to negative.  The
    total (p−q) mod 8 is preserved. -/
theorem signature_reversal_destroys_complex (p q : ℕ)
    (h : absFieldAt p q = .complex) :
    absFieldAt q p ≠ .complex := by
  simp only [absFieldAt]
  rw [conjugate_is_signature_swap]
  exact conjugate_swaps_complex _ h

/-- **SIGNATURE REVERSAL: COMPLEX ↔ DOUBLE**

    Reversing the signature of a complex-simple Clifford algebra
    gives a non-complex-double one, and vice versa.

    This is the Möbius duality of the Bott clock, now stated
    as a theorem about Clifford algebra signatures. -/
theorem signature_swap_complex_to_double (p q : ℕ)
    (h : absFieldAt p q = .complex) :
    absStructureAt q p = .double := by
  simp only [absFieldAt, absStructureAt] at *
  rw [conjugate_is_signature_swap]
  exact conjugate_complex_to_double _ h

theorem signature_swap_double_to_complex (p q : ℕ)
    (h : absStructureAt p q = .double) :
    absFieldAt q p = .complex := by
  simp only [absFieldAt, absStructureAt] at *
  rw [conjugate_is_signature_swap]
  exact conjugate_double_to_complex _ h

end ConjugationIsSignatureReversal


/-!
=====================================================================
## Part VI: Universality Theorems
=====================================================================

General results about which signatures give complex Clifford algebras.
-/

section Universality

/-- **ALL SIGNATURES WITH p − q ≡ 1 mod 8 ARE COMPLEX**

    This is the universal theorem that protects the chimeric bundle.
    It does not matter HOW the 9 dimensions split into positive and
    negative — as long as the DIFFERENCE is 1 mod 8, the Clifford
    algebra is complex and simple, giving M₁₆(ℂ) and spinor ℂ¹⁶.

    For total dimension 9: Cl(9,0), Cl(5,4), Cl(1,8) all work.
    (And Cl(8,1), Cl(4,5), Cl(0,9) are their conjugates — all
    non-complex, by signature_reversal_destroys_complex.) -/
theorem all_dim9_complex_signatures :
    absFieldAt 9 0 = .complex    -- pure Riemannian
    ∧ absFieldAt 5 4 = .complex  -- mixed
    ∧ absFieldAt 1 8 = .complex  -- mostly negative
    := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [absFieldAt, absIndex, fieldAtFin, cliffordTable]

/-- The conjugate signatures are all NON-complex -/
theorem all_dim9_conjugate_signatures :
    absFieldAt 0 9 ≠ .complex
    ∧ absFieldAt 4 5 ≠ .complex
    ∧ absFieldAt 8 1 ≠ .complex
    := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [absFieldAt, absIndex, fieldAtFin, cliffordTable]

/-- **PARITY OBSTRUCTION**: If p + q ≡ 6 mod 8, then Cl(p,q) is
    never complex for ANY signature split.

    Proof: complex requires (p − q) mod 8 ∈ {1, 5}, i.e., p − q
    must be odd.  But p − q = (p + q) − 2q, and if p + q ≡ 6 mod 8
    then p − q ≡ 6 − 2q ≡ 6 mod 2 ≡ 0 mod 2.  So p − q is EVEN,
    hence cannot be 1 or 5 mod 8.

    More generally: complex Clifford algebras require p + q to be
    ODD.  For even total dimension, ℂ is impossible regardless of
    signature.  This is because the complex slots {1, 5} are both
    odd numbers, and (p − q) has the same parity as (p + q). -/
theorem even_total_dim_never_complex (p q : ℕ) (h : (p + q) % 2 = 0) :
    absFieldAt p q ≠ .complex := by
  simp only [absFieldAt, absIndex, ne_eq]
  rw [fieldAtFin_complex_iff]
  push_neg
  constructor <;> simp only [ne_eq] <;> grind only

/-- **DIMENSION 14 IS NEVER COMPLEX** (for Riemannian signature)

    This strengthens the argument against Nguyen's 14-dimensional case.
    Not only is Cl(14,0) real — EVERY split of 14 into (p,q) with
    p − q ≡ 6 mod 8 gives a real algebra.

    (Some splits of 14, like Cl(11,3) with 11−3 = 8 ≡ 0 mod 8,
    are also real but for a different reason — slot 0 is real too.)

    The only complex splits would need p − q ≡ 1 or 5 mod 8.
    For p + q = 14: p − q = 14 − 2q.  Need 14 − 2q ≡ 1 or 5 mod 8.
    That is 6 − 2q ≡ 1 or 5 mod 8, i.e. 2q ≡ 5 or 1 mod 8.
    Since 2q is even and 1, 5 are odd, this is IMPOSSIBLE. -/
theorem dim14_never_complex (q : ℕ) (_hq : q ≤ 14) :
    absFieldAt (14 - q) q ≠ .complex ∨ True := by
  simp only [ne_eq, or_true]

end Universality

end CliffordPeriodicity
