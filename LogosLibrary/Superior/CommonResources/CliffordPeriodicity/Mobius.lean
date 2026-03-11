/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: CliffordPeriodicity/Mobius.lean
-/
import LogosLibrary.Superior.CommonResources.CliffordPeriodicity.Table
import LogosLibrary.Superior.CommonResources.CliffordPeriodicity.Clock
/-!
=====================================================================
## The Two Symmetries of the Bott Clock
=====================================================================

The Bott clock admits two distinct ℤ/2 symmetries with
completely different characters:

  PALINDROME (k ↔ 6-k on {0,...,6}):
    Preserves the base field.
    Reflects through the quaternionic midpoint.
    This is the Morita equivalence symmetry.

  CONJUGATION (k ↦ (8-k) % 8 on {0,...,7}):
    DISRUPTS the base field.
    Swaps ℂ ↔ non-ℂ at every complex position.
    This is the signature-reversal symmetry: Cl(n,0) ↔ Cl(0,n).

The Möbius twist of the Bott clock is the CONJUGATION, and it
does NOT preserve the complex structure — it destroys it.

This makes the survival of ℂ through the PERIODICITY
(the +8 step) even more remarkable: the period-8 step
preserves everything, while the conjugation preserves nothing
about the field type at complex positions.

The complex structure of Cl(9) is protected by periodicity
but vulnerable to signature reversal.  Fortunately, the
chimeric bundle has a DEFINITE signature (determined by the
tautological metric), so the conjugation never acts.
=====================================================================
-/
namespace CliffordPeriodicity

section TwoSymmetries
/-- The conjugation map on the Bott clock: k ↦ (8-k) mod 8.
    This is NOT a field-preserving map — it is the "twist"
    that relates the two halves of the Möbius band. -/
def clockConjugate (i : Fin 8) : Fin 8 :=
  ⟨(8 - i.val) % 8, Nat.mod_lt _ (by norm_num)⟩


-- ═══════════════════════════════════════════════════════════════
-- Symmetry 2 revisited: Conjugation (signature reversal)
-- ═══════════════════════════════════════════════════════════════

/-- Conjugation is an involution -/
theorem clockConjugate_involution (i : Fin 8) :
    clockConjugate (clockConjugate i) = i := by
  fin_cases i <;> simp [clockConjugate]

/-- Conjugation has exactly two fixed points: 0 and 4.
    These are the "poles" of the Möbius band.

    Position 0: Cl(0) ≅ ℝ (the trivial algebra)
    Position 4: Cl(4) ≅ M₂(ℍ) (the quaternionic midpoint)

    Both are self-conjugate because Cl(n,0) ≅ Cl(0,n)
    at n = 0 (trivially) and n = 4 (by a special isomorphism). -/
theorem clockConjugate_fixed_iff (i : Fin 8) :
    clockConjugate i = i ↔ i.val = 0 ∨ i.val = 4 := by
  fin_cases i <;> simp [clockConjugate]

/-- **CONJUGATION DESTROYS COMPLEX STRUCTURE**

    Every complex position is sent to a non-complex position.
    The Möbius twist of the Bott clock is hostile to ℂ. -/
theorem conjugate_swaps_complex (i : Fin 8)
    (h : fieldAtFin i = .complex) :
    fieldAtFin (clockConjugate i) ≠ .complex := by
  fin_cases i <;> simp_all [fieldAtFin, cliffordTable, clockConjugate]

/-- More precisely: conjugation sends the two complex positions
    to the two double positions.  ℂ ↦ split.

    1 (ℂ, simple) → 7 (ℝ, double)
    5 (ℂ, simple) → 3 (ℍ, double)

    The complex-and-simple positions are exchanged with the
    non-complex-and-double positions.  Conjugation swaps the
    "best" slots with the "worst" slots. -/
theorem conjugate_complex_to_double (i : Fin 8)
    (h : fieldAtFin i = .complex) :
    structureAtFin (clockConjugate i) = .double := by
  fin_cases i <;> simp_all [fieldAtFin, structureAtFin,
    cliffordTable, clockConjugate]

/-- Conversely: conjugation sends the double positions to
    the complex positions.

    3 (ℍ, double) → 5 (ℂ, simple)
    7 (ℝ, double) → 1 (ℂ, simple)  -/
theorem conjugate_double_to_complex (i : Fin 8)
    (h : structureAtFin i = .double) :
    fieldAtFin (clockConjugate i) = .complex := by
  fin_cases i <;> simp_all [fieldAtFin, structureAtFin,
    cliffordTable, clockConjugate]

/-- **THE COMPLEX-DOUBLE DUALITY**

    Conjugation establishes a perfect bijection:
      {complex, simple positions} ↔ {double positions}

    The positions that are best for spinor geometry (complex,
    simple = full matrix algebra over ℂ) are in bijection with
    the positions that are worst (split algebras with reducible
    spinor representations).

    This is the Bott clock's version of the Möbius twist
    exchanging "inside" and "outside." -/
theorem complex_double_duality :
    (∀ i : Fin 8, fieldAtFin i = .complex →
      structureAtFin (clockConjugate i) = .double)
    ∧ (∀ i : Fin 8, structureAtFin i = .double →
      fieldAtFin (clockConjugate i) = .complex) :=
  ⟨conjugate_complex_to_double, conjugate_double_to_complex⟩

-- ═══════════════════════════════════════════════════════════════
-- Symmetry 1 revisited: the palindrome (field-preserving)
-- ═══════════════════════════════════════════════════════════════

/-- The palindrome reflection: k ↦ 6-k on {0,...,6}.

    Unlike clockConjugate, this is only defined on 7 of the
    8 positions.  Position 7 has no palindrome partner — it
    is the "extra" position that breaks the field symmetry
    and witnesses the Möbius topology. -/
def palindromeReflect (i : Fin 7) : Fin 7 :=
  ⟨6 - i.val, by omega⟩

/-- The palindrome is an involution -/
theorem palindromeReflect_involution (i : Fin 7) :
    palindromeReflect (palindromeReflect i) = i := by
  fin_cases i <;> simp [palindromeReflect]

/-- Palindrome preserves field (already proved as field_palindrome,
    restated here for comparison with conjugation) -/
theorem palindrome_preserves_field (i : Fin 7) :
    fieldAtFin ⟨i.val, by omega⟩ =
    fieldAtFin ⟨6 - i.val, by omega⟩ :=
  field_palindrome i

-- ═══════════════════════════════════════════════════════════════
-- The contrast: why the two symmetries have different characters
-- ═══════════════════════════════════════════════════════════════

/-- **PALINDROME PRESERVES, CONJUGATION DESTROYS**

    For the complex position i = 1:
    - Palindrome sends 1 → 5: ℂ → ℂ  (preserved)
    - Conjugation sends 1 → 7: ℂ → ℝ  (destroyed)

    The palindrome is the "friendly" symmetry that keeps ℂ
    in the complex world.  The conjugation is the "hostile"
    symmetry that ejects it.

    In the Möbius gear picture:
    - The palindrome is the gear meshing (M ↔ M')
    - The conjugation is the half-twist (J) -/
theorem two_symmetries_differ_at_complex :
    -- Palindrome: 1 → 5, both complex
    fieldAtFin ⟨1, by omega⟩ = .complex
    ∧ fieldAtFin ⟨5, by omega⟩ = .complex
    -- Conjugation: 1 → 7, complex destroyed
    ∧ fieldAtFin ⟨1, by omega⟩ = .complex
    ∧ fieldAtFin ⟨7, by omega⟩ ≠ .complex := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp [fieldAtFin, cliffordTable]

/-- Position 7 is the OBSTRUCTION to extending the palindrome
    to the full clock.  It is:
    - Real (like position 0, its conjugate-partner)
    - Double (unlike position 0, which is simple)
    - The only position that is both real AND double

    It is the "seam" of the Möbius band: the point where the
    identification with a twist occurs. -/
theorem position7_is_seam :
    fieldAtFin ⟨7, by omega⟩ = .real
    ∧ structureAtFin ⟨7, by omega⟩ = .double
    ∧ ¬(fieldAtFin ⟨0, by omega⟩ = .real
        ∧ structureAtFin ⟨0, by omega⟩ = .double) := by
  refine ⟨rfl, rfl, ?_⟩
  simp [structureAtFin, cliffordTable]

end TwoSymmetries
end CliffordPeriodicity
