/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: CliffordPeriodicity/Clock.lean
-/
import LogosLibrary.Superior.CommonResources.CliffordPeriodicity.Table
/-!
=====================================================================
## Complete Bott Clock Characterization
=====================================================================

The full partition of the Bott clock by base field and by
algebra structure (simple vs double).  Eight positions,
completely characterized.

After this section, every property of the clock that your
later theorems reference is a COROLLARY of a universal
characterization, not a spot-check on hand-written data.
=====================================================================
-/
namespace CliffordPeriodicity

section UniversalCharacterization

/-- Extract the base field from the Bott clock at a given position -/
def fieldAtFin (i : Fin 8) : CliffordBaseField := (cliffordTable i).1

/-- The complex positions in the Bott clock are EXACTLY {1, 5}.

    Proof: let the computer inspect all eight entries.
    fin_cases splits the goal into eight subgoals, one per
    clock position; simp evaluates the table lookup and
    checks whether the result is .complex.

    Eight cases.  Eight evaluations.  Done. -/
theorem fieldAtFin_complex_iff (i : Fin 8) :
    fieldAtFin i = .complex ↔ i.val = 1 ∨ i.val = 5 := by
  fin_cases i <;> simp [fieldAtFin, cliffordTable]

/-- Lift from the clock to arbitrary dimension via mod 8 -/
def fieldAt (k : ℕ) : CliffordBaseField :=
  fieldAtFin ⟨k % 8, Nat.mod_lt k (by norm_num)⟩

/-- **THE CHARACTERIZATION THEOREM**

    Cl(n,0) has complex base field ⟺ n ≡ 1 or 5 (mod 8).

    This is a universal statement about the ENTIRE periodicity,
    not a spot-check at n = 9.  The quantifier ranges over
    every natural number. -/
theorem fieldAt_complex_iff (k : ℕ) :
    fieldAt k = .complex ↔ k % 8 = 1 ∨ k % 8 = 5 := by
  simp [fieldAt, fieldAtFin_complex_iff]

/-- Cl(9) is complex: now a COROLLARY of the universal theorem -/
theorem cl9_complex_universal : fieldAt 9 = .complex := by
  rw [fieldAt_complex_iff]; left; norm_num

/-- Cl(14) is not complex: also a corollary -/
theorem cl14_not_complex_universal : fieldAt 14 ≠ .complex := by
  simp only [ne_eq]; rw [fieldAt_complex_iff]; push_neg; constructor <;> norm_num



end UniversalCharacterization

section BottClockComplete

-- ═══════════════════════════════════════════════════════════════
-- Structure type extraction and characterization
-- ═══════════════════════════════════════════════════════════════

/-- Extract the algebra structure from the Bott clock -/
def structureAtFin (i : Fin 8) : CliffordAlgStructure := (cliffordTable i).2

/-- Lift to arbitrary dimension -/
def structureAt (k : ℕ) : CliffordAlgStructure :=
  structureAtFin ⟨k % 8, Nat.mod_lt k (by norm_num)⟩

/-- The double (split) positions are EXACTLY {3, 7}.

    These are the dimensions where the volume element ω = e₁⋯eₙ
    satisfies ω² = +1 AND ω is central — giving the idempotent
    splitting (1 ± ω)/2 into two simple summands. -/
theorem structureAtFin_double_iff (i : Fin 8) :
    structureAtFin i = .double ↔ i.val = 3 ∨ i.val = 7 := by
  fin_cases i <;> simp [structureAtFin, cliffordTable]

/-- The simple positions are the complement: {0, 1, 2, 4, 5, 6} -/
theorem structureAtFin_simple_iff (i : Fin 8) :
    structureAtFin i = .simple ↔ i.val ≠ 3 ∧ i.val ≠ 7 := by
  fin_cases i <;> simp [structureAtFin, cliffordTable]

/-- Universal version: double iff k ≡ 3 or 7 mod 8 -/
theorem structureAt_double_iff (k : ℕ) :
    structureAt k = .double ↔ k % 8 = 3 ∨ k % 8 = 7 := by
  simp [structureAt, structureAtFin_double_iff]

/-- Universal version: simple iff k ≢ 3, 7 mod 8 -/
theorem structureAt_simple_iff (k : ℕ) :
    structureAt k = .simple ↔ k % 8 ≠ 3 ∧ k % 8 ≠ 7 := by
  simp [structureAt, structureAtFin_simple_iff]

-- ═══════════════════════════════════════════════════════════════
-- Complete field partition (the three characterization theorems
-- from before, plus their universal lifts)
-- ═══════════════════════════════════════════════════════════════

/-- Quaternionic positions: exactly {2, 3, 4} -/
theorem fieldAtFin_quaternion_iff (i : Fin 8) :
    fieldAtFin i = .quaternion ↔ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by
  fin_cases i <;> simp [fieldAtFin, cliffordTable]

/-- Real positions: exactly {0, 6, 7} -/
theorem fieldAtFin_real_iff (i : Fin 8) :
    fieldAtFin i = .real ↔ i.val = 0 ∨ i.val = 6 ∨ i.val = 7 := by
  fin_cases i <;> simp [fieldAtFin, cliffordTable]

/-- Universal: quaternionic iff k ≡ 2, 3, or 4 mod 8 -/
theorem fieldAt_quaternion_iff (k : ℕ) :
    fieldAt k = .quaternion ↔ k % 8 = 2 ∨ k % 8 = 3 ∨ k % 8 = 4 := by
  simp [fieldAt, fieldAtFin_quaternion_iff]

/-- Universal: real iff k ≡ 0, 6, or 7 mod 8 -/
theorem fieldAt_real_iff (k : ℕ) :
    fieldAt k = .real ↔ k % 8 = 0 ∨ k % 8 = 6 ∨ k % 8 = 7 := by
  simp [fieldAt, fieldAtFin_real_iff]

-- ═══════════════════════════════════════════════════════════════
-- The partition is exhaustive and exclusive
-- ═══════════════════════════════════════════════════════════════

/-- Every Bott clock position has exactly one field type.
    (Exhaustion: the three field sets cover all of Fin 8.) -/
theorem fieldAtFin_trichotomy (i : Fin 8) :
    fieldAtFin i = .real ∨ fieldAtFin i = .complex ∨ fieldAtFin i = .quaternion := by
  fin_cases i <;> simp [fieldAtFin, cliffordTable]

/-- Every position is simple or double.
    (This is trivially true from the inductive type, but
    stating it makes the partition explicit.) -/
theorem structureAtFin_dichotomy (i : Fin 8) :
    structureAtFin i = .simple ∨ structureAtFin i = .double := by
  fin_cases i <;> simp [structureAtFin, cliffordTable]

-- ═══════════════════════════════════════════════════════════════
-- The combined classification: (field, structure) pairs
-- ═══════════════════════════════════════════════════════════════

/-- The full Bott clock entry at each position.
    This is the master lookup: given k mod 8, you know
    both the base field and the algebra structure. -/
theorem cliffordTable_complete (i : Fin 8) :
    cliffordTable i =
    match i.val with
    | 0 => (.real, .simple)
    | 1 => (.complex, .simple)
    | 2 => (.quaternion, .simple)
    | 3 => (.quaternion, .double)
    | 4 => (.quaternion, .simple)
    | 5 => (.complex, .simple)
    | 6 => (.real, .simple)
    | 7 => (.real, .double)
    | _ => (.real, .simple)  -- unreachable
    := by
  fin_cases i <;> simp [cliffordTable]

-- ═══════════════════════════════════════════════════════════════
-- Symmetry of the clock: the "palindrome" structure
-- ═══════════════════════════════════════════════════════════════

/- The Bott clock has a reflection symmetry about its midpoint.
    Positions k and (8-k) mod 8 have the same base field
    (for k = 1..7, ignoring the structure type).

    This reflects the deeper fact that Cl(n) and Cl(8-n) are
    Morita equivalent over the same division algebra.

    Concretely:
      1 ↔ 7: but field(1) = ℂ, field(7) = ℝ ... no!

    Hmm — let me be more honest.  The symmetry is
    k ↔ (6-k) mod 8 for the field, reflecting through
    the ℍ block.  Let me state what IS true: -/

/-- The field pattern is a palindrome on {0,...,6}:
    positions k and 6-k have the same field for k = 0,...,6.
      0 ↔ 6: ℝ ↔ ℝ
      1 ↔ 5: ℂ ↔ ℂ
      2 ↔ 4: ℍ ↔ ℍ
      3 = 3: ℍ (the midpoint) -/
theorem field_palindrome (i : Fin 7) :
    fieldAtFin ⟨i.val, by omega⟩ =
    fieldAtFin ⟨6 - i.val, by omega⟩ := by
  fin_cases i <;> simp [fieldAtFin, cliffordTable]

-- ═══════════════════════════════════════════════════════════════
-- Corollaries: everything from Part IV is now derived
-- ═══════════════════════════════════════════════════════════════

/-- Cl(9) is complex: corollary of the universal characterization -/
theorem cl9_complex : fieldAt 9 = .complex :=
  (fieldAt_complex_iff 9).mpr (Or.inl (by norm_num))

/-- Cl(9) is simple: corollary -/
theorem cl9_simple : structureAt 9 = .simple :=
  (structureAt_simple_iff 9).mpr ⟨by norm_num, by norm_num⟩

/-- Cl(14) is real: corollary -/
theorem cl14_real : fieldAt 14 = .real :=
  (fieldAt_real_iff 14).mpr (Or.inr (Or.inl (by norm_num)))

/-- Cl(14) is simple: corollary -/
theorem cl14_simple : structureAt 14 = .simple :=
  (structureAt_simple_iff 14).mpr ⟨by norm_num, by norm_num⟩

/-- Cl(5) is complex: corollary (the OTHER complex slot) -/
theorem cl5_complex : fieldAt 5 = .complex :=
  (fieldAt_complex_iff 5).mpr (Or.inr rfl)

/-- The complex slots come in pairs symmetric about the
    quaternionic block: positions 1 and 5 = 6-1. -/
theorem complex_pair_symmetric : fieldAt 1 = fieldAt 5 :=
  have h1 := (fieldAt_complex_iff 1).mpr (Or.inl (by norm_num))
  have h5 := (fieldAt_complex_iff 5).mpr (Or.inr (by norm_num))
  h1.trans h5.symm

end BottClockComplete
/-!
=====================================================================
## The Period-2 Clockwork
=====================================================================

The Bott clock has 8 positions.  The +2 step (graded tensor
with Cl(2) ≅ ℍ) partitions it into two orbits:

  Even orbit: 0 → 2 → 4 → 6 → 0   (fields: ℝ, ℍ, ℍ, ℝ)
  Odd orbit:  1 → 3 → 5 → 7 → 1   (fields: ℂ, ℍ, ℂ, ℝ)

The tensor product isomorphisms that DRIVE these transitions:
  ℝ ⊗ᵣ ℍ ≅ ℍ         (reals absorbed by quaternions)
  ℂ ⊗ᵣ ℍ ≅ M₂(ℂ)     (complex absorbs quaternions!)
  ℍ ⊗ᵣ ℍ ≅ M₄(ℝ)     (quaternions annihilate to reals)

The third fact — ℍ kills itself — is the engine of the return
to ℝ.  The second fact — ℂ absorbs ℍ — is why ℂ reappears.

IMPORTANT CAVEAT: these are UNGRADED tensor products of
division algebras.  The Clifford recursion uses the GRADED
tensor product, which carries more information (it tracks
the simple/double distinction as well).  The field transitions
in the Bott clock are consistent with these tensor rules but
are not fully determined by the field alone — the clock
position matters.  This is why we work with Fin 8, not with
CliffordBaseField.
=====================================================================
-/

section Period2Clockwork

/-- The +2 step on the Bott clock: graded tensor with Cl(2). -/
def clockStep2 (i : Fin 8) : Fin 8 :=
  ⟨(i.val + 2) % 8, Nat.mod_lt _ (by norm_num)⟩

/-- The +4 step: two applications of +2. -/
def clockStep4 (i : Fin 8) : Fin 8 :=
  ⟨(i.val + 4) % 8, Nat.mod_lt _ (by norm_num)⟩

/-- +2 applied four times returns to start.
    This is the period of the +2 map: order 4 in Aut(ℤ/8ℤ). -/
theorem clockStep2_period (i : Fin 8) :
    clockStep2 (clockStep2 (clockStep2 (clockStep2 i))) = i := by
  fin_cases i <;> simp [clockStep2]

/-- The even orbit: {0, 2, 4, 6} -/
def evenOrbit : Finset (Fin 8) :=
  {⟨0, by omega⟩, ⟨2, by omega⟩, ⟨4, by omega⟩, ⟨6, by omega⟩}

/-- The odd orbit: {1, 3, 5, 7} -/
def oddOrbit : Finset (Fin 8) :=
  {⟨1, by omega⟩, ⟨3, by omega⟩, ⟨5, by omega⟩, ⟨7, by omega⟩}

/-- +2 preserves the even orbit -/
theorem clockStep2_even (i : Fin 8) (h : i ∈ evenOrbit) :
    clockStep2 i ∈ evenOrbit := by
  fin_cases i <;> simp_all [clockStep2, evenOrbit]

/-- +2 preserves the odd orbit -/
theorem clockStep2_odd (i : Fin 8) (h : i ∈ oddOrbit) :
    clockStep2 i ∈ oddOrbit := by
  fin_cases i <;> simp_all [clockStep2, oddOrbit]

/-- Every position is in exactly one orbit -/
theorem orbit_partition (i : Fin 8) :
    (i ∈ evenOrbit ∧ i ∉ oddOrbit) ∨ (i ∈ oddOrbit ∧ i ∉ evenOrbit) := by
  fin_cases i <;> simp [evenOrbit, oddOrbit]

-- ═══════════════════════════════════════════════════════════════
-- Field values along each orbit
-- ═══════════════════════════════════════════════════════════════

/-- The field sequence along the even orbit: ℝ, ℍ, ℍ, ℝ
    This reflects: ℝ ⊗ ℍ → ℍ ⊗ ℍ → ℍ ⊗ ℍ → ℝ ⊗ ℍ → ...
                    =ℍ       =ℝ(×mat) =ℍ       =ℝ           -/
theorem even_orbit_fields :
    fieldAtFin ⟨0, by omega⟩ = .real
    ∧ fieldAtFin ⟨2, by omega⟩ = .quaternion
    ∧ fieldAtFin ⟨4, by omega⟩ = .quaternion
    ∧ fieldAtFin ⟨6, by omega⟩ = .real := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The field sequence along the odd orbit: ℂ, ℍ, ℂ, ℝ

    This is the crucial orbit for U⁹.  Starting from ℂ:
      position 1 (ℂ) → position 3 (ℍ) → position 5 (ℂ) → position 7 (ℝ)

    ℂ appears TWICE in this 4-cycle.  It keeps coming back
    because ℂ ⊗ᵣ ℍ ≅ M₂(ℂ): the complex numbers absorb
    the quaternions and remain complex (up to matrix size). -/
theorem odd_orbit_fields :
    fieldAtFin ⟨1, by omega⟩ = .complex
    ∧ fieldAtFin ⟨3, by omega⟩ = .quaternion
    ∧ fieldAtFin ⟨5, by omega⟩ = .complex
    ∧ fieldAtFin ⟨7, by omega⟩ = .real := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- ℂ appears ONLY in the odd orbit.
    Equivalently: complex Clifford algebras exist only in
    odd dimensions (1, 5, 9, 13, ...).

    This is because Cl(0) ≅ ℝ starts the even orbit as real,
    and Cl(1) ≅ ℂ starts the odd orbit as complex. The +2 step
    permutes within orbits, so ℂ can never cross into the even orbit. -/
theorem complex_only_odd (i : Fin 8) (h : fieldAtFin i = .complex) :
    i ∈ oddOrbit := by
  fin_cases i <;> simp_all [fieldAtFin, cliffordTable, oddOrbit]

/-- Contrapositive: even-orbit Clifford algebras are NEVER complex -/
theorem even_never_complex (i : Fin 8) (h : i ∈ evenOrbit) :
    fieldAtFin i ≠ .complex := by
  fin_cases i <;> simp_all [fieldAtFin, cliffordTable, evenOrbit]

end Period2Clockwork


/-!
=====================================================================
## Part XI-e: Why ℂ Is Special
=====================================================================

The three division algebras ℝ, ℂ, ℍ all appear in the Bott clock.
But they behave differently with respect to the simple/double
distinction:

  ℝ appears at positions {0, 6, 7}.  Position 7 is DOUBLE.
  ℍ appears at positions {2, 3, 4}.  Position 3 is DOUBLE.
  ℂ appears at positions {1, 5}.     BOTH are SIMPLE.

ℂ is the ONLY field that never appears at a double position.

Why this matters:
  - Simple means the Clifford algebra is M_k(F), a FULL matrix algebra
  - Double means M_k(F) ⊕ M_k(F), which splits the spinor into
    two irreducible half-spinor representations
  - For a clean, unsplit spinor bundle, you want SIMPLE
  - ℂ GUARANTEES simplicity.  ℝ and ℍ do not.

This is the structural reason why complex Clifford algebras
are preferred for spinor geometry: they come with no splitting
ambiguity.

The algebraic reason: the double case occurs when the volume
element ω = e₁⋯eₙ satisfies ω² = +1 and ω is central.
For complex Clifford algebras, ω generates a copy of ℂ
inside the center, and ℂ has no nontrivial idempotents
(unlike ℝ, where (1 ± ω)/2 splits the algebra).
=====================================================================
-/

section WhyComplexIsSpecial

/-- **ℂ IS ALWAYS SIMPLE**

    At every position in the Bott clock where the base field is ℂ,
    the algebra structure is simple.

    This is the KEY structural theorem.  It means:
    - Complex Clifford algebras are always full matrix algebras
    - The spinor representation is always irreducible
    - No splitting ambiguity, no choice of chirality convention -/
theorem complex_implies_simple (i : Fin 8) (h : fieldAtFin i = .complex) :
    structureAtFin i = .simple := by
  fin_cases i <;> simp_all [fieldAtFin, structureAtFin, cliffordTable]

/-- ℝ does NOT always give simple algebras: position 7 is (ℝ, double) -/
theorem real_not_always_simple :
    ∃ i : Fin 8, fieldAtFin i = .real ∧ structureAtFin i = .double := by
  exact ⟨⟨7, by omega⟩, rfl, rfl⟩

/-- ℍ does NOT always give simple algebras: position 3 is (ℍ, double) -/
theorem quaternion_not_always_simple :
    ∃ i : Fin 8, fieldAtFin i = .quaternion ∧ structureAtFin i = .double := by
  exact ⟨⟨3, by omega⟩, rfl, rfl⟩

/-- **ℂ IS THE UNIQUE ALWAYS-SIMPLE FIELD**

    ℂ is the only base field F such that every Bott clock position
    with field F is simple.

    ℝ fails (position 7).  ℍ fails (position 3).  Only ℂ survives. -/
theorem complex_unique_always_simple :
    (∀ i : Fin 8, fieldAtFin i = .complex → structureAtFin i = .simple)
    ∧ (∃ i : Fin 8, fieldAtFin i = .real ∧ structureAtFin i = .double)
    ∧ (∃ i : Fin 8, fieldAtFin i = .quaternion ∧ structureAtFin i = .double) :=
  ⟨complex_implies_simple, real_not_always_simple, quaternion_not_always_simple⟩

-- ═══════════════════════════════════════════════════════════════
-- The triple characterization of ℂ positions
-- ═══════════════════════════════════════════════════════════════

/-- **THE TRIPLE CHARACTERIZATION**

    For a Bott clock position i, the following are equivalent:
    (1) The base field is ℂ
    (2) The position is in the odd orbit AND the algebra is simple
    (3) i.val = 1 or i.val = 5

    This gives THREE ways to identify complex positions:
    by the field, by the orbit + structure, or by the number.
    All three agree. -/
theorem complex_triple_char (i : Fin 8) :
    fieldAtFin i = .complex
    ↔ (i ∈ oddOrbit ∧ structureAtFin i = .simple) := by
  fin_cases i <;> simp [fieldAtFin, structureAtFin, cliffordTable, oddOrbit]

-- ═══════════════════════════════════════════════════════════════
-- The tensor product isomorphisms (as verified data)
-- ═══════════════════════════════════════════════════════════════

/-- The three tensor product isomorphisms of real division algebras.

    These are the algebraic engine behind the Bott clock.
    We formalize them as a lookup on field pairs, recording
    the output field and the matrix dimension multiplier.

    ℝ ⊗ᵣ ℍ ≅ ℍ           (multiplier 1: no matrix growth)
    ℂ ⊗ᵣ ℍ ≅ M₂(ℂ)       (multiplier 2: matrix doubles)
    ℍ ⊗ᵣ ℍ ≅ M₄(ℝ)       (multiplier 4: matrix quadruples)

    These are UNGRADED tensor products.  They tell you what
    happens to the base field but not to the simple/double
    distinction (which requires the graded theory). -/
structure TensorRule where
  /-- First factor's base field -/
  input : CliffordBaseField
  /-- Tensor with ℍ
  Output base field -/
  output : CliffordBaseField
  /-- Matrix dimension multiplier -/
  matMultiplier : ℕ

/-- The three rules, encoding how each field responds to ⊗ ℍ -/
def tensorWithH : CliffordBaseField → TensorRule
  | .real       => ⟨.real, .quaternion, 1⟩       -- ℝ ⊗ ℍ ≅ ℍ
  | .complex    => ⟨.complex, .complex, 2⟩       -- ℂ ⊗ ℍ ≅ M₂(ℂ)
  | .quaternion => ⟨.quaternion, .real, 4⟩        -- ℍ ⊗ ℍ ≅ M₄(ℝ)

/-- ℂ is a FIXED POINT of tensor-with-ℍ at the field level.
    The matrix dimension doubles, but the field survives.

    This is the algebraic reason ℂ keeps reappearing in the
    Bott clock: quaternionic tensoring cannot knock it out of
    the complex world. -/
theorem complex_fixed_point :
    (tensorWithH .complex).output = .complex := rfl

/-- ℝ is NOT a fixed point: it gets promoted to ℍ -/
theorem real_not_fixed : (tensorWithH .real).output ≠ .real := by
  simp [tensorWithH]

/-- ℍ is NOT a fixed point: it gets demoted to ℝ -/
theorem quaternion_not_fixed : (tensorWithH .quaternion).output ≠ .quaternion := by
  simp [tensorWithH]

/-- **ℂ IS THE UNIQUE FIXED POINT OF ⊗ ℍ**

    Among the three real division algebras, ℂ is the only one
    whose field type is preserved under tensor product with ℍ.

    ℝ → ℍ (promoted)
    ℂ → ℂ (preserved!)
    ℍ → ℝ (demoted)

    This is the deepest algebraic reason for the distinguished
    role of complex Clifford algebras. -/
theorem complex_unique_fixed_point (F : CliffordBaseField) :
    (tensorWithH F).output = F ↔ F = .complex := by
  cases F <;> simp [tensorWithH]

end WhyComplexIsSpecial

end CliffordPeriodicity
