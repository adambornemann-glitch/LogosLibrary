/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: CliffordPeriodicity/Table.lean
-/
import LogosLibrary.Superior.CommonResources.CliffordPeriodicity.Basic
/-!
=====================================================================
## The Bott Periodicity Table
=====================================================================

The classification function: given n, return the CliffordData.

The table is the 8-fold periodic classification of Cl(n,0),
extended to arbitrary n via the periodicity Cl(n+8) ≅ Cl(n) ⊗ M₁₆(ℝ).

We define it explicitly for n = 0, ..., 9 (covering one full period
plus our target dimension), then provide the general recipe.

    **Sign convention (used throughout this file):**
    We define Cl(n) = Cl(n,0) with the NEGATIVE-DEFINITE relation
    v · v = -Q(v), so that e_i² = -1 for each basis vector.
    This is the geometric algebra / differential geometry convention.

    Under the positive-definite convention (v · v = +Q(v)), one gets
    Cl(1,0) ≅ ℝ ⊕ ℝ instead — the split complex numbers, projected
    by the idempotents (1 ± e₁)/2.  The positive-definite table is
    related to ours by the conjugation n ↦ (8 − n) mod 8 — the
    Möbius twist of the Bott clock (see Mobius.lean).  In particular,
    the two conventions swap the complex positions (1, 5) with the
    double positions (7, 3).  We use the negative-definite convention
    throughout.

    With our convention: the algebra {a + be₁ : a, b ∈ ℝ} with
    e₁² = -1 is precisely ℂ, via e₁ ↦ i.  The spinor is a single
    complex number.

-/
namespace CliffordPeriodicity
section PeriodicityTable
/-- Cl(0) ≅ ℝ = M₁(ℝ)

    The trivial Clifford algebra.  Zero generators, one element.
    The spinor is a single real number. -/
def cl0 : CliffordData where
  n := 0
  baseField := .real
  matDim := 1
  algStructure := .simple
  realDim := 1
  spinorDim := 1
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(1) ≅ ℂ = M₁(ℂ)

    One generator e₁ with e₁² = -1.

    This is the BASE CASE for the complex slot of the periodicity
    table.  Cl(9) ≅ M₁₆(ℂ) inherits its complex structure from
    this very fact, via Cl(9) ≅ Cl(1) ⊗ M₁₆(ℝ). -/
def cl1 : CliffordData where
  n := 1
  baseField := .complex
  matDim := 1
  algStructure := .simple
  realDim := 2
  spinorDim := 1
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(2) ≅ ℍ = M₁(ℍ)

    Two generators e₁, e₂ with e₁² = e₂² = -1, e₁e₂ = -e₂e₁.
    Set 𝐢 = e₁, 𝐣 = e₂, 𝐤 = e₁e₂.  This IS the quaternion algebra.

    The spinor is a single quaternion. -/
def cl2 : CliffordData where
  n := 2
  baseField := .quaternion
  matDim := 1
  algStructure := .simple
  realDim := 4
  spinorDim := 1
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(3) ≅ ℍ ⊕ ℍ = M₁(ℍ)²

    The first DOUBLE case.  The algebra splits into two copies
    of ℍ, projected by (1 ± e₁e₂e₃)/2.

    This is n ≡ 3 mod 8 — the first occurrence of the split. -/
def cl3 : CliffordData where
  n := 3
  baseField := .quaternion
  matDim := 1
  algStructure := .double
  realDim := 8
  spinorDim := 1
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(4) ≅ M₂(ℍ)

    The spinor is now a PAIR of quaternions — a 2-vector over ℍ.
    This is the first case where the matrix dimension exceeds 1. -/
def cl4 : CliffordData where
  n := 4
  baseField := .quaternion
  matDim := 2
  algStructure := .simple
  realDim := 16
  spinorDim := 2
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(5) ≅ M₄(ℂ)

    Back to complex!  The spinor is ℂ⁴.

    Note: the physicists' Dirac algebra is also M₄(ℂ), but it arises
    differently.  The REAL Clifford algebra Cl(1,3) ≅ M₄(ℝ) (ABS
    index 6, a real slot), and Cl(3,1) ≅ M₂(ℍ) (ABS index 2,
    quaternionic).  The physicists obtain M₄(ℂ) by COMPLEXIFYING:
    M₄(ℝ) ⊗ ℂ ≅ M₄(ℂ) or M₂(ℍ) ⊗ ℂ ≅ M₄(ℂ).

    Here, Cl(5,0) achieves M₄(ℂ) intrinsically — no complexification
    needed.  This is the same distinction that makes Cl(9) special:
    the complex structure is BUILT IN, not imposed from outside. -/
def cl5 : CliffordData where
  n := 5
  baseField := .complex
  matDim := 4
  algStructure := .simple
  realDim := 32
  spinorDim := 4
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(6) ≅ M₈(ℝ)

    Back to real.  The spinor is ℝ⁸ — an 8-dimensional real
    representation, the same dimension as the octonions.

    The deeper connection to 8-dimensional exceptionality emerges
    two steps later: the even subalgebra Cl⁰(8) ≅ Cl(7) ≅ M₈(ℝ)²
    splits into two 8-dimensional half-spinor representations, and
    Spin(8) acts on three 8-dimensional spaces (vector, S⁺, S⁻)
    related by triality.  The ℝ⁸ here at Cl(6) is a precursor,
    reflecting Spin(6) ≅ SU(4) and its 4-dimensional complex
    (= 8-dimensional real) spinor representation. -/
def cl6 : CliffordData where
  n := 6
  baseField := .real
  matDim := 8
  algStructure := .simple
  realDim := 64
  spinorDim := 8
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(7) ≅ M₈(ℝ) ⊕ M₈(ℝ) = M₈(ℝ)²

    The second DOUBLE case (n ≡ 7 mod 8). -/
def cl7 : CliffordData where
  n := 7
  baseField := .real
  matDim := 8
  algStructure := .double
  realDim := 128
  spinorDim := 8
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(8) ≅ M₁₆(ℝ)

    THE PERIOD.  Cl(8) ≅ M₁₆(ℝ), and the periodicity theorem says
    Cl(n+8) ≅ Cl(n) ⊗ M₁₆(ℝ).  So the table repeats with matrix
    dimensions multiplied by 16. -/
def cl8 : CliffordData where
  n := 8
  baseField := .real
  matDim := 16
  algStructure := .simple
  realDim := 256
  spinorDim := 16
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- **Cl(9) ≅ M₁₆(ℂ)**

    THE KEY THEOREM FOR U⁹.

    9 mod 8 = 1, same slot as Cl(1) ≅ ℂ.
    Periodicity: Cl(9) ≅ Cl(1) ⊗ M₁₆(ℝ) ≅ ℂ ⊗ M₁₆(ℝ) ≅ M₁₆(ℂ).

    The spinor is ℂ¹⁶.  Sixteen complex dimensions.
    The structure group is U(16).

    **The Clifford algebra of the chimeric bundle is intrinsically complex.**

    This is what makes the shiab operator work without complexification.
    This is what Nguyen missed in 14 dimensions (where Cl(14) ≅ M₁₂₈(ℝ)
    is REAL and you DO need to complexify by hand).

    In 9 dimensions, the algebra hands you complex structure for free. -/
def cl9 : CliffordData where
  n := 9
  baseField := .complex
  matDim := 16
  algStructure := .simple
  realDim := 512
  spinorDim := 16
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(10) ≅ M₁₆(ℍ)

    10 mod 8 = 2, same slot as Cl(2) ≅ ℍ.
    Periodicity: Cl(10) ≅ Cl(2) ⊗ M₁₆(ℝ) ≅ ℍ ⊗ M₁₆(ℝ) ≅ M₁₆(ℍ).
    The spinor is ℍ¹⁶.  Structure group Sp(16). -/
def cl10 : CliffordData where
  n := 10
  baseField := .quaternion
  matDim := 16
  algStructure := .simple
  realDim := 1024
  spinorDim := 16
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(11) ≅ M₁₆(ℍ) ⊕ M₁₆(ℍ)

    11 mod 8 = 3, the first double-quaternionic slot in the second period.
    Periodicity: Cl(11) ≅ Cl(3) ⊗ M₁₆(ℝ). -/
def cl11 : CliffordData where
  n := 11
  baseField := .quaternion
  matDim := 16
  algStructure := .double
  realDim := 2048
  spinorDim := 16
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(12) ≅ M₃₂(ℍ)

    12 mod 8 = 4, same slot as Cl(4) ≅ M₂(ℍ).
    Periodicity: Cl(12) ≅ Cl(4) ⊗ M₁₆(ℝ) ≅ M₂(ℍ) ⊗ M₁₆(ℝ) ≅ M₃₂(ℍ).
    The spinor is ℍ³².  Structure group Sp(32). -/
def cl12 : CliffordData where
  n := 12
  baseField := .quaternion
  matDim := 32
  algStructure := .simple
  realDim := 4096
  spinorDim := 32
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(13) ≅ M₆₄(ℂ)

    13 mod 8 = 5, same slot as Cl(5) ≅ M₄(ℂ).
    Periodicity: Cl(13) ≅ Cl(5) ⊗ M₁₆(ℝ) ≅ M₄(ℂ) ⊗ M₁₆(ℝ) ≅ M₆₄(ℂ).
    The spinor is ℂ⁶⁴.  Structure group U(64).

    Like Cl(9), intrinsically complex — but 64-dimensional spinors
    instead of 16.  This is what you'd get in 13 dimensions. -/
def cl13 : CliffordData where
  n := 13
  baseField := .complex
  matDim := 64
  algStructure := .simple
  realDim := 8192
  spinorDim := 64
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(14) ≅ M₁₂₈(ℝ)

    14 mod 8 = 6, same slot as Cl(6) ≅ M₈(ℝ).
    Periodicity: Cl(14) ≅ Cl(6) ⊗ M₁₆(ℝ) ≅ M₈(ℝ) ⊗ M₁₆(ℝ) ≅ M₁₂₈(ℝ).
    The spinor is ℝ¹²⁸.  Structure group O(128).

    **This is Nguyen's 14-dimensional case.**  The algebra is REAL.
    To get complex structure you must complexify by hand:
    M₁₂₈(ℝ) ⊗ ℂ ≅ M₁₂₈(ℂ).  That is an external choice, not
    forced by the algebra.  Contrast with Cl(9) where ℂ is built in. -/
def cl14 : CliffordData where
  n := 14
  baseField := .real
  matDim := 128
  algStructure := .simple
  realDim := 16384
  spinorDim := 128
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- Cl(15) ≅ M₁₂₈(ℝ) ⊕ M₁₂₈(ℝ)

    15 mod 8 = 7, the double-real slot.
    Periodicity: Cl(15) ≅ Cl(7) ⊗ M₁₆(ℝ).  Still real, still split. -/
def cl15 : CliffordData where
  n := 15
  baseField := .real
  matDim := 128
  algStructure := .double
  realDim := 32768
  spinorDim := 128
  hRealDim := by norm_num
  hSpinorDim := rfl
  hDimCheck := by simp [CliffordBaseField.dim]

/-- The periodicity table as a function on the base period -/
def cliffordTable : Fin 8 → CliffordBaseField × CliffordAlgStructure
  | ⟨0, _⟩ => (.real, .simple)
  | ⟨1, _⟩ => (.complex, .simple)
  | ⟨2, _⟩ => (.quaternion, .simple)
  | ⟨3, _⟩ => (.quaternion, .double)
  | ⟨4, _⟩ => (.quaternion, .simple)
  | ⟨5, _⟩ => (.complex, .simple)
  | ⟨6, _⟩ => (.real, .simple)
  | ⟨7, _⟩ => (.real, .double)


/-- The period-8 step: Cl(n+8) ≅ Cl(n) ⊗_ℝ M₁₆(ℝ).

    Tensoring with M₁₆(ℝ) multiplies the matrix dimension by 16,
    the real dimension by 256 = 16², and preserves both the base
    field and the simple/double structure.

    The consistency conditions (hRealDim, hSpinorDim, hDimCheck)
    force Lean to verify the dimensional accounting of the tensor
    product.  In particular, hDimCheck handles both:
      • Simple:  F.dim · (16k)² = 256 · F.dim · k²
      • Double:  2 · F.dim · (16k)² = 256 · 2 · F.dim · k²

    This makes the periodicity a *function on types* rather than
    a pattern observed across separate definitions.

    Example: `cliffordStep cl1` produces Cl(9) ≅ M₁₆(ℂ), and
    the theorem `cliffordStep cl1 = cl9` verifies this agrees
    with the hand-written classification. -/
def cliffordStep (d : CliffordData) : CliffordData where
  n := d.n + 8
  baseField := d.baseField
  matDim := 16 * d.matDim
  algStructure := d.algStructure
  realDim := 256 * d.realDim
  spinorDim := 16 * d.spinorDim
  hRealDim := by
    ring_nf; simp only [mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false]
    exact d.hRealDim
  hSpinorDim := by
    ring_nf
    simp only [mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false]
    exact d.hSpinorDim
  hDimCheck := by
    have h := d.hDimCheck
    revert h
    cases d.algStructure <;> intro h <;> rw [h] <;> ring



/-- Cl(8) is generated from Cl(0) by the period-8 step:
    Cl(8) ≅ Cl(0) ⊗ M₁₆(ℝ) ≅ ℝ ⊗ M₁₆ -/
theorem cl8_from_cl0 : cliffordStep cl0 = cl8 := rfl

/-- Cl(9) is generated from Cl(1) by the period-8 step:
    Cl(9) ≅ Cl(1) ⊗ M₁₆(ℝ) ≅ ℂ ⊗ M₁₆(ℝ) ≅ M₁₆(ℂ).
    The complex base field of Cl(1) is preserved — this is why
    Cl(9) is intrinsically complex. -/
theorem cl9_from_cl1 : cliffordStep cl1 = cl9 := rfl

/-- Cl(10) is generated from Cl(2) by the period-8 step:
    Cl(10) ≅ Cl(2) ⊗ M₁₆(ℝ) ≅ ℍ ⊗ M₁₆(ℝ) ≅ M₁₆(ℍ). -/
theorem cl10_from_cl2 : cliffordStep cl2 = cl10 := rfl

/-- Cl(11) is generated from Cl(3) by the period-8 step:
    Cl(11) ≅ Cl(3) ⊗ M₁₆(ℝ) ≅ (ℍ ⊕ ℍ) ⊗ M₁₆(ℝ) ≅ M₁₆(ℍ) ⊕ M₁₆(ℍ).
    The double structure of Cl(3) is preserved. -/
theorem cl11_from_cl3 : cliffordStep cl3 = cl11 := rfl

/-- Cl(12) is generated from Cl(4) by the period-8 step:
    Cl(12) ≅ Cl(4) ⊗ M₁₆(ℝ) ≅ M₂(ℍ) ⊗ M₁₆(ℝ) ≅ M₃₂(ℍ). -/
theorem cl12_from_cl4 : cliffordStep cl4 = cl12 := rfl

/-- Cl(13) is generated from Cl(5) by the period-8 step:
    Cl(13) ≅ Cl(5) ⊗ M₁₆(ℝ) ≅ M₄(ℂ) ⊗ M₁₆(ℝ) ≅ M₆₄(ℂ). -/
theorem cl13_from_cl5 : cliffordStep cl5 = cl13 := rfl

/-- Cl(14) is generated from Cl(6) by the period-8 step:
    Cl(14) ≅ Cl(6) ⊗ M₁₆(ℝ) ≅ M₈(ℝ) ⊗ M₁₆(ℝ) ≅ M₁₂₈(ℝ).
    The real base field of Cl(6) is preserved — this is why
    Cl(14) is NOT intrinsically complex, and why the shiab
    operator requires ad hoc complexification in 14 dimensions. -/
theorem cl14_from_cl6 : cliffordStep cl6 = cl14 := rfl

/-- Cl(15) is generated from Cl(7) by the period-8 step:
    Cl(15) ≅ Cl(7) ⊗ M₁₆(ℝ) ≅ (M₈(ℝ) ⊕ M₈(ℝ)) ⊗ M₁₆(ℝ) ≅ M₁₂₈(ℝ) ⊕ M₁₂₈(ℝ).
    The double structure of Cl(7) is preserved. -/
theorem cl15_from_cl7 : cliffordStep cl7 = cl15 := rfl

end PeriodicityTable

end CliffordPeriodicity
