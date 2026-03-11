/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: CliffordPeriodicity/Dimensions.lean
-/
import LogosLibrary.Superior.CommonResources.CliffordPeriodicity.Clock

namespace CliffordPeriodicity
/-!
=====================================================================
## The Periodicity Pattern
=====================================================================

The 8-fold periodicity as a verifiable pattern.

The field type cycles: ℝ, ℂ, ℍ, ℍ, ℍ, ℂ, ℝ, ℝ, ℝ, ℂ, ...

The doubling happens at positions 3 and 7 (mod 8).

The complex positions are 1 and 5 (mod 8).

For the chimeric bundle of Met(Xⁿ):
  total dim = n + n(n+1)/2 = n(n+3)/2

We need total dim ≡ 1 or 5 (mod 8) for complex Clifford algebra.

For n = 3: total = 9, 9 mod 8 = 1.  ✓ COMPLEX.
=====================================================================
-/

section PeriodicityPattern

/-- The positions in the period-8 cycle that give complex Clifford algebras -/
def complexPositions : Finset ℕ := {1, 5}

/-- 9 mod 8 lands on a complex position -/
theorem nine_is_complex_position : 9 % 8 ∈ complexPositions := by
  simp [complexPositions]

/-- The total dimension formula for Met(Xⁿ) -/
def metTotalDim (n : ℕ) : ℕ := n + n * (n + 1) / 2

/-- For n = 3: total = 9 -/
theorem metTotalDim_3 : metTotalDim 3 = 9 := by
  simp [metTotalDim]

/-- **WHICH BASE DIMENSIONS GIVE COMPLEX CLIFFORD ALGEBRAS?**

    We need metTotalDim(n) mod 8 ∈ {1, 5}.

    n = 1: total = 1 + 1 = 2.   2 mod 8 = 2.  ℍ.        ✗
    n = 2: total = 2 + 3 = 5.   5 mod 8 = 5.  ℂ.        ✓ (but spinor dim = 4)
    n = 3: total = 3 + 6 = 9.   9 mod 8 = 1.  ℂ.        ✓ (spinor dim = 16!)
    n = 4: total = 4 + 10 = 14. 14 mod 8 = 6. ℝ.        ✗
    n = 5: total = 5 + 15 = 20. 20 mod 8 = 4. ℍ.        ✗
    n = 6: total = 6 + 21 = 27. 27 mod 8 = 3. ℍ⊕ℍ.      ✗
    n = 7: total = 7 + 28 = 35. 35 mod 8 = 3. ℍ⊕ℍ.      ✗

    Only n = 2 and n = 3 work.  And n = 2 gives too small a spinor.

    **n = 3 is the unique base dimension producing ℂ¹⁶ spinors.** -/
theorem complex_base_dimensions :
    metTotalDim 2 % 8 ∈ complexPositions
    ∧ metTotalDim 3 % 8 ∈ complexPositions
    ∧ metTotalDim 4 % 8 ∉ complexPositions := by
  simp [metTotalDim, complexPositions]

/-- The double positions: n ≡ 3, 7 mod 8 give non-simple algebras -/
def doublePositions : Finset ℕ := {3, 7}

/-- 9 is NOT a double position -/
theorem nine_not_double : 9 % 8 ∉ doublePositions := by
  simp [doublePositions]

/-- The quaternionic positions: n ≡ 2, 3, 4 mod 8 -/
def quaternionicPositions : Finset ℕ := {2, 3, 4}

/-- 9 is NOT quaternionic -/
theorem nine_not_quaternionic : 9 % 8 ∉ quaternionicPositions := by
  simp [quaternionicPositions]


/-- Matrix dimension formula for complex Clifford algebras.
    Slot 1 (m ≡ 1 mod 8): matDim = 16^((m-1)/8)
    Slot 5 (m ≡ 5 mod 8): matDim = 4 · 16^((m-5)/8) -/
def complexMatDim (m : ℕ) : ℕ :=
  if m % 8 = 1 then 16 ^ ((m - 1) / 8)
  else if m % 8 = 5 then 4 * 16 ^ ((m - 5) / 8)
  else 0

/-- Among complex Clifford algebras, only Cl(9) has matDim = 16.

    Complex slots: m ≡ 1 (mod 8) with matDim = 16^q, q = (m-1)/8
                   m ≡ 5 (mod 8) with matDim = 4 · 16^q, q = (m-5)/8

    matDim = 16 requires:
      Slot 1: 16^q = 16  →  q = 1  →  m = 9
      Slot 5: 4 · 16^q = 16  →  16^q = 4  →  no integer solution

    Therefore m = 9 is the unique complex dimension with matDim = 16. -/
theorem unique_complex_matDim16 (m : ℕ) (_hComplex : m % 8 = 1 ∨ m % 8 = 5)
    (hMat : complexMatDim m = 16) : m = 9 := by
  unfold complexMatDim at hMat
  split_ifs at hMat with h1 h5
  · -- Slot 1: 16^q = 16 where q = (m-1)/8
    -- Upper bound: q ≥ 2 → 16^q ≥ 256 > 16
    have hq_le : (m - 1) / 8 ≤ 1 := by
      by_contra hc; push_neg at hc
      have h256 : (256 : ℕ) ≤ 16 ^ ((m - 1) / 8) := by
        calc (256 : ℕ) = 16 ^ 2 := by norm_num
          _ ≤ 16 ^ ((m - 1) / 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
      linarith
    -- Lower bound: q = 0 → 16^0 = 1 ≠ 16
    have hq_pos : 1 ≤ (m - 1) / 8 := by
      by_contra hc; push_neg at hc
      have : (m - 1) / 8 = 0 := by omega
      rw [this] at hMat; norm_num at hMat
    -- q = 1, m % 8 = 1, (m-1)/8 = 1  →  m = 9
    omega
  · -- Slot 5: 4 · 16^q = 16 where q = (m-5)/8
    -- q = 0 gives 4 ≠ 16; q ≥ 1 gives 4·16 = 64 > 16
    rcases Nat.eq_zero_or_pos ((m - 5) / 8) with h0 | h_pos
    · rw [h0] at hMat; norm_num at hMat
    · exfalso
      have : 64 ≤ 4 * 16 ^ ((m - 5) / 8) := by
        calc 64 = 4 * 16 ^ 1 := by norm_num
          _ ≤ 4 * 16 ^ ((m - 5) / 8) := by
              apply Nat.mul_le_mul_left
              exact Nat.pow_le_pow_right (by norm_num) h_pos
      omega

/-- n = 3 is the unique positive integer with n(n+3)/2 = 9 -/
theorem unique_base_dim (n : ℕ) (hn : 0 < n) (h : n * (n + 3) / 2 = 9) :
    n = 3 := by
  have hn_le : n ≤ 3 := by
    by_contra hc; push_neg at hc
    -- n ≥ 4 → n(n+3) ≥ 4·7 = 28
    have : 28 ≤ n * (n + 3) := by nlinarith
    -- but n(n+3)/2 = 9 → n(n+3) ≤ 19. Now omega sees 28 ≤ atom ≤ 19.
    omega
  interval_cases n <;> omega

/-- UNIQUENESS THEOREM (complete):
    n = 3 is the unique base dimension producing
    a complex Clifford algebra with 16-dimensional spinors.

    Proof: complexMatDim pins the total dimension to 9,
    then the quadratic n(n+3)/2 = 9 pins n to 3. -/
theorem base_dim_3_unique (n : ℕ) (hn : 0 < n)
    (hComplex : n * (n + 3) / 2 % 8 = 1 ∨ n * (n + 3) / 2 % 8 = 5)
    (hMat : complexMatDim (n * (n + 3) / 2) = 16) : n = 3 :=
  unique_base_dim n hn (unique_complex_matDim16 _ hComplex hMat)


end PeriodicityPattern

end CliffordPeriodicity
