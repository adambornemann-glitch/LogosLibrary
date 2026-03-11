/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: CliffordPeriodicity/Basic.lean
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
/-!
=====================================================================
# CLIFFORD PERIODICITY AND THE Cl(9) ISOMORPHISM
=====================================================================
Via the Curry-Howard method...
because the real thing would melt your computer.

## Overview

The 8-fold periodicity of real Clifford algebras (Bott periodicity)
classifies Cl(n,0) — the Clifford algebra of ℝⁿ with positive-definite
inner product — in terms of matrix algebras over ℝ, ℂ, or ℍ.

## The Key Result

**Cl(9,0) ≅ M₁₆(ℂ)**

Dimension 9 with Riemannian (all-positive) signature produces a
*complex* matrix algebra by the periodicity theorem.  The Clifford
algebra is intrinsically complex.  No complexification needed.

This is not a choice.  It is forced by the periodicity:
  Cl(1,0) ≅ ℂ         (the base case)
  Cl(n+8) ≅ Cl(n) ⊗ M₁₆(ℝ)  (the period-8 step)
  Cl(9)   ≅ ℂ ⊗ M₁₆(ℝ) ≅ M₁₆(ℂ)   (composition)

## Consequences for U⁹

From Cl(9) ≅ M₁₆(ℂ), everything follows:

  1. Spinor fiber = ℂ¹⁶ (16 complex dimensions)
  2. Structure group = U(16) (unitary, not orthogonal)
  3. Hermitian decomposition: M₁₆(ℂ) = u(16) ⊕ iu(16)
  4. The shiab operator ε maps through u(16) naturally
  5. The gauge field action Tr(F ∧ ε(F)) is well-defined

## The Periodicity Table

    n mod 8 │ Cl(n,0)              │ Field │ Matrix Dim  │ Type
    ────────┼──────────────────────┼───────┼─────────────┼────────
       0    │ M_k(ℝ)               │ ℝ     │ 2^(n/2)     │ Simple
       1    │ M_k(ℂ)               │ ℂ     │ 2^((n-1)/2) │ Simple
       2    │ M_k(ℍ)               │ ℍ     │ 2^((n-2)/2) │ Simple
       3    │ M_k(ℍ) ⊕ M_k(ℍ)      │ ℍ     │ 2^((n-3)/2) │ Double
       4    │ M_k(ℍ)               │ ℍ     │ 2^((n-2)/2) │ Simple
       5    │ M_k(ℂ)               │ ℂ     │ 2^((n-1)/2) │ Simple
       6    │ M_k(ℝ)               │ ℝ     │ 2^(n/2)     │ Simple
       7    │ M_k(ℝ) ⊕ M_k(ℝ)      │ ℝ     │ 2^((n-1)/2) │ Double

    For n = 9:  9 mod 8 = 1  →  M₁₆(ℂ)  →  Spinor = ℂ¹⁶

=====================================================================
-/
namespace CliffordPeriodicity
/-!
=====================================================================
## The Base Field Classification
=====================================================================

The three division algebras that appear as base fields for
real Clifford algebras.  (The octonions 𝕆 do NOT appear because
Clifford algebras are associative and 𝕆 is not.)

The field determines the structure group of the spinor bundle:
  ℝ → O(k)   or SO(k)
  ℂ → U(k)
  ℍ → Sp(k)

For U⁹ we get ℂ, hence U(16).
-/

section BaseField

/-- The three associative division algebras over ℝ.
    These are the only base fields for real Clifford algebras.

    The octonions are excluded: they are not associative,
    and Clifford algebras are (as quotients of tensor algebras). -/
inductive CliffordBaseField : Type where
  /-- The real numbers ℝ.  dim_ℝ = 1. -/
  | real : CliffordBaseField
  /-- The complex numbers ℂ.  dim_ℝ = 2. -/
  | complex : CliffordBaseField
  /-- The quaternions ℍ.  dim_ℝ = 4. -/
  | quaternion : CliffordBaseField
  deriving DecidableEq, Repr

namespace CliffordBaseField

/-- Real dimension of the base field -/
def dim : CliffordBaseField → ℕ
  | .real       => 1
  | .complex    => 2
  | .quaternion => 4

/-- Every base field has positive dimension -/
theorem dim_pos (F : CliffordBaseField) : F.dim > 0 := by
  cases F <;> simp [dim]

/-- The base field dimensions are exactly {1, 2, 4} -/
theorem dim_mem (F : CliffordBaseField) : F.dim ∈ ({1, 2, 4} : Finset ℕ) := by
  cases F <;> simp [dim]

/-- Name of the spinor structure group for each base field.

    ℝ → O(k): real orthogonal
    ℂ → U(k): complex unitary
    ℍ → Sp(k): quaternionic symplectic -/
def structureGroupName : CliffordBaseField → String
  | .real       => "O"
  | .complex    => "U"
  | .quaternion => "Sp"

/-- Whether the base field is intrinsically complex.

    This is the key property for U⁹: if the base field is ℂ,
    the Clifford algebra carries a natural complex structure
    WITHOUT any complexification by hand. -/
def isComplex : CliffordBaseField → Bool
  | .complex => true
  | _        => false

end CliffordBaseField

end BaseField


/-!
=====================================================================
## Clifford Algebra Classification Data
=====================================================================

The classification of Cl(n,0) as a matrix algebra.

A Clifford algebra is either:
  - Simple: M_k(F) for some field F and matrix dimension k
  - Double: M_k(F) ⊕ M_k(F) (two copies — the "split" case)

The double case occurs at n ≡ 3, 7 (mod 8).
-/

section Classification

/-- Whether the Clifford algebra is simple or a direct sum of two copies -/
inductive CliffordAlgStructure : Type where
  /-- Simple algebra: M_k(F) -/
  | simple : CliffordAlgStructure
  /-- Double algebra: M_k(F) ⊕ M_k(F) — occurs at n ≡ 3, 7 mod 8 -/
  | double : CliffordAlgStructure
  deriving DecidableEq, Repr

structure CliffordData where
  /-- The dimension n of the underlying vector space ℝⁿ -/
  n : ℕ
  /-- The base field (ℝ, ℂ, or ℍ) -/
  baseField : CliffordBaseField
  /-- The matrix dimension k (the algebra is M_k(F) or M_k(F)²) -/
  matDim : ℕ
  /-- Simple or double? -/
  algStructure : CliffordAlgStructure
  /-- The real dimension of the Clifford algebra = 2ⁿ -/
  realDim : ℕ
  /-- Dimension of the irreducible spinor representation over F -/
  spinorDim : ℕ
  /-- Consistency: real dimension equals 2ⁿ -/
  hRealDim : realDim = 2 ^ n
  /-- Consistency: spinor dimension equals matrix dimension -/
  hSpinorDim : spinorDim = matDim
  /-- Consistency: real dimension decomposes correctly.
      Simple: realDim = F.dim · matDim²
      Double: realDim = 2 · F.dim · matDim² -/
  hDimCheck : match algStructure with
    | .simple => realDim = baseField.dim * matDim ^ 2
    | .double => realDim = 2 * baseField.dim * matDim ^ 2
  deriving Repr

end Classification


end CliffordPeriodicity
