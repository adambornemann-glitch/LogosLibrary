/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann (skeleton by Eric Weinstein roleplay)
Filename: FanoPlane/Defs.lean
-/
import LogosLibrary.Superior.CommonResources.HopfTower.HopfTowerOctonion
import Mathlib.Tactic
/-!
=====================================================================
# THE FANO PLANE AND SEVEN QUATERNIONIC SUBALGEBRAS OF 𝕆
=====================================================================

## Purpose

This file bridges the gap between HopfTowerOctonion (which constructs
ONE quaternionic embedding ℍ ↪ 𝕆 via q ↦ (q, 0)) and the generation
theorem (which needs ALL SEVEN quaternionic subalgebras and their
orbit structure under G₂ → SU(3)).

## The Fano Plane

The Fano plane PG(2, F₂) is the smallest projective plane:
  - 7 points: {1, 2, 3, 4, 5, 6, 7}
  - 7 lines:  each containing exactly 3 points
  - Each point lies on exactly 3 lines
  - Any two points determine a unique line
  - Any two lines meet in a unique point

The seven lines (using the Cayley-Dickson labeling, 0-indexed):
  L₀ = {0, 1, 2}    L₁ = {0, 3, 4}    L₂ = {0, 5, 6}
  L₃ = {1, 3, 5}    L₄ = {1, 4, 6}    L₅ = {2, 3, 6}
  L₆ = {2, 4, 5}

This is NOT the standard cyclic labeling {1,2,4}, {2,3,5}, ...
(quadratic residues mod 7).  It is the labeling that arises
naturally from the Cayley-Dickson doubling ℍ × ℍ, where
e₁, e₂, e₃ = (i,0), (j,0), (k,0) span the "left" quaternion
and e₄, e₅, e₆, e₇ = (0,1), (0,i), (0,j), (0,k) span the
"right" factor.  Line L₀ = {0,1,2} is exactly the left-ℍ
subalgebra — the Knot IV embedding.

Each line determines a quaternionic subalgebra:
  The three basis elements on a line, together with 1 ∈ 𝕆,
  form a copy of ℍ inside 𝕆.

## What This File Should Prove

  (A) The Fano plane as a combinatorial structure (finite, decidable)
  (B) Each of the 7 lines determines a quaternionic subalgebra
  (C) Each subalgebra is associative (despite 𝕆 being non-associative)
  (D) Any TWO of the seven subalgebras generate all of 𝕆
  (E) The existing Knot IV embedding corresponds to line L₁ = {1,2,4}

## Dependencies

  - HopfTowerOctonion: 𝕆ℝ, octMul, oct_e1, oct_e2, embedOct
  - Mathlib.Combinatorics.Configuration (if available) or hand-built

=====================================================================
-/
namespace FanoPlane.Defs

open HopfTowerKnot
/-!
=====================================================================
## Part I: The Combinatorial Fano Plane
=====================================================================
-/

/-- A point of the Fano plane: one of the seven imaginary octonion units.
    We use Fin 7 for decidable equality and finiteness. -/
abbrev FanoPoint := Fin 7

/-- A line of the Fano plane: an ordered triple of points.

    The ordering encodes the SIGN of the multiplication:
    if (i, j, k) is an ordered line, then eᵢ · eⱼ = eₖ.
    Cyclic permutations preserve the sign; transpositions flip it.

    This is the octonionic multiplication table in disguise. -/
structure FanoLine where
  p1 : FanoPoint
  p2 : FanoPoint
  p3 : FanoPoint
  /-- All three points are distinct -/
  h_distinct : p1 ≠ p2 ∧ p2 ≠ p3 ∧ p1 ≠ p3
  deriving Repr

/-- The seven lines of the Fano plane.

    Convention: (i, j, k) means eᵢ · eⱼ = +eₖ
    (using the Baez/Conway octonionic multiplication table).

    The lines are:
      {e₁, e₂, e₄}  {e₂, e₃, e₅}  {e₃, e₄, e₆}  {e₄, e₅, e₇}
      {e₅, e₆, e₁}  {e₆, e₇, e₂}  {e₇, e₁, e₃}

    (Indices shifted to Fin 7: eₖ ↦ k-1) -/
def line1 : FanoLine := ⟨0, 1, 2, by norm_cast, by norm_cast, by norm_cast⟩  -- e₁e₂ = e₃
def line2 : FanoLine := ⟨0, 3, 4, by norm_cast, by norm_cast, by norm_cast⟩  -- e₁e₄ = e₅
def line3 : FanoLine := ⟨0, 5, 6, by norm_cast, by norm_cast, by norm_cast⟩  -- {e₁, e₆, e₇}: e₁e₆ = −e₇ (or e₁e₇ = +e₆)
def line4 : FanoLine := ⟨1, 3, 5, by norm_cast, by norm_cast, by norm_cast⟩  -- e₂e₄ = e₆
def line5 : FanoLine := ⟨1, 4, 6, by norm_cast, by norm_cast, by norm_cast⟩  -- e₂e₅ = e₇
def line6 : FanoLine := ⟨2, 3, 6, by norm_cast, by norm_cast, by norm_cast⟩  -- e₃e₄ = e₇
def line7 : FanoLine := ⟨2, 4, 5, by norm_cast, by norm_cast, by norm_cast⟩  -- {e₃, e₅, e₆}: e₃e₅ = −e₆ (or e₃e₆ = +e₅)

/-- The complete set of Fano lines -/
def allLines : List FanoLine := [line1, line2, line3, line4, line5, line6, line7]

/-- There are exactly 7 lines -/
theorem seven_lines : allLines.length = 7 := by exact Nat.eq_of_beq_eq_true rfl

/-- **INCIDENCE PROPERTIES**

    Each point lies on exactly 3 lines.
    Any two distinct points lie on exactly 1 line.
    Any two distinct lines meet in exactly 1 point.

    These are the axioms of PG(2, F₂). -/

-- Helper: does a point lie on a line?
def onLine (pt : FanoPoint) (ln : FanoLine) : Bool :=
  pt = ln.p1 || pt = ln.p2 || pt = ln.p3

/-- Each point lies on exactly 3 lines -/
theorem three_lines_per_point (pt : FanoPoint) :
    (allLines.filter (onLine pt)).length = 3 := by
  fin_cases pt <;> exact Nat.eq_of_beq_eq_true rfl

/-- Any two distinct points determine a unique line -/
theorem two_points_one_line (p q : FanoPoint) (h : p ≠ q) :
    ∃! ln ∈ allLines, onLine p ln = true ∧ onLine q ln = true := by
  -- Step 1: Decidable computation — filter has exactly one element
  have key : (allLines.filter (fun ln => onLine p ln && onLine q ln)).length = 1 := by
    fin_cases p <;> fin_cases q <;> simp_all <;> norm_cast
  -- Step 2: Extract the unique witness from the singleton filter
  obtain ⟨a, ha⟩ : ∃ a, (allLines.filter (fun ln => onLine p ln && onLine q ln)) = [a] := by
    match hf : (allLines.filter (fun ln => onLine p ln && onLine q ln)) with
    | [a] => exact ⟨a, rfl⟩
    | [] => simp_all
    | _ :: _ :: _ => simp_all
  have hmem : a ∈ allLines.filter (fun ln => onLine p ln && onLine q ln) := by
    rw [ha]; exact List.mem_singleton.mpr rfl
  obtain ⟨ha_in, ha_pred⟩ := List.mem_filter.mp hmem
  rw [Bool.and_eq_true] at ha_pred
  -- Step 3: Existence + uniqueness
  refine ⟨a, ⟨ha_in, ha_pred.1, ha_pred.2⟩, ?_⟩
  rintro y ⟨hy_in, hy_p, hy_q⟩
  have : y ∈ allLines.filter (fun ln => onLine p ln && onLine q ln) := by
    grind only [= List.mem_filter]
  rw [ha] at this
  exact List.mem_singleton.mp this

/-!
=====================================================================
## Part II: The Seven Quaternionic Subalgebras
=====================================================================

Each Fano line {eᵢ, eⱼ, eₖ} determines a quaternionic subalgebra:

  ℍ_L = span_ℝ{1, eᵢ, eⱼ, eₖ} ⊂ 𝕆

with multiplication table:
  eᵢ · eⱼ = eₖ,   eⱼ · eₖ = eᵢ,   eₖ · eᵢ = eⱼ
  eᵢ² = eⱼ² = eₖ² = -1

This is isomorphic to ℍ = span{1, i, j, k}.
-/


/- The seven imaginary octonion basis elements.

    These correspond to the seven points of the Fano plane.
    Each is a unit imaginary octonion: eₖ² = -1.

    Encoding in 𝕆ℝ = ℍℝ × ℍℝ:
      e₁ = (i, 0)    e₂ = (j, 0)    e₃ = (k, 0)
      e₄ = (0, 1)    e₅ = (0, i)    e₆ = (0, j)    e₇ = (0, k)

    The first three are embedded quaternion imaginaries.
    The last four involve the Cayley-Dickson "new direction." -/
def octBasis : Fin 7 → 𝕆ℝ
  | 0 => ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩ -- e₁ = (i, 0)
  | 1 => ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩ -- e₂ = (j, 0)
  | 2 => ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩ -- e₃ = (k, 0)
  | 3 => ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩ -- e₄ = (0, 1)
  | 4 => ⟨⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩⟩ -- e₅ = (0, i)
  | 5 => ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩⟩ -- e₆ = (0, j)
  | 6 => ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩⟩ -- e₇ = (0, k)

/-- The octonion multiplicative identity: (1, 0) -/
def octOne : 𝕆ℝ := 𝕆ℝ.mk 1 0

/-- Octonion addition (componentwise) -/
def octAdd (x y : 𝕆ℝ) : 𝕆ℝ := 𝕆ℝ.mk (x.l + y.l) (x.r + y.r)

/-- Real scalar multiplication on octonions -/
def octSmul (c : ℝ) (x : 𝕆ℝ) : 𝕆ℝ := 𝕆ℝ.mk (c • x.l) (c • x.r)

/-- An octonion lies in the quaternionic span of a Fano line
    if it is a real linear combination of {1, eᵢ, eⱼ, eₖ}. -/
def inQuatSpan (L : FanoLine) (x : 𝕆ℝ) : Prop :=
  ∃ a b c d : ℝ,
    x = octAdd (octSmul a octOne)
         (octAdd (octSmul b (octBasis L.p1))
           (octAdd (octSmul c (octBasis L.p2))
                   (octSmul d (octBasis L.p3))))

/- Each basis element squares to -1 -/
theorem octBasis_sq (k : Fin 7) : octMul (octBasis k) (octBasis k) = octNeg octOne := by
  fin_cases k
    <;> simp only [octBasis, octMul, octNeg, octOne, qConj,QuaternionAlgebra.mk_mul_mk]
    <;> ext
    <;> simp

/-- BASIS-INDEPENDENT: A subset of 𝕆 is a quaternionic subalgebra
    if it is 4-dimensional, contains 1, is closed under octMul,
    and is associative.

    This is the predicate that G₂ preserves.
    Every G₂ element maps quaternionic subalgebras to quaternionic
    subalgebras — but NOT necessarily standard ones. -/
structure IsQuatSubalgebra (mem : 𝕆ℝ → Prop) : Prop where
  /-- Contains the identity -/
  has_one : mem octOne
  /-- Closed under multiplication -/
  mul_closed : ∀ x y, mem x → mem y → mem (octMul x y)
  /-- Closed under addition -/
  add_closed : ∀ x y, mem x → mem y → mem (octAdd x y)
  /-- Closed under scalar multiplication -/
  smul_closed : ∀ (c : ℝ) x, mem x → mem (octSmul c x)
  /-- Associative -/
  assoc : ∀ x y z, mem x → mem y → mem z →
    octMul (octMul x y) z = octMul x (octMul y z)

/-- Extract the 8 real components of an octonion -/
def octComponent (x : 𝕆ℝ) : Fin 8 → ℝ
  | 0 => x.l.re
  | 1 => x.l.imI
  | 2 => x.l.imJ
  | 3 => x.l.imK
  | 4 => x.r.re
  | 5 => x.r.imI
  | 6 => x.r.imJ
  | 7 => x.r.imK

/-- Which of the 8 component slots each imaginary basis element occupies.
    octBasis k has a 1 in slot (basisIdx k) and zeros elsewhere. -/
def basisIdx : FanoPoint → Fin 8
  | 0 => 1   -- e₁ = (i,0) lives in l.imI
  | 1 => 2   -- e₂ = (j,0) lives in l.imJ
  | 2 => 3   -- e₃ = (k,0) lives in l.imK
  | 3 => 4   -- e₄ = (0,1) lives in r.re
  | 4 => 5   -- e₅ = (0,i) lives in r.imI
  | 5 => 6   -- e₆ = (0,j) lives in r.imJ
  | 6 => 7   -- e₇ = (0,k) lives in r.imK

/-- An octonion lies in the quaternionic span of a Fano line iff
    every imaginary component NOT on the line is zero.

    This is the "boolean" characterization: instead of exhibiting
    coefficients, we just check which slots vanish.

    For line L = {p1, p2, p3}, the live slots are
    {0 (= real part), basisIdx p1, basisIdx p2, basisIdx p3}.
    The other four slots must be zero. -/
abbrev inLineSpan (L : FanoLine) (x : 𝕆ℝ) : Prop :=
  ∀ j : Fin 7, j ≠ L.p1 → j ≠ L.p2 → j ≠ L.p3 →
    octComponent x (basisIdx j) = 0


/-- Each basis element is in the span of any line it belongs to -/
theorem octBasis_inLineSpan (L : FanoLine) (k : Fin 7)
    (hk : k = L.p1 ∨ k = L.p2 ∨ k = L.p3) :
    inLineSpan L (octBasis k) := by
  intro j hj1 hj2 hj3
  fin_cases k <;> fin_cases j <;>
    simp_all [octBasis, octComponent, basisIdx]

/-- The identity octOne is in the span of every line -/
theorem octOne_inLineSpan (L : FanoLine) : inLineSpan L octOne := by
  intro j _ _ _
  fin_cases j <;> simp [octOne, octComponent, basisIdx]

/-- octComponent distributes over octAdd -/
theorem octComponent_add (x y : 𝕆ℝ) (k : Fin 8) :
    octComponent (octAdd x y) k = octComponent x k + octComponent y k := by
  fin_cases k <;> simp [octComponent, octAdd]

/-- octComponent distributes over octSmul -/
theorem octComponent_smul (c : ℝ) (x : 𝕆ℝ) (k : Fin 8) :
    octComponent (octSmul c x) k = c * octComponent x k := by
  fin_cases k <;> simp [octComponent, octSmul, smul_eq_mul]

/-- Lookup from Fin 7 to the seven Fano lines -/
def lineByIndex : Fin 7 → FanoLine
  | 0 => line1 | 1 => line2 | 2 => line3 | 3 => line4
  | 4 => line5 | 5 => line6 | 6 => line7

/-- The Fano multiplication table: for distinct points a ≠ b,
    fanoMul a b is the third point on the unique Fano line through them.

    This encodes the full octonionic multiplication table on
    imaginary basis elements (up to sign). -/
def fanoMul : Fin 7 → Fin 7 → Fin 7
  -- Line1 = {0,1,2}
  | 0, 1 => 2 | 1, 0 => 2 | 1, 2 => 0 | 2, 1 => 0 | 0, 2 => 1 | 2, 0 => 1
  -- Line2 = {0,3,4}
  | 0, 3 => 4 | 3, 0 => 4 | 3, 4 => 0 | 4, 3 => 0 | 0, 4 => 3 | 4, 0 => 3
  -- Line3 = {0,5,6}
  | 0, 5 => 6 | 5, 0 => 6 | 5, 6 => 0 | 6, 5 => 0 | 0, 6 => 5 | 6, 0 => 5
  -- Line4 = {1,3,5}
  | 1, 3 => 5 | 3, 1 => 5 | 3, 5 => 1 | 5, 3 => 1 | 1, 5 => 3 | 5, 1 => 3
  -- Line5 = {1,4,6}
  | 1, 4 => 6 | 4, 1 => 6 | 4, 6 => 1 | 6, 4 => 1 | 1, 6 => 4 | 6, 1 => 4
  -- Line6 = {2,3,6}
  | 2, 3 => 6 | 3, 2 => 6 | 3, 6 => 2 | 6, 3 => 2 | 2, 6 => 3 | 6, 2 => 3
  -- Line7 = {2,4,5}
  | 2, 4 => 5 | 4, 2 => 5 | 4, 5 => 2 | 5, 4 => 2 | 2, 5 => 4 | 5, 2 => 4
  -- Diagonal (unused — guarded by a ≠ b in all applications)
  | a, _ => a

/-- The set of three Fano points on a line -/
def linePointSet (k : Fin 7) : Finset (Fin 7) :=
  {(lineByIndex k).p1, (lineByIndex k).p2, (lineByIndex k).p3}

/-- One round of Fano multiplication closure:
    S together with all pairwise fanoMul products.
    One round suffices because any two Fano lines share exactly
    one point, leaving 2 missing points — each reachable as a
    product of two of the 5 available points. -/
def fanoGenerate (S : Finset (Fin 7)) : Finset (Fin 7) :=
  S ∪ (S.product S).image (fun p => fanoMul p.1 p.2)

/-- Sign of the octonionic product: octBasis i · octBasis j = (fanoSign i j) • octBasis (fanoMul i j).

    +1 when (i, j) is a positively oriented Fano edge,
    -1 when negatively oriented.
    Antisymmetric: fanoSign i j = -fanoSign j i (imaginary octonions anticommute). -/
def fanoSign : Fin 7 → Fin 7 → ℝ
  -- Row 0 (e₁): e₁e₂=+e₃, e₁e₃=-e₂, e₁e₄=+e₅, e₁e₅=-e₄, e₁e₆=-e₇, e₁e₇=+e₆
  | 0, 1 =>  1 | 0, 2 => -1 | 0, 3 =>  1 | 0, 4 => -1 | 0, 5 => -1 | 0, 6 =>  1
  -- Row 1 (e₂): e₂e₁=-e₃, e₂e₃=+e₁, e₂e₄=+e₆, e₂e₅=+e₇, e₂e₆=-e₄, e₂e₇=-e₅
  | 1, 0 => -1 | 1, 2 =>  1 | 1, 3 =>  1 | 1, 4 =>  1 | 1, 5 => -1 | 1, 6 => -1
  -- Row 2 (e₃): e₃e₁=+e₂, e₃e₂=-e₁, e₃e₄=+e₇, e₃e₅=-e₆, e₃e₆=+e₅, e₃e₇=-e₄
  | 2, 0 =>  1 | 2, 1 => -1 | 2, 3 =>  1 | 2, 4 => -1 | 2, 5 =>  1 | 2, 6 => -1
  -- Row 3 (e₄): e₄e₁=-e₅, e₄e₂=-e₆, e₄e₃=-e₇, e₄e₅=+e₁, e₄e₆=+e₂, e₄e₇=+e₃
  | 3, 0 => -1 | 3, 1 => -1 | 3, 2 => -1 | 3, 4 =>  1 | 3, 5 =>  1 | 3, 6 =>  1
  -- Row 4 (e₅): e₅e₁=+e₄, e₅e₂=-e₇, e₅e₃=+e₆, e₅e₄=-e₁, e₅e₆=-e₃, e₅e₇=+e₂
  | 4, 0 =>  1 | 4, 1 => -1 | 4, 2 =>  1 | 4, 3 => -1 | 4, 5 => -1 | 4, 6 =>  1
  -- Row 5 (e₆): e₆e₁=+e₇, e₆e₂=+e₄, e₆e₃=-e₅, e₆e₄=-e₂, e₆e₅=+e₃, e₆e₇=-e₁
  | 5, 0 =>  1 | 5, 1 =>  1 | 5, 2 => -1 | 5, 3 => -1 | 5, 4 =>  1 | 5, 6 => -1
  -- Row 6 (e₇): e₇e₁=-e₆, e₇e₂=+e₅, e₇e₃=+e₄, e₇e₄=-e₃, e₇e₅=-e₂, e₇e₆=+e₁
  | 6, 0 => -1 | 6, 1 =>  1 | 6, 2 =>  1 | 6, 3 => -1 | 6, 4 => -1 | 6, 5 =>  1
  -- Diagonal (unused — guarded by i ≠ j in all applications)
  | _, _ => 0

/-!
=====================================================================
## Part I: Octonion Automorphisms
=====================================================================

An automorphism of 𝕆 is an ℝ-linear bijection φ: 𝕆 → 𝕆
satisfying φ(xy) = φ(x)φ(y) for all x, y.

We encode this as a structure carrying the map and its properties.
The Lean type-checker enforces that every use of an automorphism
must respect these constraints.
=====================================================================
-/

section Automorphisms

/-- An automorphism of the octonions.

    An ℝ-linear map φ: 𝕆 → 𝕆 that preserves the multiplication.
    We also require injectivity (surjectivity follows from
    finite-dimensionality, but is convenient to carry).

    In the Lie group G₂, each element is one of these.
    G₂ is 14-dimensional, compact, simply connected, and
    is the smallest of the five exceptional Lie groups. -/
structure OctAutomorphism where
  /-- The underlying map -/
  toFun : 𝕆ℝ → 𝕆ℝ
  /-- Preserves multiplication -/
  mul_compat : ∀ x y : 𝕆ℝ, toFun (octMul x y) = octMul (toFun x) (toFun y)
  /-- ℝ-linear: preserves addition -/
  add_compat : ∀ x y : 𝕆ℝ, toFun (octAdd x y) = octAdd (toFun x) (toFun y)
  /-- ℝ-linear: preserves scalar multiplication -/
  smul_compat : ∀ (c : ℝ) (x : 𝕆ℝ), toFun (octSmul c x) = octSmul c (toFun x)
  /-- Injective -/
  injective : Function.Injective toFun

/-- The identity automorphism -/
def OctAutomorphism.id : OctAutomorphism where
  toFun := fun x => x
  mul_compat := fun _ _ => rfl
  add_compat := fun _ _ => rfl
  smul_compat := fun _ _ => rfl
  injective := Function.injective_id

/-- Composition of automorphisms -/
def OctAutomorphism.comp (φ ψ : OctAutomorphism) : OctAutomorphism where
  toFun := φ.toFun ∘ ψ.toFun
  mul_compat := fun x y => by
    simp only [Function.comp]
    rw [ψ.mul_compat, φ.mul_compat]
  add_compat := fun x y => by
    simp only [Function.comp]
    rw [ψ.add_compat, φ.add_compat]
  smul_compat := fun c x => by
    simp only [Function.comp]
    rw [ψ.smul_compat, φ.smul_compat]
  injective := Function.Injective.comp φ.injective ψ.injective

/-- The image of a membership predicate under an automorphism -/
def imageUnder (φ : OctAutomorphism) (mem : 𝕆ℝ → Prop) : 𝕆ℝ → Prop :=
  fun x => ∃ y, φ.toFun y = x ∧ mem y


/-- The three intersection classes, computed in fano_line_pairing.

    Class 0: lines 1, 2 (share point 0 = e₁ with Knot IV)
    Class 1: lines 3, 4 (share point 1 = e₂ with Knot IV)
    Class 2: lines 5, 6 (share point 2 = e₃ with Knot IV) -/
def intersectionClass : Fin 7 → Option (Fin 3)
  | 0 => none     -- line 0 IS Knot IV, not in any class
  | 1 => some 0   -- shares e₁
  | 2 => some 0   -- shares e₁
  | 3 => some 1   -- shares e₂
  | 4 => some 1   -- shares e₂
  | 5 => some 2   -- shares e₃
  | 6 => some 2   -- shares e₃

end Automorphisms

end FanoPlane.Defs
