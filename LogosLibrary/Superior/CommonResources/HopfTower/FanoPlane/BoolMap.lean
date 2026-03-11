/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann (skeleton by Eric Weinstein roleplay)
Filename: FanoPlane/BoolMap.lean
-/
import Mathlib.Tactic
import LogosLibrary.Superior.CommonResources.HopfTower.FanoPlane.Defs
/-!
=====================================================================
# THE BOOLEAN MAP: SEVEN QUATERNIONIC SUBALGEBRAS OF 𝕆
=====================================================================

## Strategy

The standard approach to quaternionic subalgebras of 𝕆 exhibits
explicit coefficients: "x lies in span{1, eᵢ, eⱼ, eₖ} iff there
exist a, b, c, d ∈ ℝ with x = a + beᵢ + ceⱼ + deₖ."  This
creates existential witnesses at every step, and the combinatorics
of seven subalgebras × closure × associativity becomes intractable.

The boolean map replaces existential quantification with universal
component vanishing.  An octonion x ∈ 𝕆 ≅ ℝ⁸ lies in the span
of a Fano line L = {p₁, p₂, p₃} iff its four OFF-LINE imaginary
components are zero:

    inLineSpan L x  ≡  ∀ j ∉ {p₁, p₂, p₃}, octComponent x (basisIdx j) = 0

No witnesses.  No coefficients.  Just zeros.  Every subalgebra
property reduces to: extract the zeros, substitute into octMul,
close with ring.

## Main Results

  * `quatSubalgebra_closed` — Each Fano line spans a subalgebra:
    if x, y ∈ span(L), then octMul x y ∈ span(L).
    (7 lines × 4 off-line components = 28 nontrivial goals, all ring)

  * `quatSubalgebra_associative` — Each subalgebra is associative:
    octMul (octMul x y) z = octMul x (octMul y z) for x, y, z ∈ span(L).
    (7 lines × 12 zero extractions × 8 component goals, all ring)

  * `knotIV_is_fano_line` — The Hopf tower embedding q ↦ (q, 0)
    lands in line 1 = {0, 1, 2}, connecting the Cayley-Dickson
    construction to the Fano plane.

  * `two_lines_generate` — Any two distinct Fano lines generate
    all of 𝕆 under one round of multiplication.  (42 cases, all decide)

  * `multiplication_table` — The complete 7×7 octonionic product
    table: eᵢeⱼ = −δᵢⱼ + (fanoSign i j)·e_{fanoMul i j}.
    All 49 entries verified against the Cayley-Dickson formula.

  * `fano_line_pairing` — The six non-Knot-IV lines partition into
    three pairs by intersection with line 0, giving the combinatorial
    skeleton of the three-generation structure.

## Axiom Budget

  Zero axioms.  Zero sorry.  Every theorem is proved by finite
  case analysis (fin_cases), zero substitution (simp_all), and
  polynomial identity (ring).  The Fano plane is small enough
  that the type-checker can simply compute.

## Dependencies

  * `FanoPlane.Defs` — Fano line definitions, octBasis, fanoMul,
    fanoSign, inLineSpan, linePointSet, fanoGenerate
  * `HopfTowerOctonion` — 𝕆ℝ, octMul, embedOct, qConj

=====================================================================
-/
namespace FanoPlane.BoolMap
open FanoPlane.Defs HopfTowerKnot
/-- **CLOSURE UNDER MULTIPLICATION**

    For each Fano line L = {p1, p2, p3}, the set of octonions whose
    off-line components vanish is closed under octMul.

    That is: if x and y both live in span_ℝ{1, eₚ₁, eₚ₂, eₚ₃},
    then octMul x y does too.  This makes each Fano-line span
    a genuine subalgebra of 𝕆.

    Proof: fin_cases on the line index (7 cases).  For each line,
    type-annotated specialization of hx/hy at each off-line Fin 7
    index extracts concrete zero hypotheses (e.g., x.r.re = 0)
    via kernel reduction — no simp needed for the match unfolding.
    Three of seven indices are on-line and fail; try catches them.
    Then fin_cases on the target component j, simp_all substitutes
    the zeros into the octMul expression, and ring closes the
    resulting polynomial identity.

    28 nontrivial goals (7 lines × 4 off-line components),
    each reduced to 0 * foo + bar * 0 = 0 after substitution. -/
theorem quatSubalgebra_closed (k : Fin 7)
    (x y : 𝕆ℝ) (hx : inLineSpan (lineByIndex k) x)
    (hy : inLineSpan (lineByIndex k) y) :
    inLineSpan (lineByIndex k) (octMul x y) := by
  fin_cases k <;> (
    simp only [lineByIndex, line1, line2, line3, line4,
               line5, line6, line7] at hx hy ⊢
    -- Extract zero conditions via definitional reduction.
    -- Each line: 4 of 7 succeed (off-line indices); 3 fail (on-line).
    -- Type annotation forces kernel reduction — no simp needed.
    try have : x.l.imI = 0 := hx ⟨0, by omega⟩ (by lia) (by lia) (by lia)
    try have : x.l.imJ = 0 := hx ⟨1, by omega⟩ (by lia) (by lia) (by lia)
    try have : x.l.imK = 0 := hx ⟨2, by omega⟩ (by lia) (by lia) (by lia)
    try have : x.r.re  = 0 := hx ⟨3, by omega⟩ (by lia) (by lia) (by lia)
    try have : x.r.imI = 0 := hx ⟨4, by omega⟩ (by lia) (by lia) (by lia)
    try have : x.r.imJ = 0 := hx ⟨5, by omega⟩ (by lia) (by lia) (by lia)
    try have : x.r.imK = 0 := hx ⟨6, by omega⟩ (by lia) (by lia) (by lia)
    try have : y.l.imI = 0 := hy ⟨0, by omega⟩ (by lia) (by lia) (by lia)
    try have : y.l.imJ = 0 := hy ⟨1, by omega⟩ (by lia) (by lia) (by lia)
    try have : y.l.imK = 0 := hy ⟨2, by omega⟩ (by lia) (by lia) (by lia)
    try have : y.r.re  = 0 := hy ⟨3, by omega⟩ (by lia) (by lia) (by lia)
    try have : y.r.imI = 0 := hy ⟨4, by omega⟩ (by lia) (by lia) (by lia)
    try have : y.r.imJ = 0 := hy ⟨5, by omega⟩ (by lia) (by lia) (by lia)
    try have : y.r.imK = 0 := hy ⟨6, by omega⟩ (by lia) (by lia) (by lia)
    -- Context now has 8 concrete zero hypotheses (e.g., x.r.re = 0)
    -- simp_all substitutes them into the octMul expression; ring closes it
    intro j hj1 hj2 hj3
    fin_cases j <;>
      simp_all [octComponent, octMul, qConj, basisIdx])


/-- Associativity for line1 = {e₁, e₂, e₃}.
    The span lives entirely in the left ℍ component (r = 0),
    so octMul reduces to quaternion multiplication, which is associative. -/
private theorem assoc_line1 (x y z : 𝕆ℝ)
    (hx : inLineSpan line1 x) (hy : inLineSpan line1 y) (hz : inLineSpan line1 z) :
    octMul (octMul x y) z = octMul x (octMul y z) := by
  -- line1 = {0,1,2}: off-line indices 3,4,5,6 → all r-components vanish
  have : x.r.re  = 0 := hx ⟨3, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.imI = 0 := hx ⟨4, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.imJ = 0 := hx ⟨5, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.imK = 0 := hx ⟨6, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.re  = 0 := hy ⟨3, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.imI = 0 := hy ⟨4, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.imJ = 0 := hy ⟨5, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.imK = 0 := hy ⟨6, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.re  = 0 := hz ⟨3, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.imI = 0 := hz ⟨4, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.imJ = 0 := hz ⟨5, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.imK = 0 := hz ⟨6, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  -- After zero substitution: .r goals are trivial, .l goals are
  -- quaternion associativity in coordinates — a ring identity.
  unfold octMul qConj
  refine 𝕆ℝ.ext ?_ ?_ <;> ext <;> simp_all <;> ring

/-- Associativity for line2 = {e₁, e₄, e₅}.
    Spans both Cayley-Dickson halves: live components are
    l.re, l.imI, r.re, r.imI. -/
private theorem assoc_line2 (x y z : 𝕆ℝ)
    (hx : inLineSpan line2 x) (hy : inLineSpan line2 y) (hz : inLineSpan line2 z) :
    octMul (octMul x y) z = octMul x (octMul y z) := by
  -- line2 = {0,3,4}: off-line indices 1,2,5,6
  have : x.l.imJ = 0 := hx ⟨1, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.l.imK = 0 := hx ⟨2, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.imJ = 0 := hx ⟨5, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.imK = 0 := hx ⟨6, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.l.imJ = 0 := hy ⟨1, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.l.imK = 0 := hy ⟨2, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.imJ = 0 := hy ⟨5, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.imK = 0 := hy ⟨6, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.l.imJ = 0 := hz ⟨1, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.l.imK = 0 := hz ⟨2, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.imJ = 0 := hz ⟨5, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.imK = 0 := hz ⟨6, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  unfold octMul qConj
  refine 𝕆ℝ.ext ?_ ?_ <;> ext <;> simp_all <;> ring

/-- Associativity for line3 = {e₁, e₆, e₇}.
    Live components: l.re, l.imI, r.imJ, r.imK. -/
private theorem assoc_line3 (x y z : 𝕆ℝ)
    (hx : inLineSpan line3 x) (hy : inLineSpan line3 y) (hz : inLineSpan line3 z) :
    octMul (octMul x y) z = octMul x (octMul y z) := by
  -- line3 = {0,5,6}: off-line indices 1,2,3,4
  have : x.l.imJ = 0 := hx ⟨1, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.l.imK = 0 := hx ⟨2, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.re  = 0 := hx ⟨3, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.imI = 0 := hx ⟨4, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.l.imJ = 0 := hy ⟨1, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.l.imK = 0 := hy ⟨2, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.re  = 0 := hy ⟨3, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.imI = 0 := hy ⟨4, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.l.imJ = 0 := hz ⟨1, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.l.imK = 0 := hz ⟨2, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.re  = 0 := hz ⟨3, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.imI = 0 := hz ⟨4, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  unfold octMul qConj
  refine 𝕆ℝ.ext ?_ ?_ <;> ext <;> simp_all <;> ring

/-- Associativity for line4 = {e₂, e₄, e₆}.
    Live components: l.re, l.imJ, r.re, r.imJ. -/
private theorem assoc_line4 (x y z : 𝕆ℝ)
    (hx : inLineSpan line4 x) (hy : inLineSpan line4 y) (hz : inLineSpan line4 z) :
    octMul (octMul x y) z = octMul x (octMul y z) := by
  -- line4 = {1,3,5}: off-line indices 0,2,4,6
  have : x.l.imI = 0 := hx ⟨0, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.l.imK = 0 := hx ⟨2, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.imI = 0 := hx ⟨4, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.imK = 0 := hx ⟨6, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.l.imI = 0 := hy ⟨0, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.l.imK = 0 := hy ⟨2, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.imI = 0 := hy ⟨4, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.imK = 0 := hy ⟨6, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.l.imI = 0 := hz ⟨0, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.l.imK = 0 := hz ⟨2, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.imI = 0 := hz ⟨4, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.imK = 0 := hz ⟨6, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  unfold octMul qConj
  refine 𝕆ℝ.ext ?_ ?_ <;> ext <;> simp_all <;> ring

/-- Associativity for line5 = {e₂, e₅, e₇}.
    Live components: l.re, l.imJ, r.imI, r.imK. -/
private theorem assoc_line5 (x y z : 𝕆ℝ)
    (hx : inLineSpan line5 x) (hy : inLineSpan line5 y) (hz : inLineSpan line5 z) :
    octMul (octMul x y) z = octMul x (octMul y z) := by
  -- line5 = {1,4,6}: off-line indices 0,2,3,5
  have : x.l.imI = 0 := hx ⟨0, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.l.imK = 0 := hx ⟨2, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.re  = 0 := hx ⟨3, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.imJ = 0 := hx ⟨5, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.l.imI = 0 := hy ⟨0, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.l.imK = 0 := hy ⟨2, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.re  = 0 := hy ⟨3, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.imJ = 0 := hy ⟨5, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.l.imI = 0 := hz ⟨0, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.l.imK = 0 := hz ⟨2, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.re  = 0 := hz ⟨3, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.imJ = 0 := hz ⟨5, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  unfold octMul qConj
  refine 𝕆ℝ.ext ?_ ?_ <;> ext <;> simp_all <;> ring

/-- Associativity for line6 = {e₃, e₄, e₇}.
    Live components: l.re, l.imK, r.re, r.imK. -/
private theorem assoc_line6 (x y z : 𝕆ℝ)
    (hx : inLineSpan line6 x) (hy : inLineSpan line6 y) (hz : inLineSpan line6 z) :
    octMul (octMul x y) z = octMul x (octMul y z) := by
  -- line6 = {2,3,6}: off-line indices 0,1,4,5
  have : x.l.imI = 0 := hx ⟨0, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.l.imJ = 0 := hx ⟨1, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.imI = 0 := hx ⟨4, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.imJ = 0 := hx ⟨5, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.l.imI = 0 := hy ⟨0, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.l.imJ = 0 := hy ⟨1, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.imI = 0 := hy ⟨4, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.imJ = 0 := hy ⟨5, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.l.imI = 0 := hz ⟨0, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.l.imJ = 0 := hz ⟨1, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.imI = 0 := hz ⟨4, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.imJ = 0 := hz ⟨5, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  unfold octMul qConj
  refine 𝕆ℝ.ext ?_ ?_ <;> ext <;> simp_all <;> ring

/-- Associativity for line7 = {e₃, e₅, e₆}.
    Live components: l.re, l.imK, r.imI, r.imJ. -/
private theorem assoc_line7 (x y z : 𝕆ℝ)
    (hx : inLineSpan line7 x) (hy : inLineSpan line7 y) (hz : inLineSpan line7 z) :
    octMul (octMul x y) z = octMul x (octMul y z) := by
  -- line7 = {2,4,5}: off-line indices 0,1,3,6
  have : x.l.imI = 0 := hx ⟨0, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.l.imJ = 0 := hx ⟨1, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.re  = 0 := hx ⟨3, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : x.r.imK = 0 := hx ⟨6, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.l.imI = 0 := hy ⟨0, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.l.imJ = 0 := hy ⟨1, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.re  = 0 := hy ⟨3, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : y.r.imK = 0 := hy ⟨6, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.l.imI = 0 := hz ⟨0, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.l.imJ = 0 := hz ⟨1, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.re  = 0 := hz ⟨3, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  have : z.r.imK = 0 := hz ⟨6, by omega⟩ (by norm_cast) (by norm_cast) (by norm_cast)
  unfold octMul qConj
  refine 𝕆ℝ.ext ?_ ?_ <;> ext <;> simp_all <;> ring


/-- **ASSOCIATIVITY WITHIN EACH SUBALGEBRA**

    Despite 𝕆 being non-associative, each Fano-line subalgebra
    IS associative: for x, y, z in span_ℝ{1, eₚ₁, eₚ₂, eₚ₃},

      octMul (octMul x y) z = octMul x (octMul y z)

    This follows from Artin's theorem (any subalgebra of 𝕆
    generated by two elements is associative), since the three
    generators satisfy eₖ = eᵢeⱼ and the subalgebra is generated
    by just {eᵢ, eⱼ}.

    Proof: same extraction strategy as quatSubalgebra_closed.
    Type-annotated specialization pulls 4 zero hypotheses per
    input (12 total for x, y, z).  After substitution, both
    sides of the associativity equation reduce to identical
    quaternion arithmetic — ext splits into 8 components,
    simp_all substitutes zeros, and ring closes each. -/
theorem quatSubalgebra_associative (k : Fin 7)
    (x y z : 𝕆ℝ)
    (hx : inLineSpan (lineByIndex k) x)
    (hy : inLineSpan (lineByIndex k) y)
    (hz : inLineSpan (lineByIndex k) z) :
    octMul (octMul x y) z = octMul x (octMul y z) := by
  fin_cases k <;> simp only [lineByIndex] at hx hy ⊢
  · exact assoc_line1 x y z hx hy hz
  · exact assoc_line2 x y z hx hy hz
  · exact assoc_line3 x y z hx hy hz
  · exact assoc_line4 x y z hx hy hz
  · exact assoc_line5 x y z hx hy hz
  · exact assoc_line6 x y z hx hy hz
  · exact assoc_line7 x y z hx hy hz


/-- **THE KNOT IV EMBEDDING IS LINE 1**

    The embedding q ↦ (q, 0) from HopfTowerOctonion picks out
    the quaternionic subalgebra span{1, e₁, e₂, e₃} = span{1, (i,0), (j,0), (k,0)}.

    In our Fano plane labeling, this IS line1 = {0, 1, 2}.
    The off-line indices 3, 4, 5, 6 correspond to the four right-quaternion
    components r.re, r.imI, r.imJ, r.imK — which are identically zero
    for any embedded quaternion (q, 0).

    This connects the Hopf tower (Knot IV: q ↦ (q, 0)) to the
    Fano plane (line1 determines a quaternionic subalgebra). -/
theorem knotIV_is_fano_line (q : ℍℝ) : inLineSpan line1 (embedOct q) := by
  intro j hj1 hj2 hj3
  fin_cases j <;> simp_all [embedOct, octComponent, basisIdx]
  · exact not_neZero.mp fun a => hj1 rfl
  · exact not_neZero.mp fun a => hj2 rfl
  · exact not_neZero.mp fun a => hj3 rfl


/-- A line of the Fano plane: a triple of points.

    The three points form an unordered set determining a
    quaternionic subalgebra.  The SIGN of the multiplication
    eᵢ · eⱼ = ±eₖ is recorded separately by `fanoSign`
    (see Defs.lean), not by the triple ordering.

    Cyclic permutations and transpositions of a line give
    the same subalgebra; only the sign changes. -/
theorem two_lines_generate (i j : Fin 7) (h : i ≠ j) :
    fanoGenerate (linePointSet i ∪ linePointSet j) = Finset.univ := by
  fin_cases i <;> fin_cases j <;> simp_all <;> norm_cast

/-- **OFF-DIAGONAL MULTIPLICATION**: eᵢ · eⱼ = (fanoSign i j) • eₖ where k = fanoMul i j.

    42 concrete equations, each verified against the Cayley-Dickson formula. -/
theorem octBasis_mul_ne (i j : Fin 7) (h : i ≠ j) :
    octMul (octBasis i) (octBasis j) = octSmul (fanoSign i j) (octBasis (fanoMul i j)) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [octBasis, octMul, octSmul, qConj, fanoSign, fanoMul,
              QuaternionAlgebra.mk_mul_mk] <;>
    ext <;> simp

/-- **THE COMPLETE OCTONIONIC MULTIPLICATION TABLE**

    eᵢ · eⱼ = -1            if i = j  (all basis elements square to -1)
    eᵢ · eⱼ = ±eₖ           if i ≠ j  (sign and index from Fano plane)

    49 entries, all verified against octMul. -/
theorem multiplication_table (i j : Fin 7) :
    octMul (octBasis i) (octBasis j) =
      if i = j then octNeg octOne
      else octSmul (fanoSign i j) (octBasis (fanoMul i j)) := by
  by_cases h : i = j
  · subst h; simp [octBasis_sq]
  · simp only [if_neg h]; exact octBasis_mul_ne i j h


/-- **THE THREE-GENERATION PAIRING**

    Fix line 0 = {0, 1, 2} — the Knot IV embedding ℍ ↪ 𝕆.
    The remaining six Fano lines partition into three pairs,
    each sharing exactly one point with line 0:

      Pair α:  lines 1, 2  share point 0  (= e₁)
      Pair β:  lines 3, 4  share point 1  (= e₂)
      Pair γ:  lines 5, 6  share point 2  (= e₃)

    Each pair corresponds to one generation of fermions.
    The three pairs are distinguished by which imaginary
    quaternion unit of the chosen ℍ they have in common
    with the Knot IV subalgebra.

    This is the combinatorial shadow of the SU(3) orbit
    decomposition described in three_quaternionic_subalgebras
    (ObserverseLagrangian.lean, Steps C–E).  The full proof
    requires identifying SU(3) = Stab_{G₂}(line 0) and showing
    that intersection class = orbit class.  This theorem
    establishes the combinatorial half: the partition into
    three pairs of two exists and is determined by the Fano
    plane alone, with no Lie group theory.

    6 lines = 3 pairs × 2 lines/pair.
    3 pairs = 3 generations.
    The factor of 3 is not numerology — it is a theorem
    about the incidence geometry of PG(2, F₂). -/
theorem fano_line_pairing :
    linePointSet 1 ∩ linePointSet 0 = {0}
    ∧ linePointSet 2 ∩ linePointSet 0 = {0}
    ∧ linePointSet 3 ∩ linePointSet 0 = {1}
    ∧ linePointSet 4 ∩ linePointSet 0 = {1}
    ∧ linePointSet 5 ∩ linePointSet 0 = {2}
    ∧ linePointSet 6 ∩ linePointSet 0 = {2} := by
  simp only [linePointSet, lineByIndex, line1, line2, line3, line4, line5, line6, line7]
  norm_cast

end FanoPlane.BoolMap
