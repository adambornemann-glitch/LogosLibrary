# The Fano Plane and Seven Quaternionic Subalgebras of 𝕆

## Overview

A Lean 4 formalization of the Fano plane PG(2, F₂) as the incidence
geometry governing octonionic multiplication, together with the seven
quaternionic subalgebras of 𝕆 and their role in the three-generation
structure of the Standard Model.

## The Fano Plane

The Fano plane is the smallest projective plane: 7 points, 7 lines,
3 points per line, 3 lines per point, any two points on a unique line,
any two lines meeting in a unique point.

We use the **Cayley-Dickson labeling**, in which the octonions are
constructed as 𝕆 = ℍ × ℍ with basis elements:

    e₁ = (i,0)   e₂ = (j,0)   e₃ = (k,0)
    e₄ = (0,1)   e₅ = (0,i)   e₆ = (0,j)   e₇ = (0,k)

The seven lines (0-indexed as Fin 7 throughout):

    L₀ = {0, 1, 2}    L₁ = {0, 3, 4}    L₂ = {0, 5, 6}
    L₃ = {1, 3, 5}    L₄ = {1, 4, 6}    L₅ = {2, 3, 6}
    L₆ = {2, 4, 5}

This is NOT the standard cyclic labeling {1,2,4}, {2,3,5}, ...
(quadratic residues mod 7).  The two labelings are isomorphic as
abstract incidence structures but produce different multiplication
tables.  The Cayley-Dickson labeling is natural for our purposes
because L₀ = {0,1,2} is exactly the left-ℍ subalgebra — the
Knot IV embedding q ↦ (q, 0).

## The Boolean Map Strategy

The standard approach to quaternionic subalgebras exhibits explicit
coefficients: "x ∈ span{1, eᵢ, eⱼ, eₖ} iff ∃ a,b,c,d ∈ ℝ..."
This creates existential witnesses at every step.

The boolean map replaces existential quantification with universal
component vanishing.  An octonion x ∈ 𝕆 ≅ ℝ⁸ lies in the span of
a Fano line L = {p₁, p₂, p₃} iff its four off-line imaginary
components are zero:

    inLineSpan L x  ≡  ∀ j ∉ {p₁, p₂, p₃}, octComponent x (basisIdx j) = 0

No witnesses.  No coefficients.  Just zeros.  Every subalgebra
property reduces to: extract the zeros, substitute into octMul,
close with `ring`.

## File Structure

### Defs.lean — Combinatorial and Algebraic Foundations

- `FanoPoint`, `FanoLine`: the incidence structure
- Seven line definitions with distinctness proofs
- `octBasis`: the seven imaginary octonion basis elements in ℍ × ℍ
- `inLineSpan`: the boolean characterization of subalgebra membership
- `fanoMul`, `fanoSign`: the octonionic multiplication table on Fin 7
- `octComponent`, `basisIdx`: coordinate extraction machinery
- `OctAutomorphism`: structure for ℝ-linear multiplicative bijections of 𝕆
- `IsQuatSubalgebra`: basis-independent predicate for quaternionic subalgebras
- `intersectionClass`: the three-class partition of non-Knot-IV lines
- Incidence properties: `three_lines_per_point`, `two_points_one_line`

### BoolMap.lean — The Seven Subalgebras

- **`quatSubalgebra_closed`**: each Fano-line span is closed under octMul
  (7 lines × 4 off-line components = 28 goals, all by `ring`)
- **`quatSubalgebra_associative`**: each subalgebra is associative
  (7 individual proofs, 12 zero extractions per proof, closed by `ring`)
- **`knotIV_is_fano_line`**: the Hopf tower embedding q ↦ (q, 0) lands in L₀
- **`two_lines_generate`**: any two distinct lines generate all 7 points
  under one round of fanoMul (42 cases, all by `decide`)
- **`octBasis_mul_ne`**: the complete 7×7 off-diagonal multiplication table,
  all 42 entries verified against Cayley-Dickson
- **`multiplication_table`**: diagonal (eᵢ² = −1) and off-diagonal unified
- **`fano_line_pairing`**: the six non-Knot-IV lines partition into three
  pairs by intersection with L₀, giving the combinatorial skeleton of
  the three-generation structure

### G2Automorphisms.lean — G₂ and Three Generations

- **`aut_preserves_identity`**: every octonion automorphism fixes 1 ∈ 𝕆
  (proved from idempotent analysis + injectivity, no axioms)
- **`standard_is_quat_subalgebra`**: each Fano-line span satisfies the
  basis-independent subalgebra predicate
- **`aut_preserves_quat_subalgebra`**: automorphisms map quaternionic
  subalgebras to quaternionic subalgebras
- **`aut_determined_by_basis`**: an automorphism is determined by its
  values on the seven basis elements (via `oct_decompose` + linearity)
- **`three_generation_decomposition`**: 7 = 1 + 2 + 2 + 2, with each
  class having exactly 2 members, 3 classes total, exhausting all
  non-Knot-IV lines
- Three axioms from exceptional Lie group theory (see below)

## Axiom Budget

### Proved (0 axioms, 0 sorry)

Everything in Defs.lean and BoolMap.lean is fully proved by finite
computation.  In G2Automorphisms.lean, all results in Part I
(automorphism structure preservation) are fully proved.

### Axiomatized (3 axioms)

The three-generation theorem requires Lie group theory beyond current
Mathlib infrastructure.  Three axioms are used:

| Axiom | Content | Reference |
|---|---|---|
| `g2_transitive_on_subalgebras` | For any two Fano lines, ∃ automorphism mapping one to the other | Cartan 1914; Baez 2002 §4.1 |
| `three_orbits_part_a` | Lines in the same intersection class are conjugate under Stab(e₁) | Furey 2016 |
| `three_orbits_part_b` | Lines in different intersection classes are not conjugate under Stab(e₁) | Furey 2016 |

The first axiom gives **canonicality**: the choice of distinguished
subalgebra does not matter.  The second and third together give
**three generations**: exactly three orbits of size two under the
SU(3) stabilizer.

## The Three-Generation Argument (Summary)

1. The octonions 𝕆 contain exactly seven standard quaternionic
   subalgebras, one per Fano line.  *(Proved: `standard_is_quat_subalgebra`)*

2. Fix one subalgebra as distinguished (Knot IV = L₀).  The remaining
   six partition into three pairs by intersection with L₀.
   *(Proved: `fano_line_pairing`, `class_size_two`, `three_classes`)*

3. G₂ = Aut(𝕆) acts transitively on subalgebras, so the choice of
   distinguished subalgebra is canonical.  *(Axiom: `g2_transitive_on_subalgebras`)*

4. The stabilizer Stab_{G₂}(e₁) ≅ SU(3) preserves the three
   intersection classes, giving exactly three orbits of size two.
   *(Axioms: `three_orbits_part_a`, `three_orbits_part_b`)*

5. Each orbit corresponds to one generation of Standard Model fermions.
   The factor of 3 is a theorem of incidence geometry, not numerology.

## The Octonion–Clifford Connection

The octonions are the fourth normed division algebra, but they do NOT
appear as a base field for Clifford algebras because they are not
associative.  The `CliffordBaseField` type in CliffordPeriodicity/Basic.lean
has exactly three constructors (ℝ, ℂ, ℍ) — the Fano plane is the
*obstruction* that explains why there is no fourth.

The connection runs deeper: Cl(6,0) ≅ M₈(ℝ) has an 8-dimensional
spinor (the same dimension as 𝕆), and the even subalgebra
Cl⁰(8,0) ≅ M₈(ℝ) ⊕ M₈(ℝ) gives the two half-spinor representations
whose triality under Spin(8) is intimately connected to octonionic
structure.  The Fano plane encodes where associativity fails in 𝕆;
the Bott clock encodes which associative algebras survive.

## References

- J. Baez, "The Octonions," Bull. AMS 39 (2002), 145–205.
- C. Furey, "Standard Model Physics from an Algebra?" Ph.D. thesis (2016).
- É. Cartan, "Les groupes réels simples, finis et continus," Ann. Sci. ENS 31 (1914).
- M. F. Atiyah, R. Bott, A. Shapiro, "Clifford modules," Topology 3 Suppl. 1 (1964), 3–38.
- R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Springer GTM 82 (1982).