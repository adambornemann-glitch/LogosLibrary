# Clifford Periodicity and the Cl(9) Isomorphism

## Overview

A Lean 4 formalization of the 8-fold periodicity of real Clifford algebras
(Bott periodicity), organized as a verified lookup API for the classification
of Cl(n,0) and Cl(p,q).

The target result is **Cl(9,0) ≅ M₁₆(ℂ)**: the Clifford algebra of a
9-dimensional Riemannian manifold is intrinsically complex, with spinor
fiber ℂ¹⁶ and structure group U(16).  This is the algebraic foundation
for the shiab operator in the Observerse Lagrangian.

The uniqueness theorem closes the circle: **n = 3 is the only base
dimension** for which the chimeric bundle Met(Xⁿ) produces a complex
Clifford algebra with 16-dimensional spinors.

## What This Is (and What It Is Not)

This is a **conditional formalization**.  The eight base cases of the
periodicity table (Cl(0) through Cl(7)) are *asserted* as definitions,
not *derived* from the universal property of Clifford algebras.  A full
derivation would require constructing Cl(n) as a quotient of the tensor
algebra T(ℝⁿ), proving the universal property, computing explicit
isomorphisms for each base case, and establishing the graded tensor
product decomposition Cl(n+2) ≅ Cl(n) ⊗̂ Cl(2).  This is beyond current
Mathlib infrastructure.

What Lean *does* verify:

- Every dimensional consistency condition (realDim = 2ⁿ, the
  field-dimension decomposition for simple and double algebras)
- The periodicity step as a computable function on classification data
- Agreement between the step function and hand-written entries
- All universal characterization theorems (complex iff n ≡ 1,5 mod 8, etc.)
- The ABS classification for indefinite signatures Cl(p,q)
- Signature cancellation, signature robustness, and the parity obstruction
- The uniqueness of n = 3 as the base dimension yielding ℂ¹⁶ spinors
- The Hermitian decomposition M₁₆(ℂ) = u(16) ⊕ iu(16)

The base cases are the axioms; everything else is machine-checked.

## Sign Convention

Throughout this development, Cl(n,0) uses the **negative-definite** relation:

    v · v = −Q(v),  so  eᵢ² = −1

This is the geometric algebra / differential geometry convention.  Under
this convention, Cl(1,0) = span{1, e₁} with e₁² = −1 is isomorphic to ℂ.

The positive-definite convention (eᵢ² = +1) gives a different table,
related to ours by the conjugation map n ↦ (8 − n) mod 8 — the Möbius
twist of the Bott clock (see Mobius.lean).

## File Structure

### Basic.lean — Foundations

- `CliffordBaseField`: the three associative division algebras (ℝ, ℂ, ℍ)
- `CliffordAlgStructure`: simple (M_k(F)) vs. double (M_k(F) ⊕ M_k(F))
- `CliffordData`: the complete classification datum for a Clifford algebra
  (dimension, base field, matrix size, structure type, with consistency proofs)

### Table.lean — The Periodicity Table

- Explicit `CliffordData` definitions for Cl(0) through Cl(15)
- `cliffordStep`: the period-8 function Cl(n) ↦ Cl(n+8), encoding
  the tensor product Cl(n+8) ≅ Cl(n) ⊗ M₁₆(ℝ)
- Verification theorems: `cliffordStep cl1 = cl9`, etc.
- `cliffordTable`: the base period as a function Fin 8 → (Field, Structure)

### Clock.lean — Universal Characterization

- `fieldAt`, `structureAt`: classification functions for arbitrary n
- **The characterization theorem**: Cl(n) is complex iff n ≡ 1 or 5 mod 8
- Complete partition of the Bott clock by field type and structure type
- The palindrome symmetry (field pattern on positions 0–6)
- Period-2 clockwork: even and odd orbits under the +2 step
- **ℂ is the unique always-simple field**: complex Clifford algebras never split
- **ℂ is the unique fixed point of ⊗ ℍ**: the algebraic engine of periodicity
- The triple characterization: complex ↔ odd orbit ∧ simple ↔ positions {1, 5}

### Mobius.lean — The Two Symmetries

- `clockConjugate`: the map k ↦ (8−k) mod 8 (signature reversal)
- The palindrome reflection: k ↦ (6−k) on positions 0–6 (field-preserving)
- **Conjugation destroys complex structure**: every complex position maps
  to a non-complex position under signature reversal
- **The complex–double duality**: conjugation establishes a perfect bijection
  between complex-simple positions and double positions
- Position 7 as the "seam" of the Möbius band

### Signature.lean — Indefinite Clifford Algebras Cl(p,q)

- `absIndex`: the Atiyah–Bott–Shapiro index (p−q) mod 8
- Compatibility: `absIndex n 0 = n % 8` (reduces to the existing API)
- **Signature robustness**: both Cl(9,0) and Cl(1,8) are complex and simple
- **Signature cancellation**: Cl(p+1, q+1) has the same type as Cl(p,q)
- **Conjugation = signature swap**: Cl(q,p) sits at the clock-conjugate of Cl(p,q)
- **Parity obstruction**: no signature split of an even-dimensional space
  can ever produce a complex Clifford algebra
- The chimeric bridge theorem: the Clifford tower of U⁹ is signature-invariant

### Dimensions.lean — Uniqueness of Dimension 9

- `metTotalDim`: the chimeric bundle dimension formula n(n+3)/2
- `complexMatDim`: matrix dimension as a function of position in the Bott clock
- **Dimension 9 is the unique complex slot with matDim = 16**:
  among all complex Clifford algebras Cl(m) with m ≡ 1 or 5 mod 8,
  only m = 9 gives 16-dimensional spinors
- **n = 3 is the unique base dimension**: the quadratic n(n+3)/2 = 9
  has n = 3 as its only positive solution — the chimeric construction
  over 3-manifolds is the unique source of ℂ¹⁶ spinors
- Survey of base dimensions n = 1 through 7: only n = 2 and n = 3
  produce complex Clifford algebras, and only n = 3 gives matDim = 16

### SpinorData.lean — Spinor Bundle and Hermitian Decomposition

- `SpinorBundleData`: complete data structure for the spinor bundle
  (fiber dimensions, structure group, unitarity)
- `spinorU9`: the spinor bundle of Cl(9) with fiber ℂ¹⁶ and structure
  group U(16) of dimension 256
- Spin(10) compatibility: the 16-dimensional spinor matches a single
  generation of Standard Model fermions
- `HermitianDecompData`: the decomposition M₁₆(ℂ) = u(16) ⊕ iu(16)
- **Dimensional match**: dim_ℝ M₁₆(ℂ) = 512 = 2⁹ = dim_ℝ Cl(9)
- The even split: u(16) and iu(16) each have real dimension 256

## Axiom Budget

**Zero axioms.  Zero sorry.**  Every theorem is proved by finite
computation (`fin_cases`, `simp`, `norm_num`, `omega`, `ring`).

The base cases of the periodicity table are definitions, not axioms.
They are guarded by the `hDimCheck` consistency condition, which
catches transposition errors by verifying the dimensional decomposition.

## Key Results for Downstream Use

| Theorem | Statement | File |
|---|---|---|
| `fieldAt_complex_iff` | Cl(n) is complex iff n ≡ 1, 5 mod 8 | Clock.lean |
| `complex_unique_fixed_point` | ℂ is the only field preserved by ⊗ ℍ | Clock.lean |
| `complex_implies_simple` | Complex Clifford algebras never split | Clock.lean |
| `complex_triple_char` | Complex ↔ odd orbit ∧ simple ↔ {1, 5} | Clock.lean |
| `complex_double_duality` | Conjugation bijects complex ↔ double | Mobius.lean |
| `chimeric_signature_robust` | Cl(9,0) and Cl(1,8) are both M₁₆(ℂ) | Signature.lean |
| `signature_cancellation` | Adding a (+,−) pair preserves the type | Signature.lean |
| `conjugate_is_signature_swap` | Cl(q,p) = clockConjugate of Cl(p,q) | Signature.lean |
| `signature_reversal_destroys_complex` | Cl(q,p) is never complex when Cl(p,q) is | Signature.lean |
| `even_total_dim_never_complex` | Even total dimension ⟹ never complex | Signature.lean |
| `unique_complex_matDim16` | m = 9 is the unique complex dim with matDim 16 | Dimensions.lean |
| `base_dim_3_unique` | n = 3 is the unique base dim yielding ℂ¹⁶ spinors | Dimensions.lean |
| `hermDecomp_matches_cl9` | dim_ℝ M₁₆(ℂ) = 512 = dim_ℝ Cl(9) | SpinorData.lean |

## The Periodicity Table

```
n mod 8 │ Cl(n,0)           │ Field │ Structure │ Spinor
────────┼───────────────────┼───────┼───────────┼────────
   0    │ M_k(ℝ)            │ ℝ     │ Simple    │ ℝ^k
   1    │ M_k(ℂ)            │ ℂ     │ Simple    │ ℂ^k
   2    │ M_k(ℍ)            │ ℍ     │ Simple    │ ℍ^k
   3    │ M_k(ℍ) ⊕ M_k(ℍ)   │ ℍ     │ Double    │ ℍ^k ⊕ ℍ^k
   4    │ M_k(ℍ)            │ ℍ     │ Simple    │ ℍ^k
   5    │ M_k(ℂ)            │ ℂ     │ Simple    │ ℂ^k
   6    │ M_k(ℝ)            │ ℝ     │ Simple    │ ℝ^k
   7    │ M_k(ℝ) ⊕ M_k(ℝ)   │ ℝ     │ Double    │ ℝ^k ⊕ ℝ^k
```

For n = 9:  9 mod 8 = 1  →  M₁₆(ℂ)  →  Spinor = ℂ¹⁶  →  U(16)

## References

- M. F. Atiyah, R. Bott, A. Shapiro, "Clifford modules," Topology 3 Suppl. 1 (1964), 3–38.
- H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton (1989), Chapter I.
- R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Springer GTM 82 (1982).