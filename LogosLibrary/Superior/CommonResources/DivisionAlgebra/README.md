# DivisionAlgebra — Hurwitz Classification and Gauge Correspondence

**The four normed division algebras and everything that follows from them.**

---

## Overview

The only normed division algebras over ℝ are:

| Algebra | Dimension | Cayley-Dickson step | Commutative | Associative | Alternative |
|---------|:---------:|:-------------------:|:-----------:|:-----------:|:-----------:|
| ℝ | 1 | 0 | ✓ | ✓ | ✓ |
| ℂ | 2 | 1 | ✓ | ✓ | ✓ |
| ℍ | 4 | 2 | ✗ | ✓ | ✓ |
| 𝕆 | 8 | 3 | ✗ | ✗ | ✓ |

This is Hurwitz's theorem (1898). There is no fifth entry. The
Cayley-Dickson construction at step 4 produces the sedenions (dim 16),
which have zero divisors — the norm-composition identity ‖xy‖ = ‖x‖·‖y‖
fails, and with it the entire algebraic machinery.

This directory encodes the classification as a Lean 4 inductive type with
exactly four constructors. The type *is* the theorem: every property
is established by structural induction on a finite type with no axioms.

---

## Files

### Basic.lean

The main classification file. Contains:

**The NDA type** — an inductive type with four constructors (`.real`,
`.complex`, `.quaternion`, `.octonion`). Dimension, Cayley-Dickson step,
and all algebraic properties are computable functions on this type.

**Algebraic properties** — the hierarchy Commutative ⊂ Associative ⊂
Alternative, with ℍ as the first non-commutative algebra and 𝕆 as
the only non-associative NDA. The key theorem: all four NDAs are
alternative (the weakest useful identity, x(xy) = x²y).

**Hurwitz classification** — valid dimensions are {1, 2, 4, 8}, the
NDA is uniquely determined by its dimension (or by its Cayley-Dickson
step), and there are exactly four.

**Gauge correspondence** — a bijection between {U(1), SU(2), SU(3)} and
{ℂ, ℍ, 𝕆}, with round-trip theorems in both directions, injectivity,
and the Standard Model completeness theorem: every non-trivial NDA has
a gauge factor and every gauge factor has an NDA. There is no SU(4)
because there is no 16-dimensional NDA.

**Entropy manifolds** — the unit sphere S^{dim−1} of each NDA, with
dimension formula, Mersenne-like structure (dims are 2^step − 1), and
the sum 0 + 1 + 3 + 7 = 11.

**Hopf fibration data** — fibre, total space, and base dimensions for
each NDA. Tower nesting (each fibre is the previous level's total
space), the S¹ thermal circle persistence theorem, and the single-axion
theorem.

**Dimensional coincidences that are not coincidences** — total SM algebra
dimension 14, total with ℝ is 15 = 2⁴ − 1 (Mersenne), entropy manifold
sum 11, total SM generators 12.

**Key theorems:**

- `standard_model_complete` — the SM has exactly three gauge factors
  because Hurwitz says so
- `hopf_tower_nesting` — each Hopf fibre is the previous total space
- `single_axion_from_fiber_persistence` — one S¹, one winding mode,
  one axion
- `dim_determines_NDA` — the NDA is unique given its dimension
- `no_dim_sixteen` — there is no 16-dimensional NDA

### Quaternions.lean

The quaternion algebra ℍ, built on Mathlib's `QuaternionAlgebra`.

**Basis and multiplication table** — the complete multiplication table
for {1, 𝐢, 𝐣, 𝐤}, including all six nontrivial products and the three
squares. A `quat_ext` tactic macro handles the component-level proofs.

**su(2) structure** — the commutation relations [𝐢, 𝐣] = 2𝐤 (and cyclic
permutations), antisymmetry, self-commutator vanishing, and the Jacobi
identity. The pure imaginary quaternions form a Lie algebra: closed under
addition, scalar multiplication, and the commutator bracket.

**ℝ³ identification** — embedding ℝ³ as pure imaginary quaternions via
`fromR3`, round-trip theorem, dot product, cross product, and the
quaternion product formula: for pure imaginary p, q,
p·q = −(p·q) + (p × q). This is why quaternions encode 3D geometry.

**Norm and conjugation** — conjugate, norm squared, non-negativity,
involution, anti-multiplicativity of conjugation, norm-squared
multiplicativity (the Euler four-square identity), and the
key fact that q·q̄ is real with value ‖q‖².

**Rotation action** — conjugation action q·v·q̄, norm preservation
(isometry), pure-imaginary preservation (rotations stay in ℝ³),
trivial action of 1, composition (group homomorphism), and the
kernel theorem: q and −q give the same rotation (the double cover
SU(2) → SO(3)).

---

## What Is Proven vs What Is Assumed

**Axioms: 0**

Everything is proved by structural induction on the four-constructor
`NDA` type, or by explicit computation on Mathlib's quaternion algebra.
Hurwitz's theorem is encoded in the type itself — the inductive type
has four constructors, and that is the classification.

A more foundational treatment would prove Hurwitz from the axioms of
normed algebras. That proof requires substantial real analysis and
algebraic topology (Adams' theorem for the topological version).
For the purposes of this library, encoding the classification as
a finite type is both correct and practical.

**Structure fields: 0**

These files make no physical assumptions. They are pure algebra and
combinatorics. The physical interpretation (gauge groups, entropy
manifolds, axions) is in the theorem *names* and *comments*, not in
the *proofs*. The proofs are about natural numbers, finite types,
and quaternion multiplication.

---

## Statistics

| File | Theorems | sorry | Axioms |
|------|:--------:|:-----:|:------:|
| Basic.lean | ~45 | 0 | 0 |
| Quaternions.lean | ~35 | 0 | 0 |
| **Total** | **~80** | **0** | **0** |

---

## Downstream Usage

DivisionAlgebra is imported by:

- `HopfTower/HopfFibration.lean` — uses `NDA` type and Hopf data
- `KnotTheory/Strings/` — uses gauge correspondence and dimensions
- `KnotTheory/YangMills/` — uses Hurwitz to force three gauge factors
- `SpectralTriples/` — uses NDA dimensions for Cl(9) context
- `SuperCausets/` — uses quaternion forcing theorem

---

## License

MIT. See [LICENSE](../../LICENSE).