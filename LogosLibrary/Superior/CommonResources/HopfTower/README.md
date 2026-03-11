# HopfTower — The Cayley-Dickson Doubling Chain ℝ ↪ ℂ ↪ ℍ ↪ 𝕆

**Hopf fibrations, the tower of knots, the Fueter restriction chain,
and the octonionic endpoint.**

---

## Overview

Adams (1960) proved that the only fibre bundles of spheres are:

```
  S⁰ → S¹  → S¹     (real)
  S¹ → S³  → S²     (complex)
  S³ → S⁷  → S⁴     (quaternionic)
  S⁷ → S¹⁵ → S⁸     (octonionic)
```

These four fibrations correspond to the four normed division algebras.
They nest: each fibre is the previous level's total space. The S¹
thermal circle appears at the quaternionic level and persists at the
octonionic level. Adams says the tower terminates. Hurwitz says the
same thing in algebraic language.

This directory constructs the Hopf maps, proves the fibre actions
preserve them, establishes the self-similar tower structure, and
terminates the tower at the octonions via a constructive
non-associativity witness.

---

## Files

### HopfFibration.lean — The Quaternionic Hopf Map and Adams' Theorem

The central file. Constructs the quaternionic Hopf map S⁷ → S⁴ from
quaternion pairs (a, b) with ‖a‖² + ‖b‖² = 1:

```
  π(a, b) = (‖a‖² − ‖b‖², 2ab̄)
```

**What is proved:**

- **Sphere-to-sphere** — the fundamental norm identity
  (‖a‖²−‖b‖²)² + 4‖a‖²‖b‖² = (‖a‖²+‖b‖²)² guarantees the Hopf map
  sends S⁷ to S⁴.

- **S³ fibre action** — right multiplication (a,b) ↦ (aq, bq) by unit
  quaternion q preserves both S⁷ and the Hopf projection. Both
  components (real and quaternionic) are individually invariant. The
  action is free (principal bundle).

- **S¹ sub-fibre persistence** — the embedding θ ↦ ⟨cos θ, sin θ, 0, 0⟩
  lands on S³ (unit quaternions), and the S¹ action on S⁷ preserves
  the quaternionic Hopf map automatically (as a special case of S³
  invariance). The S¹ subgroup is closed under composition, has
  identity at θ = 0, and period 2π.

- **Real Hopf map** — the squaring map z ↦ z² on S¹ → S¹, with S⁰
  fibre ({±1} = antipodal points).

- **Adams' theorem** — axiomatised (5 axioms: existence of the four
  Hopf fibrations plus the classification theorem). Consequences:
  no sedenion Hopf, valid fibre/total/base dimensions are
  {0,1,3,7}/{1,3,7,15}/{1,2,4,8}.

- **Unified Hopf tower** — connects the Hopf fibrations to the NDA
  classification from DivisionAlgebra. Tower nesting, dimension sums,
  fibre dimension sequence, the single-axion theorem (tower version),
  pipeline theorems for SU(2) and SU(3), and the no-fifth-gauge-group
  theorem.

**Stats:** ~55 theorems, 0 sorry, 5 axioms (Adams).

### HopfTowerKnot.lean — The Tower of Knots

The self-similarity of the Hopf tower under Cayley-Dickson doubling.
Three topological "knots" (binding theorems), one analytic chain,
and one fibre inclusion sequence.

**Knot I (ℝ → ℂ):** The real Hopf map is the restriction of the
complex Hopf map under the embedding (x, y) ↦ (x, 0, y, 0). The
two realHopf components appear as hopfMap₃ and hopfMap₁, with
hopfMap₂ = 0 (the equatorial constraint). The S⁰ fibre {±1} is
the S¹ fibre restricted to {θ = 0, θ = π}.

**Knot II (ℂ → ℍ):** The complex Hopf map is the restriction of
the quaternionic Hopf map under the embedding
(a, b, c, d) ↦ (⟨a,b,0,0⟩, ⟨c,d,0,0⟩). Two quaternionic components
vanish (the transverse directions). The S¹ fibre is a sub-fibre
of S³.

**Knot III (ℝ → ℍ, composed):** The real Hopf map recovered directly
from the quaternionic Hopf map, with maximal transverse vanishing
(3 components zero).

**Fueter restriction chain:** The Fueter operator
(quaternionic Cauchy-Riemann, symbol ∂̄*∂̄ = Δ₄) restricts to the
Cauchy-Riemann operator (Δ₂) by setting σ₂ = σ₃ = 0, and further
to the ordinary derivative (Δ₁) by setting σ₁ = 0. Verified at
the symbol level as polynomial identities.

**Fibre chain:** S⁰ ⊂ S¹ ⊂ S³ with S¹ as maximal torus (the
largest commutative subgroup of S³). S³ non-commutativity is proved
by witness: 𝐢𝐣 = 𝐤 ≠ −𝐤 = 𝐣𝐢.

**Master theorem:** A single 14-part conjunction assembling all three
knots, the Fueter chain, the fibre inclusions, and the self-similarity.

**Stats:** ~50 theorems, 0 sorry, 0 axioms.

### HopfTowerOctonion.lean — The Octonionic Extension and Endpoint

Extends the tower to the octonions 𝕆 = ℍ × ℍ via Cayley-Dickson
doubling.

**Octonion infrastructure:** The type `𝕆ℝ` (quaternion pairs), the
Cayley-Dickson multiplication (ac − d̄b, da + bc̄), conjugation
(ā, −b), norm squared (‖a‖² + ‖b‖²), and the fundamental identity
x · x̄ = (‖x‖², 0) with all imaginary parts vanishing.

**Knot IV (ℍ → 𝕆):** The quaternionic Hopf map is the restriction of
the octonionic Hopf map under the embedding q ↦ (q, 0). Four
transverse components vanish (the entire right quaternion). Quaternion
multiplication embeds faithfully: octMul of embedded quaternions
equals embedded quaternion multiplication.

**Knot V (ℝ → 𝕆, composed):** The real Hopf map recovered from the
octonionic Hopf map through the composed embedding x ↦ ((x,0,0,0), 0).

**Extended Fueter chain:** Δ₈ → Δ₄ → Δ₂ → Δ₁, with the octonionic
Fueter operator restricting to the quaternionic one by setting
σ₄ = σ₅ = σ₆ = σ₇ = 0.

**Non-associativity witness:** The octonions fail associativity:
(e₁ · e₂) · e₄ ≠ e₁ · (e₂ · e₄), proved by explicit computation.
But embedded quaternions remain associative (the ℍ subalgebra is
preserved).

**Self-similarity:** Dimension doubling across all three levels
(sphere dims 1→3→7→15, base dims 1→2→4→8, transverse vanishing
1→2→4). The hypothetical next level would require S³¹, S¹⁶ — but
there is no 16-dimensional NDA.

**Complete tower master theorem:** An 11-part conjunction assembling
Knot IV, Knot V, the extended Fueter chain, non-associativity,
embedded associativity, and dimension doubling.

**Stats:** ~50 theorems, 0 sorry, 0 axioms.

---

## The Pattern

Every binding theorem has the same structure:

1. Embed the lower algebra into the higher one by zeroing the new
   Cayley-Dickson coordinates.
2. The higher Hopf map restricts to the lower Hopf map.
3. Transverse components vanish (1 for Knot I, 2 for Knot II,
   4 for Knot IV — powers of two).
4. The lower fibre is a sub-fibre of the higher fibre.
5. The Fueter operator restricts to the lower operator.

This self-similarity *is* the Cayley-Dickson construction viewed
through the Hopf lens.

```
  ℝ ════════╗
  ║  Knot I ║
  ℂ ════════╬═══════╗
  ║ Knot II ║       ║
  ℍ ════════╬═══════╬═══════╗
  ║ Knot IV ║       ║       ║
  𝕆 ════════╝  Knot III    Knot V
  ║                 ║       ║
  (TOWER ENDS)      ║       ║
  ╚═════════════════╝═══════╝

  S⁰ ──→ S¹ ──→ S³ ──→ S⁷        (fibres)
  Δ₁ ←── Δ₂ ←── Δ₄ ←── Δ₈        (Laplacians)
  1      2      4      8  → 16?   (dimensions)
  ℝ      ℂ      ℍ      𝕆  → 𝕊?    (algebras)
                            ↑
                       zero divisors!
```

---

## What Is Proven vs What Is Assumed

**Axioms: 5** (all in HopfFibration.lean, all encoding Adams' theorem)

- `SphereFibrationExists` — opaque predicate
- `realHopf_exists`, `complexHopf_exists`, `quaternionicHopf_exists`,
  `octonionicHopf_exists` — the four fibrations exist
- `adams_theorem` — these are the *only* sphere fibrations

Adams' theorem requires K-theory and Adams operations. Formalising the
proof would be a major project in its own right (and would be a
contribution to Mathlib, not to physics). The axiomatisation is honest
and clearly labelled.

Everything else — the Hopf maps, fibre actions, norm identities, tower
nesting, self-similarity, the octonionic endpoint — is proved from
quaternion arithmetic and the axiomatised Adams classification.

**Structure fields: 0.** These files make no physical assumptions.
The Hopf maps are constructed from quaternion pairs, the fibre actions
are right multiplication, and the binding theorems are equalities of
real and quaternionic expressions. Physics enters only in the comments.

---

## Combined Statistics

| File | Theorems | sorry | Axioms |
|------|:--------:|:-----:|:------:|
| HopfFibration.lean | ~55 | 0 | 5 |
| HopfTowerKnot.lean | ~50 | 0 | 0 |
| HopfTowerOctonion.lean | ~50 | 0 | 0 |
| **Total** | **~155** | **0** | **5** |

---

## A Note on Self-Containment

Each file reproduces certain quaternion definitions (qConj, normSq,
normSq_mul, etc.) locally rather than importing them from
Quaternions.lean. This is deliberate. It means each file can be read,
reviewed, and type-checked in isolation — you do not need to hold the
entire dependency graph in your head to verify that the Hopf map sends
spheres to spheres. The full library uses proper imports; the local
copies are for reviewability.

---

## Downstream Usage

HopfTower is imported by:

- `KnotTheory/Knots/` — the Hopf Knot and Extended Knot
- `KnotTheory/Strings/` — S¹ fibre persistence, Hopf dimensions
- `SpectralTriples/` — Hopf tower for U⁹ spectral action
- `SuperCausets/` — quaternion forcing via Hopf base dimension

---

## License

MIT. See [LICENSE](../../LICENSE).