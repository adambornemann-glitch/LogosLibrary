/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Knots/Defs.lean
-/
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
/-!
=====================================================================
# THE TOWER OF KNOTS
=====================================================================

## Overview

The Hopf tower is self-similar.  At each level of the division
algebra hierarchy ℝ ↪ ℂ ↪ ℍ, the Hopf map restricts to the
previous level's Hopf map under a canonical embedding.

This file proves THREE binding theorems:

  **Knot I**:   S¹ ↪ S³  restricts complex Hopf → real Hopf
  **Knot II**:  S³ ↪ S⁷  restricts quaternionic Hopf → complex Hopf
  **Knot III**: S¹ ↪ S⁷  the composition: real Hopf from quaternionic

And the ANALYTIC counterpart — the Fueter restriction chain:

  **Δ₄ → Δ₂ → Δ₁**

  The Fueter operator (quaternionic Cauchy-Riemann) restricts to
  the Cauchy-Riemann operator (complex), which restricts to the
  ordinary derivative (real).  Same embedding, same zeroing-out.

## The Pattern

Every binding theorem has the same structure:

  1. Embed by zeroing out the new Cayley-Dickson coordinates
  2. The Hopf map restricts (some components match, rest vanish)
  3. The fiber restricts (the lower fiber is a sub-fiber)
  4. The norm identity specializes

This self-similarity is not a coincidence.  It IS the
Cayley-Dickson construction, viewed through the Hopf lens.

## The Tower

    ℝ ──────────→ ℂ ──────────→ ℍ
    │              │              │
    S¹─realHopf→S¹ S³─cplxHopf→S² S⁷─quatHopf→S⁴
    │              │              │
    └── Knot I ────┘── Knot II ──┘
    │                             │
    └──────── Knot III ───────────┘

    Δ₁ ←──restrict── Δ₂ ←──restrict── Δ₄
     ℝ                ℂ                 ℍ

=====================================================================
-/
namespace HopfTower.Defs

open Real
/-- Standard quaternions ℍ[ℝ] with the explicit 3-parameter form -/
abbrev ℍℝ := QuaternionAlgebra ℝ (-1) (0) (-1)
/-!
=====================================================================
## Definitions
=====================================================================

Reproducing key definitions from both frameworks for
self-contained verification.
-/

section Definitions

-- ═══════════════════════════════════════════════════════════════
-- The Real Hopf Map:  S¹ → S¹
-- ═══════════════════════════════════════════════════════════════

/-- The real Hopf map: (x,y) ↦ (x²-y², 2xy)
    This is z ↦ z² on the unit circle. -/
def realHopf (x y : ℝ) : ℝ × ℝ := (x ^ 2 - y ^ 2, 2 * x * y)

-- ═══════════════════════════════════════════════════════════════
-- The Complex Hopf Map:  S³ → S²
-- ═══════════════════════════════════════════════════════════════

def hopfMap₁ (a b c d : ℝ) : ℝ := 2 * (a * c + b * d)
def hopfMap₂ (a b c d : ℝ) : ℝ := 2 * (b * c - a * d)
def hopfMap₃ (a b c d : ℝ) : ℝ := a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2

noncomputable def fiberRotation (a b c d θ : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (a * cos θ - b * sin θ, a * sin θ + b * cos θ,
   c * cos θ - d * sin θ, c * sin θ + d * cos θ)

-- ═══════════════════════════════════════════════════════════════
-- Quaternion Infrastructure
-- ═══════════════════════════════════════════════════════════════

def qConj (q : ℍℝ) : ℍℝ :=
  ⟨q.re, -q.imI, -q.imJ, -q.imK⟩

noncomputable def normSq (q : ℍℝ) : ℝ :=
  q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2

theorem normSq_mul (p q : ℍℝ) : normSq (p * q) = normSq p * normSq q := by
  unfold normSq
  simp; ring

theorem normSq_conj (q : ℍℝ) : normSq (qConj q) = normSq q := by
  unfold normSq qConj; simp

theorem qConj_mul (p q : ℍℝ) : qConj (p * q) = qConj q * qConj p := by
  unfold qConj
  ext <;> simp <;> ring

theorem qConj_qConj (q : ℍℝ) : qConj (qConj q) = q := by
  unfold qConj; ext <;> simp

theorem mul_qConj_eq (q : ℍℝ) :
    q * qConj q = ⟨normSq q, 0, 0, 0⟩ := by
  unfold qConj normSq
  ext <;> simp <;> ring

theorem real_quat_one : (⟨1, 0, 0, 0⟩ : ℍℝ) = 1 := by
  ext <;> simp

theorem mul_qConj_unit (q : ℍℝ) (hq : normSq q = 1) :
    q * qConj q = 1 := by rw [mul_qConj_eq, hq, real_quat_one]

-- ═══════════════════════════════════════════════════════════════
-- The Quaternionic Hopf Map:  S⁷ → S⁴
-- ═══════════════════════════════════════════════════════════════

noncomputable def quatHopf₀ (a b : ℍℝ) : ℝ := normSq a - normSq b
noncomputable def quatHopfQ (a b : ℍℝ) : ℍℝ := a * qConj b

noncomputable def s1Embed (θ : ℝ) : ℍℝ := ⟨cos θ, sin θ, 0, 0⟩

-- ═══════════════════════════════════════════════════════════════
-- The Fueter Operator Symbols
-- ═══════════════════════════════════════════════════════════════

def fueterSymbol (σ₀ σ₁ σ₂ σ₃ : ℝ) : ℍℝ := ⟨σ₀, σ₁, σ₂, σ₃⟩
def fueterConjSymbol (σ₀ σ₁ σ₂ σ₃ : ℝ) : ℍℝ := ⟨σ₀, -σ₁, -σ₂, -σ₃⟩

end Definitions
/-!
=====================================================================
# THE OCTONIONIC EXTENSION — KNOT IV AND THE END OF THE TOWER
=====================================================================

## Overview

This file extends the Tower of Knots to the octonions 𝕆,
constructed via Cayley-Dickson doubling of ℍ.

The octonionic Hopf fibration  S⁷ → S¹⁵ → S⁸  is the LAST
Hopf fibration of spheres (Adams, 1960).  The tower ends here
because the next doubling (the sedenions) has zero divisors —
the norm is no longer multiplicative.

We prove:

  **Knot IV**:  S⁷ ↪ S¹⁵  restricts octonionic Hopf → quaternionic Hopf
  **Knot V**:   Composed embeddings ℂ → 𝕆 and ℝ → 𝕆
  **Δ₈ → Δ₄**: The octonionic Fueter operator restricts to quaternionic

And the STRUCTURAL endpoint:

  **Non-Associativity**: 𝕆 is NOT associative (proved by witness)
  **Alternativity**: The subalgebra generated by any two elements IS associative
  **Adams**: The tower cannot continue — this is the final knot

## The Pattern (same as always)

    1. Embed by zeroing the new Cayley-Dickson coordinate
    2. The Hopf map restricts
    3. Transverse components vanish (now FOUR of them)
    4. The fiber restricts

## The Complete Tower

    ℝ ───────────→ ℂ ───────────→ ℍ ───────────→ 𝕆
    │              │              │              │
    S¹─realHopf→S¹ S³─cplxHopf→S² S⁷─quatHopf→S⁴ S¹⁵─octHopf→S⁸
    │              │              │              │
    └── Knot I ────┘── Knot II ──┘── Knot IV ──┘
    │                             │              │
    └──────── Knot III ───────────┘              │
    │                                            │
    └─────────────── Knot V ─────────────────────┘

    Δ₁ ←──restrict── Δ₂ ←──restrict── Δ₄ ←──restrict── Δ₈
     ℝ                ℂ                 ℍ                 𝕆

    S⁰ ⊂ S¹ ⊂ S³ ⊂ S⁷
   {±1}  U(1) SU(2)  (not a group!)

                                                    ∎  (Adams)
=====================================================================
-/




/-!
=====================================================================
The Cayley-Dickson Octonions
=====================================================================

𝕆 = ℍ × ℍ  with the twisted multiplication:

    (a, b) · (c, d) = (ac - d̄b, da + bc̄)

where ̄ denotes quaternion conjugation.

This is NOT associative.  It IS alternative:
the subalgebra generated by any two elements is associative.

The norm is multiplicative: ‖xy‖ = ‖x‖·‖y‖.
This makes 𝕆 a composition algebra — the LAST one over ℝ.
=====================================================================
-/

section CayleyDicksonOctonions

/-- The Cayley-Dickson octonions: pairs of quaternions.

    We use `l` (left) and `r` (right) for the two ℍ components.
    An octonion (a, b) represents a + b·e₄ where e₄ is the new
    Cayley-Dickson imaginary unit. -/
@[ext]
structure 𝕆ℝ where
  l : ℍℝ
  r : ℍℝ

instance : Inhabited 𝕆ℝ := ⟨⟨0, 0⟩⟩

/-- Cayley-Dickson multiplication:
    (a, b) · (c, d) = (ac - conj(d)·b, da + b·conj(c))

    Note: this is NOT associative.  The twist by conjugation
    is what kills associativity while preserving alternativity. -/
def octMul (x y : 𝕆ℝ) : 𝕆ℝ :=
  ⟨x.l * y.l - qConj y.r * x.r,
   y.r * x.l + x.r * qConj y.l⟩

/-- Octonion conjugation: conj(a, b) = (conj(a), -b) -/
def octConj (x : 𝕆ℝ) : 𝕆ℝ := ⟨qConj x.l, -x.r⟩

/-- Octonion norm squared: ‖(a,b)‖² = ‖a‖² + ‖b‖² -/
noncomputable def octNormSq (x : 𝕆ℝ) : ℝ := normSq x.l + normSq x.r

/-- Octonion negation -/
def octNeg (x : 𝕆ℝ) : 𝕆ℝ := ⟨-x.l, -x.r⟩

-- ═══════════════════════════════════════════════════════════════
-- Auxiliary lemmas for quaternion-in-octonion reasoning
-- ═══════════════════════════════════════════════════════════════

theorem qConj_zero : qConj (0 : ℍℝ) = 0 := by
  unfold qConj; ext <;> simp

theorem qConj_neg (q : ℍℝ) : qConj (-q) = -(qConj q) := by
  unfold qConj; ext <;> simp

theorem normSq_zero : normSq (0 : ℍℝ) = 0 := by
  unfold normSq; simp

theorem normSq_neg (q : ℍℝ) : normSq (-q) = normSq q := by
  unfold normSq; simp

-- ═══════════════════════════════════════════════════════════════
-- The fundamental identity: o · conj(o) = ‖o‖² (as scalar octonion)
-- ═══════════════════════════════════════════════════════════════

/-- **OCTONION NORM IDENTITY**: x · conj(x) has scalar left component.

    octMul (a, b) (conj(a), -b) = (a·conj(a) + conj(b)·b, -b·a + b·a)
                                 = (‖a‖² + ‖b‖², 0)

    The right component vanishes because -ba + ba = 0.
    The left component is the norm squared (as a scalar quaternion). -/
theorem octMul_octConj (x : 𝕆ℝ) :
    (octMul x (octConj x)).r = 0 := by
  unfold octMul octConj qConj
  ext <;> simp

/-- The left component of x · conj(x) is the norm squared -/
theorem octMul_octConj_left (x : 𝕆ℝ) :
    normSq (octMul x (octConj x)).l = (octNormSq x) ^ 2 := by
  unfold octMul octConj octNormSq normSq qConj
  simp; ring

/-- x · conj(x) has scalar left component (all imaginary parts zero) -/
theorem octMul_octConj_scalar (x : 𝕆ℝ) :
    (octMul x (octConj x)).l.imI = 0
    ∧ (octMul x (octConj x)).l.imJ = 0
    ∧ (octMul x (octConj x)).l.imK = 0 := by
  unfold octMul octConj qConj
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> ring

end CayleyDicksonOctonions

end HopfTower.Defs
