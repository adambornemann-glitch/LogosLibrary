/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Knots/FueterRestriction.lean
-/
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Defs
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_III
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_IV
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_V
/-!
=====================================================================
## Part IV: The Fueter Restriction Chain
=====================================================================

The ANALYTIC counterpart of the topological tower.

The Fueter symbol:  σ̃ = σ₀ + 𝐢σ₁ + 𝐣σ₂ + 𝐤σ₃
Its conjugate:     σ̃* = σ₀ - 𝐢σ₁ - 𝐣σ₂ - 𝐤σ₃

Product:  σ̃* · σ̃ = (σ₀² + σ₁² + σ₂² + σ₃²) · 1 = Δ₄ · 1

Restrict σ₂ = σ₃ = 0:
  σ̃*σ̃ = (σ₀² + σ₁²) · 1 = Δ₂ · 1     (Cauchy-Riemann)

Restrict σ₁ = σ₂ = σ₃ = 0:
  σ̃*σ̃ = σ₀² · 1 = Δ₁ · 1              (ordinary derivative)

Same embedding pattern: zero out the Cayley-Dickson coordinates.
=====================================================================
-/
namespace HopfTower.Properties
open HopfTower.Defs HopfTower.Knots Real

section FueterChain

/-- **THE FULL FUETER-LAPLACIAN**:  σ̃* · σ̃ = Δ₄ -/
theorem fueter_laplacian (σ₀ σ₁ σ₂ σ₃ : ℝ) :
    fueterConjSymbol σ₀ σ₁ σ₂ σ₃ * fueterSymbol σ₀ σ₁ σ₂ σ₃ =
    ⟨σ₀ ^ 2 + σ₁ ^ 2 + σ₂ ^ 2 + σ₃ ^ 2, 0, 0, 0⟩ := by
  unfold fueterConjSymbol fueterSymbol
  ext <;> simp only [QuaternionAlgebra.mk_mul_mk, mul_neg, neg_mul, one_mul, neg_neg, mul_one,
    neg_zero, zero_mul, add_zero, sub_neg_eq_add] <;> ring

/-- **RESTRICTION TO ℂ: CAUCHY-RIEMANN → Δ₂**

    Set σ₂ = σ₃ = 0.  The Fueter operator becomes the
    Cauchy-Riemann operator ∂/∂z̄ = ∂/∂σ₀ + i·∂/∂σ₁.

    The product σ̃*σ̃ = σ₀² + σ₁² is the 2D Laplacian.

    This is the analytic Knot II: the same zeroing-out that
    restricts the quaternionic Hopf to the complex Hopf also
    restricts the Fueter operator to the CR operator. -/
theorem cauchy_riemann_from_fueter (σ₀ σ₁ : ℝ) :
    fueterConjSymbol σ₀ σ₁ 0 0 * fueterSymbol σ₀ σ₁ 0 0 =
    ⟨σ₀ ^ 2 + σ₁ ^ 2, 0, 0, 0⟩ := by
  have h := fueter_laplacian σ₀ σ₁ 0 0
  simp at h; exact h

/-- **THE CR SYMBOL IS COMPLEX**

    When σ₂ = σ₃ = 0, the Fueter symbol ⟨σ₀, σ₁, 0, 0⟩ lives
    in the complex subalgebra ℂ ↪ ℍ.  Its product with the
    conjugate stays in ℂ (in fact, in ℝ).

    This mirrors the Hopf restriction: complex quaternions
    multiplied together stay complex. -/
theorem cr_symbol_complex (σ₀ σ₁ : ℝ) :
    (fueterSymbol σ₀ σ₁ 0 0).imJ = 0 ∧
    (fueterSymbol σ₀ σ₁ 0 0).imK = 0 ∧
    (fueterConjSymbol σ₀ σ₁ 0 0).imJ = 0 ∧
    (fueterConjSymbol σ₀ σ₁ 0 0).imK = 0 := by
  unfold fueterSymbol fueterConjSymbol; simp

/-- **RESTRICTION TO ℝ: ORDINARY DERIVATIVE → Δ₁**

    Set σ₁ = σ₂ = σ₃ = 0.  The Fueter operator becomes
    the ordinary derivative d/dσ₀.

    The product σ̃*σ̃ = σ₀² is the 1D Laplacian d²/dσ₀².

    This is the analytic Knot III: maximal restriction. -/
theorem ordinary_derivative_from_fueter (σ₀ : ℝ) :
    fueterConjSymbol σ₀ 0 0 0 * fueterSymbol σ₀ 0 0 0 =
    ⟨σ₀ ^ 2, 0, 0, 0⟩ := by
  have h := fueter_laplacian σ₀ 0 0 0
  simp at h; exact h

/-- **THE FULL RESTRICTION CHAIN**

    Δ₄ ──restrict──→ Δ₂ ──restrict──→ Δ₁

    Each step zeroes out one Cayley-Dickson level.
    The Laplacian drops dimension at each step. -/
theorem fueter_restriction_chain (σ₀ σ₁ σ₂ σ₃ : ℝ) :
    -- Full Fueter: 4D Laplacian
    (fueterConjSymbol σ₀ σ₁ σ₂ σ₃ * fueterSymbol σ₀ σ₁ σ₂ σ₃).re =
      σ₀ ^ 2 + σ₁ ^ 2 + σ₂ ^ 2 + σ₃ ^ 2
    ∧
    -- Restrict to ℂ: 2D Laplacian
    (fueterConjSymbol σ₀ σ₁ 0 0 * fueterSymbol σ₀ σ₁ 0 0).re =
      σ₀ ^ 2 + σ₁ ^ 2
    ∧
    -- Restrict to ℝ: 1D Laplacian
    (fueterConjSymbol σ₀ 0 0 0 * fueterSymbol σ₀ 0 0 0).re =
      σ₀ ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · -- Δ₄: extract .re from the full identity
    have h := fueter_laplacian σ₀ σ₁ σ₂ σ₃
    have : (fueterConjSymbol σ₀ σ₁ σ₂ σ₃ * fueterSymbol σ₀ σ₁ σ₂ σ₃).re =
           (⟨σ₀ ^ 2 + σ₁ ^ 2 + σ₂ ^ 2 + σ₃ ^ 2, 0, 0, 0⟩ : ℍℝ).re :=
      congrArg QuaternionAlgebra.re h
    simpa using this
  · -- Δ₂: extract .re from the CR identity
    have h := cauchy_riemann_from_fueter σ₀ σ₁
    have : (fueterConjSymbol σ₀ σ₁ 0 0 * fueterSymbol σ₀ σ₁ 0 0).re =
           (⟨σ₀ ^ 2 + σ₁ ^ 2, 0, 0, 0⟩ : ℍℝ).re :=
      congrArg QuaternionAlgebra.re h
    simpa using this
  · -- Δ₁: extract .re from the ordinary derivative identity
    have h := ordinary_derivative_from_fueter σ₀
    have : (fueterConjSymbol σ₀ 0 0 0 * fueterSymbol σ₀ 0 0 0).re =
           (⟨σ₀ ^ 2, 0, 0, 0⟩ : ℍℝ).re :=
      congrArg QuaternionAlgebra.re h
    simpa using this

/-- **SCALAR PROPERTY PERSISTS**

    At every level of restriction, the operator product is scalar
    (all imaginary parts vanish).  The Laplacian is always a
    scalar operator, regardless of which subalgebra we're in.  -/
theorem laplacian_scalar_at_every_level (σ₀ σ₁ σ₂ σ₃ : ℝ) :
    -- Δ₄: scalar
    (fueterConjSymbol σ₀ σ₁ σ₂ σ₃ * fueterSymbol σ₀ σ₁ σ₂ σ₃).imI = 0 ∧
    (fueterConjSymbol σ₀ σ₁ σ₂ σ₃ * fueterSymbol σ₀ σ₁ σ₂ σ₃).imJ = 0 ∧
    (fueterConjSymbol σ₀ σ₁ σ₂ σ₃ * fueterSymbol σ₀ σ₁ σ₂ σ₃).imK = 0
    ∧
    -- Δ₂: scalar
    (fueterConjSymbol σ₀ σ₁ 0 0 * fueterSymbol σ₀ σ₁ 0 0).imI = 0 ∧
    (fueterConjSymbol σ₀ σ₁ 0 0 * fueterSymbol σ₀ σ₁ 0 0).imJ = 0 ∧
    (fueterConjSymbol σ₀ σ₁ 0 0 * fueterSymbol σ₀ σ₁ 0 0).imK = 0
    ∧
    -- Δ₁: scalar (trivially, since the symbol is real)
    (fueterConjSymbol σ₀ 0 0 0 * fueterSymbol σ₀ 0 0 0).imI = 0 ∧
    (fueterConjSymbol σ₀ 0 0 0 * fueterSymbol σ₀ 0 0 0).imJ = 0 ∧
    (fueterConjSymbol σ₀ 0 0 0 * fueterSymbol σ₀ 0 0 0).imK = 0 := by
  have h₄ := fueter_laplacian σ₀ σ₁ σ₂ σ₃
  have h₂ := cauchy_riemann_from_fueter σ₀ σ₁
  have h₁ := ordinary_derivative_from_fueter σ₀
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Δ₄
  · exact congrArg QuaternionAlgebra.imI h₄ |>.symm ▸ rfl
  · exact congrArg QuaternionAlgebra.imJ h₄ |>.symm ▸ rfl
  · exact congrArg QuaternionAlgebra.imK h₄ |>.symm ▸ rfl
  -- Δ₂
  · exact congrArg QuaternionAlgebra.imI h₂ |>.symm ▸ rfl
  · exact congrArg QuaternionAlgebra.imJ h₂ |>.symm ▸ rfl
  · exact congrArg QuaternionAlgebra.imK h₂ |>.symm ▸ rfl
  -- Δ₁
  · exact congrArg QuaternionAlgebra.imI h₁ |>.symm ▸ rfl
  · exact congrArg QuaternionAlgebra.imJ h₁ |>.symm ▸ rfl
  · exact congrArg QuaternionAlgebra.imK h₁ |>.symm ▸ rfl

end FueterChain
/-!
=====================================================================
##The Extended Fueter Chain  Δ₈ → Δ₄ → Δ₂ → Δ₁
=====================================================================

The octonionic Fueter symbol:
  σ̃ = (⟨σ₀, σ₁, σ₂, σ₃⟩, ⟨σ₄, σ₅, σ₆, σ₇⟩)

Its conjugate:
  σ̃* = (⟨σ₀, -σ₁, -σ₂, -σ₃⟩, ⟨-σ₄, -σ₅, -σ₆, -σ₇⟩)

Product σ̃* · σ̃ should give Σσᵢ² = Δ₈ (the 8D Laplacian).

Restriction: set σ₄=σ₅=σ₆=σ₇=0 → back to Δ₄ (quaternionic Fueter).
=====================================================================
-/

section FueterOctonionic

/-- The octonionic Fueter symbol -/
def octFueterSymbol (σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇ : ℝ) : 𝕆ℝ :=
  ⟨⟨σ₀, σ₁, σ₂, σ₃⟩, ⟨σ₄, σ₅, σ₆, σ₇⟩⟩

/-- The conjugate octonionic Fueter symbol -/
def octFueterConjSymbol (σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇ : ℝ) : 𝕆ℝ :=
  ⟨⟨σ₀, -σ₁, -σ₂, -σ₃⟩, ⟨-σ₄, -σ₅, -σ₆, -σ₇⟩⟩

/-- Sanity check: the conjugate symbol IS octConj of the symbol -/
theorem octFueterConj_is_octConj (σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇ : ℝ) :
    octFueterConjSymbol σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇ =
    octConj (octFueterSymbol σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇) := by
  unfold octFueterConjSymbol octFueterSymbol octConj qConj
  ext <;> simp

/-- **THE OCTONIONIC FUETER-LAPLACIAN**: σ̃* · σ̃ gives Δ₈

    The right component vanishes (always true for x · conj(x)). -/
    theorem octFueter_laplacian_right (σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇ : ℝ) :
    (octMul (octFueterConjSymbol σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇)
            (octFueterSymbol σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇)).r = 0 := by
  unfold octMul octFueterConjSymbol octFueterSymbol qConj
  ext <;> simp <;> ring

/-- The left component of σ̃*·σ̃ is scalar -/
theorem octFueter_laplacian_scalar (σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇ : ℝ) :
    let prod := octMul (octFueterConjSymbol σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇)
                       (octFueterSymbol σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇)
    prod.l.imI = 0 ∧ prod.l.imJ = 0 ∧ prod.l.imK = 0 := by
  unfold octMul octFueterConjSymbol octFueterSymbol qConj
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> ring

/-- **THE 8D LAPLACIAN**: The real part of σ̃*·σ̃ = Σσᵢ²

    This is the fundamental identity of the octonionic Fueter operator. -/
theorem octFueter_laplacian_re (σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇ : ℝ) :
    (octMul (octFueterConjSymbol σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇)
            (octFueterSymbol σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇)).l.re =
    σ₀ ^ 2 + σ₁ ^ 2 + σ₂ ^ 2 + σ₃ ^ 2 +
    σ₄ ^ 2 + σ₅ ^ 2 + σ₆ ^ 2 + σ₇ ^ 2 := by
  unfold octMul octFueterConjSymbol octFueterSymbol qConj
  simp; ring

/-- **RESTRICTION TO ℍ: Δ₈ → Δ₄**

    Set σ₄ = σ₅ = σ₆ = σ₇ = 0.
    The octonionic Fueter operator becomes the quaternionic Fueter operator.

    This is the analytic Knot IV: same zeroing-out that restricts
    octHopf → quatHopf also restricts Δ₈ → Δ₄. -/
theorem fueter_oct_to_quat (σ₀ σ₁ σ₂ σ₃ : ℝ) :
    (octMul (octFueterConjSymbol σ₀ σ₁ σ₂ σ₃ 0 0 0 0)
            (octFueterSymbol σ₀ σ₁ σ₂ σ₃ 0 0 0 0)).l.re =
    σ₀ ^ 2 + σ₁ ^ 2 + σ₂ ^ 2 + σ₃ ^ 2 := by
  have h := octFueter_laplacian_re σ₀ σ₁ σ₂ σ₃ 0 0 0 0
  simp at h; exact h

/-- The restricted symbol is an embedded quaternionic symbol -/
theorem fueter_restriction_embeds (σ₀ σ₁ σ₂ σ₃ : ℝ) :
    octFueterSymbol σ₀ σ₁ σ₂ σ₃ 0 0 0 0 =
    embedOct (fueterSymbol σ₀ σ₁ σ₂ σ₃) := by
  unfold octFueterSymbol embedOct fueterSymbol; rfl

/-- **THE FULL EXTENDED FUETER CHAIN**: Δ₈ → Δ₄ → Δ₂ → Δ₁ -/
theorem extended_fueter_chain (σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇ : ℝ) :
    -- Δ₈: 8D Laplacian
    (octMul (octFueterConjSymbol σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇)
            (octFueterSymbol σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇)).l.re =
      σ₀ ^ 2 + σ₁ ^ 2 + σ₂ ^ 2 + σ₃ ^ 2 + σ₄ ^ 2 + σ₅ ^ 2 + σ₆ ^ 2 + σ₇ ^ 2
    ∧
    -- Δ₄: restrict to ℍ
    (octMul (octFueterConjSymbol σ₀ σ₁ σ₂ σ₃ 0 0 0 0)
            (octFueterSymbol σ₀ σ₁ σ₂ σ₃ 0 0 0 0)).l.re =
      σ₀ ^ 2 + σ₁ ^ 2 + σ₂ ^ 2 + σ₃ ^ 2
    ∧
    -- Δ₂: restrict to ℂ
    (octMul (octFueterConjSymbol σ₀ σ₁ 0 0 0 0 0 0)
            (octFueterSymbol σ₀ σ₁ 0 0 0 0 0 0)).l.re =
      σ₀ ^ 2 + σ₁ ^ 2
    ∧
    -- Δ₁: restrict to ℝ
    (octMul (octFueterConjSymbol σ₀ 0 0 0 0 0 0 0)
            (octFueterSymbol σ₀ 0 0 0 0 0 0 0)).l.re =
      σ₀ ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact octFueter_laplacian_re σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇
  · exact fueter_oct_to_quat σ₀ σ₁ σ₂ σ₃
  · -- Δ₂
    have h := octFueter_laplacian_re σ₀ σ₁ 0 0 0 0 0 0
    simp at h; linarith
  · -- Δ₁
    have h := octFueter_laplacian_re σ₀ 0 0 0 0 0 0 0
    simp at h; linarith

end FueterOctonionic

end HopfTower.Properties
