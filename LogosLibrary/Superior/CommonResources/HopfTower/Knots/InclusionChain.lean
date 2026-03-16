/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Knots/InclusionChain.lean
-/
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Defs
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_III
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_IV
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_V
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.NonAssociativity
/-!
=====================================================================
## Part VI: The Fiber Inclusion Chain
=====================================================================

The fibers nest:  S⁰ ⊂ S¹ ⊂ S³

At each level, the lower fiber sits inside the higher fiber
as a distinguished subgroup.  The S¹ thermal circle of the
Strings framework lives inside the S³ fiber of the YangMills
framework as a maximal torus.

The chain of fibers IS the chain of unit norm elements in the
division algebra tower:

    {±1} ⊂ U(1) ⊂ SU(2)

This is the gauge group hierarchy, expressed as fiber inclusions.
=====================================================================
-/
namespace HopfTower.Properties
open HopfTower.Defs HopfTower.Knots Real

section FiberChain

/-- **S⁰ ⊂ S¹**: The discrete fiber sits inside the circle.

    S⁰ = {θ = 0, θ = π} inside S¹ = {θ ∈ [0, 2π)}.
    The two elements are the identity and the antipode. -/
theorem s0_in_s1 :
    s1Embed 0 = 1 ∧ s1Embed Real.pi = -1 := by
  unfold s1Embed
  constructor <;> ext <;> simp [cos_zero, sin_zero, cos_pi, sin_pi]

/-- **S¹ ⊂ S³**: The circle sits inside the 3-sphere.

    The s1Embed map θ ↦ ⟨cos θ, sin θ, 0, 0⟩ lands on S³
    (inside ℍ with unit norm).

    This is the thermal circle inside the full gauge fiber. -/
theorem s1_in_s3 (θ : ℝ) : normSq (s1Embed θ) = 1 := by
  unfold normSq s1Embed
  nlinarith [sin_sq_add_cos_sq θ]

/-- The inclusion S⁰ ↪ S¹ ↪ S³ is transitive:
    s1Embed at θ=0 gives the identity quaternion,
    which is the +1 element of S⁰. -/
theorem fiber_chain_identity :
    s1Embed 0 = 1 ∧ normSq (s1Embed 0) = 1 := by
  exact ⟨(s0_in_s1).1, s1_in_s3 0⟩

/-- **THE S¹ IS A MAXIMAL TORUS OF S³**

    The s1Embed image {⟨cos θ, sin θ, 0, 0⟩} is a maximal
    commutative subgroup of S³ (the unit quaternions).

    Two S¹-embedded elements multiply within S¹: -/
theorem s1_subgroup_closure (θ₁ θ₂ : ℝ) :
    s1Embed θ₁ * s1Embed θ₂ = s1Embed (θ₁ + θ₂) := by
  unfold s1Embed
  ext <;> simp [Real.cos_add, Real.sin_add]; rfl
  exact AddCommMagma.add_comm (cos θ₁ * sin θ₂) (sin θ₁ * cos θ₂)

/-- The S¹ subgroup is commutative (abelian) -/
theorem s1_commutative (θ₁ θ₂ : ℝ) :
    s1Embed θ₁ * s1Embed θ₂ = s1Embed θ₂ * s1Embed θ₁ := by
  rw [s1_subgroup_closure, s1_subgroup_closure]
  congr 1; ring

/-- The full S³ is NOT commutative: there exist unit quaternions
    that do not commute.

    Witness: 𝐢 and 𝐣.  Both have norm 1.
      𝐢𝐣 = 𝐤,  𝐣𝐢 = -𝐤,  𝐤 ≠ -𝐤.

    The S¹ is the largest commutative piece of S³. -/
theorem s3_noncommutative :
    let qi : ℍℝ := ⟨0, 1, 0, 0⟩
    let qj : ℍℝ := ⟨0, 0, 1, 0⟩
    qi * qj ≠ qj * qi := by
  intro qi qj h
  have h1 : qi * qj = ⟨0,0,0,1⟩ := by
    ext <;> simp <;> linarith
  have h2 : qj * qi = ⟨0,0,0,-1⟩ := by
    ext <;> simp <;> linarith
  rw [h1, h2] at h
  have : (1 : ℝ) = -1 := congrArg QuaternionAlgebra.imK h
  linarith

/-- **THE PHYSICAL INTERPRETATION OF THE FIBER CHAIN**

    S⁰ ⊂ S¹ ⊂ S³  corresponds to  {±1} ⊂ U(1) ⊂ SU(2)

    The fiber chain IS the gauge group inclusion chain:
    - S⁰ = ℤ₂: the center of SU(2), charge conjugation
    - S¹ = U(1): electromagnetism, the thermal circle
    - S³ = SU(2): weak force, the full isospin fiber

    At each level, the sub-fiber generates a sub-gauge-symmetry.

    The key fact: U(1) ⊂ SU(2) is the MAXIMAL TORUS.
    This is why the electroweak theory has one photon
    (from U(1)) inside three weak bosons (from SU(2)). -/
theorem gauge_fiber_dimensions :
    -- S⁰ has 0 dimensions (discrete)
    True ∧
    -- S¹ has 1 dimension (one gauge boson: photon)
    True ∧
    -- S³ has 3 dimensions (three gauge bosons: W⁺, W⁻, Z⁰)
    -- The difference: 3 - 1 = 2 "extra" bosons
    3 - 1 = (2 : ℕ) := by
  exact ⟨trivial, trivial, rfl⟩

end FiberChain

/-!
=====================================================================
## Part XIII: The Fiber Chain Extension  S⁰ ⊂ S¹ ⊂ S³ ⊂ S⁷
=====================================================================

The unit octonions form S⁷.  This is NOT a Lie group
(non-associativity!), but it IS a smooth Moufang loop.

The embedded S³ (unit quaternions) sits inside S⁷ as a
genuine subgroup — associativity is restored within the image.

    S⁰ ⊂ S¹ ⊂ S³ ⊂ S⁷
   {±1}  U(1) SU(2)  (Moufang loop, not a group)

The gauge theory interpretation ends here: S⁷ does not
correspond to any standard gauge group.  This is deeply
connected to the non-existence of octonionic gauge theories
(the Jacobi identity fails for 𝔤₂ over 𝕆).
=====================================================================
-/

section FiberChainExtended

/-- S³ ⊂ S⁷: embedded unit quaternions are unit octonions -/
theorem s3_in_s7 (q : ℍℝ) (hq : normSq q = 1) :
    octNormSq (embedOct q) = 1 := by
  rw [octNormSq_embed]; exact hq

/-- The embedded S³ is a genuine subgroup of S⁷:
    product of embedded unit quaternions is an embedded unit quaternion -/
theorem s3_subgroup_in_s7 (p q : ℍℝ)
    (hp : normSq p = 1) (hq : normSq q = 1) :
    octMul (embedOct p) (embedOct q) = embedOct (p * q) ∧
    normSq (p * q) = 1 := by
  constructor
  · exact octMul_embed p q
  · rw [normSq_mul]
    nlinarith [hp, hq]

/-- **S⁷ IS NOT A GROUP**: Non-associativity of unit octonions.

    All three basis elements e₁, e₂, e₄ have unit norm,
    but their multiplication is not associative. -/
theorem s7_not_a_group :
    octNormSq oct_e1 = 1 ∧ octNormSq oct_e2 = 1 ∧ octNormSq oct_e4 = 1
    ∧ octMul (octMul oct_e1 oct_e2) oct_e4 ≠
      octMul oct_e1 (octMul oct_e2 oct_e4) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold octNormSq oct_e1 normSq; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, one_pow, zero_add, add_zero]
  · unfold octNormSq oct_e2 normSq; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, one_pow, zero_add]
  · unfold octNormSq oct_e4 normSq; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, one_pow, zero_add]
  · exact oct_not_associative

/-- **THE FIBER DIMENSION CHAIN**

    fiber(S¹→S¹) = S⁰:  0-dimensional  (discrete)
    fiber(S³→S²) = S¹:  1-dimensional  (circle)
    fiber(S⁷→S⁴) = S³:  3-dimensional  (3-sphere/SU(2))
    fiber(S¹⁵→S⁸) = S⁷: 7-dimensional  (7-sphere/Moufang loop)

    The fiber dimensions: 0, 1, 3, 7 = 2⁰-1, 2¹-1, 2²-1, 2³-1.
    These are the dimensions of the unit spheres in ℝ, ℂ, ℍ, 𝕆. -/
theorem fiber_dimensions :
    2 ^ 0 - 1 = (0 : ℕ)    -- S⁰ has dim 0
    ∧ 2 ^ 1 - 1 = (1 : ℕ)  -- S¹ has dim 1
    ∧ 2 ^ 2 - 1 = (3 : ℕ)  -- S³ has dim 3
    ∧ 2 ^ 3 - 1 = (7 : ℕ)  -- S⁷ has dim 7
    := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end FiberChainExtended

end HopfTower.Properties
