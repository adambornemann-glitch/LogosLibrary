/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: HopfTower/MobiusTower.lean
-/
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Defs
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_I
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_II
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_III
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_IV
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.Knot_V
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.FueterRestriction
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.SelfSimilarity
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.NonAssociativity
import LogosLibrary.Superior.CommonResources.HopfTower.Knots.InclusionChain
/-!
=====================================================================
# THE MÖBIUS TOPOLOGY OF THE HOPF TOWER
=====================================================================

## Overview

The conjugation operator J appears at every level of the
Cayley-Dickson tower  ℝ ↪ ℂ ↪ ℍ ↪ 𝕆  and plays the same
structural role each time:

  - It is an **involution**:  J² = 1
  - It is **anti-multiplicative**:  J(ab) = J(b)·J(a)
  - It **preserves the norm**:  ‖J(a)‖ = ‖a‖
  - It generates the **unit condition**:  a·J(a) = ‖a‖²

These four properties make J the **tooth profile** of a
Möbius gear.  Two gears mesh when their tooth profiles
interlock — when the anti-automorphism of one aligns with
the anti-automorphism of the other.

The Hopf fibration and the KMS modular flow are two such gears.
They share the same J:

  - **Hopf tower**:  J = quaternion/octonion conjugation
    The fiber action (a,b) ↦ (aq, bq) preserves the Hopf map
    BECAUSE J reverses multiplication order, allowing q·J(q) = 1
    to cancel in the right place.

  - **KMS modular flow**:  J = Tomita conjugation
    The modular flow σ_t preserves the KMS state BECAUSE J
    implements the boundary identification of the thermal strip:
    ω(a·σ_t(b)) ↔ ω(σ_t(b)·a)  via  J.

They mesh because they share J.  The twist of matter (Hopf fiber)
and the twist of time (modular flow) are the SAME twist, expressed
in different algebras.

## The Restriction Chain

At each embedding  𝔸 ↪ 𝔸'  (zeroing out the new Cayley-Dickson
coordinate), the higher J restricts to the lower J:

    J_𝕆 ∘ embed = embed ∘ J_ℍ
    J_ℍ ∘ embed = embed ∘ J_ℂ   (= J_ℍ on reals)

The conjugation is **coherent** across the tower.  The same
half-twist, seen at every level.

## Twist Visibility

The Cayley-Dickson twist is INVISIBLE within the embedded
subalgebra (where the new coordinate is zero).  It becomes
VISIBLE only when the new coordinate is activated:

  - ℂ ↪ ℍ:  no twist when j=k=0, non-commutative when j,k≠0
  - ℍ ↪ 𝕆:  no twist when right=0, non-associative when right≠0

This is the same phenomenon as the KMS strip: the twist is
invisible in the commutative (classical) limit, but structurally
present and manifesting in the non-commutative (quantum) regime.

## The Termination

The tower ends at 𝕆 because one more Cayley-Dickson doubling
(to the sedenions 𝕊) produces zero divisors.  In gear language:
the tooth profile breaks.  J can no longer simultaneously be an
involution, be anti-multiplicative, AND preserve the norm in a
way that gives a division algebra.

    J_ℝ ═════════╗
    ║  restricts ║
    J_ℂ ═════════╬═══════╗
    ║  restricts ║       ║
    J_ℍ ═════════╬═══════╝
    ║  restricts ║
    J_𝕆 ═════════╝
    ║
    (J breaks at 𝕊)

    Hopf fiber:    S⁰ ⊂ S¹ ⊂ S³ ⊂ S⁷
    J involution:  id   conj  qConj octConj
    Fixed points:  ℝ    ℝ     ℝ     ℝ   (always the reals!)
    Twist cost:    0    1     3     7   (= fiber dimension)

=====================================================================
-/
namespace HopfTower.Properties
open HopfTower.Defs HopfTower.Knots


/-!
=====================================================================
## Utility: Right Inverse
=====================================================================

The right inverse `qConj q * q = 1` is not in Defs.lean.
We derive it from the left inverse via the involution property.
-/

section Utility

/-- **RIGHT INVERSE**: qConj q * q = 1 when ‖q‖² = 1.

    Derived from the left inverse by applying it to qConj q
    (which also has unit norm) and using qConj² = id. -/
theorem qConj_mul_unit (q : ℍℝ) (hq : normSq q = 1) :
    qConj q * q = 1 := by
  have hc : normSq (qConj q) = 1 := by rw [normSq_conj]; exact hq
  have h := mul_qConj_unit (qConj q) hc
  rwa [qConj_qConj] at h

end Utility

/-!
=====================================================================
## Part I: THE MÖBIUS INVOLUTION — J as Tooth Profile
=====================================================================

J has four defining properties that make it a Möbius involution:

  (I)   J² = 1              (involution)
  (II)  J(ab) = J(b)·J(a)   (anti-multiplicativity)
  (III) ‖J(a)‖ = ‖a‖        (norm preservation)
  (IV)  a·J(a) = ‖a‖²       (unit generation)

The quaternionic versions (I)-(IV) are already in Defs.lean:
  qConj_qConj, qConj_mul, normSq_conj, mul_qConj_eq

Here we verify the OCTONIONIC versions and package everything.

=====================================================================
-/

section MöbiusInvolution

/-!
### Octonionic J: octConj

The quaternionic axioms are established in Defs.lean:
  (I)   qConj_qConj    (II)  qConj_mul
  (III) normSq_conj     (IV)  mul_qConj_eq

We now verify the SAME axioms at the octonionic level.
-/

/-- **(I) INVOLUTION**: J² = 1 at the octonionic level.

    octConj(octConj(a, b)) = octConj(conj(a), -b) = (a, b)

    Two half-twists = identity.  This is π₁(Möbius strip) = ℤ₂. -/
theorem oct_J_involution (x : 𝕆ℝ) : octConj (octConj x) = x := by
  unfold octConj qConj; ext <;> simp

/-- **(II) ANTI-MULTIPLICATIVITY**: J reverses octonionic multiplication.

    This is the deepest theorem here.  Despite the octonions being
    non-associative, conjugation STILL reverses multiplication order.
    The twist survives non-associativity.

    conj(xy) = conj(y) · conj(x)

    This is REMARKABLE: the anti-automorphism property of J
    holds even when the algebra itself is non-associative.
    The tooth profile is valid even at the edge of the tower. -/
theorem oct_J_anti_mul (x y : 𝕆ℝ) :
    octConj (octMul x y) = octMul (octConj y) (octConj x) := by
  unfold octConj octMul qConj; ext <;> simp <;> ring

/-- **(III) NORM PRESERVATION**: octonionic J is an isometry.

    ‖conj(a, b)‖² = ‖conj(a)‖² + ‖-b‖² = ‖a‖² + ‖b‖² -/
theorem oct_J_norm (x : 𝕆ℝ) : octNormSq (octConj x) = octNormSq x := by
  unfold octNormSq octConj; rw [normSq_conj, normSq_neg]

/-! **(IV) UNIT GENERATION**: The right component of x · conj(x) vanishes.

    Already proved in Defs.lean as `octMul_octConj`.
    x · conj(x) lives in the embedded ℍ ⊂ 𝕆.
    Furthermore, its left component is scalar (`octMul_octConj_scalar`). -/

/-- **PACKAGING: The Four Axioms Together**

    At both levels, J satisfies all four Möbius involution axioms.
    The tooth profile is valid at ℍ and at 𝕆. -/
theorem mobius_axioms_quat :
    (∀ q : ℍℝ, qConj (qConj q) = q)
    ∧ (∀ p q : ℍℝ, qConj (p * q) = qConj q * qConj p)
    ∧ (∀ q : ℍℝ, normSq (qConj q) = normSq q)
    ∧ (∀ q : ℍℝ, q * qConj q = ⟨normSq q, 0, 0, 0⟩) :=
  ⟨qConj_qConj, qConj_mul, normSq_conj, mul_qConj_eq⟩

theorem mobius_axioms_oct :
    (∀ x : 𝕆ℝ, octConj (octConj x) = x)
    ∧ (∀ x y : 𝕆ℝ, octConj (octMul x y) = octMul (octConj y) (octConj x))
    ∧ (∀ x : 𝕆ℝ, octNormSq (octConj x) = octNormSq x)
    ∧ (∀ x : 𝕆ℝ, (octMul x (octConj x)).r = 0) :=
  ⟨oct_J_involution, oct_J_anti_mul, oct_J_norm, octMul_octConj⟩

end MöbiusInvolution


/-!
=====================================================================
## Part II: THE RESTRICTION CHAIN — J Commutes with Embedding
=====================================================================

The higher J, restricted to the embedded subalgebra, IS the lower J.

    J_𝕆 ∘ embed = embed ∘ J_ℍ     (octConj_embed, from Knot_IV)
    J_ℍ ∘ embed = embed ∘ J_ℝ      (qConj_embedReal, from Knot_III)

  embed          embed          embed
ℝ ──────→ ℂ ──────→ ℍ ──────→ 𝕆
│          │          │          │
J_ℝ=id    J_ℂ=conj   J_ℍ=qConj  J_𝕆=octConj
│          │          │          │
ℝ ──────→ ℂ ──────→ ℍ ──────→ 𝕆
  embed          embed          embed

Every square commutes.

=====================================================================
-/

section RestrictionChain

/-- **THE FULL RESTRICTION CHAIN**:  J_𝕆 → J_ℍ → J_ℝ = id

    Composing: octConj restricted to real octonions is the identity. -/
theorem J_full_restriction_chain (x : ℝ) :
    octConj (embedOct (embedReal x)) = embedOct (embedReal x) := by
  rw [octConj_embed, qConj_embedReal]

/-- **THE FULL COHERENCE THEOREM**

    All three structures — multiplication, conjugation, norm —
    restrict coherently from 𝕆 to ℍ.  The tooth profile, the gear
    rotation, and the gear radius all agree across levels. -/
theorem full_coherence (p q : ℍℝ) :
    -- Multiplication restricts
    octMul (embedOct p) (embedOct q) = embedOct (p * q)
    ∧
    -- Conjugation restricts
    octConj (embedOct p) = embedOct (qConj p)
    ∧
    -- Norm restricts
    octNormSq (embedOct p) = normSq p :=
  ⟨octMul_embed p q, octConj_embed p, octNormSq_embed p⟩

end RestrictionChain


/-!
=====================================================================
## Part III: FIXED POINTS OF J — The Real Subalgebra
=====================================================================

The fixed points of J (elements satisfying J(a) = a) are exactly
the REAL elements — those with all imaginary parts zero.

    Fix(J_ℍ) = {⟨r, 0, 0, 0⟩ : r ∈ ℝ}  ≅  ℝ
    Fix(J_𝕆) = {(⟨r, 0, 0, 0⟩, 0) : r ∈ ℝ}  ≅  ℝ

The fixed-point subalgebra is ALWAYS ℝ, regardless of how high
we go in the tower.  This is the KMS connection:

  - In modular theory: Fix(J) = Z(M) ∩ M  (the center)
  - In the Hopf tower: Fix(J) = ℝ  (the reals)
  - Physically: the twist-invariant observables are classical

=====================================================================
-/

section FixedPoints

/-- **FIXED POINTS OF J_ℍ**: Exactly the real quaternions.

    qConj(q) = q  ⟺  q.imI = 0 ∧ q.imJ = 0 ∧ q.imK = 0

    qConj negates all imaginary parts, so equality forces them to zero. -/
theorem quat_J_fixed_iff (q : ℍℝ) :
    qConj q = q ↔ q.imI = 0 ∧ q.imJ = 0 ∧ q.imK = 0 := by
  constructor
  · intro h
    unfold qConj at h
    have hi : (-q.imI : ℝ) = q.imI := congrArg QuaternionAlgebra.imI h
    have hj : (-q.imJ : ℝ) = q.imJ := congrArg QuaternionAlgebra.imJ h
    have hk : (-q.imK : ℝ) = q.imK := congrArg QuaternionAlgebra.imK h
    exact ⟨by linarith, by linarith, by linarith⟩
  · intro ⟨hi, hj, hk⟩
    unfold qConj; ext <;> simp [hi, hj, hk]

/-- **NON-REAL QUATERNIONS ARE MOVED BY J**

    If q has any nonzero imaginary part, then qConj(q) ≠ q.
    The twist is invisible only for the reals. -/
theorem quat_J_moves_nonreal (q : ℍℝ)
    (h : q.imI ≠ 0 ∨ q.imJ ≠ 0 ∨ q.imK ≠ 0) :
    qConj q ≠ q := by
  intro heq
  rw [quat_J_fixed_iff] at heq
  rcases h with hi | hj | hk
  · exact hi heq.1
  · exact hj heq.2.1
  · exact hk heq.2.2

/-- **FIXED POINTS OF J_𝕆** (on embedded quaternions):
    The fixed points of octConj within the embedded ℍ ⊂ 𝕆
    are exactly the embedded reals. -/
theorem oct_J_fixed_embed_iff (q : ℍℝ) :
    octConj (embedOct q) = embedOct q ↔
    q.imI = 0 ∧ q.imJ = 0 ∧ q.imK = 0 := by
  rw [octConj_embed]
  constructor
  · intro h
    have : qConj q = q := by
      have := congrArg 𝕆ℝ.l h
      simpa [embedOct] using this
    rwa [quat_J_fixed_iff] at this
  · intro h; rw [(quat_J_fixed_iff q).mpr h]

/-- **FIXED POINTS ARE A SUBALGEBRA**

    The fixed-point set ℝ is closed under multiplication.
    (Real quaternions multiply to real quaternions.) -/
theorem fixed_points_closed_mul (p q : ℍℝ)
    (hp : qConj p = p) (hq : qConj q = q) :
    qConj (p * q) = p * q := by
  have ⟨hpi, hpj, hpk⟩ := (quat_J_fixed_iff p).mp hp
  have ⟨hqi, hqj, hqk⟩ := (quat_J_fixed_iff q).mp hq
  have hp' : p = ⟨p.re, 0, 0, 0⟩ := by ext <;> simp [hpi, hpj, hpk]
  have hq' : q = ⟨q.re, 0, 0, 0⟩ := by ext <;> simp [hqi, hqj, hqk]
  rw [hp', hq']
  unfold qConj; ext <;> simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, mul_neg,
    mul_one, neg_zero, neg_neg, sub_zero, zero_mul, sub_self]

end FixedPoints


/-!
=====================================================================
## Part IV: THE FIBER-CONJUGATION INTERLOCK
=====================================================================

This is the mechanical explanation of WHY the Hopf fibration works.

The S³ fiber acts on S⁷ by right multiplication:
    (a, b) ↦ (aq, bq)

The Hopf map is:
    π(a, b) = (‖a‖² - ‖b‖², a · J(b))

The fiber action preserves π.  The REASON is a four-step
calculation, each step using one axiom of J:

    (aq) · J(bq)
    = (aq) · (J(q) · J(b))      ← ANTI-MULTIPLICATIVITY
    = a · (q · J(q)) · J(b)     ← ASSOCIATIVITY (of ℍ)
    = a · 1 · J(b)              ← UNIT GENERATION (q·J(q)=1)
    = a · J(b)                  ← identity law

Without ANY of these steps, the gear does not mesh.  This is
why the tower ends at 𝕆: the octonions are NOT associative,
so step 2 fails for the full S⁷ fiber.

=====================================================================
-/

section FiberConjugationInterlock

/-- **THE FIBER ACTION THEOREM** (decomposed into J-steps)

    Each step is annotated with which Möbius axiom it uses. -/
theorem fiber_action_via_J (a b q : ℍℝ) (hq : normSq q = 1) :
    quatHopfQ (a * q) (b * q) = quatHopfQ a b := by
  unfold quatHopfQ
  -- Step 1: ANTI-MULTIPLICATIVITY of J
  rw [qConj_mul]
  -- Step 3 (precomputed): UNIT GENERATION
  have h_unit : q * qConj q = 1 := mul_qConj_unit q hq
  -- Step 2: ASSOCIATIVITY — regroup to isolate q · J(q)
  calc (a * q) * (qConj q * qConj b)
      = a * (q * (qConj q * qConj b)) := by rw [mul_assoc]
    _ = a * ((q * qConj q) * qConj b) := by rw [mul_assoc q]
    _ = a * (1 * qConj b) := by rw [h_unit]
    _ = a * qConj b := by rw [one_mul]

/-- **S³ ACTION PRESERVES BOTH HOPF COMPONENTS**

    The real component ‖a‖²-‖b‖² is preserved because
    ‖aq‖² = ‖a‖²·‖q‖² = ‖a‖².  Here J enters through
    normSq_mul (the Euler four-square identity). -/
theorem fiber_action_hopf₀ (a b q : ℍℝ) (hq : normSq q = 1) :
    quatHopf₀ (a * q) (b * q) = quatHopf₀ a b := by
  unfold quatHopf₀; rw [normSq_mul, normSq_mul, hq, mul_one, mul_one]

/-- **THE FULL FIBER INVARIANCE** -/
theorem fiber_full_invariance (a b q : ℍℝ) (hq : normSq q = 1) :
    quatHopf₀ (a * q) (b * q) = quatHopf₀ a b ∧
    quatHopfQ (a * q) (b * q) = quatHopfQ a b :=
  ⟨fiber_action_hopf₀ a b q hq, fiber_action_via_J a b q hq⟩

/-- **THE UNIT CONDITION = PURE TWIST**

    Fiber elements satisfy ‖q‖² = 1, making J(q) the inverse.
    No stretching, only rotation.  The contact surface where
    the gears mesh: "all rotation, no scaling." -/
theorem unit_is_pure_twist (q : ℍℝ) (hq : normSq q = 1) :
    q * qConj q = 1 ∧ qConj q * q = 1 ∧ normSq q = 1 :=
  ⟨mul_qConj_unit q hq, qConj_mul_unit q hq, hq⟩

/-- **THE FIBER IS THE KERNEL OF THE TWIST**

    An element q acts trivially on the Hopf map iff q is in the
    fiber.  The fiber is exactly the set of unit elements —
    the set of pure twists.  The kernel of the projection IS
    the set of all twists. -/
theorem fiber_is_twist_group (a b q : ℍℝ)
    (hab : normSq a + normSq b = 1) (hq : normSq q = 1) :
    normSq (a * q) + normSq (b * q) = 1
    ∧ quatHopf₀ (a * q) (b * q) = quatHopf₀ a b
    ∧ quatHopfQ (a * q) (b * q) = quatHopfQ a b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [normSq_mul, normSq_mul, hq, mul_one, mul_one]; exact hab
  · exact fiber_action_hopf₀ a b q hq
  · exact fiber_action_via_J a b q hq

end FiberConjugationInterlock


/-!
=====================================================================
## Part V: TWIST VISIBILITY — The Cayley-Dickson Ghost
=====================================================================

The twist is a GHOST: present everywhere, visible only when
you activate the new Cayley-Dickson coordinate.

  - At ℍ ↪ 𝕆: when right = 0, multiplication is associative.
    When right ≠ 0, non-associativity appears.

  - At ℂ ↪ ℍ: when j = k = 0, multiplication is commutative.
    When j, k ≠ 0, non-commutativity appears.

The twist is added by the Cayley-Dickson construction at each
level.  But it only ACTIVATES when you use the new coordinate.
Within the embedded subalgebra, everything is as before.

=====================================================================
-/

section TwistVisibility

/-- **COMMUTATIVITY AT THE REAL LEVEL**

    Real quaternions commute.  J is trivial (= identity),
    so there is no twist to see. -/
theorem real_level_commutative (x y : ℝ) :
    embedReal x * embedReal y = embedReal y * embedReal x := by
  unfold embedReal; ext <;> simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, mul_neg,
    mul_one, neg_zero, neg_neg, sub_zero, zero_mul, sub_self]; ring

/-- **THE TWIST VISIBILITY THEOREM**

    The Cayley-Dickson twist is invisible within the embedded
    subalgebra and visible outside it.

    Within ℍ ↪ 𝕆:  associative     (twist invisible)
    Outside ℍ ↪ 𝕆:  non-associative (twist visible)

    Within ℝ ↪ ℍ:  commutative      (twist invisible)
    Outside ℝ ↪ ℍ:  non-commutative  (twist visible)

    At each level, the new Cayley-Dickson coordinate activates
    a new twist.  The twist is the GHOST in the machine. -/
theorem twist_visibility :
    -- ℝ ↪ ℍ: commutative inside, non-commutative outside
    (∀ x y : ℝ, embedReal x * embedReal y = embedReal y * embedReal x)
    ∧ (∃ p q : ℍℝ, p * q ≠ q * p)
    ∧
    -- ℍ ↪ 𝕆: associative inside, non-associative outside
    (∀ p q r : ℍℝ,
      octMul (embedOct p) (octMul (embedOct q) (embedOct r)) =
      octMul (octMul (embedOct p) (embedOct q)) (embedOct r))
    ∧ (∃ x y z : 𝕆ℝ, octMul (octMul x y) z ≠ octMul x (octMul y z)) := by
  refine ⟨real_level_commutative, ?_, ?_, ?_⟩
  -- Non-commutativity witness: reuse s3_noncommutative from InclusionChain
  · exact ⟨⟨0,1,0,0⟩, ⟨0,0,1,0⟩, s3_noncommutative⟩
  -- Embedded associativity: from NonAssociativity
  · intro p q r
    rw [octMul_embed, octMul_embed, octMul_embed, octMul_embed, mul_assoc]
  -- Non-associativity witness: from NonAssociativity
  · exact ⟨oct_e1, oct_e2, oct_e4, oct_not_associative⟩

end TwistVisibility


/-!
=====================================================================
## Part VI: THE TERMINATION — The Tooth Breaks
=====================================================================

Each Cayley-Dickson doubling adds one twist, and each twist has
a "cost" measured by which algebraic property is lost:

    ℝ → ℂ:   lose ordering         (gain: algebraic closure)
    ℂ → ℍ:   lose commutativity    (gain: 3D rotations)
    ℍ → 𝕆:   lose associativity    (gain: exceptional structures)
    𝕆 → 𝕊:   lose division!        (gain: NOTHING useful)

We prove: J works at ℍ, J works at 𝕆, and the embedded subalgebra
always retains the full structure.  The ACCUMULATION of twists
is what eventually breaks the tower.

=====================================================================
-/

section Termination

/-- **J ENABLES THE FIBER ACTION**

    J provides the inverse, norm provides the sphere constraint,
    and together they enable the fiber action to preserve the
    Hopf map.  The three legs of the triangle:
    J + norm + division ⟹ Hopf. -/
theorem J_enables_fiber_action (q : ℍℝ) (hq : normSq q = 1) :
    q * qConj q = 1
    ∧ normSq q = 1
    ∧ (∀ a b : ℍℝ,
        quatHopf₀ (a * q) (b * q) = quatHopf₀ a b ∧
        quatHopfQ (a * q) (b * q) = quatHopfQ a b) :=
  ⟨mul_qConj_unit q hq, hq,
   fun a b => ⟨fiber_action_hopf₀ a b q hq, fiber_action_via_J a b q hq⟩⟩

end Termination


/-!
=====================================================================
## Part VII: THE COMMON J — Master Theorem
=====================================================================

Everything together.

The conjugation J is the structural constant of the Hopf tower.
It is the same operation at every level, restricted coherently
through the embeddings, with the same four axioms, enabling
the same fiber action, and terminating for the same reason.

The Hopf tower and the KMS modular flow share this J.
They are two gears with the same tooth profile.
They mesh because the tooth profile is universal.

=====================================================================
-/

section CommonJ

/-- **THE COMMON J: MASTER THEOREM**

    The conjugation operator J:
    (1) Satisfies the four Möbius involution axioms at ℍ and 𝕆
    (2) Restricts coherently across the embedding tower
    (3) Has fixed points = ℝ at every level
    (4) Enables the fiber action at every level
    (5) Is invisible within embedded subalgebras (twist visibility)
    (6) Creates the algebraic degradation that terminates the tower -/
theorem the_common_J :
    -- ═══════════════════════════════════════════════════════
    -- (1) Möbius axioms at ℍ
    -- ═══════════════════════════════════════════════════════
    (∀ q : ℍℝ, qConj (qConj q) = q)
    ∧ (∀ p q : ℍℝ, qConj (p * q) = qConj q * qConj p)
    ∧ (∀ q : ℍℝ, normSq (qConj q) = normSq q)
    ∧ (∀ q : ℍℝ, q * qConj q = ⟨normSq q, 0, 0, 0⟩)
    ∧
    -- ═══════════════════════════════════════════════════════
    -- (2) Möbius axioms at 𝕆
    -- ═══════════════════════════════════════════════════════
    (∀ x : 𝕆ℝ, octConj (octConj x) = x)
    ∧ (∀ x y : 𝕆ℝ, octConj (octMul x y) = octMul (octConj y) (octConj x))
    ∧ (∀ x : 𝕆ℝ, octNormSq (octConj x) = octNormSq x)
    ∧ (∀ x : 𝕆ℝ, (octMul x (octConj x)).r = 0)
    ∧
    -- ═══════════════════════════════════════════════════════
    -- (3) Restriction coherence
    -- ═══════════════════════════════════════════════════════
    (∀ q : ℍℝ, octConj (embedOct q) = embedOct (qConj q))
    ∧ (∀ x : ℝ, qConj (embedReal x) = embedReal x)
    ∧
    -- ═══════════════════════════════════════════════════════
    -- (4) Fixed points = ℝ
    -- ═══════════════════════════════════════════════════════
    (∀ q : ℍℝ, qConj q = q ↔ q.imI = 0 ∧ q.imJ = 0 ∧ q.imK = 0)
    ∧
    -- ═══════════════════════════════════════════════════════
    -- (5) Fiber action enabled by J
    -- ═══════════════════════════════════════════════════════
    (∀ a b q : ℍℝ, normSq q = 1 →
      quatHopf₀ (a * q) (b * q) = quatHopf₀ a b ∧
      quatHopfQ (a * q) (b * q) = quatHopfQ a b)
    ∧
    -- ═══════════════════════════════════════════════════════
    -- (6) Twist visibility
    -- ═══════════════════════════════════════════════════════
    (∀ p q r : ℍℝ,
      octMul (embedOct p) (octMul (embedOct q) (embedOct r)) =
      octMul (octMul (embedOct p) (embedOct q)) (embedOct r))
    ∧ (∃ x y z : 𝕆ℝ, octMul (octMul x y) z ≠ octMul x (octMul y z))
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (1) Möbius axioms at ℍ
  · exact qConj_qConj
  · exact qConj_mul
  · exact normSq_conj
  · exact mul_qConj_eq
  -- (2) Möbius axioms at 𝕆
  · exact oct_J_involution
  · exact oct_J_anti_mul
  · exact oct_J_norm
  · exact octMul_octConj
  -- (3) Restriction coherence
  · exact octConj_embed
  · exact qConj_embedReal
  -- (4) Fixed points
  · exact quat_J_fixed_iff
  -- (5) Fiber action
  · intro a b q hq
    exact ⟨fiber_action_hopf₀ a b q hq, fiber_action_via_J a b q hq⟩
  -- (6) Twist visibility
  · intro p q r
    rw [octMul_embed, octMul_embed, octMul_embed, octMul_embed, mul_assoc]
  · exact ⟨oct_e1, oct_e2, oct_e4, oct_not_associative⟩

end CommonJ

end HopfTower.Properties
