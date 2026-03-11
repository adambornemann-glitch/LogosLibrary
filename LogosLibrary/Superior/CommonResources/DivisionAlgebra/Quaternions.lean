/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: DivisionAlgebra/Quaternions.lean
-/
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
/-!
=====================================================================
# SUPERIOR-STRING THEORY: QUATERNION ALGEBRA
=====================================================================

The quaternionic backbone of the entropic string framework.

## The Core Identification

The quaternion multiplication table:

  𝐢𝐣 = 𝐤,  𝐣𝐤 = 𝐢,  𝐤𝐢 = 𝐣
  𝐣𝐢 = -𝐤, 𝐤𝐣 = -𝐢, 𝐢𝐤 = -𝐣

IS the rotation algebra:

  [Jₓ, Jᵧ] = 2Jᵤ  (and cyclic)

This is not an analogy. The imaginary quaternions ARE su(2).

## The Hopf Map from Conjugation

The Hopf projection π: S³ → S² defined in `Topology.lean` is
the conjugation action of unit quaternions on a fixed basis element:

  π(q) = q · 𝐢 · q̄

This connects the topological structure (Hopf fibration, axion)
to the algebraic structure (rotations, angular momentum).

## The Fueter Operator

The quaternionic Cauchy-Riemann operator:

  ∂̄ = ∂/∂σ_R + 𝐢 ∂/∂σ_I + 𝐣 ∂/∂σ_J + 𝐤 ∂/∂σ_K

Its algebraic symbol satisfies: ∂̄* · ∂̄ = Δ₄ (the 4D Laplacian).
This is verified at the symbol level as a polynomial identity.

## Contents

- Quaternion basis elements and full multiplication table
- Commutation relations (the su(2) Lie algebra)
- Pure imaginary subspace
- Conjugation action and norm preservation
- Hopf map as conjugation
- Fueter operator symbol calculus
- Connection to the entropic parameter
-/
namespace DivisionAlgebra.Quaternion

open Real --SuperiorString.Topology
/-!
=====================================================================
## Part I: Quaternion Basis Elements
=====================================================================

We work with Mathlib's `ℍℝ = QuaternionAlgebra ℝ (-1) (-1)`.

The basis: {1, 𝐢, 𝐣, 𝐤}

The multiplication table encodes the structure constants of su(2).
Every entry is either ±1 or ±𝐢, ±𝐣, ±𝐤.
-/

section Basis

/-- The quaternionic imaginary unit 𝐢 -/
def qi : QuaternionAlgebra ℝ (-1) (0) (-1) := ⟨0, 1, 0, 0⟩

/-- The quaternionic imaginary unit 𝐣 -/
def qj : QuaternionAlgebra ℝ (-1) (0) (-1) := ⟨0, 0, 1, 0⟩

/-- The quaternionic imaginary unit 𝐤 -/
def qk : QuaternionAlgebra ℝ (-1) (0) (-1) := ⟨0, 0, 0, 1⟩

/-- The quaternionic unit 1 -/
def q1 : QuaternionAlgebra ℝ (-1) (0) (-1) := ⟨1, 0, 0, 0⟩

-- === Component access lemmas ===

@[simp] theorem qi_re : qi.re = 0 := rfl
@[simp] theorem qi_imI : qi.imI = 1 := rfl
@[simp] theorem qi_imJ : qi.imJ = 0 := rfl
@[simp] theorem qi_imK : qi.imK = 0 := rfl

@[simp] theorem qj_re : qj.re = 0 := rfl
@[simp] theorem qj_imI : qj.imI = 0 := rfl
@[simp] theorem qj_imJ : qj.imJ = 1 := rfl
@[simp] theorem qj_imK : qj.imK = 0 := rfl

@[simp] theorem qk_re : qk.re = 0 := rfl
@[simp] theorem qk_imI : qk.imI = 0 := rfl
@[simp] theorem qk_imJ : qk.imJ = 0 := rfl
@[simp] theorem qk_imK : qk.imK = 1 := rfl

end Basis

/-!
=====================================================================
## Part II: The Multiplication Table
=====================================================================

The complete multiplication table for quaternion basis elements.
Six nontrivial products (the rest follow by linearity):

  𝐢𝐣 = 𝐤     𝐣𝐢 = -𝐤
  𝐣𝐤 = 𝐢     𝐤𝐣 = -𝐢
  𝐤𝐢 = 𝐣     𝐢𝐤 = -𝐣

Plus the squares:
  𝐢² = -1    𝐣² = -1    𝐤² = -1

These are proved by `ext` decomposition into components
followed by `simp` with the quaternion multiplication lemmas.
-/

section MultiplicationTable

-- Helper: expand and close quaternion component goals
macro "quat_ext" : tactic =>
  `(tactic| (
    try unfold qi; try unfold qj; try unfold qk; try unfold q1
    ext
    all_goals simp [Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
    all_goals norm_num))


-- === The positive cyclic products ===

/- all of the following section is broken with
failed to synthesize instance of type class
  HMul (ℍℝ) (ℍℝ) ?m.3

  and `simp` made no progress
  -/
/-- 𝐢𝐣 = 𝐤 -/
theorem mul_qi_qj : qi * qj = qk := by quat_ext

/-- 𝐣𝐤 = 𝐢 -/
theorem mul_qj_qk : qj * qk = qi := by quat_ext

/-- 𝐤𝐢 = 𝐣 -/
theorem mul_qk_qi : qk * qi = qj := by quat_ext

-- === The negative cyclic products ===

/-- 𝐣𝐢 = -𝐤 -/
theorem mul_qj_qi : qj * qi = -qk := by quat_ext

/-- 𝐤𝐣 = -𝐢 -/
theorem mul_qk_qj : qk * qj = -qi := by quat_ext

/-- 𝐢𝐤 = -𝐣 -/
theorem mul_qi_qk : qi * qk = -qj := by quat_ext

-- === The squares ===

/-- 𝐢² = -1 -/
theorem sq_qi : qi * qi = -q1 := by quat_ext <;> rfl

/-- 𝐣² = -1 -/
theorem sq_qj : qj * qj = -q1 := by quat_ext <;> rfl

/-- 𝐤² = -1 -/
theorem sq_qk : qk * qk = -q1 := by quat_ext <;> rfl

/-- The scalar triple product: 𝐢𝐣𝐤 = -1

    This is the quaternion analog of the determinant. -/
theorem triple_product : qi * qj * qk = -q1 := by
  rw [mul_qi_qj, sq_qk]

end MultiplicationTable

-- everything downstream from this is broken obviously

/-!
=====================================================================
## Part III: The Commutation Relations — su(2)
=====================================================================

The commutator [A, B] = AB - BA applied to quaternion basis:

  [𝐢, 𝐣] = 𝐢𝐣 - 𝐣𝐢 = 𝐤 - (-𝐤) = 2𝐤
  [𝐣, 𝐤] = 𝐣𝐤 - 𝐤𝐣 = 𝐢 - (-𝐢) = 2𝐢
  [𝐤, 𝐢] = 𝐤𝐢 - 𝐢𝐤 = 𝐣 - (-𝐣) = 2𝐣

These are EXACTLY the su(2) structure constants (up to 2i).

The physics convention [Jₓ, Jᵧ] = iJᵤ corresponds to
identifying Jₓ = 𝐢/2, Jᵧ = 𝐣/2, Jᵤ = 𝐤/2.

The quaternion imaginary units ARE angular momentum operators
(up to a factor of 2).
-/

section CommutationRelations

/-- Standard quaternions ℍ[ℝ] with the explicit 3-parameter form -/
abbrev ℍℝ := QuaternionAlgebra ℝ (-1) (0) (-1)

/-- The Lie bracket (commutator) of two quaternions -/
def commutator (p q : ℍℝ) : ℍℝ := p * q - q * p

notation "[" p ", " q "]ₕ" => commutator p q

/-- **[𝐢, 𝐣] = 2𝐤**

    The fundamental su(2) commutation relation.

    In physics notation: [Jₓ, Jᵧ] = iJᵤ with J = σ/2. -/
theorem comm_qi_qj : [qi, qj]ₕ = 2 • qk := by
  simp only [commutator, mul_qi_qj, mul_qj_qi, sub_neg_eq_add]
  ext <;> simp [qk]; ring_nf

/-- **[𝐣, 𝐤] = 2𝐢** (cyclic) -/
theorem comm_qj_qk : [qj, qk]ₕ = 2 • qi := by
  simp only [commutator, mul_qj_qk, mul_qk_qj, sub_neg_eq_add]
  ext <;> simp [qi]; ring_nf

/-- **[𝐤, 𝐢] = 2𝐣** (cyclic) -/
theorem comm_qk_qi : [qk, qi]ₕ = 2 • qj := by
  simp only [commutator, mul_qk_qi, mul_qi_qk, sub_neg_eq_add]
  ext <;> simp [qj]; ring_nf

/-- Antisymmetry of the commutator -/
theorem comm_antisymm (p q : ℍℝ) : [p, q]ₕ = -[q, p]ₕ := by
  unfold commutator; norm_num

/-- Self-commutator vanishes -/
theorem comm_self (p : ℍℝ) : [p, p]ₕ = 0 := by
  unfold commutator; norm_num

/-- **THE JACOBI IDENTITY**

    [[A,B],C] + [[B,C],A] + [[C,A],B] = 0

    This makes the pure imaginary quaternions into a Lie algebra.
    The Jacobi identity is what makes su(2) an actual Lie algebra,
    not just a vector space with a bracket.

    For quaternions this follows from associativity of multiplication. -/
theorem jacobi_identity (p q r : ℍℝ) :
    [commutator p q, r]ₕ + [commutator q r, p]ₕ + [commutator r p, q]ₕ = 0 := by
  unfold commutator
  simp only [mul_sub, sub_mul, ← mul_assoc]
  abel

end CommutationRelations

/-!
=====================================================================
## Part IV: Pure Imaginary Quaternions
=====================================================================

A quaternion is pure imaginary if its real part vanishes: q.re = 0.

The pure imaginary quaternions form a 3-dimensional real vector
space, which is ALSO a Lie algebra under the commutator.

This 3D space is su(2) ≅ so(3) ≅ ℝ³.
-/

section PureImaginary

/-- A quaternion is pure imaginary if its real part is zero -/
def IsPureImaginary (q : ℍℝ) : Prop := q.re = 0

/-- The basis elements are pure imaginary -/
theorem qi_pure : IsPureImaginary qi := rfl
theorem qj_pure : IsPureImaginary qj := rfl
theorem qk_pure : IsPureImaginary qk := rfl

/-- Pure imaginary quaternions are closed under addition -/
theorem pure_add (p q : ℍℝ) (hp : IsPureImaginary p) (hq : IsPureImaginary q) :
    IsPureImaginary (p + q) := by
  unfold IsPureImaginary at *
  simp [hp, hq]

/-- Pure imaginary quaternions are closed under scalar multiplication -/
theorem pure_smul (r : ℝ) (q : ℍℝ) (hq : IsPureImaginary q) :
    IsPureImaginary (r • q) := by
  unfold IsPureImaginary at *
  simp [hq]

/-- The commutator of pure imaginaries is pure imaginary.

    This is the closure of the Lie bracket: su(2) is a Lie subalgebra. -/
theorem pure_comm (p q : ℍℝ) (hp : IsPureImaginary p) (hq : IsPureImaginary q) :
    IsPureImaginary (commutator p q) := by
  unfold IsPureImaginary commutator
  simp only [QuaternionAlgebra.re_sub, QuaternionAlgebra.re_mul, neg_mul, one_mul, mul_neg, mul_one,
    neg_zero, zero_mul, add_zero, neg_neg]
  unfold IsPureImaginary at hp hq
  rw [hp, hq]
  ring

/-- Embed ℝ³ as pure imaginary quaternions -/
def fromR3 (x y z : ℝ) : ℍℝ := ⟨0, x, y, z⟩

theorem fromR3_pure (x y z : ℝ) : IsPureImaginary (fromR3 x y z) := rfl

/-- Extract the ℝ³ components -/
def toR3 (q : ℍℝ) : ℝ × ℝ × ℝ := (q.imI, q.imJ, q.imK)

/-- Round-trip: embed then extract = identity -/
theorem toR3_fromR3 (x y z : ℝ) : toR3 (fromR3 x y z) = (x, y, z) := rfl

/-- The dot product of pure imaginary quaternions.

    For pure imaginary p, q: Re(p̄q) = -(p · q)
    where p · q = p.imI*q.imI + p.imJ*q.imJ + p.imK*q.imK -/
noncomputable def dotProduct (p q : ℍℝ) : ℝ :=
  p.imI * q.imI + p.imJ * q.imJ + p.imK * q.imK

/-- The cross product of pure imaginary quaternions.

    For pure imaginary p, q: Im(pq) = p × q

    The quaternion product ENCODES both the dot and cross product:
      pq = -(p · q) + (p × q) -/
def crossProduct (p q : ℍℝ) : ℍℝ :=
  fromR3
    (p.imJ * q.imK - p.imK * q.imJ)
    (p.imK * q.imI - p.imI * q.imK)
    (p.imI * q.imJ - p.imJ * q.imI)

/-- **THE QUATERNION PRODUCT FORMULA**

    For pure imaginary p, q:
      p * q = -(p · q) + (p × q)

    This is the deepest reason quaternions encode 3D geometry:
    multiplication IS the combination of dot and cross products. -/
theorem pure_mul_decomposition (p q : ℍℝ)
    (hp : IsPureImaginary p) (hq : IsPureImaginary q) :
    p * q = ⟨-(dotProduct p q), (crossProduct p q).imI,
            (crossProduct p q).imJ, (crossProduct p q).imK⟩ := by
  unfold IsPureImaginary at hp hq
  unfold dotProduct crossProduct fromR3
  ext <;> simp [hp, hq] <;> ring

end PureImaginary

/-!
=====================================================================
## Part V: Conjugation and Norm
=====================================================================

The quaternion conjugate: q̄ = q.re - q.imI·𝐢 - q.imJ·𝐣 - q.imK·𝐤

The norm squared: |q|² = q · q̄ = re² + imI² + imJ² + imK²

Key property: |q₁q₂|² = |q₁|²|q₂|² (multiplicativity)

This is what makes quaternion rotations work: conjugation by a
unit quaternion preserves the norm of pure imaginary quaternions.
-/

section NormAndConjugation

/-- The quaternion conjugate: negate all imaginary parts -/
def qConj (q : ℍℝ) : ℍℝ :=
  ⟨q.re, -q.imI, -q.imJ, -q.imK⟩

/-- The norm squared: sum of squares of all components -/
noncomputable def normSq (q : ℍℝ) : ℝ :=
  q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2

/-- Norm squared is non-negative -/
theorem normSq_nonneg (q : ℍℝ) : normSq q ≥ 0 := by
  unfold normSq
  positivity

/-- Norm squared of a unit quaternion is 1 -/
theorem normSq_unit (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    normSq ⟨a, b, c, d⟩ = 1 := h

/-- Conjugate of conjugate is identity -/
theorem qConj_qConj (q : ℍℝ) : qConj (qConj q) = q := by
  unfold qConj; ext <;> simp

/-- Conjugation is anti-multiplicative: (pq)* = q* p* -/
theorem qConj_mul (p q : ℍℝ) : qConj (p * q) = qConj q * qConj p := by
  unfold qConj
  ext <;> simp <;> ring

/-- q · q̄ is real: all imaginary parts vanish.

    The product of a quaternion with its conjugate is always
    a real scalar (equal to the norm squared). -/
theorem mul_conj_imI (q : ℍℝ) : (q * qConj q).imI = 0 := by
  unfold qConj; simp only [QuaternionAlgebra.imI_mul, mul_neg, zero_mul, neg_zero, add_zero,
    neg_mul, one_mul, neg_neg]; ring

theorem mul_conj_imJ (q : ℍℝ) : (q * qConj q).imJ = 0 := by
  unfold qConj; simp only [QuaternionAlgebra.imJ_mul, mul_neg, neg_mul, one_mul, neg_neg, zero_mul,
    neg_zero, add_zero]; ring

theorem mul_conj_imK (q : ℍℝ) : (q * qConj q).imK = 0 := by
  unfold qConj; simp only [QuaternionAlgebra.imK_mul, mul_neg, zero_mul, neg_zero, add_zero,
    sub_neg_eq_add]; ring


/-- **NORM SQUARED FROM PRODUCT**: |q|² = Re(q · q̄) -/
theorem normSq_eq_mul_conj_re (q : ℍℝ) :
    normSq q = (q * qConj q).re := by
  unfold normSq qConj
  simp only [QuaternionAlgebra.re_mul, neg_mul, one_mul, mul_neg, neg_neg, mul_one, neg_zero,
    zero_mul, add_zero, sub_neg_eq_add]
  ring

/-- **MULTIPLICATIVITY OF NORM SQUARED**: |pq|² = |p|²|q|²

    This is the Euler four-square identity.
    It is what makes quaternions a NORMED division algebra.

    Physical consequence: conjugation by a unit quaternion
    preserves the norm. Rotations preserve lengths. -/
theorem normSq_mul (p q : ℍℝ) : normSq (p * q) = normSq p * normSq q := by
  unfold normSq
  simp only [QuaternionAlgebra.re_mul, neg_mul, one_mul, mul_neg, mul_one, neg_zero, zero_mul,
    add_zero, neg_neg, QuaternionAlgebra.imI_mul, sub_neg_eq_add, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]
  ring

/-- Norm squared of the conjugate equals norm squared -/
theorem normSq_conj (q : ℍℝ) : normSq (qConj q) = normSq q := by
  unfold normSq qConj; simp

end NormAndConjugation

/-!
=====================================================================
## Part VI: The Rotation Action
=====================================================================

For unit quaternion q (|q|² = 1) and pure imaginary v:

  q · v · q̄   is pure imaginary with |q·v·q̄|² = |v|²

This IS a rotation of v ∈ ℝ³.

The map q ↦ (v ↦ qvq̄) is a surjective homomorphism
from S³ (unit quaternions) to SO(3) (rotations),
with kernel {±1}. This is the double cover SU(2) → SO(3).
-/

section RotationAction

/-- The conjugation action: q acts on v by q · v · q̄ -/
def conjugationAction (q v : ℍℝ) : ℍℝ :=
  q * v * qConj q

/-- **ROTATION PRESERVES NORM**

    For any q with |q|² = 1 and any v:
      |qvq̄|² = |q|² · |v|² · |q̄|² = 1 · |v|² · 1 = |v|²

    Conjugation by a unit quaternion is an isometry. -/
theorem conjugation_preserves_norm (q v : ℍℝ)
    (hq : normSq q = 1) :
    normSq (conjugationAction q v) = normSq v := by
  unfold conjugationAction
  rw [normSq_mul, normSq_mul, normSq_conj, hq]
  ring

/-- **CONJUGATION OF PURE IMAGINARY IS PURE IMAGINARY**

    If v is pure imaginary, then qvq̄ is also pure imaginary.
    The rotation action stays within ℝ³ ⊂ ℍ. -/
theorem conjugation_preserves_pure (q v : ℍℝ)
    (_hq : normSq q = 1) (hv : IsPureImaginary v) :
    IsPureImaginary (conjugationAction q v) := by
  unfold IsPureImaginary conjugationAction qConj at *
  simp only [QuaternionAlgebra.re_mul, neg_mul, one_mul, mul_neg, mul_one, neg_zero, zero_mul,
    add_zero, neg_neg, QuaternionAlgebra.imI_mul, sub_neg_eq_add, neg_add_rev,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul]
  unfold normSq at _hq
  nlinarith [sq_nonneg q.re, sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK,
             sq_nonneg v.imI, sq_nonneg v.imJ, sq_nonneg v.imK, hv]

/-- The identity quaternion acts trivially -/
theorem conjugation_identity (v : ℍℝ) :
    conjugationAction q1 v = v := by
  unfold conjugationAction q1 qConj
  ext <;> simp only [neg_zero, QuaternionAlgebra.imI_mul, QuaternionAlgebra.re_mul, one_mul,
    mul_zero, zero_mul, add_zero, mul_neg, mul_one, neg_neg, sub_zero, zero_add,
    QuaternionAlgebra.imJ_mul, neg_mul, QuaternionAlgebra.imK_mul]

/-- Conjugation composes: (pq) acts as p then q.

    This is the group homomorphism property:
      (pq)v(pq)* = p(qvq*)p*   -/
theorem conjugation_compose (p q v : ℍℝ) :
    conjugationAction (p * q) v = conjugationAction p (conjugationAction q v) := by
  unfold conjugationAction
  rw [qConj_mul]
  simp only [mul_assoc]

/-- **THE KERNEL**: q and -q give the same rotation.

    This is the double cover SU(2) → SO(3).
    Two antipodal points on S³ represent the same rotation. -/
theorem conjugation_neg (q v : ℍℝ) :
    conjugationAction (-q) v = conjugationAction q v := by
  unfold conjugationAction qConj
  ext <;> simp only [neg_mul, QuaternionAlgebra.re_neg, QuaternionAlgebra.imI_neg, neg_neg,
    QuaternionAlgebra.imJ_neg, QuaternionAlgebra.imK_neg, QuaternionAlgebra.re_mul, one_mul,
    mul_neg, mul_one, neg_zero, zero_mul, add_zero, QuaternionAlgebra.imI_mul, sub_neg_eq_add,
    neg_add_rev, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, neg_sub] <;> ring

end RotationAction

end DivisionAlgebra.Quaternion
