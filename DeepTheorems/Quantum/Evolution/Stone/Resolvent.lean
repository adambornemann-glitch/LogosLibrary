/-
================================================================================
STONE'S THEOREM: CORE STRUCTURES AND DEFINITIONS
================================================================================

This file establishes the mathematical foundations for Stone's theorem using
the unbounded operator machinery proven to work in Robertson's theorem.

Key theorem: Bijective correspondence between strongly continuous one-parameter
unitary groups U(t) and self-adjoint operators A via U(t) = exp(itA).

Strategy: Use the domain-tracking approach from Robertson that successfully
handles unbounded operators with Submodule domains.

References:
  - Reed & Simon, "Methods of Modern Mathematical Physics" Vol. 1, Ch. VIII
  - Hall, B.C. "Quantum Theory for Mathematicians" Ch. 9-10
  - Our own Robertson.Core for the unbounded operator pattern
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

-- Import Robertson's proven unbounded operator machinery
import LogosLibrary.DeepTheorems.Quantum.Uncertainty.Robertson.Core

namespace StoneTheorem

open InnerProductSpace MeasureTheory Complex Filter Topology
open scoped BigOperators Topology
set_option linter.unusedSectionVars false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
================================================================================
SECTION 1: ONE-PARAMETER UNITARY GROUPS
================================================================================

A strongly continuous one-parameter unitary group is a family {U(t)}_{t∈ℝ}
satisfying:
  1. U(0) = I
  2. U(s+t) = U(s)U(t)
  3. U(t)* = U(-t)
  4. t ↦ U(t)ψ is continuous for each ψ

This is the "dynamics" side of Stone's theorem.
-/

/--
Strongly continuous one-parameter unitary group.

Physical interpretation: Time evolution in quantum mechanics
Mathematical content: The "U(t) = exp(itH)" side of Stone's theorem

NOTE: We do NOT require differentiability - only strong continuity.
Stone's theorem will prove the generator exists from this alone!
-/
structure OneParameterUnitaryGroup where
  /-- The family of operators U(t) for each t ∈ ℝ -/
  U : ℝ → (H →L[ℂ] H)

  /-- U(t) preserves inner products (unitarity) -/
  unitary : ∀ (t : ℝ) (ψ φ : H), ⟪U t ψ, U t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ

  /-- Group property: U(s+t) = U(s)U(t) -/
  group_law : ∀ s t : ℝ, U (s + t) = (U s).comp (U t)

  /-- Identity: U(0) = I -/
  identity : U 0 = ContinuousLinearMap.id ℂ H

  /-- Strong continuity: t ↦ U(t)ψ is continuous for each ψ -/
  strong_continuous : ∀ ψ : H, Continuous (fun t : ℝ => U t ψ)

/-!
### Derived Properties of One-Parameter Groups
-/

namespace OneParameterUnitaryGroup

/--
U(-t) = U(t)* (inverse equals adjoint for unitary operators).

**Mathematical Content:**
For any strongly continuous one-parameter unitary group, the operator at time -t
is exactly the adjoint (Hermitian conjugate) of the operator at time t:
  U(-t) = U(t)*

**Proof Strategy:**
1. Use the group law: U(t)U(-t) = U(t + (-t)) = U(0) = I
   This shows U(-t) is the inverse of U(t)
2. Use unitarity: ⟨U(t)ψ, U(t)φ⟩ = ⟨ψ, φ⟩
3. Combine these to show: ⟨U(-t)ψ, φ⟩ = ⟨ψ, U(t)φ⟩
   which is the defining property of the adjoint

The key calculation:
  ⟨U(-t)ψ, φ⟩ = ⟨U(t)(U(-t)ψ), U(t)φ⟩  [by unitarity]
               = ⟨ψ, U(t)φ⟩              [since U(t)U(-t) = I]

**Why This Matters:**
- Shows unitary operators are normal: U(t)U(t)* = U(t)*U(t)
- Essential for proving generators are symmetric: if Aψ = lim (U(t)ψ - ψ)/(it),
  then ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩
- Confirms physical reversibility: time evolution backward is the adjoint of
  time evolution forward

**Physical Interpretation:**
In quantum mechanics, U(t) evolves states forward in time. Its adjoint U(t)*
evolves states backward in time. This theorem proves these are related by
time reversal: U(-t) = U(t)*, showing the fundamental reversibility of
unitary quantum dynamics.

**Relation to Other Properties:**
Combined with the group law, this gives:
- U(t)* = U(-t) = [U(t)]⁻¹, so unitary operators are self-adjoint in the
  inverse sense
- U(t)*U(t) = U(-t)U(t) = U(0) = I, confirming U(t) is an isometry
-/
theorem inverse_eq_adjoint (U_grp : OneParameterUnitaryGroup (H := H)) (t : ℝ) :
    U_grp.U (-t) = (U_grp.U t).adjoint := by
  ext ψ
  apply ext_inner_right ℂ
  intro φ

  -- Want: ⟨U(-t)ψ, φ⟩ = ⟨ψ, U(t)φ⟩
  -- Use: U(t)U(-t) = I, so U(t)(U(-t)ψ) = ψ
  -- And unitarity

  have h_inv : U_grp.U t (U_grp.U (-t) ψ) = ψ := by
    have h1 : t + (-t) = 0 := by ring
    have h2 : U_grp.U (t + (-t)) = (U_grp.U t).comp (U_grp.U (-t)) :=
      U_grp.group_law t (-t)
    rw [h1] at h2
    have h3 : (U_grp.U t).comp (U_grp.U (-t)) = U_grp.U 0 := h2.symm
    have h4 : U_grp.U 0 = ContinuousLinearMap.id ℂ H := U_grp.identity
    rw [h4] at h3
    have : (U_grp.U t) ((U_grp.U (-t)) ψ) = ((U_grp.U t).comp (U_grp.U (-t))) ψ := rfl
    rw [this, h3]
    rfl

  calc ⟪U_grp.U (-t) ψ, φ⟫_ℂ
      = ⟪U_grp.U t (U_grp.U (-t) ψ), U_grp.U t φ⟫_ℂ := by
          rw [← U_grp.unitary t (U_grp.U (-t) ψ) φ]
      _ = ⟪ψ, U_grp.U t φ⟫_ℂ := by rw [h_inv]
      _ = ⟪(U_grp.U t).adjoint ψ, φ⟫_ℂ := by
          -- This is the definition of adjoint!
          rw [ContinuousLinearMap.adjoint_inner_left]



/--
U(t) is norm-preserving (isometry).

**Mathematical Content:**
For any t ∈ ℝ and ψ ∈ H, the unitary operator U(t) preserves norms:
  ‖U(t)ψ‖ = ‖ψ‖

This is the defining property of an isometry.

**Proof Strategy:**
Direct consequence of unitarity:
1. Unitarity gives: ⟨U(t)ψ, U(t)ψ⟩ = ⟨ψ, ψ⟩
2. The norm is defined by: ‖x‖² = Re⟨x, x⟩
3. Therefore: ‖U(t)ψ‖² = ‖ψ‖²
4. Take square roots (both sides non-negative)

**Why This Matters:**
- Confirms U(t) is an isometry (distance-preserving)
- Combined with surjectivity, proves U(t) is unitary
- Essential for showing ‖U(t)‖ = 1 as an operator
- Guarantees no "loss of information" under time evolution

**Physical Interpretation:**
In quantum mechanics, this is the normalization preservation principle:
if ψ is a normalized state (‖ψ‖ = 1), then U(t)ψ remains normalized
for all times t. This ensures probability is conserved during quantum
evolution - the total probability remains 1 under unitary dynamics.

**Relation to Other Properties:**
- Implies U(t) is injective (if U(t)ψ = 0, then ‖ψ‖ = 0, so ψ = 0)
- Combined with the group law, proves U(t) is surjective (U(-t) is inverse)
- Together these show U(t) is a unitary operator in the operator-theoretic sense
-/
theorem norm_preserving (U_grp : OneParameterUnitaryGroup (H := H)) (t : ℝ) (ψ : H) :
    ‖U_grp.U t ψ‖ = ‖ψ‖ := by
  have h := U_grp.unitary t ψ ψ
  -- h : ⟪U_grp.U t ψ, U_grp.U t ψ⟫_ℂ = ⟪ψ, ψ⟫_ℂ

  -- Norm is defined by: ‖x‖² = ⟨x, x⟩
  have h1 : (⟪U_grp.U t ψ, U_grp.U t ψ⟫_ℂ).re = ‖U_grp.U t ψ‖ ^ 2 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (U_grp.U t ψ)
    calc (⟪U_grp.U t ψ, U_grp.U t ψ⟫_ℂ).re
        = ((‖U_grp.U t ψ‖ ^ 2 : ℂ)).re := by
            have h_re := congr_arg Complex.re this
            simp only at h_re
            exact h_re
      _ = ‖U_grp.U t ψ‖ ^ 2 := by norm_cast

  have h2 : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
    calc (⟪ψ, ψ⟫_ℂ).re
        = ((‖ψ‖ ^ 2 : ℂ)).re := by
            have h_re := congr_arg Complex.re this
            simp only at h_re
            exact h_re
      _ = ‖ψ‖ ^ 2 := by norm_cast

  -- From h: ⟨Uψ, Uψ⟩ = ⟨ψ, ψ⟩, we get ‖Uψ‖² = ‖ψ‖²
  have h_sq : ‖U_grp.U t ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    calc ‖U_grp.U t ψ‖ ^ 2
        = (⟪U_grp.U t ψ, U_grp.U t ψ⟫_ℂ).re := h1.symm
      _ = (⟪ψ, ψ⟫_ℂ).re := by rw [h]
      _ = ‖ψ‖ ^ 2 := h2

  -- Take square roots
  have : ‖U_grp.U t ψ‖ = ‖ψ‖ ∨ ‖U_grp.U t ψ‖ = -‖ψ‖ := by
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h_sq
  cases this with
  | inl h => exact h
  | inr h =>
      -- ‖U(t)ψ‖ = -‖ψ‖, but both are non-negative, so both = 0
      have h1 : 0 ≤ ‖U_grp.U t ψ‖ := norm_nonneg _
      have h2 : 0 ≤ ‖ψ‖ := norm_nonneg _
      linarith


/--
U(t) has operator norm equal to 1.

**Mathematical Content:**
For any t ∈ ℝ, the operator norm of U(t) is exactly 1:
  ‖U(t)‖ = sup{‖U(t)ψ‖ : ‖ψ‖ ≤ 1} = 1

**Proof Strategy:**
Two inequalities:
1. **Upper bound (‖U(t)‖ ≤ 1):**
   For any ψ: ‖U(t)ψ‖ = ‖ψ‖ ≤ ‖ψ‖, so ‖U(t)‖ ≤ 1

2. **Lower bound (‖U(t)‖ ≥ 1):**
   Use the factorization U(0) = U(t)U(-t) and submultiplicativity:
   - 1 = ‖I‖ = ‖U(0)‖ = ‖U(t)U(-t)‖ ≤ ‖U(t)‖·‖U(-t)‖
   - Both ‖U(t)‖ ≤ 1 and ‖U(-t)‖ ≤ 1
   - Therefore ‖U(t)‖·‖U(-t)‖ ≥ 1 forces ‖U(t)‖ = 1

**Why This Matters:**
- Confirms U(t) is a unitary operator in the operator norm sense
- Shows the group of unitary operators sits on the "unit sphere" of operators
- Essential for bounding errors in numerical integration of Schrödinger equation
- Proves the propagator is optimally conditioned (condition number = 1)

**Physical Interpretation:**
In quantum mechanics, ‖U(t)‖ = 1 means time evolution is "perfectly stable":
no amplification or decay of states under unitary dynamics. The worst-case
amplification factor is exactly 1 - quantum evolution is optimally well-behaved
from a numerical analysis perspective.

**Relation to Other Properties:**
- Combines `norm_preserving` (pointwise: ‖U(t)ψ‖ = ‖ψ‖) with submultiplicativity
- The identity ‖U(t)‖·‖U(-t)‖ ≥ ‖U(t)U(-t)‖ = 1 is tight: equality holds
- Shows unitary operators form a bounded subset of B(H) with radius 1
- Essential for proving the generator A is densely defined (bounded operators
  couldn't have densely defined unbounded inverses)

**Note:** Requires `[Nontrivial H]` to ensure ‖I‖ = 1. In the trivial space
H = {0}, all operators have norm 0.
-/
theorem norm_one [Nontrivial H] (U_grp : OneParameterUnitaryGroup (H := H)) (t : ℝ) :
    ‖U_grp.U t‖ = 1 := by
  have h_le : ‖U_grp.U t‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound
    · norm_num
    · intro ψ
      calc ‖U_grp.U t ψ‖
          = ‖ψ‖ := norm_preserving U_grp t ψ
        _ = 1 * ‖ψ‖ := by ring
      rfl

  have h_ge : 1 ≤ ‖U_grp.U t‖ := by
    calc 1 = ‖ContinuousLinearMap.id ℂ H‖ := ContinuousLinearMap.norm_id.symm
      _ = ‖U_grp.U 0‖ := by rw [← U_grp.identity]
      _ = ‖U_grp.U (t + (-t))‖ := by ring_nf
      _ = ‖(U_grp.U t).comp (U_grp.U (-t))‖ := by rw [← U_grp.group_law]
      _ ≤ ‖U_grp.U t‖ * ‖U_grp.U (-t)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖U_grp.U t‖ * 1 := by
          have : ‖U_grp.U (-t)‖ ≤ 1 := by
            apply ContinuousLinearMap.opNorm_le_bound
            · norm_num
            · intro ψ
              calc ‖U_grp.U (-t) ψ‖ = ‖ψ‖ := norm_preserving U_grp (-t) ψ
                _ = 1 * ‖ψ‖ := by ring
              rfl
          exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖U_grp.U t‖ := by ring

  exact le_antisymm h_le h_ge

end OneParameterUnitaryGroup

/-!
================================================================================
SECTION 2: GENERATORS (UNBOUNDED OPERATORS)
================================================================================

The generator A of a group U(t) is defined by:
  Aψ = -i lim_{t→0} (U(t)ψ - ψ)/t

This is an UNBOUNDED operator, so we use Robertson's proven pattern:
  - Linear operator on all of H (type-wise)
  - Dense domain where it's actually defined
  - Self-adjointness via inner product condition
-/

/--
Generator of a one-parameter unitary group.

Uses the Robertson.Core.UnboundedObservable pattern for domain tracking.

Key challenge: Proving this is self-adjoint, not just symmetric!
Self-adjointness requires proving Range(A ± iI) = H (the hard part).
-/
structure Generator (U_grp : OneParameterUnitaryGroup (H := H)) where
  /-- The operator itself (formally defined on all of H) -/
  op : H →ₗ[ℂ] H

  /-- Dense domain where the limit defining the generator exists -/
  domain : Submodule ℂ H

  /-- The domain is dense (crucial for Stone's theorem) -/
  dense_domain : Dense (domain : Set H)

  /-- Generator formula: Aψ = -i lim_{t→0} (U(t)ψ - ψ)/t

  The limit is taken in the punctured neighborhood of 0.
  We express: Aψ = lim_{t→0, t≠0} (U(t)ψ - ψ)/(it)
  -/
  generator_formula : ∀ (ψ : H) (_ /-hψ-/ : ψ ∈ domain),
    Tendsto (fun t : ℝ => ((I : ℂ) * (t : ℂ))⁻¹ • (U_grp.U t ψ - ψ))
          (𝓝[≠] 0)
          (𝓝 (op ψ))

  /-- Domain is invariant under time evolution -/
  domain_invariant : ∀ (t : ℝ) (ψ : H), ψ ∈ domain → U_grp.U t ψ ∈ domain

  /-- Generator is symmetric (self-adjointness proven separately) -/
  symmetric : ∀ (ψ φ : H), ψ ∈ domain → φ ∈ domain →
    ⟪op ψ, φ⟫_ℂ = ⟪ψ, op φ⟫_ℂ

/-!
### Key Construction Lemmas for Generators

These prove that the domain has the required properties.
-/

namespace Generator

/-
Elements of the form ∫₀^h U(t)ψ dt are in the domain.
This is the key construction proving domain densit
-/

/-!
================================================================================
SECTION 3: SELF-ADJOINTNESS CRITERIA
================================================================================

Self-adjoint ≠ Symmetric!

For unbounded operators:
  - Symmetric: ⟨Aψ,φ⟩ = ⟨ψ,Aφ⟩ for ψ,φ ∈ D(A)
  - Self-adjoint: A = A* (including domain equality!)

The key criterion for self-adjointness:
  A symmetric + Range(A ± iI) = H  ⟹  A self-adjoint
-/

/--
A generator is self-adjoint if its range under (A ± iI) covers H.

This is the HARD part of Stone's theorem! We'll prove this using
the integral: ψ = ∫₀^∞ e^{-t} U(t)φ dt
-/
def IsSelfAdjoint {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) : Prop :=
  (∀ φ : H, ∃ (ψ : H) (_ /-hψ-/ : ψ ∈ gen.domain),
    gen.op ψ + (I : ℂ) • ψ = φ) ∧
  (∀ φ : H, ∃ (ψ : H) (_ /-hψ-/ : ψ ∈ gen.domain),
    gen.op ψ - (I : ℂ) • ψ = φ)

/-!
### The Resolvent (For Self-Adjoint Generators)

For self-adjoint A and z ∉ ℝ, the resolvent R_z = (A - zI)^{-1} exists
as a BOUNDED operator on H.

This is magic: unbounded operator → family of bounded operators!
-/
/-
================================================================================
SECTION 4: Resolvent
================================================================================
-/

/--
The solution chosen by `resolvent_at_i` satisfies the defining equation.

**Statement:** For any φ ∈ H, the element `Classical.choose (hsa.2 φ)` returned by
the self-adjointness property satisfies:
1. It's in the domain: `ψ ∈ gen.domain`
2. It solves the equation: `(A - iI)ψ = φ`

**Purpose:**
This is the extraction lemma that unpacks the existential quantifier in
`IsSelfAdjoint gen`. It's the bridge between:
- The abstract existence claim: "∀ φ, ∃ ψ ∈ domain, (A - iI)ψ = φ"
- The concrete chosen value: `Classical.choose (hsa.2 φ)`

**Usage Pattern:**
```lean
have h := resolvent_at_i_spec gen hsa φ
-- Now h.1 : chosen element ∈ domain
-- And h.2 : (A - iI)(chosen element) = φ
```

**Why Separate from Uniqueness:**
- `resolvent_at_i_spec`: Existence (unpacks `Classical.choose_spec`)
- `resolvent_at_i_unique`: Uniqueness (proven via eigenvalue contradiction)
Together they justify using `Classical.choose` to define the resolvent as a function.

**Technical Note:**
The `.2` in `hsa.2` selects the second component of the conjunction in
`IsSelfAdjoint`, which gives Range(A - iI) = H. The `.1` would give Range(A + iI) = H.
-/
lemma resolvent_at_i_spec {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : IsSelfAdjoint gen) (φ : H) :
    Classical.choose (hsa.2 φ) ∈ gen.domain ∧
    gen.op (Classical.choose (hsa.2 φ)) - I • (Classical.choose (hsa.2 φ)) = φ := by
  obtain ⟨h_mem, h_eq⟩ := Classical.choose_spec (hsa.2 φ)
  exact ⟨h_mem, h_eq⟩





/--
Uniqueness of solutions to (A - iI)ψ = φ.

**Statement:** If ψ₁ and ψ₂ both satisfy (A - iI)ψ = φ for the same φ, then ψ₁ = ψ₂.

**Proof Strategy:**
1. Subtract equations: (A - iI)(ψ₁ - ψ₂) = 0
2. So A(ψ₁ - ψ₂) = i(ψ₁ - ψ₂), making i an eigenvalue with eigenvector ψ₁ - ψ₂
3. Take inner product: ⟨A(ψ₁ - ψ₂), ψ₁ - ψ₂⟩ = i‖ψ₁ - ψ₂‖²
4. But A is symmetric, so ⟨A(ψ₁ - ψ₂), ψ₁ - ψ₂⟩ ∈ ℝ
5. A purely imaginary number (i‖ψ₁ - ψ₂‖²) equals a real number only if both = 0
6. Therefore ‖ψ₁ - ψ₂‖² = 0, giving ψ₁ = ψ₂

**Key Insight:** Self-adjoint operators cannot have non-real eigenvalues. This is
the fundamental obstruction that makes (A - zI) invertible for z ∉ ℝ.

**Why This Matters:**
- Makes `resolvent_at_i` well-defined (Classical.choose gives THE unique solution)
- Proves injectivity of (A - iI), which combined with surjectivity gives invertibility
- The same argument works for ANY z with Im(z) ≠ 0, giving the full resolvent

**Physical Meaning:**
A quantum system with Hamiltonian H cannot have complex energy eigenvalues
(energy must be real). This is equivalent to H being self-adjoint.
-/
lemma resolvent_at_i_unique {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (_ /-hsa-/ : IsSelfAdjoint gen)
    (φ ψ₁ ψ₂ : H)
    (hψ₁ : ψ₁ ∈ gen.domain) (hψ₂ : ψ₂ ∈ gen.domain)
    (h₁ : gen.op ψ₁ - I • ψ₁ = φ) (h₂ : gen.op ψ₂ - I • ψ₂ = φ) :
    ψ₁ = ψ₂ := by

  -- Subtract the equations
  have h_diff : gen.op ψ₁ - I • ψ₁ - (gen.op ψ₂ - I • ψ₂) = 0 := by
    rw [h₁, h₂]
    simp

  -- First, show ψ₁ - ψ₂ ∈ domain (Submodule is closed under subtraction)
  have h_sub_domain : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem hψ₁ hψ₂

  -- Rewrite as (A - iI)(ψ₁ - ψ₂) = 0
  have h_factor : gen.op (ψ₁ - ψ₂) - I • (ψ₁ - ψ₂) = 0 := by
    have op_sub := gen.op.map_sub ψ₁ ψ₂
    calc gen.op (ψ₁ - ψ₂) - I • (ψ₁ - ψ₂)
        = (gen.op ψ₁ - gen.op ψ₂) - I • (ψ₁ - ψ₂) := by rw [op_sub]
      _ = (gen.op ψ₁ - gen.op ψ₂) - (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
      _ = (gen.op ψ₁ - I • ψ₁) - (gen.op ψ₂ - I • ψ₂) := by abel
      _ = 0 := h_diff

  -- So A(ψ₁ - ψ₂) = i(ψ₁ - ψ₂)
  have h_eigen : gen.op (ψ₁ - ψ₂) = I • (ψ₁ - ψ₂) := by
    exact sub_eq_zero.mp h_factor

  -- Take inner product with (ψ₁ - ψ₂)
  have h_inner : ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ = (starRingEnd ℂ) I * ‖ψ₁ - ψ₂‖ ^ 2 := by
    rw [h_eigen, inner_smul_left, inner_self_eq_norm_sq_to_K]
    rfl
  -- Simplify: conj(I) = -I
  have h_inner' : ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ = -I * ‖ψ₁ - ψ₂‖ ^ 2 := by
    rw [h_inner]
    simp only [Complex.conj_I]

  -- But A is symmetric, so ⟨A(ψ₁ - ψ₂), ψ₁ - ψ₂⟩ is real
  have h_sym : ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ = ⟪ψ₁ - ψ₂, gen.op (ψ₁ - ψ₂)⟫_ℂ := by
    exact gen.symmetric (ψ₁ - ψ₂) (ψ₁ - ψ₂) h_sub_domain h_sub_domain

  -- So ⟨A(ψ₁ - ψ₂), ψ₁ - ψ₂⟩ is real (equals its own conjugate)
  have h_real : (⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ).im = 0 := by
    have eq_conj : ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ = (starRingEnd ℂ) ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ := by
      calc ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ
          = ⟪ψ₁ - ψ₂, gen.op (ψ₁ - ψ₂)⟫_ℂ := h_sym
        _ = (starRingEnd ℂ) ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ :=
            (inner_conj_symm (ψ₁ - ψ₂) (gen.op (ψ₁ - ψ₂))).symm
    -- z = conj(z) means Im(z) = -Im(z), so Im(z) = 0
    have h_parts := Complex.ext_iff.mp eq_conj
    simp only [Complex.conj_im] at h_parts
    linarith [h_parts.2]

  -- But we also have it equals -I * ‖ψ₁ - ψ₂‖², which has imaginary part -‖ψ₁ - ψ₂‖²
  have h_imag : (⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ).im = -(‖ψ₁ - ψ₂‖ ^ 2) := by
    rw [h_inner']
    rw [mul_comm, Complex.mul_im]
    simp only [Complex.neg_re, Complex.neg_im,
              Complex.I_re, Complex.I_im, mul_zero,neg_zero]
    -- Now: (↑‖ψ₁ - ψ₂‖ ^ 2).re * -1 + 0 = -‖ψ₁ - ψ₂‖ ^ 2
    norm_cast
    ring_nf
    simp

  -- Combining: ‖ψ₁ - ψ₂‖² = 0
  have : ‖ψ₁ - ψ₂‖ ^ 2 = 0 := by
    have h_eq : -(‖ψ₁ - ψ₂‖ ^ 2) = (0 : ℝ) := by
      calc -(‖ψ₁ - ψ₂‖ ^ 2) = (⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ).im := h_imag.symm
        _ = 0 := h_real
    linarith

  -- Therefore ψ₁ = ψ₂
  have : ‖ψ₁ - ψ₂‖ = 0 := by
    exact sq_eq_zero_iff.mp this
  exact sub_eq_zero.mp (norm_eq_zero.mp this)



/--
The resolvent operator R_i = (A - iI)⁻¹ at z = i.

**Mathematical Content:**
For a self-adjoint generator A, the resolvent at i is the bounded linear operator
that inverts (A - iI). For each φ ∈ H, it returns the unique ψ ∈ domain(A)
satisfying:
  (A - iI)ψ = φ

**Existence:** The self-adjointness condition `IsSelfAdjoint` guarantees that
Range(A - iI) = H, so every φ has a solution.

**Uniqueness:** If A is symmetric and (A - iI)ψ = 0, then Aψ = iψ, making i
an eigenvalue. But taking ⟨Aψ, ψ⟩ gives a real number (by symmetry) equal to
i‖ψ‖² (imaginary), forcing ψ = 0. Hence (A - iI) is injective.

**Boundedness:** The key identity
  ‖(A - iI)ψ‖² = ‖Aψ‖² + ‖ψ‖²
(which holds because Re⟨Aψ, iψ⟩ = 0 for symmetric A) proves ‖(A - iI)ψ‖ ≥ ‖ψ‖,
giving the Lipschitz bound ‖R_i‖ ≤ 1.

**Significance:**
- First step in proving the spectral theorem via functional calculus
- Base case for constructing R_z for all z ∉ ℝ via Neumann series
- The existence of bounded resolvents off the real line is THE defining property
  distinguishing self-adjoint from merely symmetric operators

**Physical Interpretation:**
In quantum mechanics, (E - H)⁻¹ is the resolvent of the Hamiltonian H. Its poles
on the real axis are the energy eigenvalues. The resolvent at i represents the
response of the system to a complex energy probe.

**Implementation Note:**
Uses `Classical.choose` to extract solutions from the existential in `IsSelfAdjoint`.
Linearity and continuity are proven via the uniqueness of solutions to (A - iI)ψ = φ.
-/
noncomputable def resolvent_at_i {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : IsSelfAdjoint gen) : H →L[ℂ] H where
  toFun φ := Classical.choose (hsa.2 φ)

  map_add' := by
    intro φ₁ φ₂
    -- Strategy: Both R(φ₁) + R(φ₂) and R(φ₁ + φ₂) satisfy (A - iI)·(?) = φ₁ + φ₂
    -- By uniqueness, they're equal

    -- Extract what we know about R(φ₁) and R(φ₂)
    have h₁ := resolvent_at_i_spec gen hsa φ₁
    have h₂ := resolvent_at_i_spec gen hsa φ₂
    have h_sum := resolvent_at_i_spec gen hsa (φ₁ + φ₂)

    -- Show R(φ₁) + R(φ₂) is in domain
    have h_add_domain : Classical.choose (hsa.2 φ₁) + Classical.choose (hsa.2 φ₂) ∈ gen.domain :=
      gen.domain.add_mem h₁.1 h₂.1

    -- Show (A - iI)(R(φ₁) + R(φ₂)) = φ₁ + φ₂
    have h_add_eq : gen.op (Classical.choose (hsa.2 φ₁) + Classical.choose (hsa.2 φ₂)) -
                    I • (Classical.choose (hsa.2 φ₁) + Classical.choose (hsa.2 φ₂)) = φ₁ + φ₂ := by
      have op_add := gen.op.map_add (Classical.choose (hsa.2 φ₁)) (Classical.choose (hsa.2 φ₂))
      calc gen.op (Classical.choose (hsa.2 φ₁) + Classical.choose (hsa.2 φ₂)) -
           I • (Classical.choose (hsa.2 φ₁) + Classical.choose (hsa.2 φ₂))
          = (gen.op (Classical.choose (hsa.2 φ₁)) + gen.op (Classical.choose (hsa.2 φ₂))) -
            I • (Classical.choose (hsa.2 φ₁) + Classical.choose (hsa.2 φ₂)) := by rw [op_add]
        _ = (gen.op (Classical.choose (hsa.2 φ₁)) + gen.op (Classical.choose (hsa.2 φ₂))) -
            (I • Classical.choose (hsa.2 φ₁) + I • Classical.choose (hsa.2 φ₂)) := by rw [smul_add]
        _ = (gen.op (Classical.choose (hsa.2 φ₁)) - I • Classical.choose (hsa.2 φ₁)) +
            (gen.op (Classical.choose (hsa.2 φ₂)) - I • Classical.choose (hsa.2 φ₂)) := by abel
        _ = φ₁ + φ₂ := by rw [h₁.2, h₂.2]

    -- Apply uniqueness
    exact (resolvent_at_i_unique gen hsa (φ₁ + φ₂)
      (Classical.choose (hsa.2 φ₁) + Classical.choose (hsa.2 φ₂))
      (Classical.choose (hsa.2 (φ₁ + φ₂)))
      h_add_domain h_sum.1 h_add_eq h_sum.2).symm

  map_smul' := by
    intro c φ
    -- Similar strategy: both c•R(φ) and R(c•φ) satisfy (A - iI)·(?) = c•φ

    have h := resolvent_at_i_spec gen hsa φ
    have h_scaled := resolvent_at_i_spec gen hsa (c • φ)

    -- Show c•R(φ) is in domain
    have h_smul_domain : c • Classical.choose (hsa.2 φ) ∈ gen.domain :=
      gen.domain.smul_mem c h.1

    -- Show (A - iI)(c•R(φ)) = c•φ
    have h_smul_eq : gen.op (c • Classical.choose (hsa.2 φ)) -
                     I • (c • Classical.choose (hsa.2 φ)) = c • φ := by
      have op_smul := gen.op.map_smul c (Classical.choose (hsa.2 φ))
      calc gen.op (c • Classical.choose (hsa.2 φ)) - I • (c • Classical.choose (hsa.2 φ))
          = c • gen.op (Classical.choose (hsa.2 φ)) - I • (c • Classical.choose (hsa.2 φ)) := by rw [op_smul]
        _ = c • gen.op (Classical.choose (hsa.2 φ)) - c • (I • Classical.choose (hsa.2 φ)) := by rw [smul_comm]
        _ = c • (gen.op (Classical.choose (hsa.2 φ)) - I • Classical.choose (hsa.2 φ)) := by rw [smul_sub]
        _ = c • φ := by rw [h.2]

    -- Apply uniqueness
    exact (resolvent_at_i_unique gen hsa (c • φ)
      (c • Classical.choose (hsa.2 φ))
      (Classical.choose (hsa.2 (c • φ)))
      h_smul_domain h_scaled.1 h_smul_eq h_scaled.2).symm

  cont := by
    have lip : LipschitzWith 1 (fun φ => Classical.choose (hsa.2 φ)) := by
      intro φ₁ φ₂

      let ψ₁ := Classical.choose (hsa.2 φ₁)
      let ψ₂ := Classical.choose (hsa.2 φ₂)

      have h₁ := resolvent_at_i_spec gen hsa φ₁
      have h₂ := resolvent_at_i_spec gen hsa φ₂

      -- (A - iI)(ψ₁ - ψ₂) = φ₁ - φ₂
      have h_diff : gen.op (ψ₁ - ψ₂) - I • (ψ₁ - ψ₂) = φ₁ - φ₂ := by
        calc gen.op (ψ₁ - ψ₂) - I • (ψ₁ - ψ₂)
            = (gen.op ψ₁ - gen.op ψ₂) - I • (ψ₁ - ψ₂) := by rw [gen.op.map_sub]
          _ = (gen.op ψ₁ - gen.op ψ₂) - (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
          _ = (gen.op ψ₁ - I • ψ₁) - (gen.op ψ₂ - I • ψ₂) := by abel
          _ = φ₁ - φ₂ := by rw [h₁.2, h₂.2]

      -- ‖ψ₁ - ψ₂‖ ≤ ‖φ₁ - φ₂‖
      -- ‖ψ₁ - ψ₂‖ ≤ ‖φ₁ - φ₂‖
      have bound : ‖ψ₁ - ψ₂‖ ≤ ‖φ₁ - φ₂‖ := by
        let Δψ := ψ₁ - ψ₂

        -- Key: ‖(A - iI)Δψ‖² = ‖A(Δψ)‖² + ‖Δψ‖²
        have key_expand : ‖gen.op Δψ - I • Δψ‖ ^ 2 = ‖gen.op Δψ‖ ^ 2 + ‖Δψ‖ ^ 2 := by
          have h_sub_domain : Δψ ∈ gen.domain := gen.domain.sub_mem h₁.1 h₂.1

          -- Expand ‖x - y‖² = ‖x‖² + ‖y‖² - 2 Re⟨x, y⟩
          have expand : ‖gen.op Δψ - I • Δψ‖ ^ 2 =
              ‖gen.op Δψ‖ ^ 2 + ‖I • Δψ‖ ^ 2 - 2 * (⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by
            -- Convert LHS to inner product
            have h1 : ‖gen.op Δψ - I • Δψ‖ ^ 2 = (⟪gen.op Δψ - I • Δψ, gen.op Δψ - I • Δψ⟫_ℂ).re := by
              have h_inner : (⟪gen.op Δψ - I • Δψ, gen.op Δψ - I • Δψ⟫_ℂ).re = ‖gen.op Δψ - I • Δψ‖ ^ 2 := by
                have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op Δψ - I • Δψ)
                -- this gives: ⟪x, x⟫_ℂ = ↑‖x‖^2

                -- Take .re of both sides
                have h_re_both : (⟪gen.op Δψ - I • Δψ, gen.op Δψ - I • Δψ⟫_ℂ).re = ((‖gen.op Δψ - I • Δψ‖ ^ 2 : ℂ)).re := by
                  rw [this]
                  norm_cast

                -- Now use that (↑r).re = r
                have h_re : ((‖gen.op Δψ - I • Δψ‖ ^ 2 : ℂ)).re = ‖gen.op Δψ - I • Δψ‖ ^ 2 := by
                  norm_cast

                rw [h_re_both, h_re]

              rw [← h_inner]

            rw [h1, inner_sub_left, inner_sub_right, inner_sub_right]
            simp only [Complex.sub_re]

            -- Convert RHS norms to inner products
            have h2 : ‖gen.op Δψ‖ ^ 2 = (⟪gen.op Δψ, gen.op Δψ⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op Δψ)
              rw [this]
              norm_cast


            have h3 : ‖I • Δψ‖ ^ 2 = (⟪I • Δψ, I • Δψ⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (I • Δψ)
              rw [this]
              norm_cast

            rw [h2, h3]

            -- Cross terms
            have h_cross : (⟪gen.op Δψ, I • Δψ⟫_ℂ).re + (⟪I • Δψ, gen.op Δψ⟫_ℂ).re =
                          2 * (⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by
              have := inner_conj_symm (𝕜 := ℂ) (gen.op Δψ) (I • Δψ)
              have h_eq : (⟪I • Δψ, gen.op Δψ⟫_ℂ).re = (⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by
                calc (⟪I • Δψ, gen.op Δψ⟫_ℂ).re
                    = ((starRingEnd ℂ) ⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by norm_num
                  _ = (⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by simp only [Complex.conj_re]
              rw [h_eq]
              ring

            rw [h_cross.symm]
            ring

          -- Show ‖iΔψ‖ = ‖Δψ‖
          have norm_I_smul : ‖I • Δψ‖ = ‖Δψ‖ := by
            rw [norm_smul]
            simp

          -- Show Re⟨A(Δψ), iΔψ⟩ = 0
          have cross_zero : (⟪gen.op Δψ, I • Δψ⟫_ℂ).re = 0 := by
            have h_sub_domain : Δψ ∈ gen.domain := gen.domain.sub_mem h₁.1 h₂.1

            rw [inner_smul_right]
            -- ⟨Aψ, iψ⟩ = i⟨Aψ, ψ⟩
            have h1 : I * ⟪gen.op Δψ, Δψ⟫_ℂ = I * (⟪gen.op Δψ, Δψ⟫_ℂ).re +
                      I * Complex.I * (⟪gen.op Δψ, Δψ⟫_ℂ).im := by
              conv_lhs => rw [← Complex.re_add_im (⟪gen.op Δψ, Δψ⟫_ℂ)]
              ring

            -- A is symmetric, so ⟨Aψ, ψ⟩ is real
            have h_real : (⟪gen.op Δψ, Δψ⟫_ℂ).im = 0 := by
              have h_sym := gen.symmetric Δψ Δψ h_sub_domain h_sub_domain
              have h_conj : ⟪gen.op Δψ, Δψ⟫_ℂ = (starRingEnd ℂ) ⟪gen.op Δψ, Δψ⟫_ℂ := by
                rw [h_sym]
                calc ⟪Δψ, gen.op Δψ⟫_ℂ
                  = ⟪gen.op Δψ, Δψ⟫_ℂ := (gen.symmetric Δψ Δψ h_sub_domain h_sub_domain).symm
                _ = (starRingEnd ℂ) ⟪Δψ, gen.op Δψ⟫_ℂ := (inner_conj_symm (𝕜 := ℂ) (gen.op Δψ) Δψ).symm
              have := Complex.ext_iff.mp h_conj
              simp only [Complex.conj_im] at this
              linarith [this.2]

            rw [h1, h_real]
            -- Now: (i * re).re = 0
            simp

          rw [expand, norm_I_smul, cross_zero]
          ring

        -- Therefore ‖(A - iI)Δψ‖² ≥ ‖Δψ‖²
        have le_sq : ‖Δψ‖ ^ 2 ≤ ‖gen.op Δψ - I • Δψ‖ ^ 2 := by
          rw [key_expand]
          have : 0 ≤ ‖gen.op Δψ‖ ^ 2 := sq_nonneg _
          linarith

        -- Take square roots
        have le_norm : ‖Δψ‖ ≤ ‖gen.op Δψ - I • Δψ‖ := by
          have h_nonneg_left : 0 ≤ ‖Δψ‖ := norm_nonneg _
          have h_nonneg_right : 0 ≤ ‖gen.op Δψ - I • Δψ‖ := norm_nonneg _
          have h_sq : ‖Δψ‖ ^ 2 ≤ ‖gen.op Δψ - I • Δψ‖ ^ 2 := le_sq
          by_contra h_not
          push_neg at h_not
          -- If ‖Δψ‖ > ‖gen.op Δψ - I • Δψ‖, then ‖Δψ‖² > ‖gen.op Δψ - I • Δψ‖²
          have : ‖gen.op Δψ - I • Δψ‖ ^ 2 < ‖Δψ‖ ^ 2 := by
            nlinarith [sq_nonneg (‖Δψ‖ - ‖gen.op Δψ - I • Δψ‖)]
          linarith

        -- Substitute back
        calc ‖ψ₁ - ψ₂‖ = ‖Δψ‖ := rfl
          _ ≤ ‖gen.op Δψ - I • Δψ‖ := le_norm
          _ = ‖φ₁ - φ₂‖ := by rw [h_diff]

      -- Convert to edist
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
      simp only [ENNReal.coe_one, one_mul]
      exact ENNReal.ofReal_le_ofReal bound

    exact lip.continuous






/--
The resolvent operator R_{-i} = (A + iI)⁻¹ at z = -i.

**Mathematical Content:**
For a self-adjoint generator A, the resolvent at -i is the bounded linear operator
that inverts (A + iI). For each φ ∈ H, it returns the unique ψ ∈ domain(A)
satisfying:
  (A + iI)ψ = φ

**Relation to R_i:**
This is the "conjugate" of `resolvent_at_i`. While R_i inverts (A - iI), this
inverts (A + iI). Together they demonstrate that the resolvent exists on both
sides of the real axis.

**Construction:**
Uses the first component `hsa.1` of `IsSelfAdjoint`, which guarantees
Range(A + iI) = H (compare to `hsa.2` which gives Range(A - iI) = H).

The proof of boundedness uses the same key identity:
  ‖(A + iI)ψ‖² = ‖Aψ‖² + ‖ψ‖²
giving ‖R_{-i}‖ ≤ 1.

**Why Both Resolvents?:**
Having both R_i and R_{-i} proves that A has resolvent in both upper and lower
half-planes. This bilateral surjectivity is characteristic of self-adjoint operators
(symmetric operators may fail on one or both sides).
-/
noncomputable def resolvent_at_neg_i {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : IsSelfAdjoint gen) : H →L[ℂ] H where
  toFun φ := Classical.choose (hsa.1 φ)

  map_add' := by
    intro φ₁ φ₂
    -- Same proof structure as resolvent_at_i, but with (A + iI) instead of (A - iI)
    have h₁ := Classical.choose_spec (hsa.1 φ₁)
    have h₂ := Classical.choose_spec (hsa.1 φ₂)
    have h_sum := Classical.choose_spec (hsa.1 (φ₁ + φ₂))

    have h_add_domain : Classical.choose (hsa.1 φ₁) + Classical.choose (hsa.1 φ₂) ∈ gen.domain :=
      gen.domain.add_mem h₁.1 h₂.1

    have h_add_eq : gen.op (Classical.choose (hsa.1 φ₁) + Classical.choose (hsa.1 φ₂)) +
                    I • (Classical.choose (hsa.1 φ₁) + Classical.choose (hsa.1 φ₂)) = φ₁ + φ₂ := by
      have op_add := gen.op.map_add (Classical.choose (hsa.1 φ₁)) (Classical.choose (hsa.1 φ₂))
      calc gen.op (Classical.choose (hsa.1 φ₁) + Classical.choose (hsa.1 φ₂)) +
           I • (Classical.choose (hsa.1 φ₁) + Classical.choose (hsa.1 φ₂))
          = (gen.op (Classical.choose (hsa.1 φ₁)) + gen.op (Classical.choose (hsa.1 φ₂))) +
            I • (Classical.choose (hsa.1 φ₁) + Classical.choose (hsa.1 φ₂)) := by rw [op_add]
        _ = (gen.op (Classical.choose (hsa.1 φ₁)) + gen.op (Classical.choose (hsa.1 φ₂))) +
            (I • Classical.choose (hsa.1 φ₁) + I • Classical.choose (hsa.1 φ₂)) := by rw [smul_add]
        _ = (gen.op (Classical.choose (hsa.1 φ₁)) + I • Classical.choose (hsa.1 φ₁)) +
            (gen.op (Classical.choose (hsa.1 φ₂)) + I • Classical.choose (hsa.1 φ₂)) := by abel
        _ = φ₁ + φ₂ := by rw [h₁.2, h₂.2]

    -- Uniqueness proof (same structure, using (A + iI) instead of (A - iI))
    have unique : ∀ ψ₁ ψ₂, ψ₁ ∈ gen.domain → ψ₂ ∈ gen.domain →
                  gen.op ψ₁ + I • ψ₁ = φ₁ + φ₂ → gen.op ψ₂ + I • ψ₂ = φ₁ + φ₂ → ψ₁ = ψ₂ := by
      intro ψ₁ ψ₂ hψ₁ hψ₂ heq₁ heq₂
      have h_diff : gen.op ψ₁ + I • ψ₁ - (gen.op ψ₂ + I • ψ₂) = 0 := by
        rw [heq₁, heq₂]; simp
      have h_sub_domain : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem hψ₁ hψ₂
      have h_factor : gen.op (ψ₁ - ψ₂) + I • (ψ₁ - ψ₂) = 0 := by
        have op_sub := gen.op.map_sub ψ₁ ψ₂
        calc gen.op (ψ₁ - ψ₂) + I • (ψ₁ - ψ₂)
            = (gen.op ψ₁ - gen.op ψ₂) + I • (ψ₁ - ψ₂) := by rw [op_sub]
          _ = (gen.op ψ₁ - gen.op ψ₂) + (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
          _ = (gen.op ψ₁ + I • ψ₁) - (gen.op ψ₂ + I • ψ₂) := by abel
          _ = 0 := h_diff
      have h_eigen : gen.op (ψ₁ - ψ₂) = -I • (ψ₁ - ψ₂) := by
        have := add_eq_zero_iff_eq_neg.mp h_factor
        rw [← neg_smul] at this
        exact this
      have h_inner : ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ = (starRingEnd ℂ) (-I) * ‖ψ₁ - ψ₂‖ ^ 2 := by
        rw [h_eigen, inner_smul_left, inner_self_eq_norm_sq_to_K]; rfl
      have h_inner' : ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ = I * ‖ψ₁ - ψ₂‖ ^ 2 := by
        rw [h_inner]; simp only [Complex.conj_neg_I]
      have h_sym : ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ = ⟪ψ₁ - ψ₂, gen.op (ψ₁ - ψ₂)⟫_ℂ := by
        exact gen.symmetric (ψ₁ - ψ₂) (ψ₁ - ψ₂) h_sub_domain h_sub_domain
      have h_real : (⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ).im = 0 := by
        have eq_conj : ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ = (starRingEnd ℂ) ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ := by
          calc ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ
              = ⟪ψ₁ - ψ₂, gen.op (ψ₁ - ψ₂)⟫_ℂ := h_sym
            _ = (starRingEnd ℂ) ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ :=
                (inner_conj_symm (𝕜 := ℂ) (ψ₁ - ψ₂) (gen.op (ψ₁ - ψ₂))).symm
        have h_parts := Complex.ext_iff.mp eq_conj
        simp only [Complex.conj_im] at h_parts
        linarith [h_parts.2]
      have h_imag : (⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ).im = ‖ψ₁ - ψ₂‖ ^ 2 := by
        rw [h_inner', mul_comm, Complex.mul_im]
        simp only [Complex.I_re, Complex.I_im, mul_zero]
        norm_cast; ring_nf
      have : ‖ψ₁ - ψ₂‖ ^ 2 = 0 := by
        have h_eq : ‖ψ₁ - ψ₂‖ ^ 2 = (0 : ℝ) := by
          calc ‖ψ₁ - ψ₂‖ ^ 2 = (⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ).im := h_imag.symm
            _ = 0 := h_real
        exact h_eq
      have : ‖ψ₁ - ψ₂‖ = 0 := sq_eq_zero_iff.mp this
      exact sub_eq_zero.mp (norm_eq_zero.mp this)

    exact (unique _ _ h_add_domain h_sum.1 h_add_eq h_sum.2).symm

  map_smul' := by
    intro c φ
    have h := Classical.choose_spec (hsa.1 φ)
    have h_scaled := Classical.choose_spec (hsa.1 (c • φ))

    have h_smul_domain : c • Classical.choose (hsa.1 φ) ∈ gen.domain :=
      gen.domain.smul_mem c h.1

    have h_smul_eq : gen.op (c • Classical.choose (hsa.1 φ)) +
                     I • (c • Classical.choose (hsa.1 φ)) = c • φ := by
      have op_smul := gen.op.map_smul c (Classical.choose (hsa.1 φ))
      calc gen.op (c • Classical.choose (hsa.1 φ)) + I • (c • Classical.choose (hsa.1 φ))
          = c • gen.op (Classical.choose (hsa.1 φ)) + I • (c • Classical.choose (hsa.1 φ)) := by rw [op_smul]
        _ = c • gen.op (Classical.choose (hsa.1 φ)) + c • (I • Classical.choose (hsa.1 φ)) := by rw [smul_comm]
        _ = c • (gen.op (Classical.choose (hsa.1 φ)) + I • Classical.choose (hsa.1 φ)) := by rw [smul_add]
        _ = c • φ := by rw [h.2]

    have unique : ∀ ψ₁ ψ₂, ψ₁ ∈ gen.domain → ψ₂ ∈ gen.domain →
                  gen.op ψ₁ + I • ψ₁ = c • φ → gen.op ψ₂ + I • ψ₂ = c • φ → ψ₁ = ψ₂ := by
      intro ψ₁ ψ₂ hψ₁ hψ₂ heq₁ heq₂
      have h_diff : gen.op ψ₁ + I • ψ₁ - (gen.op ψ₂ + I • ψ₂) = 0 := by
        rw [heq₁, heq₂]; simp
      have h_sub_domain : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem hψ₁ hψ₂
      have h_factor : gen.op (ψ₁ - ψ₂) + I • (ψ₁ - ψ₂) = 0 := by
        have op_sub := gen.op.map_sub ψ₁ ψ₂
        calc gen.op (ψ₁ - ψ₂) + I • (ψ₁ - ψ₂)
            = (gen.op ψ₁ - gen.op ψ₂) + I • (ψ₁ - ψ₂) := by rw [op_sub]
          _ = (gen.op ψ₁ - gen.op ψ₂) + (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
          _ = (gen.op ψ₁ + I • ψ₁) - (gen.op ψ₂ + I • ψ₂) := by abel
          _ = 0 := h_diff
      have h_eigen : gen.op (ψ₁ - ψ₂) = -I • (ψ₁ - ψ₂) := by
        calc gen.op (ψ₁ - ψ₂)
            = -(I • (ψ₁ - ψ₂)) := add_eq_zero_iff_eq_neg.mp h_factor
          _ = -I • (ψ₁ - ψ₂) := (neg_smul I (ψ₁ - ψ₂)).symm
      have h_inner : ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ = (starRingEnd ℂ) (-I) * ‖ψ₁ - ψ₂‖ ^ 2 := by
        rw [h_eigen, inner_smul_left, inner_self_eq_norm_sq_to_K]; rfl
      have h_inner' : ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ = I * ‖ψ₁ - ψ₂‖ ^ 2 := by
        rw [h_inner]; simp
      have h_sym : ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ = ⟪ψ₁ - ψ₂, gen.op (ψ₁ - ψ₂)⟫_ℂ := by
        exact gen.symmetric (ψ₁ - ψ₂) (ψ₁ - ψ₂) h_sub_domain h_sub_domain
      have h_real : (⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ).im = 0 := by
        have eq_conj : ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ = (starRingEnd ℂ) ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ := by
          calc ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ
              = ⟪ψ₁ - ψ₂, gen.op (ψ₁ - ψ₂)⟫_ℂ := h_sym
            _ = (starRingEnd ℂ) ⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ :=
                (inner_conj_symm (𝕜 := ℂ) (ψ₁ - ψ₂) (gen.op (ψ₁ - ψ₂))).symm
        have h_parts := Complex.ext_iff.mp eq_conj
        simp only [Complex.conj_im] at h_parts
        linarith [h_parts.2]
      have h_imag : (⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ).im = ‖ψ₁ - ψ₂‖ ^ 2 := by
        rw [h_inner', mul_comm, Complex.mul_im]
        simp only [Complex.I_re, Complex.I_im, mul_zero]
        norm_cast; ring_nf
      have : ‖ψ₁ - ψ₂‖ ^ 2 = 0 := by
        calc ‖ψ₁ - ψ₂‖ ^ 2 = (⟪gen.op (ψ₁ - ψ₂), ψ₁ - ψ₂⟫_ℂ).im := h_imag.symm
          _ = 0 := h_real
      have : ‖ψ₁ - ψ₂‖ = 0 := sq_eq_zero_iff.mp this
      exact sub_eq_zero.mp (norm_eq_zero.mp this)

    exact (unique _ _ h_smul_domain h_scaled.1 h_smul_eq h_scaled.2).symm

  cont := by
    have lip : LipschitzWith 1 (fun φ => Classical.choose (hsa.1 φ)) := by
      intro φ₁ φ₂
      let ψ₁ := Classical.choose (hsa.1 φ₁)
      let ψ₂ := Classical.choose (hsa.1 φ₂)
      have h₁ := Classical.choose_spec (hsa.1 φ₁)
      have h₂ := Classical.choose_spec (hsa.1 φ₂)

      have h_diff : gen.op (ψ₁ - ψ₂) + I • (ψ₁ - ψ₂) = φ₁ - φ₂ := by
        calc gen.op (ψ₁ - ψ₂) + I • (ψ₁ - ψ₂)
            = (gen.op ψ₁ - gen.op ψ₂) + I • (ψ₁ - ψ₂) := by rw [gen.op.map_sub]
          _ = (gen.op ψ₁ - gen.op ψ₂) + (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
          _ = (gen.op ψ₁ + I • ψ₁) - (gen.op ψ₂ + I • ψ₂) := by abel
          _ = φ₁ - φ₂ := by rw [h₁.2, h₂.2]

      have bound : ‖ψ₁ - ψ₂‖ ≤ ‖φ₁ - φ₂‖ := by
        let Δψ := ψ₁ - ψ₂
        have key_expand : ‖gen.op Δψ + I • Δψ‖ ^ 2 = ‖gen.op Δψ‖ ^ 2 + ‖Δψ‖ ^ 2 := by
          have h_sub_domain : Δψ ∈ gen.domain := gen.domain.sub_mem h₁.1 h₂.1

          have expand : ‖gen.op Δψ + I • Δψ‖ ^ 2 =
                        ‖gen.op Δψ‖ ^ 2 + ‖I • Δψ‖ ^ 2 + 2 * (⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by
            have h_inner : (⟪gen.op Δψ + I • Δψ, gen.op Δψ + I • Δψ⟫_ℂ).re = ‖gen.op Δψ + I • Δψ‖ ^ 2 := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op Δψ + I • Δψ)
              have h_re_both : (⟪gen.op Δψ + I • Δψ, gen.op Δψ + I • Δψ⟫_ℂ).re = ((‖gen.op Δψ + I • Δψ‖ ^ 2 : ℂ)).re := by
                rw [this]
                rfl
              have h_re : ((‖gen.op Δψ + I • Δψ‖ ^ 2 : ℂ)).re = ‖gen.op Δψ + I • Δψ‖ ^ 2 := by norm_cast
              rw [h_re_both, h_re]
            rw [← h_inner]
            rw [inner_add_left, inner_add_right, inner_add_right]
            have h1 : ‖gen.op Δψ‖ ^ 2 = (⟪gen.op Δψ, gen.op Δψ⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op Δψ)
              calc ‖gen.op Δψ‖ ^ 2
                  = ((‖gen.op Δψ‖ ^ 2 : ℂ)).re := by norm_cast
                _ = (⟪gen.op Δψ, gen.op Δψ⟫_ℂ).re := by
                    have h_re := congr_arg Complex.re this
                    simp only at h_re
                    exact h_re.symm
            have h2 : ‖I • Δψ‖ ^ 2 = (⟪I • Δψ, I • Δψ⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (I • Δψ)
              calc ‖I • Δψ‖ ^ 2
                  = ((‖I • Δψ‖ ^ 2 : ℂ)).re := by norm_cast
                _ = (⟪I • Δψ, I • Δψ⟫_ℂ).re := by
                    have h_re := congr_arg Complex.re this
                    simp only at h_re
                    exact h_re.symm
            simp only [Complex.add_re]
            rw [← h1, ← h2]
            have h_cross : (⟪gen.op Δψ, I • Δψ⟫_ℂ).re + (⟪I • Δψ, gen.op Δψ⟫_ℂ).re =
                           2 * (⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by
              have := inner_conj_symm (𝕜 := ℂ) (gen.op Δψ) (I • Δψ)
              have h_eq : (⟪I • Δψ, gen.op Δψ⟫_ℂ).re = (⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by
                calc (⟪I • Δψ, gen.op Δψ⟫_ℂ).re
                    = ((starRingEnd ℂ) ⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by norm_num
                  _ = (⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by simp only [Complex.conj_re]
              rw [h_eq]; ring
            rw [h_cross.symm]; ring

          have norm_I_smul : ‖I • Δψ‖ = ‖Δψ‖ := by rw [norm_smul]; simp

          have cross_zero : (⟪gen.op Δψ, I • Δψ⟫_ℂ).re = 0 := by
            rw [inner_smul_right]
            have h1 : I * ⟪gen.op Δψ, Δψ⟫_ℂ = I * (⟪gen.op Δψ, Δψ⟫_ℂ).re +
                      I * Complex.I * (⟪gen.op Δψ, Δψ⟫_ℂ).im := by
              conv_lhs => rw [← Complex.re_add_im (⟪gen.op Δψ, Δψ⟫_ℂ)]
              ring_nf
            have h_real : (⟪gen.op Δψ, Δψ⟫_ℂ).im = 0 := by
              have h_sym := gen.symmetric Δψ Δψ h_sub_domain h_sub_domain
              have h_conj : ⟪gen.op Δψ, Δψ⟫_ℂ = (starRingEnd ℂ) ⟪gen.op Δψ, Δψ⟫_ℂ := by
                calc ⟪gen.op Δψ, Δψ⟫_ℂ
                    = ⟪Δψ, gen.op Δψ⟫_ℂ := h_sym
                  _ = (starRingEnd ℂ) ⟪gen.op Δψ, Δψ⟫_ℂ := (inner_conj_symm (𝕜 := ℂ) Δψ (gen.op Δψ)).symm
              have h_parts := Complex.ext_iff.mp h_conj
              simp only [Complex.conj_im] at h_parts
              linarith [h_parts.2]
            rw [h1, h_real]; simp

          rw [expand, norm_I_smul, cross_zero]; ring

        have le_sq : ‖Δψ‖ ^ 2 ≤ ‖gen.op Δψ + I • Δψ‖ ^ 2 := by
          rw [key_expand]; have : 0 ≤ ‖gen.op Δψ‖ ^ 2 := sq_nonneg _; linarith

        have le_norm : ‖Δψ‖ ≤ ‖gen.op Δψ + I • Δψ‖ := by
          by_contra h_not
          push_neg at h_not
          -- If ‖gen.op Δψ + I • Δψ‖ < ‖Δψ‖, square both sides
          have h_sq_lt : ‖gen.op Δψ + I • Δψ‖ ^ 2 < ‖Δψ‖ ^ 2 := by
            have h1 : 0 ≤ ‖gen.op Δψ + I • Δψ‖ := norm_nonneg _
            have h2 : 0 ≤ ‖Δψ‖ := norm_nonneg _
            nlinarith [sq_nonneg (‖Δψ‖ - ‖gen.op Δψ + I • Δψ‖), h_not, h1, h2]
          linarith

        calc ‖ψ₁ - ψ₂‖ = ‖Δψ‖ := rfl
          _ ≤ ‖gen.op Δψ + I • Δψ‖ := le_norm
          _ = ‖φ₁ - φ₂‖ := by rw [h_diff]

      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
      simp only [ENNReal.coe_one, one_mul]
      exact ENNReal.ofReal_le_ofReal bound

    exact lip.continuous

/--
The resolvent operator R_i = (A - iI)⁻¹ is bounded with norm ≤ 1.

**Mathematical Content:**
For a self-adjoint generator A, the resolvent at i satisfies the uniform bound:
  ∀ φ ∈ H: ‖R_i(φ)‖ ≤ ‖φ‖

This proves ‖R_i‖ ≤ 1 as a bounded operator on H.

**Proof Strategy:**
The key identity for any ψ in the domain of A is:
  ‖(A - iI)ψ‖² = ‖Aψ‖² + ‖ψ‖²

This follows from expanding the norm and using that the cross term vanishes:
  Re⟨Aψ, iψ⟩ = Re(i·⟨Aψ, ψ⟩) = 0

since ⟨Aψ, ψ⟩ ∈ ℝ by symmetry of A.

From the identity: ‖(A - iI)ψ‖² ≥ ‖ψ‖², so ‖(A - iI)ψ‖ ≥ ‖ψ‖.

For φ = (A - iI)ψ, we have ψ = R_i(φ), giving:
  ‖R_i(φ)‖ = ‖ψ‖ ≤ ‖(A - iI)ψ‖ = ‖φ‖

**Why This Matters:**
- The bound ‖R_i‖ ≤ 1 is sharp (equality holds for certain states)
- This is a special case of the general bound ‖R_z‖ ≤ 1/|Im(z)|
- The bounded resolvent is THE defining characteristic separating self-adjoint
  from merely symmetric operators
- Essential for proving the spectral theorem via functional calculus

**Physical Interpretation:**
In quantum mechanics with Hamiltonian H, the resolvent (E - H)⁻¹ represents
the system's response to energy probes. The bound says probing at complex
energy i produces a bounded response - no resonances at non-real energies.

**Comparison with R_{-i}:**
The conjugate resolvent `resolvent_at_neg_i` inverts (A + iI) and satisfies
the identical bound ‖R_{-i}‖ ≤ 1 by the same argument (using -i instead of i).
-/
lemma resolvent_at_i_bound {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : IsSelfAdjoint gen) :
    ‖resolvent_at_i gen hsa‖ ≤ 1 := by
  -- Prove: for all φ, ‖R_i(φ)‖ ≤ ‖φ‖
  have h_bound : ∀ φ : H, ‖resolvent_at_i gen hsa φ‖ ≤ ‖φ‖ := by
    intro φ
    set ψ := resolvent_at_i gen hsa φ
    have h_spec := resolvent_at_i_spec gen hsa φ
    have h_eq : gen.op ψ - I • ψ = φ := h_spec.2

    -- Key: ‖(A - iI)ψ‖² = ‖Aψ‖² + ‖ψ‖²
    let Δψ := ψ
    have key_expand : ‖gen.op Δψ - I • Δψ‖ ^ 2 = ‖gen.op Δψ‖ ^ 2 + ‖Δψ‖ ^ 2 := by
      have h_domain : Δψ ∈ gen.domain := h_spec.1
      have expand : ‖gen.op Δψ - I • Δψ‖ ^ 2 =
          ‖gen.op Δψ‖ ^ 2 + ‖I • Δψ‖ ^ 2 - 2 * (⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by
        have h_inner : (⟪gen.op Δψ - I • Δψ, gen.op Δψ - I • Δψ⟫_ℂ).re =
            ‖gen.op Δψ - I • Δψ‖ ^ 2 := by
          have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op Δψ - I • Δψ)
          have h_re_both : (⟪gen.op Δψ - I • Δψ, gen.op Δψ - I • Δψ⟫_ℂ).re =
              ((‖gen.op Δψ - I • Δψ‖ ^ 2 : ℂ)).re := by rw [this]; rfl
          have h_re : ((‖gen.op Δψ - I • Δψ‖ ^ 2 : ℂ)).re = ‖gen.op Δψ - I • Δψ‖ ^ 2 := by
            norm_cast
          rw [h_re_both, h_re]
        rw [← h_inner, inner_sub_left, inner_sub_right, inner_sub_right]
        simp only [Complex.sub_re]
        have h2 : ‖gen.op Δψ‖ ^ 2 = (⟪gen.op Δψ, gen.op Δψ⟫_ℂ).re := by
          have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op Δψ)
          rw [this]; norm_cast
        have h3 : ‖I • Δψ‖ ^ 2 = (⟪I • Δψ, I • Δψ⟫_ℂ).re := by
          have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (I • Δψ)
          rw [this]; norm_cast
        rw [h2, h3]
        have h_cross : (⟪gen.op Δψ, I • Δψ⟫_ℂ).re + (⟪I • Δψ, gen.op Δψ⟫_ℂ).re =
                      2 * (⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by
          have h_eq : (⟪I • Δψ, gen.op Δψ⟫_ℂ).re = (⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by
            calc (⟪I • Δψ, gen.op Δψ⟫_ℂ).re
                = ((starRingEnd ℂ) ⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by norm_num
              _ = (⟪gen.op Δψ, I • Δψ⟫_ℂ).re := by simp only [Complex.conj_re]
          rw [h_eq]; ring
        rw [h_cross.symm]; ring
      have norm_I_smul : ‖I • Δψ‖ = ‖Δψ‖ := by rw [norm_smul]; simp
      have cross_zero : (⟪gen.op Δψ, I • Δψ⟫_ℂ).re = 0 := by
        rw [inner_smul_right]
        have h1 : I * ⟪gen.op Δψ, Δψ⟫_ℂ = I * (⟪gen.op Δψ, Δψ⟫_ℂ).re +
                  I * Complex.I * (⟪gen.op Δψ, Δψ⟫_ℂ).im := by
          conv_lhs => rw [← Complex.re_add_im (⟪gen.op Δψ, Δψ⟫_ℂ)]
          ring_nf
        have h_real : (⟪gen.op Δψ, Δψ⟫_ℂ).im = 0 := by
          have h_sym := gen.symmetric Δψ Δψ h_domain h_domain
          have h_conj : ⟪gen.op Δψ, Δψ⟫_ℂ = (starRingEnd ℂ) ⟪gen.op Δψ, Δψ⟫_ℂ := by
            calc ⟪gen.op Δψ, Δψ⟫_ℂ
                = ⟪Δψ, gen.op Δψ⟫_ℂ := gen.symmetric Δψ Δψ h_domain h_domain
              _ = (starRingEnd ℂ) ⟪gen.op Δψ, Δψ⟫_ℂ :=
                  (inner_conj_symm (𝕜 := ℂ) Δψ (gen.op Δψ)).symm
          have := Complex.ext_iff.mp h_conj
          simp only [Complex.conj_im] at this
          linarith [this.2]
        rw [h1, h_real]; simp
      rw [expand, norm_I_smul, cross_zero]; ring

    have le_sq : ‖Δψ‖ ^ 2 ≤ ‖gen.op Δψ - I • Δψ‖ ^ 2 := by
      rw [key_expand]; have : 0 ≤ ‖gen.op Δψ‖ ^ 2 := sq_nonneg _; linarith

    have le_norm : ‖Δψ‖ ≤ ‖gen.op Δψ - I • Δψ‖ := by
      by_contra h_not; push_neg at h_not
      have : ‖gen.op Δψ - I • Δψ‖ ^ 2 < ‖Δψ‖ ^ 2 := by
        have h1 : 0 ≤ ‖gen.op Δψ - I • Δψ‖ := norm_nonneg _
        have h2 : 0 ≤ ‖Δψ‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖Δψ‖ - ‖gen.op Δψ - I • Δψ‖)]
      linarith

    calc ‖ψ‖ = ‖Δψ‖ := rfl
      _ ≤ ‖gen.op Δψ - I • Δψ‖ := le_norm
      _ = ‖φ‖ := by rw [h_eq]

  -- Now use this to bound the operator norm
  apply ContinuousLinearMap.opNorm_le_bound
  · norm_num
  · intro φ
    calc ‖resolvent_at_i gen hsa φ‖
        ≤ ‖φ‖ := h_bound φ
      _ = 1 * ‖φ‖ := by ring


/--
Lower bound estimate for (A - zI) when Im(z) ≠ 0.

**The Foundation of Everything:**
For any z ∈ ℂ with Im(z) ≠ 0 and any ψ in the domain of A, we have:
  ‖(A - zI)ψ‖ ≥ |Im(z)| · ‖ψ‖

**Why This Matters:**
1. Proves (A - zI) is injective for all z ∉ ℝ
2. Shows Range(A - zI) is closed (bounded below)
3. Gives explicit bound on resolvent: ‖R_z‖ ≤ 1/|Im(z)|
4. Distinguishes self-adjoint from symmetric operators

**Proof Strategy:**
Write z = x + iy where x = Re(z), y = Im(z) ≠ 0. Then:
  (A - zI)ψ = (A - xI)ψ - iy·ψ

Expand the norm squared using the key identity:
  ‖(A - xI)ψ - iy·ψ‖² = ‖(A - xI)ψ‖² + |y|²‖ψ‖² + 2Re⟨(A-xI)ψ, -iy·ψ⟩

The cross term vanishes because:
- Re⟨(A-xI)ψ, -iy·ψ⟩ = -Im(y)·Re⟨(A-xI)ψ, ψ⟩
- But ⟨(A-xI)ψ, ψ⟩ ∈ ℝ (A-xI is symmetric)
- So the cross term is purely imaginary times real = has zero real part

Therefore: ‖(A - zI)ψ‖² ≥ |y|²‖ψ‖²

**Physical Interpretation:**
In quantum mechanics, this says you can't have resonances exactly on the real energy axis
for self-adjoint Hamiltonians. The imaginary part provides a "gap" that prevents collapse
onto the spectrum.
-/
lemma lower_bound_estimate {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (z : ℂ) (_ /-hz-/ : z.im ≠ 0)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ‖gen.op ψ - z • ψ‖ ≥ |z.im| * ‖ψ‖ := by
  -- Decompose z = x + iy
  set x := z.re
  set y := z.im

  -- Rewrite (A - zI)ψ = (A - xI)ψ - iy·ψ
  have h_decomp : gen.op ψ - z • ψ = (gen.op ψ - x • ψ) - (y * I) • ψ := by
    have hz_eq : z = x + y * I := by
      simp [x, y]
    calc gen.op ψ - z • ψ
        = gen.op ψ - (x + y * I) • ψ := by rw [hz_eq]
      _ = gen.op ψ - (x • ψ + (y * I) • ψ) := by rw [add_smul];rfl
      _ = (gen.op ψ - x • ψ) - (y * I) • ψ := by abel

  rw [h_decomp]

  -- Expand ‖(A - xI)ψ - iy·ψ‖²
  have h_expand : ‖(gen.op ψ - x • ψ) - (y * I) • ψ‖^2 =
                ‖gen.op ψ - x • ψ‖^2 + ‖(y * I) • ψ‖^2 +
                2 * (⟪gen.op ψ - x • ψ, -((y * I) • ψ)⟫_ℂ).re := by
  -- Direct expansion using ‖a - b‖² formula
    have h_formula : ∀ (a b : H), ‖a - b‖^2 = ‖a‖^2 + ‖b‖^2 - 2 * (⟪a, b⟫_ℂ).re := by
      intro a b
      have h_inner : (⟪a - b, a - b⟫_ℂ).re = ‖a - b‖ ^ 2 := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (a - b)
        calc (⟪a - b, a - b⟫_ℂ).re
            = ((‖a - b‖ ^ 2 : ℂ)).re := by
                have h_re := congr_arg Complex.re this
                simp only at h_re
                exact h_re
          _ = ‖a - b‖ ^ 2 := by norm_cast
      rw [← h_inner, inner_sub_left, inner_sub_right, inner_sub_right]
      simp only [Complex.sub_re]
      have h1 : (⟪a, a⟫_ℂ).re = ‖a‖^2 := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) a
        calc (⟪a, a⟫_ℂ).re
            = ((‖a‖ ^ 2 : ℂ)).re := by
                have h_re := congr_arg Complex.re this
                simp only at h_re
                exact h_re
          _ = ‖a‖^2 := by norm_cast
      have h2 : (⟪b, b⟫_ℂ).re = ‖b‖^2 := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) b
        calc (⟪b, b⟫_ℂ).re
            = ((‖b‖ ^ 2 : ℂ)).re := by
                have h_re := congr_arg Complex.re this
                simp only at h_re
                exact h_re
          _ = ‖b‖^2 := by norm_cast
      rw [h1, h2]
      have h_cross : (⟪a, b⟫_ℂ).re + (⟪b, a⟫_ℂ).re = 2 * (⟪a, b⟫_ℂ).re := by
        have := inner_conj_symm (𝕜 := ℂ) a b
        have : (⟪b, a⟫_ℂ).re = (⟪a, b⟫_ℂ).re := by
          calc (⟪b, a⟫_ℂ).re
              = ((starRingEnd ℂ) ⟪a, b⟫_ℂ).re := by norm_num
            _ = (⟪a, b⟫_ℂ).re := by simp only [Complex.conj_re]
        rw [this]; ring
      rw [h_cross.symm]; ring

    -- Apply to our specific case
    calc ‖(gen.op ψ - x • ψ) - (y * I) • ψ‖^2
        = ‖gen.op ψ - x • ψ‖^2 + ‖(y * I) • ψ‖^2 - 2 * (⟪gen.op ψ - x • ψ, (y * I) • ψ⟫_ℂ).re :=
            h_formula (gen.op ψ - x • ψ) ((y * I) • ψ)
      _ = ‖gen.op ψ - x • ψ‖^2 + ‖(y * I) • ψ‖^2 + 2 * (⟪gen.op ψ - x • ψ, -((y * I) • ψ)⟫_ℂ).re := by
          have : (⟪gen.op ψ - x • ψ, -((y * I) • ψ)⟫_ℂ).re = -(⟪gen.op ψ - x • ψ, (y * I) • ψ⟫_ℂ).re := by
            rw [inner_neg_right]; simp only [Complex.neg_re]
          rw [this]; ring

  -- The norm of iy·ψ
  have h_norm_scale : ‖(y * I) • ψ‖ = |y| * ‖ψ‖ := by
    calc ‖(y * I) • ψ‖
        = ‖(y * I : ℂ)‖ * ‖ψ‖ := norm_smul _ _
      _ = |y| * ‖ψ‖ := by simp

  -- The cross term vanishes
  have h_cross_zero : (⟪gen.op ψ - x • ψ, -((y * I) • ψ)⟫_ℂ).re = 0 := by
    rw [inner_neg_right, inner_smul_right]
    -- Now we have: (-(y * I * ⟪gen.op ψ - x • ψ, ψ⟫_ℂ)).re = 0

    -- First show ⟨(A-xI)ψ, ψ⟩ is real
    have h_real : (⟪gen.op ψ - x • ψ, ψ⟫_ℂ).im = 0 := by
      rw [inner_sub_left]
      have h_Areal : (⟪gen.op ψ, ψ⟫_ℂ).im = 0 := by
        have h_sym := gen.symmetric ψ ψ hψ hψ
        have h_conj : ⟪gen.op ψ, ψ⟫_ℂ = (starRingEnd ℂ) ⟪gen.op ψ, ψ⟫_ℂ := by
          calc ⟪gen.op ψ, ψ⟫_ℂ
              = ⟪ψ, gen.op ψ⟫_ℂ := h_sym
            _ = (starRingEnd ℂ) ⟪gen.op ψ, ψ⟫_ℂ :=
                (inner_conj_symm (𝕜 := ℂ) ψ (gen.op ψ)).symm
        have h_parts := Complex.ext_iff.mp h_conj
        simp only [Complex.conj_im] at h_parts
        linarith [h_parts.2]

      have h_xreal : (⟪x • ψ, ψ⟫_ℂ).im = 0 := by
        -- x is real, so x • ψ = (x : ℂ) • ψ
        have : (x : ℂ) • ψ = x • ψ := rfl
        rw [← this, inner_smul_left]
        -- Now: ((x : ℂ) * ⟨ψ, ψ⟩).im = 0
        have h_inner_real : (⟪ψ, ψ⟫_ℂ).im = 0 := by
          have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
          rw [this]
          norm_cast
        simp [h_inner_real]

      simp [h_Areal, h_xreal]

    -- So ⟨(A-xI)ψ, ψ⟩ is real, write it as its real part
    have h_as_real : ⟪gen.op ψ - x • ψ, ψ⟫_ℂ = ((⟪gen.op ψ - x • ψ, ψ⟫_ℂ).re : ℂ) := by
      conv_lhs => rw [← Complex.re_add_im (⟪gen.op ψ - x • ψ, ψ⟫_ℂ), h_real]
      simp

    rw [h_as_real]
    -- Now: Re(-(y*I)·r) where r ∈ ℝ
    simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im,
              Complex.ofReal_re, Complex.ofReal_im]
    ring_nf

    rw [h_as_real]
    -- Now: Re(-(y*i)·r) where r ∈ ℝ
    simp only [Complex.ofReal_re]
    abel_nf; simp



  -- Now: ‖(A-zI)ψ‖² = ‖(A-xI)ψ‖² + |y|²‖ψ‖² ≥ |y|²‖ψ‖²
  have h_ge : ‖gen.op ψ - x • ψ‖^2 + (|y| * ‖ψ‖)^2 ≥ (|y| * ‖ψ‖)^2 := by
    have : 0 ≤ ‖gen.op ψ - x • ψ‖^2 := sq_nonneg _
    linarith

  -- Now prove the squared inequality first
  have h_sq : ‖(gen.op ψ - x • ψ) - (y * I) • ψ‖^2 ≥ (|y| * ‖ψ‖)^2 := by
    rw [h_expand, h_norm_scale, h_cross_zero]
    simp only [mul_zero, add_zero]
    -- Now: ‖(A-xI)ψ‖² + |y|²‖ψ‖² ≥ |y|²‖ψ‖²
    have : 0 ≤ ‖gen.op ψ - x • ψ‖^2 := sq_nonneg _
    linarith

  -- Take square root to get the final result
  by_contra h_not
  push_neg at h_not
  have h1 : 0 ≤ ‖(gen.op ψ - x • ψ) - (y * I) • ψ‖ := norm_nonneg _
  have h2 : 0 ≤ |y| * ‖ψ‖ := by
    apply mul_nonneg
    · exact abs_nonneg _
    · exact norm_nonneg _
  nlinarith [sq_nonneg (|y| * ‖ψ‖ - ‖(gen.op ψ - x • ψ) - (y * I) • ψ‖), h_sq, h_not, h1, h2]


/-!
### Neumann Series Machinery

For a bounded linear operator T with ‖T‖ < 1, the series Σₙ Tⁿ converges
to (I - T)⁻¹. This is the operator-theoretic analogue of 1/(1-x) = Σ xⁿ.
-/

section NeumannSeries

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/--
Powers of operators satisfy ‖Tⁿ‖ ≤ ‖T‖ⁿ.

This is the submultiplicativity of operator norm applied inductively.
-/
lemma opNorm_pow_le (T : E →L[ℂ] E) (n : ℕ) : ‖T^n‖ ≤ ‖T‖^n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    calc ‖T^(n+1)‖
        = ‖T^n * T‖ := by rw [pow_succ]
      _ ≤ ‖T^n‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖T‖^n * ‖T‖ := by
          apply mul_le_mul_of_nonneg_right ih (norm_nonneg _)
      _ = ‖T‖^(n+1) := by rw [pow_succ]

/--
When ‖T‖ < 1, the powers Tⁿ converge to zero in operator norm.

Proof: ‖Tⁿ‖ ≤ ‖T‖ⁿ → 0 since ‖T‖ < 1.
-/
lemma opNorm_pow_tendsto_zero (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    Tendsto (fun n => ‖T^n‖) atTop (𝓝 0) := by
  have h_geom : Tendsto (fun n => ‖T‖^n) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    rw [norm_norm]
    exact hT
  have h_bound : ∀ n, ‖T^n‖ ≤ ‖T‖^n := fun n => opNorm_pow_le T n
  have h_nonneg : ∀ n, 0 ≤ ‖T^n‖ := fun n => norm_nonneg _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_geom h_nonneg h_bound

/--
Partial sums of the Neumann series: Sₙ = I + T + T² + ... + T^(n-1)
-/
noncomputable def neumannPartialSum (T : E →L[ℂ] E) (n : ℕ) : E →L[ℂ] E :=
  Finset.sum (Finset.range n) (fun k => T^k)

/--
Telescoping identity: (I - T) * Sₙ = I - Tⁿ

This is the key algebraic identity for Neumann series.
-/
lemma neumannPartialSum_mul (T : E →L[ℂ] E) (n : ℕ) :
    (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n =
    ContinuousLinearMap.id ℂ E - T^n := by
  induction n with
  | zero =>
    simp only [neumannPartialSum, Finset.range_zero, Finset.sum_empty, pow_zero]
    simp only [mul_zero]
    ext x : 1
    simp_all only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
    Pi.sub_apply, id_eq, ContinuousLinearMap.one_apply, sub_self]
  | succ n ih =>
    simp only [neumannPartialSum] at ih ⊢
    rw [Finset.sum_range_succ]
    rw [mul_add]
    rw [ih]
    -- Goal: I - T^n + (I - T) * T^n = I - T^(n+1)
    have h_id_eq : ContinuousLinearMap.id ℂ E = (1 : E →L[ℂ] E) := rfl
    rw [h_id_eq]
    rw [sub_mul, one_mul]
    rw [← pow_succ']
    -- Goal: 1 - T^n + (T^n - T^(n+1)) = 1 - T^(n+1)
    abel

/--
When ‖T‖ < 1, the Neumann partial sums form a Cauchy sequence in operator norm.
-/
lemma neumannPartialSum_cauchy (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    CauchySeq (neumannPartialSum T) := by
  apply cauchySeq_of_summable_dist
  -- Need: Summable (fun n => dist (S_n) (S_{n+1}))
  -- dist(S_n, S_{n+1}) = ‖T^n‖ ≤ ‖T‖^n
  have h_bound : ∀ n, dist (neumannPartialSum T n) (neumannPartialSum T (n + 1)) ≤ ‖T‖^n := by
    intro n
    simp only [neumannPartialSum, dist_eq_norm, Finset.sum_range_succ]
    rw [← norm_neg, neg_sub, add_sub_cancel_left]
    exact opNorm_pow_le T n
  apply Summable.of_nonneg_of_le
  · intro n; exact dist_nonneg
  · exact h_bound
  · exact summable_geometric_of_lt_one (norm_nonneg _) hT

/--
The Neumann series: limit of partial sums when ‖T‖ < 1.
-/
noncomputable def neumannSeries (T : E →L[ℂ] E) (_ /-hT-/ : ‖T‖ < 1) : E →L[ℂ] E :=
  limUnder atTop (neumannPartialSum T)

/--
The Neumann series satisfies (I - T) * S = I.
-/
lemma neumannSeries_mul_left (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    (ContinuousLinearMap.id ℂ E - T) * neumannSeries T hT = ContinuousLinearMap.id ℂ E := by
  -- neumannSeries is the limit of partial sums
  have h_lim : Tendsto (neumannPartialSum T) atTop (𝓝 (neumannSeries T hT)) := by
    exact (neumannPartialSum_cauchy T hT).tendsto_limUnder

  -- (I - T) * Sₙ → (I - T) * S by continuity of multiplication
  have h_mul_lim : Tendsto (fun n => (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n)
      atTop (𝓝 ((ContinuousLinearMap.id ℂ E - T) * neumannSeries T hT)) := by
    exact Tendsto.const_mul (ContinuousLinearMap.id ℂ E - T) h_lim

  -- But (I - T) * Sₙ = I - Tⁿ by telescoping
  have h_eq : ∀ n, (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n =
      ContinuousLinearMap.id ℂ E - T^n := neumannPartialSum_mul T

  -- And Tⁿ → 0
  have h_pow_lim : Tendsto (fun n => T^n) atTop (𝓝 0) := by
    have h := opNorm_pow_tendsto_zero T hT
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h

  -- So I - Tⁿ → I - 0 = I
  have h_sub_lim : Tendsto (fun n => ContinuousLinearMap.id ℂ E - T^n) atTop
      (𝓝 (ContinuousLinearMap.id ℂ E - 0)) := by
    exact Tendsto.const_sub (ContinuousLinearMap.id ℂ E) h_pow_lim

  simp only [sub_zero] at h_sub_lim

  -- Combine: (I - T) * S = lim (I - T) * Sₙ = lim (I - Tⁿ) = I
  have h_eq_lim : Tendsto (fun n => (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n)
      atTop (𝓝 (ContinuousLinearMap.id ℂ E)) := by
    simp only [h_eq]
    exact h_sub_lim

  exact tendsto_nhds_unique h_mul_lim h_eq_lim

/--
The Neumann series satisfies S * (I - T) = I.
-/
lemma neumannSeries_mul_right (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    neumannSeries T hT * (ContinuousLinearMap.id ℂ E - T) = ContinuousLinearMap.id ℂ E := by
  -- First prove the telescoping identity for right multiplication
  have h_telescope : ∀ n, neumannPartialSum T n * (ContinuousLinearMap.id ℂ E - T) =
      ContinuousLinearMap.id ℂ E - T^n := by
    intro n
    induction n with
    | zero =>
      simp only [neumannPartialSum, Finset.range_zero, Finset.sum_empty, pow_zero]
      simp only [zero_mul]
      ext x : 1
      simp_all only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
    Pi.sub_apply, id_eq, ContinuousLinearMap.one_apply, sub_self]
    | succ n ih =>
      simp only [neumannPartialSum] at ih ⊢
      rw [Finset.sum_range_succ]
      rw [add_mul]
      rw [ih]
      have h_id_eq : ContinuousLinearMap.id ℂ E = (1 : E →L[ℂ] E) := rfl
      rw [h_id_eq]
      rw [mul_sub, mul_one]
      rw [← pow_succ]
      abel

  -- neumannSeries is the limit of partial sums
  have h_lim : Tendsto (neumannPartialSum T) atTop (𝓝 (neumannSeries T hT)) :=
    (neumannPartialSum_cauchy T hT).tendsto_limUnder

  -- Sₙ * (I - T) → S * (I - T) by continuity
  have h_mul_lim : Tendsto (fun n => neumannPartialSum T n * (ContinuousLinearMap.id ℂ E - T))
      atTop (𝓝 (neumannSeries T hT * (ContinuousLinearMap.id ℂ E - T))) := by
    exact Tendsto.mul_const (ContinuousLinearMap.id ℂ E - T) h_lim

  -- Tⁿ → 0
  have h_pow_lim : Tendsto (fun n => T^n) atTop (𝓝 0) := by
    have h := opNorm_pow_tendsto_zero T hT
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h

  -- I - Tⁿ → I
  have h_sub_lim : Tendsto (fun n => ContinuousLinearMap.id ℂ E - T^n) atTop
      (𝓝 (ContinuousLinearMap.id ℂ E)) := by
    have := Tendsto.const_sub (ContinuousLinearMap.id ℂ E) h_pow_lim
    simp only [sub_zero] at this
    exact this

  -- Combine
  have h_eq_lim : Tendsto (fun n => neumannPartialSum T n * (ContinuousLinearMap.id ℂ E - T))
      atTop (𝓝 (ContinuousLinearMap.id ℂ E)) := by
    simp only [h_telescope]
    exact h_sub_lim

  exact tendsto_nhds_unique h_mul_lim h_eq_lim

/--
When ‖T‖ < 1, the operator (I - T) is invertible with inverse given by the Neumann series.
-/
lemma isUnit_one_sub (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    IsUnit (ContinuousLinearMap.id ℂ E - T) := by
  refine ⟨⟨ContinuousLinearMap.id ℂ E - T, neumannSeries T hT, ?_, ?_⟩, rfl⟩
  · exact neumannSeries_mul_left T hT
  · exact neumannSeries_mul_right T hT



/-- For z near i, we can construct R_z from R_i via Neumann series -/
lemma resolvent_near_i {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im > 0) (h_close : ‖z - I‖ < 1) :
    ∀ φ : H, ∃! (ψ : {x : H // x ∈ gen.domain}),
      gen.op ψ.val - z • ψ.val = φ := by
  intro φ

  -- Setup
  let R := resolvent_at_i gen hsa
  let lambda_val := z - I

  -- Key bound: ‖λ·R‖ < 1, enabling Neumann series
  have h_op_bound : ‖lambda_val • R‖ < 1 := by
    calc ‖lambda_val • R‖
        = ‖lambda_val‖ * ‖R‖ := norm_smul lambda_val R
      _ ≤ ‖lambda_val‖ * 1 := by
          apply mul_le_mul_of_nonneg_left
          · exact resolvent_at_i_bound gen hsa
          · exact norm_nonneg _
      _ = ‖z - I‖ := by ring
      _ < 1 := h_close

  -- Part 1: Existence via Neumann series
  have h_exists : ∃ (ψ : {x : H // x ∈ gen.domain}),
      gen.op ψ.val - z • ψ.val = φ := by
    -- Strategy: (A - zI) = (A - iI) - (z - i)I
    -- So for ψ in domain: (A - zI)ψ = (A - iI)ψ - (z - i)ψ
    -- Rearranging: (A - zI)ψ = φ iff (A - iI)ψ = φ + (z - i)ψ
    -- iff ψ = R_i(φ + (z - i)ψ) = R_i(φ) + (z - i)R_i(ψ)
    -- iff (I - (z - i)R_i)ψ = R_i(φ)
    -- iff ψ = [I - (z - i)R_i]^{-1} R_i(φ)

    -- The Neumann series gives [I - (z-i)R_i]^{-1}
    let T := lambda_val • R
    let S := neumannSeries T h_op_bound

    -- Candidate solution: ψ₀ = S(R(φ))
    let ψ₀ := S (R φ)

    -- Need to show ψ₀ ∈ domain
    -- R(φ) ∈ domain by definition of resolvent_at_i
    have h_Rφ_spec := resolvent_at_i_spec gen hsa φ
    have h_Rφ_domain : R φ ∈ gen.domain := h_Rφ_spec.1

    -- The tricky part: S(R(φ)) may not be in domain!
    -- We need a different approach: solve (I - (z-i)R_i)η = φ first,
    -- then ψ = R_i(η) is in domain

    let η := S φ
    let ψ := R η

    have h_ψ_spec := resolvent_at_i_spec gen hsa η
    have h_ψ_domain : ψ ∈ gen.domain := h_ψ_spec.1

    use ⟨ψ, h_ψ_domain⟩

    -- Need: (A - zI)ψ = φ
    -- We have: (A - iI)ψ = η (from resolvent definition)
    -- And: (I - (z-i)R)η = φ (from Neumann series)

    have h_resolvent_eq : gen.op ψ - I • ψ = η := h_ψ_spec.2

    -- (I - T)S = I, so (I - T)(Sφ) = φ, i.e., η - T(η) = φ
    have h_neumann_eq : η - T η = φ := by
      have h_inv := neumannSeries_mul_left T h_op_bound
      calc η - T η
          = (ContinuousLinearMap.id ℂ H - T) η := by simp [T]
        _ = ((ContinuousLinearMap.id ℂ H - T) * S) φ := by simp [η, S]
        _ = ContinuousLinearMap.id ℂ H φ := by rw [h_inv]
        _ = φ := rfl

    -- Now compute (A - zI)ψ
    calc gen.op ψ - z • ψ
        = gen.op ψ - (I + lambda_val) • ψ := by simp [lambda_val]
      _ = gen.op ψ - I • ψ - lambda_val • ψ := by rw [add_smul]; abel
      _ = η - lambda_val • ψ := by rw [h_resolvent_eq]
      _ = η - lambda_val • (R η) := rfl
      _ = η - (lambda_val • R) η := by rfl
      _ = η - T η := rfl
      _ = φ := h_neumann_eq

  -- Part 2: Uniqueness (via lower_bound_estimate at z)
  obtain ⟨ψ, hψ⟩ := h_exists
  use ψ, hψ
  intro ψ' hψ'

  -- Show ψ = ψ' by showing their difference is zero
  have h_diff : gen.op (ψ.val - ψ'.val) - z • (ψ.val - ψ'.val) = 0 := by
    calc gen.op (ψ.val - ψ'.val) - z • (ψ.val - ψ'.val)
        = (gen.op ψ.val - gen.op ψ'.val) - z • (ψ.val - ψ'.val) := by
            rw [gen.op.map_sub]
      _ = (gen.op ψ.val - gen.op ψ'.val) - (z • ψ.val - z • ψ'.val) := by
            rw [smul_sub]
      _ = (gen.op ψ.val - z • ψ.val) - (gen.op ψ'.val - z • ψ'.val) := by abel
      _ = φ - φ := by rw [hψ, hψ']
      _ = 0 := sub_self φ

  -- Apply lower_bound_estimate: since Im(z) > 0, we have ‖(A-zI)(ψ-ψ')‖ ≥ |Im(z)|·‖ψ-ψ'‖
  have h_im_ne : z.im ≠ 0 := ne_of_gt hz

  have h_sub_domain : ψ.val - ψ'.val ∈ gen.domain :=
    gen.domain.sub_mem ψ.property ψ'.property

  have h_bound := lower_bound_estimate gen z h_im_ne (ψ.val - ψ'.val) h_sub_domain

  -- From h_diff: LHS = 0, so |Im(z)|·‖ψ-ψ'‖ ≤ 0
  rw [h_diff] at h_bound
  simp only [norm_zero, ge_iff_le] at h_bound

  -- Since |Im(z)| > 0, we get ‖ψ-ψ'‖ = 0
  have h_im_pos : 0 < |z.im| := abs_pos.mpr h_im_ne

  have h_norm_zero : ‖ψ.val - ψ'.val‖ = 0 := by
    by_contra h_ne
    have h_pos : 0 < ‖ψ.val - ψ'.val‖ := by
      cases' (norm_nonneg (ψ.val - ψ'.val)).lt_or_eq with h h
      · exact h
      · exact absurd h.symm h_ne
    have : 0 < |z.im| * ‖ψ.val - ψ'.val‖ := mul_pos h_im_pos h_pos
    linarith

  -- Therefore ψ = ψ'
  have h_eq : ψ.val = ψ'.val := sub_eq_zero.mp (norm_eq_zero.mp h_norm_zero)
  ext
  exact h_eq.symm



/--
The resolvent exists for all z with Im(z) ≠ 0.

**The Big Theorem:** For self-adjoint A and any z ∉ ℝ, the equation
  (A - zI)ψ = φ
has a unique solution ψ ∈ domain(A) for every φ ∈ H.

**Proof Strategy (Three Parts):**

1. **Injectivity:** From `lower_bound_estimate`:
   If (A - zI)ψ = 0, then 0 = ‖(A - zI)ψ‖ ≥ |Im(z)|‖ψ‖
   Since |Im(z)| > 0, we get ‖ψ‖ = 0, so ψ = 0.

2. **Closed Range:** Also from `lower_bound_estimate`:
   If (A - zI)ψₙ is Cauchy, then ψₙ is Cauchy because
   ‖ψₙ - ψₘ‖ ≤ (1/|Im(z)|)‖(A - zI)(ψₙ - ψₘ)‖

3. **Dense Range (The Hard Part):**
   Suppose φ ⊥ Range(A - zI). Then for all ψ ∈ domain(A):
   - 0 = ⟨(A - zI)ψ, φ⟩ = ⟨Aψ, φ⟩ - z⟨ψ, φ⟩
   - By symmetry of A: ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩
   - So: ⟨ψ, Aφ⟩ = z⟨ψ, φ⟩
   - But also: ⟨Aψ, φ⟩ = z⟨ψ, φ⟩
   - By symmetry again: ⟨ψ, Aφ⟩ = ⟨Aψ, φ⟩ = z⟨ψ, φ⟩
   - Taking conjugate: ⟨Aφ, ψ⟩ = z̄⟨φ, ψ⟩ = z̄⟨ψ, φ⟩
   - But ⟨Aφ, ψ⟩ = ⟨ψ, Aφ⟩ = z⟨ψ, φ⟩
   - Therefore: z⟨ψ, φ⟩ = z̄⟨ψ, φ⟩
   - Since z ≠ z̄ (as Im(z) ≠ 0), we get ⟨ψ, φ⟩ = 0 for all ψ ∈ domain
   - Since domain is dense, φ = 0!

**Why This Matters:**
This is the fundamental theorem distinguishing self-adjoint from merely symmetric
operators. Only self-adjoint operators have invertible resolvents off ℝ.

**Physical Meaning:**
Complex energies don't exist for quantum systems with self-adjoint Hamiltonians.
The resolvent (E - H)⁻¹ exists for all non-real E, proving energy must be real.
-/
theorem self_adjoint_range_all_z
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im ≠ 0) :
    ∀ φ : H, ∃! (ψ : {x : H // x ∈ gen.domain}),
      gen.op ψ.val - z • ψ.val = φ := by
  intro φ

  -- Part 1: Existence via density argument
  -- Key lemma: orthogonal complement of Range(A - zI) is {0}
  have h_ker_zero : ∀ (χ : H),
      (∀ (ψ : {x : H // x ∈ gen.domain}), ⟪gen.op ψ.val - z • ψ.val, χ⟫_ℂ = 0) → χ = 0 := by
    intro χ h_orth

    -- From orthogonality: ⟪Aψ, χ⟫ = z̄·⟪ψ, χ⟫ for all ψ ∈ domain
    have h_eigen_cond : ∀ (ψ : H), ψ ∈ gen.domain → ⟪gen.op ψ, χ⟫_ℂ = (starRingEnd ℂ z) * ⟪ψ, χ⟫_ℂ := by
      intro ψ hψ
      have h := h_orth ⟨ψ, hψ⟩
      simp only at h
      calc ⟪gen.op ψ, χ⟫_ℂ
          = ⟪gen.op ψ - z • ψ + z • ψ, χ⟫_ℂ := by simp
        _ = ⟪gen.op ψ - z • ψ, χ⟫_ℂ + ⟪z • ψ, χ⟫_ℂ := by rw [inner_add_left]
        _ = 0 + ⟪z • ψ, χ⟫_ℂ := by rw [h]
        _ = (starRingEnd ℂ z) * ⟪ψ, χ⟫_ℂ := by rw [inner_smul_left]; ring

    -- Use IsSelfAdjoint: find η with (A - iI)η = (z̄ - i)•χ
    set z_bar := (starRingEnd ℂ) z with hz_bar_def

    -- (A - iI) is surjective, so find η ∈ domain with (A - iI)η = (z̄ - i)•χ
    obtain ⟨η, hη_dom, hη_eq⟩ := hsa.2 ((z_bar - I) • χ)
    -- hη_eq : gen.op η - I • η = (z̄ - i) • χ

    -- (A + iI) is surjective, so find ξ ∈ domain with (A + iI)ξ = (z̄ + i)•χ
    obtain ⟨ξ, hξ_dom, hξ_eq⟩ := hsa.1 ((z_bar + I) • χ)
    -- hξ_eq : gen.op ξ + I • ξ = (z̄ + i) • χ

    -- Key calculation 1: Compute ⟪χ, η⟫ using η's equation and eigen condition
    -- From hη_eq: Aη = (z̄ - i)•χ + i•η
    have h_Aη : gen.op η = (z_bar - I) • χ + I • η := by
      calc gen.op η
          = (gen.op η - I • η) + I • η := by simp
        _ = (z_bar - I) • χ + I • η := by rw [hη_eq]

    -- Apply eigen condition to η
    have h_eigen_η : ⟪gen.op η, χ⟫_ℂ = z_bar * ⟪η, χ⟫_ℂ := h_eigen_cond η hη_dom

    -- Compute ⟪Aη, χ⟫ directly from h_Aη
    have h_inner_Aη : ⟪gen.op η, χ⟫_ℂ = (starRingEnd ℂ (z_bar - I)) * ‖χ‖^2 + (starRingEnd ℂ I) * ⟪η, χ⟫_ℂ := by
      calc ⟪gen.op η, χ⟫_ℂ
          = ⟪(z_bar - I) • χ + I • η, χ⟫_ℂ := by rw [h_Aη]
        _ = ⟪(z_bar - I) • χ, χ⟫_ℂ + ⟪I • η, χ⟫_ℂ := by rw [inner_add_left]
        _ = (starRingEnd ℂ (z_bar - I)) * ⟪χ, χ⟫_ℂ + (starRingEnd ℂ I) * ⟪η, χ⟫_ℂ := by
            rw [inner_smul_left, inner_smul_left]
        _ = (starRingEnd ℂ (z_bar - I)) * ‖χ‖^2 + (starRingEnd ℂ I) * ⟪η, χ⟫_ℂ := by
            rw [inner_self_eq_norm_sq_to_K]
            simp

    -- Combining the two expressions for ⟪Aη, χ⟫:
    -- z̄ * ⟪η, χ⟫ = conj(z̄ - i) * ‖χ‖² + conj(i) * ⟪η, χ⟫
    -- z̄ * ⟪η, χ⟫ = (z - (-i)) * ‖χ‖² + (-i) * ⟪η, χ⟫
    -- z̄ * ⟪η, χ⟫ = (z + i) * ‖χ‖² - i * ⟪η, χ⟫
    -- (z̄ + i) * ⟪η, χ⟫ = (z + i) * ‖χ‖²

    have h_conj_zbar_minus_I : (starRingEnd ℂ) (z_bar - I) = z + I := by
      simp [hz_bar_def]

    have h_conj_I : (starRingEnd ℂ) I = -I := Complex.conj_I

    have h_relation_η : (z_bar + I) * ⟪η, χ⟫_ℂ = (z + I) * ‖χ‖^2 := by
      have h1 := h_eigen_η
      have h2 := h_inner_Aη
      rw [h_conj_zbar_minus_I, h_conj_I] at h2
      -- h1: z̄ * ⟪η, χ⟫ = ⟪Aη, χ⟫
      -- h2: ⟪Aη, χ⟫ = (z + I) * ‖χ‖² + (-I) * ⟪η, χ⟫
      calc (z_bar + I) * ⟪η, χ⟫_ℂ
          = z_bar * ⟪η, χ⟫_ℂ + I * ⟪η, χ⟫_ℂ := by ring
        _ = ⟪gen.op η, χ⟫_ℂ + I * ⟪η, χ⟫_ℂ := by rw [h1]
        _ = ((z + I) * ‖χ‖^2 + (-I) * ⟪η, χ⟫_ℂ) + I * ⟪η, χ⟫_ℂ := by rw [h2]
        _ = (z + I) * ‖χ‖^2 := by ring

    -- Key calculation 2: Similar for ξ
    have h_Aξ : gen.op ξ = (z_bar + I) • χ - I • ξ := by
      calc gen.op ξ
          = (gen.op ξ + I • ξ) - I • ξ := by simp
        _ = (z_bar + I) • χ - I • ξ := by rw [hξ_eq]

    have h_eigen_ξ : ⟪gen.op ξ, χ⟫_ℂ = z_bar * ⟪ξ, χ⟫_ℂ := h_eigen_cond ξ hξ_dom

    have h_inner_Aξ : ⟪gen.op ξ, χ⟫_ℂ = (starRingEnd ℂ (z_bar + I)) * ‖χ‖^2 - (starRingEnd ℂ I) * ⟪ξ, χ⟫_ℂ := by
      calc ⟪gen.op ξ, χ⟫_ℂ
          = ⟪(z_bar + I) • χ - I • ξ, χ⟫_ℂ := by rw [h_Aξ]
        _ = ⟪(z_bar + I) • χ, χ⟫_ℂ - ⟪I • ξ, χ⟫_ℂ := by rw [inner_sub_left]
        _ = (starRingEnd ℂ (z_bar + I)) * ⟪χ, χ⟫_ℂ - (starRingEnd ℂ I) * ⟪ξ, χ⟫_ℂ := by
            rw [inner_smul_left, inner_smul_left]
        _ = (starRingEnd ℂ (z_bar + I)) * ‖χ‖^2 - (starRingEnd ℂ I) * ⟪ξ, χ⟫_ℂ := by
            rw [inner_self_eq_norm_sq_to_K]
            simp

    have h_conj_zbar_plus_I : (starRingEnd ℂ) (z_bar + I) = z - I := by
      simp [hz_bar_def]
      ring

    have h_relation_ξ : (z_bar - I) * ⟪ξ, χ⟫_ℂ = (z - I) * ‖χ‖^2 := by
      have h1 := h_eigen_ξ
      have h2 := h_inner_Aξ
      rw [h_conj_zbar_plus_I, h_conj_I] at h2
      calc (z_bar - I) * ⟪ξ, χ⟫_ℂ
          = z_bar * ⟪ξ, χ⟫_ℂ - I * ⟪ξ, χ⟫_ℂ := by ring
        _ = ⟪gen.op ξ, χ⟫_ℂ - I * ⟪ξ, χ⟫_ℂ := by rw [h1]
        _ = ((z - I) * ‖χ‖^2 - (-I) * ⟪ξ, χ⟫_ℂ) - I * ⟪ξ, χ⟫_ℂ := by rw [h2]
        _ = (z - I) * ‖χ‖^2 := by ring

    -- Key calculation 3: Use symmetry of A on η and ξ
    -- ⟪Aη, ξ⟫ = ⟪η, Aξ⟫
    have h_sym : ⟪gen.op η, ξ⟫_ℂ = ⟪η, gen.op ξ⟫_ℂ := gen.symmetric η ξ hη_dom hξ_dom

    -- LHS: ⟪Aη, ξ⟫ = ⟪(z̄-i)χ + iη, ξ⟫ = (z-(-i))⟪χ,ξ⟫ + (-i)⟪η,ξ⟫ = (z+i)⟪χ,ξ⟫ - i⟪η,ξ⟫
    have h_LHS : ⟪gen.op η, ξ⟫_ℂ = (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by
      calc ⟪gen.op η, ξ⟫_ℂ
          = ⟪(z_bar - I) • χ + I • η, ξ⟫_ℂ := by rw [h_Aη]
        _ = ⟪(z_bar - I) • χ, ξ⟫_ℂ + ⟪I • η, ξ⟫_ℂ := by rw [inner_add_left]
        _ = (starRingEnd ℂ (z_bar - I)) * ⟪χ, ξ⟫_ℂ + (starRingEnd ℂ I) * ⟪η, ξ⟫_ℂ := by
            rw [inner_smul_left, inner_smul_left]
        _ = (z + I) * ⟪χ, ξ⟫_ℂ + (-I) * ⟪η, ξ⟫_ℂ := by rw [h_conj_zbar_minus_I, h_conj_I]
        _ = (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by ring

    -- RHS: ⟪η, Aξ⟫ = ⟪η, (z̄+i)χ - iξ⟫ = (z̄+i)⟪η,χ⟫ - i⟪η,ξ⟫
    have h_RHS : ⟪η, gen.op ξ⟫_ℂ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by
      calc ⟪η, gen.op ξ⟫_ℂ
          = ⟪η, (z_bar + I) • χ - I • ξ⟫_ℂ := by rw [h_Aξ]
        _ = ⟪η, (z_bar + I) • χ⟫_ℂ - ⟪η, I • ξ⟫_ℂ := by rw [inner_sub_right]
        _ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by rw [inner_smul_right, inner_smul_right]

    -- From symmetry: (z + i)⟪χ,ξ⟫ - i⟪η,ξ⟫ = (z̄ + i)⟪η,χ⟫ - i⟪η,ξ⟫
    -- Therefore: (z + i)⟪χ,ξ⟫ = (z̄ + i)⟪η,χ⟫
    have h_cancel : (z + I) * ⟪χ, ξ⟫_ℂ = (z_bar + I) * ⟪η, χ⟫_ℂ := by
      have : (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by
        rw [← h_LHS, ← h_RHS, h_sym]
      -- find alternative to this tactic.
      simp_all +arith

    -- From h_relation_η: (z̄ + i)⟪η, χ⟫ = (z + i)‖χ‖²
    -- So: (z + i)⟪χ,ξ⟫ = (z + i)‖χ‖²
    have h_chi_xi_eq : (z + I) * ⟪χ, ξ⟫_ℂ = (z + I) * ‖χ‖^2 := by
      calc (z + I) * ⟪χ, ξ⟫_ℂ
          = (z_bar + I) * ⟪η, χ⟫_ℂ := h_cancel
        _ = (z + I) * ‖χ‖^2 := h_relation_η

    -- Now we show χ = 0 by considering cases on z + i ≠ 0
    -- Since Im(z) ≠ 0, we have z ≠ -i, so z + i ≠ 0
    --have h_z_plus_i_ne : z + I ≠ 0 := by
    -- We need to show χ = 0. Split cases on whether z = -I.
    by_cases h_z_eq_neg_I : z = -I
    · -- Case z = -I: use h_relation_ξ directly
      -- z_bar = conj(-I) = I, so z_bar - I = 0, and z - I = -2I
      have h_zbar_eq : z_bar = I := by
        simp only [hz_bar_def, h_z_eq_neg_I, map_neg, Complex.conj_I]
        ring
      have h_zbar_minus_I : z_bar - I = 0 := by rw [h_zbar_eq]; ring
      have h_z_minus_I : z - I = -2 * I := by rw [h_z_eq_neg_I]; ring
      -- Substitute into h_relation_ξ: 0 * ⟪ξ, χ⟫ = (-2I) * ‖χ‖²
      rw [h_zbar_minus_I, h_z_minus_I] at h_relation_ξ
      simp only [zero_mul] at h_relation_ξ
      -- So 0 = -2I * ‖χ‖², and -2I ≠ 0
      have h_two_I_ne : (-2 : ℂ) * I ≠ 0 := by
        simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero]
        subst h_z_eq_neg_I
        simp_all only [conj_I, map_neg, neg_neg, sub_self, neg_mul, neg_smul, zero_eq_neg, mul_eq_zero, OfNat.ofNat_ne_zero,
          I_ne_zero, or_self, ne_eq, not_false_eq_true, pow_eq_zero_iff, ofReal_eq_zero, norm_eq_zero, false_or, neg_im, I_im,
          neg_eq_zero, one_ne_zero, sub_neg_eq_add, inner_zero_right, implies_true, mul_zero, smul_zero, zero_add, zero_sub,
          neg_add_cancel, map_zero, norm_zero, ofReal_zero, zero_pow, add_zero, map_add, inner_zero_left, inner_neg_right,
          neg_inj, z_bar]
      have h_norm_sq_zero : (‖χ‖^2 : ℂ) = 0 := by
        have := mul_eq_zero.mp h_relation_ξ.symm
        cases this with
        | inl h => exact absurd h h_two_I_ne
        | inr h => exact h
      have h_norm_zero : ‖χ‖ = 0 := by
        have h : (‖χ‖ : ℂ) = 0 := sq_eq_zero_iff.mp h_norm_sq_zero
        exact Complex.ofReal_eq_zero.mp h
      exact norm_eq_zero.mp h_norm_zero

    · -- Case z ≠ -I, so z + I ≠ 0
      have h_z_plus_i_ne : z + I ≠ 0 := by
        intro h_eq
        apply h_z_eq_neg_I
        calc z = z + I - I := by ring
          _ = 0 - I := by rw [h_eq]
          _ = -I := by ring

      -- Now proceed with the original argument...


      -- From h_chi_xi_eq and z + I ≠ 0: ⟪χ, ξ⟫ = ‖χ‖²
      have h_inner_chi_xi : ⟪χ, ξ⟫_ℂ = ‖χ‖^2 := by
        have := mul_left_cancel₀ h_z_plus_i_ne h_chi_xi_eq
        calc ⟪χ, ξ⟫_ℂ = (‖χ‖^2 : ℂ) := this
          _ = ‖χ‖^2 := by norm_cast

      -- Also get ⟪ξ, χ⟫ = ‖χ‖² via conjugate symmetry
      have h_inner_xi_chi : ⟪ξ, χ⟫_ℂ = ‖χ‖^2 := by
        have h1 : ⟪ξ, χ⟫_ℂ = (starRingEnd ℂ) ⟪χ, ξ⟫_ℂ := (inner_conj_symm ξ χ).symm
        rw [h_inner_chi_xi] at h1
        simp at h1
        exact h1

      -- Substitute into h_relation_ξ
      have h_final : (z_bar - I) * (‖χ‖^2 : ℂ) = (z - I) * ‖χ‖^2 := by
        calc (z_bar - I) * (‖χ‖^2 : ℂ)
            = (z_bar - I) * ⟪ξ, χ⟫_ℂ := by rw [← h_inner_xi_chi]
          _ = (z - I) * ↑‖χ‖^2 := h_relation_ξ

      -- So (z̄ - z) * ‖χ‖² = 0
      have h_diff_zero : (z_bar - z) * (‖χ‖^2 : ℂ) = 0 := by
        have : (z_bar - I) * (‖χ‖^2 : ℂ) - (z - I) * ‖χ‖^2 = 0 := by
          rw [h_final]; ring
        calc (z_bar - z) * (‖χ‖^2 : ℂ)
            = (z_bar - I - (z - I)) * ‖χ‖^2 := by ring
          _ = (z_bar - I) * ‖χ‖^2 - (z - I) * ‖χ‖^2 := by ring
          _ = 0 := this

      -- Now z̄ - z = -2i * Im(z) ≠ 0 since Im(z) ≠ 0
      have h_zbar_minus_z_ne : z_bar - z ≠ 0 := by
        intro h_eq
        have h_zbar_eq_z : z_bar = z := sub_eq_zero.mp h_eq
        have h_im_zero : z.im = 0 := by
          have h1 : ((starRingEnd ℂ) z).im = z.im := by
            rw [hz_bar_def] at h_zbar_eq_z
            exact congrArg Complex.im h_zbar_eq_z
          simp only [Complex.conj_im] at h1
          -- h1 : -z.im = z.im, so z.im = 0
          linarith
        exact hz h_im_zero

      -- Therefore ‖χ‖² = 0
      have h_norm_sq_zero : (‖χ‖^2 : ℂ) = 0 := by
        have := mul_eq_zero.mp h_diff_zero
        cases this with
        | inl h => exact absurd h h_zbar_minus_z_ne
        | inr h => exact h

      -- So χ = 0
      have h_norm_zero : ‖χ‖ = 0 := by
        have h : (‖χ‖ : ℂ) = 0 := sq_eq_zero_iff.mp h_norm_sq_zero
        exact Complex.ofReal_eq_zero.mp h

      exact norm_eq_zero.mp h_norm_zero

  -- Part 2: Use density to show existence
  -- Range(A - zI)⊥ = {0} implies Range(A - zI) is dense
  -- Combined with closedness (from lower_bound_estimate) gives Range = H

  have h_range_closed : IsClosed (Set.range (fun (ψ : {x : H // x ∈ gen.domain}) =>
                                            gen.op ψ.val - z • ψ.val)) := by
    rw [← isSeqClosed_iff_isClosed]
    intro u φ hu_range hφ_lim
  -- Now we have:
  -- u : ℕ → H
  -- hu_range : ∀ n, u n ∈ Set.range ...
  -- hφ_lim : Tendsto u atTop (𝓝 φ)
  -- Goal: φ ∈ Set.range ...
    have hu_cauchy : CauchySeq u := hφ_lim.cauchySeq
    choose ψ_seq hψ_seq using fun n => Set.mem_range.mp (hu_range n)

    have hψ_cauchy : CauchySeq (fun n => (ψ_seq n).val) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have hε_scaled : 0 < |z.im| * ε := mul_pos (abs_pos.mpr hz) hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu_cauchy (|z.im| * ε) hε_scaled
      use N
      intro m hm n hn
      have h_sub_domain : (ψ_seq m).val - (ψ_seq n).val ∈ gen.domain :=
        gen.domain.sub_mem (ψ_seq m).property (ψ_seq n).property
      have h_bound := lower_bound_estimate gen z hz
        ((ψ_seq m).val - (ψ_seq n).val) h_sub_domain
      have h_diff : gen.op ((ψ_seq m).val - (ψ_seq n).val) -
                    z • ((ψ_seq m).val - (ψ_seq n).val) = u m - u n := by
        calc gen.op ((ψ_seq m).val - (ψ_seq n).val) - z • ((ψ_seq m).val - (ψ_seq n).val)
            = (gen.op (ψ_seq m).val - gen.op (ψ_seq n).val) -
              z • ((ψ_seq m).val - (ψ_seq n).val) := by rw [gen.op.map_sub]
          _ = (gen.op (ψ_seq m).val - gen.op (ψ_seq n).val) -
              (z • (ψ_seq m).val - z • (ψ_seq n).val) := by rw [smul_sub]
          _ = (gen.op (ψ_seq m).val - z • (ψ_seq m).val) -
              (gen.op (ψ_seq n).val - z • (ψ_seq n).val) := by abel
          _ = u m - u n := by rw [hψ_seq m, hψ_seq n]
      rw [h_diff] at h_bound
      have h_ubound : dist (u m) (u n) < |z.im| * ε := hN m hm n hn
      rw [dist_eq_norm] at h_ubound
      have h_chain : |z.im| * ‖(ψ_seq m).val - (ψ_seq n).val‖ < |z.im| * ε := by
        calc |z.im| * ‖(ψ_seq m).val - (ψ_seq n).val‖
            ≤ ‖u m - u n‖ := h_bound
          _ < |z.im| * ε := h_ubound
      have h_pos : 0 < |z.im| := abs_pos.mpr hz
      rw [dist_eq_norm]
      exact (mul_lt_mul_left h_pos).mp h_chain

    -- ψ_seq converges to some limit ψ_lim
    obtain ⟨ψ_lim, hψ_lim⟩ := cauchySeq_tendsto_of_complete hψ_cauchy

    -- The hard part: showing ψ_lim ∈ domain
    -- This requires that generators are closed operators (graph closed)
    -- Standard result but needs additional infrastructure
    -- Show ψ_lim ∈ domain using the resolvent at i
    -- Key: R_i is bounded and R_i((A - iI)ψ) = ψ for ψ ∈ domain

    let R := resolvent_at_i gen hsa

    -- (A - iI)ψ_n = (A - zI)ψ_n + (z - i)ψ_n = u_n + (z - i)ψ_n
    have h_AiI : ∀ n, gen.op (ψ_seq n).val - I • (ψ_seq n).val =
                      u n + (z - I) • (ψ_seq n).val := by
      intro n
      have h := hψ_seq n  -- (A - zI)ψ_n = u_n
      calc gen.op (ψ_seq n).val - I • (ψ_seq n).val
          = (gen.op (ψ_seq n).val - z • (ψ_seq n).val) + (z - I) • (ψ_seq n).val := by
              rw [sub_smul]; abel
        _ = u n + (z - I) • (ψ_seq n).val := by rw [h]

    -- The sequence (A - iI)ψ_n converges to φ + (z - i)·ψ_lim
    have h_AiI_lim : Tendsto (fun n => gen.op (ψ_seq n).val - I • (ψ_seq n).val)
                            atTop (𝓝 (φ + (z - I) • ψ_lim)) := by
      have h1 : Tendsto u atTop (𝓝 φ) := hφ_lim
      have h2 : Tendsto (fun n => (z - I) • (ψ_seq n).val) atTop (𝓝 ((z - I) • ψ_lim)) := by
        exact Tendsto.const_smul hψ_lim (z - I)
      have h3 : Tendsto (fun n => u n + (z - I) • (ψ_seq n).val) atTop
                        (𝓝 (φ + (z - I) • ψ_lim)) := Tendsto.add h1 h2
      convert h3 using 1
      ext n
      exact h_AiI n

    -- R_i((A - iI)ψ) = ψ for any ψ ∈ domain
    have h_R_inverse : ∀ (ψ : H) (hψ : ψ ∈ gen.domain),
                        R (gen.op ψ - I • ψ) = ψ := by
      intro ψ hψ
      -- R_i(η) is the unique element satisfying (A - iI)(R_i η) = η
      -- We have (A - iI)ψ = gen.op ψ - I • ψ, and ψ ∈ domain
      -- So ψ is a solution to (A - iI)x = (gen.op ψ - I • ψ)
      -- By uniqueness, R_i(gen.op ψ - I • ψ) = ψ
      let η := gen.op ψ - I • ψ
      have h_Rη_spec := resolvent_at_i_spec gen hsa η
      -- h_Rη_spec.1 : R η ∈ domain
      -- h_Rη_spec.2 : (A - iI)(R η) = η
      apply resolvent_at_i_unique gen hsa η (R η) ψ h_Rη_spec.1 hψ h_Rη_spec.2
      rfl  -- (A - iI)ψ = η by definition of η

    -- By continuity: R_i((A - iI)ψ_n) → R_i(φ + (z - i)·ψ_lim)
    have h_R_lim : Tendsto (fun n => R (gen.op (ψ_seq n).val - I • (ψ_seq n).val))
                          atTop (𝓝 (R (φ + (z - I) • ψ_lim))) := by
      exact R.continuous.tendsto _ |>.comp h_AiI_lim

    -- But R_i((A - iI)ψ_n) = ψ_n
    have h_R_eq : ∀ n, R (gen.op (ψ_seq n).val - I • (ψ_seq n).val) = (ψ_seq n).val := by
      intro n
      exact h_R_inverse (ψ_seq n).val (ψ_seq n).property

    -- So ψ_n → R_i(φ + (z - i)·ψ_lim)
    have h_ψ_lim_alt : Tendsto (fun n => (ψ_seq n).val) atTop (𝓝 (R (φ + (z - I) • ψ_lim))) := by
      convert h_R_lim using 1
      ext n
      exact (h_R_eq n).symm

    -- By uniqueness of limits: ψ_lim = R_i(φ + (z - i)·ψ_lim)
    have h_ψ_lim_eq : ψ_lim = R (φ + (z - I) • ψ_lim) := by
      exact tendsto_nhds_unique hψ_lim h_ψ_lim_alt

    -- Since R_i maps into domain, ψ_lim ∈ domain
    have h_ψ_lim_domain : ψ_lim ∈ gen.domain := by
      rw [h_ψ_lim_eq]
      exact (resolvent_at_i_spec gen hsa (φ + (z - I) • ψ_lim)).1

    -- Now show (A - zI)ψ_lim = φ
    have h_eq : gen.op ψ_lim - z • ψ_lim = φ := by
      -- We have (A - zI)ψ_n → φ and ψ_n → ψ_lim
      -- Need continuity of A on domain in graph topology, or use the limit directly
      -- Since (A - iI)ψ_lim = φ + (z - i)·ψ_lim (from R_i inversion)
      have h_AiI_ψ_lim : gen.op ψ_lim - I • ψ_lim = φ + (z - I) • ψ_lim := by
        have h_spec := resolvent_at_i_spec gen hsa (φ + (z - I) • ψ_lim)
        conv_lhs => rw [h_ψ_lim_eq]
        exact h_spec.2
      calc gen.op ψ_lim - z • ψ_lim
          = (gen.op ψ_lim - I • ψ_lim) - (z - I) • ψ_lim := by rw [sub_smul]; abel
        _ = (φ + (z - I) • ψ_lim) - (z - I) • ψ_lim := by rw [h_AiI_ψ_lim]
        _ = φ := by abel

    exact ⟨⟨ψ_lim, h_ψ_lim_domain⟩, h_eq⟩

  have h_dense : Dense (Set.range (fun (ψ : {x : H // x ∈ gen.domain}) =>
                                    gen.op ψ.val - z • ψ.val)) := by
    set S := Set.range (fun (ψ : {x : H // x ∈ gen.domain}) => gen.op ψ.val - z • ψ.val) with hS_def

    -- S is the carrier of a submodule M (range of a linear map is a subspace)
    let M : Submodule ℂ H := {
      carrier := S
      add_mem' := by
        intro a b ha hb
        obtain ⟨ψa, hψa⟩ := ha
        obtain ⟨ψb, hψb⟩ := hb
        refine ⟨⟨ψa.val + ψb.val, gen.domain.add_mem ψa.property ψb.property⟩, ?_⟩
        simp only [← hψa, ← hψb]
        rw [gen.op.map_add, smul_add]
        abel
      zero_mem' := ⟨⟨0, gen.domain.zero_mem⟩, by simp⟩
      smul_mem' := by
        intro c a ha
        obtain ⟨ψ, hψ⟩ := ha
        refine ⟨⟨c • ψ.val, gen.domain.smul_mem c ψ.property⟩, ?_⟩
        simp only [← hψ]
        rw [gen.op.map_smul, smul_sub, smul_comm z c]
    }

    have hM_eq : (M : Set H) = S := rfl

    -- Mᗮ = ⊥ because h_ker_zero says orthogonal complement is trivial
    have h_M_orth : Mᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro χ hχ
      apply h_ker_zero χ
      intro ψ
      have h_mem : gen.op ψ.val - z • ψ.val ∈ M := ⟨ψ, rfl⟩
      exact Submodule.inner_right_of_mem_orthogonal h_mem hχ

    -- Mᗮ = ⊥ implies M.topologicalClosure = ⊤
    have h_M_top : M.topologicalClosure = ⊤ := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure]
      rw [h_M_orth]
      exact Submodule.bot_orthogonal_eq_top

    -- M is dense in H
    have h_M_dense : Dense (M : Set H) := by
      rw [dense_iff_closure_eq]
      have h_coe : closure (M : Set H) = (M.topologicalClosure : Set H) :=
        (Submodule.topologicalClosure_coe M).symm
      rw [h_coe, h_M_top]
      rfl

    -- S = M as sets, so S is dense
    rw [← hM_eq]
    exact h_M_dense

  -- Combine: closed + dense = univ
  have h_eq_univ : Set.range (fun (ψ : {x : H // x ∈ gen.domain}) =>
                                gen.op ψ.val - z • ψ.val) = Set.univ := by
    have h_closure := h_dense.closure_eq
    rw [IsClosed.closure_eq h_range_closed] at h_closure
    exact h_closure

  -- Existence
  have h_exists : ∃ (ψ : {x : H // x ∈ gen.domain}), gen.op ψ.val - z • ψ.val = φ := by
    have : φ ∈ Set.univ := Set.mem_univ φ
    rw [← h_eq_univ] at this
    exact Set.mem_range.mp this

  -- Uniqueness (already proven via lower_bound_estimate)
  obtain ⟨ψ, hψ⟩ := h_exists
  use ψ, hψ
  intro ψ' hψ'
  have h_diff : gen.op (ψ.val - ψ'.val) - z • (ψ.val - ψ'.val) = 0 := by
    calc gen.op (ψ.val - ψ'.val) - z • (ψ.val - ψ'.val)
        = (gen.op ψ.val - gen.op ψ'.val) - z • (ψ.val - ψ'.val) := by rw [gen.op.map_sub]
      _ = (gen.op ψ.val - gen.op ψ'.val) - (z • ψ.val - z • ψ'.val) := by rw [smul_sub]
      _ = (gen.op ψ.val - z • ψ.val) - (gen.op ψ'.val - z • ψ'.val) := by abel
      _ = φ - φ := by rw [hψ, hψ']
      _ = 0 := sub_self φ
  have h_bound : ‖gen.op (ψ.val - ψ'.val) - z • (ψ.val - ψ'.val)‖ ≥
                  |z.im| * ‖ψ.val - ψ'.val‖ := by
    exact lower_bound_estimate gen z hz (ψ.val - ψ'.val)
      (gen.domain.sub_mem ψ.property ψ'.property)
  rw [h_diff] at h_bound
  simp at h_bound
  have h_im_pos : 0 < |z.im| := abs_pos.mpr hz
  have : ‖ψ.val - ψ'.val‖ = 0 := by
    by_contra h_ne
    have h_elem_ne : ψ.val - ψ'.val ≠ 0 := fun h_eq => h_ne (h_eq ▸ norm_zero)
    have h_norm_pos : 0 < ‖ψ.val - ψ'.val‖ := norm_pos_iff.mpr h_elem_ne
    have : 0 < |z.im| * ‖ψ.val - ψ'.val‖ := mul_pos h_im_pos h_norm_pos
    linarith
  ext
  exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm


/--
Resolvent operator (when it exists).

For self-adjoint generator A and Im(z) ≠ 0, this is well-defined and bounded.
-/
noncomputable def resolvent {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (z : ℂ)
    (hz : z.im ≠ 0) (hsa : IsSelfAdjoint gen) : H →L[ℂ] H :=
  { toFun := fun φ => (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ)).val

    map_add' := by
      intro φ₁ φ₂
      let ψ₁_sub := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁)
      let ψ₂_sub := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂)
      let ψ_sum_sub := Classical.choose (self_adjoint_range_all_z gen hsa z hz (φ₁ + φ₂))

      have h₁ := (Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ₁)).1
      have h₂ := (Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ₂)).1
      have h_sum_unique := (Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz (φ₁ + φ₂))).2

      -- ψ₁ + ψ₂ is in domain
      have h_add_domain : ψ₁_sub.val + ψ₂_sub.val ∈ gen.domain :=
        gen.domain.add_mem ψ₁_sub.property ψ₂_sub.property

      -- (A - zI)(ψ₁ + ψ₂) = φ₁ + φ₂
      have h_add_eq : gen.op (ψ₁_sub.val + ψ₂_sub.val) - z • (ψ₁_sub.val + ψ₂_sub.val) = φ₁ + φ₂ := by
        calc gen.op (ψ₁_sub.val + ψ₂_sub.val) - z • (ψ₁_sub.val + ψ₂_sub.val)
            = (gen.op ψ₁_sub.val + gen.op ψ₂_sub.val) - z • (ψ₁_sub.val + ψ₂_sub.val) := by
                rw [gen.op.map_add]
          _ = (gen.op ψ₁_sub.val + gen.op ψ₂_sub.val) - (z • ψ₁_sub.val + z • ψ₂_sub.val) := by
                rw [smul_add]
          _ = (gen.op ψ₁_sub.val - z • ψ₁_sub.val) + (gen.op ψ₂_sub.val - z • ψ₂_sub.val) := by abel
          _ = φ₁ + φ₂ := by rw [h₁, h₂]

      -- By uniqueness
      have h_eq : ψ_sum_sub = (⟨ψ₁_sub.val + ψ₂_sub.val, h_add_domain⟩ : {x : H // x ∈ gen.domain}) := by
        symm
        apply h_sum_unique
        simp only
        exact h_add_eq

      exact congrArg Subtype.val h_eq

    map_smul' := by
      intro c φ
      let ψ_sub := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ)
      let ψ_scaled_sub := Classical.choose (self_adjoint_range_all_z gen hsa z hz (c • φ))

      have h := (Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ)).1
      have h_scaled_unique := (Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz (c • φ))).2

      -- c • ψ is in domain
      have h_smul_domain : c • ψ_sub.val ∈ gen.domain :=
        gen.domain.smul_mem c ψ_sub.property

      -- (A - zI)(c • ψ) = c • φ
      have h_smul_eq : gen.op (c • ψ_sub.val) - z • (c • ψ_sub.val) = c • φ := by
        calc gen.op (c • ψ_sub.val) - z • (c • ψ_sub.val)
            = c • gen.op ψ_sub.val - z • (c • ψ_sub.val) := by
                rw [gen.op.map_smul]
          _ = c • gen.op ψ_sub.val - c • (z • ψ_sub.val) := by
                rw [smul_comm z c]
          _ = c • (gen.op ψ_sub.val - z • ψ_sub.val) := by
                rw [smul_sub]
          _ = c • φ := by rw [h]

      -- By uniqueness
      have h_eq : ψ_scaled_sub = (⟨c • ψ_sub.val, h_smul_domain⟩ : {x : H // x ∈ gen.domain}) := by
        symm
        apply h_scaled_unique
        simp only
        exact h_smul_eq

      exact congrArg Subtype.val h_eq

    cont := by
      -- Use the bound ‖R_z(φ)‖ ≤ (1/|Im(z)|) · ‖φ‖
      have h_lip : LipschitzWith ⟨1 / |z.im|, by positivity⟩
          (fun φ => (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ)).val) := by
        intro φ₁ φ₂
        let ψ₁ := (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁)).val
        let ψ₂ := (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂)).val

        have h₁ := (Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ₁)).1
        have h₂ := (Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ₂)).1
        have h₁_dom := (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁)).property
        have h₂_dom := (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂)).property

        -- (A - zI)(ψ₁ - ψ₂) = φ₁ - φ₂
        have h_diff : gen.op (ψ₁ - ψ₂) - z • (ψ₁ - ψ₂) = φ₁ - φ₂ := by
          calc gen.op (ψ₁ - ψ₂) - z • (ψ₁ - ψ₂)
              = (gen.op ψ₁ - gen.op ψ₂) - z • (ψ₁ - ψ₂) := by rw [gen.op.map_sub]
            _ = (gen.op ψ₁ - gen.op ψ₂) - (z • ψ₁ - z • ψ₂) := by rw [smul_sub]
            _ = (gen.op ψ₁ - z • ψ₁) - (gen.op ψ₂ - z • ψ₂) := by abel
            _ = φ₁ - φ₂ := by rw [h₁, h₂]

        have h_sub_domain : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem h₁_dom h₂_dom

        -- Apply lower_bound_estimate
        have h_bound := lower_bound_estimate gen z hz (ψ₁ - ψ₂) h_sub_domain
        rw [h_diff] at h_bound

        -- |Im(z)| · ‖ψ₁ - ψ₂‖ ≤ ‖φ₁ - φ₂‖
        have h_im_pos : 0 < |z.im| := abs_pos.mpr hz

        have h_norm_bound : ‖ψ₁ - ψ₂‖ ≤ (1 / |z.im|) * ‖φ₁ - φ₂‖ := by
          have h1 : |z.im| * ‖ψ₁ - ψ₂‖ ≤ ‖φ₁ - φ₂‖ := h_bound
          calc ‖ψ₁ - ψ₂‖
              = (1 / |z.im|) * (|z.im| * ‖ψ₁ - ψ₂‖) := by field_simp
            _ ≤ (1 / |z.im|) * ‖φ₁ - φ₂‖ := by
                apply mul_le_mul_of_nonneg_left h1
                positivity

        rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
        have h_nnreal : (0 : ℝ) ≤ 1 / |z.im| := by positivity
        let c : NNReal := ⟨1 / |z.im|, h_nnreal⟩
        calc ENNReal.ofReal ‖ψ₁ - ψ₂‖
            ≤ ENNReal.ofReal (1 / |z.im| * ‖φ₁ - φ₂‖) := ENNReal.ofReal_le_ofReal h_norm_bound
          _ = ENNReal.ofReal (1 / |z.im|) * ENNReal.ofReal ‖φ₁ - φ₂‖ := by
              rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / |z.im|)]
          _ = (c : ENNReal) * ENNReal.ofReal ‖φ₁ - φ₂‖ := by
              congr 1
              exact ENNReal.ofReal_eq_coe_nnreal h_nnreal



      exact h_lip.continuous }

/--
Resolvent identity: R(z) - R(w) = (z - w)R(z)R(w)

This fundamental identity relates resolvents at different points.
-/
theorem resolvent_identity {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : IsSelfAdjoint gen)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    resolvent gen z hz hsa - resolvent gen w hw hsa =
    (z - w) • ((resolvent gen z hz hsa).comp (resolvent gen w hw hsa)) := by
  ext φ

  -- Let ψ_w = R_w(φ), so (A - wI)ψ_w = φ
  let ψ_w_sub := Classical.choose (self_adjoint_range_all_z gen hsa w hw φ)
  let ψ_w := ψ_w_sub.val
  have h_w_domain : ψ_w ∈ gen.domain := ψ_w_sub.property
  have h_w_eq : gen.op ψ_w - w • ψ_w = φ := (Classical.choose_spec (self_adjoint_range_all_z gen hsa w hw φ)).1

  -- Let ψ_z = R_z(φ), so (A - zI)ψ_z = φ
  let ψ_z_sub := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ)
  let ψ_z := ψ_z_sub.val
  have h_z_domain : ψ_z ∈ gen.domain := ψ_z_sub.property
  have h_z_eq : gen.op ψ_z - z • ψ_z = φ := (Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ)).1

  -- Let η = R_z(ψ_w), so (A - zI)η = ψ_w
  let η_sub := Classical.choose (self_adjoint_range_all_z gen hsa z hz ψ_w)
  let η := η_sub.val
  have h_η_domain : η ∈ gen.domain := η_sub.property
  have h_η_eq : gen.op η - z • η = ψ_w := (Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz ψ_w)).1

  have h_Rz : resolvent gen z hz hsa φ = ψ_z := rfl
  have h_Rw : resolvent gen w hw hsa φ = ψ_w := rfl
  have h_Rz_ψw : resolvent gen z hz hsa ψ_w = η := rfl

  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.comp_apply]
  rw [h_Rz, h_Rw, h_Rz_ψw]

  -- Key: (A - zI)ψ_w = φ + (w - z)ψ_w
  have h_Az_ψw : gen.op ψ_w - z • ψ_w = φ + (w - z) • ψ_w := by
    have h_Aw : gen.op ψ_w = φ + w • ψ_w := by
      calc gen.op ψ_w
          = (gen.op ψ_w - w • ψ_w) + w • ψ_w := by abel
        _ = φ + w • ψ_w := by rw [h_w_eq]
    calc gen.op ψ_w - z • ψ_w
        = (φ + w • ψ_w) - z • ψ_w := by rw [h_Aw]
      _ = φ + (w - z) • ψ_w := by rw [sub_smul]; abel

  -- ψ_z + (w - z)η is in domain and solves (A - zI)x = φ + (w - z)ψ_w
  have h_sum_domain : ψ_z + (w - z) • η ∈ gen.domain := by
    apply gen.domain.add_mem h_z_domain
    exact gen.domain.smul_mem (w - z) h_η_domain

  have h_sum_eq : gen.op (ψ_z + (w - z) • η) - z • (ψ_z + (w - z) • η) = φ + (w - z) • ψ_w := by
    calc gen.op (ψ_z + (w - z) • η) - z • (ψ_z + (w - z) • η)
        = (gen.op ψ_z + gen.op ((w - z) • η)) - z • (ψ_z + (w - z) • η) := by
            rw [gen.op.map_add]
      _ = (gen.op ψ_z + (w - z) • gen.op η) - z • (ψ_z + (w - z) • η) := by
            rw [gen.op.map_smul]
      _ = (gen.op ψ_z + (w - z) • gen.op η) - (z • ψ_z + z • ((w - z) • η)) := by
            rw [smul_add]
      _ = (gen.op ψ_z - z • ψ_z) + ((w - z) • gen.op η - z • ((w - z) • η)) := by abel
      _ = (gen.op ψ_z - z • ψ_z) + ((w - z) • gen.op η - (w - z) • (z • η)) := by
            rw [smul_comm z (w - z) η]
      _ = (gen.op ψ_z - z • ψ_z) + (w - z) • (gen.op η - z • η) := by
            rw [← smul_sub]
      _ = φ + (w - z) • ψ_w := by rw [h_z_eq, h_η_eq]

  -- Both ψ_w and ψ_z + (w-z)η solve (A - zI)x = φ + (w-z)ψ_w
  -- By uniqueness they are equal
  let target := φ + (w - z) • ψ_w
  let canonical := Classical.choose (self_adjoint_range_all_z gen hsa z hz target)
  have h_canonical_unique := (Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz target)).2

  have h_ψw_is_canonical : (⟨ψ_w, h_w_domain⟩ : {x : H // x ∈ gen.domain}) = canonical := by
    apply h_canonical_unique
    simp only
    exact h_Az_ψw

  have h_sum_is_canonical : (⟨ψ_z + (w - z) • η, h_sum_domain⟩ : {x : H // x ∈ gen.domain}) = canonical := by
    apply h_canonical_unique
    simp only
    exact h_sum_eq

  have h_eq_vals : ψ_w = ψ_z + (w - z) • η := by
    have h1 : (⟨ψ_w, h_w_domain⟩ : {x : H // x ∈ gen.domain}) =
              ⟨ψ_z + (w - z) • η, h_sum_domain⟩ := by
      rw [h_ψw_is_canonical, ← h_sum_is_canonical]
    exact congrArg Subtype.val h1

  -- ψ_z - ψ_w = ψ_z - (ψ_z + (w - z)η) = -(w-z)η = (z-w)η
  calc ψ_z - ψ_w
      = ψ_z - (ψ_z + (w - z) • η) := by rw [h_eq_vals]
    _ = -((w - z) • η) := by abel
    _ = (-(w - z)) • η := by rw [neg_smul]
    _ = (z - w) • η := by ring_nf

/--
Bound on resolvent norm: ‖R_z‖ ≤ 1/|Im(z)|

This shows the resolvent is bounded with an explicit bound.
-/
theorem resolvent_bound {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im ≠ 0) :
    ‖resolvent gen z hz hsa‖ ≤ 1 / |z.im| := by
  -- Prove pointwise bound: ‖R_z(φ)‖ ≤ (1/|Im(z)|) · ‖φ‖
  have h_pointwise : ∀ φ : H, ‖resolvent gen z hz hsa φ‖ ≤ (1 / |z.im|) * ‖φ‖ := by
    intro φ

    -- ψ := R_z(φ) is the unique element satisfying (A - zI)ψ = φ
    let ψ_sub := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ)
    let ψ := ψ_sub.val

    -- ψ is in the domain
    have h_domain : ψ ∈ gen.domain := ψ_sub.property

    -- (A - zI)ψ = φ
    have h_eq : gen.op ψ - z • ψ = φ := by
      have h_spec := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ)
      exact h_spec.1

    -- From lower_bound_estimate: ‖(A - zI)ψ‖ ≥ |Im(z)| · ‖ψ‖
    have h_lower := lower_bound_estimate gen z hz ψ h_domain

    -- Substituting (A - zI)ψ = φ: ‖φ‖ ≥ |Im(z)| · ‖ψ‖
    rw [h_eq] at h_lower

    -- Rearrange: ‖ψ‖ ≤ ‖φ‖ / |Im(z)|
    have h_im_pos : 0 < |z.im| := abs_pos.mpr hz

    have h_ψ_bound : ‖ψ‖ ≤ ‖φ‖ / |z.im| := by
      have h_mul : |z.im| * ‖ψ‖ ≤ ‖φ‖ := h_lower
      calc ‖ψ‖
          = (|z.im|)⁻¹ * (|z.im| * ‖ψ‖) := by field_simp
        _ ≤ (|z.im|)⁻¹ * ‖φ‖ := by
            apply mul_le_mul_of_nonneg_left h_mul
            exact inv_nonneg.mpr (abs_nonneg _)
        _ = ‖φ‖ / |z.im| := by rw [inv_mul_eq_div]

    -- resolvent gen z hz hsa φ = ψ by definition
    have h_res_eq : resolvent gen z hz hsa φ = ψ := rfl

    calc ‖resolvent gen z hz hsa φ‖
        = ‖ψ‖ := by rw [h_res_eq]
      _ ≤ ‖φ‖ / |z.im| := h_ψ_bound
      _ = (1 / |z.im|) * ‖φ‖ := by ring

  -- Convert pointwise bound to operator norm bound
  apply ContinuousLinearMap.opNorm_le_bound
  · apply div_nonneg
    · norm_num
    · exact abs_nonneg _
  · exact h_pointwise
