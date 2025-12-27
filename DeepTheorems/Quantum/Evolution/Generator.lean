/-
Author: Adam Bornemann
Created: 10/10/2025
Updated: 12/26/2025

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
import LogosLibrary.DeepTheorems.Quantum.Uncertainty.Core

namespace Stone.Generators

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
  /-- Dense domain where the limit defining the generator exists -/
  domain : Submodule ℂ H
  /-- The operator itself (formally defined on all of H) -/
  op : domain →ₗ[ℂ] H
  /-- The domain is dense (crucial for Stone's theorem) -/
  dense_domain : Dense (domain : Set H)
  /-- Generator formula: Aψ = -i lim_{t→0} (U(t)ψ - ψ)/t

  The limit is taken in the punctured neighborhood of 0.
  We express: Aψ = lim_{t→0, t≠0} (U(t)ψ - ψ)/(it)
  -/
  generator_formula : ∀ (ψ : domain),
    Tendsto (fun t : ℝ => ((I : ℂ) * (t : ℂ))⁻¹ • (U_grp.U t (ψ : H) - (ψ : H)))
          (𝓝[≠] 0)
          (𝓝 (op ψ))
  /-- Domain is invariant under time evolution -/
  domain_invariant : ∀ (t : ℝ) (ψ : H), ψ ∈ domain → U_grp.U t ψ ∈ domain
  /-- Generator is symmetric (self-adjointness proven separately) -/
  symmetric : ∀ (ψ φ : domain), ⟪op ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), op φ⟫_ℂ
  /-- Go fuck yourself-/
  domain_maximal : ∀ ψ : H, (∃ η : H, Tendsto (fun t : ℝ => ((I : ℂ) * (t : ℂ))⁻¹ • (U_grp.U t ψ - ψ)) (𝓝[≠] 0) (𝓝 η)) → ψ ∈ domain


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
def Generator.IsSelfAdjoint {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) : Prop :=
  (∀ φ : H, ∃ (ψ : H) (hψ : ψ ∈ gen.domain),
    gen.op ⟨ψ, hψ⟩ + (I : ℂ) • ψ = φ) ∧
  (∀ φ : H, ∃ (ψ : H) (hψ : ψ ∈ gen.domain),
    gen.op ⟨ψ, hψ⟩ - (I : ℂ) • ψ = φ)


/-!
### Helper Lemmas for Generator Uniqueness
-/

/-- The domain of a generator is exactly the set of vectors where the limit exists.
This characterization shows that the domain is uniquely determined by the unitary group. -/
lemma generator_domain_char (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp) (ψ : H) :
    ψ ∈ gen.domain ↔
    ∃ (η : H), Tendsto (fun t : ℝ => ((I : ℂ) * (t : ℂ))⁻¹ • (U_grp.U t ψ - ψ))
                       (𝓝[≠] 0) (𝓝 η) := by
  constructor
  · intro hψ
    exact ⟨gen.op ⟨ψ, hψ⟩, gen.generator_formula ⟨ψ, hψ⟩⟩
  · intro ⟨η, hη⟩
    exact gen.domain_maximal ψ ⟨η, hη⟩

/-- For self-adjoint generators, the domain is maximal: it contains all vectors
where the limit defining the generator exists. -/
lemma selfAdjoint_domain_maximal (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp) (_ /-hsa-/ : gen.IsSelfAdjoint) (ψ : H)
    (η : H) (hη : Tendsto (fun t : ℝ => ((I : ℂ) * (t : ℂ))⁻¹ • (U_grp.U t ψ - ψ))
                          (𝓝[≠] 0) (𝓝 η)) :
    ψ ∈ gen.domain := gen.domain_maximal ψ ⟨η, hη⟩

/-- Self-adjoint generators of the same unitary group have the same domain. -/
lemma selfAdjoint_generators_domain_eq (U_grp : OneParameterUnitaryGroup (H := H))
    (gen₁ gen₂ : Generator U_grp)
    (hsa₁ : gen₁.IsSelfAdjoint) (hsa₂ : gen₂.IsSelfAdjoint) :
    gen₁.domain = gen₂.domain := by
  ext ψ
  constructor
  · intro hψ₁
    -- ψ ∈ gen₁.domain means the limit exists (with value gen₁.op ψ)
    have h_lim := gen₁.generator_formula (⟨ψ, hψ₁⟩ : gen₁.domain)
    -- By maximality of gen₂.domain, since limit exists, ψ ∈ gen₂.domain
    exact selfAdjoint_domain_maximal U_grp gen₂ hsa₂ ψ (gen₁.op (⟨ψ, hψ₁⟩ : gen₁.domain)) h_lim
  · intro hψ₂
    have h_lim := gen₂.generator_formula (⟨ψ, hψ₂⟩ : gen₂.domain)
    exact selfAdjoint_domain_maximal U_grp gen₁ hsa₁ ψ (gen₂.op (⟨ψ, hψ₂⟩ : gen₂.domain)) h_lim

/-- Generators that agree on their common domain are equal as linear maps on the domain. -/
lemma generator_op_eq_on_domain (U_grp : OneParameterUnitaryGroup (H := H))
    (gen₁ gen₂ : Generator U_grp) (ψ : H)
    (hψ₁ : ψ ∈ gen₁.domain) (hψ₂ : ψ ∈ gen₂.domain) :
    gen₁.op (⟨ψ, hψ₁⟩ : gen₁.domain) = gen₂.op (⟨ψ, hψ₂⟩ : gen₂.domain) := by
  -- Both are the unique limit of the same expression
  have h₁ := gen₁.generator_formula (⟨ψ, hψ₁⟩ : gen₁.domain)
  have h₂ := gen₂.generator_formula (⟨ψ, hψ₂⟩ : gen₂.domain)
  exact tendsto_nhds_unique h₁ h₂

/-- For generators with the same domain, if they agree on the domain, they agree everywhere.
This uses the fact that the generator is determined by its action on the dense domain. -/
lemma generator_op_ext_of_eq_on_domain (U_grp : OneParameterUnitaryGroup (H := H))
    (gen₁ gen₂ : Generator U_grp)
    (h_dom : gen₁.domain = gen₂.domain)
    (h_eq : ∀ (ψ : H) (hψ₁ : ψ ∈ gen₁.domain) (hψ₂ : ψ ∈ gen₂.domain),
            gen₁.op ⟨ψ, hψ₁⟩ = gen₂.op ⟨ψ, hψ₂⟩) :
    HEq gen₁.op gen₂.op := by
  have h_eq' : gen₁.op = h_dom ▸ gen₂.op := by
    ext ⟨ψ, hψ⟩
    have hψ₂ : ψ ∈ gen₂.domain := h_dom ▸ hψ
    rw [h_eq ψ hψ hψ₂]
    congr 1
    rw [h_dom]
    rw [h_dom]
    rw [@Function.const_def, ← h_dom]
    exact HEq.refl (Function.const (↥gen₁.domain) H)
    rw [h_dom]
    rw [@eqRec_eq_cast]
    exact HEq.symm (cast_heq (Eq.symm h_dom ▸ rfl) gen₂.op)
    rw [@heq_comm]
    congr 1
    exact
      (Set.eqOn_univ (fun x => x ∈ gen₁.domain) fun x => x ∈ gen₂.domain).mp fun ⦃x⦄ a =>
        congrFun (congrArg Membership.mem h_dom) x
    exact heq_of_eqRec_eq (congrFun (congrArg Membership.mem h_dom) ψ) rfl

  rw [h_eq', @heq_comm, @eqRec_eq_cast]
  exact HEq.symm (cast_heq (Eq.symm h_dom ▸ rfl) gen₂.op)


end Stone.Generators
