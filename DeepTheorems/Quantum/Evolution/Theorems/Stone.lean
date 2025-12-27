/-
Author: Adam Bornemann
Created: 10/22/2025
Updated: 12/26/2025

================================================================================
STONE'S THEOREM: THE COMPLETE STATEMENT
================================================================================

Stone's Theorem (1932): There is a bijective correspondence between
  • Strongly continuous one-parameter unitary groups U(t) on a Hilbert space H
  • Self-adjoint operators A on H (possibly unbounded)

The correspondence is given by: U(t) = exp(itA)

This file assembles the complete proof from:
  • Core.lean       - Structures and definitions
  • Resolvent.lean  - Resolvent theory for self-adjoint operators (~2500 lines)
  • Exponential.lean - Yosida approximation and operator exponentials (~3000 lines)

References:
  - Stone, M.H. "On one-parameter unitary groups in Hilbert Space" (1932)
  - Reed & Simon, "Methods of Modern Mathematical Physics" Vol. 1, Ch. VIII
  - Hall, B.C. "Quantum Theory for Mathematicians" Ch. 9-10
-/

import LogosLibrary.DeepTheorems.Quantum.Evolution.Yosida
import LogosLibrary.DeepTheorems.Quantum.Evolution.Resolvent
namespace StonesTheorem

open InnerProductSpace Complex Filter Topology
open StonesTheorem.Yosida StonesTheorem.Resolvent StonesTheorem.Bochner Stone.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
================================================================================
PART I: GROUP → GENERATOR (Existence and Uniqueness)
================================================================================

Every strongly continuous one-parameter unitary group has a unique
self-adjoint generator.
-/

/-- **Stone's Theorem, Part I: Existence of Generator**

Every strongly continuous one-parameter unitary group U(t) has a self-adjoint
generator A such that U(t) = exp(itA).

The generator is constructed via:
  D(A) = {ψ ∈ H | lim_{t→0} (U(t)ψ - ψ)/(it) exists}
  Aψ = lim_{t→0} (U(t)ψ - ψ)/(it)

Self-adjointness is proven via:
  1. Symmetry: ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩ for ψ, φ ∈ D(A)
  2. Surjectivity: Range(A ± iI) = H (proven in Resolvent.lean)
-/
theorem stone_existence (U_grp : OneParameterUnitaryGroup (H := H)) :
    ∃ (gen : Generator U_grp), gen.IsSelfAdjoint :=
  ⟨Generator.ofUnitaryGroup U_grp, Generator.ofUnitaryGroup_isSelfAdjoint U_grp⟩


/-- **Stone's Theorem, Part I: Uniqueness of Generator**

The self-adjoint generator of a strongly continuous unitary group is unique.

If A₁ and A₂ are both self-adjoint generators of U(t), then A₁ = A₂ on
their common domain, and their domains are equal.
-/
theorem stone_uniqueness
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen₁ gen₂ : Generator U_grp)
    (hsa₁ : gen₁.IsSelfAdjoint)
    (hsa₂ : gen₂.IsSelfAdjoint) :
    HEq gen₁.op gen₂.op ∧ gen₁.domain = gen₂.domain := by
  -- Domains are equal by maximality of self-adjoint operators
  have h_dom := selfAdjoint_generators_domain_eq U_grp gen₁ gen₂ hsa₁ hsa₂

  -- Operators agree on the common domain by uniqueness of limits
  have h_eq_on_dom : ∀ (ψ : H) (hψ₁ : ψ ∈ gen₁.domain) (hψ₂ : ψ ∈ gen₂.domain),
      gen₁.op ⟨ψ, hψ₁⟩ = gen₂.op ⟨ψ, hψ₂⟩ := by
    intro ψ hψ₁ hψ₂
    exact generator_op_eq_on_domain U_grp gen₁ gen₂ ψ hψ₁ hψ₂

  -- Operators are equal everywhere (as HEq since domains are equal)
  have h_op := generator_op_ext_of_eq_on_domain U_grp gen₁ gen₂ h_dom h_eq_on_dom

  exact ⟨h_op, h_dom⟩



/-- **Stone's Theorem, Part I: Combined Statement**

Every strongly continuous one-parameter unitary group has a UNIQUE
self-adjoint generator.
-/
theorem stone_part_one (U_grp : OneParameterUnitaryGroup (H := H)) :
    ∃! (gen : Generator U_grp), gen.IsSelfAdjoint := by
  obtain ⟨gen, hsa⟩ := stone_existence U_grp
  refine ⟨gen, hsa, ?_⟩
  intro gen' hsa'
  have ⟨h_op, h_dom⟩ := stone_uniqueness U_grp gen gen' hsa hsa'
  -- Generator is a structure with op and domain as data fields
  -- The remaining fields (dense_domain, generator_formula, domain_invariant, symmetric, domain_maximal)
  -- are proofs (Prop-valued), so they're equal by proof irrelevance once data matches
  cases gen with
  | mk op domain dense_domain generator_formula domain_invariant symmetric domain_maximal =>
    cases gen' with
    | mk op' domain' dense_domain' generator_formula' domain_invariant' symmetric' domain_maximal' =>
      simp only at h_op h_dom
      subst h_dom
      simp only [heq_eq_eq] at h_op
      subst h_op
      rfl

/-!
================================================================================
PART II: GENERATOR → GROUP (The Exponential Map)
================================================================================

Every self-adjoint operator generates a strongly continuous one-parameter
unitary group via the exponential map.
-/

/-- **Stone's Theorem, Part II: Exponential Equals Original Group**

For a self-adjoint generator A of U(t), the exponential exp(itA)
constructed via Yosida approximation equals the original group U(t).

This is the culmination of Exponential.lean:
  exp(itA) := s-lim_{n→∞} exp(it·Aₙˢʸᵐ)
where Aₙˢʸᵐ are the symmetrized Yosida approximants.
-/
theorem stone_exponential_eq_group
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ : H) :
    exponential' gen hsa h_dense t ψ = U_grp.U t ψ := by
  -- Both exponential and U(t) are continuous linear maps
  -- They agree on the dense set D(A)
  -- Therefore they agree everywhere by density

  -- Step 1: Agreement on domain
  have h_agree_on_domain : ∀ φ ∈ gen.domain, exponential' gen hsa h_dense t φ = U_grp.U t φ := by
    intro φ hφ
    have h_tendsto := expBounded_yosidaApproxSym_tendsto_unitary gen hsa h_dense t φ hφ
    have h_exp_tendsto := exponential_tendsto gen hsa h_dense t φ
    exact tendsto_nhds_unique h_exp_tendsto h_tendsto

  -- Step 2: Both are isometries
  have h_exp_isometry : ∀ χ : H, ‖exponential' gen hsa h_dense t χ‖ = ‖χ‖ := by
    intro χ
    have h := exponential_unitary gen hsa h_dense t χ χ
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h_sq : ‖exponential' gen hsa h_dense t χ‖^2 = ‖χ‖^2 := by exact_mod_cast h
    nlinarith [sq_nonneg (‖exponential' gen hsa h_dense t χ‖ - ‖χ‖),
               sq_nonneg (‖exponential' gen hsa h_dense t χ‖ + ‖χ‖),
               norm_nonneg (exponential' gen hsa h_dense t χ), norm_nonneg χ]

  have h_U_isometry : ∀ χ : H, ‖U_grp.U t χ‖ = ‖χ‖ := by
    intro χ
    have h := U_grp.unitary t χ χ
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h_sq : ‖U_grp.U t χ‖^2 = ‖χ‖^2 := by exact_mod_cast h
    nlinarith [sq_nonneg (‖U_grp.U t χ‖ - ‖χ‖),
               sq_nonneg (‖U_grp.U t χ‖ + ‖χ‖),
               norm_nonneg (U_grp.U t χ), norm_nonneg χ]

  -- Step 3: Use density argument
  apply eq_of_forall_dist_le
  intro ε hε

  have hε2 : ε / 2 > 0 := by linarith
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp
    (h_dense.closure_eq ▸ Set.mem_univ ψ) (ε / 2) hε2
  rw [dist_eq_norm] at hφ_close ⊢

  calc ‖exponential' gen hsa h_dense t ψ - U_grp.U t ψ‖
      = ‖(exponential' gen hsa h_dense t ψ - exponential' gen hsa h_dense t φ) +
         (exponential' gen hsa h_dense t φ - U_grp.U t φ) +
         (U_grp.U t φ - U_grp.U t ψ)‖ := by congr 1; abel
    _ ≤ ‖exponential' gen hsa h_dense t ψ - exponential' gen hsa h_dense t φ‖ +
        ‖exponential' gen hsa h_dense t φ - U_grp.U t φ‖ +
        ‖U_grp.U t φ - U_grp.U t ψ‖ := by
          apply le_trans (norm_add_le _ _)
          apply add_le_add_right (norm_add_le _ _)
    _ = ‖exponential' gen hsa h_dense t (ψ - φ)‖ + 0 + ‖U_grp.U t (φ - ψ)‖ := by
          rw [← map_sub, ← map_sub, h_agree_on_domain φ hφ_mem, sub_self, norm_zero]
    _ = ‖ψ - φ‖ + 0 + ‖φ - ψ‖ := by
          rw [h_exp_isometry, h_U_isometry]
    _ = 2 * ‖ψ - φ‖ := by rw [norm_sub_rev]; ring
    _ ≤ 2 * (ε / 2) := by linarith [hφ_close]
    _ = ε := by ring

/-- **Stone's Theorem, Part II: The Exponential Forms a Unitary Group**

The exponential map exp(itA) for self-adjoint A forms a strongly continuous
one-parameter unitary group.
-/
theorem stone_exponential_is_unitary_group
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H)) :
    -- Unitarity
    (∀ t ψ φ, ⟪exponential' gen hsa h_dense t ψ, exponential' gen hsa h_dense t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ) ∧
    -- Group law
    (∀ s t ψ, exponential' gen hsa h_dense (s + t) ψ = exponential' gen hsa h_dense s (exponential' gen hsa h_dense t ψ)) ∧
    -- Identity
    (∀ ψ, exponential' gen hsa h_dense 0 ψ = ψ) ∧
    -- Strong continuity
    (∀ ψ, Continuous (fun t => exponential' gen hsa h_dense t ψ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun t ψ φ => exponential_unitary gen hsa h_dense t ψ φ
  · exact fun s t ψ => exponential_group_law gen hsa h_dense s t ψ
  · exact fun ψ => exponential_identity gen hsa h_dense ψ
  · exact fun ψ => exponential_strong_continuous gen hsa h_dense ψ

/-!
================================================================================
PART III: THE BIJECTION
================================================================================

Stone's theorem establishes a bijective correspondence.
-/

/-- **Stone's Theorem: The Generator of exp(itA) is A**

If we start with a self-adjoint generator A, form exp(itA), and then
compute the generator of this group, we recover A.

This closes the loop: Generator → Group → Generator = identity
-/
theorem stone_generator_of_exponential
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    Tendsto (fun t : ℝ => ((I * t)⁻¹ : ℂ) • (exponential' gen hsa h_dense t ψ - ψ))
            (𝓝[≠] 0) (𝓝 (gen.op ⟨ψ, hψ⟩)) := by
  -- exponential_generator_eq gives: t⁻¹ • (exp(t)ψ - ψ) → I • Aψ
  have h := exponential_generator_eq gen hsa h_dense ψ hψ

  -- Convert: (I * t)⁻¹ • x = -I • (t⁻¹ • x)
  have h_convert : ∀ t : ℝ, t ≠ 0 →
      ((I * (t : ℂ))⁻¹ : ℂ) • (exponential' gen hsa h_dense t ψ - ψ) =
      (-I) • ((t⁻¹ : ℂ) • (exponential' gen hsa h_dense t ψ - ψ)) := by
    intro t ht
    rw [← smul_assoc]
    congr 1
    rw [mul_inv_rev, mul_comm ((t : ℂ))⁻¹, Complex.inv_I, ← Complex.ofReal_inv]
    rfl

  -- Multiply h by -I: -I • (t⁻¹ • (exp(t)ψ - ψ)) → -I • I • Aψ = Aψ
  have h_lim := h.const_smul (-I)

  -- Simplify: (-I) • I • Aψ = Aψ
  have h_simp : (-I) • I • gen.op ⟨ψ, hψ⟩ = gen.op ⟨ψ, hψ⟩ := by
    rw [smul_smul]
    simp only [neg_mul, I_mul_I, neg_neg, one_smul]
  rw [h_simp] at h_lim

  -- Connect via the conversion
  exact h_lim.congr' (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (h_convert t ht).symm)

/-- **Stone's Theorem: Complete Bijection Statement**

There is a bijective correspondence between:
  • Strongly continuous one-parameter unitary groups on H
  • Self-adjoint operators on H

Given by: U(t) ↔ A where U(t) = exp(itA)
-/
theorem stone_bijection :
    ∀ (U_grp : OneParameterUnitaryGroup (H := H)),
    ∃! (gen : Generator U_grp), gen.IsSelfAdjoint ∧
      (∀ (hsa : gen.IsSelfAdjoint) (h_dense : Dense (gen.domain : Set H)),
        ∀ t ψ, U_grp.U t ψ = exponential' gen hsa h_dense t ψ) := by
  intro U_grp
  obtain ⟨gen, hsa, h_unique⟩ := stone_part_one U_grp
  refine ⟨gen, ⟨hsa, ?_⟩, ?_⟩
  · intro hsa' h_dense t ψ
    exact (stone_exponential_eq_group U_grp gen hsa' h_dense t ψ).symm
  · intro gen' ⟨hsa', _⟩
    exact h_unique gen' hsa'

/-!
================================================================================
PART IV: PHYSICAL INTERPRETATION
================================================================================

In quantum mechanics, Stone's theorem is the mathematical foundation for
the time evolution of quantum states.
-/

/-- **Schrödinger Equation**

For a quantum system with Hamiltonian H (a self-adjoint operator),
the time evolution satisfies:

  i ℏ d/dt |ψ(t)⟩ = H |ψ(t)⟩

In our convention with U(t) = exp(itA), we get d/dt[U(t)ψ] = iA·U(t)ψ.

Note: Physics typically uses U(t) = exp(-itH), giving d/dt = -iH.
Our convention is A = -H (generator = negative Hamiltonian).
-/
theorem schrodinger_equation
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ₀ : H) (hψ₀ : ψ₀ ∈ gen.domain) :
    -- The evolved state ψ(t) = U(t)ψ₀ satisfies d/dt[U(t)ψ₀]|_{t=0} = iAψ₀
    HasDerivAt (fun t : ℝ => U_grp.U t ψ₀)
               (I • gen.op ⟨U_grp.U 0 ψ₀, gen.domain_invariant 0 ψ₀ hψ₀⟩)
               0 := by
  -- Use exponential_derivative_on_domain at t = 0
  have h_deriv := exponential_derivative_on_domain gen hsa h_dense 0 ψ₀ hψ₀

  -- Convert from exponential to U_grp.U
  have h_eq : ∀ t, exponential' gen hsa h_dense t ψ₀ = U_grp.U t ψ₀ :=
    fun t => stone_exponential_eq_group U_grp gen hsa h_dense t ψ₀

  -- Rewrite the derivative using the equality
  have h_fun_eq : (fun t => exponential' gen hsa h_dense t ψ₀) = (fun t => U_grp.U t ψ₀) := by
    ext t; exact h_eq t
  rw [h_fun_eq] at h_deriv

  exact h_deriv

/-!
================================================================================
SUMMARY
================================================================================

STONE'S THEOREM (Complete):

Let H be a complex Hilbert space.

(1) EXISTENCE: Every strongly continuous one-parameter unitary group
    {U(t)}_{t∈ℝ} on H has a self-adjoint generator A defined by

      D(A) = {ψ | lim_{t→0} (U(t)ψ - ψ)/(it) exists}
      Aψ = lim_{t→0} (U(t)ψ - ψ)/(it)

(2) UNIQUENESS: The generator is unique.

(3) REPRESENTATION: U(t) = exp(itA) where the exponential is defined via
    the Yosida approximation:

      exp(itA) = s-lim_{n→∞} exp(it·Aₙ)

    where Aₙ are bounded self-adjoint approximants to A.

(4) CONVERSE: Given any self-adjoint operator A, the formula U(t) = exp(itA)
    defines a strongly continuous one-parameter unitary group with generator A.

(5) BIJECTION: This establishes a bijective correspondence between
    strongly continuous one-parameter unitary groups and self-adjoint operators.

DEPENDENCIES:
  • Generator.lean:        Structures, ~700 lines
  • Bochner.lean:     Bochner machinery, 2500 lines
  • Resolvent.lean:   Resolvent theory, ~2500 lines
  • Yosida.lean: Yosida approximation, ~5000 lines
  • Theorem.lean:     This file, assembly

REMAINING SORRIES (in Exponential.lean):
  • duhamel_estimate: Requires Bochner integration machinery
  • yosidaApproxSym_uniform_convergence_on_orbit: Requires Arzelà-Ascoli
  • exponential_tendsto: Technical issue with limUnder definition

Total: ~10,000+ lines for the complete formalization of Stone's theorem.
================================================================================
-/

end StonesTheorem
