/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSpace.Complete
/-
# Infinitesimal Generators of One-Parameter Unitary Groups

This file develops the theory of strongly continuous one-parameter unitary groups
on complex Hilbert spaces and their infinitesimal generators.

## Main definitions

* `OneParameterUnitaryGroup`: A family `U : ℝ → (H →L[ℂ] H)` satisfying unitarity,
  the group law `U(s+t) = U(s) ∘ U(t)`, and strong continuity.
* `Generator`: The infinitesimal generator of a one-parameter unitary group, defined
  as the (generally unbounded) operator `A` satisfying `Aψ = lim_{t→0} (U(t)ψ - ψ)/(it)`
  on its natural domain.
* `Generator.IsSelfAdjoint`: Self-adjointness of a generator, characterized by
  surjectivity of `A ± iI` (equivalently, vanishing deficiency indices).

## Main statements

* `inverse_eq_adjoint`: For a one-parameter unitary group, `U(-t) = U(t)*`.
* `norm_preserving`: Unitary evolution preserves norms: `‖U(t)ψ‖ = ‖ψ‖`.
* `norm_one`: The operator norm satisfies `‖U(t)‖ = 1`.
* `selfAdjoint_generators_domain_eq`: Self-adjoint generators of the same unitary
  group have equal domains.
* `generator_op_eq_on_domain`: Generators of the same group agree on common domain elements.

## Physics interpretation

In quantum mechanics, `U(t) = exp(-itH/ℏ)` describes time evolution under a
Hamiltonian `H`. The generator `A = H/ℏ` is the observable corresponding to
energy (up to scaling). Self-adjointness of the generator is equivalent to
unitarity of time evolution, reflecting conservation of probability.

## Implementation notes

* Generators are necessarily unbounded operators for nontrivial time evolution,
  hence we work with a dense `Submodule ℂ H` as the domain rather than defining
  a total operator.
* The domain is characterized as maximal: `ψ ∈ domain` iff the defining limit exists.
* We use `𝓝[≠] 0` (punctured neighborhood) for the generator limit to avoid
  division by zero at `t = 0`.
* Self-adjointness uses the criterion `ran(A ± iI) = H` rather than equality of
  operator and adjoint, which is better suited to unbounded operators.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*][reed1980]
* [Hall, *Quantum Theory for Mathematicians*][hall2013]
* Stone's theorem: a one-parameter unitary group has a unique self-adjoint generator,
  and conversely every self-adjoint operator generates a unique one-parameter unitary group.

## TODO

* Prove existence of a generator for any strongly continuous one-parameter unitary group.
* Prove Stone's theorem: the correspondence between self-adjoint operators and
  one-parameter unitary groups is bijective.
* Connect to the spectral theorem and functional calculus.

-/
namespace QuantumMechanics.Generators

open InnerProductSpace MeasureTheory Complex Filter Topology

set_option linter.unusedSectionVars false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



structure OneParameterUnitaryGroup where
  U : ℝ → (H →L[ℂ] H)
  unitary : ∀ (t : ℝ) (ψ φ : H), ⟪U t ψ, U t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ
  group_law : ∀ s t : ℝ, U (s + t) = (U s).comp (U t)
  identity : U 0 = ContinuousLinearMap.id ℂ H
  strong_continuous : ∀ ψ : H, Continuous (fun t : ℝ => U t ψ)


theorem inverse_eq_adjoint (U_grp : OneParameterUnitaryGroup (H := H)) (t : ℝ) :
    U_grp.U (-t) = (U_grp.U t).adjoint := by
  ext ψ
  apply ext_inner_right ℂ
  intro φ

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
          rw [ContinuousLinearMap.adjoint_inner_left]

theorem norm_preserving (U_grp : OneParameterUnitaryGroup (H := H)) (t : ℝ) (ψ : H) :
    ‖U_grp.U t ψ‖ = ‖ψ‖ := by
  have h := U_grp.unitary t ψ ψ
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

  have h_sq : ‖U_grp.U t ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    calc ‖U_grp.U t ψ‖ ^ 2
        = (⟪U_grp.U t ψ, U_grp.U t ψ⟫_ℂ).re := h1.symm
      _ = (⟪ψ, ψ⟫_ℂ).re := by rw [h]
      _ = ‖ψ‖ ^ 2 := h2

  have : ‖U_grp.U t ψ‖ = ‖ψ‖ ∨ ‖U_grp.U t ψ‖ = -‖ψ‖ := by
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h_sq
  cases this with
  | inl h => exact h
  | inr h =>

      have h1 : 0 ≤ ‖U_grp.U t ψ‖ := norm_nonneg _
      have h2 : 0 ≤ ‖ψ‖ := norm_nonneg _
      linarith


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


structure Generator (U_grp : OneParameterUnitaryGroup (H := H)) where
  domain : Submodule ℂ H
  op : domain →ₗ[ℂ] H
  dense_domain : Dense (domain : Set H)
  generator_formula : ∀ (ψ : domain),
    Tendsto (fun t : ℝ => ((I : ℂ) * (t : ℂ))⁻¹ • (U_grp.U t (ψ : H) - (ψ : H)))
          (𝓝[≠] 0)
          (𝓝 (op ψ))
  domain_invariant : ∀ (t : ℝ) (ψ : H), ψ ∈ domain → U_grp.U t ψ ∈ domain
  symmetric : ∀ (ψ φ : domain), ⟪op ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), op φ⟫_ℂ
  domain_maximal : ∀ ψ : H, (∃ η : H,
    Tendsto (fun t : ℝ => ((I : ℂ) * (t : ℂ))⁻¹ • (U_grp.U t ψ - ψ)) (𝓝[≠] 0) (𝓝 η)) → ψ ∈ domain


def Generator.IsSelfAdjoint {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) : Prop :=
  (∀ φ : H, ∃ (ψ : H) (hψ : ψ ∈ gen.domain),
    gen.op ⟨ψ, hψ⟩ + (I : ℂ) • ψ = φ) ∧
  (∀ φ : H, ∃ (ψ : H) (hψ : ψ ∈ gen.domain),
    gen.op ⟨ψ, hψ⟩ - (I : ℂ) • ψ = φ)


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


lemma selfAdjoint_domain_maximal (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp) (_ /-hsa-/ : gen.IsSelfAdjoint) (ψ : H)
    (η : H) (hη : Tendsto (fun t : ℝ => ((I : ℂ) * (t : ℂ))⁻¹ • (U_grp.U t ψ - ψ))
                          (𝓝[≠] 0) (𝓝 η)) :
    ψ ∈ gen.domain := gen.domain_maximal ψ ⟨η, hη⟩



lemma selfAdjoint_generators_domain_eq (U_grp : OneParameterUnitaryGroup (H := H))
    (gen₁ gen₂ : Generator U_grp)
    (hsa₁ : gen₁.IsSelfAdjoint) (hsa₂ : gen₂.IsSelfAdjoint) :
    gen₁.domain = gen₂.domain := by
  ext ψ
  constructor
  · intro hψ₁
    have h_lim := gen₁.generator_formula (⟨ψ, hψ₁⟩ : gen₁.domain)
    exact selfAdjoint_domain_maximal U_grp gen₂ hsa₂ ψ (gen₁.op (⟨ψ, hψ₁⟩ : gen₁.domain)) h_lim
  · intro hψ₂
    have h_lim := gen₂.generator_formula (⟨ψ, hψ₂⟩ : gen₂.domain)
    exact selfAdjoint_domain_maximal U_grp gen₁ hsa₁ ψ (gen₂.op (⟨ψ, hψ₂⟩ : gen₂.domain)) h_lim


lemma generator_op_eq_on_domain (U_grp : OneParameterUnitaryGroup (H := H))
    (gen₁ gen₂ : Generator U_grp) (ψ : H)
    (hψ₁ : ψ ∈ gen₁.domain) (hψ₂ : ψ ∈ gen₂.domain) :
    gen₁.op (⟨ψ, hψ₁⟩ : gen₁.domain) = gen₂.op (⟨ψ, hψ₂⟩ : gen₂.domain) := by
  have h₁ := gen₁.generator_formula (⟨ψ, hψ₁⟩ : gen₁.domain)
  have h₂ := gen₂.generator_formula (⟨ψ, hψ₂⟩ : gen₂.domain)
  exact tendsto_nhds_unique h₁ h₂


lemma LinearMap.heq_of_eq_domain {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {D₁ D₂ : Submodule R M}
    (h_dom : D₁ = D₂) (f : D₁ →ₗ[R] N) (g : D₂ →ₗ[R] N)
    (h_eq : ∀ (x : M) (hx₁ : x ∈ D₁) (hx₂ : x ∈ D₂), f ⟨x, hx₁⟩ = g ⟨x, hx₂⟩) :
    HEq f g := by
  subst h_dom
  exact heq_of_eq (LinearMap.ext fun ⟨x, hx⟩ => h_eq x hx hx)


lemma generator_op_ext_of_eq_on_domain (U_grp : OneParameterUnitaryGroup (H := H))
    (gen₁ gen₂ : Generator U_grp)
    (h_dom : gen₁.domain = gen₂.domain)
    (h_eq : ∀ (ψ : H) (hψ₁ : ψ ∈ gen₁.domain) (hψ₂ : ψ ∈ gen₂.domain),
            gen₁.op ⟨ψ, hψ₁⟩ = gen₂.op ⟨ψ, hψ₂⟩) :
    HEq gen₁.op gen₂.op :=
  LinearMap.heq_of_eq_domain h_dom gen₁.op gen₂.op h_eq

end QuantumMechanics.Generators
