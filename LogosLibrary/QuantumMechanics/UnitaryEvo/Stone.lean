/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: UnitaryEvo/Stone.lean
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent
/-!
# Stone's Theorem: Complete Statement

This file assembles the complete Stone's theorem, establishing a bijective
correspondence between strongly continuous one-parameter unitary groups and
self-adjoint operators on a Hilbert space.

## Main statements

* `stone_existence`: Every strongly continuous one-parameter unitary group
  has a self-adjoint generator.
* `stone_uniqueness`: The self-adjoint generator is unique.
* `stone_part_one`: Existence and uniqueness combined: ∃! self-adjoint generator.
* `stone_exponential_eq_group`: U(t) = exp(itA) for the generator A.
* `stone_exponential_is_unitary_group`: exp(itA) satisfies all unitary group axioms.
* `stone_generator_of_exponential`: The generator of exp(itA) is A.
* `stone_bijection`: The complete bijection statement.

## The theorem

**Stone's Theorem.** Let H be a complex Hilbert space. There is a bijective
correspondence between:
- Strongly continuous one-parameter unitary groups {U(t)}_{t∈ℝ} on H
- Self-adjoint operators A on H

given by U(t) = exp(itA), where the generator A is defined by
  Aψ = lim_{t→0} (it)⁻¹(U(t)ψ - ψ)
on the domain of vectors where this limit exists.

## Structure of the proof

**Forward direction** (Bochner.lean):
1. Define the generator via the strong limit formula
2. Prove density of the domain using averaged vectors
3. Establish symmetry from the unitary property
4. Prove self-adjointness via deficiency indices (surjectivity of A ± iI)

**Reverse direction** (Yosida.lean):
1. Approximate unbounded A by bounded Yosida approximants Aₙ
2. exp(i·Aₙ·t) is unitary since i·Aₙ is skew-adjoint
3. Duhamel's formula controls U(t) - exp(i·Aₙ·t)
4. Convergence Aₙ → A on domain implies exp(i·Aₙ·t) → U(t)

**Uniqueness** (Generator.lean):
Self-adjoint generators of the same group agree on their common domain,
and maximality forces the domains to coincide.

## References

* [Stone, "On one-parameter unitary groups in Hilbert space"][stone1932]
* [von Neumann, "Über Funktionen von Funktionaloperatoren"][vonneumann1932]
* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Theorem VIII.8

## Tags

Stone's theorem, unitary group, self-adjoint operator, spectral theory
-/
namespace QuantumMechanics.StonesTheorem

open InnerProductSpace Complex Filter Topology
open QuantumMechanics.Yosida QuantumMechanics.Resolvent QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


lemma stone_existence (U_grp : OneParameterUnitaryGroup (H := H)) :
    ∃ (gen : Generator U_grp), gen.IsSelfAdjoint :=
  ⟨Generator.ofUnitaryGroup U_grp, Generator.ofUnitaryGroup_isSelfAdjoint U_grp⟩


lemma stone_uniqueness
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen₁ gen₂ : Generator U_grp)
    (hsa₁ : gen₁.IsSelfAdjoint)
    (hsa₂ : gen₂.IsSelfAdjoint) :
    HEq gen₁.op gen₂.op ∧ gen₁.domain = gen₂.domain := by

  have h_dom := selfAdjoint_generators_domain_eq U_grp gen₁ gen₂ hsa₁ hsa₂

  have h_eq_on_dom : ∀ (ψ : H) (hψ₁ : ψ ∈ gen₁.domain) (hψ₂ : ψ ∈ gen₂.domain),
      gen₁.op ⟨ψ, hψ₁⟩ = gen₂.op ⟨ψ, hψ₂⟩ := by
    intro ψ hψ₁ hψ₂
    exact generator_op_eq_on_domain U_grp gen₁ gen₂ ψ hψ₁ hψ₂

  have h_op := generator_op_ext_of_eq_on_domain U_grp gen₁ gen₂ h_dom h_eq_on_dom

  exact ⟨h_op, h_dom⟩


lemma stone_part_one (U_grp : OneParameterUnitaryGroup (H := H)) :
    ∃! (gen : Generator U_grp), gen.IsSelfAdjoint := by
  obtain ⟨gen, hsa⟩ := stone_existence U_grp
  refine ⟨gen, hsa, ?_⟩
  intro gen' hsa'
  have ⟨h_op, h_dom⟩ := stone_uniqueness U_grp gen gen' hsa hsa'
  cases gen with
  | mk op domain dense_domain generator_formula domain_invariant symmetric domain_maximal =>
    cases gen' with
    | mk op' domain' dense_domain' generator_formula' domain_invariant' symmetric' domain_maximal' =>
      simp only at h_op h_dom
      subst h_dom
      simp only [heq_eq_eq] at h_op
      subst h_op
      rfl


lemma stone_exponential_eq_group
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ : H) :
    exponential gen hsa h_dense t ψ = U_grp.U t ψ := by

  have h_agree_on_domain : ∀ φ ∈ gen.domain, exponential gen hsa h_dense t φ = U_grp.U t φ := by
    intro φ hφ
    have h_tendsto := expBounded_yosidaApproxSym_tendsto_unitary gen hsa h_dense t φ hφ
    have h_exp_tendsto := exponential_tendsto gen hsa h_dense t φ
    exact tendsto_nhds_unique h_exp_tendsto h_tendsto

  have h_exp_isometry : ∀ χ : H, ‖exponential gen hsa h_dense t χ‖ = ‖χ‖ := by
    intro χ
    have h := exponential_unitary gen hsa h_dense t χ χ
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h_sq : ‖exponential gen hsa h_dense t χ‖^2 = ‖χ‖^2 := by exact_mod_cast h
    nlinarith [sq_nonneg (‖exponential gen hsa h_dense t χ‖ - ‖χ‖),
               sq_nonneg (‖exponential gen hsa h_dense t χ‖ + ‖χ‖),
               norm_nonneg (exponential gen hsa h_dense t χ), norm_nonneg χ]

  have h_U_isometry : ∀ χ : H, ‖U_grp.U t χ‖ = ‖χ‖ := by
    intro χ
    have h := U_grp.unitary t χ χ
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h_sq : ‖U_grp.U t χ‖^2 = ‖χ‖^2 := by exact_mod_cast h
    nlinarith [sq_nonneg (‖U_grp.U t χ‖ - ‖χ‖),
               sq_nonneg (‖U_grp.U t χ‖ + ‖χ‖),
               norm_nonneg (U_grp.U t χ), norm_nonneg χ]

  apply eq_of_forall_dist_le
  intro ε hε

  have hε2 : ε / 2 > 0 := by linarith
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp
    (h_dense.closure_eq ▸ Set.mem_univ ψ) (ε / 2) hε2
  rw [dist_eq_norm] at hφ_close ⊢

  calc ‖exponential gen hsa h_dense t ψ - U_grp.U t ψ‖
      = ‖(exponential gen hsa h_dense t ψ - exponential gen hsa h_dense t φ) +
         (exponential gen hsa h_dense t φ - U_grp.U t φ) +
         (U_grp.U t φ - U_grp.U t ψ)‖ := by congr 1; abel
    _ ≤ ‖exponential gen hsa h_dense t ψ - exponential gen hsa h_dense t φ‖ +
        ‖exponential gen hsa h_dense t φ - U_grp.U t φ‖ +
        ‖U_grp.U t φ - U_grp.U t ψ‖ := by
          apply le_trans (norm_add_le _ _)
          gcongr
          exact norm_add_le _ _
    _ = ‖exponential gen hsa h_dense t (ψ - φ)‖ + 0 + ‖U_grp.U t (φ - ψ)‖ := by
          rw [← map_sub, ← map_sub, h_agree_on_domain φ hφ_mem, sub_self, norm_zero]
    _ = ‖ψ - φ‖ + 0 + ‖φ - ψ‖ := by
          rw [h_exp_isometry, h_U_isometry]
    _ = 2 * ‖ψ - φ‖ := by rw [norm_sub_rev]; ring
    _ ≤ 2 * (ε / 2) := by linarith [hφ_close]
    _ = ε := by ring


lemma stone_exponential_is_unitary_group
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H)) :
    (∀ t ψ φ, ⟪exponential gen hsa h_dense t ψ, exponential gen hsa h_dense t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ) ∧
    (∀ s t ψ, exponential gen hsa h_dense (s + t) ψ = exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ)) ∧
    (∀ ψ, exponential gen hsa h_dense 0 ψ = ψ) ∧
    (∀ ψ, Continuous (fun t => exponential gen hsa h_dense t ψ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun t ψ φ => exponential_unitary gen hsa h_dense t ψ φ
  · exact fun s t ψ => exponential_group_law gen hsa h_dense s t ψ
  · exact fun ψ => exponential_identity gen hsa h_dense ψ
  · exact fun ψ => exponential_strong_continuous gen hsa h_dense ψ


lemma stone_generator_of_exponential
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    Tendsto (fun t : ℝ => ((I * t)⁻¹ : ℂ) • (exponential gen hsa h_dense t ψ - ψ))
            (𝓝[≠] 0) (𝓝 (gen.op ⟨ψ, hψ⟩)) := by

  have h := exponential_generator_eq gen hsa h_dense ψ hψ

  have h_convert : ∀ t : ℝ, t ≠ 0 →
      ((I * (t : ℂ))⁻¹ : ℂ) • (exponential gen hsa h_dense t ψ - ψ) =
      (-I) • ((t⁻¹ : ℂ) • (exponential gen hsa h_dense t ψ - ψ)) := by
    intro t ht
    rw [← smul_assoc]
    congr 1
    rw [mul_inv_rev, mul_comm ((t : ℂ))⁻¹, Complex.inv_I, ← Complex.ofReal_inv]
    rfl

  have h_lim := h.const_smul (-I)

  have h_simp : (-I) • I • gen.op ⟨ψ, hψ⟩ = gen.op ⟨ψ, hψ⟩ := by
    rw [smul_smul]
    simp only [neg_mul, I_mul_I, neg_neg, one_smul]
  rw [h_simp] at h_lim

  exact h_lim.congr' (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (h_convert t ht).symm)


theorem stone_bijection :
    ∀ (U_grp : OneParameterUnitaryGroup (H := H)),
    ∃! (gen : Generator U_grp), gen.IsSelfAdjoint ∧
      (∀ (hsa : gen.IsSelfAdjoint) (h_dense : Dense (gen.domain : Set H)),
        ∀ t ψ, U_grp.U t ψ = exponential gen hsa h_dense t ψ) := by

  intro U_grp
  obtain ⟨gen, hsa, h_unique⟩ := stone_part_one U_grp
  refine ⟨gen, ⟨hsa, ?_⟩, ?_⟩
  · intro hsa' h_dense t ψ
    exact (stone_exponential_eq_group U_grp gen hsa' h_dense t ψ).symm
  · intro gen' ⟨hsa', _⟩
    exact h_unique gen' hsa'



end QuantumMechanics.StonesTheorem
