/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.Duhamel.Helpers

/-!
# Commutation Properties for Duhamel's Formula

This file proves that resolvents and Yosida approximants commute with the
unitary group, and that certain norms are constant along orbits.

## Main results

* `resolvent_commutes_unitary`: `R(z)(U(t)φ) = U(t)(R(z)φ)`
* `yosidaApproxSym_commutes_unitary`: `Aₙˢʸᵐ(U(t)φ) = U(t)(Aₙˢʸᵐφ)`
* `norm_gen_diff_constant`: `‖A(U(s)φ) - Aₙ(U(s)φ)‖` is constant in `s`

-/

namespace QuantumMechanics.Yosida

open Complex Resolvent Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U_grp : OneParameterUnitaryGroup (H := H)}



lemma resolvent_commutes_unitary
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) (φ : H) :
    Resolvent.resolvent gen z hz hsa (U_grp.U t φ) =
    U_grp.U t (Resolvent.resolvent gen z hz hsa φ) := by
  set ψ := Resolvent.resolvent gen z hz hsa φ
  have hψ_spec := resolvent_spec gen hsa z hz φ
  have hψ_dom : ψ ∈ gen.domain := hψ_spec.1
  have hψ_eq : gen.op ⟨ψ, hψ_dom⟩ - z • ψ = φ := hψ_spec.2
  have hUψ_dom : U_grp.U t ψ ∈ gen.domain := gen.domain_invariant t ψ hψ_dom
  have hUψ_eq : gen.op ⟨U_grp.U t ψ, hUψ_dom⟩ - z • (U_grp.U t ψ) = U_grp.U t φ := by
    rw [generator_commutes_unitary gen t ψ hψ_dom]
    rw [← ContinuousLinearMap.map_smul]
    rw [← ContinuousLinearMap.map_sub]
    congr 1
  set ψ' := Resolvent.resolvent gen z hz hsa (U_grp.U t φ)
  have hψ'_spec := resolvent_spec gen hsa z hz (U_grp.U t φ)
  have hψ'_dom : ψ' ∈ gen.domain := hψ'_spec.1
  have hψ'_eq : gen.op ⟨ψ', hψ'_dom⟩ - z • ψ' = U_grp.U t φ := hψ'_spec.2
  have h_diff_dom : ψ' - U_grp.U t ψ ∈ gen.domain := gen.domain.sub_mem hψ'_dom hUψ_dom
  have h_diff : ψ' - U_grp.U t ψ = 0 := by
    apply resolvent_unique gen z hz (ψ' - U_grp.U t ψ) h_diff_dom
    have h1 : gen.op ⟨ψ' - U_grp.U t ψ, h_diff_dom⟩ =
              gen.op ⟨ψ', hψ'_dom⟩ - gen.op ⟨U_grp.U t ψ, hUψ_dom⟩ := by
      have := gen.op.map_sub ⟨ψ', hψ'_dom⟩ ⟨U_grp.U t ψ, hUψ_dom⟩
      convert this using 2
    rw [h1, smul_sub, sub_sub_sub_comm, hψ'_eq, hUψ_eq, sub_self]
  exact sub_eq_zero.mp h_diff

lemma yosidaApproxSym_commutes_unitary
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (φ : H) :
    yosidaApproxSym gen hsa n (U_grp.U t φ) = U_grp.U t (yosidaApproxSym gen hsa n φ) := by
  unfold yosidaApproxSym
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
  unfold resolventAtIn resolventAtNegIn
  rw [resolvent_commutes_unitary gen hsa _ _ t φ]
  rw [resolvent_commutes_unitary gen hsa _ _ t φ]
  simp only [neg_mul, smul_add, map_add, map_smul]

lemma norm_gen_diff_constant
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (s : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    ‖gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s φ)‖ =
    ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖ := by
  rw [generator_commutes_unitary gen s φ hφ]
  rw [yosidaApproxSym_commutes_unitary gen hsa n s φ]
  rw [← ContinuousLinearMap.map_sub]
  exact norm_preserving U_grp s (gen.op ⟨φ, hφ⟩ - (yosidaApproxSym gen hsa n) φ)

end QuantumMechanics.Yosida
