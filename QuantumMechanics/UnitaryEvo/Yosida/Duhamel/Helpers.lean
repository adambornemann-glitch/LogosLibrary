/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.ExpBounded.Unitary

/-!
# Helper Lemmas for Duhamel's Formula

This file contains utility lemmas about unitary groups, generators, and their
interactions needed for the Duhamel formula and estimates.

## Main results

* `unitary_group_at_zero`: `U(0) = id`
* `U_neg_eq_adjoint`: `U(-t) = U(t)*`
* `U_norm_preserving`: `‖U(t)φ‖ = ‖φ‖`
* `generator_commutes_unitary`: `A(U(t)φ) = U(t)(Aφ)` on domain
* `resolvent_unique`: Solutions to `(A - z)ψ = 0` with `z.im ≠ 0` are unique
* `smul_I_skewSelfAdjoint`: `i·A` is skew-adjoint when `A` is self-adjoint

-/

namespace QuantumMechanics.Yosida

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Resolvent QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U_grp : OneParameterUnitaryGroup (H := H)}

/-! ### Basic unitary group properties -/

lemma U_neg_eq_adjoint (t : ℝ) :
    U_grp.U (-t) = ContinuousLinearMap.adjoint (U_grp.U t) := by
  ext φ
  apply ext_inner_left ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_right]
  have h_inv : U_grp.U (-t) (U_grp.U t ψ) = ψ := by
    have := U_grp.group_law (-t) t
    simp only [neg_add_cancel] at this
    rw [U_grp.identity] at this
    rw [← ContinuousLinearMap.comp_apply, ← this, ContinuousLinearMap.id_apply]
  have h := U_grp.unitary (-t) (U_grp.U t ψ) φ
  rw [h_inv] at h
  exact h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {U_grp : OneParameterUnitaryGroup (H := H)}

lemma unitary_group_at_zero (ψ : H) : U_grp.U 0 ψ = ψ := by
  rw [U_grp.identity]
  simp only [ContinuousLinearMap.id_apply]

lemma unitary_group_domain_invariant
    (gen : Generator U_grp)
    (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    U_grp.U t φ ∈ gen.domain :=
  gen.domain_invariant t φ hφ

/-! ### Generator commutation -/

lemma generator_commutes_unitary
    (gen : Generator U_grp)
    (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    gen.op ⟨U_grp.U t φ, gen.domain_invariant t φ hφ⟩ = U_grp.U t (gen.op ⟨φ, hφ⟩) := by
  have hUtφ : U_grp.U t φ ∈ gen.domain := gen.domain_invariant t φ hφ
  have h_gen_Utφ := gen.generator_formula ⟨U_grp.U t φ, hUtφ⟩
  have h_gen_φ := gen.generator_formula ⟨φ, hφ⟩
  have h_key : ∀ s : ℝ, U_grp.U s (U_grp.U t φ) - U_grp.U t φ = U_grp.U t (U_grp.U s φ - φ) := by
    intro s
    have h1 : U_grp.U s (U_grp.U t φ) = U_grp.U (s + t) φ := by
      rw [U_grp.group_law]
      rfl
    have h2 : U_grp.U (s + t) φ = U_grp.U (t + s) φ := by
      rw [add_comm]
    have h3 : U_grp.U (t + s) φ = U_grp.U t (U_grp.U s φ) := by
      rw [U_grp.group_law]
      rfl
    calc U_grp.U s (U_grp.U t φ) - U_grp.U t φ
        = U_grp.U t (U_grp.U s φ) - U_grp.U t φ := by rw [h1, h2, h3]
      _ = U_grp.U t (U_grp.U s φ) - U_grp.U t φ := rfl
      _ = U_grp.U t (U_grp.U s φ - φ) := by rw [ContinuousLinearMap.map_sub]
  have h_eq_seq : ∀ s : ℝ, (I * s)⁻¹ • (U_grp.U s (U_grp.U t φ) - U_grp.U t φ) =
                          U_grp.U t ((I * s)⁻¹ • (U_grp.U s φ - φ)) := by
    intro s
    rw [h_key s, ContinuousLinearMap.map_smul]
  have h_rhs_tendsto : Tendsto (fun s : ℝ => U_grp.U t ((I * (s : ℂ))⁻¹ • (U_grp.U s φ - φ)))
                               (𝓝[≠] 0) (𝓝 (U_grp.U t (gen.op ⟨φ, hφ⟩))) := by
    apply Filter.Tendsto.comp (U_grp.U t).continuous.continuousAt h_gen_φ
  have h_limits_eq := tendsto_nhds_unique h_gen_Utφ (h_rhs_tendsto.congr (fun s => (h_eq_seq s).symm))
  exact h_limits_eq

lemma U_norm_preserving (U_grp : OneParameterUnitaryGroup (H := H)) (t : ℝ) (φ : H) :
    ‖U_grp.U t φ‖ = ‖φ‖ := by
  have h := U_grp.unitary t φ φ
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), h]


/-! ### Resolvent uniqueness -/
lemma resolvent_unique {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (z : ℂ) (hz : z.im ≠ 0)
    (ψ : H) (hψ : ψ ∈ gen.domain)
    (h : gen.op ⟨ψ, hψ⟩ - z • ψ = 0) : ψ = 0 := by
  -- If Aψ = zψ with z.im ≠ 0, then ψ = 0
  have h_eq : gen.op ⟨ψ, hψ⟩ = z • ψ := by
    rw [sub_eq_zero] at h; exact h
  -- ⟪ψ, Aψ⟫ = z * ⟪ψ, ψ⟫
  have h1 : ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ = z * ⟪ψ, ψ⟫_ℂ := by
    rw [h_eq, inner_smul_right];
  -- By symmetry: ⟪Aψ, ψ⟫ = ⟪ψ, Aψ⟫
  have h2 : ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ = ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ :=
    gen.symmetric ⟨ψ, hψ⟩ ⟨ψ, hψ⟩
  -- Also ⟪Aψ, ψ⟫ = conj ⟪ψ, Aψ⟫ (inner product conjugate symmetry)
  have h3 : ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ = starRingEnd ℂ ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ :=
    (inner_conj_symm (gen.op ⟨ψ, hψ⟩) ψ).symm
  -- So ⟪ψ, Aψ⟫ = conj ⟪ψ, Aψ⟫, meaning ⟪ψ, Aψ⟫ is real
  have h4 : ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ = starRingEnd ℂ ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ := by
    rw [← h3, h2]
  -- z * ⟪ψ, ψ⟫ is real
  rw [h1] at h4
  -- ⟪ψ, ψ⟫ = ‖ψ‖² which is real and non-negative
  have h5 : ⟪ψ, ψ⟫_ℂ = (‖ψ‖ : ℂ)^2 := inner_self_eq_norm_sq_to_K ψ
  rw [h5] at h4
  -- z * ‖ψ‖² = conj(z * ‖ψ‖²) = conj(z) * ‖ψ‖²
  simp only [map_mul] at h4
  -- (z - conj z) * ‖ψ‖² = 0
  have h6 : (z - starRingEnd ℂ z) * (‖ψ‖ : ℂ)^2 = 0 := by
    rw [sub_mul, h4]
    simp_all only [ne_eq, sub_self, map_pow, conj_ofReal, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply,
      mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, ofReal_eq_zero, norm_eq_zero]
  -- z - conj z = 2i * im(z) ≠ 0
  have h7 : z - starRingEnd ℂ z ≠ 0 := by
    rw [sub_conj]
    intro h
    simp only [mul_eq_zero, ofReal_eq_zero, I_ne_zero, or_false] at h
    simp_all only [ne_eq, sub_self, map_pow, conj_ofReal, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply,
      mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, ofReal_eq_zero, norm_eq_zero,
      mul_eq_zero, or_self]
  -- So ‖ψ‖² = 0, hence ψ = 0
  have h8 : (‖ψ‖ : ℂ)^2 = 0 := by
    cases mul_eq_zero.mp h6 with
    | inl h => exact absurd h h7
    | inr h => exact h
  have h9 : ‖ψ‖ = 0 := by
    have : (‖ψ‖ : ℂ) = 0 := pow_eq_zero h8
    exact_mod_cast this
  exact norm_eq_zero.mp h9


end QuantumMechanics.Yosida
