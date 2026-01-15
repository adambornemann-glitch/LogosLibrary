/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent

/-!
# Basic Lemmas for Yosida Approximation

This file contains foundational arithmetic lemmas about `I * n` for positive naturals,
and basic resolvent specifications needed for the Yosida approximation construction.

## Main results

* `I_mul_pnat_im_ne_zero`: `(I * n).im ≠ 0` for `n : ℕ+`
* `neg_I_mul_pnat_im_ne_zero`: `(-I * n).im ≠ 0` for `n : ℕ+`
* `resolvent_spec`: The resolvent satisfies `(A - z)R(z)φ = φ`

-/

namespace QuantumMechanics.Yosida

open Complex QuantumMechanics.Resolvent Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Arithmetic lemmas for `I * n` -/

lemma I_mul_pnat_im_ne_zero (n : ℕ+) : (I * (n : ℂ)).im ≠ 0 := by
  simp only [mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
  exact Nat.cast_ne_zero.mpr n.ne_zero

lemma neg_I_mul_pnat_im_ne_zero (n : ℕ+) : (-I * (n : ℂ)).im ≠ 0 := by
  simp only [neg_mul, neg_im]
  exact neg_ne_zero.mpr (I_mul_pnat_im_ne_zero n)

lemma I_mul_pnat_im (n : ℕ+) : (I * (n : ℂ)).im = (n : ℝ) := by
  simp [mul_im]

lemma abs_I_mul_pnat_im (n : ℕ+) : |(I * (n : ℂ)).im| = (n : ℝ) := by
  rw [I_mul_pnat_im]
  exact abs_of_pos (Nat.cast_pos.mpr n.pos)

lemma norm_pnat_sq (n : ℕ+) : ‖((n : ℂ)^2)‖ = (n : ℝ)^2 := by
  rw [norm_pow]
  simp

lemma norm_I_mul_pnat (n : ℕ+) : ‖I * (n : ℂ)‖ = (n : ℝ) := by
  calc ‖I * (n : ℂ)‖
      = ‖I‖ * ‖(n : ℂ)‖ := norm_mul I (n : ℂ)
    _ = 1 * ‖(n : ℂ)‖ := by rw [norm_I]
    _ = ‖(n : ℂ)‖ := one_mul _
    _ = (n : ℝ) := by simp only [norm_natCast]

/-! ### Resolvent specifications -/

lemma resolvent_spec
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : ℂ) (hz : z.im ≠ 0) (φ : H) :
    (Resolvent.resolvent gen z hz hsa φ) ∈ gen.domain ∧
    gen.op ⟨Resolvent.resolvent gen z hz hsa φ,
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists).property⟩ -
    z • (Resolvent.resolvent gen z hz hsa φ) = φ := by
  let ψ_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists
  have h_mem : (ψ_sub : H) ∈ gen.domain := ψ_sub.property
  have h_eq := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists
  constructor
  · exact h_mem
  · convert h_eq using 2

lemma resolvent_spec'
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : ℂ) (hz : z.im ≠ 0) (φ : H) :
    ∃ (h : Resolvent.resolvent gen z hz hsa φ ∈ gen.domain),
      gen.op ⟨Resolvent.resolvent gen z hz hsa φ, h⟩ -
      z • (Resolvent.resolvent gen z hz hsa φ) = φ := by
  let ψ_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists
  have h_eq := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists
  exact ⟨ψ_sub.property, h_eq⟩

end QuantumMechanics.Yosida
