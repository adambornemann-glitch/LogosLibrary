/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.LowerBound
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.SpecialCases
/-!
# Neumann Series Expansion for the Resolvent

This file proves local existence of the resolvent near `z = i` using the
Neumann series expansion. Since `‖R(i)‖ ≤ 1`, for any `z` with `‖z - i‖ < 1`
we can express `R(z) = R(i)(1 - (z-i)R(i))⁻¹` via the geometric series.

## Main results

* `resolvent_near_i`: For `Im(z) > 0` and `‖z - i‖ < 1`, the equation
  `(A - zI)ψ = φ` has a unique solution for every `φ ∈ H`.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3
-/

namespace QuantumMechanics.Resolvent

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Local resolvent near i -/

/-- Near `z = i`, existence follows from Neumann series expansion. -/
lemma resolvent_near_i {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im > 0) (h_close : ‖z - I‖ < 1) :
    ∀ φ : H, ∃! (ψ : gen.domain), gen.op ψ - z • (ψ : H) = φ := by
  intro φ
  let R := resolvent_at_i gen hsa
  let lambda_val := z - I
  have h_op_bound : ‖lambda_val • R‖ < 1 := by
    calc ‖lambda_val • R‖
        = ‖lambda_val‖ * ‖R‖ := norm_smul lambda_val R
      _ ≤ ‖lambda_val‖ * 1 := by
          apply mul_le_mul_of_nonneg_left
          · exact resolvent_at_i_bound gen hsa
          · exact norm_nonneg _
      _ = ‖z - I‖ := by ring
      _ < 1 := h_close
  have h_exists : ∃ (ψ : gen.domain), gen.op ψ - z • (ψ : H) = φ := by
    let T := lambda_val • R
    let S := neumannSeries T h_op_bound
    let η := S φ
    let ψ_val := R η
    have h_ψ_mem : ψ_val ∈ gen.domain := resolvent_solution_mem gen hsa η
    have h_ψ_eq : gen.op ⟨ψ_val, h_ψ_mem⟩ - I • ψ_val = η := resolvent_solution_eq gen hsa η
    use ⟨ψ_val, h_ψ_mem⟩
    have h_neumann_eq : η - T η = φ := by
      have h_inv := neumannSeries_mul_left T h_op_bound
      calc η - T η
          = (ContinuousLinearMap.id ℂ H - T) η := by simp [T]
        _ = ((ContinuousLinearMap.id ℂ H - T) * S) φ := by simp [η, S]
        _ = ContinuousLinearMap.id ℂ H φ := by rw [h_inv]
        _ = φ := rfl
    calc gen.op ⟨ψ_val, h_ψ_mem⟩ - z • ψ_val
        = gen.op ⟨ψ_val, h_ψ_mem⟩ - (I + lambda_val) • ψ_val := by simp [lambda_val]
      _ = gen.op ⟨ψ_val, h_ψ_mem⟩ - I • ψ_val - lambda_val • ψ_val := by rw [add_smul]; abel
      _ = η - lambda_val • ψ_val := by rw [h_ψ_eq]
      _ = η - lambda_val • (R η) := rfl
      _ = η - (lambda_val • R) η := by rfl
      _ = η - T η := rfl
      _ = φ := h_neumann_eq
  obtain ⟨ψ, hψ⟩ := h_exists
  use ψ, hψ
  intro ψ' hψ'
  have h_sub_mem : (ψ : H) - (ψ' : H) ∈ gen.domain :=
    gen.domain.sub_mem ψ.property ψ'.property
  have h_diff : gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ - z • ((ψ : H) - (ψ' : H)) = 0 := by
    have op_sub := gen.op.map_sub ψ ψ'
    have op_eq : gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ = gen.op ψ - gen.op ψ' := by
      convert op_sub using 1
    calc gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ - z • ((ψ : H) - (ψ' : H))
        = (gen.op ψ - gen.op ψ') - z • ((ψ : H) - (ψ' : H)) := by rw [op_eq]
      _ = (gen.op ψ - gen.op ψ') - (z • (ψ : H) - z • (ψ' : H)) := by rw [smul_sub]
      _ = (gen.op ψ - z • (ψ : H)) - (gen.op ψ' - z • (ψ' : H)) := by abel
      _ = φ - φ := by rw [hψ, hψ']
      _ = 0 := sub_self φ
  have h_im_ne : z.im ≠ 0 := ne_of_gt hz
  have h_bound := lower_bound_estimate gen z h_im_ne ((ψ : H) - (ψ' : H)) h_sub_mem
  rw [h_diff] at h_bound
  simp only [norm_zero, ge_iff_le] at h_bound
  have h_im_pos : 0 < |z.im| := abs_pos.mpr h_im_ne
  have h_norm_zero : ‖(ψ : H) - (ψ' : H)‖ = 0 := by
    by_contra h_ne
    have h_pos : 0 < ‖(ψ : H) - (ψ' : H)‖ := by
      cases' (norm_nonneg ((ψ : H) - (ψ' : H))).lt_or_eq with h h
      · exact h
      · exact absurd h.symm h_ne
    have : 0 < |z.im| * ‖(ψ : H) - (ψ' : H)‖ := mul_pos h_im_pos h_pos
    linarith
  have h_eq : (ψ : H) = (ψ' : H) := sub_eq_zero.mp (norm_eq_zero.mp h_norm_zero)
  exact Subtype.ext h_eq.symm
