/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.NormExpansion

/-!
# Resolvent at ±i

This file constructs the resolvent operators at `z = ±i` directly from the
self-adjointness criterion. These special cases are used to bootstrap the
general resolvent construction.

## Main definitions

* `resolvent_at_i`: The resolvent `R(i) = (A - iI)⁻¹`
* `resolvent_at_neg_i`: The resolvent `R(-i) = (A + iI)⁻¹`

## Main statements

* `resolvent_at_i_unique`: Solutions to `(A - iI)ψ = φ` are unique
* `resolvent_at_neg_i_unique`: Solutions to `(A + iI)ψ = φ` are unique
* `resolvent_at_i_bound`: `‖R(i)‖ ≤ 1`

## Implementation notes

The self-adjointness criterion states that `ran(A ± iI) = H`. We use
`Classical.choose` to extract solutions and prove they are unique using
the lower bound estimate from `NormExpansion`.
-/

namespace QuantumMechanics.Resolvent

open InnerProductSpace MeasureTheory Complex Filter Topology
open QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## Resolvent at i -/

lemma resolvent_at_i_spec {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    ∃ (ψ : gen.domain), gen.op ψ - I • (ψ : H) = φ := by
  obtain ⟨ψ, hψ, h_eq⟩ := hsa.2 φ
  exact ⟨⟨ψ, hψ⟩, h_eq⟩

lemma resolvent_at_i_unique {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (_ : Generator.IsSelfAdjoint gen)
    (φ ψ₁ ψ₂ : H)
    (hψ₁ : ψ₁ ∈ gen.domain) (hψ₂ : ψ₂ ∈ gen.domain)
    (h₁ : gen.op ⟨ψ₁, hψ₁⟩ - I • ψ₁ = φ)
    (h₂ : gen.op ⟨ψ₂, hψ₂⟩ - I • ψ₂ = φ) :
    ψ₁ = ψ₂ := by
  have h_sub_mem : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem hψ₁ hψ₂
  have h_factor : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ - I • (ψ₁ - ψ₂) = 0 := by
    have op_sub := gen.op.map_sub ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩
    calc gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ - I • (ψ₁ - ψ₂)
        = (gen.op ⟨ψ₁, hψ₁⟩ - gen.op ⟨ψ₂, hψ₂⟩) - I • (ψ₁ - ψ₂) :=
          congrFun (congrArg HSub.hSub op_sub) (I • (ψ₁ - ψ₂))
      _ = (gen.op ⟨ψ₁, hψ₁⟩ - gen.op ⟨ψ₂, hψ₂⟩) - (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
      _ = (gen.op ⟨ψ₁, hψ₁⟩ - I • ψ₁) - (gen.op ⟨ψ₂, hψ₂⟩ - I • ψ₂) := by abel
      _ = φ - φ := by rw [h₁, h₂]
      _ = 0 := sub_self φ
  -- From the norm expansion: ‖ψ‖ ≤ ‖Aψ - Iψ‖
  have h_le := norm_le_norm_sub_I_smul gen ⟨ψ₁ - ψ₂, h_sub_mem⟩
  simp only at h_le
  have : ‖ψ₁ - ψ₂‖ ≤ 0 := by
    calc ‖ψ₁ - ψ₂‖
        ≤ ‖gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ - I • (ψ₁ - ψ₂)‖ := h_le
      _ = ‖(0 : H)‖ := by rw [h_factor]
      _ = 0 := norm_zero
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm this (norm_nonneg _)))

lemma resolvent_solution_mem {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    Classical.choose (hsa.2 φ) ∈ gen.domain :=
  Classical.choose (Classical.choose_spec (hsa.2 φ))

lemma resolvent_solution_eq {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    gen.op ⟨Classical.choose (hsa.2 φ), resolvent_solution_mem gen hsa φ⟩ -
    I • Classical.choose (hsa.2 φ) = φ :=
  Classical.choose_spec (Classical.choose_spec (hsa.2 φ))

/-- The resolvent at `z = i`, constructed via the self-adjointness criterion. -/
noncomputable def resolvent_at_i {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H where
  toFun φ := Classical.choose (hsa.2 φ)
  map_add' φ₁ φ₂ := by
    let R₁ := Classical.choose (hsa.2 φ₁)
    let R₂ := Classical.choose (hsa.2 φ₂)
    let R_sum := Classical.choose (hsa.2 (φ₁ + φ₂))
    have h₁_mem : R₁ ∈ gen.domain := resolvent_solution_mem gen hsa φ₁
    have h₂_mem : R₂ ∈ gen.domain := resolvent_solution_mem gen hsa φ₂
    have h_sum_mem : R_sum ∈ gen.domain := resolvent_solution_mem gen hsa (φ₁ + φ₂)
    have h₁_eq := resolvent_solution_eq gen hsa φ₁
    have h₂_eq := resolvent_solution_eq gen hsa φ₂
    have h_sum_eq := resolvent_solution_eq gen hsa (φ₁ + φ₂)
    have h_add_mem : R₁ + R₂ ∈ gen.domain := gen.domain.add_mem h₁_mem h₂_mem
    have h_add_eq : gen.op ⟨R₁ + R₂, h_add_mem⟩ - I • (R₁ + R₂) = φ₁ + φ₂ := by
      have op_add := gen.op.map_add ⟨R₁, h₁_mem⟩ ⟨R₂, h₂_mem⟩
      calc gen.op ⟨R₁ + R₂, h_add_mem⟩ - I • (R₁ + R₂)
          = (gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩) - I • (R₁ + R₂) :=
            congrFun (congrArg HSub.hSub op_add) (I • (R₁ + R₂))
        _ = (gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩) - (I • R₁ + I • R₂) := by rw [smul_add]
        _ = (gen.op ⟨R₁, h₁_mem⟩ - I • R₁) + (gen.op ⟨R₂, h₂_mem⟩ - I • R₂) := by abel
        _ = φ₁ + φ₂ := by rw [h₁_eq, h₂_eq]
    exact (resolvent_at_i_unique gen hsa (φ₁ + φ₂) (R₁ + R₂) R_sum
      h_add_mem h_sum_mem h_add_eq h_sum_eq).symm
  map_smul' c φ := by
    let R_φ := Classical.choose (hsa.2 φ)
    let R_scaled := Classical.choose (hsa.2 (c • φ))
    have h_mem : R_φ ∈ gen.domain := resolvent_solution_mem gen hsa φ
    have h_scaled_mem : R_scaled ∈ gen.domain := resolvent_solution_mem gen hsa (c • φ)
    have h_eq := resolvent_solution_eq gen hsa φ
    have h_scaled_eq := resolvent_solution_eq gen hsa (c • φ)
    have h_smul_mem : c • R_φ ∈ gen.domain := gen.domain.smul_mem c h_mem
    have h_smul_eq : gen.op ⟨c • R_φ, h_smul_mem⟩ - I • (c • R_φ) = c • φ := by
      have op_smul := gen.op.map_smul c ⟨R_φ, h_mem⟩
      calc gen.op ⟨c • R_φ, h_smul_mem⟩ - I • (c • R_φ)
          = c • gen.op ⟨R_φ, h_mem⟩ - I • (c • R_φ) :=
            congrFun (congrArg HSub.hSub op_smul) (I • c • R_φ)
        _ = c • gen.op ⟨R_φ, h_mem⟩ - c • (I • R_φ) := by rw [smul_comm]
        _ = c • (gen.op ⟨R_φ, h_mem⟩ - I • R_φ) := by rw [smul_sub]
        _ = c • φ := by rw [h_eq]
    exact (resolvent_at_i_unique gen hsa (c • φ) (c • R_φ) R_scaled
      h_smul_mem h_scaled_mem h_smul_eq h_scaled_eq).symm
  cont := by
    have lipschitz : LipschitzWith 1 (fun φ => Classical.choose (hsa.2 φ)) := by
      refine LipschitzWith.of_edist_le ?_
      intro φ₁ φ₂
      let ψ₁ := Classical.choose (hsa.2 φ₁)
      let ψ₂ := Classical.choose (hsa.2 φ₂)
      have h₁_mem : ψ₁ ∈ gen.domain := resolvent_solution_mem gen hsa φ₁
      have h₂_mem : ψ₂ ∈ gen.domain := resolvent_solution_mem gen hsa φ₂
      have h₁_eq := resolvent_solution_eq gen hsa φ₁
      have h₂_eq := resolvent_solution_eq gen hsa φ₂
      have h_sub_mem : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem h₁_mem h₂_mem
      have h_diff : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ - I • (ψ₁ - ψ₂) = φ₁ - φ₂ := by
        have op_sub := gen.op.map_sub ⟨ψ₁, h₁_mem⟩ ⟨ψ₂, h₂_mem⟩
        calc gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ - I • (ψ₁ - ψ₂)
            = (gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩) - I • (ψ₁ - ψ₂) :=
              congrFun (congrArg HSub.hSub op_sub) (I • (ψ₁ - ψ₂))
          _ = (gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩) - (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
          _ = (gen.op ⟨ψ₁, h₁_mem⟩ - I • ψ₁) - (gen.op ⟨ψ₂, h₂_mem⟩ - I • ψ₂) := by abel
          _ = φ₁ - φ₂ := by rw [h₁_eq, h₂_eq]
      have h_le := norm_le_norm_sub_I_smul gen ⟨ψ₁ - ψ₂, h_sub_mem⟩
      have bound : ‖ψ₁ - ψ₂‖ ≤ ‖φ₁ - φ₂‖ := by
        calc ‖ψ₁ - ψ₂‖
            ≤ ‖gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ - I • (ψ₁ - ψ₂)‖ := h_le
          _ = ‖φ₁ - φ₂‖ := by rw [h_diff]
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal bound
    exact lipschitz.continuous



/-! ## Resolvent at -i -/

lemma resolvent_solution_mem_plus {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    Classical.choose (hsa.1 φ) ∈ gen.domain :=
  Classical.choose (Classical.choose_spec (hsa.1 φ))

lemma resolvent_solution_eq_plus {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    gen.op ⟨Classical.choose (hsa.1 φ), resolvent_solution_mem_plus gen hsa φ⟩ +
    I • Classical.choose (hsa.1 φ) = φ :=
  Classical.choose_spec (Classical.choose_spec (hsa.1 φ))

lemma resolvent_at_neg_i_unique {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (_ : Generator.IsSelfAdjoint gen)
    (φ ψ₁ ψ₂ : H)
    (hψ₁ : ψ₁ ∈ gen.domain) (hψ₂ : ψ₂ ∈ gen.domain)
    (h₁ : gen.op ⟨ψ₁, hψ₁⟩ + I • ψ₁ = φ)
    (h₂ : gen.op ⟨ψ₂, hψ₂⟩ + I • ψ₂ = φ) :
    ψ₁ = ψ₂ := by
  have h_sub_mem : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem hψ₁ hψ₂
  have h_factor : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂) = 0 := by
    have op_sub := gen.op.map_sub ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩
    calc gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂)
        = (gen.op ⟨ψ₁, hψ₁⟩ - gen.op ⟨ψ₂, hψ₂⟩) + I • (ψ₁ - ψ₂) :=
          congrFun (congrArg HAdd.hAdd op_sub) (I • (ψ₁ - ψ₂))
      _ = (gen.op ⟨ψ₁, hψ₁⟩ - gen.op ⟨ψ₂, hψ₂⟩) + (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
      _ = (gen.op ⟨ψ₁, hψ₁⟩ + I • ψ₁) - (gen.op ⟨ψ₂, hψ₂⟩ + I • ψ₂) := by abel
      _ = φ - φ := by rw [h₁, h₂]
      _ = 0 := sub_self φ
  -- From the norm expansion: ‖ψ‖ ≤ ‖Aψ + Iψ‖
  have h_le := norm_le_norm_add_I_smul gen ⟨ψ₁ - ψ₂, h_sub_mem⟩
  simp only at h_le
  have : ‖ψ₁ - ψ₂‖ ≤ 0 := by
    calc ‖ψ₁ - ψ₂‖
        ≤ ‖gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂)‖ := h_le
      _ = ‖(0 : H)‖ := by rw [h_factor]
      _ = 0 := norm_zero
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm this (norm_nonneg _)))

/-- The resolvent at `z = -i`, constructed via the self-adjointness criterion. -/
noncomputable def resolvent_at_neg_i {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H where
  toFun φ := Classical.choose (hsa.1 φ)
  map_add' φ₁ φ₂ := by
    let R₁ := Classical.choose (hsa.1 φ₁)
    let R₂ := Classical.choose (hsa.1 φ₂)
    let R_sum := Classical.choose (hsa.1 (φ₁ + φ₂))
    have h₁_mem : R₁ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ₁
    have h₂_mem : R₂ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ₂
    have h_sum_mem : R_sum ∈ gen.domain := resolvent_solution_mem_plus gen hsa (φ₁ + φ₂)
    have h₁_eq := resolvent_solution_eq_plus gen hsa φ₁
    have h₂_eq := resolvent_solution_eq_plus gen hsa φ₂
    have h_sum_eq := resolvent_solution_eq_plus gen hsa (φ₁ + φ₂)
    have h_add_mem : R₁ + R₂ ∈ gen.domain := gen.domain.add_mem h₁_mem h₂_mem
    have h_add_eq : gen.op ⟨R₁ + R₂, h_add_mem⟩ + I • (R₁ + R₂) = φ₁ + φ₂ := by
      have op_add := gen.op.map_add ⟨R₁, h₁_mem⟩ ⟨R₂, h₂_mem⟩
      calc gen.op ⟨R₁ + R₂, h_add_mem⟩ + I • (R₁ + R₂)
          = (gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩) + I • (R₁ + R₂) :=
            congrFun (congrArg HAdd.hAdd op_add) (I • (R₁ + R₂))
        _ = (gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩) + (I • R₁ + I • R₂) := by rw [smul_add]
        _ = (gen.op ⟨R₁, h₁_mem⟩ + I • R₁) + (gen.op ⟨R₂, h₂_mem⟩ + I • R₂) := by abel
        _ = φ₁ + φ₂ := by rw [h₁_eq, h₂_eq]
    exact (resolvent_at_neg_i_unique gen hsa (φ₁ + φ₂) (R₁ + R₂) R_sum
      h_add_mem h_sum_mem h_add_eq h_sum_eq).symm
  map_smul' c φ := by
    let R_φ := Classical.choose (hsa.1 φ)
    let R_scaled := Classical.choose (hsa.1 (c • φ))
    have h_mem : R_φ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ
    have h_scaled_mem : R_scaled ∈ gen.domain := resolvent_solution_mem_plus gen hsa (c • φ)
    have h_eq := resolvent_solution_eq_plus gen hsa φ
    have h_scaled_eq := resolvent_solution_eq_plus gen hsa (c • φ)
    have h_smul_mem : c • R_φ ∈ gen.domain := gen.domain.smul_mem c h_mem
    have h_smul_eq : gen.op ⟨c • R_φ, h_smul_mem⟩ + I • (c • R_φ) = c • φ := by
      have op_smul := gen.op.map_smul c ⟨R_φ, h_mem⟩
      calc gen.op ⟨c • R_φ, h_smul_mem⟩ + I • (c • R_φ)
          = c • gen.op ⟨R_φ, h_mem⟩ + I • (c • R_φ) :=
            congrFun (congrArg HAdd.hAdd op_smul) (I • c • R_φ)
        _ = c • gen.op ⟨R_φ, h_mem⟩ + c • (I • R_φ) := by rw [smul_comm]
        _ = c • (gen.op ⟨R_φ, h_mem⟩ + I • R_φ) := by rw [smul_add]
        _ = c • φ := by rw [h_eq]
    exact (resolvent_at_neg_i_unique gen hsa (c • φ) (c • R_φ) R_scaled
      h_smul_mem h_scaled_mem h_smul_eq h_scaled_eq).symm
  cont := by
    have lipschitz : LipschitzWith 1 (fun φ => Classical.choose (hsa.1 φ)) := by
      refine LipschitzWith.of_edist_le ?_
      intro φ₁ φ₂
      let ψ₁ := Classical.choose (hsa.1 φ₁)
      let ψ₂ := Classical.choose (hsa.1 φ₂)
      have h₁_mem : ψ₁ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ₁
      have h₂_mem : ψ₂ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ₂
      have h₁_eq := resolvent_solution_eq_plus gen hsa φ₁
      have h₂_eq := resolvent_solution_eq_plus gen hsa φ₂
      have h_sub_mem : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem h₁_mem h₂_mem
      have h_diff : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂) = φ₁ - φ₂ := by
        have op_sub := gen.op.map_sub ⟨ψ₁, h₁_mem⟩ ⟨ψ₂, h₂_mem⟩
        calc gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂)
            = (gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩) + I • (ψ₁ - ψ₂) :=
              congrFun (congrArg HAdd.hAdd op_sub) (I • (ψ₁ - ψ₂))
          _ = (gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩) + (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
          _ = (gen.op ⟨ψ₁, h₁_mem⟩ + I • ψ₁) - (gen.op ⟨ψ₂, h₂_mem⟩ + I • ψ₂) := by abel
          _ = φ₁ - φ₂ := by rw [h₁_eq, h₂_eq]
      have h_le := norm_le_norm_add_I_smul gen ⟨ψ₁ - ψ₂, h_sub_mem⟩
      have bound : ‖ψ₁ - ψ₂‖ ≤ ‖φ₁ - φ₂‖ := by
        calc ‖ψ₁ - ψ₂‖
            ≤ ‖gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂)‖ := h_le
          _ = ‖φ₁ - φ₂‖ := by rw [h_diff]
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal bound
    exact lipschitz.continuous

/-! ## Bounds -/

lemma resolvent_at_i_bound {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    ‖resolvent_at_i gen hsa‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro φ
  let ψ := resolvent_at_i gen hsa φ
  have h_mem : ψ ∈ gen.domain := resolvent_solution_mem gen hsa φ
  have h_eq : gen.op ⟨ψ, h_mem⟩ - I • ψ = φ := resolvent_solution_eq gen hsa φ
  have h_le := norm_le_norm_sub_I_smul gen ⟨ψ, h_mem⟩
  simp only at h_le
  calc ‖resolvent_at_i gen hsa φ‖ = ‖ψ‖ := rfl
    _ ≤ ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ := h_le
    _ = ‖φ‖ := by rw [h_eq]
    _ = 1 * ‖φ‖ := by ring

lemma resolvent_at_neg_i_bound {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    ‖resolvent_at_neg_i gen hsa‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro φ
  let ψ := resolvent_at_neg_i gen hsa φ
  have h_mem : ψ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ
  have h_eq : gen.op ⟨ψ, h_mem⟩ + I • ψ = φ := resolvent_solution_eq_plus gen hsa φ
  have h_le := norm_le_norm_add_I_smul gen ⟨ψ, h_mem⟩
  simp only at h_le
  calc ‖resolvent_at_neg_i gen hsa φ‖ = ‖ψ‖ := rfl
    _ ≤ ‖gen.op ⟨ψ, h_mem⟩ + I • ψ‖ := h_le
    _ = ‖φ‖ := by rw [h_eq]
    _ = 1 * ‖φ‖ := by ring

/-! ## Left inverse property -/

theorem resolvent_at_neg_i_left_inverse {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = ψ := by
  set φ := gen.op ⟨ψ, hψ⟩ + I • ψ
  set χ := resolvent_at_neg_i gen hsa φ
  have hχ_mem : χ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ
  have hχ_eq : gen.op ⟨χ, hχ_mem⟩ + I • χ = φ := resolvent_solution_eq_plus gen hsa φ
  exact resolvent_at_neg_i_unique gen hsa φ χ ψ hχ_mem hψ hχ_eq rfl

theorem resolvent_at_i_left_inverse {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    resolvent_at_i gen hsa (gen.op ⟨ψ, hψ⟩ - I • ψ) = ψ := by
  set φ := gen.op ⟨ψ, hψ⟩ - I • ψ
  set χ := resolvent_at_i gen hsa φ
  have hχ_mem : χ ∈ gen.domain := resolvent_solution_mem gen hsa φ
  have hχ_eq : gen.op ⟨χ, hχ_mem⟩ - I • χ = φ := resolvent_solution_eq gen hsa φ
  exact resolvent_at_i_unique gen hsa φ χ ψ hχ_mem hψ hχ_eq rfl

end QuantumMechanics.Resolvent
