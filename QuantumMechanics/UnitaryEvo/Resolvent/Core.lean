/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Range
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner
/-!
# The Resolvent Operator

This file defines the resolvent operator `R(z) = (A - zI)⁻¹` for self-adjoint
generators and proves the fundamental bound `‖R(z)‖ ≤ 1/|Im(z)|`.

## Main definitions

* `resolvent`: The resolvent operator `R(z) = (A - zI)⁻¹` as a bounded linear map

## Main statements

* `resolvent_bound`: `‖R(z)‖ ≤ 1/|Im(z)|`

## Implementation notes

The resolvent is constructed via `LinearMap.mkContinuous` using the existence
and uniqueness from `self_adjoint_range_all_z` together with the lower bound
estimate which provides the continuity bound.
-/

namespace QuantumMechanics.Resolvent

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The resolvent operator `R(z) = (A - zI)⁻¹` for self-adjoint `A` and `Im(z) ≠ 0`. -/
noncomputable def resolvent {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (z : ℂ)
    (hz : z.im ≠ 0) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun φ =>
        let ψ : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists
        (ψ : H)
      map_add' := fun φ₁ φ₂ => by
        have h₁ := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ₁).exists
        have h₂ := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ₂).exists
        have h_sum_eq := Classical.choose_spec
          (self_adjoint_range_all_z gen hsa z hz (φ₁ + φ₂)).exists
        have h_add_mem :
            ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
              gen.domain) : H) +
            ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
              gen.domain) : H) ∈ gen.domain :=
          gen.domain.add_mem
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
              gen.domain).property
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
              gen.domain).property
        have h_add_eq :
            gen.op ⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
                      gen.domain) : H) +
                     ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
                      gen.domain) : H), h_add_mem⟩ -
            z • (((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
                   gen.domain) : H) +
                 ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
                   gen.domain) : H)) = φ₁ + φ₂ := by
          have op_add := gen.op.map_add
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain)
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain)
          have op_eq :
              gen.op ⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
                        gen.domain) : H) +
                       ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
                        gen.domain) : H), h_add_mem⟩ =
              gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
                      gen.domain) +
              gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
                      gen.domain) := by
            convert op_add using 1
          calc gen.op ⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
                         gen.domain) : H) +
                        ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
                         gen.domain) : H), h_add_mem⟩ -
               z • (((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
                      gen.domain) : H) +
                    ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
                      gen.domain) : H))
              = (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
                         gen.domain) +
                 gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
                         gen.domain)) -
                z • (((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
                       gen.domain) : H) +
                     ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
                       gen.domain) : H)) := by rw [op_eq]
            _ = (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
                         gen.domain) +
                 gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
                         gen.domain)) -
                (z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
                       gen.domain) : H) +
                 z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
                       gen.domain) : H)) := by rw [smul_add]
            _ = (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
                         gen.domain) -
                 z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
                       gen.domain) : H)) +
                (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
                         gen.domain) -
                 z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
                       gen.domain) : H)) := by abel
            _ = φ₁ + φ₂ := by rw [h₁, h₂]
        have h_eq :
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz (φ₁ + φ₂)).exists :
              gen.domain) =
            ⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
               gen.domain) : H) +
             ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
               gen.domain) : H), h_add_mem⟩ :=
          (self_adjoint_range_all_z gen hsa z hz (φ₁ + φ₂)).unique h_sum_eq h_add_eq
        calc ((Classical.choose (self_adjoint_range_all_z gen hsa z hz (φ₁ + φ₂)).exists :
               gen.domain) : H)
            = (⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
                  gen.domain) : H) +
                ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
                  gen.domain) : H), h_add_mem⟩ : gen.domain) := by rw [h_eq]
          _ = ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists :
                gen.domain) : H) +
              ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists :
                gen.domain) : H) := rfl
      map_smul' := fun c φ => by
        simp only [RingHom.id_apply]
        have h := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists
        have h_scaled_eq := Classical.choose_spec
          (self_adjoint_range_all_z gen hsa z hz (c • φ)).exists
        have h_smul_mem :
            c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                  gen.domain) : H) ∈ gen.domain :=
          gen.domain.smul_mem c
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
              gen.domain).property
        have h_smul_eq :
            gen.op ⟨c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                          gen.domain) : H), h_smul_mem⟩ -
            z • (c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                       gen.domain) : H)) = c • φ := by
          have op_smul := gen.op.map_smul c
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain)
          have op_eq :
              gen.op ⟨c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                            gen.domain) : H), h_smul_mem⟩ =
              c • gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                          gen.domain) := by
            convert op_smul using 1
          calc gen.op ⟨c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                             gen.domain) : H), h_smul_mem⟩ -
               z • (c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                          gen.domain) : H))
              = c • gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                            gen.domain) -
                z • (c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                           gen.domain) : H)) := by rw [op_eq]
            _ = c • gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                            gen.domain) -
                c • (z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                           gen.domain) : H)) := by rw [smul_comm z c]
            _ = c • (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                             gen.domain) -
                z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                      gen.domain) : H)) := by rw [smul_sub]
            _ = c • φ := by rw [h]
        have h_eq :
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz (c • φ)).exists :
              gen.domain) =
            ⟨c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                   gen.domain) : H), h_smul_mem⟩ :=
          (self_adjoint_range_all_z gen hsa z hz (c • φ)).unique h_scaled_eq h_smul_eq
        have h_val := congrArg (↑· : gen.domain → H) h_eq
        simp only at h_val
        exact h_val
    }
    (1 / |z.im|)
    (by
      intro φ
      have h := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists
      have h_mem := (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
                     gen.domain).property
      have h_bound := lower_bound_estimate gen z hz
        ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
          gen.domain) : H) h_mem
      rw [h] at h_bound
      have h_im_pos : 0 < |z.im| := abs_pos.mpr hz
      calc ‖((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
              gen.domain) : H)‖
          = (1 / |z.im|) * (|z.im| *
            ‖((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists :
               gen.domain) : H)‖) := by field_simp
        _ ≤ (1 / |z.im|) * ‖φ‖ := by
            apply mul_le_mul_of_nonneg_left h_bound
            positivity
    )

/-- The resolvent satisfies `‖R(z)‖ ≤ 1/|Im(z)|`. -/
theorem resolvent_bound {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im ≠ 0) :
    ‖resolvent gen z hz hsa‖ ≤ 1 / |z.im| := by
  have h_pointwise : ∀ φ : H, ‖resolvent gen z hz hsa φ‖ ≤ (1 / |z.im|) * ‖φ‖ := by
    intro φ
    let ψ_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists
    let ψ := (ψ_sub : H)
    have h_domain : ψ ∈ gen.domain := ψ_sub.property
    have h_eq : gen.op ψ_sub - z • ψ = φ :=
      Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists
    have h_lower := lower_bound_estimate gen z hz ψ h_domain
    rw [h_eq] at h_lower
    have h_im_pos : 0 < |z.im| := abs_pos.mpr hz
    have h_ψ_bound : ‖ψ‖ ≤ ‖φ‖ / |z.im| := by
      have h_mul : |z.im| * ‖ψ‖ ≤ ‖φ‖ := h_lower
      calc ‖ψ‖
          = (|z.im|)⁻¹ * (|z.im| * ‖ψ‖) := by field_simp
        _ ≤ (|z.im|)⁻¹ * ‖φ‖ := by
            apply mul_le_mul_of_nonneg_left h_mul
            exact inv_nonneg.mpr (abs_nonneg _)
        _ = ‖φ‖ / |z.im| := by rw [inv_mul_eq_div]
    have h_res_eq : resolvent gen z hz hsa φ = ψ := rfl
    calc ‖resolvent gen z hz hsa φ‖
        = ‖ψ‖ := by rw [h_res_eq]
      _ ≤ ‖φ‖ / |z.im| := h_ψ_bound
      _ = (1 / |z.im|) * ‖φ‖ := by ring
  apply ContinuousLinearMap.opNorm_le_bound
  · apply div_nonneg
    · norm_num
    · exact abs_nonneg _
  · exact h_pointwise

end QuantumMechanics.Resolvent
