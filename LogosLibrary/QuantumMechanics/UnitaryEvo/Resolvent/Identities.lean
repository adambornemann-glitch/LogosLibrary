/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Core

/-!
# Resolvent Identities

This file proves the fundamental algebraic identities satisfied by the resolvent:
* The resolvent identity: `R(z) - R(w) = (z - w) R(z) R(w)`
* The adjoint relation: `R(z)* = R(z̄)`

## Main definitions

* `resolventFun`: The resolvent as a function on `OffRealAxis`

## Main statements

* `resolvent_identity`: `R(z) - R(w) = (z - w) R(z) R(w)`
* `resolvent_adjoint`: `R(z)* = R(z̄)`
* `resolventFun_bound`: `‖R(z)‖ ≤ 1/|Im(z)|` (wrapper)
* `resolventFun_identity`: Resolvent identity for `resolventFun`
* `resolventFun_adjoint`: Adjoint relation for `resolventFun`

## Physics interpretation

The resolvent identity encodes the semigroup property of time evolution in the
spectral domain. It shows that resolvents at different points are related
algebraically, which is crucial for perturbation theory.

The adjoint relation `R(z)* = R(z̄)` reflects the self-adjointness of the
generator and shows that the resolvent maps the upper half-plane to the
lower half-plane under adjoints.
-/

namespace QuantumMechanics.Resolvent

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The resolvent identity: `R(z) - R(w) = (z - w) R(z) R(w)`. -/
theorem resolvent_identity {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    resolvent gen z hz hsa - resolvent gen w hw hsa =
    (z - w) • ((resolvent gen z hz hsa).comp (resolvent gen w hw hsa)) := by
  ext φ
  let ψ_w_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa w hw φ).exists
  let ψ_w := (ψ_w_sub : H)
  have h_w_domain : ψ_w ∈ gen.domain := ψ_w_sub.property
  have h_w_eq : gen.op ψ_w_sub - w • ψ_w = φ :=
    Classical.choose_spec (self_adjoint_range_all_z gen hsa w hw φ).exists
  let ψ_z_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists
  let ψ_z := (ψ_z_sub : H)
  have h_z_domain : ψ_z ∈ gen.domain := ψ_z_sub.property
  have h_z_eq : gen.op ψ_z_sub - z • ψ_z = φ :=
    Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists
  let η_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz ψ_w).exists
  let η := (η_sub : H)
  have h_η_domain : η ∈ gen.domain := η_sub.property
  have h_η_eq : gen.op η_sub - z • η = ψ_w :=
    Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz ψ_w).exists
  have h_Rz : resolvent gen z hz hsa φ = ψ_z := rfl
  have h_Rw : resolvent gen w hw hsa φ = ψ_w := rfl
  have h_Rz_ψw : resolvent gen z hz hsa ψ_w = η := rfl
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.comp_apply]
  rw [h_Rz, h_Rw, h_Rz_ψw]
  have h_Az_ψw : gen.op ⟨ψ_w, h_w_domain⟩ - z • ψ_w = φ + (w - z) • ψ_w := by
    have h_Aw : gen.op ⟨ψ_w, h_w_domain⟩ = φ + w • ψ_w := by
      have h_eq : gen.op ⟨ψ_w, h_w_domain⟩ = gen.op ψ_w_sub := rfl
      calc gen.op ⟨ψ_w, h_w_domain⟩
          = (gen.op ψ_w_sub - w • ψ_w) + w • ψ_w := by abel
        _ = φ + w • ψ_w := by rw [h_w_eq]
    calc gen.op ⟨ψ_w, h_w_domain⟩ - z • ψ_w
        = (φ + w • ψ_w) - z • ψ_w := by rw [h_Aw]
      _ = φ + (w - z) • ψ_w := by rw [sub_smul]; abel
  have h_sum_domain : ψ_z + (w - z) • η ∈ gen.domain := by
    apply gen.domain.add_mem h_z_domain
    exact gen.domain.smul_mem (w - z) h_η_domain
  have h_sum_eq : gen.op ⟨ψ_z + (w - z) • η, h_sum_domain⟩ -
      z • (ψ_z + (w - z) • η) = φ + (w - z) • ψ_w := by
    have op_add := gen.op.map_add ψ_z_sub ((w - z) • η_sub)
    have h_smul_mem : (w - z) • η ∈ gen.domain := gen.domain.smul_mem (w - z) h_η_domain
    have op_eq : gen.op ⟨ψ_z + (w - z) • η, h_sum_domain⟩ =
                 gen.op ψ_z_sub + gen.op ⟨(w - z) • η, h_smul_mem⟩ := by
      convert op_add using 1
    have op_smul := gen.op.map_smul (w - z) η_sub
    have op_smul_eq : gen.op ⟨(w - z) • η, h_smul_mem⟩ = (w - z) • gen.op η_sub := by
      convert op_smul using 1
    calc gen.op ⟨ψ_z + (w - z) • η, h_sum_domain⟩ - z • (ψ_z + (w - z) • η)
        = (gen.op ψ_z_sub + gen.op ⟨(w - z) • η, h_smul_mem⟩) - z • (ψ_z + (w - z) • η) :=
            by rw [op_eq]
      _ = (gen.op ψ_z_sub + (w - z) • gen.op η_sub) - z • (ψ_z + (w - z) • η) :=
            by rw [op_smul_eq]
      _ = (gen.op ψ_z_sub + (w - z) • gen.op η_sub) - (z • ψ_z + z • ((w - z) • η)) :=
            by rw [smul_add]
      _ = (gen.op ψ_z_sub - z • ψ_z) + ((w - z) • gen.op η_sub - z • ((w - z) • η)) := by abel
      _ = (gen.op ψ_z_sub - z • ψ_z) + ((w - z) • gen.op η_sub - (w - z) • (z • η)) :=
            by rw [smul_comm z (w - z) η]
      _ = (gen.op ψ_z_sub - z • ψ_z) + (w - z) • (gen.op η_sub - z • η) := by rw [← smul_sub]
      _ = φ + (w - z) • ψ_w := by rw [h_z_eq, h_η_eq]
  let target := φ + (w - z) • ψ_w
  have h_ψw_solves : gen.op ⟨ψ_w, h_w_domain⟩ - z • ψ_w = target := h_Az_ψw
  have h_sum_solves : gen.op ⟨ψ_z + (w - z) • η, h_sum_domain⟩ -
      z • (ψ_z + (w - z) • η) = target := h_sum_eq
  have h_eq_vals : ψ_w = ψ_z + (w - z) • η := by
    have h1 : (⟨ψ_w, h_w_domain⟩ : gen.domain) =
        (⟨ψ_z + (w - z) • η, h_sum_domain⟩ : gen.domain) :=
      (self_adjoint_range_all_z gen hsa z hz target).unique h_ψw_solves h_sum_solves
    exact congrArg Subtype.val h1
  calc ψ_z - ψ_w
      = ψ_z - (ψ_z + (w - z) • η) := by rw [h_eq_vals]
    _ = -((w - z) • η) := by abel
    _ = (-(w - z)) • η := by rw [neg_smul]
    _ = (z - w) • η := by ring_nf

/-- The resolvent adjoint relation: `R(z)* = R(z̄)`. -/
theorem resolvent_adjoint {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im ≠ 0) :
    (resolvent gen z hz hsa).adjoint =
    resolvent gen (starRingEnd ℂ z) (by simp only [Complex.conj_im, neg_ne_zero]; exact hz) hsa := by
  ext φ
  apply ext_inner_right ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_left]
  set z_bar := (starRingEnd ℂ) z with hz_bar_def
  have hz_bar : z_bar.im ≠ 0 := by
    rw [hz_bar_def]; simp only [Complex.conj_im, neg_ne_zero]; exact hz
  let ξ_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz ψ).exists
  let ξ := (ξ_sub : H)
  have hξ_domain : ξ ∈ gen.domain := ξ_sub.property
  have hξ_eq : gen.op ξ_sub - z • ξ = ψ :=
    Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz ψ).exists
  have hξ_def : resolvent gen z hz hsa ψ = ξ := rfl
  let η_sub : gen.domain :=
    Classical.choose (self_adjoint_range_all_z gen hsa z_bar hz_bar φ).exists
  let η := (η_sub : H)
  have hη_domain : η ∈ gen.domain := η_sub.property
  have hη_eq : gen.op η_sub - z_bar • η = φ :=
    Classical.choose_spec (self_adjoint_range_all_z gen hsa z_bar hz_bar φ).exists
  have hη_def : resolvent gen z_bar hz_bar hsa φ = η := rfl
  rw [hξ_def, hη_def]
  have hAξ : gen.op ξ_sub = ψ + z • ξ := by
    calc gen.op ξ_sub = (gen.op ξ_sub - z • ξ) + z • ξ := by abel
      _ = ψ + z • ξ := by rw [hξ_eq]
  have hAη : gen.op η_sub = φ + z_bar • η := by
    calc gen.op η_sub = (gen.op η_sub - z_bar • η) + z_bar • η := by abel
      _ = φ + z_bar • η := by rw [hη_eq]
  have h_sym : ⟪gen.op η_sub, ξ⟫_ℂ = ⟪η, gen.op ξ_sub⟫_ℂ := gen.symmetric η_sub ξ_sub
  have h_LHS : ⟪gen.op η_sub, ξ⟫_ℂ = ⟪φ, ξ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by
    calc ⟪gen.op η_sub, ξ⟫_ℂ
        = ⟪φ + z_bar • η, ξ⟫_ℂ := by rw [hAη]
      _ = ⟪φ, ξ⟫_ℂ + ⟪z_bar • η, ξ⟫_ℂ := by rw [inner_add_left]
      _ = ⟪φ, ξ⟫_ℂ + (starRingEnd ℂ) z_bar • ⟪η, ξ⟫_ℂ := by rw [inner_smul_left]; rfl
      _ = ⟪φ, ξ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by simp [hz_bar_def]
  have h_RHS : ⟪η, gen.op ξ_sub⟫_ℂ = ⟪η, ψ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by
    calc ⟪η, gen.op ξ_sub⟫_ℂ
        = ⟪η, ψ + z • ξ⟫_ℂ := by rw [hAξ]
      _ = ⟪η, ψ⟫_ℂ + ⟪η, z • ξ⟫_ℂ := by rw [inner_add_right]
      _ = ⟪η, ψ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by rw [inner_smul_right]; rfl
  have h_cancel : ⟪φ, ξ⟫_ℂ + z • ⟪η, ξ⟫_ℂ = ⟪η, ψ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by
    rw [← h_LHS, ← h_RHS, h_sym]
  exact add_right_cancel h_cancel

/-! ## Wrapper definitions and theorems for `resolventFun` -/

/-- The resolvent as a function on `OffRealAxis`. -/
noncomputable def resolventFun {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    OffRealAxis → (H →L[ℂ] H) :=
  fun z => resolvent gen z.val z.property hsa

theorem resolventFun_bound {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : OffRealAxis) :
    ‖resolventFun gen hsa z‖ ≤ 1 / |z.val.im| :=
  resolvent_bound gen hsa z.val z.property

theorem resolventFun_identity {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z w : OffRealAxis) :
    resolventFun gen hsa z - resolventFun gen hsa w =
    (z.val - w.val) • ((resolventFun gen hsa z).comp (resolventFun gen hsa w)) :=
  resolvent_identity gen hsa z.val w.val z.property w.property

theorem resolventFun_adjoint {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : OffRealAxis) :
    (resolventFun gen hsa z).adjoint =
    resolventFun gen hsa ⟨starRingEnd ℂ z.val, by simp; exact z.property⟩ :=
  resolvent_adjoint gen hsa z.val z.property

end QuantumMechanics.Resolvent
