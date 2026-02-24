/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Range.Orthogonal
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.Range.ClosedRange
/-!
# Surjectivity of (A - zI) for Self-Adjoint Generators

This file proves the main resolvent theorem: for a self-adjoint generator `A`
and any `z` with `Im(z) ≠ 0`, the equation `(A - zI)ψ = φ` has a unique
solution for every `φ ∈ H`.

The proof combines three facts:
1. The orthogonal complement of the range is trivial (from `Orthogonal.lean`)
2. The range is closed (from `ClosedRange.lean`)
3. Closed + dense = everything

## Main results

* `rangeSubmodule`: The range of `(A - zI)` as a submodule
* `range_sub_smul_dense`: The range is dense
* `solution_unique`: Solutions are unique
* `self_adjoint_range_all_z`: **Main theorem** — existence and uniqueness for all `z`

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3
-/
namespace QuantumMechanics.Resolvent

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H][CompleteSpace H]
/-! ### Step 3: Range is dense -/

/-- The range of (A - zI) forms a submodule. -/
def rangeSubmodule {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (z : ℂ) : Submodule ℂ H where
  carrier := Set.range (fun (ψ : gen.domain) => gen.op ψ - z • (ψ : H))
  add_mem' := by
    intro a b ha hb
    obtain ⟨ψa, hψa⟩ := ha
    obtain ⟨ψb, hψb⟩ := hb
    refine ⟨⟨(ψa : H) + (ψb : H), gen.domain.add_mem ψa.property ψb.property⟩, ?_⟩
    have op_add := gen.op.map_add ψa ψb
    simp only [← hψa, ← hψb]
    calc gen.op ⟨(ψa : H) + (ψb : H), _⟩ - z • ((ψa : H) + (ψb : H))
        = (gen.op ψa + gen.op ψb) - z • ((ψa : H) + (ψb : H)) := by congr 1
      _ = (gen.op ψa + gen.op ψb) - (z • (ψa : H) + z • (ψb : H)) := by rw [smul_add]
      _ = (gen.op ψa - z • (ψa : H)) + (gen.op ψb - z • (ψb : H)) := by abel
  zero_mem' := ⟨⟨0, gen.domain.zero_mem⟩, by simp only [smul_zero, sub_zero]; exact gen.op.map_zero⟩
  smul_mem' := by
    intro c a ha
    obtain ⟨ψ, hψ⟩ := ha
    refine ⟨⟨c • (ψ : H), gen.domain.smul_mem c ψ.property⟩, ?_⟩
    have op_smul := gen.op.map_smul c ψ
    simp only [← hψ]
    calc gen.op ⟨c • (ψ : H), _⟩ - z • (c • (ψ : H))
        = c • gen.op ψ - z • (c • (ψ : H)) := by congr 1
      _ = c • gen.op ψ - c • (z • (ψ : H)) := by rw [smul_comm z c]
      _ = c • (gen.op ψ - z • (ψ : H)) := by rw [smul_sub]

/-- The range of (A - zI) is dense when Im(z) ≠ 0. -/
lemma range_sub_smul_dense {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im ≠ 0) :
    Dense (Set.range (fun (ψ : gen.domain) => gen.op ψ - z • (ψ : H))) := by
  let M := rangeSubmodule gen z
  have hM_eq : (M : Set H) = Set.range (fun (ψ : gen.domain) => gen.op ψ - z • (ψ : H)) := rfl
  have h_M_orth : Mᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro χ hχ
    apply orthogonal_range_eq_zero gen hsa z hz χ
    intro ψ
    have h_mem : gen.op ψ - z • (ψ : H) ∈ M := ⟨ψ, rfl⟩
    exact Submodule.inner_right_of_mem_orthogonal h_mem hχ
  have h_M_top : M.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    rw [h_M_orth]
    exact Submodule.bot_orthogonal_eq_top
  have h_M_dense : Dense (M : Set H) := by
    rw [dense_iff_closure_eq]
    have h_coe : closure (M : Set H) = (M.topologicalClosure : Set H) :=
      (Submodule.topologicalClosure_coe M).symm
    rw [h_coe, h_M_top]
    rfl
  rw [← hM_eq]
  exact h_M_dense


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-! ### Uniqueness from lower bound -/

/-- Solutions to (A - zI)ψ = φ are unique when Im(z) ≠ 0. -/
lemma solution_unique {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (z : ℂ) (hz : z.im ≠ 0) (φ : H)
    (ψ ψ' : gen.domain)
    (hψ : gen.op ψ - z • (ψ : H) = φ)
    (hψ' : gen.op ψ' - z • (ψ' : H) = φ) : ψ = ψ' := by
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
  have h_bound := lower_bound_estimate gen z hz ((ψ : H) - (ψ' : H)) h_sub_mem
  rw [h_diff] at h_bound
  simp only [norm_zero, ge_iff_le] at h_bound
  have h_im_pos : 0 < |z.im| := abs_pos.mpr hz
  have h_norm_zero : ‖(ψ : H) - (ψ' : H)‖ = 0 := by
    by_contra h_ne
    have h_pos : 0 < ‖(ψ : H) - (ψ' : H)‖ := by
      cases' (norm_nonneg ((ψ : H) - (ψ' : H))).lt_or_eq with h h
      · exact h
      · exact absurd h.symm h_ne
    have : 0 < |z.im| * ‖(ψ : H) - (ψ' : H)‖ := mul_pos h_im_pos h_pos
    linarith
  rw [norm_sub_rev] at h_norm_zero
  symm
  exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp h_norm_zero))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-! ### Main theorem -/

/-- **Main Theorem**: For self-adjoint `A` and `Im(z) ≠ 0`, the equation
    `(A - zI)ψ = φ` has a unique solution for every `φ`. -/
theorem self_adjoint_range_all_z
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im ≠ 0) :
    ∀ φ : H, ∃! (ψ : gen.domain), gen.op ψ - z • (ψ : H) = φ := by
  intro φ
  -- Existence: closed + dense = everything
  have h_range_closed := range_sub_smul_closed gen hsa z hz
  have h_dense := range_sub_smul_dense gen hsa z hz
  have h_eq_univ : Set.range (fun (ψ : gen.domain) => gen.op ψ - z • (ψ : H)) = Set.univ := by
    have h_closure := h_dense.closure_eq
    rw [IsClosed.closure_eq h_range_closed] at h_closure
    exact h_closure
  have h_exists : ∃ (ψ : gen.domain), gen.op ψ - z • (ψ : H) = φ := by
    have : φ ∈ Set.univ := Set.mem_univ φ
    rw [← h_eq_univ] at this
    exact Set.mem_range.mp this
  -- Uniqueness: from lower bound
  obtain ⟨ψ, hψ⟩ := h_exists
  exact ⟨ψ, hψ, fun ψ' hψ' => (solution_unique gen z hz φ ψ ψ' hψ hψ').symm⟩

end QuantumMechanics.Resolvent
