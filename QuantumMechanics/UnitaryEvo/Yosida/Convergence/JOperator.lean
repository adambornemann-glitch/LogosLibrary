/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.Symmetry

/-!
# Convergence of the J Operator

This file proves that the contractive operator `Jₙ = -in·R(in)` converges
strongly to the identity on the domain, and extends this to all of H by density.

## Main results

* `yosidaJ_eq_sub_resolvent_A`: `Jₙφ = φ - R(in)(Aφ)` for `φ ∈ D(A)`
* `yosidaJ_tendsto_on_domain`: `Jₙφ → φ` for `φ ∈ D(A)`
* `yosida_J_tendsto_id`: `Jₙψ → ψ` for all `ψ ∈ H`

-/

namespace QuantumMechanics.Yosida

open Complex Filter Topology Resolvent Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U_grp : OneParameterUnitaryGroup (H := H)}

lemma yosidaJ_eq_sub_resolvent_A
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (φ : H) (hφ : φ ∈ gen.domain) :
    (-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ =
      φ - Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩) := by
  -- Let R = R(in) and z = in for clarity
  set z := I * (n : ℂ) with hz_def
  set R := Resolvent.resolvent gen z (I_mul_pnat_im_ne_zero n) hsa with hR_def
  -- R(φ) is in domain and satisfies (A - zI)(Rφ) = φ
  obtain ⟨hRφ_domain, hRφ_eq⟩ := resolvent_spec gen hsa z (I_mul_pnat_im_ne_zero n) φ
  -- From (A - zI)(Rφ) = φ, we get A(Rφ) = φ + z·Rφ
  have h_ARφ : gen.op ⟨R φ, hRφ_domain⟩ = φ + z • (R φ) := by
    calc gen.op ⟨R φ, hRφ_domain⟩
        = (gen.op ⟨R φ, hRφ_domain⟩ - z • R φ) + z • R φ := by abel
      _ = φ + z • R φ := by rw [hRφ_eq]
  -- R(Aφ) is in domain and satisfies (A - zI)(R(Aφ)) = Aφ
  obtain ⟨hRAφ_domain, hRAφ_eq⟩ := resolvent_spec gen hsa z (I_mul_pnat_im_ne_zero n) (gen.op ⟨φ, hφ⟩)
  -- Key: R((A-zI)φ) = φ for φ ∈ D(A)
  have h_R_AzI : R (gen.op ⟨φ, hφ⟩ - z • φ) = φ := by
    let ψ_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z
                               (I_mul_pnat_im_ne_zero n) (gen.op ⟨φ, hφ⟩ - z • φ)).exists
    have h_ψ_eq := Classical.choose_spec (self_adjoint_range_all_z gen hsa z
                    (I_mul_pnat_im_ne_zero n) (gen.op ⟨φ, hφ⟩ - z • φ)).exists
    have h_φ_solves : gen.op ⟨φ, hφ⟩ - z • φ = gen.op ⟨φ, hφ⟩ - z • φ := rfl
    have h_subtype : (⟨φ, hφ⟩ : gen.domain) = ψ_sub :=
      (self_adjoint_range_all_z gen hsa z (I_mul_pnat_im_ne_zero n)
        (gen.op ⟨φ, hφ⟩ - z • φ)).unique h_φ_solves h_ψ_eq
    calc R (gen.op ⟨φ, hφ⟩ - z • φ)
        = ψ_sub.val := rfl
      _ = (⟨φ, hφ⟩ : gen.domain).val := by rw [← h_subtype]
      _ = φ := rfl
  -- By linearity: R(Aφ - zφ) = R(Aφ) - z·Rφ
  have h_R_linear : R (gen.op ⟨φ, hφ⟩ - z • φ) = R (gen.op ⟨φ, hφ⟩) - z • R φ := by
    calc R (gen.op ⟨φ, hφ⟩ - z • φ)
        = R (gen.op ⟨φ, hφ⟩) - R (z • φ) := by rw [R.map_sub]
      _ = R (gen.op ⟨φ, hφ⟩) - z • R φ := by rw [R.map_smul]
  -- So R(Aφ) = φ + z·Rφ
  have h_RAφ_explicit : R (gen.op ⟨φ, hφ⟩) = φ + z • R φ := by
    calc R (gen.op ⟨φ, hφ⟩)
        = R (gen.op ⟨φ, hφ⟩) - z • R φ + z • R φ := by abel
      _ = R (gen.op ⟨φ, hφ⟩ - z • φ) + z • R φ := by rw [h_R_linear]
      _ = φ + z • R φ := by rw [h_R_AzI]
  -- Conclude: (-z)·Rφ = φ - R(Aφ)
  calc (-I * (n : ℂ)) • R φ
      = (-z) • R φ := by rw [neg_mul]
    _ = -(z • R φ) := by rw [neg_smul]
    _ = φ - (φ + z • R φ) := by abel
    _ = φ - R (gen.op ⟨φ, hφ⟩) := by rw [← h_RAφ_explicit]

lemma yosidaJ_tendsto_on_domain
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => (-I * (n : ℂ)) •
              Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ)
            atTop (𝓝 φ) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_cases h_Aφ_zero : ‖gen.op ⟨φ, hφ⟩‖ = 0
  · -- Case: Aφ = 0, so Jₙφ = φ for all n
    use 1
    intro n _
    rw [yosidaJ_eq_sub_resolvent_A gen hsa n φ hφ]
    have h_Aφ_eq_zero : gen.op ⟨φ, hφ⟩ = 0 := norm_eq_zero.mp h_Aφ_zero
    simp only [h_Aφ_eq_zero, map_zero, sub_zero]
    rw [dist_self]
    exact hε
  · -- Case: ‖Aφ‖ > 0
    have h_Aφ_pos : 0 < ‖gen.op ⟨φ, hφ⟩‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_Aφ_zero)
    -- Choose N > ‖Aφ‖/ε
    use ⟨Nat.ceil (‖gen.op ⟨φ, hφ⟩‖ / ε) + 1, Nat.add_one_pos _⟩
    intro n hn
    calc dist ((-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ) φ
        = ‖(-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ - φ‖ :=
            dist_eq_norm _ _
      _ = ‖(φ - Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)) - φ‖ := by
            rw [yosidaJ_eq_sub_resolvent_A gen hsa n φ hφ]
      _ = ‖-Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)‖ := by
            congr 1; abel
      _ = ‖Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)‖ :=
            norm_neg _
      _ ≤ ‖Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ * ‖gen.op ⟨φ, hφ⟩‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 / (n : ℝ)) * ‖gen.op ⟨φ, hφ⟩‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            calc ‖Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖
                ≤ 1 / |(I * (n : ℂ)).im| := resolvent_bound gen hsa _ _
              _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]
      _ < ε := by
            have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos
            have h_n_bound : ‖gen.op ⟨φ, hφ⟩‖ / ε + 1 ≤ (n : ℝ) := by
              have h1 : (Nat.ceil (‖gen.op ⟨φ, hφ⟩‖ / ε) + 1 : ℕ) ≤ n := hn
              calc ‖gen.op ⟨φ, hφ⟩‖ / ε + 1
                  ≤ ↑(Nat.ceil (‖gen.op ⟨φ, hφ⟩‖ / ε)) + 1 :=
                      add_le_add_right (Nat.le_ceil _) _
                _ = ↑(Nat.ceil (‖gen.op ⟨φ, hφ⟩‖ / ε) + 1) := by norm_cast
                _ ≤ (n : ℝ) := Nat.cast_le.mpr h1
            have h_ratio_lt : ‖gen.op ⟨φ, hφ⟩‖ / ε < (n : ℝ) := by linarith
            have h_prod_lt : ‖gen.op ⟨φ, hφ⟩‖ < (n : ℝ) * ε := by
              calc ‖gen.op ⟨φ, hφ⟩‖
                  = (‖gen.op ⟨φ, hφ⟩‖ / ε) * ε := by field_simp
                _ < (n : ℝ) * ε := mul_lt_mul_of_pos_right h_ratio_lt hε
            calc (1 / (n : ℝ)) * ‖gen.op ⟨φ, hφ⟩‖
                = ‖gen.op ⟨φ, hφ⟩‖ / (n : ℝ) := by ring
              _ = ‖gen.op ⟨φ, hφ⟩‖ * (1 / (n : ℝ)) := by ring
              _ < ((n : ℝ) * ε) * (1 / (n : ℝ)) := by
                  apply mul_lt_mul_of_pos_right h_prod_lt
                  exact one_div_pos.mpr hn_pos
              _ = ε := by field_simp

theorem yosida_J_tendsto_id
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (ψ : H) :
    Tendsto (fun n : ℕ+ => (-I * (n : ℂ)) •
              resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa ψ)
            atTop (𝓝 ψ) := by
  let J : ℕ+ → H →L[ℂ] H := fun n =>
    (-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Step 1: Approximate ψ by domain element φ
  have h_dense := gen.dense_domain
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp (h_dense.closure_eq ▸ Set.mem_univ ψ)
                                    (ε / 3) (by linarith)
  -- Step 2: Get N such that Jₙφ is close to φ for n ≥ N
  have h_domain_conv := yosidaJ_tendsto_on_domain gen hsa φ hφ_mem
  rw [Metric.tendsto_atTop] at h_domain_conv
  obtain ⟨N, hN⟩ := h_domain_conv (ε / 3) (by linarith)
  -- Step 3: For n ≥ N, Jₙψ is close to ψ
  use N
  intro n hn
  calc dist (J n ψ) ψ
      ≤ dist (J n ψ) (J n φ) + dist (J n φ) φ + dist φ ψ := dist_triangle4 _ _ _ _
    _ = ‖J n ψ - J n φ‖ + dist (J n φ) φ + dist φ ψ := by rw [dist_eq_norm]
    _ = ‖J n (ψ - φ)‖ + dist (J n φ) φ + dist φ ψ := by
        congr 1
        rw [ContinuousLinearMap.map_sub]
    _ ≤ ‖J n‖ * ‖ψ - φ‖ + dist (J n φ) φ + dist φ ψ := by
        apply add_le_add_right (add_le_add_right (ContinuousLinearMap.le_opNorm _ _) _)
    _ ≤ 1 * ‖ψ - φ‖ + dist (J n φ) φ + dist φ ψ := by
        apply add_le_add_right (add_le_add_right _ _)
        apply mul_le_mul_of_nonneg_right (yosidaJ_norm_bound gen hsa n) (norm_nonneg _)
    _ = ‖ψ - φ‖ + dist (J n φ) φ + dist φ ψ := by rw [one_mul]
    _ = dist ψ φ + dist (J n φ) φ + dist φ ψ := by rw [← dist_eq_norm]
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h1 : dist ψ φ < ε / 3 := hφ_close
        have h2 : dist (J n φ) φ < ε / 3 := hN n hn
        have h3 : dist φ ψ < ε / 3 := by rw [dist_comm]; exact hφ_close
        exact add_lt_add (add_lt_add h1 h2) h3
    _ = ε := by ring

end QuantumMechanics.Yosida
