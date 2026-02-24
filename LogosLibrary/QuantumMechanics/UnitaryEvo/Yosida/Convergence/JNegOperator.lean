/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.Convergence.JOperator

/-!
# Convergence of the JNeg Operator

This file proves that the contractive operator `Jₙ⁻ = in·R(-in)` converges
strongly to the identity on the domain, and extends this to all of H by density.

## Main results

* `yosidaJNeg_eq_sub_resolvent_A`: `Jₙ⁻φ = φ - R(-in)(Aφ)` for `φ ∈ D(A)`
* `yosidaJNeg_tendsto_on_domain`: `Jₙ⁻φ → φ` for `φ ∈ D(A)`
* `yosidaJNeg_tendsto_id`: `Jₙ⁻ψ → ψ` for all `ψ ∈ H`

-/

namespace QuantumMechanics.Yosida

open Complex Filter Topology Resolvent Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U_grp : OneParameterUnitaryGroup (H := H)}

lemma yosidaJNeg_eq_sub_resolvent_A
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (φ : H) (hφ : φ ∈ gen.domain) :
    (I * (n : ℂ)) • Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa φ =
      φ - Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩) := by
  set z := -I * (n : ℂ) with hz_def
  set R := Resolvent.resolvent gen z (neg_I_mul_pnat_im_ne_zero n) hsa with hR_def
  -- R((A-zI)φ) = φ for φ ∈ D(A)
  have h_R_AzI : R (gen.op ⟨φ, hφ⟩ - z • φ) = φ := by
    let ψ_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z
                               (neg_I_mul_pnat_im_ne_zero n) (gen.op ⟨φ, hφ⟩ - z • φ)).exists
    have h_ψ_eq := Classical.choose_spec (self_adjoint_range_all_z gen hsa z
                    (neg_I_mul_pnat_im_ne_zero n) (gen.op ⟨φ, hφ⟩ - z • φ)).exists
    have h_φ_solves : gen.op ⟨φ, hφ⟩ - z • φ = gen.op ⟨φ, hφ⟩ - z • φ := rfl
    have h_subtype : (⟨φ, hφ⟩ : gen.domain) = ψ_sub :=
      (self_adjoint_range_all_z gen hsa z (neg_I_mul_pnat_im_ne_zero n)
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
  -- Conclude: (in)·Rφ = φ - R(Aφ) since z = -in
  calc (I * (n : ℂ)) • R φ
      = -((-I * (n : ℂ)) • R φ) := by simp only [neg_mul, neg_smul, neg_neg]
    _ = -(z • R φ) := by rw [hz_def]
    _ = φ - (φ + z • R φ) := by abel
    _ = φ - R (gen.op ⟨φ, hφ⟩) := by rw [← h_RAφ_explicit]

lemma yosidaJNeg_tendsto_on_domain
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaJNeg gen hsa n φ) atTop (𝓝 φ) := by
  unfold yosidaJNeg resolventAtNegIn
  have h_identity : ∀ n : ℕ+,
      (I * (n : ℂ)) • Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa φ =
      φ - Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩) :=
    fun n => yosidaJNeg_eq_sub_resolvent_A gen hsa n φ hφ
  have h_tendsto : Tendsto (fun n : ℕ+ => φ - Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)) atTop (𝓝 φ) := by
    -- First show R(-in)(Aφ) → 0
    have h_to_zero : Tendsto (fun n : ℕ+ => Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)) atTop (𝓝 0) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (‖gen.op ⟨φ, hφ⟩‖ / ε)
      use ⟨N + 1, Nat.succ_pos N⟩
      intro n hn
      rw [dist_eq_norm, sub_zero]
      have h_res_bound : ‖Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖ ≤ 1 / (n : ℝ) := by
        calc ‖Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖
            ≤ 1 / |(-I * (n : ℂ)).im| := resolvent_bound gen hsa _ _
          _ = 1 / (n : ℝ) := by
              simp only [neg_mul, neg_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
              rw [div_eq_div_iff_comm, natCast_re]
              rw [abs_neg, Nat.abs_cast]
      have hn_ge : (n : ℕ) ≥ N + 1 := hn
      have hn_gt : (n : ℝ) > N := by
        have h : (N + 1 : ℕ) ≤ (n : ℕ) := hn
        calc (n : ℝ) ≥ (N + 1 : ℕ) := Nat.cast_le.mpr h
          _ = N + 1 := by simp
          _ > N := by linarith
      calc ‖Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)‖
          ≤ ‖Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖ * ‖gen.op ⟨φ, hφ⟩‖ :=
              ContinuousLinearMap.le_opNorm _ _
        _ ≤ (1 / (n : ℝ)) * ‖gen.op ⟨φ, hφ⟩‖ := by
              apply mul_le_mul_of_nonneg_right h_res_bound (norm_nonneg _)
        _ = ‖gen.op ⟨φ, hφ⟩‖ / (n : ℝ) := by ring
        _ < ε := by
              by_cases hAφ : ‖gen.op ⟨φ, hφ⟩‖ = 0
              · simp [hAφ, hε]
              · have hAφ_pos : 0 < ‖gen.op ⟨φ, hφ⟩‖ := (norm_nonneg _).lt_of_ne' hAφ
                calc ‖gen.op ⟨φ, hφ⟩‖ / (n : ℝ)
                  < ‖gen.op ⟨φ, hφ⟩‖ / N := by
                      have hN_pos : (0 : ℝ) < N := by
                        have : 0 < ‖gen.op ⟨φ, hφ⟩‖ / ε := div_pos hAφ_pos hε
                        linarith
                      apply div_lt_div_of_pos_left hAφ_pos hN_pos hn_gt
                _ ≤ ε := by
                      have hN_pos : (0 : ℝ) < N := by
                        have : 0 < ‖gen.op ⟨φ, hφ⟩‖ / ε := div_pos hAφ_pos hε
                        linarith
                      rw [propext (div_le_iff₀ hN_pos)]
                      calc ‖gen.op ⟨φ, hφ⟩‖ = (‖gen.op ⟨φ, hφ⟩‖ / ε) * ε := by field_simp
                        _ ≤ N * ε := by
                            apply mul_le_mul_of_nonneg_right (le_of_lt hN) (le_of_lt hε)
                      linarith
    have h_sub : Tendsto (fun n : ℕ+ => φ - Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)) atTop (𝓝 (φ - 0)) := by
      exact Filter.Tendsto.sub tendsto_const_nhds h_to_zero
    simp only [sub_zero] at h_sub
    exact h_sub
  exact h_tendsto.congr (fun n => (h_identity n).symm)

lemma yosidaJNeg_tendsto_id
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) :
    Tendsto (fun n : ℕ+ => yosidaJNeg gen hsa n ψ) atTop (𝓝 ψ) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  -- Step 1: Approximate ψ by φ ∈ D(A) with ‖ψ - φ‖ < ε/3
  have hε3 : ε / 3 > 0 := by linarith
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp
    (h_dense.closure_eq ▸ Set.mem_univ ψ) (ε / 3) hε3
  rw [dist_eq_norm] at hφ_close
  -- Step 2: For φ ∈ D(A), Jₙ⁻φ → φ
  have h_conv_φ := yosidaJNeg_tendsto_on_domain gen hsa φ hφ_mem
  rw [Metric.tendsto_atTop] at h_conv_φ
  obtain ⟨N, hN⟩ := h_conv_φ (ε / 3) hε3
  use N
  intro n hn
  rw [dist_eq_norm]
  calc ‖yosidaJNeg gen hsa n ψ - ψ‖
      = ‖(yosidaJNeg gen hsa n ψ - yosidaJNeg gen hsa n φ) +
         (yosidaJNeg gen hsa n φ - φ) + (φ - ψ)‖ := by abel_nf
    _ ≤ ‖yosidaJNeg gen hsa n ψ - yosidaJNeg gen hsa n φ‖ +
        ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by
          apply le_trans (norm_add_le _ _)
          apply add_le_add_right
          exact norm_add_le _ _
    _ = ‖yosidaJNeg gen hsa n (ψ - φ)‖ +
        ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by
          congr 2
          simp only [map_sub]
    _ ≤ ‖yosidaJNeg gen hsa n‖ * ‖ψ - φ‖ +
        ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by
          apply add_le_add_right
          apply add_le_add_right
          exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖ψ - φ‖ + ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by
          apply add_le_add_right
          apply add_le_add_right
          apply mul_le_mul_of_nonneg_right (yosidaJNeg_norm_bound gen hsa n) (norm_nonneg _)
    _ = ‖ψ - φ‖ + ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by ring
    _ < ε / 3 + ε / 3 + ε / 3 := by
          apply add_lt_add
          apply add_lt_add
          · exact hφ_close
          · rw [← dist_eq_norm]; exact hN n hn
          · rw [norm_sub_rev]; exact hφ_close
    _ = ε := by ring

end QuantumMechanics.Yosida
