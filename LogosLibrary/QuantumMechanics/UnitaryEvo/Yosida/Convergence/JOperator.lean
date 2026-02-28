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
    simp [norm_eq_zero.mp h_Aφ_zero, dist_self, hε]
  · -- Case: ‖Aφ‖ > 0
    have h_Aφ_pos : 0 < ‖gen.op ⟨φ, hφ⟩‖ := (norm_nonneg _).lt_of_ne' h_Aφ_zero
    use ⟨Nat.ceil (‖gen.op ⟨φ, hφ⟩‖ / ε) + 1, Nat.add_one_pos _⟩
    intro n hn
    -- Rewrite Jₙφ - φ = -R(in)(Aφ) and take norms
    have h_eq : dist ((-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ))
        (I_mul_pnat_im_ne_zero n) hsa φ) φ =
        ‖Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa
        (gen.op ⟨φ, hφ⟩)‖ := by
      rw [dist_eq_norm, yosidaJ_eq_sub_resolvent_A gen hsa n φ hφ]
      simp [norm_neg]
    rw [h_eq]
    -- ‖R(in)(Aφ)‖ ≤ ‖R(in)‖ · ‖Aφ‖ ≤ (1/n) · ‖Aφ‖ < ε
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr n.pos
    calc ‖Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa
            (gen.op ⟨φ, hφ⟩)‖
        ≤ ‖Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ *
            ‖gen.op ⟨φ, hφ⟩‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 / (n : ℝ)) * ‖gen.op ⟨φ, hφ⟩‖ := by
          gcongr
          calc ‖Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖
              ≤ 1 / |(I * (n : ℂ)).im| := resolvent_bound gen hsa _ _
            _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]
      _ < ε := by
          rw [one_div, inv_mul_lt_iff₀ hn_pos]
          have h1 : (⌈‖gen.op ⟨φ, hφ⟩‖ / ε⌉₊ + 1 : ℕ) ≤ n := hn
          calc ‖gen.op ⟨φ, hφ⟩‖
              = (‖gen.op ⟨φ, hφ⟩‖ / ε) * ε := by field_simp
            _ ≤ ↑⌈‖gen.op ⟨φ, hφ⟩‖ / ε⌉₊ * ε := by gcongr; exact Nat.le_ceil _
            _ < (↑⌈‖gen.op ⟨φ, hφ⟩‖ / ε⌉₊ + 1) * ε := by nlinarith
            _ ≤ (n : ℝ) * ε := by gcongr; exact_mod_cast h1

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
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp
    (gen.dense_domain.closure_eq ▸ Set.mem_univ ψ) (ε / 3) (by linarith)
  -- Step 2: Get N such that Jₙφ is close to φ for n ≥ N
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp
    (yosidaJ_tendsto_on_domain gen hsa φ hφ_mem)) (ε / 3) (by linarith)
  -- Step 3: Triangle inequality
  use N
  intro n hn
  calc dist (J n ψ) ψ
      ≤ dist (J n ψ) (J n φ) + dist (J n φ) φ + dist φ ψ :=
        dist_triangle4 _ _ _ _
    _ = ‖J n (ψ - φ)‖ + dist (J n φ) φ + dist φ ψ := by
        rw [dist_eq_norm, ContinuousLinearMap.map_sub]
    _ ≤ ‖J n‖ * ‖ψ - φ‖ + dist (J n φ) φ + dist φ ψ := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖ψ - φ‖ + dist (J n φ) φ + dist φ ψ := by
        gcongr; exact yosidaJ_norm_bound gen hsa n
    _ = dist ψ φ + dist (J n φ) φ + dist φ ψ := by
        rw [one_mul, ← dist_eq_norm]
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact Metric.mem_ball.mp (hN n hn)
        · exact Metric.mem_ball'.mp hφ_close
    _ = ε := by ring

end QuantumMechanics.Yosida
