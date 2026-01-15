/-
Copyright (c) 2025 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.Duhamel.Formula

/-!
# Duhamel Estimates and Convergence

This file uses Duhamel's formula to prove estimates on the difference
`U(t)φ - exp(i·Aₙˢʸᵐ·t)φ` and establishes convergence of the Yosida
exponentials to the unitary group.

## Main results

* `duhamel_estimate`: `‖U(t)φ - exp(i·Aₙˢʸᵐ·t)φ‖ ≤ |t| · sup_s ‖Aφ - Aₙφ‖`
* `yosidaApproxSym_uniform_convergence_on_orbit`: Uniform convergence on orbits
* `expBounded_yosidaApproxSym_tendsto_unitary`: `exp(i·Aₙˢʸᵐ·t)φ → U(t)φ`
* `expBounded_yosidaApproxSym_cauchy`: The sequence is Cauchy for all `ψ`

-/

namespace QuantumMechanics.Yosida

open Complex Filter Topology MeasureTheory Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U_grp : OneParameterUnitaryGroup (H := H)}

/-! ### Duhamel estimate -/

lemma duhamel_estimate
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    ‖U_grp.U t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ ≤
    |t| * ⨆ (s : Set.Icc 0 |t|), ‖gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s φ)‖ := by
  rw [duhamel_identity gen hsa n t φ hφ]
  set B := I • yosidaApproxSym gen hsa n
  set C := ⨆ (s : Set.Icc 0 |t|), ‖gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ -
                                   yosidaApproxSym gen hsa n (U_grp.U s φ)‖
  have hB : ContinuousLinearMap.adjoint B = -B :=
    smul_I_skewSelfAdjoint (yosidaApproxSym gen hsa n) (yosidaApproxSym_selfAdjoint gen hsa n)
  have h_isometric : ∀ τ v, ‖expBounded B τ v‖ = ‖v‖ := by
    intro τ v
    have h_unitary := expBounded_mem_unitary B hB τ
    exact unitary.norm_map ⟨expBounded B τ, h_unitary⟩ v
  have h_bound := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := C)
                    (f := duhamelIntegrand gen hsa n t φ hφ)
  calc ‖∫ s in (0)..t, duhamelIntegrand gen hsa n t φ hφ s‖
      ≤ C * |t - 0| := h_bound ?_
    _ = C * |t| := by simp only [sub_zero]
    _ = |t| * C := mul_comm C |t|
  intro s hs
  unfold duhamelIntegrand
  rw [h_isometric]
  rw [← smul_sub, norm_smul, norm_I, one_mul]
  rw [Set.mem_uIoc] at hs
  have h_bdd : BddAbove (Set.range (fun (s : Set.Icc 0 |t|) =>
    ‖gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s φ)‖)) := by
    have h_const : ∀ s : Set.Icc 0 |t|,
        ‖gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s φ)‖ =
        ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖ := by
      intro s
      exact norm_gen_diff_constant gen hsa n s φ hφ
    use ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖
    intro x hx
    simp only [Set.mem_range] at hx
    obtain ⟨s, hs⟩ := hx
    rw [← hs, h_const]
  cases hs with
  | inl h =>
    have hs_pos : 0 ≤ s := le_of_lt h.1
    have hs_le : s ≤ |t| := by
      have h1 : 0 < s := h.1
      have h2 : s ≤ t := h.2
      have h3 : 0 ≤ t := le_trans (le_of_lt h1) h2
      rw [abs_of_nonneg h3]
      exact h2
    apply le_ciSup_of_le h_bdd ⟨s, hs_pos, hs_le⟩
    rfl
  | inr h =>
    rw [norm_gen_diff_constant gen hsa n s φ hφ]
    have h0_mem : (0 : ℝ) ∈ Set.Icc 0 |t| := by
      constructor
      · exact le_refl 0
      · exact abs_nonneg t
    have h_at_0 : ‖gen.op ⟨U_grp.U 0 φ, gen.domain_invariant 0 φ hφ⟩ -
                  yosidaApproxSym gen hsa n (U_grp.U 0 φ)‖ ≤ C := by
      apply le_ciSup_of_le h_bdd ⟨0, h0_mem⟩
      rfl
    simp only [U_grp.identity, ContinuousLinearMap.id_apply] at h_at_0
    exact h_at_0

/-! ### Uniform convergence on orbits -/

lemma yosidaApproxSym_uniform_convergence_on_orbit
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => ⨆ (s : Set.Icc 0 |t|),
             ‖gen.op ⟨U_grp.U s.val φ, gen.domain_invariant s.val φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s.val φ)‖)
            atTop (𝓝 0) := by
  have h_const : ∀ n : ℕ+, ∀ s : Set.Icc 0 |t|,
      ‖gen.op ⟨U_grp.U s.val φ, gen.domain_invariant s.val φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s.val φ)‖ =
      ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖ :=
    fun n s => norm_gen_diff_constant gen hsa n s.val φ hφ
  have h_nonempty : Nonempty (Set.Icc (0 : ℝ) |t|) := ⟨⟨0, le_refl 0, abs_nonneg t⟩⟩
  have h_sup_eq : ∀ n : ℕ+,
      (⨆ (s : Set.Icc 0 |t|), ‖gen.op ⟨U_grp.U s.val φ, gen.domain_invariant s.val φ hφ⟩ -
                              yosidaApproxSym gen hsa n (U_grp.U s.val φ)‖) =
      ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖ := by
    intro n
    simp_rw [h_const n]
    exact ciSup_const
  simp_rw [h_sup_eq]
  have h_tendsto := yosidaApproxSym_tendsto_on_domain gen hsa h_dense φ hφ
  have h_norm : Tendsto (fun n : ℕ+ => ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖) atTop (𝓝 0) := by
    have h : Tendsto (fun n => gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := gen.op ⟨φ, hφ⟩)).sub h_tendsto
      simp only [sub_self] at this
      convert this using 1
    exact tendsto_norm_zero.comp h
  exact h_norm

/-! ### Convergence to unitary group -/

lemma expBounded_yosidaApproxSym_tendsto_unitary
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ)
            atTop (𝓝 (U_grp.U t φ)) := by
  by_cases ht : t = 0
  · simp only [ht]
    have h_exp_zero : ∀ n : ℕ+, expBounded (I • yosidaApproxSym gen hsa n) 0 φ = φ :=
      fun n => expBounded_at_zero _ φ
    have h_U_zero : U_grp.U 0 φ = φ := unitary_group_at_zero φ
    simp_rw [h_exp_zero, h_U_zero]
    exact tendsto_const_nhds
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    have h_unif := yosidaApproxSym_uniform_convergence_on_orbit gen hsa h_dense t φ hφ
    rw [Metric.tendsto_atTop] at h_unif
    have ht_pos : 0 < |t| + 1 := by linarith [abs_nonneg t]
    have hεt : ε / (|t| + 1) > 0 := div_pos hε ht_pos
    obtain ⟨N, hN⟩ := h_unif (ε / (|t| + 1)) hεt
    use N
    intro n hn
    rw [dist_eq_norm]
    calc ‖expBounded (I • yosidaApproxSym gen hsa n) t φ - U_grp.U t φ‖
        = ‖U_grp.U t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ := norm_sub_rev _ _
      _ ≤ |t| * ⨆ (s : Set.Icc 0 |t|), ‖gen.op ⟨U_grp.U s.val φ, gen.domain_invariant s.val φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s.val φ)‖ :=
          duhamel_estimate gen hsa n t φ hφ
      _ < |t| * (ε / (|t| + 1)) := by
          apply mul_lt_mul_of_pos_left _ (abs_pos.mpr ht)
          specialize hN n hn
          simp only [dist_zero_right, Real.norm_eq_abs] at hN
          rw [abs_of_nonneg] at hN
          · exact hN
          · apply Real.iSup_nonneg
            intro s
            exact norm_nonneg _
      _ < (|t| + 1) * (ε / (|t| + 1)) := by
          apply mul_lt_mul_of_pos_right _ hεt
          linarith
      _ = ε := mul_div_cancel₀ ε (ne_of_gt ht_pos)

/-! ### Cauchy sequence -/

theorem expBounded_yosidaApproxSym_cauchy
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ : H) :
    CauchySeq (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t ψ) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε3 : ε / 3 > 0 := by linarith
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp
    (h_dense.closure_eq ▸ Set.mem_univ ψ) (ε / 3) hε3
  rw [dist_eq_norm] at hφ_close
  have h_cauchy_φ : CauchySeq (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ) := by
    apply Filter.Tendsto.cauchySeq
    exact expBounded_yosidaApproxSym_tendsto_unitary gen hsa h_dense t φ hφ_mem
  rw [Metric.cauchySeq_iff] at h_cauchy_φ
  obtain ⟨N, hN⟩ := h_cauchy_φ (ε / 3) hε3
  use N
  intro m hm n hn
  rw [dist_eq_norm]
  calc ‖expBounded (I • yosidaApproxSym gen hsa m) t ψ -
        expBounded (I • yosidaApproxSym gen hsa n) t ψ‖
      = ‖(expBounded (I • yosidaApproxSym gen hsa m) t ψ - expBounded (I • yosidaApproxSym gen hsa m) t φ) +
         (expBounded (I • yosidaApproxSym gen hsa m) t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ) +
         (expBounded (I • yosidaApproxSym gen hsa n) t φ - expBounded (I • yosidaApproxSym gen hsa n) t ψ)‖ := by
          congr 1; abel
    _ ≤ ‖expBounded (I • yosidaApproxSym gen hsa m) t ψ - expBounded (I • yosidaApproxSym gen hsa m) t φ‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa m) t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa n) t φ - expBounded (I • yosidaApproxSym gen hsa n) t ψ‖ := by
          apply le_trans (norm_add_le _ _)
          apply add_le_add_right
          exact norm_add_le _ _
    _ = ‖expBounded (I • yosidaApproxSym gen hsa m) t (ψ - φ)‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa m) t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa n) t (φ - ψ)‖ := by
          congr 1
          · congr 1
            · rw [← ContinuousLinearMap.map_sub]
          · rw [← ContinuousLinearMap.map_sub]
    _ = ‖ψ - φ‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa m) t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ +
        ‖φ - ψ‖ := by
          congr 1
          · congr 1
            · exact expBounded_yosidaApproxSym_isometry gen hsa m t (ψ - φ)
          · exact expBounded_yosidaApproxSym_isometry gen hsa n t (φ - ψ)
    _ < ε / 3 + ε / 3 + ε / 3 := by
          apply add_lt_add
          apply add_lt_add
          · exact hφ_close
          · rw [← dist_eq_norm]; exact hN m hm n hn
          · rw [norm_sub_rev]; exact hφ_close
    _ = ε := by ring

end QuantumMechanics.Yosida
