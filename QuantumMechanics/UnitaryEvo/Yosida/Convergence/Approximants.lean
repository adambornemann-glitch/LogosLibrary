/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.Convergence.JNegOperator

/-!
# Convergence of Yosida Approximants

This file proves that the Yosida approximants `Aₙ`, `Aₙ⁻`, and `Aₙˢʸᵐ` converge
strongly to the generator `A` on its domain.

## Main results

* `yosidaApprox_eq_J_comp_A`: `Aₙφ = Jₙ(Aφ)` for `φ ∈ D(A)`
* `yosidaApprox_tendsto_on_domain`: `Aₙφ → Aφ` for `φ ∈ D(A)`
* `yosidaApproxNeg_eq_JNeg_A`: `Aₙ⁻φ = Jₙ⁻(Aφ)` for `φ ∈ D(A)`
* `yosidaApproxNeg_tendsto_on_domain`: `Aₙ⁻φ → Aφ` for `φ ∈ D(A)`
* `yosidaApproxSym_eq_avg`: `Aₙˢʸᵐ = ½(Aₙ + Aₙ⁻)`
* `yosidaApproxSym_tendsto_on_domain`: `Aₙˢʸᵐφ → Aφ` for `φ ∈ D(A)`
* `yosidaApprox_commutes_resolvent`: `Aₙ` commutes with resolvents

-/

namespace QuantumMechanics.Yosida

open Complex Filter Topology Resolvent Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U_grp : OneParameterUnitaryGroup (H := H)}

theorem yosidaApprox_eq_J_comp_A
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (φ : H) (hφ : φ ∈ gen.domain) :
    yosidaApprox gen hsa n φ = yosidaJ gen hsa n (gen.op ⟨φ, hφ⟩) := by
  -- Get the key identity: Jₙφ = φ - R(in)(Aφ)
  have hJ_eq := yosidaJ_eq_sub_resolvent_A gen hsa n φ hφ
  -- Rearrange to get R(in)(Aφ) = φ + (in) • R(in)φ
  have hR_Aφ : Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)
             = φ + (I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
    unfold yosidaJ at hJ_eq
    have h_rearrange : Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩) =
             φ - (-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
      calc Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)
          = φ - (φ - Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)) := by
              rw [sub_sub_cancel]
        _ = φ - (-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
              rw [← hJ_eq]
    calc Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)
        = φ - (-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := h_rearrange
      _ = φ + -(-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
          rw [sub_eq_add_neg, neg_smul]
      _ = φ + (I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
          congr 2
          ring
  -- Key scalar identity: (-I * n) * (I * n) = n²
  have h_scalar : (-I * (n : ℂ)) * (I * (n : ℂ)) = (n : ℂ)^2 := by
    calc (-I * (n : ℂ)) * (I * (n : ℂ))
        = -I * I * (n : ℂ) * (n : ℂ) := by ring
      _ = -(I * I) * (n : ℂ)^2 := by ring
      _ = -(I^2) * (n : ℂ)^2 := by rw [sq I]
      _ = -(-1) * (n : ℂ)^2 := by rw [I_sq]
      _ = (n : ℂ)^2 := by ring
  -- Now prove main equality by computing RHS to LHS
  symm
  unfold yosidaApprox yosidaJ
  simp only [resolventAtIn]
  calc (-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)
      = (-I * (n : ℂ)) • (φ + (I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) _ hsa φ) := by
          rw [hR_Aφ]
    _ = (-I * (n : ℂ)) • φ + (-I * (n : ℂ)) • ((I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) _ hsa φ) := by
          rw [smul_add]
    _ = (-I * (n : ℂ)) • φ + ((-I * (n : ℂ)) * (I * (n : ℂ))) • Resolvent.resolvent gen (I * (n : ℂ)) _ hsa φ := by
          rw [smul_smul]
    _ = (-I * (n : ℂ)) • φ + ((n : ℂ)^2) • Resolvent.resolvent gen (I * (n : ℂ)) _ hsa φ := by
          rw [h_scalar]
    _ = ((n : ℂ)^2) • Resolvent.resolvent gen (I * (n : ℂ)) _ hsa φ + (-I * (n : ℂ)) • φ := by
          rw [add_comm]
    _ = ((n : ℂ)^2) • Resolvent.resolvent gen (I * (n : ℂ)) _ hsa φ - (I * (n : ℂ)) • φ := by
          have h_neg : -I * (n : ℂ) = -(I * (n : ℂ)) := by ring
          have h : (-I * (n : ℂ)) • φ = -((I * (n : ℂ)) • φ) := by
            rw [h_neg, neg_smul]
          rw [h, ← sub_eq_add_neg]

theorem yosidaApprox_tendsto_on_domain
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaApprox gen hsa n ψ) atTop (𝓝 (gen.op ⟨ψ, hψ⟩)) := by
  -- Aₙψ = Jₙ(Aψ) by yosidaApprox_eq_J_comp_A
  -- Jₙ(Aψ) → Aψ by yosida_J_tendsto_id applied to (gen.op ⟨ψ, hψ⟩)
  simp only [fun n => yosidaApprox_eq_J_comp_A gen hsa n ψ hψ]
  exact yosida_J_tendsto_id gen hsa (gen.op ⟨ψ, hψ⟩)

lemma yosidaApproxNeg_eq_JNeg_A
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (φ : H) (hφ : φ ∈ gen.domain) :
    yosidaApproxNeg gen hsa n φ = yosidaJNeg gen hsa n (gen.op ⟨φ, hφ⟩) := by
  unfold yosidaApproxNeg yosidaJNeg resolventAtNegIn
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.id_apply]
  set R := Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa
  have h := yosidaJNeg_eq_sub_resolvent_A gen hsa n φ hφ
  have h_RAφ : R (gen.op ⟨φ, hφ⟩) = φ - (I * (n : ℂ)) • R φ := by
    abel_nf ; rw [h, ← h];
    simp_all only [neg_mul, Int.reduceNeg, neg_smul, one_smul, neg_sub, add_sub_cancel, R]
  -- Compute (in)² = -n²
  have h_in_sq : (I * (n : ℂ)) * (I * (n : ℂ)) = -((n : ℂ)^2) := by
    calc (I * (n : ℂ)) * (I * (n : ℂ))
        = I * I * (n : ℂ) * (n : ℂ) := by ring
      _ = (-1) * (n : ℂ) * (n : ℂ) := by rw [I_mul_I]
      _ = -((n : ℂ)^2) := by ring
  symm
  calc (I * (n : ℂ)) • R (gen.op ⟨φ, hφ⟩)
      = (I * (n : ℂ)) • (φ - (I * (n : ℂ)) • R φ) := by rw [h_RAφ]
    _ = (I * (n : ℂ)) • φ - (I * (n : ℂ)) • ((I * (n : ℂ)) • R φ) := smul_sub _ _ _
    _ = (I * (n : ℂ)) • φ - ((I * (n : ℂ)) * (I * (n : ℂ))) • R φ := by rw [smul_smul]
    _ = (I * (n : ℂ)) • φ - (-((n : ℂ)^2)) • R φ := by rw [h_in_sq]
    _ = (I * (n : ℂ)) • φ + (n : ℂ)^2 • R φ := by rw [neg_smul, sub_neg_eq_add]
    _ = (n : ℂ)^2 • R φ + (I * (n : ℂ)) • φ := by abel

lemma yosidaApproxNeg_tendsto_on_domain
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaApproxNeg gen hsa n φ) atTop (𝓝 (gen.op ⟨φ, hφ⟩)) := by
  have h_eq : ∀ n : ℕ+, yosidaApproxNeg gen hsa n φ = yosidaJNeg gen hsa n (gen.op ⟨φ, hφ⟩) :=
    fun n => yosidaApproxNeg_eq_JNeg_A gen hsa n φ hφ
  simp_rw [h_eq]
  exact yosidaJNeg_tendsto_id gen hsa h_dense (gen.op ⟨φ, hφ⟩)

lemma yosidaApproxSym_eq_avg
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    yosidaApproxSym gen hsa n = (1/2 : ℂ) • (yosidaApprox gen hsa n + yosidaApproxNeg gen hsa n) := by
  unfold yosidaApproxSym yosidaApprox yosidaApproxNeg resolventAtIn resolventAtNegIn
  ext ψ
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
             ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  set R_pos := resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa
  set R_neg := resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa
  have h : (1 / 2 : ℂ) * (n : ℂ)^2 = (n : ℂ)^2 / 2 := by ring
  calc ((n : ℂ)^2 / 2) • (R_pos ψ + R_neg ψ)
      = ((n : ℂ)^2 / 2) • R_pos ψ + ((n : ℂ)^2 / 2) • R_neg ψ := smul_add _ _ _
    _ = (1 / 2 : ℂ) • ((n : ℂ)^2 • R_pos ψ) + (1 / 2 : ℂ) • ((n : ℂ)^2 • R_neg ψ) := by
        simp only [smul_smul]; ring_nf
    _ = (1 / 2 : ℂ) • ((n : ℂ)^2 • R_pos ψ + (n : ℂ)^2 • R_neg ψ) := by rw [← smul_add]
    _ = (1 / 2 : ℂ) • ((n : ℂ)^2 • R_pos ψ - (I * (n : ℂ)) • ψ + ((n : ℂ)^2 • R_neg ψ + (I * (n : ℂ)) • ψ)) := by
        congr 1; abel
    _ = (1 / 2 : ℂ) • (((n : ℂ)^2 • R_pos ψ - (I * (n : ℂ)) • ψ) + ((n : ℂ)^2 • R_neg ψ + (I * (n : ℂ)) • ψ)) := by
        congr 1

theorem yosidaApproxSym_tendsto_on_domain
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaApproxSym gen hsa n φ) atTop (𝓝 (gen.op ⟨φ, hφ⟩)) := by
  have h_eq : ∀ n : ℕ+, yosidaApproxSym gen hsa n φ =
      (1/2 : ℂ) • (yosidaApprox gen hsa n φ + yosidaApproxNeg gen hsa n φ) := by
    intro n
    calc yosidaApproxSym gen hsa n φ
        = ((1/2 : ℂ) • (yosidaApprox gen hsa n + yosidaApproxNeg gen hsa n)) φ := by
            rw [yosidaApproxSym_eq_avg]
      _ = (1/2 : ℂ) • (yosidaApprox gen hsa n φ + yosidaApproxNeg gen hsa n φ) := by
            simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
  simp_rw [h_eq]
  have h_pos := yosidaApprox_tendsto_on_domain gen hsa φ hφ
  have h_neg := yosidaApproxNeg_tendsto_on_domain gen hsa h_dense φ hφ
  have h_sum : Tendsto (fun n : ℕ+ => yosidaApprox gen hsa n φ + yosidaApproxNeg gen hsa n φ)
      atTop (𝓝 (gen.op ⟨φ, hφ⟩ + gen.op ⟨φ, hφ⟩)) := h_pos.add h_neg
  have h_half : Tendsto (fun n : ℕ+ => (1/2 : ℂ) • (yosidaApprox gen hsa n φ + yosidaApproxNeg gen hsa n φ))
      atTop (𝓝 ((1/2 : ℂ) • (gen.op ⟨φ, hφ⟩ + gen.op ⟨φ, hφ⟩))) := h_sum.const_smul (1/2 : ℂ)
  have h_simp : (1/2 : ℂ) • (gen.op ⟨φ, hφ⟩ + gen.op ⟨φ, hφ⟩) = gen.op ⟨φ, hφ⟩ := by
    rw [← two_smul ℂ (gen.op ⟨φ, hφ⟩), smul_smul]
    norm_num
  rw [h_simp] at h_half
  exact h_half

theorem yosidaApprox_commutes_resolvent
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (z : ℂ) (hz : z.im ≠ 0) :
    (yosidaApprox gen hsa n).comp (resolvent gen z hz hsa)
      = (resolvent gen z hz hsa).comp (yosidaApprox gen hsa n) := by
  -- First establish that resolvents commute
  have h_resolvent_comm : (resolventAtIn gen hsa n).comp (resolvent gen z hz hsa) =
                          (resolvent gen z hz hsa).comp (resolventAtIn gen hsa n) := by
    unfold resolventAtIn
    by_cases h_eq : I * (n : ℂ) = z
    · have hz' : (I * (n : ℂ)).im ≠ 0 := I_mul_pnat_im_ne_zero n
      have h_res_eq : resolvent gen (I * (n : ℂ)) hz' hsa = resolvent gen z hz hsa := by
        subst h_eq
        congr
      rw [h_res_eq]
    · have h_diff_ne : I * (n : ℂ) - z ≠ 0 := sub_ne_zero.mpr h_eq
      have h_diff_ne' : z - I * (n : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h_eq)
      have h_id1 := resolvent_identity gen hsa (I * (n : ℂ)) z (I_mul_pnat_im_ne_zero n) hz
      have h_id2 := resolvent_identity gen hsa z (I * (n : ℂ)) hz (I_mul_pnat_im_ne_zero n)
      have h1 : (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa).comp (resolvent gen z hz hsa) =
                (I * (n : ℂ) - z)⁻¹ • (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa - resolvent gen z hz hsa) := by
        symm
        calc (I * (n : ℂ) - z)⁻¹ • (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa - resolvent gen z hz hsa)
            = (I * (n : ℂ) - z)⁻¹ • ((I * (n : ℂ) - z) • (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa).comp (resolvent gen z hz hsa)) := by
                rw [h_id1]
          _ = (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa).comp (resolvent gen z hz hsa) := by
                rw [smul_smul, inv_mul_cancel₀ h_diff_ne, one_smul]
      have h2 : (resolvent gen z hz hsa).comp (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa) =
                (z - I * (n : ℂ))⁻¹ • (resolvent gen z hz hsa - resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa) := by
        symm
        calc (z - I * (n : ℂ))⁻¹ • (resolvent gen z hz hsa - resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa)
            = (z - I * (n : ℂ))⁻¹ • ((z - I * (n : ℂ)) • (resolvent gen z hz hsa).comp (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa)) := by
                rw [h_id2]
          _ = (resolvent gen z hz hsa).comp (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa) := by
                rw [smul_smul, inv_mul_cancel₀ h_diff_ne', one_smul]
      rw [h1, h2]
      have h_inv_neg : (z - I * (n : ℂ))⁻¹ = -(I * (n : ℂ) - z)⁻¹ := by
        rw [← neg_sub, neg_inv]
      have h_sub_neg : resolvent gen z hz hsa - resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa =
                      -(resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa - resolvent gen z hz hsa) := by
        rw [neg_sub]
      rw [h_inv_neg, h_sub_neg, smul_neg, neg_smul, neg_neg]
  -- Now expand yosidaApprox and use resolvent commutativity
  unfold yosidaApprox
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  congr 1
  unfold resolventAtIn
  simp only [resolventAtIn] at h_resolvent_comm
  rw [h_resolvent_comm]

end QuantumMechanics.Yosida
