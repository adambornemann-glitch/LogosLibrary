/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: ExpBounded/Unitary.lean
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.ExpBounded.Adjoint

/-!
# Unitarity of Exponentials of Skew-Adjoint Operators

This file proves that the exponential of a skew-adjoint operator is unitary,
and establishes derivative formulas for the bounded exponential.

## Main results

* `expBounded_skewAdjoint_unitary`: If `B* = -B`, then `exp(tB)*exp(tB) = exp(tB)exp(tB)* = 1`
* `expBounded_mem_unitary`: `exp(tB) ∈ unitary` when `B` is skew-adjoint
* `expBounded_yosidaApproxSym_unitary`: `exp(i·Aₙˢʸᵐ·t)` preserves inner products
* `expBounded_yosidaApproxSym_isometry`: `exp(i·Aₙˢʸᵐ·t)` is an isometry
* `expBounded_hasDerivAt`: Derivative of the exponential

-/

namespace QuantumMechanics.Yosida

open Complex Filter Topology InnerProductSpace Resolvent Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U_grp : OneParameterUnitaryGroup (H := H)}

/-! ### Skew-adjoint implies unitary exponential -/

theorem expBounded_skewAdjoint_unitary (B : H →L[ℂ] H) (hB : B.adjoint = -B) (t : ℝ) :
    (expBounded B t).adjoint.comp (expBounded B t) = ContinuousLinearMap.id ℂ H ∧
    (expBounded B t).comp (expBounded B t).adjoint = ContinuousLinearMap.id ℂ H := by
  -- exp(tB)* = exp(tB*) = exp(t(-B)) = exp(-tB)
  have h_adj : (expBounded B t).adjoint = expBounded B (-t) := by
    rw [adjoint_expBounded]
    rw [hB]
    unfold expBounded
    congr 1
    ext k
    congr 2
    ext x
    simp only [ofReal_neg, neg_smul, smul_neg]
  constructor
  · -- exp(tB)* ∘ exp(tB) = exp(-tB) ∘ exp(tB) = exp(0) = I
    rw [h_adj]
    rw [← expBounded_group_law B (-t) t]
    simp only [neg_add_cancel]
    unfold expBounded
    simp only [ofReal_zero, zero_smul]
    have h_eq : (fun k : ℕ => (1 / k.factorial : ℂ) • (0 : H →L[ℂ] H) ^ k) =
                (fun k : ℕ => if k = 0 then 1 else 0) := by
      ext k
      cases k with
      | zero => simp
      | succ k => simp [pow_succ]
    rw [h_eq]
    rw [tsum_eq_single 0]
    · abel
    · intro k hk
      simp [hk]
  · -- exp(tB) ∘ exp(tB)* = exp(tB) ∘ exp(-tB) = exp(0) = I
    rw [h_adj]
    rw [← expBounded_group_law B t (-t)]
    simp only [add_neg_cancel]
    unfold expBounded
    simp only [ofReal_zero, zero_smul]
    have h_eq : (fun k : ℕ => (1 / k.factorial : ℂ) • (0 : H →L[ℂ] H) ^ k) =
                (fun k : ℕ => if k = 0 then 1 else 0) := by
      ext k
      cases k with
      | zero => simp
      | succ k => simp [pow_succ]
    rw [h_eq]
    rw [tsum_eq_single 0]
    · abel
    · intro k hk
      simp [hk]

lemma expBounded_mem_unitary (B : H →L[ℂ] H) (hB : ContinuousLinearMap.adjoint B = -B) (t : ℝ) :
    expBounded B t ∈ unitary (H →L[ℂ] H) := by
  haveI : NormedAlgebra ℚ (H →L[ℂ] H) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  rw [Unitary.mem_iff]
  constructor
  · -- star (exp B t) * exp B t = 1
    have h1 : star (expBounded B t) = expBounded (-B) t := by
      rw [ContinuousLinearMap.star_eq_adjoint, adjoint_expBounded, hB]
    rw [h1, expBounded_eq_exp, expBounded_eq_exp]
    have h_comm : Commute ((t : ℂ) • (-B)) ((t : ℂ) • B) := by
      unfold Commute SemiconjBy
      simp_all only [smul_neg, coe_smul, Algebra.mul_smul_comm, neg_mul,
        Algebra.smul_mul_assoc, mul_neg]
    have h2 := (NormedSpace.exp_add_of_commute h_comm).symm
    simp only [smul_neg, neg_add_cancel, NormedSpace.exp_zero] at h2
    simp_all only [smul_neg, coe_smul, Commute.neg_left_iff, Commute.refl]
  · -- exp B t * star (exp B t) = 1
    have h1 : star (expBounded B t) = expBounded (-B) t := by
      rw [ContinuousLinearMap.star_eq_adjoint, adjoint_expBounded, hB]
    rw [h1, expBounded_eq_exp, expBounded_eq_exp]
    have h_comm : Commute ((t : ℂ) • B) ((t : ℂ) • (-B)) := by
      unfold Commute SemiconjBy
      simp_all only [coe_smul, smul_neg, mul_neg, Algebra.mul_smul_comm,
        Algebra.smul_mul_assoc, neg_mul]
    have h2 := (NormedSpace.exp_add_of_commute h_comm).symm
    simp only [smul_neg, add_neg_cancel, NormedSpace.exp_zero] at h2
    simp_all only [smul_neg, coe_smul]

/-! ### Unitarity for Yosida approximants -/

lemma smul_I_skewSelfAdjoint (A : H →L[ℂ] H) (hA : ContinuousLinearMap.adjoint A = A) :
    ContinuousLinearMap.adjoint (I • A) = -(I • A) := by
  have h := ContinuousLinearMap.adjoint.map_smulₛₗ I A
  rw [h, hA, starRingEnd_apply, star_def, conj_I]
  simp only [neg_smul]

theorem expBounded_yosidaApproxSym_unitary
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (ψ φ : H) :
    ⟪expBounded (I • yosidaApproxSym gen hsa n) t ψ,
     expBounded (I • yosidaApproxSym gen hsa n) t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
  have h_skew := I_smul_yosidaApproxSym_skewAdjoint gen hsa n
  have h_unitary := expBounded_skewAdjoint_unitary (I • yosidaApproxSym gen hsa n) h_skew t
  let U := expBounded (I • yosidaApproxSym gen hsa n) t
  calc ⟪U ψ, U φ⟫_ℂ
      = ⟪ψ, U.adjoint (U φ)⟫_ℂ := (ContinuousLinearMap.adjoint_inner_right U ψ (U φ)).symm
    _ = ⟪ψ, (U.adjoint.comp U) φ⟫_ℂ := rfl
    _ = ⟪ψ, (ContinuousLinearMap.id ℂ H) φ⟫_ℂ := by rw [h_unitary.1]
    _ = ⟪ψ, φ⟫_ℂ := by simp

theorem expBounded_yosidaApproxSym_isometry
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (ψ : H) :
    ‖expBounded (I • yosidaApproxSym gen hsa n) t ψ‖ = ‖ψ‖ := by
  set U := expBounded (I • yosidaApproxSym gen hsa n) t with hU
  have h_inner := expBounded_yosidaApproxSym_unitary gen hsa n t ψ ψ
  have h1 : ‖U ψ‖^2 = re ⟪U ψ, U ψ⟫_ℂ := (inner_self_eq_norm_sq (𝕜 := ℂ) (U ψ)).symm
  have h2 : ‖ψ‖^2 = re ⟪ψ, ψ⟫_ℂ := (inner_self_eq_norm_sq (𝕜 := ℂ) ψ).symm
  have h_sq : ‖U ψ‖^2 = ‖ψ‖^2 := by
    rw [h1, h2, h_inner]
  have h_nonneg1 : 0 ≤ ‖U ψ‖ := norm_nonneg _
  have h_nonneg2 : 0 ≤ ‖ψ‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖U ψ‖ - ‖ψ‖), sq_nonneg (‖U ψ‖ + ‖ψ‖), h_sq, h_nonneg1, h_nonneg2]

theorem expBounded_yosida_norm_le
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) :
    ‖expBounded (I • yosidaApprox gen hsa n) t‖ ≤
    Real.exp (|t| * ‖I • yosidaApprox gen hsa n‖) :=
  expBounded_norm_bound _ _

/-! ### Derivatives of exponential -/

/-- Key lemma: derivative of exp at 0 along the direction B. -/
lemma expBounded_hasDerivAt_zero (B : H →L[ℂ] H) :
    HasDerivAt (fun τ : ℝ => expBounded B τ) B 0 := by
  haveI : IsScalarTower ℝ ℂ H := RestrictScalars.isScalarTower ℝ ℂ H
  haveI : CompleteSpace (H →L[ℂ] H) := inferInstance
  letI : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _  -- letI not haveI!
  haveI : IsScalarTower ℝ ℂ (H →L[ℂ] H) :=
    ⟨fun r c f => ContinuousLinearMap.ext fun x => smul_assoc r c (f x)⟩
  simp_rw [expBounded_eq_exp]
  have h_path : HasDerivAt (fun t : ℝ => (t : ℂ) • B) B 0 := by
    have h := (ofRealCLM.hasDerivAt (x := (0 : ℝ))).smul_const B
    convert h using 1
    exact (one_smul ℂ B).symm
  have h_fderiv : HasFDerivAt NormedSpace.exp
      (1 : (H →L[ℂ] H) →L[ℝ] (H →L[ℂ] H)) ((fun t : ℝ => (t : ℂ) • B) 0) := by
    simp only [ofReal_zero, zero_smul]
    show HasFDerivAt NormedSpace.exp (1 : (H →L[ℂ] H) →L[ℝ] (H →L[ℂ] H)) 0
    exact hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := H →L[ℂ] H)
  have h_comp := h_fderiv.comp_hasDerivAt (0 : ℝ) h_path
  convert h_comp using 1

/-- Derivative of the bounded exponential at any point. -/
lemma expBounded_hasDerivAt (B : H →L[ℂ] H) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => expBounded B t) (B.comp (expBounded B τ)) τ := by
  haveI : IsScalarTower ℝ ℂ H := RestrictScalars.isScalarTower ℝ ℂ H
  letI : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
  haveI : IsScalarTower ℝ ℂ (H →L[ℂ] H) :=
    ⟨fun r c f => ContinuousLinearMap.ext fun x => smul_assoc r c (f x)⟩
  have h_eq : ∀ t, expBounded B t = (expBounded B τ).comp (expBounded B (t - τ)) := by
    intro t
    rw [← expBounded_add_smul]
    congr 1; ring
  have h_shift : HasDerivAt (fun t => expBounded B (t - τ)) B τ := by
    have h0 : HasDerivAt (fun t => expBounded B t) B (τ - τ) := by
      simp only [sub_self]
      exact expBounded_hasDerivAt_zero B
    exact h0.comp_sub_const τ τ
  have h_val : expBounded B (τ - τ) = 1 := by simp only [sub_self, expBounded_at_zero']
  have h_post : HasDerivAt (fun t => (expBounded B τ).comp (expBounded B (t - τ)))
                           ((expBounded B τ).comp B) τ := by
    set A := expBounded B τ
    have h_clm : HasFDerivAt (fun T : H →L[ℂ] H => A.comp T)
                             ((ContinuousLinearMap.compL ℂ H H H) A)
                             (expBounded B (τ - τ)) :=
      ((ContinuousLinearMap.compL ℂ H H H) A).hasFDerivAt
    have h_clm' := h_clm.restrictScalars ℝ   -- was: ℂ (no-op)
    have h_comp := h_clm'.comp_hasDerivAt τ h_shift
    convert h_comp using 1
  have h_comm : (expBounded B τ).comp B = B.comp (expBounded B τ) := by
    ext ψ
    simp only [ContinuousLinearMap.comp_apply]
    have := B_commute_expBounded B τ
    unfold Commute SemiconjBy at this
    exact congrFun (congrArg DFunLike.coe this.symm) ψ
  rw [h_comm] at h_post
  exact h_post.congr_of_eventuallyEq (Eventually.of_forall (fun t => (h_eq t)))

end QuantumMechanics.Yosida
