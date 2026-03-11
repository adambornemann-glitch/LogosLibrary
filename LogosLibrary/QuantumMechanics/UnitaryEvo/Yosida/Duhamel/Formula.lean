/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Duhamel/Formula.lean
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.Duhamel.Commutation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-!
# Duhamel's Formula

This file proves Duhamel's formula relating the unitary group `U(t)` to the
Yosida exponential approximants:

`U(t)φ - exp(i·Aₙˢʸᵐ·t)φ = ∫₀ᵗ exp(i·Aₙˢʸᵐ·(t-s)) · (iA - i·Aₙˢʸᵐ)(U(s)φ) ds`

## Main definitions

* `duhamelIntegrand`: The integrand in Duhamel's formula

## Main results

* `unitary_hasDerivAt_zero`: `d/dt[U(t)φ]|_{t=0} = i·Aφ` for `φ ∈ D(A)`
* `unitary_hasDerivAt`: `d/dt[U(t)φ]|_{t=s} = i·A(U(s)φ)` for `φ ∈ D(A)`
* `duhamel_identity`: The Duhamel formula

-/

namespace QuantumMechanics.Yosida

open Complex Filter Topology MeasureTheory Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U_grp : OneParameterUnitaryGroup (H := H)}

/-! ### Duhamel integrand -/

/-- The integrand in Duhamel's formula. -/
noncomputable def duhamelIntegrand
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) (s : ℝ) : H :=
  expBounded (I • yosidaApproxSym gen hsa n) (t - s)
    (I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ - I • yosidaApproxSym gen hsa n (U_grp.U s φ))

lemma duhamelIntegrand_continuous
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    Continuous (duhamelIntegrand gen hsa n t φ hφ) := by
  unfold duhamelIntegrand
  have h_comm : ∀ s, gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ =
                     U_grp.U s (gen.op ⟨φ, hφ⟩) :=
    fun s => generator_commutes_unitary gen s φ hφ
  have h_Uφ_cont : Continuous (fun s => U_grp.U s φ) := U_grp.strong_continuous φ
  have h_UAφ_cont : Continuous (fun s => U_grp.U s (gen.op ⟨φ, hφ⟩)) :=
    U_grp.strong_continuous (gen.op ⟨φ, hφ⟩)
  have h_Aorbit_cont : Continuous (fun s => gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩) := by
    simp_rw [h_comm]; exact h_UAφ_cont
  have h_yosida_cont : Continuous (fun s => yosidaApproxSym gen hsa n (U_grp.U s φ)) :=
    (yosidaApproxSym gen hsa n).continuous.comp h_Uφ_cont
  have h_diff_cont : Continuous (fun s =>
      I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ -
      I • yosidaApproxSym gen hsa n (U_grp.U s φ)) :=
    (continuous_const.smul h_Aorbit_cont).sub (continuous_const.smul h_yosida_cont)
  set B := I • yosidaApproxSym gen hsa n
  have h_exp_cont_τ : Continuous (fun τ : ℝ => expBounded B τ) := by
    unfold expBounded
    have h_eq : ∀ τ : ℝ, (∑' k : ℕ, (1 / k.factorial : ℂ) • ((τ : ℂ) • B) ^ k) =
                NormedSpace.exp ((τ : ℂ) • B) := by
      intro τ
      rw [NormedSpace.exp_eq_tsum ℂ]
      congr 1; ext k; simp only [one_div]
    simp_rw [h_eq]
    have h_smul_cont : Continuous (fun τ : ℝ => (τ : ℂ) • B) :=
      continuous_ofReal.smul continuous_const
    haveI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
    have h_exp_cont : Continuous (fun T : H →L[ℂ] H => NormedSpace.exp T) :=
      NormedSpace.exp_continuous
    exact h_exp_cont.comp h_smul_cont
  have h_exp_cont_s : Continuous (fun s : ℝ => expBounded B (t - s)) :=
    h_exp_cont_τ.comp (continuous_const.sub continuous_id)
  exact h_exp_cont_s.clm_apply h_diff_cont

lemma duhamelIntegrand_bound
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) (s : ℝ)
    (_ : s ∈ Set.Icc 0 |t|) :
    ‖duhamelIntegrand gen hsa n t φ hφ s‖ ≤
    ‖I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ - I • yosidaApproxSym gen hsa n (U_grp.U s φ)‖ := by
  unfold duhamelIntegrand
  rw [expBounded_yosidaApproxSym_isometry gen hsa n (t - s)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {U_grp : OneParameterUnitaryGroup (H := H)}

/-! ### Derivative of unitary group -/

lemma unitary_hasDerivAt_zero
    (gen : Generator U_grp) (φ : H) (hφ : φ ∈ gen.domain) :
    HasDerivAt (fun t => U_grp.U t φ) (I • gen.op ⟨φ, hφ⟩) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h_U0 : U_grp.U 0 φ = φ := by
    have := U_grp.identity
    simp only [this, ContinuousLinearMap.id_apply]
  have h_gen := gen.generator_formula ⟨φ, hφ⟩
  haveI : IsScalarTower ℝ ℂ H := RestrictScalars.isScalarTower ℝ ℂ H
  have h_slope_eq : ∀ t : ℝ, t ≠ 0 →
    slope (fun t => U_grp.U t φ) 0 t = (t : ℂ)⁻¹ • (U_grp.U t φ - φ) := by
    intro t ht
    simp only [slope, vsub_eq_sub, h_U0, sub_zero]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp only [map_inv₀, coe_algebraMap]
  have h_convert : ∀ t : ℝ, t ≠ 0 →
      (t⁻¹ : ℂ) • (U_grp.U t φ - φ) = I • ((I * (t : ℂ))⁻¹ • (U_grp.U t φ - φ)) := by
    intro t ht
    rw [← smul_assoc]
    congr 1
    rw [smul_eq_mul, mul_inv_rev, inv_I, mul_neg, mul_comm ((↑t)⁻¹) I,
        ← neg_mul, ← mul_assoc]
    simp
  have h_scale : Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (U_grp.U t φ - φ))
                         (𝓝[≠] 0) (𝓝 (I • gen.op ⟨φ, hφ⟩)) := by
    have h_smul_tendsto := Tendsto.const_smul h_gen I
    apply Tendsto.congr' _ h_smul_tendsto
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (h_convert t ht).symm
  apply h_scale.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (h_slope_eq t ht).symm

lemma unitary_hasDerivAt
    (gen : Generator U_grp) (_ : gen.IsSelfAdjoint)
    (s : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    HasDerivAt (fun t => U_grp.U t φ)
               (I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩) s := by
  have h_eq : ∀ t, U_grp.U t φ = U_grp.U s (U_grp.U (t - s) φ) := by
    intro t
    have := U_grp.group_law s (t - s)
    simp only [add_sub_cancel] at this
    calc U_grp.U t φ
        = (U_grp.U s).comp (U_grp.U (t - s)) φ := by rw [← this]
      _ = U_grp.U s (U_grp.U (t - s) φ) := rfl
  have h_shift : HasDerivAt (fun t => U_grp.U (t - s) φ) (I • gen.op ⟨φ, hφ⟩) s := by
    have h0 : HasDerivAt (fun t => U_grp.U t φ) (I • gen.op ⟨φ, hφ⟩) (s - s) := by
      simp only [sub_self]
      exact unitary_hasDerivAt_zero gen φ hφ
    exact h0.comp_sub_const s s
  haveI : IsScalarTower ℝ ℂ H := RestrictScalars.isScalarTower ℝ ℂ H
  have h_comp : HasDerivAt (fun t => U_grp.U s (U_grp.U (t - s) φ))
                         (U_grp.U s (I • gen.op ⟨φ, hφ⟩)) s := by
    let L := (U_grp.U s).restrictScalars ℝ
    have h_eq : ∀ v, L v = U_grp.U s v := fun v => rfl
    have h_L := L.hasFDerivAt.comp_hasDerivAt s h_shift
    convert h_L using 1
  have h_comm := generator_commutes_unitary gen s φ hφ
  have h_val : U_grp.U s (I • gen.op ⟨φ, hφ⟩) = I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ := by
    rw [ContinuousLinearMap.map_smul, h_comm]
  rw [h_val] at h_comp
  exact h_comp.congr_of_eventuallyEq (Eventually.of_forall (fun t => (h_eq t)))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U_grp : OneParameterUnitaryGroup (H := H)}

/-! ### Duhamel identity -/

theorem duhamel_identity
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    U_grp.U t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ =
    ∫ s in (0)..t, duhamelIntegrand gen hsa n t φ hφ s := by
  set B := I • yosidaApproxSym gen hsa n
  let f : ℝ → H := fun s => expBounded B (t - s) (U_grp.U s φ)
  have hf_t : f t = U_grp.U t φ := by
    simp_all only [sub_self, f, B]
    simp only [expBounded_at_zero', ContinuousLinearMap.one_apply]
  have hf_0 : f 0 = expBounded B t φ := by
    simp_all only [sub_self, sub_zero, f, B]
    have h := U_grp.identity
    simp only [h, ContinuousLinearMap.id_apply]
  have h_exp_deriv : ∀ s, HasDerivAt (fun s => expBounded B (t - s))
                                    (-(B.comp (expBounded B (t - s)))) s := by
    intro s
    have h := expBounded_hasDerivAt B (t - s)
    have h1 : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
      convert (hasDerivAt_const s t).sub (hasDerivAt_id' s) using 1; ring
    have h_comp := h.scomp s h1
    convert h_comp using 1
    simp only [neg_one_smul]
  have h_U_deriv : ∀ s, HasDerivAt (fun s => U_grp.U s φ)
                         (I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩) s :=
    fun s => unitary_hasDerivAt gen hsa s φ hφ
  haveI : IsScalarTower ℝ ℂ H := RestrictScalars.isScalarTower ℝ ℂ H
  have h_deriv : ∀ s, HasDerivAt f (duhamelIntegrand gen hsa n t φ hφ s) s := by
    intro s
    have h_bil : IsBoundedBilinearMap ℝ (fun p : (H →L[ℂ] H) × H => p.1 p.2) := {
      add_left := fun T₁ T₂ v => by simp only [ContinuousLinearMap.add_apply]
      smul_left := fun c T v => by simp only; rfl
      add_right := fun T v₁ v₂ => T.map_add v₁ v₂
      smul_right := fun c T v => by
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), T.map_smul]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      bound := by
        use 1
        constructor
        · norm_num
        · intro T v
          simp only [one_mul]
          exact T.le_opNorm v
    }
    have h_pair : HasDerivAt (fun s => (expBounded B (t - s), U_grp.U s φ))
                            (-(B.comp (expBounded B (t - s))),
                              I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩) s :=
      (h_exp_deriv s).prodMk (h_U_deriv s)
    have h_fderiv := h_bil.hasFDerivAt (expBounded B (t - s), U_grp.U s φ)
    have h_comp := h_fderiv.comp_hasDerivAt s h_pair
    have h_deriv_val : h_bil.deriv (expBounded B (t - s), U_grp.U s φ)
                    (-(B.comp (expBounded B (t - s))),
                     I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩) =
                   duhamelIntegrand gen hsa n t φ hφ s := by
      simp only [IsBoundedBilinearMap.deriv_apply]
      unfold duhamelIntegrand
      set ψ := U_grp.U s φ
      set expB := expBounded B (t - s)
      set Aψ := gen.op ⟨ψ, gen.domain_invariant s φ hφ⟩
      set Aₙψ := yosidaApproxSym gen hsa n ψ
      have h_comm : B.comp expB = expB.comp B := by
        ext v
        simp only [ContinuousLinearMap.comp_apply]
        have := B_commute_expBounded B (t - s)
        unfold Commute SemiconjBy at this
        exact congrFun (congrArg DFunLike.coe this) v
      calc expB (I • Aψ) + (-(B.comp expB)) ψ
          = expB (I • Aψ) - (B.comp expB) ψ := by
              simp only [ContinuousLinearMap.neg_apply]
              exact Eq.symm (sub_eq_add_neg (expB (I • Aψ)) ((B.comp expB) ψ))
        _ = expB (I • Aψ) - (expB.comp B) ψ := by rw [h_comm]
        _ = expB (I • Aψ) - expB (B ψ) := by rfl
        _ = expB (I • Aψ - B ψ) := by rw [ContinuousLinearMap.map_sub]
        _ = expB (I • Aψ - I • Aₙψ) := by congr 1
    convert h_comp using 1
    exact id (Eq.symm h_deriv_val)
  have h_cont : Continuous f := by
    unfold f
    have h1 : Continuous (fun s => expBounded B (t - s)) := by
      have h_smul : Continuous (fun s : ℝ => ((t - s) : ℂ) • B) := by
        apply Continuous.smul
        · have : (fun s : ℝ => ((t - s) : ℂ)) = (fun s : ℝ => (t : ℂ) - (s : ℂ)) := by
            ext s; rfl
          rw [this]
          exact continuous_const.sub continuous_ofReal
        · exact continuous_const
      haveI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
      have h_exp : Continuous (NormedSpace.exp : (H →L[ℂ] H) → (H →L[ℂ] H)) :=
        NormedSpace.exp_continuous
      have h_comp := h_exp.comp h_smul
      convert h_comp using 1
      ext s v
      simp only [Function.comp_apply, expBounded]
      congr 1
      ext k
      congr 1
      field_simp
      rw [ofReal_sub]
      rw [NormedSpace.exp_eq_tsum ℂ]
      congr 1; ext k; simp only [one_div]
    have h2 : Continuous (fun s => U_grp.U s φ) := U_grp.strong_continuous φ
    exact h1.clm_apply h2
  have h_int : IntervalIntegrable (duhamelIntegrand gen hsa n t φ hφ) MeasureTheory.volume 0 t :=
    (duhamelIntegrand_continuous gen hsa n t φ hφ).intervalIntegrable 0 t
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
                  (fun s _ => h_deriv s) h_int
  rw [hf_t, hf_0] at h_ftc
  exact h_ftc.symm

end QuantumMechanics.Yosida
