/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.Uncertainty.UnboundedOperators
/-!
# The Robertson Uncertainty Relation

This module proves the Robertson uncertainty inequality, the general form of
Heisenberg's uncertainty principle for arbitrary pairs of observables.

## Main results

* `im_inner_shifted_eq_half_commutator`: The imaginary part of ⟨Ãψ, B̃ψ⟩ equals
  half the imaginary part of ⟨ψ, [A,B]ψ⟩
* `robertson_uncertainty`: For any observables A, B and normalized state ψ,
  $$\sigma_A \sigma_B \geq \tfrac{1}{2}|\langle [A,B] \rangle_\psi|$$

## Proof outline

1. Shift to centered observables: Ã = A - ⟨A⟩, B̃ = B - ⟨B⟩
2. Apply Cauchy-Schwarz: |⟨Ãψ, B̃ψ⟩| ≤ ‖Ãψ‖ · ‖B̃ψ‖ = σ_A · σ_B
3. Extract the imaginary part: |⟨Ãψ, B̃ψ⟩| ≥ |Im⟨Ãψ, B̃ψ⟩|
4. Relate to commutator: Im⟨Ãψ, B̃ψ⟩ = ½ Im⟨ψ, [A,B]ψ⟩
5. Use `commutator_re_eq_zero`: ⟨ψ, [A,B]ψ⟩ is purely imaginary

The key insight is that shifting by expectation values doesn't affect the
commutator ([Ã, B̃] = [A, B]), so the uncertainty bound depends only on
the algebraic structure of the observables, not on the particular state.

## Implementation notes

`ShiftedDomainConditions` extends `DomainConditions` with the normalization
requirement ‖ψ‖ = 1. This bundles all hypotheses needed for the inequality.

## Physical interpretation

This inequality is the mathematical content of Heisenberg's uncertainty
principle. For position X and momentum P with [X, P] = iℏ, it yields:

$$\sigma_X \sigma_P \geq \frac{\hbar}{2}$$

The bound is achieved by Gaussian wave packets (coherent states).

## References

* [Robertson, "The uncertainty principle"][robertson1929]
* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], Section 3.5

## Tags

uncertainty principle, Robertson inequality, Heisenberg, commutator
-/
namespace QuantumMechanics.Robertson

open InnerProductSpace UnboundedObservable
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


structure ShiftedDomainConditions (A B : UnboundedObservable H) (ψ : H) extends
    DomainConditions A B ψ where
  h_norm : ‖ψ‖ = 1

namespace ShiftedDomainConditions

variable {A B : UnboundedObservable H} {ψ : H}

noncomputable def A'ψ (h : ShiftedDomainConditions A B ψ) : H :=
  A.shiftedApply ψ ψ h.h_norm h.hψ_A h.hψ_A

noncomputable def B'ψ (h : ShiftedDomainConditions A B ψ) : H :=
  B.shiftedApply ψ ψ h.h_norm h.hψ_B h.hψ_B

theorem B'ψ_in_A_domain (h : ShiftedDomainConditions A B ψ) : h.B'ψ ∈ A.domain := by
  unfold B'ψ shiftedApply
  exact A.domain.sub_mem h.hBψ_A (A.domain.smul_mem _ h.hψ_A)

theorem A'ψ_in_B_domain (h : ShiftedDomainConditions A B ψ) : h.A'ψ ∈ B.domain := by
  unfold A'ψ shiftedApply
  exact B.domain.sub_mem h.hAψ_B (B.domain.smul_mem _ h.hψ_B)

end ShiftedDomainConditions


lemma sq_le_sq' {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x^2 ≤ y^2 := by
  calc x^2 = x * x := sq x
    _ ≤ x * y := by exact mul_le_mul_of_nonneg_left hxy hx
    _ ≤ y * y := by exact mul_le_mul_of_nonneg_right hxy (le_trans hx hxy)
    _ = y^2 := (sq y).symm


lemma normSq_of_re_zero {z : ℂ} (h : z.re = 0) : Complex.normSq z = z.im^2 := by
  rw [Complex.normSq_apply, h]
  ring

lemma normSq_of_im_zero {z : ℂ} (h : z.im = 0) : Complex.normSq z = z.re^2 := by
  rw [Complex.normSq_apply, h]
  ring

lemma normSq_eq_re_sq_add_im_sq (z : ℂ) : Complex.normSq z = z.re^2 + z.im^2 := by
  rw [Complex.normSq_apply]
  ring


theorem im_inner_shifted_eq_half_commutator (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    (⟪h.A'ψ, h.B'ψ⟫_ℂ).im =
    (1/2) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im := by

  have h_sym1 : ⟪h.A'ψ, h.B'ψ⟫_ℂ = ⟪ψ, A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain⟫_ℂ :=
    A.shifted_symmetric ψ h.h_norm h.hψ_A h.hψ_A h.B'ψ_in_A_domain

  have h_sym2 : ⟪h.B'ψ, h.A'ψ⟫_ℂ = ⟪ψ, B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain⟫_ℂ :=
    B.shifted_symmetric ψ h.h_norm h.hψ_B h.hψ_B h.A'ψ_in_B_domain

  have h_im_formula : (⟪h.A'ψ, h.B'ψ⟫_ℂ).im = (⟪h.A'ψ, h.B'ψ⟫_ℂ - ⟪h.B'ψ, h.A'ψ⟫_ℂ).im / 2 := by
    rw [← inner_conj_symm h.B'ψ h.A'ψ]
    simp only [Complex.sub_im, Complex.conj_im]
    ring

  rw [h_im_formula, h_sym1, h_sym2]
  have h_expand : A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain -
                  B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain =
                  commutatorAt A B ψ h.toDomainConditions := by
    unfold shiftedApply ShiftedDomainConditions.A'ψ ShiftedDomainConditions.B'ψ
    unfold commutatorAt DomainConditions.ABψ DomainConditions.BAψ
    simp only [shiftedApply]
    rw [A.apply_sub h.hBψ_A (A.domain.smul_mem _ h.hψ_A)]
    rw [A.apply_smul _ h.hψ_A]
    rw [B.apply_sub h.hAψ_B (B.domain.smul_mem _ h.hψ_B)]
    rw [B.apply_smul _ h.hψ_B]
    module

  unfold commutatorAt DomainConditions.ABψ DomainConditions.BAψ
  simp only [inner_sub_right]
  ring_nf

  have h_key : ⟪ψ, A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain⟫_ℂ -
               ⟪ψ, B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain⟫_ℂ =
               ⟪ψ, h.ABψ⟫_ℂ - ⟪ψ, h.BAψ⟫_ℂ := by
    rw [← inner_sub_right, ← inner_sub_right, h_expand]
    exact rfl
  rw [h_key]
  exact rfl



theorem norm_eq_abs_im_of_re_zero {z : ℂ} (h : z.re = 0) : ‖z‖ = |z.im| := by
  have hz : z = z.im * Complex.I := Complex.ext (by simp [h]) (by simp)
  rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact congrArg abs (congrArg Complex.im hz)


theorem robertson_uncertainty (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B ≥
    (1/2) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖ := by

  have h_cs : ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖ ≤ ‖h.A'ψ‖ * ‖h.B'ψ‖ :=
    norm_inner_le_norm h.A'ψ h.B'ψ

  have h_cs_sq : ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖^2 ≤ ‖h.A'ψ‖^2 * ‖h.B'ψ‖^2 := by
    have := sq_le_sq' (norm_nonneg _) h_cs
    rwa [mul_pow] at this

  have h_var_eq : ‖h.A'ψ‖^2 * ‖h.B'ψ‖^2 =
                  A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B := by
    unfold variance ShiftedDomainConditions.A'ψ ShiftedDomainConditions.B'ψ
    rfl

  have h_im_le : (⟪h.A'ψ, h.B'ψ⟫_ℂ).im^2 ≤ ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖^2 := by
    rw [Complex.sq_norm]
    have := normSq_eq_re_sq_add_im_sq ⟪h.A'ψ, h.B'ψ⟫_ℂ
    linarith [sq_nonneg (⟪h.A'ψ, h.B'ψ⟫_ℂ).re]

  have h_im_eq : (⟪h.A'ψ, h.B'ψ⟫_ℂ).im =
                 (1/2) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im :=
    im_inner_shifted_eq_half_commutator A B ψ h

  have h_comm_re_zero : (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).re = 0 :=
    commutator_re_eq_zero A B ψ h.toDomainConditions

  have h_comm_norm : ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖ =
                     |(⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im| :=
    norm_eq_abs_im_of_re_zero h_comm_re_zero

  have h_var_bound : A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B ≥
                     (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 := by
    calc A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B
      _ = ‖h.A'ψ‖^2 * ‖h.B'ψ‖^2 := h_var_eq.symm
      _ ≥ ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖^2 := h_cs_sq
      _ ≥ (⟪h.A'ψ, h.B'ψ⟫_ℂ).im^2 := h_im_le
      _ = ((1/2) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im)^2 := by rw [h_im_eq]
      _ = (1/4) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im^2 := by ring
      _ = (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 := by
          congr 1
          rw [Complex.sq_norm, normSq_of_re_zero h_comm_re_zero]

  have h_sqrt_bound : Real.sqrt (A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B) ≥
                      Real.sqrt ((1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2) :=
    Real.sqrt_le_sqrt h_var_bound

  have h_lhs : Real.sqrt (A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B) =
               A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B := by
    unfold stdDev
    rw [← Real.sqrt_mul (variance_nonneg A ψ h.h_norm h.hψ_A)]

  have h_rhs : Real.sqrt ((1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2) =
               (1/2) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖ := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1/4)]
    rw [Real.sqrt_sq (norm_nonneg _)]
    have : Real.sqrt (1/4 : ℝ) = 1/2 := by
      rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]
      congr 1
      norm_num
    rw [this]

  rw [h_lhs, h_rhs] at h_sqrt_bound
  exact h_sqrt_bound

end QuantumMechanics.Robertson
