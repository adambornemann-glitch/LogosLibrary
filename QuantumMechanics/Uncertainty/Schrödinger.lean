/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.Uncertainty.Robertson
/-!
# The Schrödinger Uncertainty Relation

This module proves the Schrödinger uncertainty inequality, which strengthens
Robertson's bound by including a covariance term.

## Main definitions

* `covariance`: Cov(A,B)_ψ = ½⟨{A,B}⟩_ψ - ⟨A⟩_ψ⟨B⟩_ψ

## Main results

* `re_inner_shifted_eq_covariance`: Re⟨Ãψ, B̃ψ⟩ = Cov(A,B)_ψ
* `schrodinger_uncertainty`: The variance form of the inequality:
  $$\sigma_A^2 \sigma_B^2 \geq \tfrac{1}{4}|\langle[A,B]\rangle|^2 + \text{Cov}(A,B)^2$$
* `schrodinger_stddev`: The standard deviation form:
  $$\sigma_A \sigma_B \geq \sqrt{\tfrac{1}{4}|\langle[A,B]\rangle|^2 + \text{Cov}(A,B)^2}$$
* `robertson_from_schrodinger`: Robertson's inequality as a corollary

## Proof outline

The key observation is that Cauchy-Schwarz gives us |⟨Ãψ, B̃ψ⟩|² ≤ σ_A² σ_B²,
and the full complex inner product decomposes as:

$$|\langle\tilde{A}\psi, \tilde{B}\psi\rangle|^2 =
  (\text{Re}\langle\tilde{A}\psi, \tilde{B}\psi\rangle)^2 +
  (\text{Im}\langle\tilde{A}\psi, \tilde{B}\psi\rangle)^2$$

where:
- The real part equals the covariance
- The imaginary part equals ½ Im⟨ψ, [A,B]ψ⟩

Robertson's inequality discards the covariance term; Schrödinger's keeps it.

## Physical interpretation

The covariance term measures statistical correlation between observables.
For uncorrelated observables (Cov = 0), this reduces to Robertson.
For correlated observables, the uncertainty bound is strictly tighter.

The Schrödinger form is saturated by squeezed states, which have nonzero
covariance between position and momentum.

## Historical note

Schrödinger published this refinement in 1930, one year after Robertson's
inequality and three years after Heisenberg's original argument. It remained
relatively obscure until squeezed states became experimentally relevant
in quantum optics.

## References

* [Schrödinger, "Zum Heisenbergschen Unschärfeprinzip"][schrodinger1930]
* [Robertson, "The uncertainty principle"][robertson1929]

## Tags

uncertainty principle, Schrödinger inequality, covariance, squeezed states
-/
namespace QuantumMechanics.Schrodinger

open InnerProductSpace UnboundedObservable Robertson
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- The covariance `Cov(A,B)_ψ = ½⟨{A,B}⟩ - ⟨A⟩⟨B⟩`. -/
noncomputable def covariance (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) : ℝ :=
  (1/2) * (⟪ψ, anticommutatorAt A B ψ h.toDomainConditions⟫_ℂ).re -
  A.expectation ψ h.h_norm h.hψ_A * B.expectation ψ h.h_norm h.hψ_B

/-- The real part of `⟨Ãψ, B̃ψ⟩` equals the covariance. -/
theorem re_inner_shifted_eq_covariance (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    (⟪h.A'ψ, h.B'ψ⟫_ℂ).re = covariance A B ψ h := by

  set μ_A := A.expectation ψ h.h_norm h.hψ_A
  set μ_B := B.expectation ψ h.h_norm h.hψ_B

  have h_norm_sq : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, h.h_norm]; simp

  have h_re_formula : (⟪h.A'ψ, h.B'ψ⟫_ℂ).re = (⟪h.A'ψ, h.B'ψ⟫_ℂ + ⟪h.B'ψ, h.A'ψ⟫_ℂ).re / 2 := by
    rw [← inner_conj_symm h.B'ψ h.A'ψ]
    simp only [Complex.add_re, Complex.conj_re]
    ring

  have h_sym1 : ⟪h.A'ψ, h.B'ψ⟫_ℂ = ⟪ψ, A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain⟫_ℂ :=
    A.shifted_symmetric ψ h.h_norm h.hψ_A h.hψ_A h.B'ψ_in_A_domain

  have h_sym2 : ⟪h.B'ψ, h.A'ψ⟫_ℂ = ⟪ψ, B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain⟫_ℂ :=
    B.shifted_symmetric ψ h.h_norm h.hψ_B h.hψ_B h.A'ψ_in_B_domain

  rw [h_re_formula, h_sym1, h_sym2]

  have h_expand_sum : A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain +
                      B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain =
                      anticommutatorAt A B ψ h.toDomainConditions -
                      (2 * μ_B : ℂ) • h.Aψ - (2 * μ_A : ℂ) • h.Bψ +
                      (2 * μ_A * μ_B : ℂ) • ψ := by
    unfold shiftedApply ShiftedDomainConditions.A'ψ ShiftedDomainConditions.B'ψ
    unfold anticommutatorAt DomainConditions.ABψ DomainConditions.BAψ
    unfold DomainConditions.Aψ DomainConditions.Bψ
    simp only [shiftedApply]
    rw [A.apply_sub h.hBψ_A (A.domain.smul_mem _ h.hψ_A)]
    rw [A.apply_smul _ h.hψ_A]
    rw [B.apply_sub h.hAψ_B (B.domain.smul_mem _ h.hψ_B)]
    rw [B.apply_smul _ h.hψ_B]
    module

  have h_inner_Aψ : ⟪ψ, h.Aψ⟫_ℂ = μ_A := by
    unfold DomainConditions.Aψ
    rw [A.inner_self_eq_re h.hψ_A]
    exact rfl

  have h_inner_Bψ : ⟪ψ, h.Bψ⟫_ℂ = μ_B := by
    unfold DomainConditions.Bψ
    rw [B.inner_self_eq_re h.hψ_B]
    exact rfl

  have h_inner_sum : ⟪ψ, A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain +
                        B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain⟫_ℂ =
                     ⟪ψ, anticommutatorAt A B ψ h.toDomainConditions⟫_ℂ -
                     (2 * μ_A * μ_B : ℂ) := by
    rw [h_expand_sum]
    simp only [inner_sub_right, inner_add_right, inner_smul_right]
    rw [h_inner_Aψ, h_inner_Bψ, h_norm_sq]
    ring

  have h_add_re : (⟪ψ, A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain⟫_ℂ +
                  ⟪ψ, B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain⟫_ℂ).re =
                  (⟪ψ, anticommutatorAt A B ψ h.toDomainConditions⟫_ℂ - (2 * μ_A * μ_B : ℂ)).re := by
    congr 1
    rw [← inner_add_right, h_inner_sum]

  rw [h_add_re]
  unfold covariance

  have h_anti_real : (⟪ψ, anticommutatorAt A B ψ h.toDomainConditions⟫_ℂ).im = 0 :=
    anticommutator_im_eq_zero A B ψ h.toDomainConditions

  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_mul, add_zero, one_div]
  ring

/-- **Schrödinger uncertainty inequality**: `Var(A) Var(B) ≥ ¼|⟨[A,B]⟩|² + Cov(A,B)²`.

This is stronger than Robertson's inequality, which drops the covariance term. -/
theorem schrodinger_uncertainty (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B ≥
    (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 +
    (covariance A B ψ h)^2 := by

  have h_cs_sq : ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖^2 ≤ ‖h.A'ψ‖^2 * ‖h.B'ψ‖^2 := by
    have h_cs : ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖ ≤ ‖h.A'ψ‖ * ‖h.B'ψ‖ := norm_inner_le_norm h.A'ψ h.B'ψ
    have := sq_le_sq' (norm_nonneg _) h_cs
    rwa [mul_pow] at this

  have h_var_eq : ‖h.A'ψ‖^2 * ‖h.B'ψ‖^2 =
                  A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B := by
    unfold variance ShiftedDomainConditions.A'ψ ShiftedDomainConditions.B'ψ; rfl

  have h_re_eq : (⟪h.A'ψ, h.B'ψ⟫_ℂ).re = covariance A B ψ h :=
    re_inner_shifted_eq_covariance A B ψ h

  have h_im_eq : (⟪h.A'ψ, h.B'ψ⟫_ℂ).im =
                 (1/2) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im :=
    im_inner_shifted_eq_half_commutator A B ψ h

  have h_comm_re_zero : (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).re = 0 :=
    commutator_re_eq_zero A B ψ h.toDomainConditions

  have h_norm_sq_decomp : ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖^2 =
                          (covariance A B ψ h)^2 +
                          (1/4) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im^2 := by
    rw [Complex.sq_norm, normSq_eq_re_sq_add_im_sq, h_re_eq, h_im_eq]
    ring

  have h_comm_norm_eq : (1/4) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im^2 =
                        (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 := by
    congr 1
    rw [Complex.sq_norm, normSq_of_re_zero h_comm_re_zero]

  calc A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B
    _ = ‖h.A'ψ‖^2 * ‖h.B'ψ‖^2 := h_var_eq.symm
    _ ≥ ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖^2 := h_cs_sq
    _ = (covariance A B ψ h)^2 + (1/4) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im^2 :=
        h_norm_sq_decomp
    _ = (covariance A B ψ h)^2 + (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 := by
        rw [h_comm_norm_eq]
    _ = (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 + (covariance A B ψ h)^2 := by
        ring

/-- Robertson's inequality as a corollary of Schrödinger's (variance form). -/
theorem robertson_from_schrodinger (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B ≥
    (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 := by
  have h_schrodinger := schrodinger_uncertainty A B ψ h
  have h_cov_sq_nonneg : 0 ≤ (covariance A B ψ h)^2 := sq_nonneg _
  linarith

/-- Robertson's inequality as a corollary of Schrödinger's (standard deviation form). -/
theorem robertson_stddev_from_schrodinger (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B ≥
    (1/2) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖ := by

  have h_var := robertson_from_schrodinger A B ψ h
  have h_sqrt := Real.sqrt_le_sqrt h_var

  have h_lhs : Real.sqrt (A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B) =
               A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B := by
    unfold stdDev
    rw [← Real.sqrt_mul (variance_nonneg A ψ h.h_norm h.hψ_A)]

  have h_rhs : Real.sqrt ((1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2) =
               (1/2) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖ := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1/4)]
    rw [Real.sqrt_sq (norm_nonneg _)]
    have : Real.sqrt (1/4 : ℝ) = 1/2 := by
      rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]; norm_num
    rw [this]

  rw [h_lhs, h_rhs] at h_sqrt
  exact h_sqrt

/-- Schrödinger uncertainty in standard deviation form. -/
theorem schrodinger_stddev (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B ≥
    Real.sqrt ((1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 +
               (covariance A B ψ h)^2) := by
  have h_var := schrodinger_uncertainty A B ψ h
  have h_sqrt := Real.sqrt_le_sqrt h_var
  have h_lhs : Real.sqrt (A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B) =
               A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B := by
    unfold stdDev
    rw [← Real.sqrt_mul (variance_nonneg A ψ h.h_norm h.hψ_A)]
  rw [h_lhs] at h_sqrt
  exact h_sqrt
end QuantumMechanics.Schrodinger
