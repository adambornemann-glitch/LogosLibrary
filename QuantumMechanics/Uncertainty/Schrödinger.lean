
/-
================================================================================
SCHRÖDINGER'S UNCERTAINTY RELATION
================================================================================

Author: Adam Bornemann

The REAL theorem. Robertson is just this with a term dropped.

Schrödinger (1930):
    Var(A) · Var(B) ≥ (1/4)|⟨[A,B]⟩|² + Cov(A,B)²

Robertson (1929):
    Var(A) · Var(B) ≥ (1/4)|⟨[A,B]⟩|²

The difference? Robertson throws away Cov(A,B)². That's it.
-/
import LogosLibrary.QuantumMechanics.Uncertainty.Robertson

namespace QuantumMechanics.Schrodinger

open InnerProductSpace UnboundedObservable Robertson
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-============================================================================
  SECTION 1: THE REAL PART — COVARIANCE
============================================================================-/

/--
Quantum covariance: Cov(A,B) = (1/2)⟨{A,B}⟩ - ⟨A⟩⟨B⟩

This measures the correlation between observables A and B.
Unlike classical covariance, we need to symmetrize because AB ≠ BA.
-/
noncomputable def covariance (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) : ℝ :=
  (1/2) * (⟪ψ, anticommutatorAt A B ψ h.toDomainConditions⟫_ℂ).re -
  A.expectation ψ h.h_norm h.hψ_A * B.expectation ψ h.h_norm h.hψ_B

/--
Key lemma: Re⟨A'ψ, B'ψ⟩ = Cov(A,B)

The real part of the shifted inner product IS the covariance.
This is the term Robertson discards.
-/
theorem re_inner_shifted_eq_covariance (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    (⟪h.A'ψ, h.B'ψ⟫_ℂ).re = covariance A B ψ h := by

  -- Notation
  set μ_A := A.expectation ψ h.h_norm h.hψ_A
  set μ_B := B.expectation ψ h.h_norm h.hψ_B

  -- Normalization
  have h_norm_sq : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, h.h_norm]; simp

  -- Step 1: Re(z) = (z + conj(z))/2, and conj⟨u,v⟩ = ⟨v,u⟩
  have h_re_formula : (⟪h.A'ψ, h.B'ψ⟫_ℂ).re = (⟪h.A'ψ, h.B'ψ⟫_ℂ + ⟪h.B'ψ, h.A'ψ⟫_ℂ).re / 2 := by
    rw [← inner_conj_symm h.B'ψ h.A'ψ]
    simp only [Complex.add_re, Complex.conj_re]
    ring

  -- Step 2: Use symmetry
  have h_sym1 : ⟪h.A'ψ, h.B'ψ⟫_ℂ = ⟪ψ, A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain⟫_ℂ :=
    A.shifted_symmetric ψ h.h_norm h.hψ_A h.hψ_A h.B'ψ_in_A_domain

  have h_sym2 : ⟪h.B'ψ, h.A'ψ⟫_ℂ = ⟪ψ, B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain⟫_ℂ :=
    B.shifted_symmetric ψ h.h_norm h.hψ_B h.hψ_B h.A'ψ_in_B_domain

  rw [h_re_formula, h_sym1, h_sym2]

  -- Step 3: Expand A'(B'ψ) + B'(A'ψ) = {A,B}ψ - 2μ_B·Aψ - 2μ_A·Bψ + 2μ_A·μ_B·ψ
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

  -- Step 4: Take inner product and use ⟨ψ,Aψ⟩ = μ_A, ⟨ψ,Bψ⟩ = μ_B, ⟨ψ,ψ⟩ = 1
  have h_inner_Aψ : ⟪ψ, h.Aψ⟫_ℂ = μ_A := by
    unfold DomainConditions.Aψ
    rw [A.inner_self_eq_re h.hψ_A]
    exact rfl

  have h_inner_Bψ : ⟪ψ, h.Bψ⟫_ℂ = μ_B := by
    unfold DomainConditions.Bψ
    rw [B.inner_self_eq_re h.hψ_B]
    exact rfl

  -- Step 5: Compute the inner product of the sum
  have h_inner_sum : ⟪ψ, A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain +
                        B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain⟫_ℂ =
                     ⟪ψ, anticommutatorAt A B ψ h.toDomainConditions⟫_ℂ -
                     (2 * μ_A * μ_B : ℂ) := by
    rw [h_expand_sum]
    simp only [inner_sub_right, inner_add_right, inner_smul_right]
    rw [h_inner_Aψ, h_inner_Bψ, h_norm_sq]
    ring

  -- Step 6: Extract real part
  -- First, establish that the sum of inner products equals inner product of sum
  have h_add_re : (⟪ψ, A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain⟫_ℂ +
                  ⟪ψ, B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain⟫_ℂ).re =
                  (⟪ψ, anticommutatorAt A B ψ h.toDomainConditions⟫_ℂ - (2 * μ_A * μ_B : ℂ)).re := by
    congr 1
    rw [← inner_add_right, h_inner_sum]

  rw [h_add_re]
  unfold covariance
  -- The anticommutator expectation is real (we'll use this implicitly)
  have h_anti_real : (⟪ψ, anticommutatorAt A B ψ h.toDomainConditions⟫_ℂ).im = 0 :=
    anticommutator_im_eq_zero A B ψ h.toDomainConditions

  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_mul, add_zero, one_div]
  ring

/-============================================================================
  SECTION 2: SCHRÖDINGER'S UNCERTAINTY RELATION
============================================================================-/

/--
**Schrödinger's Uncertainty Relation** (1930)

The FULL geometric content of Cauchy-Schwarz applied to quantum observables:

    Var(A) · Var(B) ≥ (1/4)|⟨[A,B]⟩|² + Cov(A,B)²

This is strictly stronger than Robertson's inequality. The covariance term
Cov(A,B)² is always non-negative, so Schrödinger ≥ Robertson always.

Equality (saturation) occurs when:
- Robertson: Gaussian wave packets for position-momentum
- Schrödinger: Only when Cov(A,B) = 0 as well (uncorrelated observables)
-/
theorem schrodinger_uncertainty (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B ≥
    (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 +
    (covariance A B ψ h)^2 := by

  /-
  STEP 1: CAUCHY-SCHWARZ

  Var(A)·Var(B) = ‖A'ψ‖²·‖B'ψ‖² ≥ |⟨A'ψ, B'ψ⟩|²
  -/

  have h_cs_sq : ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖^2 ≤ ‖h.A'ψ‖^2 * ‖h.B'ψ‖^2 := by
    have h_cs : ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖ ≤ ‖h.A'ψ‖ * ‖h.B'ψ‖ := norm_inner_le_norm h.A'ψ h.B'ψ
    have := sq_le_sq' (norm_nonneg _) h_cs
    rwa [mul_pow] at this

  have h_var_eq : ‖h.A'ψ‖^2 * ‖h.B'ψ‖^2 =
                  A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B := by
    unfold variance ShiftedDomainConditions.A'ψ ShiftedDomainConditions.B'ψ; rfl

  /-
  STEP 2: PYTHAGOREAN DECOMPOSITION

  |⟨A'ψ, B'ψ⟩|² = Re(⟨A'ψ, B'ψ⟩)² + Im(⟨A'ψ, B'ψ⟩)²
               = Cov(A,B)² + (1/4)|⟨[A,B]⟩|²

  This is where we KEEP both terms, unlike Robertson.
  -/

  have h_re_eq : (⟪h.A'ψ, h.B'ψ⟫_ℂ).re = covariance A B ψ h :=
    re_inner_shifted_eq_covariance A B ψ h

  have h_im_eq : (⟪h.A'ψ, h.B'ψ⟫_ℂ).im =
                 (1/2) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im :=
    im_inner_shifted_eq_half_commutator A B ψ h

  have h_comm_re_zero : (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).re = 0 :=
    commutator_re_eq_zero A B ψ h.toDomainConditions

  -- |⟨A'ψ, B'ψ⟩|² = Re² + Im²
  have h_norm_sq_decomp : ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖^2 =
                          (covariance A B ψ h)^2 +
                          (1/4) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im^2 := by
    rw [Complex.sq_norm, normSq_eq_re_sq_add_im_sq, h_re_eq, h_im_eq]
    ring

  -- (1/4)·Im²  = (1/4)·‖z‖² when Re(z) = 0
  have h_comm_norm_eq : (1/4) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im^2 =
                        (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 := by
    congr 1
    rw [Complex.sq_norm, normSq_of_re_zero h_comm_re_zero]

  /-
  STEP 3: ASSEMBLE
  -/

  calc A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B
    _ = ‖h.A'ψ‖^2 * ‖h.B'ψ‖^2 := h_var_eq.symm
    _ ≥ ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖^2 := h_cs_sq
    _ = (covariance A B ψ h)^2 + (1/4) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im^2 :=
        h_norm_sq_decomp
    _ = (covariance A B ψ h)^2 + (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 := by
        rw [h_comm_norm_eq]
    _ = (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 + (covariance A B ψ h)^2 := by
        ring

/-============================================================================
  SECTION 3: ROBERTSON AS A COROLLARY
============================================================================-/

/--
Robertson's inequality is Schrödinger with the covariance term dropped.

Since Cov(A,B)² ≥ 0, we have:
    Schrödinger: Var(A)·Var(B) ≥ (1/4)|⟨[A,B]⟩|² + Cov²
    Robertson:   Var(A)·Var(B) ≥ (1/4)|⟨[A,B]⟩|²

Robertson ≤ Schrödinger always. Strict inequality when Cov(A,B) ≠ 0.
-/
theorem robertson_from_schrodinger (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B ≥
    (1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2 := by
  have h_schrodinger := schrodinger_uncertainty A B ψ h
  have h_cov_sq_nonneg : 0 ≤ (covariance A B ψ h)^2 := sq_nonneg _
  linarith

/--
The standard deviation form of Robertson, derived from Schrödinger.
-/
theorem robertson_stddev_from_schrodinger (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B ≥
    (1/2) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖ := by
  -- This follows from robertson_from_schrodinger by taking square roots
  have h_var := robertson_from_schrodinger A B ψ h
  have h_sqrt := Real.sqrt_le_sqrt h_var

  -- Simplify LHS
  have h_lhs : Real.sqrt (A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B) =
               A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B := by
    unfold stdDev
    rw [← Real.sqrt_mul (variance_nonneg A ψ h.h_norm h.hψ_A)]

  -- Simplify RHS
  have h_rhs : Real.sqrt ((1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2) =
               (1/2) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖ := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1/4)]
    rw [Real.sqrt_sq (norm_nonneg _)]
    have : Real.sqrt (1/4 : ℝ) = 1/2 := by
      rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]; norm_num
    rw [this]

  rw [h_lhs, h_rhs] at h_sqrt
  exact h_sqrt

/-============================================================================
  SECTION 4: THE FULL STANDARD DEVIATION FORM OF SCHRÖDINGER
============================================================================-/

/--
Schrödinger's inequality in standard deviation form:

    σ_A · σ_B ≥ √((1/4)|⟨[A,B]⟩|² + Cov(A,B)²)

Or equivalently:
    σ_A² · σ_B² ≥ (1/4)|⟨[A,B]⟩|² + Cov(A,B)²
-/
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
