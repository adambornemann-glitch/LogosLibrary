
/-
================================================================================
ROBERTSON'S UNCERTAINTY PRINCIPLE
================================================================================

Author: Adam Bornemann
Refactored: With proper unbounded operator types

This file proves Robertson's generalized uncertainty relation:

    σ_A · σ_B ≥ (1/2)|⟨[A,B]⟩|

using the correct type-theoretic foundation for unbounded operators.
-/
import LogosLibrary.QuantumMechanics.Uncertainty.UnboundedOperators

namespace QuantumMechanics.Robertson

open InnerProductSpace UnboundedObservable
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-============================================================================
  SECTION 1: DOMAIN CONDITIONS FOR SHIFTED OPERATORS
============================================================================-/

/--
Extended domain conditions that include what we need for shifted operators.
Since shifting by a scalar preserves the domain, this is straightforward.
-/
structure ShiftedDomainConditions (A B : UnboundedObservable H) (ψ : H) extends
    DomainConditions A B ψ where
  /-- The state is normalized -/
  h_norm : ‖ψ‖ = 1

namespace ShiftedDomainConditions

variable {A B : UnboundedObservable H} {ψ : H}

/-- The shifted A applied to ψ -/
noncomputable def A'ψ (h : ShiftedDomainConditions A B ψ) : H :=
  A.shiftedApply ψ ψ h.h_norm h.hψ_A h.hψ_A

/-- The shifted B applied to ψ -/
noncomputable def B'ψ (h : ShiftedDomainConditions A B ψ) : H :=
  B.shiftedApply ψ ψ h.h_norm h.hψ_B h.hψ_B

/-- Key fact: B'ψ is still in A's domain (since B'ψ = Bψ - μψ and both are in Dom(A)) -/
theorem B'ψ_in_A_domain (h : ShiftedDomainConditions A B ψ) : h.B'ψ ∈ A.domain := by
  unfold B'ψ shiftedApply
  exact A.domain.sub_mem h.hBψ_A (A.domain.smul_mem _ h.hψ_A)

/-- Key fact: A'ψ is still in B's domain -/
theorem A'ψ_in_B_domain (h : ShiftedDomainConditions A B ψ) : h.A'ψ ∈ B.domain := by
  unfold A'ψ shiftedApply
  exact B.domain.sub_mem h.hAψ_B (B.domain.smul_mem _ h.hψ_B)

end ShiftedDomainConditions

/-============================================================================
  SECTION 2: ALGEBRAIC LEMMAS (Clean, Standalone, Maintainable)
============================================================================-/

/--
Squaring preserves order for non-negative reals.
-/
lemma sq_le_sq' {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x^2 ≤ y^2 := by
  calc x^2 = x * x := sq x
    _ ≤ x * y := by exact mul_le_mul_of_nonneg_left hxy hx
    _ ≤ y * y := by exact mul_le_mul_of_nonneg_right hxy (le_trans hx hxy)
    _ = y^2 := (sq y).symm

/--
For a purely imaginary complex number, |z|² = Im(z)².
-/
lemma normSq_of_re_zero {z : ℂ} (h : z.re = 0) : Complex.normSq z = z.im^2 := by
  rw [Complex.normSq_apply, h]
  ring

/--
For a purely real complex number, |z|² = Re(z)².
-/
lemma normSq_of_im_zero {z : ℂ} (h : z.im = 0) : Complex.normSq z = z.re^2 := by
  rw [Complex.normSq_apply, h]
  ring

/--
The Pythagorean decomposition: |z|² = Re(z)² + Im(z)².
-/
lemma normSq_eq_re_sq_add_im_sq (z : ℂ) : Complex.normSq z = z.re^2 + z.im^2 := by
  rw [Complex.normSq_apply]
  ring




/-============================================================================
  SECTION 3: THE COMMUTATOR INVARIANCE LEMMA
============================================================================-/

/--
The key lemma: Im⟨A'ψ, B'ψ⟩ = (1/2) Im⟨ψ, [A,B]ψ⟩

Proof sketch:
  ⟨A'ψ, B'ψ⟩ - ⟨B'ψ, A'ψ⟩ = 2i·Im⟨A'ψ, B'ψ⟩    (property of complex numbers)
  ⟨A'ψ, B'ψ⟩ = ⟨ψ, A'(B'ψ)⟩                      (by symmetry of A')
  ⟨B'ψ, A'ψ⟩ = ⟨ψ, B'(A'ψ)⟩                      (by symmetry of B')
  A'(B'ψ) - B'(A'ψ) = [A,B]ψ                      (shifting cancels in commutator)
-/
theorem im_inner_shifted_eq_half_commutator (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    (⟪h.A'ψ, h.B'ψ⟫_ℂ).im =
    (1/2) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im := by

  -- Step 1: Use symmetry to rewrite ⟨A'ψ, B'ψ⟩ and ⟨B'ψ, A'ψ⟩
  have h_sym1 : ⟪h.A'ψ, h.B'ψ⟫_ℂ = ⟪ψ, A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain⟫_ℂ :=
    A.shifted_symmetric ψ h.h_norm h.hψ_A h.hψ_A h.B'ψ_in_A_domain

  have h_sym2 : ⟪h.B'ψ, h.A'ψ⟫_ℂ = ⟪ψ, B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain⟫_ℂ :=
    B.shifted_symmetric ψ h.h_norm h.hψ_B h.hψ_B h.A'ψ_in_B_domain

  -- Step 2: The difference relates to the commutator via:
  -- Im(z) = (z - conj(z)) / (2i), and conj⟨u,v⟩ = ⟨v,u⟩
  have h_im_formula : (⟪h.A'ψ, h.B'ψ⟫_ℂ).im = (⟪h.A'ψ, h.B'ψ⟫_ℂ - ⟪h.B'ψ, h.A'ψ⟫_ℂ).im / 2 := by
    rw [← inner_conj_symm h.B'ψ h.A'ψ]
    simp only [Complex.sub_im, Complex.conj_im]
    ring

  rw [h_im_formula, h_sym1, h_sym2]

  -- Step 3: Show A'(B'ψ) - B'(A'ψ) = ABψ - BAψ (the scalar terms cancel)
  have h_expand : A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain -
                  B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain =
                  commutatorAt A B ψ h.toDomainConditions := by
    unfold shiftedApply ShiftedDomainConditions.A'ψ ShiftedDomainConditions.B'ψ
    unfold commutatorAt DomainConditions.ABψ DomainConditions.BAψ
    -- A'(B'ψ) = A(Bψ - μ_B•ψ) - μ_A•(Bψ - μ_B•ψ)
    --         = ABψ - μ_B•Aψ - μ_A•Bψ + μ_A•μ_B•ψ
    -- B'(A'ψ) = B(Aψ - μ_A•ψ) - μ_B•(Aψ - μ_A•ψ)
    --         = BAψ - μ_A•Bψ - μ_B•Aψ + μ_A•μ_B•ψ
    -- Difference = ABψ - BAψ (all other terms cancel!)
    simp only [shiftedApply]
    rw [A.apply_sub h.hBψ_A (A.domain.smul_mem _ h.hψ_A)]
    rw [A.apply_smul _ h.hψ_A]
    rw [B.apply_sub h.hAψ_B (B.domain.smul_mem _ h.hψ_B)]
    rw [B.apply_smul _ h.hψ_B]
    module

  --simp only [inner_sub_right, h_expand] -- `simp` made no progress
  unfold commutatorAt DomainConditions.ABψ DomainConditions.BAψ
  simp only [inner_sub_right]
  ring_nf
  /-⊢ (⟪ψ, A.shiftedApply ψ h.B'ψ ⋯ ⋯ ⋯⟫_ℂ - ⟪ψ, B.shiftedApply ψ h.A'ψ ⋯ ⋯ ⋯⟫_ℂ).im * (1 / 2) =
  (⟪ψ, A ⬝ B ⬝ ψ ⊢ ⋯ ⊢ ⋯⟫_ℂ - ⟪ψ, B ⬝ A ⬝ ψ ⊢ ⋯ ⊢ ⋯⟫_ℂ).im * (1 / 2)-/
  have h_key : ⟪ψ, A.shiftedApply ψ h.B'ψ h.h_norm h.hψ_A h.B'ψ_in_A_domain⟫_ℂ -
               ⟪ψ, B.shiftedApply ψ h.A'ψ h.h_norm h.hψ_B h.A'ψ_in_B_domain⟫_ℂ =
               ⟪ψ, h.ABψ⟫_ℂ - ⟪ψ, h.BAψ⟫_ℂ := by
    rw [← inner_sub_right, ← inner_sub_right, h_expand]
    exact rfl
  rw [h_key]
  exact rfl


/-- For a purely imaginary number, the norm equals the absolute value of the imaginary part -/
theorem norm_eq_abs_im_of_re_zero {z : ℂ} (h : z.re = 0) : ‖z‖ = |z.im| := by
  have hz : z = z.im * Complex.I := Complex.ext (by simp [h]) (by simp)
  rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact congrArg abs (congrArg Complex.im hz)

/-============================================================================
  SECTION 4: ROBERTSON'S UNCERTAINTY PRINCIPLE
============================================================================-/

/--
**Robertson's Uncertainty Principle** (1929)

For symmetric operators A and B on a Hilbert space, and any normalized
state ψ in the appropriate domain:

    σ_A · σ_B ≥ (1/2)|⟨ψ, [A,B]ψ⟩|

where σ_A = √Var(A) is the standard deviation (uncertainty) of A.

This is the fundamental quantum mechanical uncertainty relation,
showing that non-commuting observables cannot be simultaneously
known with arbitrary precision.
-/
theorem robertson_uncertainty (A B : UnboundedObservable H) (ψ : H)
    (h : ShiftedDomainConditions A B ψ) :
    A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B ≥
    (1/2) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖ := by

  /-
  STEP 1: CAUCHY-SCHWARZ

  |⟨A'ψ, B'ψ⟩|² ≤ ‖A'ψ‖² · ‖B'ψ‖² = Var(A) · Var(B)
  -/

  have h_cs : ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖ ≤ ‖h.A'ψ‖ * ‖h.B'ψ‖ :=
    norm_inner_le_norm h.A'ψ h.B'ψ

  -- Square both sides
  have h_cs_sq : ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖^2 ≤ ‖h.A'ψ‖^2 * ‖h.B'ψ‖^2 := by
    have := sq_le_sq' (norm_nonneg _) h_cs
    rwa [mul_pow] at this

  -- Recognize variances
  have h_var_eq : ‖h.A'ψ‖^2 * ‖h.B'ψ‖^2 =
                  A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B := by
    unfold variance ShiftedDomainConditions.A'ψ ShiftedDomainConditions.B'ψ
    rfl

  /-
  STEP 2: DECOMPOSE THE INNER PRODUCT

  ⟨A'ψ, B'ψ⟩ has:
  - Real part from anticommutator (covariance)
  - Imaginary part from commutator

  We only need: |⟨A'ψ, B'ψ⟩|² ≥ |Im⟨A'ψ, B'ψ⟩|²
  -/

  have h_im_le : (⟪h.A'ψ, h.B'ψ⟫_ℂ).im^2 ≤ ‖⟪h.A'ψ, h.B'ψ⟫_ℂ‖^2 := by
    rw [Complex.sq_norm]
    have := normSq_eq_re_sq_add_im_sq ⟪h.A'ψ, h.B'ψ⟫_ℂ
    linarith [sq_nonneg (⟪h.A'ψ, h.B'ψ⟫_ℂ).re]

  /-
  STEP 3: CONNECT IMAGINARY PART TO COMMUTATOR

  Im⟨A'ψ, B'ψ⟩ = (1/2)Im⟨ψ, [A',B']ψ⟩ = (1/2)Im⟨ψ, [A,B]ψ⟩

  And since the commutator expectation is purely imaginary:
  |⟨ψ, [A,B]ψ⟩| = |Im⟨ψ, [A,B]ψ⟩|
  -/

  -- The key relation between the inner product and commutator
  have h_im_eq : (⟪h.A'ψ, h.B'ψ⟫_ℂ).im =
                 (1/2) * (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im :=
    im_inner_shifted_eq_half_commutator A B ψ h

  -- The commutator expectation is purely imaginary
  have h_comm_re_zero : (⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).re = 0 :=
    commutator_re_eq_zero A B ψ h.toDomainConditions

  -- So its norm equals the absolute value of its imaginary part
  have h_comm_norm : ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖ =
                     |(⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ).im| :=
    norm_eq_abs_im_of_re_zero h_comm_re_zero

  /-
  STEP 4: ASSEMBLE THE BOUND

  Var(A)·Var(B) ≥ |⟨A'ψ,B'ψ⟩|² ≥ Im(⟨A'ψ,B'ψ⟩)² = (1/4)|⟨[A,B]⟩|²

  Taking square roots:
  σ_A · σ_B ≥ (1/2)|⟨[A,B]⟩|
  -/

  -- Combine the inequalities at the variance level
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

  -- Take square roots
  have h_sqrt_bound : Real.sqrt (A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B) ≥
                      Real.sqrt ((1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2) :=
    Real.sqrt_le_sqrt h_var_bound

  -- Simplify LHS: √(Var(A)·Var(B)) = σ_A · σ_B
  have h_lhs : Real.sqrt (A.variance ψ h.h_norm h.hψ_A * B.variance ψ h.h_norm h.hψ_B) =
               A.stdDev ψ h.h_norm h.hψ_A * B.stdDev ψ h.h_norm h.hψ_B := by
    unfold stdDev
    rw [← Real.sqrt_mul (variance_nonneg A ψ h.h_norm h.hψ_A)]

  -- Simplify RHS: √((1/4)·|z|²) = (1/2)·|z|
  have h_rhs : Real.sqrt ((1/4) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖^2) =
               (1/2) * ‖⟪ψ, commutatorAt A B ψ h.toDomainConditions⟫_ℂ‖ := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1/4)]
    rw [Real.sqrt_sq (norm_nonneg _)]
    have : Real.sqrt (1/4 : ℝ) = 1/2 := by
      rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]
      congr 1
      norm_num
    rw [this]

  -- Combine
  rw [h_lhs, h_rhs] at h_sqrt_bound
  exact h_sqrt_bound
