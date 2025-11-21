import LogosLibrary.DeepTheorems.Quantum.Uncertainty.Robertson.Core
import LogosLibrary.DeepTheorems.Quantum.Uncertainty.Robertson.Lemmas
/-
================================================================================
ROBERTSON'S UNCERTAINTY PRINCIPLE - COMPLETE PROOF
================================================================================

This file contains the complete proof of Robertson's generalized uncertainty
relation for unbounded self-adjoint operators on a Hilbert space:

  σ_A · σ_B ≥ (1/2)|⟨[A,B]⟩|

The proof strategy:
  Step 1: Shift operators by expectation values
  Step 2: Apply Cauchy-Schwarz: |⟨Ãψ, B̃ψ⟩|² ≤ ‖Ãψ‖² · ‖B̃ψ‖²
  Step 3: Decompose inner product into commutator/anticommutator
  Step 4: Extract imaginary part (commutator contribution)
  Step 5: Prove Commutator invariance under shifting
  Step 6: Combine and take square roots to get final inequality

This generalizes Heisenberg's position-momentum uncertainty to any pair
of non-commuting observables, showing uncertainty is intrinsic to QM.

References:
  - Robertson, H.P. (1929). Phys. Rev. 34, 163
  - Schrödinger, E. (1930). Sitzungsber. Preuss. Akad. Wiss. 14, 296
-/
namespace Robertson.Theorem

open InnerProductSpace MeasureTheory Complex
open Robertson.Core Robertson.Lemmas
open scoped BigOperators

/-============================================================================
  MAIN THEOREM: ROBERTSON'S UNCERTAINTY PRINCIPLE
============================================================================-/

/--
Robertson's Uncertainty Principle for Unbounded Self-Adjoint Operators.

Given two (possibly unbounded) self-adjoint operators A and B on a Hilbert
space H, and a normalized state ψ in the domain of both operators and their
compositions, the product of standard deviations satisfies:

  σ_A(ψ) · σ_B(ψ) ≥ (1/2)|⟨ψ, [A,B]ψ⟩|

This fundamental inequality shows that non-commuting observables cannot be
simultaneously known with arbitrary precision - not due to measurement
limitations, but as an intrinsic property of quantum states.

Key assumptions:
  - A, B are self-adjoint on their domains
  - ψ is normalized and in the domain of A, B, AB, and BA
  - The operators can be unbounded (like position/momentum)

The proof carefully tracks domain requirements for unbounded operators,
which is crucial for mathematical rigor when dealing with position and
momentum operators in L²(ℝ).
-/
theorem robertson_uncertainty_principle {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [IsScalarTower ℝ ℂ H]
    (A B : UnboundedObservable H)
    (ψ : H)
    (h_norm : ‖ψ‖ = 1)
    (h_domain_A : ψ ∈ A.domain)
    (h_domain_B : ψ ∈ B.domain)
    (h_domain_comp_AB : B.op ψ ∈ A.domain)
    (h_domain_comp_BA : A.op ψ ∈ B.domain) :
    unboundedStandardDeviation A ψ h_norm h_domain_A *
    unboundedStandardDeviation B ψ h_norm h_domain_B ≥
    (1/2) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖ := by

/-
STEP 1: SHIFT OPERATORS BY EXPECTATION VALUES

Define Ã = A - ⟨A⟩I and B̃ = B - ⟨B⟩I. These shifted operators have:
  - Zero expectation value: ⟨Ã⟩ = ⟨B̃⟩ = 0
  - Same commutator as originals: [Ã,B̃] = [A,B]
  - Variance equals squared norm: Var(A) = ‖Ãψ‖²
-/

  -- Compute expectation values
  set A_exp := unboundedExpectationValue A ψ h_norm h_domain_A
  set B_exp := unboundedExpectationValue B ψ h_norm h_domain_B

  -- Define shifted operators
  set A' := A.op - A_exp • (1 : H →ₗ[ℂ] H)
  set B' := B.op - B_exp • (1 : H →ₗ[ℂ] H)

  -- Prove shifted operators remain self-adjoint (real scalars preserve self-adjointness)
  have h_A'_sa : ∀ v w, v ∈ A.domain → w ∈ A.domain → ⟪A' v, w⟫_ℂ = ⟪v, A' w⟫_ℂ :=
    isSelfAdjoint_sub_smul_of_real A.op A_exp A.domain A.self_adjoint

  have h_B'_sa : ∀ v w, v ∈ B.domain → w ∈ B.domain → ⟪B' v, w⟫_ℂ = ⟪v, B' w⟫_ℂ :=
    isSelfAdjoint_sub_smul_of_real B.op B_exp B.domain B.self_adjoint

/-
STEP 2: APPLY CAUCHY-SCHWARZ INEQUALITY

For any vectors u, v in an inner product space:
  |⟨u,v⟩|² ≤ ‖u‖² · ‖v‖²

Applied to u = Ãψ, v = B̃ψ:
  |⟨Ãψ, B̃ψ⟩|² ≤ ‖Ãψ‖² · ‖B̃ψ‖² = Var(A) · Var(B)
-/

  have h_cauchy_schwarz :
      unboundedVariance A ψ h_norm h_domain_A * unboundedVariance B ψ h_norm h_domain_B ≥
      ‖⟪A' ψ, B' ψ⟫_ℂ‖^2 := by
    -- By definition: Var(A) = ‖Ãψ‖², Var(B) = ‖B̃ψ‖²
    show ‖A' ψ‖^2 * ‖B' ψ‖^2 ≥ ‖⟪A' ψ, B' ψ⟫_ℂ‖^2

    -- Apply Cauchy-Schwarz
    have hcs : ‖⟪A' ψ, B' ψ⟫_ℂ‖ ≤ ‖A' ψ‖ * ‖B' ψ‖ := norm_inner_le_norm (A' ψ) (B' ψ)

    -- Square both sides (preserves inequality for non-negative numbers)
    have hcs_sq : ‖⟪A' ψ, B' ψ⟫_ℂ‖^2 ≤ (‖A' ψ‖ * ‖B' ψ‖)^2 := by
      apply pow_le_pow_of_le_left
      · exact norm_nonneg _
      · exact hcs

    -- Simplify (a·b)² = a²·b²
    rw [mul_pow] at hcs_sq
    exact hcs_sq

/-
STEP 3: DECOMPOSE INNER PRODUCT INTO COMMUTATOR/ANTICOMMUTATOR

Key algebraic identity:
  2⟨Ãψ, B̃ψ⟩ = ⟨ψ, (ÃB̃ + B̃Ã)ψ⟩ + ⟨ψ, (ÃB̃ - B̃Ã)ψ⟩
              = ⟨ψ, {Ã,B̃}ψ⟩ + ⟨ψ, [Ã,B̃]ψ⟩

The anticommutator {Ã,B̃} has real expectation (symmetric)
The commutator [Ã,B̃] has imaginary expectation (antisymmetric)
-/

  -- Track domain membership for compositions
  have h_dom_B'ψ_A : B' ψ ∈ A.domain :=
    A.domain.sub_mem h_domain_comp_AB (A.domain.smul_mem _ h_domain_A)
  have h_dom_A'ψ_B : A' ψ ∈ B.domain :=
    B.domain.sub_mem h_domain_comp_BA (B.domain.smul_mem _ h_domain_B)

  -- Prove the decomposition identity
  have h_decomposition :
      ⟪A' ψ, B' ψ⟫_ℂ =
      (1/2 : ℂ) * (⟪ψ, (A' ∘ₗ B' + B' ∘ₗ A') ψ⟫_ℂ + ⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ) := by
    -- Use self-adjointness to move A' across the inner product
    have h1 : ⟪A' ψ, B' ψ⟫_ℂ = ⟪ψ, (A' ∘ₗ B') ψ⟫_ℂ := by
      rw [LinearMap.comp_apply]
      rw [← h_A'_sa ψ (B' ψ) h_domain_A h_dom_B'ψ_A]

    -- Expand as (AB + AB)/2 = AB, then rearrange
    rw [h1]
    simp only [LinearMap.add_apply, LinearMap.sub_apply, inner_add_right, inner_sub_right]
    ring

/-
STEP 4: EXTRACT IMAGINARY PART (COMMUTATOR CONTRIBUTION)

Since commutator expectation is purely imaginary and anticommutator
expectation is purely real, we have:
  ⟨Ãψ, B̃ψ⟩ = (real part) + i(imaginary part)

Therefore: |⟨Ãψ, B̃ψ⟩|² ≥ |Im⟨Ãψ, B̃ψ⟩|² = (1/4)|⟨[Ã,B̃]⟩|²
-/

  have h_commutator_bound :
      ‖⟪A' ψ, B' ψ⟫_ℂ‖^2 ≥
      (1/4) * ‖⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ‖^2 := by

    -- Define commutator and anticommutator expectations for clarity
    set C := ⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ  -- Commutator (imaginary)
    set D := ⟪ψ, (A' ∘ₗ B' + B' ∘ₗ A') ψ⟫_ℂ  -- Anticommutator (real)

    -- Prove C is purely imaginary (Re(C) = 0)
    have h_C_imaginary : C.re = 0 := by
      apply expectation_commutator_re_eq_zero A' B' ψ A.domain B.domain
            h_A'_sa h_B'_sa h_domain_A h_domain_B h_dom_B'ψ_A h_dom_A'ψ_B

    -- Prove D is purely real (Im(D) = 0)
    have h_D_real : D.im = 0 := by
      apply expectation_anticommutator_im_eq_zero A' B' ψ A.domain B.domain
            h_A'_sa h_B'_sa h_domain_A h_domain_B h_dom_B'ψ_A h_dom_A'ψ_B

    -- Calculate the bound using |z|² = Re(z)² + Im(z)²
    calc ‖⟪A' ψ, B' ψ⟫_ℂ‖^2
      _ = ‖(1/2 : ℂ) * (D + C)‖^2 := by rw [h_decomposition]
      _ = (1/4) * ‖D + C‖^2 := by norm_num; ring
      _ = (1/4) * (D.re^2 + C.im^2) := by
          congr 1
          rw [Complex.sq_norm, Complex.normSq_apply]
          rw [Complex.add_re, Complex.add_im, h_C_imaginary, h_D_real]
          simp
          -- ⊢ D.re * D.re + C.im * C.im = D.re ^ 2 + C.im ^ 2, easily solved with ring
          ring
      _ ≥ (1/4) * C.im^2 := by nlinarith  -- D.re² ≥ 0
      _ = (1/4) * ‖C‖^2 := by
          -- Since C is purely imaginary: ‖C‖² = |Im(C)|²
          congr 1
          rw [Complex.sq_norm, Complex.normSq_apply, h_C_imaginary]
          simp
          -- ⊢ C.im ^ 2 = C.im * C.im, easily solved with ring or linarith
          ring

/-
STEP 5: PROVE COMMUTATOR INVARIANCE UNDER SHIFTING

Key fact: [A - λI, B - μI] = [A,B] for any scalars λ, μ

This is because scalar multiples of identity commute with everything:
  [λI, B] = λIB - BλI = λB - λB = 0
-/

  have h_commutator_invariant :
    ⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ =
    ⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ := by
  -- The commutator of shifted operators equals the commutator of original operators
  -- because [A - λI, B - μI] = AB - AμI - λIB + λμI - BA + BλI + μIA - λμI
  --                          = AB - BA + terms that cancel
  {
  -- Let's be very explicit about the cancellation
  calc ⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ
    _ = ⟪ψ, A' (B' ψ) - B' (A' ψ)⟫_ℂ := by
        simp [LinearMap.sub_apply, LinearMap.comp_apply]
    _ = ⟪ψ, (A.op - A_exp • 1) ((B.op - B_exp • 1) ψ) -
            (B.op - B_exp • 1) ((A.op - A_exp • 1) ψ)⟫_ℂ := rfl
    _ = ⟪ψ, (A.op - A_exp • 1) (B.op ψ - B_exp • ψ) -
            (B.op - B_exp • 1) (A.op ψ - A_exp • ψ)⟫_ℂ := by
        trivial
    _ = ⟪ψ, A.op (B.op ψ) - A.op (B_exp • ψ) - A_exp • (B.op ψ) + A_exp • (B_exp • ψ) -
            (B.op (A.op ψ) - B.op (A_exp • ψ) - B_exp • (A.op ψ) + B_exp • (A_exp • ψ))⟫_ℂ := by
          -- Expand using linearity of A.op and B.op
        simp only [LinearMap.sub_apply, LinearMap.smul_apply]
        -- Distribute A.op over (B.op ψ - B_exp • ψ)
        rw [LinearMap.map_sub A.op (B.op ψ) (B_exp • ψ)]
        rw [LinearMap.map_sub B.op (A.op ψ) (A_exp • ψ)]
        -- Now it's just algebra
        simp only [sub_sub, add_sub]
        -- I will proceed to absolutely MASH the tactics.
        abel_nf! ; ring_nf!
        -- Not quite enough ey?  I see you.
        simp! ; abel_nf! -- got him!

    _ = ⟪ψ, A.op (B.op ψ) - B_exp • (A.op ψ) - A_exp • (B.op ψ) + A_exp • B_exp • ψ -
            B.op (A.op ψ) + A_exp • (B.op ψ) + B_exp • (A.op ψ) - A_exp • B_exp • ψ⟫_ℂ := by
        -- The trick is we need to first apply LinearMap.map_smul
        conv_lhs =>
          arg 2
          -- Convert A.op (B_exp • ψ) to B_exp • A.op ψ
          rfl
        -- Now handle the algebra
        simp only [inner_sub_right, inner_add_right, smul_smul, mul_comm B_exp A_exp]
        -- I will proceed to absolutely MASH the tactics.
        abel_nf! ; simp! ; ring_nf!

    _ = ⟪ψ, A.op (B.op ψ) - B.op (A.op ψ)⟫_ℂ := by
        -- Cancel terms
        abel_nf
    _ = ⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ := by
        simp [LinearMap.sub_apply, LinearMap.comp_apply]
  }
/-
STEP 6: COMBINE INEQUALITIES AND TAKE SQUARE ROOT

We've shown:
  Var(A)·Var(B) ≥ |⟨Ãψ,B̃ψ⟩|² ≥ (1/4)|⟨[A,B]⟩|²

Taking square roots (valid since both sides are non-negative):
  σ_A · σ_B ≥ (1/2)|⟨[A,B]⟩|

Mathematical subtlety: When taking square roots of an inequality between
non-negative numbers, the inequality direction is preserved. This is because
the square root function is monotonically increasing on [0,∞).
-/

  -- Combine the variance bound with the commutator bound
  have h_combined :
      unboundedVariance A ψ h_norm h_domain_A * unboundedVariance B ψ h_norm h_domain_B ≥
      (1/4) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖^2 := by
    calc unboundedVariance A ψ h_norm h_domain_A * unboundedVariance B ψ h_norm h_domain_B
      _ ≥ ‖⟪A' ψ, B' ψ⟫_ℂ‖^2 := h_cauchy_schwarz
      _ ≥ (1/4) * ‖⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ‖^2 := h_commutator_bound
      _ = (1/4) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖^2 := by
          rw [h_commutator_invariant]

/-
  CRUCIAL STEP: Apply square root to both sides of the inequality.

  Mathematical justification:
  - Both sides are non-negative (variances are ≥ 0, norms are ≥ 0)
  - sqrt is monotone: if 0 ≤ b ≤ a, then √b ≤ √a (preserves ≥ inequalities)
  - This transforms our variance inequality into a standard deviation inequality
-/

  -- Apply square root to both sides, preserving the inequality direction
  have h_sqrt : Real.sqrt (unboundedVariance A ψ h_norm h_domain_A *
                          unboundedVariance B ψ h_norm h_domain_B) ≥
                Real.sqrt ((1/4) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖^2) := by
    -- We have from h_combined: LHS ≥ RHS where both sides are non-negative
    -- The square root function is monotone increasing on [0,∞)
    -- So if a ≥ b ≥ 0, then √a ≥ √b

    -- First establish non-negativity of both sides
    have lhs_nonneg : 0 ≤ unboundedVariance A ψ h_norm h_domain_A *
                          unboundedVariance B ψ h_norm h_domain_B := by
      apply mul_nonneg
      · exact unboundedVariance_nonneg _ _ _ _
      · exact unboundedVariance_nonneg _ _ _ _

    have rhs_nonneg : 0 ≤ (1/4) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖^2 := by
      apply mul_nonneg
      · norm_num
      · exact sq_nonneg _
    -- Now apply the monotonicity of sqrt
    -- Since LHS ≥ RHS and both are ≥ 0, we have √LHS ≥ √RHS
    exact Real.sqrt_le_sqrt h_combined
  /-
    Now we simplify both sides of h_sqrt to get the final form.
    This involves two key algebraic facts:
    1. √(a·b) = √a · √b for non-negative a, b
    2. √(x²) = |x| = x for non-negative x
  -/

  -- Simplify the left-hand side: √(var(A) * var(B)) = √var(A) * √var(B) = σ_A * σ_B
  have lhs_eq : Real.sqrt (unboundedVariance A ψ h_norm h_domain_A *
                          unboundedVariance B ψ h_norm h_domain_B) =
                Real.sqrt (unboundedVariance A ψ h_norm h_domain_A) *
                Real.sqrt (unboundedVariance B ψ h_norm h_domain_B) := by
    apply Real.sqrt_mul
    -- Need to prove the variance is non-negative (which it always is)
    exact unboundedVariance_nonneg _ _ _ _

  -- Simplify the right-hand side: √((1/4) * ‖z‖²) = √(1/4) * √(‖z‖²) = (1/2) * ‖z‖
  have rhs_eq : Real.sqrt ((1/4) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖^2) =
              (1/2) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖ := by
    -- Step 1: Use √(a·b) = √a · √b
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1/4)]

    -- Step 2: Simplify √(1/4) = 1/2
    -- This works because (1/2)² = 1/4 and 1/2 ≥ 0
    have sqrt_quarter : Real.sqrt (1/4 : ℝ) = 1/2 := by
      have h : (1/2 : ℝ)^2 = 1/4 := by norm_num
      rw [← h, Real.sqrt_sq (by norm_num : 0 ≤ (1/2 : ℝ))]
    rw [sqrt_quarter]

    -- Step 3: Simplify √(‖z‖²) = ‖z‖
    -- This uses the fact that ‖z‖ ≥ 0, so √(‖z‖²) = |‖z‖| = ‖z‖
    rw [Real.sqrt_sq (norm_nonneg _)]

    /-
      FINAL STEP: Combine everything to get Robertson's inequality.

      We have:
      - h_sqrt: √(Var(A)·Var(B)) ≥ √((1/4)·‖⟨[A,B]⟩‖²)
      - lhs_eq: √(Var(A)·Var(B)) = σ_A · σ_B
      - rhs_eq: √((1/4)·‖⟨[A,B]⟩‖²) = (1/2)·‖⟨[A,B]⟩‖

      Therefore: σ_A · σ_B ≥ (1/2)·‖⟨[A,B]⟩‖
    -/

  -- Unfold the definition of standard deviation (which is √variance)
  unfold unboundedStandardDeviation

  -- Rewrite both sides of h_sqrt using our simplification lemmas
  rw [lhs_eq, rhs_eq] at h_sqrt

  -- h_sqrt now states exactly what we wanted to prove!
  exact h_sqrt





end Robertson.Theorem
