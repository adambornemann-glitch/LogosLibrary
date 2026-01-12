
/-
================================================================================
SCHRÖDINGER'S UNCERTAINTY RELATION — A LEAN 4 FORMALIZATION
================================================================================

Author: Adam Bornemann (Robertson foundation)

Mathematical Content: E. Schrödinger's strengthened uncertainty relation (1930)

────────────────────────────────────────────────────────────────────────────────
MAIN RESULT
────────────────────────────────────────────────────────────────────────────────

For symmetric operators A and B on a Hilbert space H, and any normalized
state ψ in the appropriate domain:

        σ_A² · σ_B²  ≥  (1/4)|⟨[A,B]⟩|²  +  Cov(A,B)²

where:
  • σ_A² = Var(A) = ⟨(A - ⟨A⟩)²⟩     is the variance of A
  • σ_B² = Var(B) = ⟨(B - ⟨B⟩)²⟩     is the variance of B
  • [A,B] = AB - BA                   is the commutator
  • Cov(A,B) = ½⟨{Ã,B̃}⟩              is the quantum covariance
            = ½(⟨AB + BA⟩ - 2⟨A⟩⟨B⟩)
  • {Ã,B̃} = ÃB̃ + B̃Ã                 is the anticommutator of shifted operators

This STRICTLY STRENGTHENS Robertson's inequality:

        σ_A · σ_B  ≥  (1/2)|⟨[A,B]⟩|        (Robertson 1929)

The additional covariance term is always non-negative, so Schrödinger's
bound is at least as tight as Robertson's, and strictly tighter when
Cov(A,B) ≠ 0.

────────────────────────────────────────────────────────────────────────────────
THE KEY INSIGHT: ROBERTSON DROPS A TERM
────────────────────────────────────────────────────────────────────────────────

Both proofs begin identically:

  1. Shift operators: Ã = A - ⟨A⟩I, B̃ = B - ⟨B⟩I
  2. Cauchy-Schwarz: Var(A)·Var(B) = ‖Ãψ‖²·‖B̃ψ‖² ≥ |⟨Ãψ, B̃ψ⟩|²
  3. Decompose: 2⟨Ãψ, B̃ψ⟩ = ⟨{Ã,B̃}⟩ + ⟨[Ã,B̃]⟩
                           = (real)  + (imaginary)

At this point:
  |⟨Ãψ, B̃ψ⟩|² = (1/4)(⟨{Ã,B̃}⟩² + |⟨[A,B]⟩|²)
                       ↑              ↑
                   COVARIANCE    COMMUTATOR

Robertson DISCARDS the covariance term (it's ≥ 0, so inequality still holds).
Schrödinger KEEPS it.

That's the entire difference. The "strengthening" is simply not throwing
away information that was already computed.

────────────────────────────────────────────────────────────────────────────────
GEOMETRIC INTERPRETATION
────────────────────────────────────────────────────────────────────────────────

The complex number ⟨Ãψ, B̃ψ⟩ lives in ℂ ≅ ℝ².

  • Real axis: Covariance (symmetric/anticommutator contribution)
  • Imaginary axis: Commutator contribution

Robertson bounds only the imaginary component: |Im(z)| ≤ |z|
Schrödinger uses the full Pythagorean theorem: |z|² = Re(z)² + Im(z)²

Both are consequences of Hilbert space geometry (Cauchy-Schwarz).
Neither requires self-adjointness — symmetry suffices.

────────────────────────────────────────────────────────────────────────────────
WHEN DOES SCHRÖDINGER BEAT ROBERTSON?
────────────────────────────────────────────────────────────────────────────────

The covariance Cov(A,B) = ½⟨{Ã,B̃}⟩ measures the "correlation" between
observables A and B in state ψ.

  • Cov(A,B) = 0: Schrödinger = Robertson (e.g., Gaussian wave packets
                  for position-momentum, which saturate Robertson)

  • Cov(A,B) ≠ 0: Schrödinger is strictly stronger
                  (e.g., squeezed states, correlated observables)

For qubits (2-level systems), Schrödinger's inequality is an EQUALITY
for all states and all pairs of observables. This is because SU(2) acts
transitively on the Bloch sphere — there's no "slack" in the bound.

────────────────────────────────────────────────────────────────────────────────
HISTORICAL NOTE
────────────────────────────────────────────────────────────────────────────────

Schrödinger published this strengthening in 1930, just one year after
Robertson's generalization. Yet it remains far less known — most textbooks
present only Robertson's version.

Why? Probably because:
  1. For position-momentum with Gaussian states, Robertson saturates
  2. The covariance term is state-dependent and harder to interpret
  3. Robertson's form |⟨[A,B]⟩|/2 is more "canonical" looking

But Schrödinger's version reveals the full geometric content of the
uncertainty principle as a statement about inner product decomposition.

────────────────────────────────────────────────────────────────────────────────
REFERENCES
────────────────────────────────────────────────────────────────────────────────

[1] Schrödinger, E. (1930). "Zum Heisenbergschen Unschärfeprinzip".
    Sitzungsberichte der Preussischen Akademie der Wissenschaften,
    Physikalisch-mathematische Klasse 14: 296-303.

[2] Robertson, H.P. (1929). "The Uncertainty Principle".
    Physical Review 34(2): 163-164.

[3] Angelow, A. & Batoni, M. (1999). "Translation with annotation of the
    original paper of Erwin Schrödinger (1930)".
    Bulgarian Journal of Physics 26(5/6): 193-203. arXiv:quant-ph/9903100

[4] Griffiths, D.J. "Introduction to Quantum Mechanics" Problem 3.35
    (derives Schrödinger's relation as an exercise)

────────────────────────────────────────────────────────────────────────────────
-/
import LogosLibrary.QuantumMechanics.Uncertainty.Core

namespace Schrodinger.Theorem
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open InnerProductSpace MeasureTheory Complex
open Robertson.Core Robertson.Lemmas
open scoped BigOperators

/-============================================================================
  SCHRÖDINGER'S UNCERTAINTY RELATION (VARIANCE FORM)
============================================================================-/

/--
Schrödinger's Strengthened Uncertainty Relation (1930).

This is the FULL geometric content of Cauchy-Schwarz applied to quantum
observables, without discarding the covariance term that Robertson drops.

For symmetric operators A and B:

  Var(A) · Var(B) ≥ (1/4)|⟨[A,B]⟩|² + (1/4)|⟨{Ã,B̃}⟩|²

where Ã = A - ⟨A⟩I and B̃ = B - ⟨B⟩I are the mean-shifted operators.

The second term (1/4)|⟨{Ã,B̃}⟩|² = Cov(A,B)² is the quantum covariance
squared, which Robertson's inequality discards.

Key insight: This theorem requires EXACTLY the same hypotheses as Robertson.
The additional strength comes for free — we simply don't throw away a
non-negative term that was already computed in the proof.
-/
theorem schrodinger_uncertainty_principle {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [IsScalarTower ℝ ℂ H]
    (A B : UnboundedObservable H)
    (ψ : H)
    (h_norm : ‖ψ‖ = 1)
    (h_domain_A : ψ ∈ A.domain)
    (h_domain_B : ψ ∈ B.domain)
    (h_domain_comp_AB : B.op ψ ∈ A.domain)
    (h_domain_comp_BA : A.op ψ ∈ B.domain) :
    unboundedVariance A ψ h_norm h_domain_A * unboundedVariance B ψ h_norm h_domain_B ≥
    (1/4) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖^2 +
    (1/4) * (⟪ψ, ((A.op - (unboundedExpectationValue A ψ h_norm h_domain_A) • (1 : H →ₗ[ℂ] H)) ∘ₗ
                  (B.op - (unboundedExpectationValue B ψ h_norm h_domain_B) • (1 : H →ₗ[ℂ] H)) +
                  (B.op - (unboundedExpectationValue B ψ h_norm h_domain_B) • (1 : H →ₗ[ℂ] H)) ∘ₗ
                  (A.op - (unboundedExpectationValue A ψ h_norm h_domain_A) • (1 : H →ₗ[ℂ] H))) ψ⟫_ℂ).re^2 := by

  /-
  STEP 1: SHIFT OPERATORS BY EXPECTATION VALUES

  Identical to Robertson's proof.
  -/

  set A_exp := unboundedExpectationValue A ψ h_norm h_domain_A
  set B_exp := unboundedExpectationValue B ψ h_norm h_domain_B
  set A' := A.op - A_exp • (1 : H →ₗ[ℂ] H)
  set B' := B.op - B_exp • (1 : H →ₗ[ℂ] H)

  -- Shifted operators remain symmetric
  have h_A'_symmOp : ∀ v w, v ∈ A.domain → w ∈ A.domain → ⟪A' v, w⟫_ℂ = ⟪v, A' w⟫_ℂ :=
    isSymmetric_sub_smul_of_real A.op A_exp A.domain A.SymmetricOperator

  have h_B'_symmOp : ∀ v w, v ∈ B.domain → w ∈ B.domain → ⟪B' v, w⟫_ℂ = ⟪v, B' w⟫_ℂ :=
    isSymmetric_sub_smul_of_real B.op B_exp B.domain B.SymmetricOperator

  /-
  STEP 2: APPLY CAUCHY-SCHWARZ

  Identical to Robertson's proof.
  -/

  have h_cauchy_schwarz :
      unboundedVariance A ψ h_norm h_domain_A * unboundedVariance B ψ h_norm h_domain_B ≥
      ‖⟪A' ψ, B' ψ⟫_ℂ‖^2 := by
    show ‖A' ψ‖^2 * ‖B' ψ‖^2 ≥ ‖⟪A' ψ, B' ψ⟫_ℂ‖^2
    have hcs : ‖⟪A' ψ, B' ψ⟫_ℂ‖ ≤ ‖A' ψ‖ * ‖B' ψ‖ := norm_inner_le_norm (A' ψ) (B' ψ)
    have hcs_sq : ‖⟪A' ψ, B' ψ⟫_ℂ‖^2 ≤ (‖A' ψ‖ * ‖B' ψ‖)^2 := by
      apply pow_le_pow_of_le_left
      · exact norm_nonneg _
      · exact hcs
    rw [mul_pow] at hcs_sq
    exact hcs_sq

  /-
  STEP 3: DOMAIN BOOKKEEPING

  Identical to Robertson's proof.
  -/

  have h_dom_B'ψ_A : B' ψ ∈ A.domain :=
    A.domain.sub_mem h_domain_comp_AB (A.domain.smul_mem _ h_domain_A)
  have h_dom_A'ψ_B : A' ψ ∈ B.domain :=
    B.domain.sub_mem h_domain_comp_BA (B.domain.smul_mem _ h_domain_B)

  /-
  STEP 4: DECOMPOSE INNER PRODUCT

  This is where the magic happens. We decompose:
    ⟨Ãψ, B̃ψ⟩ = (1/2)(⟨{Ã,B̃}⟩ + ⟨[Ã,B̃]⟩)
              = (1/2)(real + imaginary)
  -/

  have h_decomposition :
      ⟪A' ψ, B' ψ⟫_ℂ =
      (1/2 : ℂ) * (⟪ψ, (A' ∘ₗ B' + B' ∘ₗ A') ψ⟫_ℂ + ⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ) := by
    have h1 : ⟪A' ψ, B' ψ⟫_ℂ = ⟪ψ, (A' ∘ₗ B') ψ⟫_ℂ := by
      rw [LinearMap.comp_apply]
      rw [← h_A'_symmOp ψ (B' ψ) h_domain_A h_dom_B'ψ_A]
    rw [h1]
    simp only [LinearMap.add_apply, LinearMap.sub_apply, inner_add_right, inner_sub_right]
    ring

  /-
  STEP 5: THE SCHRÖDINGER BOUND — KEEP BOTH TERMS!

  Here's where we diverge from Robertson. Instead of discarding the real
  part (anticommutator/covariance), we keep the full Pythagorean identity:

    |z|² = Re(z)² + Im(z)²

  This gives us the strengthened bound.
  -/

  have h_schrodinger_bound :
      ‖⟪A' ψ, B' ψ⟫_ℂ‖^2 =
      (1/4) * (⟪ψ, (A' ∘ₗ B' + B' ∘ₗ A') ψ⟫_ℂ).re^2 +
      (1/4) * (⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ).im^2 := by

    set C := ⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ  -- Commutator expectation (imaginary)
    set D := ⟪ψ, (A' ∘ₗ B' + B' ∘ₗ A') ψ⟫_ℂ  -- Anticommutator expectation (real)

    -- C is purely imaginary
    have h_C_imaginary : C.re = 0 := by
      apply expectation_commutator_re_eq_zero A' B' ψ A.domain B.domain
            h_A'_symmOp h_B'_symmOp h_domain_A h_domain_B h_dom_B'ψ_A h_dom_A'ψ_B

    -- D is purely real
    have h_D_real : D.im = 0 := by
      apply expectation_anticommutator_im_eq_zero A' B' ψ A.domain B.domain
            h_A'_symmOp h_B'_symmOp h_domain_A h_domain_B h_dom_B'ψ_A h_dom_A'ψ_B

    -- The key calculation: |⟨Ãψ,B̃ψ⟩|² = (1/4)(D.re² + C.im²)
    calc ‖⟪A' ψ, B' ψ⟫_ℂ‖^2
      _ = ‖(1/2 : ℂ) * (D + C)‖^2 := by rw [h_decomposition]
      _ = (1/4) * ‖D + C‖^2 := by norm_num; ring
      _ = (1/4) * ((D + C).re^2 + (D + C).im^2) := by
          congr 1
          rw [Complex.sq_norm, Complex.normSq_apply]
          ring
      _ = (1/4) * (D.re^2 + C.im^2) := by
          -- Use D.im = 0 and C.re = 0
          rw [Complex.add_re, Complex.add_im, h_C_imaginary, h_D_real]
          ring
      _ = (1/4) * D.re^2 + (1/4) * C.im^2 := by ring

  /-
  STEP 6: RELATE COMMUTATOR TO ORIGINAL OPERATORS

  The commutator is invariant under shifting: [Ã,B̃] = [A,B]
  So we can express the commutator term using the original operators.
  -/

  have h_commutator_norm_eq :
      (⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ).im^2 =
      ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖^2 := by
    -- First show the commutators are equal
    have h_comm_eq : ⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ =
                     ⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ := by
      -- The commutator is invariant under real affine shifts
      calc ⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ
        _ = ⟪ψ, A' (B' ψ) - B' (A' ψ)⟫_ℂ := by
            simp [LinearMap.sub_apply, LinearMap.comp_apply]
        _ = ⟪ψ, (A.op - A_exp • 1) ((B.op - B_exp • 1) ψ) -
                (B.op - B_exp • 1) ((A.op - A_exp • 1) ψ)⟫_ℂ := rfl
        _ = ⟪ψ, (A.op - A_exp • 1) (B.op ψ - B_exp • ψ) -
                (B.op - B_exp • 1) (A.op ψ - A_exp • ψ)⟫_ℂ := by trivial
        _ = ⟪ψ, A.op (B.op ψ) - A.op (B_exp • ψ) - A_exp • (B.op ψ) + A_exp • (B_exp • ψ) -
                (B.op (A.op ψ) - B.op (A_exp • ψ) - B_exp • (A.op ψ) + B_exp • (A_exp • ψ))⟫_ℂ := by
            simp only [LinearMap.sub_apply, LinearMap.smul_apply]
            rw [LinearMap.map_sub A.op (B.op ψ) (B_exp • ψ)]
            rw [LinearMap.map_sub B.op (A.op ψ) (A_exp • ψ)]
            simp only [sub_sub, add_sub]
            simp_all [A', A_exp, B', B_exp]
            abel_nf!; ring_nf!; simp!; abel_nf!
        _ = ⟪ψ, A.op (B.op ψ) - B_exp • (A.op ψ) - A_exp • (B.op ψ) + A_exp • B_exp • ψ -
                B.op (A.op ψ) + A_exp • (B.op ψ) + B_exp • (A.op ψ) - A_exp • B_exp • ψ⟫_ℂ := by
            conv_lhs => arg 2; rfl
            simp only [inner_sub_right, inner_add_right, smul_smul, mul_comm B_exp A_exp]
            abel_nf!; simp!; module
        _ = ⟪ψ, A.op (B.op ψ) - B.op (A.op ψ)⟫_ℂ := by abel_nf
        _ = ⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ := by
            simp [LinearMap.sub_apply, LinearMap.comp_apply]

    -- Now use the fact that the commutator expectation is purely imaginary
    -- So |⟨[A,B]⟩|² = Im(⟨[A,B]⟩)²
    rw [h_comm_eq]

    -- The commutator expectation is purely imaginary
    have h_comm_re_zero : (⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ).re = 0 := by
      -- Use the original operators' symmetry
      apply expectation_commutator_re_eq_zero A.op B.op ψ A.domain B.domain
            A.SymmetricOperator B.SymmetricOperator
            h_domain_A h_domain_B h_domain_comp_AB h_domain_comp_BA

    -- For purely imaginary z: |z|² = Im(z)²
    rw [Complex.sq_norm, Complex.normSq_apply, h_comm_re_zero]
    ring

  /-
  STEP 7: FINAL ASSEMBLY

  Combine Cauchy-Schwarz with the Schrödinger decomposition.
  -/

  calc unboundedVariance A ψ h_norm h_domain_A * unboundedVariance B ψ h_norm h_domain_B
    _ ≥ ‖⟪A' ψ, B' ψ⟫_ℂ‖^2 := h_cauchy_schwarz
    _ = (1/4) * (⟪ψ, (A' ∘ₗ B' + B' ∘ₗ A') ψ⟫_ℂ).re^2 +
        (1/4) * (⟪ψ, (A' ∘ₗ B' - B' ∘ₗ A') ψ⟫_ℂ).im^2 := h_schrodinger_bound
    _ = (1/4) * (⟪ψ, (A' ∘ₗ B' + B' ∘ₗ A') ψ⟫_ℂ).re^2 +
        (1/4) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖^2 := by
          rw [h_commutator_norm_eq]
    _ = (1/4) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖^2 +
        (1/4) * (⟪ψ, (A' ∘ₗ B' + B' ∘ₗ A') ψ⟫_ℂ).re^2 := by ring


/-============================================================================
  COROLLARY: ROBERTSON AS A SPECIAL CASE
============================================================================-/

/--
Robertson's inequality follows from Schrödinger by dropping a non-negative term.

This explicitly shows that Robertson is strictly weaker than Schrödinger
(unless the covariance term happens to be zero).
-/
theorem robertson_from_schrodinger {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [IsScalarTower ℝ ℂ H]
    (A B : UnboundedObservable H)
    (ψ : H)
    (h_norm : ‖ψ‖ = 1)
    (h_domain_A : ψ ∈ A.domain)
    (h_domain_B : ψ ∈ B.domain)
    (h_domain_comp_AB : B.op ψ ∈ A.domain)
    (h_domain_comp_BA : A.op ψ ∈ B.domain) :
    unboundedVariance A ψ h_norm h_domain_A * unboundedVariance B ψ h_norm h_domain_B ≥
    (1/4) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖^2 := by

  have h_schrodinger := schrodinger_uncertainty_principle A B ψ h_norm
                        h_domain_A h_domain_B h_domain_comp_AB h_domain_comp_BA

  -- The covariance term is non-negative (it's a square)
  have h_cov_nonneg : 0 ≤ (1/4) * (⟪ψ, ((A.op - (unboundedExpectationValue A ψ h_norm h_domain_A) • (1 : H →ₗ[ℂ] H)) ∘ₗ
                  (B.op - (unboundedExpectationValue B ψ h_norm h_domain_B) • (1 : H →ₗ[ℂ] H)) +
                  (B.op - (unboundedExpectationValue B ψ h_norm h_domain_B) • (1 : H →ₗ[ℂ] H)) ∘ₗ
                  (A.op - (unboundedExpectationValue A ψ h_norm h_domain_A) • (1 : H →ₗ[ℂ] H))) ψ⟫_ℂ).re^2 := by
    apply mul_nonneg
    · norm_num
    · exact sq_nonneg _

  linarith


/-============================================================================
  THE QUANTUM COVARIANCE
============================================================================-/

/--
Definition of quantum covariance between two observables.

Cov(A,B) = (1/2)⟨{Ã,B̃}⟩ = (1/2)(⟨AB⟩ + ⟨BA⟩) - ⟨A⟩⟨B⟩

This is the quantum generalization of classical covariance. Note that
unlike classical covariance, we need to symmetrize (AB + BA)/2 because
AB ≠ BA in general.
-/
noncomputable def quantumCovariance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (A B : UnboundedObservable H) (ψ : H) (h_norm : ‖ψ‖ = 1)
    (h_domain_A : ψ ∈ A.domain) (h_domain_B : ψ ∈ B.domain)
    (h_domain_comp_AB : B.op ψ ∈ A.domain) (h_domain_comp_BA : A.op ψ ∈ B.domain) : ℝ :=
  (1/2) * (⟪ψ, (A.op ∘ₗ B.op + B.op ∘ₗ A.op) ψ⟫_ℂ).re -
  unboundedExpectationValue A ψ h_norm h_domain_A *
  unboundedExpectationValue B ψ h_norm h_domain_B

/--
Schrödinger's inequality in terms of quantum covariance.

σ_A² · σ_B² ≥ (1/4)|⟨[A,B]⟩|² + Cov(A,B)²

This is the "textbook form" of Schrödinger's relation.
-/
theorem schrodinger_with_covariance {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [IsScalarTower ℝ ℂ H]
    (A B : UnboundedObservable H)
    (ψ : H)
    (h_norm : ‖ψ‖ = 1)
    (h_domain_A : ψ ∈ A.domain)
    (h_domain_B : ψ ∈ B.domain)
    (h_domain_comp_AB : B.op ψ ∈ A.domain)
    (h_domain_comp_BA : A.op ψ ∈ B.domain) :
    unboundedVariance A ψ h_norm h_domain_A * unboundedVariance B ψ h_norm h_domain_B ≥
    (1/4) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖^2 +
    (quantumCovariance A B ψ h_norm h_domain_A h_domain_B h_domain_comp_AB h_domain_comp_BA)^2 := by

  -- This follows from schrodinger_uncertainty_principle by showing the
  -- anticommutator term equals the covariance squared

  set A_exp := unboundedExpectationValue A ψ h_norm h_domain_A
  set B_exp := unboundedExpectationValue B ψ h_norm h_domain_B
  set A' := A.op - A_exp • (1 : H →ₗ[ℂ] H)
  set B' := B.op - B_exp • (1 : H →ₗ[ℂ] H)

  have h_main := schrodinger_uncertainty_principle A B ψ h_norm
                 h_domain_A h_domain_B h_domain_comp_AB h_domain_comp_BA

  -- Need to show the anticommutator of shifted operators relates to covariance
  have h_anticomm_eq : (⟪ψ, (A' ∘ₗ B' + B' ∘ₗ A') ψ⟫_ℂ).re =
                       2 * quantumCovariance A B ψ h_norm h_domain_A h_domain_B
                           h_domain_comp_AB h_domain_comp_BA := by
    unfold quantumCovariance

    /-
    Strategy: Prove that
      ⟪ψ, (A' ∘ₗ B' + B' ∘ₗ A') ψ⟫ = ⟪ψ, (A ∘ₗ B + B ∘ₗ A) ψ⟫ - 2·A_exp·B_exp

    The expansion:
      {Ã,B̃}ψ = (A - ⟨A⟩I)(B - ⟨B⟩I)ψ + (B - ⟨B⟩I)(A - ⟨A⟩I)ψ
             = {A,B}ψ - 2⟨A⟩Bψ - 2⟨B⟩Aψ + 2⟨A⟩⟨B⟩ψ

    Taking ⟨ψ|·⟩ and using ⟨ψ|Aψ⟩ = ⟨A⟩, ⟨ψ|Bψ⟩ = ⟨B⟩, ⟨ψ|ψ⟩ = 1:
      ⟨{Ã,B̃}⟩ = ⟨{A,B}⟩ - 2⟨A⟩⟨B⟩ - 2⟨B⟩⟨A⟩ + 2⟨A⟩⟨B⟩
              = ⟨{A,B}⟩ - 2⟨A⟩⟨B⟩
    -/

    -- STEP 1: Normalization gives ⟪ψ, ψ⟫ = 1
    have h_inner_self : ⟪ψ, ψ⟫_ℂ = 1 := by
      exact (inner_eq_one_iff_of_norm_one h_norm h_norm).mpr rfl

    -- STEP 2: Symmetric operators have real expectation values
    -- For symmetric A: ⟪Aψ, ψ⟫ = ⟪ψ, Aψ⟫ and ⟪Aψ, ψ⟫ = star⟪ψ, Aψ⟫
    -- Therefore ⟪ψ, Aψ⟫ = star⟪ψ, Aψ⟫, which means Im⟪ψ, Aψ⟫ = 0

    have h_A_real : ⟪ψ, A.op ψ⟫_ℂ = (A_exp : ℂ) := by
      have h_sym := A.SymmetricOperator ψ ψ h_domain_A h_domain_A
      rw [← inner_conj_symm] at h_sym
      -- h_sym : (starRingEnd ℂ) ⟪ψ, A.op ψ⟫_ℂ = ⟪ψ, A.op ψ⟫_ℂ
      apply Complex.ext
      · -- Real part equals A_exp by definition
        rfl
      · -- Imaginary part is 0 since conj(z) = z implies Im(z) = 0
        simp only [Complex.ofReal_im]
        -- starRingEnd ℂ is just complex conjugation
        have h_im := congr_arg Complex.im h_sym
        simp only [Complex.conj_im] at h_im
        -- h_im : -⟪ψ, A.op ψ⟫_ℂ.im = ⟪ψ, A.op ψ⟫_ℂ.im
        linarith

    have h_B_real : ⟪ψ, B.op ψ⟫_ℂ = (B_exp : ℂ) := by
      have h_sym := B.SymmetricOperator ψ ψ h_domain_B h_domain_B
      rw [← inner_conj_symm] at h_sym
      apply Complex.ext
      · rfl
      · simp only [Complex.ofReal_im]
        have h_im := congr_arg Complex.im h_sym
        simp only [Complex.conj_im] at h_im
        linarith

    -- STEP 3: Main algebraic expansion
    -- Expand A'(B'ψ) + B'(A'ψ) where A' = A - A_exp•I, B' = B - B_exp•I

    have h_main : ⟪ψ, (A' ∘ₗ B' + B' ∘ₗ A') ψ⟫_ℂ =
              ⟪ψ, (A.op ∘ₗ B.op + B.op ∘ₗ A.op) ψ⟫_ℂ - 2 * ↑A_exp * ↑B_exp := by
      have h_one : ∀ v : H, (1 : H →ₗ[ℂ] H) v = v := fun v => rfl

      have h_map_smul_real : ∀ (f : H →ₗ[ℂ] H) (r : ℝ) (v : H), f (r • v) = r • f v := by
        intros f r v
        rw [← algebraMap_smul ℂ r v, f.map_smul, algebraMap_smul]

      have h_inner_smul_real : ∀ (r : ℝ) (v : H), ⟪ψ, r • v⟫_ℂ = ↑r * ⟪ψ, v⟫_ℂ := by
        intros r v
        rw [← algebraMap_smul ℂ r v, inner_smul_right]
        rfl

      simp only [A', B']
      simp only [LinearMap.add_apply, LinearMap.comp_apply,
                LinearMap.sub_apply, LinearMap.smul_apply, h_one]
      simp only [LinearMap.map_sub, h_map_smul_real]
      -- Include h_inner_smul_real and h_inner_self in this simp to fully expand
      simp only [inner_add_right, inner_sub_right, h_inner_smul_real, h_inner_self]
      rw [h_A_real.symm, h_B_real.symm]
      ring

    -- STEP 4: Take real parts of both sides
    calc (⟪ψ, (A' ∘ₗ B' + B' ∘ₗ A') ψ⟫_ℂ).re
      _ = (⟪ψ, (A.op ∘ₗ B.op + B.op ∘ₗ A.op) ψ⟫_ℂ - 2 * ↑A_exp * ↑B_exp).re := by
            rw [h_main]
      _ = (⟪ψ, (A.op ∘ₗ B.op + B.op ∘ₗ A.op) ψ⟫_ℂ).re - (2 * ↑A_exp * ↑B_exp : ℂ).re := by
            rw [Complex.sub_re]
      _ = (⟪ψ, (A.op ∘ₗ B.op + B.op ∘ₗ A.op) ψ⟫_ℂ).re - 2 * A_exp * B_exp := by
            -- 2 * A_exp * B_exp is real, so (↑(2*A_exp*B_exp) : ℂ).re = 2*A_exp*B_exp
            simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                       mul_zero, sub_zero]
            abel
      _ = 2 * (1 / 2 * (⟪ψ, (A.op ∘ₗ B.op + B.op ∘ₗ A.op) ψ⟫_ℂ).re - A_exp * B_exp) := by
            ring

  calc unboundedVariance A ψ h_norm h_domain_A * unboundedVariance B ψ h_norm h_domain_B
    _ ≥ (1/4) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖^2 +
        (1/4) * (⟪ψ, (A' ∘ₗ B' + B' ∘ₗ A') ψ⟫_ℂ).re^2 := h_main
    _ = (1/4) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖^2 +
        (1/4) * (2 * quantumCovariance A B ψ h_norm h_domain_A h_domain_B
                    h_domain_comp_AB h_domain_comp_BA)^2 := by rw [h_anticomm_eq]
    _ = (1/4) * ‖⟪ψ, (A.op ∘ₗ B.op - B.op ∘ₗ A.op) ψ⟫_ℂ‖^2 +
        (quantumCovariance A B ψ h_norm h_domain_A h_domain_B
             h_domain_comp_AB h_domain_comp_BA)^2 := by ring

end Schrodinger.Theorem
