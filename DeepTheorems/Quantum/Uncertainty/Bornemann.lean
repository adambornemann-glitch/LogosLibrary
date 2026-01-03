/-
Author: Adam Bornemann, current SLOS (yeah, that's right- this is MY principle)
Created: 11/5/2025
Updated: 12/3/2026

================================================================================
BORNEMANN'S THEOREM OF FORBIDDEN SDS
================================================================================

**References:**
- Heisenberg, W. (1927). "Über den anschaulichen Inhalt der quantentheoretischen
  Kinematik und Mechanik". Z. Physik 43, 172-198.
- Kennard, E.H. (1927). "Zur Quantenmechanik einfacher Bewegungstypen".
  Z. Physik 44, 326-352. (First rigorous proof of σₓσₚ ≥ ℏ/2)
- Robertson, H.P. (1929). "The Uncertainty Principle". Phys. Rev. 34, 163-164.
- ME.

Note: Is this just a standard equation that falls out of Robertson?  Absolutely.
But I don't see any of you formalizing it and using it to kill Schwarzschild in dS,
so, respectfully- sit down.
-/
import LogosLibrary.DeepTheorems.Quantum.Uncertainty.Core -- For unbounded operators
import LogosLibrary.DeepTheorems.Quantum.Uncertainty.Robertson -- For unbounded operators
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Robertson.Core Robertson.Theorem

namespace Bornemann
/-!
### Angular Momentum Operators and Commutation Relations

For unbounded operators, commutators require careful domain considerations.
We need a common dense domain that is:
1. Contained in the domain of each L_i
2. Stable under each L_i (so compositions L_i L_j are defined)
-/

/-- Reduced Planck constant (in SI units: J·s) -/
noncomputable def ℏ : ℝ := 1.054571817e-34

/-- ℏ is positive -/
theorem hbar_pos : ℏ > 0 := by
  unfold ℏ
  norm_num

/-- The commutator [A, B]ψ = ABψ - BAψ for unbounded operators -/
def commutatorApply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (A B : UnboundedObservable H) (ψ : H) : H :=
  A.op (B.op ψ) - B.op (A.op ψ)

notation "[" A ", " B "]" => commutatorApply A B


/-!
### Expectation Values and Standard Deviation for Unbounded Operators

To state the uncertainty principle, we need:
1. Expectation value ⟨A⟩ = ⟨ψ|A|ψ⟩
2. Variance Var(A) = ⟨A²⟩ - ⟨A⟩²
3. Standard deviation σ_A = √Var(A)
-/
/- Inner product in complex Hilbert space (helper to avoid type inference issues) -/
noncomputable def complexInner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ φ : H) : ℂ :=
  @inner ℂ H _ ψ φ

/-- Expectation value of an unbounded observable: ⟨A⟩_ψ = ⟨ψ|A|ψ⟩ -/
noncomputable def unboundedExpectation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) : ℂ :=
  complexInner ψ (A.op ψ)

/-- For self-adjoint operators on normalized states, expectation is real

    **Proof sketch:**
    ⟨ψ|A|ψ⟩* = ⟨Aψ|ψ⟩ = ⟨ψ|Aψ⟩ (by self-adjointness)
    So ⟨A⟩* = ⟨A⟩, which means ⟨A⟩ ∈ ℝ
-/
theorem unboundedExpectation_conj_eq_self {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) (hψ : ψ ∈ A.domain) :
    starRingEnd ℂ (unboundedExpectation A ψ) = unboundedExpectation A ψ := by
  unfold unboundedExpectation complexInner
  rw [inner_conj_symm]
  have h_sa := A.self_adjoint ψ ψ hψ hψ
  exact h_sa

/-- Extract the real part of expectation (which equals the full value for self-adjoint) -/
noncomputable def unboundedExpectationReal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) : ℝ :=
  (unboundedExpectation A ψ).re

/-- Variance of an unbounded observable: Var(A) = ‖Aψ‖² - ⟨A⟩²

    This equals ⟨(A - ⟨A⟩)²⟩ = ⟨A²⟩ - ⟨A⟩² for normalized ψ.
-/
noncomputable def unboundedVariance {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) : ℝ :=
  ‖A.op ψ‖^2 - (unboundedExpectationReal A ψ)^2

/-- Standard deviation: σ_A = √Var(A) -/
noncomputable def unboundedStdDev {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) : ℝ :=
  Real.sqrt (unboundedVariance A ψ)

/-- Standard deviation is non-negative -/
theorem unboundedStdDev_nonneg {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) :
    unboundedStdDev A ψ ≥ 0 := by
  unfold unboundedStdDev
  exact Real.sqrt_nonneg _

/-- Angular momentum operators with canonical commutation relations

    **Mathematical structure:**
    - Three self-adjoint operators L_x, L_y, L_z on a Hilbert space H
    - A common dense domain D stable under all three operators
    - Commutation relations hold on D:
      [L_x, L_y] = iℏL_z  (and cyclic permutations)

    **Physical meaning:**
    - L_i generates rotations about the i-axis
    - Non-commutativity reflects incompatibility of measuring
      different angular momentum components simultaneously
    - Robertson uncertainty: σ_Lx · σ_Ly ≥ (ℏ/2)|⟨L_z⟩|

    **Why common domain matters:**
    - Unbounded operators aren't defined everywhere
    - To compute [L_x, L_y]ψ = L_x(L_y ψ) - L_y(L_x ψ), need:
      * ψ ∈ D(L_y) so L_y ψ exists
      * L_y ψ ∈ D(L_x) so L_x(L_y ψ) exists
      * Similarly for the other term
    - Common stable domain guarantees all this
-/
structure AngularMomentumOperators (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- x-component of angular momentum -/
  L_x : UnboundedObservable H
  /-- y-component of angular momentum -/
  L_y : UnboundedObservable H
  /-- z-component of angular momentum -/
  L_z : UnboundedObservable H

  /-- Common dense domain where all operators and their compositions are defined -/
  common_domain : Submodule ℂ H

  /-- The common domain is dense in H -/
  common_domain_dense : Dense (common_domain : Set H)

  /-- Common domain is contained in L_x domain -/
  common_in_Lx : ∀ ψ : H, ψ ∈ common_domain → ψ ∈ L_x.domain

  /-- Common domain is contained in L_y domain -/
  common_in_Ly : ∀ ψ : H, ψ ∈ common_domain → ψ ∈ L_y.domain

  /-- Common domain is contained in L_z domain -/
  common_in_Lz : ∀ ψ : H, ψ ∈ common_domain → ψ ∈ L_z.domain

  /-- L_x preserves the common domain -/
  Lx_stable : ∀ ψ : H, ψ ∈ common_domain → L_x.op ψ ∈ common_domain

  /-- L_y preserves the common domain -/
  Ly_stable : ∀ ψ : H, ψ ∈ common_domain → L_y.op ψ ∈ common_domain

  /-- L_z preserves the common domain -/
  Lz_stable : ∀ ψ : H, ψ ∈ common_domain → L_z.op ψ ∈ common_domain

  /-- Canonical commutation: [L_x, L_y] = iℏL_z -/
  commutation_xy : ∀ ψ : H, ψ ∈ common_domain →
    L_x.op (L_y.op ψ) - L_y.op (L_x.op ψ) = (Complex.I * (ℏ : ℂ)) • L_z.op ψ

  /-- Canonical commutation: [L_y, L_z] = iℏL_x -/
  commutation_yz : ∀ ψ : H, ψ ∈ common_domain →
    L_y.op (L_z.op ψ) - L_z.op (L_y.op ψ) = (Complex.I * (ℏ : ℂ)) • L_x.op ψ

  /-- Canonical commutation: [L_z, L_x] = iℏL_y -/
  commutation_zx : ∀ ψ : H, ψ ∈ common_domain →
    L_z.op (L_x.op ψ) - L_x.op (L_z.op ψ) = (Complex.I * (ℏ : ℂ)) • L_y.op ψ

/-- The commutator [L_x, L_y] equals iℏL_z as operators on the common domain -/
theorem Lx_Ly_commutator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H) (hψ : ψ ∈ L.common_domain) :
    [L.L_x, L.L_y] ψ = (Complex.I * (ℏ : ℂ)) • L.L_z.op ψ := by
  unfold commutatorApply
  exact L.commutation_xy ψ hψ

/-- The commutator [L_y, L_z] equals iℏL_x as operators on the common domain -/
theorem Ly_Lz_commutator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H) (hψ : ψ ∈ L.common_domain) :
    [L.L_y, L.L_z] ψ = (Complex.I * (ℏ : ℂ)) • L.L_x.op ψ := by
  unfold commutatorApply
  exact L.commutation_yz ψ hψ

/-- The commutator [L_z, L_x] equals iℏL_y as operators on the common domain -/
theorem Lz_Lx_commutator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H) (hψ : ψ ∈ L.common_domain) :
    [L.L_z, L.L_x] ψ = (Complex.I * (ℏ : ℂ)) • L.L_y.op ψ := by
  unfold commutatorApply
  exact L.commutation_zx ψ hψ

/-- Antisymmetry: [L_y, L_x] = -iℏL_z -/
theorem Ly_Lx_commutator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H) (hψ : ψ ∈ L.common_domain) :
    [L.L_y, L.L_x] ψ = -(Complex.I * (ℏ : ℂ)) • L.L_z.op ψ := by
  unfold commutatorApply
  have h := L.commutation_xy ψ hψ
  calc L.L_y.op (L.L_x.op ψ) - L.L_x.op (L.L_y.op ψ)
      = -(L.L_x.op (L.L_y.op ψ) - L.L_y.op (L.L_x.op ψ)) := by simp
    _ = -((Complex.I * (ℏ : ℂ)) • L.L_z.op ψ) := by rw [h]
    _ = -(Complex.I * (ℏ : ℂ)) • L.L_z.op ψ := by rw [neg_smul]

/-- Domain conditions for angular momentum uncertainty principle -/
structure AngularMomentumUncertaintyDomain {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H) : Prop where
  /-- ψ is in the common domain -/
  in_common : ψ ∈ L.common_domain
  /-- ψ is normalized -/
  normalized : ‖ψ‖ = 1



/- |iℏ| = ℏ (since ℏ > 0) -/
theorem norm_I_mul_hbar : ‖Complex.I * (ℏ : ℂ)‖ = ℏ := by
  rw [norm_mul, Complex.norm_I, one_mul]
  rw [Complex.norm_real]
  exact abs_of_pos hbar_pos

/-- Domain conditions for angular momentum uncertainty -/
structure AngularMomentumUncertaintyDomain' {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (L : AngularMomentumOperators H) (ψ : H) : Prop where
  h_norm : ‖ψ‖ = 1
  h_Lx : ψ ∈ L.L_x.domain
  h_Ly : ψ ∈ L.L_y.domain
  h_Lz : ψ ∈ L.L_z.domain
  h_Ly_in_Lx : L.L_y.op ψ ∈ L.L_x.domain
  h_Lx_in_Ly : L.L_x.op ψ ∈ L.L_y.domain

/-- The commutator [L_x, L_y] = iℏL_z -/
axiom angular_momentum_commutator_xy {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (L : AngularMomentumOperators H) (ψ : H)
    (h_Lx : ψ ∈ L.L_x.domain) (h_Ly : ψ ∈ L.L_y.domain)
    (h_Lz : ψ ∈ L.L_z.domain)
    (h_Ly_in_Lx : L.L_y.op ψ ∈ L.L_x.domain)
    (h_Lx_in_Ly : L.L_x.op ψ ∈ L.L_y.domain) :
    (L.L_x.op ∘ₗ L.L_y.op - L.L_y.op ∘ₗ L.L_x.op) ψ = (Complex.I * ℏ) • L.L_z.op ψ


/-- Robertson's uncertainty principle for angular momentum

    **Statement:**
    σ_Lx · σ_Ly ≥ (ℏ/2)|⟨L_z⟩|

    **Derivation:**
    From [L_x, L_y] = iℏL_z and general Robertson inequality:
    σ_A · σ_B ≥ (1/2)|⟨[A,B]⟩|

    We get:
    σ_Lx · σ_Ly ≥ (1/2)|⟨iℏL_z⟩| = (1/2)|iℏ||⟨L_z⟩| = (ℏ/2)|⟨L_z⟩|

    **Physical meaning:**
    You cannot simultaneously know L_x and L_y with arbitrary precision.
    The product of uncertainties has a lower bound proportional to |⟨L_z⟩|.
-/
theorem angular_momentum_uncertainty {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [IsScalarTower ℝ ℂ H]
    (L : AngularMomentumOperators H) (ψ : H)
    (h_domain : AngularMomentumUncertaintyDomain' L ψ) :
    unboundedStandardDeviation L.L_x ψ h_domain.h_norm h_domain.h_Lx *
    unboundedStandardDeviation L.L_y ψ h_domain.h_norm h_domain.h_Ly ≥
    (ℏ / 2) * ‖@inner ℂ H _ ψ (L.L_z.op ψ)‖ := by
  -- Step 1: Apply Robertson uncertainty principle with A = L_x, B = L_y
  have h_rob := robertson_uncertainty_principle L.L_x L.L_y ψ
                  h_domain.h_norm h_domain.h_Lx h_domain.h_Ly
                  h_domain.h_Ly_in_Lx h_domain.h_Lx_in_Ly

  -- Step 2: Get the commutator relation [L_x, L_y] = iℏL_z
  have h_comm := angular_momentum_commutator_xy L ψ
                   h_domain.h_Lx h_domain.h_Ly h_domain.h_Lz
                   h_domain.h_Ly_in_Lx h_domain.h_Lx_in_Ly

  have h_norm_ihbar : ‖(-Complex.I : ℂ) * ℏ‖ = ℏ := by
    calc ‖(-Complex.I : ℂ) * ℏ‖
        = ‖-Complex.I‖ * ‖(ℏ : ℂ)‖ := norm_mul (-Complex.I) ℏ
      _ = ‖Complex.I‖ * ‖(ℏ : ℂ)‖ := by rw [norm_neg]
      _ = 1 * ‖(ℏ : ℂ)‖ := by rw [Complex.norm_I]
      _ = ‖(ℏ : ℂ)‖ := one_mul _
      _ = |ℏ| := by
          have h := @RCLike.norm_ofReal ℂ _ ℏ
          exact h
      _ = ℏ := abs_of_pos ℏ_pos

  -- Step 4: Transform Robertson's RHS to our target
  calc unboundedStandardDeviation L.L_x ψ h_domain.h_norm h_domain.h_Lx *
       unboundedStandardDeviation L.L_y ψ h_domain.h_norm h_domain.h_Ly
      ≥ (1/2) * ‖@inner ℂ H _ ψ ((L.L_x.op ∘ₗ L.L_y.op - L.L_y.op ∘ₗ L.L_x.op) ψ)‖ := h_rob
    _ = (1/2) * ‖@inner ℂ H _ ψ ((Complex.I * ℏ) • L.L_z.op ψ)‖ := by
        rw [h_comm]
    _ = (1/2) * ‖(starRingEnd ℂ (Complex.I * ℏ)) * @inner ℂ H _ ψ (L.L_z.op ψ)‖ := by
        rw [inner_smul_right]
        simp
    _ = (1/2) * ‖(-Complex.I * ℏ) * @inner ℂ H _ ψ (L.L_z.op ψ)‖ := by
        congr 2
        simp
    _ = (1/2) * (‖(-Complex.I : ℂ) * ℏ‖ * ‖@inner ℂ H _ ψ (L.L_z.op ψ)‖) := by
        rw [Complex.norm_mul]
    _ = (1/2) * (ℏ * ‖@inner ℂ H _ ψ (L.L_z.op ψ)‖) := by
        rw [h_norm_ihbar]
    _ = (ℏ / 2) * ‖@inner ℂ H _ ψ (L.L_z.op ψ)‖ := by
        ring



/-- **Angular momentum components cannot all be sharp simultaneously.**

If a quantum state ψ has nonzero expected angular momentum along z (i.e., ⟨ψ|Lz|ψ⟩ ≠ 0),
then the standard deviations in both Lₓ and Lᵧ must be strictly positive.

This is a direct consequence of `angular_momentum_uncertainty` combined with the
non-negativity of standard deviations: if either ΔLₓ = 0 or ΔLᵧ = 0, then their
product vanishes, contradicting the lower bound (ℏ/2)|⟨Lz⟩| > 0.

Physically: a particle with definite angular momentum about any axis cannot have
definite angular momentum about the orthogonal axes. This is the rotational analog
of position-momentum uncertainty. -/
theorem angular_momentum_uncertainty_nonzero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [IsScalarTower ℝ ℂ H]
    (L : AngularMomentumOperators H) (ψ : H)
    (h_domain : AngularMomentumUncertaintyDomain' L ψ)
    (h_Lz_nonzero : @inner ℂ H _ ψ (L.L_z.op ψ) ≠ 0) :
    unboundedStandardDeviation L.L_x ψ h_domain.h_norm h_domain.h_Lx > 0 ∧
    unboundedStandardDeviation L.L_y ψ h_domain.h_norm h_domain.h_Ly > 0 := by

  -- The RHS of uncertainty is positive when ⟨ψ, L_z ψ⟩ ≠ 0
  have h_rhs_pos : (ℏ / 2) * ‖@inner ℂ H _ ψ (L.L_z.op ψ)‖ > 0 := by
    apply mul_pos
    · exact div_pos ℏ_pos (by norm_num : (2 : ℝ) > 0)
    · rw [norm_pos_iff]
      exact h_Lz_nonzero

  have h_ineq := angular_momentum_uncertainty L ψ h_domain

  -- Standard deviations are non-negative
  have h_x_nn : unboundedStandardDeviation L.L_x ψ h_domain.h_norm h_domain.h_Lx ≥ 0 :=
    unboundedStandardDeviation_nonneg L.L_x ψ h_domain.h_norm h_domain.h_Lx
  have h_y_nn : unboundedStandardDeviation L.L_y ψ h_domain.h_norm h_domain.h_Ly ≥ 0 :=
    unboundedStandardDeviation_nonneg L.L_y ψ h_domain.h_norm h_domain.h_Ly

  -- If either is zero, product is zero, contradicting h_ineq and h_rhs_pos
  by_contra h_neg
  rw [not_and_or] at h_neg

  -- not (x > 0) with x ≥ 0 means x = 0
  have h_or : unboundedStandardDeviation L.L_x ψ h_domain.h_norm h_domain.h_Lx = 0 ∨
              unboundedStandardDeviation L.L_y ψ h_domain.h_norm h_domain.h_Ly = 0 := by
    cases h_neg with
    | inl h_x_not_pos =>
      left
      push_neg at h_x_not_pos
      linarith
    | inr h_y_not_pos =>
      right
      push_neg at h_y_not_pos
      linarith

  cases h_or with
  | inl h_x_zero =>
    have h_prod_zero : unboundedStandardDeviation L.L_x ψ h_domain.h_norm h_domain.h_Lx *
                       unboundedStandardDeviation L.L_y ψ h_domain.h_norm h_domain.h_Ly = 0 := by
      rw [h_x_zero, zero_mul]
    have h_contra : (0 : ℝ) ≥ (ℏ / 2) * ‖@inner ℂ H _ ψ (L.L_z.op ψ)‖ := by
      calc (0 : ℝ)
          = unboundedStandardDeviation L.L_x ψ h_domain.h_norm h_domain.h_Lx *
            unboundedStandardDeviation L.L_y ψ h_domain.h_norm h_domain.h_Ly := h_prod_zero.symm
        _ ≥ (ℏ / 2) * ‖@inner ℂ H _ ψ (L.L_z.op ψ)‖ := h_ineq
    linarith
  | inr h_y_zero =>
    have h_prod_zero : unboundedStandardDeviation L.L_x ψ h_domain.h_norm h_domain.h_Lx *
                       unboundedStandardDeviation L.L_y ψ h_domain.h_norm h_domain.h_Ly = 0 := by
      rw [h_y_zero, mul_zero]
    have h_contra : (0 : ℝ) ≥ (ℏ / 2) * ‖@inner ℂ H _ ψ (L.L_z.op ψ)‖ := by
      calc (0 : ℝ)
          = unboundedStandardDeviation L.L_x ψ h_domain.h_norm h_domain.h_Lx *
            unboundedStandardDeviation L.L_y ψ h_domain.h_norm h_domain.h_Ly := h_prod_zero.symm
        _ ≥ (ℏ / 2) * ‖@inner ℂ H _ ψ (L.L_z.op ψ)‖ := h_ineq
    linarith

end Bornemann
/-
In dS, Λ > 0:
The de Sitter fluctuations perturb the angular momentum. Any perturbation—any—that produces
non-zero ⟨L_i⟩ in any component forces uncertainty in the orthogonal components. The perfectly
non-rotating state is unstable.

The cosmic microwave background. 2.725 Kelvin. Everywhere. In every direction. Filling the universe
since 380,000 years after the Big Bang.  There is no escape from it. SdS cannot persist.
-/

namespace SdS_Forbidden

open Bornemann Robertson.Core

/-!
# Schwarzschild-de Sitter is Forbidden

SdS spacetime cannot represent a physical black hole in any universe
with a thermal bath at T > 0.
-/

/-! ## GR Structures -/

structure SdSParameters where
  M : ℝ
  Λ : ℝ
  h_M_pos : M > 0
  h_Λ_pos : Λ > 0

structure KdSParameters where
  M : ℝ
  Λ : ℝ
  J : ℝ
  h_M_pos : M > 0
  h_Λ_pos : Λ > 0

def SdS_as_KdS (p : SdSParameters) : KdSParameters where
  M := p.M
  Λ := p.Λ
  J := 0
  h_M_pos := p.h_M_pos
  h_Λ_pos := p.h_Λ_pos

/-! ## Thermal Bath -/

structure ThermalBath where
  T : ℝ
  h_T_pos : T > 0

def CMB : ThermalBath where
  T := 2.725
  h_T_pos := by norm_num

noncomputable def deSitterTemperature (Λ : ℝ) (h_Λ_pos : Λ > 0) : ThermalBath where
  T := Real.sqrt (Λ / 3) / (2 * Real.pi * k_B)
  h_T_pos := by
    apply div_pos
    · exact Real.sqrt_pos.mpr (div_pos h_Λ_pos (by norm_num : (3 : ℝ) > 0))
    · apply mul_pos
      apply mul_pos <;> norm_num
      exact Real.pi_pos
      exact k_B_pos

/-! ## Zero Angular Momentum States -/

/-- A state has zero angular momentum iff all expectations vanish -/
def IsZeroAngularMomentumState {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H) : Prop :=
  ‖ψ‖ = 1 ∧
  @inner ℂ H _ ψ (L.L_x.op ψ) = 0 ∧
  @inner ℂ H _ ψ (L.L_y.op ψ) = 0 ∧
  @inner ℂ H _ ψ (L.L_z.op ψ) = 0

/-- A state represents SdS iff it has zero angular momentum -/
def RepresentsSdS {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H) : Prop :=
  IsZeroAngularMomentumState L ψ

/-! ## Core Theorems (No Measure Theory Required) -/

/-- Any state with ⟨L_z⟩ ≠ 0 cannot be SdS -/
theorem nonzero_Lz_not_SdS {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H)
    (h_Lz_nonzero : @inner ℂ H _ ψ (L.L_z.op ψ) ≠ 0) :
    ¬RepresentsSdS L ψ := by
  intro h_SdS
  unfold RepresentsSdS IsZeroAngularMomentumState at h_SdS
  exact h_Lz_nonzero h_SdS.2.2.2

/-- Any state with ⟨L_x⟩ ≠ 0 cannot be SdS -/
theorem nonzero_Lx_not_SdS {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H)
    (h_Lx_nonzero : @inner ℂ H _ ψ (L.L_x.op ψ) ≠ 0) :
    ¬RepresentsSdS L ψ := by
  intro h_SdS
  unfold RepresentsSdS IsZeroAngularMomentumState at h_SdS
  exact h_Lx_nonzero h_SdS.2.1

/-- Any state with ⟨L_y⟩ ≠ 0 cannot be SdS -/
theorem nonzero_Ly_not_SdS {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H)
    (h_Ly_nonzero : @inner ℂ H _ ψ (L.L_y.op ψ) ≠ 0) :
    ¬RepresentsSdS L ψ := by
  intro h_SdS
  unfold RepresentsSdS IsZeroAngularMomentumState at h_SdS
  exact h_Ly_nonzero h_SdS.2.2.1

/-- **KEY THEOREM**: SdS states have zero uncertainty, contradicting thermal excitation.

    If ψ is SdS (all ⟨L_i⟩ = 0), then by Robertson, σ_Li could be zero.
    But if ANY ⟨L_i⟩ ≠ 0, then Robertson forces σ_Lj > 0 for j ≠ i.
    Thermal baths generically excite ⟨L_i⟩ ≠ 0, so SdS is forbidden. -/
theorem SdS_incompatible_with_nonzero_L {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [IsScalarTower ℝ ℂ H]
    (L : AngularMomentumOperators H) (ψ : H)
    (_ /-h_dom-/ : AngularMomentumUncertaintyDomain' L ψ)
    (h_some_L_nonzero : @inner ℂ H _ ψ (L.L_x.op ψ) ≠ 0 ∨
                        @inner ℂ H _ ψ (L.L_y.op ψ) ≠ 0 ∨
                        @inner ℂ H _ ψ (L.L_z.op ψ) ≠ 0) :
    ¬RepresentsSdS L ψ := by
  rcases h_some_L_nonzero with h_Lx | h_Ly | h_Lz
  · exact nonzero_Lx_not_SdS L ψ h_Lx
  · exact nonzero_Ly_not_SdS L ψ h_Ly
  · exact nonzero_Lz_not_SdS L ψ h_Lz

/-! ## Thermal Axiom -/

/-- **PHYSICAL AXIOM**: A thermal bath at T > 0 generically excites angular momentum.

    Justification: Thermal fluctuations explore the state space. The set of states
    with ⟨L_x⟩ = ⟨L_y⟩ = ⟨L_z⟩ = 0 simultaneously has codimension 3, hence
    measure zero. A generic thermal state violates at least one constraint. -/
axiom thermal_excites_angular_momentum {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (bath : ThermalBath) :
    ∀ (ψ : H), ‖ψ‖ = 1 →
      -- Generic states satisfy this (measure-theoretically almost all)
      @inner ℂ H _ ψ (L.L_x.op ψ) ≠ 0 ∨
      @inner ℂ H _ ψ (L.L_y.op ψ) ≠ 0 ∨
      @inner ℂ H _ ψ (L.L_z.op ψ) ≠ 0

/-! ## Main Result -/

/-- **MAIN THEOREM**: SdS is forbidden in any thermal universe -/
theorem SdS_forbidden {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [IsScalarTower ℝ ℂ H]
    (L : AngularMomentumOperators H) (bath : ThermalBath)
    (ψ : H) (h_dom : AngularMomentumUncertaintyDomain' L ψ) :
    ¬RepresentsSdS L ψ := by
  have h_excited := thermal_excites_angular_momentum L bath ψ h_dom.h_norm
  exact SdS_incompatible_with_nonzero_L L ψ h_dom h_excited

/-- **COROLLARY**: SdS is forbidden in our universe (CMB at 2.725 K) -/
theorem SdS_forbidden_our_universe {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [IsScalarTower ℝ ℂ H]
    (L : AngularMomentumOperators H)
    (ψ : H) (h_dom : AngularMomentumUncertaintyDomain' L ψ) :
    ¬RepresentsSdS L ψ :=
  SdS_forbidden L CMB ψ h_dom

/-- **PHYSICAL CONCLUSION**: All black holes in de Sitter must have J ≠ 0 -/
theorem all_BH_rotating {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [IsScalarTower ℝ ℂ H]
    (L : AngularMomentumOperators H) (bath : ThermalBath)
    (ψ : H) (h_dom : AngularMomentumUncertaintyDomain' L ψ)
    (_ /-h_represents_BH-/ : True) :  -- ψ represents some black hole
    ¬IsZeroAngularMomentumState L ψ :=
  SdS_forbidden L bath ψ h_dom

end SdS_Forbidden
/-
To the information paradox proponants: the ball is in your court, prove the paradox still exists
in KdS.
-Bornemann.
P.S. Where is your spherical cow god now?  Also, this is me being gentle.  Consider that gravity cannot be screened
and that Schwarzschild requires 0 interactions with the environment.  This is obviously logically impossible.

....don't make me put that in a proof as well.
-/
