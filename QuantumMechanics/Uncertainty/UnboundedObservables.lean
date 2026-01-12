/-
================================================================================
UNBOUNDED OBSERVABLES — FOUNDATIONS
================================================================================

Author: Adam Bornemann

This module provides the correct type-theoretic foundation for unbounded
operators in quantum mechanics. The key insight is that unbounded operators
are genuinely partial functions — they're only defined on dense subspaces.

The type system enforces this: you cannot apply an operator without proving
your vector is in the domain.

-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Complex.Basic

namespace QuantumMechanics
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open InnerProductSpace
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-============================================================================
  SECTION 1: THE UNBOUNDED OBSERVABLE STRUCTURE
============================================================================-/

/--
An unbounded symmetric operator on a Hilbert space.

This correctly models operators like position and momentum:
- `domain`: A dense submodule where the operator is defined
- `toFun`: The operator itself, only defined on domain elements
- `dense`: The domain is dense in H (physical requirement)
- `symmetric`: ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩ for all ψ, φ in domain

Note: Symmetric ≠ Self-adjoint for unbounded operators!
Robertson's inequality only requires symmetry.
-/
structure UnboundedObservable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The domain: a dense submodule of H -/
  domain : Submodule ℂ H
  /-- The operator: a linear map from domain to H -/
  toFun : domain →ₗ[ℂ] H
  /-- Physical requirement: domain is dense -/
  dense : Dense (domain : Set H)
  /-- Symmetry: ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩ -/
  symmetric : ∀ ψ φ : domain, ⟪toFun ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), toFun φ⟫_ℂ

namespace UnboundedObservable

/-============================================================================
  SECTION 2: BASIC API AND NOTATION
============================================================================-/

/-- Apply the operator to a vector with explicit domain membership proof -/
@[inline]
def apply (A : UnboundedObservable H) (ψ : H) (hψ : ψ ∈ A.domain) : H :=
  A.toFun ⟨ψ, hψ⟩

/-- Notation for operator application: A ⬝ ψ ⊢ hψ -/
notation:max A " ⬝ " ψ " ⊢ " hψ => UnboundedObservable.apply A ψ hψ

/-- Coercion: use A directly as a function on domain elements -/
instance : CoeFun (UnboundedObservable H) (fun A => A.domain → H) where
  coe A := A.toFun

/-- Construct a domain element -/
@[inline]
def toDomainElt (A : UnboundedObservable H) (ψ : H) (hψ : ψ ∈ A.domain) : A.domain :=
  ⟨ψ, hψ⟩

/-============================================================================
  SECTION 3: SYMMETRY LEMMAS
============================================================================-/

/-- Symmetry with explicit membership proofs (main interface) -/
theorem symmetric' (A : UnboundedObservable H) {ψ φ : H}
    (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) :
    ⟪A ⬝ ψ ⊢ hψ, φ⟫_ℂ = ⟪ψ, A ⬝ φ ⊢ hφ⟫_ℂ :=
  A.symmetric ⟨ψ, hψ⟩ ⟨φ, hφ⟩

/-- Expectation values of symmetric operators are real -/
theorem inner_self_im_eq_zero (A : UnboundedObservable H) {ψ : H} (hψ : ψ ∈ A.domain) :
    (⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ).im = 0 := by
  have h := A.symmetric' hψ hψ
  rw [← inner_conj_symm] at h
  have := congr_arg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-- Expectation value equals its real part (as a complex number) -/
theorem inner_self_eq_re (A : UnboundedObservable H) {ψ : H} (hψ : ψ ∈ A.domain) :
    ⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ = (⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ).re := by
  simp [Complex.ext_iff, A.inner_self_im_eq_zero hψ]

/-============================================================================
  SECTION 4: LINEARITY LEMMAS
============================================================================-/


theorem apply_add (A : UnboundedObservable H) {ψ φ : H}
    (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) :
    A.apply (ψ + φ) (A.domain.add_mem hψ hφ) = A.apply ψ hψ + A.apply φ hφ :=
  A.toFun.map_add ⟨ψ, hψ⟩ ⟨φ, hφ⟩

theorem apply_smul (A : UnboundedObservable H) {ψ : H} (c : ℂ) (hψ : ψ ∈ A.domain) :
    A.apply (c • ψ) (A.domain.smul_mem c hψ) = c • A.apply ψ hψ :=
  A.toFun.map_smul c ⟨ψ, hψ⟩

theorem apply_sub (A : UnboundedObservable H) {ψ φ : H}
    (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) :
    A.apply (ψ - φ) (A.domain.sub_mem hψ hφ) = A.apply ψ hψ - A.apply φ hφ :=
  A.toFun.map_sub ⟨ψ, hψ⟩ ⟨φ, hφ⟩

theorem apply_smul_real (A : UnboundedObservable H) {ψ : H} (r : ℝ) (hψ : ψ ∈ A.domain) :
    A.apply ((r : ℂ) • ψ) (A.domain.smul_mem (r : ℂ) hψ) = (r : ℂ) • A.apply ψ hψ :=
  apply_smul A (r : ℂ) hψ

/-============================================================================
  SECTION 5: COMPOSITION AND DOMAIN CONDITIONS
============================================================================-/

/--
Bundled domain conditions for applying the commutator [A,B] to ψ.

To compute [A,B]ψ = ABψ - BAψ, we need:
- ψ ∈ Dom(A) ∩ Dom(B)
- Bψ ∈ Dom(A)
- Aψ ∈ Dom(B)
-/
structure DomainConditions (A B : UnboundedObservable H) (ψ : H) where
  hψ_A : ψ ∈ A.domain
  hψ_B : ψ ∈ B.domain
  hBψ_A : B.apply ψ hψ_B ∈ A.domain
  hAψ_B : A.apply ψ hψ_A ∈ B.domain

namespace DomainConditions

variable {A B : UnboundedObservable H} {ψ : H}

/-- Convenience: extract A application -/
def Aψ (h : DomainConditions A B ψ) : H := A ⬝ ψ ⊢ h.hψ_A

/-- Convenience: extract B application -/
def Bψ (h : DomainConditions A B ψ) : H := B ⬝ ψ ⊢ h.hψ_B

/-- Convenience: extract AB application -/
def ABψ (h : DomainConditions A B ψ) : H := A ⬝ (B ⬝ ψ ⊢ h.hψ_B) ⊢ h.hBψ_A

/-- Convenience: extract BA application -/
def BAψ (h : DomainConditions A B ψ) : H := B ⬝ (A ⬝ ψ ⊢ h.hψ_A) ⊢ h.hAψ_B

end DomainConditions

/-- Commutator applied to ψ: [A,B]ψ = ABψ - BAψ -/
def commutatorAt (A B : UnboundedObservable H) (ψ : H) (h : DomainConditions A B ψ) : H :=
  h.ABψ - h.BAψ

/-- Anticommutator applied to ψ: {A,B}ψ = ABψ + BAψ -/
def anticommutatorAt (A B : UnboundedObservable H) (ψ : H) (h : DomainConditions A B ψ) : H :=
  h.ABψ + h.BAψ

/-============================================================================
  SECTION 6: COMMUTATOR AND ANTICOMMUTATOR PROPERTIES
============================================================================-/

/-- The commutator expectation ⟨ψ, [A,B]ψ⟩ is purely imaginary -/
theorem commutator_re_eq_zero (A B : UnboundedObservable H) (ψ : H)
    (h : DomainConditions A B ψ) :
    (⟪ψ, commutatorAt A B ψ h⟫_ℂ).re = 0 := by
  unfold commutatorAt DomainConditions.ABψ DomainConditions.BAψ
  simp only [inner_sub_right]
  -- Use symmetry: ⟨ψ, ABψ⟩ = ⟨Aψ, Bψ⟩ and ⟨ψ, BAψ⟩ = ⟨Bψ, Aψ⟩
  have h1 : ⟪ψ, A ⬝ (B ⬝ ψ ⊢ h.hψ_B) ⊢ h.hBψ_A⟫_ℂ =
            ⟪A ⬝ ψ ⊢ h.hψ_A, B ⬝ ψ ⊢ h.hψ_B⟫_ℂ := by
    exact Eq.symm (symmetric' A h.hψ_A h.hBψ_A)
  have h2 : ⟪ψ, B ⬝ (A ⬝ ψ ⊢ h.hψ_A) ⊢ h.hAψ_B⟫_ℂ =
            ⟪B ⬝ ψ ⊢ h.hψ_B, A ⬝ ψ ⊢ h.hψ_A⟫_ℂ := by
    exact Eq.symm (symmetric' B h.hψ_B h.hAψ_B)
  rw [h1, h2, ← inner_conj_symm (B ⬝ ψ ⊢ h.hψ_B) (A ⬝ ψ ⊢ h.hψ_A)]
  simp only [Complex.sub_re, Complex.conj_re]
  ring

/-- The anticommutator expectation ⟨ψ, {A,B}ψ⟩ is purely real -/
theorem anticommutator_im_eq_zero (A B : UnboundedObservable H) (ψ : H)
    (h : DomainConditions A B ψ) :
    (⟪ψ, anticommutatorAt A B ψ h⟫_ℂ).im = 0 := by
  unfold anticommutatorAt DomainConditions.ABψ DomainConditions.BAψ
  simp only [inner_add_right]
  have h1 : ⟪ψ, A ⬝ (B ⬝ ψ ⊢ h.hψ_B) ⊢ h.hBψ_A⟫_ℂ =
            ⟪A ⬝ ψ ⊢ h.hψ_A, B ⬝ ψ ⊢ h.hψ_B⟫_ℂ := by
    exact Eq.symm (symmetric' A h.hψ_A h.hBψ_A)
  have h2 : ⟪ψ, B ⬝ (A ⬝ ψ ⊢ h.hψ_A) ⊢ h.hAψ_B⟫_ℂ =
            ⟪B ⬝ ψ ⊢ h.hψ_B, A ⬝ ψ ⊢ h.hψ_A⟫_ℂ := by
    exact Eq.symm (symmetric' B h.hψ_B h.hAψ_B)
  rw [h1, h2, ← inner_conj_symm (B ⬝ ψ ⊢ h.hψ_B) (A ⬝ ψ ⊢ h.hψ_A)]
  simp only [Complex.add_im, Complex.conj_im]
  ring

/-============================================================================
  SECTION 7: STATISTICAL QUANTITIES
============================================================================-/

/-- Expectation value: ⟨A⟩_ψ = Re⟨ψ, Aψ⟩ -/
noncomputable def expectation (A : UnboundedObservable H) (ψ : H)
    (_ : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : ℝ :=
  (⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ).re

/-- Shifted operator Ã = A - ⟨A⟩I applied to ψ -/
noncomputable def shiftedApply (A : UnboundedObservable H) (ψ : H) (φ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) : H :=
  (A ⬝ φ ⊢ hφ) - (A.expectation ψ h_norm hψ : ℂ) • φ

/-- The shifted operator Ã preserves symmetry -/
theorem shifted_symmetric (A : UnboundedObservable H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ_dom : ψ ∈ A.domain)
    {φ₁ φ₂ : H} (hφ₁ : φ₁ ∈ A.domain) (hφ₂ : φ₂ ∈ A.domain) :
    ⟪A.shiftedApply ψ φ₁ h_norm hψ_dom hφ₁, φ₂⟫_ℂ =
    ⟪φ₁, A.shiftedApply ψ φ₂ h_norm hψ_dom hφ₂⟫_ℂ := by
  unfold shiftedApply
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  rw [A.symmetric' hφ₁ hφ₂]
  simp only [Complex.conj_ofReal]

/-- Variance: Var(A)_ψ = ‖Ãψ‖² where Ã = A - ⟨A⟩I -/
noncomputable def variance (A : UnboundedObservable H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : ℝ :=
  ‖A.shiftedApply ψ ψ h_norm hψ hψ‖^2

/-- Standard deviation: σ_A = √Var(A) -/
noncomputable def stdDev (A : UnboundedObservable H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : ℝ :=
  Real.sqrt (A.variance ψ h_norm hψ)

/-- Variance is non-negative -/
theorem variance_nonneg (A : UnboundedObservable H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) :
    0 ≤ A.variance ψ h_norm hψ :=
  sq_nonneg _

/-- Standard deviation is non-negative -/
theorem stdDev_nonneg (A : UnboundedObservable H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) :
    0 ≤ A.stdDev ψ h_norm hψ :=
  Real.sqrt_nonneg _

end UnboundedObservable

end QuantumMechanics
