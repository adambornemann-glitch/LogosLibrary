/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Complex.Basic
/-!
# Unbounded Observables

This module provides the type-theoretic foundation for unbounded self-adjoint
operators in quantum mechanics. The key design decision is that unbounded
operators are modeled as genuinely partial functions: the type system enforces
that you cannot apply an operator without proving membership in its domain.

## Main definitions

* `UnboundedObservable`: A symmetric operator with dense domain
* `DomainConditions`: Bundled proof that [A,B]ψ is well-defined
* `commutatorAt`: The commutator [A,B]ψ = ABψ - BAψ
* `anticommutatorAt`: The anticommutator {A,B}ψ = ABψ + BAψ
* `expectation`: ⟨A⟩_ψ = Re⟨ψ, Aψ⟩
* `variance`: Var(A)_ψ = ‖(A - ⟨A⟩)ψ‖²
* `stdDev`: σ_A = √Var(A)

## Main results

* `symmetric'`: ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩ for ψ, φ in the domain
* `inner_self_im_eq_zero`: Expectation values are real
* `commutator_re_eq_zero`: ⟨ψ, [A,B]ψ⟩ is purely imaginary
* `anticommutator_im_eq_zero`: ⟨ψ, {A,B}ψ⟩ is purely real
* `shifted_symmetric`: The shifted operator A - ⟨A⟩I is symmetric

## Design notes

We use `Submodule ℂ H` for domains rather than bare sets, ensuring closure
under linear combinations. The notation `A ⬝ ψ ⊢ hψ` makes domain proofs
explicit at the call site.

Note that symmetric ≠ self-adjoint for unbounded operators. Self-adjointness
requires additionally that Dom(A) = Dom(A*). This module only assumes symmetry,
which suffices for Robertson's uncertainty inequality.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII
* [Hall, *Quantum Theory for Mathematicians*][hall2013], Chapter 9

## Tags

unbounded operator, symmetric operator, observable, commutator, uncertainty
-/
namespace QuantumMechanics
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open InnerProductSpace
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure UnboundedObservable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  domain : Submodule ℂ H
  toFun : domain →ₗ[ℂ] H
  dense : Dense (domain : Set H)
  symmetric : ∀ ψ φ : domain, ⟪toFun ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), toFun φ⟫_ℂ

namespace UnboundedObservable



@[inline]
def apply (A : UnboundedObservable H) (ψ : H) (hψ : ψ ∈ A.domain) : H :=
  A.toFun ⟨ψ, hψ⟩


notation:max A " ⬝ " ψ " ⊢ " hψ => UnboundedObservable.apply A ψ hψ


instance : CoeFun (UnboundedObservable H) (fun A => A.domain → H) where
  coe A := A.toFun

@[inline]
def toDomainElt (A : UnboundedObservable H) (ψ : H) (hψ : ψ ∈ A.domain) : A.domain :=
  ⟨ψ, hψ⟩

theorem symmetric' (A : UnboundedObservable H) {ψ φ : H}
    (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) :
    ⟪A ⬝ ψ ⊢ hψ, φ⟫_ℂ = ⟪ψ, A ⬝ φ ⊢ hφ⟫_ℂ :=
  A.symmetric ⟨ψ, hψ⟩ ⟨φ, hφ⟩

theorem inner_self_im_eq_zero (A : UnboundedObservable H) {ψ : H} (hψ : ψ ∈ A.domain) :
    (⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ).im = 0 := by
  have h := A.symmetric' hψ hψ
  rw [← inner_conj_symm] at h
  have := congr_arg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

theorem inner_self_eq_re (A : UnboundedObservable H) {ψ : H} (hψ : ψ ∈ A.domain) :
    ⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ = (⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ).re := by
  simp [Complex.ext_iff, A.inner_self_im_eq_zero hψ]


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


structure DomainConditions (A B : UnboundedObservable H) (ψ : H) where
  hψ_A : ψ ∈ A.domain
  hψ_B : ψ ∈ B.domain
  hBψ_A : B.apply ψ hψ_B ∈ A.domain
  hAψ_B : A.apply ψ hψ_A ∈ B.domain

namespace DomainConditions

variable {A B : UnboundedObservable H} {ψ : H}

def Aψ (h : DomainConditions A B ψ) : H := A ⬝ ψ ⊢ h.hψ_A

def Bψ (h : DomainConditions A B ψ) : H := B ⬝ ψ ⊢ h.hψ_B

def ABψ (h : DomainConditions A B ψ) : H := A ⬝ (B ⬝ ψ ⊢ h.hψ_B) ⊢ h.hBψ_A

def BAψ (h : DomainConditions A B ψ) : H := B ⬝ (A ⬝ ψ ⊢ h.hψ_A) ⊢ h.hAψ_B

end DomainConditions


def commutatorAt (A B : UnboundedObservable H) (ψ : H) (h : DomainConditions A B ψ) : H :=
  h.ABψ - h.BAψ


def anticommutatorAt (A B : UnboundedObservable H) (ψ : H) (h : DomainConditions A B ψ) : H :=
  h.ABψ + h.BAψ

theorem commutator_re_eq_zero (A B : UnboundedObservable H) (ψ : H)
    (h : DomainConditions A B ψ) :
    (⟪ψ, commutatorAt A B ψ h⟫_ℂ).re = 0 := by
  unfold commutatorAt DomainConditions.ABψ DomainConditions.BAψ
  simp only [inner_sub_right]
  have h1 : ⟪ψ, A ⬝ (B ⬝ ψ ⊢ h.hψ_B) ⊢ h.hBψ_A⟫_ℂ =
            ⟪A ⬝ ψ ⊢ h.hψ_A, B ⬝ ψ ⊢ h.hψ_B⟫_ℂ := by
    exact Eq.symm (symmetric' A h.hψ_A h.hBψ_A)
  have h2 : ⟪ψ, B ⬝ (A ⬝ ψ ⊢ h.hψ_A) ⊢ h.hAψ_B⟫_ℂ =
            ⟪B ⬝ ψ ⊢ h.hψ_B, A ⬝ ψ ⊢ h.hψ_A⟫_ℂ := by
    exact Eq.symm (symmetric' B h.hψ_B h.hAψ_B)
  rw [h1, h2, ← inner_conj_symm (B ⬝ ψ ⊢ h.hψ_B) (A ⬝ ψ ⊢ h.hψ_A)]
  simp only [Complex.sub_re, Complex.conj_re]
  ring


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


noncomputable def expectation (A : UnboundedObservable H) (ψ : H)
    (_ : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : ℝ :=
  (⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ).re


noncomputable def shiftedApply (A : UnboundedObservable H) (ψ : H) (φ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) : H :=
  (A ⬝ φ ⊢ hφ) - (A.expectation ψ h_norm hψ : ℂ) • φ


theorem shifted_symmetric (A : UnboundedObservable H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ_dom : ψ ∈ A.domain)
    {φ₁ φ₂ : H} (hφ₁ : φ₁ ∈ A.domain) (hφ₂ : φ₂ ∈ A.domain) :
    ⟪A.shiftedApply ψ φ₁ h_norm hψ_dom hφ₁, φ₂⟫_ℂ =
    ⟪φ₁, A.shiftedApply ψ φ₂ h_norm hψ_dom hφ₂⟫_ℂ := by
  unfold shiftedApply
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  rw [A.symmetric' hφ₁ hφ₂]
  simp only [Complex.conj_ofReal]


noncomputable def variance (A : UnboundedObservable H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : ℝ :=
  ‖A.shiftedApply ψ ψ h_norm hψ hψ‖^2


noncomputable def stdDev (A : UnboundedObservable H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : ℝ :=
  Real.sqrt (A.variance ψ h_norm hψ)


theorem variance_nonneg (A : UnboundedObservable H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) :
    0 ≤ A.variance ψ h_norm hψ :=
  sq_nonneg _


theorem stdDev_nonneg (A : UnboundedObservable H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) :
    0 ≤ A.stdDev ψ h_norm hψ :=
  Real.sqrt_nonneg _

end UnboundedObservable

end QuantumMechanics
