/-
Author: Adam Bornemann
Created: 11/5/2025
Updated: 11/16/2025

================================================================================
WOBBLE'S THEOREM OF FORBIDDEN SDS
================================================================================

**References:**
- Heisenberg, W. (1927). "Über den anschaulichen Inhalt der quantentheoretischen
  Kinematik und Mechanik". Z. Physik 43, 172-198.
- Kennard, E.H. (1927). "Zur Quantenmechanik einfacher Bewegungstypen".
  Z. Physik 44, 326-352. (First rigorous proof of σₓσₚ ≥ ℏ/2)
- Robertson, H.P. (1929). "The Uncertainty Principle". Phys. Rev. 34, 163-164.
- von Wobble-Bob, Dr. Baron (2025) This very proof.

Note: Is this just a standard equation that falls out of Robertson?  Absolutely.
But I don't see any of you formalizing it and using it to kill Schwarzschild in dS,
so, respectfully- please let me have this?  ^_^.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum.Prime  -- for extended norm_num
import Mathlib.Tactic.Polyrith
import LogosLibrary.Relativity.Thermodynamics.ConnesRovelli
import LogosLibrary.QuantumMechanics.Uncertainty.Schrodinger -- For unbounded operators
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open QuantumMechanics.Schrodinger QuantumMechanics.Robertson QuantumMechanics.UnboundedObservable InnerProductSpace Complex

namespace QuantumMechanics.ForbiddenSdS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H][CompleteSpace H]
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

noncomputable def k_B : ℝ := 1

theorem k_B_pos : k_B > 0 := by unfold k_B; norm_num

/-- For symmetric operators, expectation is real (conjugate equals self) -/
theorem unboundedExpectation_conj_eq_self {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) (hψ : ψ ∈ A.domain) :
    starRingEnd ℂ ⟪ψ, A.apply ψ hψ⟫_ℂ = ⟪ψ, A.apply ψ hψ⟫_ℂ := by
  rw [inner_conj_symm]
  exact A.symmetric' hψ hψ

/-- Extract the real part of expectation -/
noncomputable def unboundedExpectationReal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) (hψ : ψ ∈ A.domain) : ℝ :=
  (⟪ψ, A.apply ψ hψ⟫_ℂ).re

/-- Variance of an unbounded observable: Var(A) = ‖Aψ‖² - ⟨A⟩² -/
noncomputable def unboundedVariance {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) (hψ : ψ ∈ A.domain) : ℝ :=
  ‖A.apply ψ hψ‖^2 - (⟪ψ, A.apply ψ hψ⟫_ℂ).re^2

/-- Standard deviation: σ_A = √Var(A) -/
noncomputable def unboundedStandardDeviation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) (hψ : ψ ∈ A.domain) : ℝ :=
  Real.sqrt (unboundedVariance A ψ hψ)

/-- Standard deviation is non-negative -/
theorem unboundedStandardDeviation_nonneg {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedObservable H) (ψ : H) (hψ : ψ ∈ A.domain) :
    unboundedStandardDeviation A ψ hψ ≥ 0 := by
  unfold unboundedStandardDeviation
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
  Lx_stable : ∀ ψ : H, (hψ : ψ ∈ common_domain) →
    L_x.apply ψ (common_in_Lx ψ hψ) ∈ common_domain

  /-- L_y preserves the common domain -/
  Ly_stable : ∀ ψ : H, (hψ : ψ ∈ common_domain) →
    L_y.apply ψ (common_in_Ly ψ hψ) ∈ common_domain

  /-- L_z preserves the common domain -/
  Lz_stable : ∀ ψ : H, (hψ : ψ ∈ common_domain) →
    L_z.apply ψ (common_in_Lz ψ hψ) ∈ common_domain

  /-- Canonical commutation: [L_x, L_y] = iℏL_z -/
  commutation_xy : ∀ ψ : H, (hψ : ψ ∈ common_domain) →
    let hψ_x := common_in_Lx ψ hψ
    let hψ_y := common_in_Ly ψ hψ
    let hψ_z := common_in_Lz ψ hψ
    let hLyψ_x := common_in_Lx _ (Ly_stable ψ hψ)
    let hLxψ_y := common_in_Ly _ (Lx_stable ψ hψ)
    L_x.apply (L_y.apply ψ hψ_y) hLyψ_x - L_y.apply (L_x.apply ψ hψ_x) hLxψ_y =
      (Complex.I * (ℏ : ℂ)) • L_z.apply ψ hψ_z

  /-- Canonical commutation: [L_y, L_z] = iℏL_x -/
  commutation_yz : ∀ ψ : H, (hψ : ψ ∈ common_domain) →
    let hψ_x := common_in_Lx ψ hψ
    let hψ_y := common_in_Ly ψ hψ
    let hψ_z := common_in_Lz ψ hψ
    let hLzψ_y := common_in_Ly _ (Lz_stable ψ hψ)
    let hLyψ_z := common_in_Lz _ (Ly_stable ψ hψ)
    L_y.apply (L_z.apply ψ hψ_z) hLzψ_y - L_z.apply (L_y.apply ψ hψ_y) hLyψ_z =
      (Complex.I * (ℏ : ℂ)) • L_x.apply ψ hψ_x

  /-- Canonical commutation: [L_z, L_x] = iℏL_y -/
  commutation_zx : ∀ ψ : H, (hψ : ψ ∈ common_domain) →
    let hψ_x := common_in_Lx ψ hψ
    let hψ_y := common_in_Ly ψ hψ
    let hψ_z := common_in_Lz ψ hψ
    let hLxψ_z := common_in_Lz _ (Lx_stable ψ hψ)
    let hLzψ_x := common_in_Lx _ (Lz_stable ψ hψ)
    L_z.apply (L_x.apply ψ hψ_x) hLxψ_z - L_x.apply (L_z.apply ψ hψ_z) hLzψ_x =
      (Complex.I * (ℏ : ℂ)) • L_y.apply ψ hψ_y



/-- The commutator [L_x, L_y] equals iℏL_z as operators on the common domain -/
theorem Lx_Ly_commutator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H) (hψ : ψ ∈ L.common_domain) :
    let hψ_x := L.common_in_Lx ψ hψ
    let hψ_y := L.common_in_Ly ψ hψ
    let hψ_z := L.common_in_Lz ψ hψ
    let hLyψ_x := L.common_in_Lx _ (L.Ly_stable ψ hψ)
    let hLxψ_y := L.common_in_Ly _ (L.Lx_stable ψ hψ)
    L.L_x.apply (L.L_y.apply ψ hψ_y) hLyψ_x - L.L_y.apply (L.L_x.apply ψ hψ_x) hLxψ_y =
      (Complex.I * (ℏ : ℂ)) • L.L_z.apply ψ hψ_z :=
  L.commutation_xy ψ hψ

/-- The commutator [L_y, L_z] equals iℏL_x as operators on the common domain -/
theorem Ly_Lz_commutator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H) (hψ : ψ ∈ L.common_domain) :
    let hψ_x := L.common_in_Lx ψ hψ
    let hψ_y := L.common_in_Ly ψ hψ
    let hψ_z := L.common_in_Lz ψ hψ
    let hLzψ_y := L.common_in_Ly _ (L.Lz_stable ψ hψ)
    let hLyψ_z := L.common_in_Lz _ (L.Ly_stable ψ hψ)
    L.L_y.apply (L.L_z.apply ψ hψ_z) hLzψ_y - L.L_z.apply (L.L_y.apply ψ hψ_y) hLyψ_z =
      (Complex.I * (ℏ : ℂ)) • L.L_x.apply ψ hψ_x :=
  L.commutation_yz ψ hψ

/-- The commutator [L_z, L_x] equals iℏL_y as operators on the common domain -/
theorem Lz_Lx_commutator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H) (hψ : ψ ∈ L.common_domain) :
    let hψ_x := L.common_in_Lx ψ hψ
    let hψ_y := L.common_in_Ly ψ hψ
    let hψ_z := L.common_in_Lz ψ hψ
    let hLxψ_z := L.common_in_Lz _ (L.Lx_stable ψ hψ)
    let hLzψ_x := L.common_in_Lx _ (L.Lz_stable ψ hψ)
    L.L_z.apply (L.L_x.apply ψ hψ_x) hLxψ_z - L.L_x.apply (L.L_z.apply ψ hψ_z) hLzψ_x =
      (Complex.I * (ℏ : ℂ)) • L.L_y.apply ψ hψ_y :=
  L.commutation_zx ψ hψ


/-- Antisymmetry: [L_y, L_x] = -iℏL_z -/
theorem Ly_Lx_commutator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H) (hψ : ψ ∈ L.common_domain) :
    let hψ_x := L.common_in_Lx ψ hψ
    let hψ_y := L.common_in_Ly ψ hψ
    let hψ_z := L.common_in_Lz ψ hψ
    let hLyψ_x := L.common_in_Lx _ (L.Ly_stable ψ hψ)
    let hLxψ_y := L.common_in_Ly _ (L.Lx_stable ψ hψ)
    L.L_y.apply (L.L_x.apply ψ hψ_x) hLxψ_y - L.L_x.apply (L.L_y.apply ψ hψ_y) hLyψ_x =
      -(Complex.I * (ℏ : ℂ)) • L.L_z.apply ψ hψ_z := by
  have h := L.commutation_xy ψ hψ
  simp only at h ⊢
  -- h : XY - YX = iℏZ
  -- goal : YX - XY = -iℏZ
  rw [← neg_sub, h, neg_smul]


/-- Domain conditions for angular momentum uncertainty (clean version) -/
structure AngularMomentumUncertaintyDomain {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H) : Prop where
  h_norm : ‖ψ‖ = 1
  h_common : ψ ∈ L.common_domain


/- |iℏ| = ℏ (since ℏ > 0) -/
theorem norm_I_mul_hbar : ‖Complex.I * (ℏ : ℂ)‖ = ℏ := by
  rw [norm_mul, Complex.norm_I, one_mul]
  rw [Complex.norm_real]
  exact abs_of_pos hbar_pos


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : AngularMomentumOperators H} {ψ : H}

-- Derive everything from common_domain
def h_Lx (h : AngularMomentumUncertaintyDomain L ψ) : ψ ∈ L.L_x.domain :=
  L.common_in_Lx ψ h.h_common

def h_Ly (h : AngularMomentumUncertaintyDomain L ψ) : ψ ∈ L.L_y.domain :=
  L.common_in_Ly ψ h.h_common

def h_Lz (h : AngularMomentumUncertaintyDomain L ψ) : ψ ∈ L.L_z.domain :=
  L.common_in_Lz ψ h.h_common

def h_Ly_in_Lx (h : AngularMomentumUncertaintyDomain L ψ) :
    L.L_y.apply ψ (h_Ly h) ∈ L.L_x.domain :=
  L.common_in_Lx _ (L.Ly_stable ψ h.h_common)

def h_Lx_in_Ly (h : AngularMomentumUncertaintyDomain L ψ) :
    L.L_x.apply ψ (h_Lx h) ∈ L.L_y.domain :=
  L.common_in_Ly _ (L.Lx_stable ψ h.h_common)

def toShiftedDomainConditions (h : AngularMomentumUncertaintyDomain L ψ) :
    ShiftedDomainConditions L.L_x L.L_y ψ where
  hψ_A := h_Lx h
  hψ_B := h_Ly h
  hBψ_A := h_Ly_in_Lx h
  hAψ_B := h_Lx_in_Ly h
  h_norm := h.h_norm

end QuantumMechanics.ForbiddenSdS
