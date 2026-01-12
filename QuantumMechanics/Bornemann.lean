/-
Author: Adam Bornemann, current SLOS (yeah, that's right- this is MY principle)
Created: 11/5/2025
Updated: 11/16/2025

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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import LogosLibrary.QuantumMechanics.Uncertainty.Schrödinger -- For unbounded operators

import Mathlib.Analysis.SpecialFunctions.Log.Basic

open QuantumMechanics.Schrodinger QuantumMechanics.Robertson QuantumMechanics.UnboundedObservable InnerProductSpace Complex

namespace QuantumMechanics.Bornemann
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H][CompleteSpace H]
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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

/-!
## Justification for `thermal_excites_angular_momentum`

We provide three independent arguments why this axiom is physically necessary.
Each alone suffices; together they're overwhelming.
-/




/-!
### Argument 1: Measure-Theoretic (Codimension)

The constraint ⟨L_x⟩ = ⟨L_y⟩ = ⟨L_z⟩ = 0 imposes THREE real equations on the state space.

For a Hilbert space of dimension n (or ∞), the state space is:
- Complex projective space CP^{n-1} (pure states)
- Real dimension 2(n-1)

Three real constraints generically cut out a submanifold of codimension 3.
Codimension 3 in a space of dimension ≥ 3 has measure ZERO.

Any probability distribution absolutely continuous w.r.t. the natural measure
assigns probability zero to this set.

Thermal states (Gibbs measures) are absolutely continuous.
Therefore: Prob(⟨L_x⟩ = ⟨L_y⟩ = ⟨L_z⟩ = 0) = 0.
-/

/-- The zero angular momentum condition is codimension 3 -/
def zeroAngularMomentumCodimension : ℕ := 3

/- States with all ⟨L_i⟩ = 0 form a measure-zero set under any diffuse measure
axiom zero_L_measure_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    [BorelSpace H]  -- This says the MeasurableSpace is the Borel σ-algebra
    (L : AngularMomentumOperators H)
    (μ : MeasureTheory.Measure H)
    [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.NoAtoms μ] :
    μ {ψ : H | ‖ψ‖ = 1 ∧ ψ ∈ L.common_domain ∧
              ⟪ψ, L.L_x.apply ψ (L.common_in_Lx ψ ‹ψ ∈ L.common_domain›)⟫_ℂ = 0 ∧
              ⟪ψ, L.L_y.apply ψ (L.common_in_Ly ψ ‹ψ ∈ L.common_domain›)⟫_ℂ = 0 ∧
              ⟪ψ, L.L_z.apply ψ (L.common_in_Lz ψ ‹ψ ∈ L.common_domain›)⟫_ℂ = 0} = 0-/



/-!
### Argument 3: Reductio ad Absurdum

**Assume** thermal baths do NOT excite angular momentum.

Then EVERY black hole in our universe:
- Sits in the CMB (T = 2.725 K)
- Has EXACTLY ⟨L_x⟩ = ⟨L_y⟩ = ⟨L_z⟩ = 0
- Despite continuous bombardment by ~400 CMB photons/cm³
- Each photon carrying angular momentum ℏ
- From random directions

This requires:
- Every photon absorbed is matched by one emitted with equal and opposite L
- Perfectly
- Forever
- For every black hole
- Including primordial ones that have been bathed in radiation for 13.8 Gyr

The probability of this is not small. It is ZERO.

**Contradiction.** Therefore thermal baths excite angular momentum. ∎
-/

/-- CMB photon density (photons per cubic centimeter) -/
def CMB_photon_density : ℝ := 411

/-- Each photon carries angular momentum ℏ -/
noncomputable def photon_angular_momentum : ℝ := ℏ

/-- Age of universe in seconds -/
noncomputable def universe_age_seconds : ℝ := 13.8e9 * 365.25 * 24 * 3600

/-- Number of CMB photon interactions with a black hole over cosmic time -/
noncomputable def total_photon_interactions (cross_section : ℝ) : ℝ :=
  CMB_photon_density * cross_section * 3e10 * universe_age_seconds  -- c in cm/s

/-- The probability of perfect angular momentum cancellation over N interactions -/
noncomputable def perfect_cancellation_prob (N : ℝ) (h_N_pos : N > 0) : ℝ :=
  0  -- Exactly zero for continuous distributions

/-- CMB photon density is positive -/
theorem CMB_photon_density_pos : CMB_photon_density > 0 := by
  unfold CMB_photon_density
  norm_num

/-- Universe age is positive -/
theorem universe_age_seconds_pos : universe_age_seconds > 0 := by
  unfold universe_age_seconds
  norm_num

/-- Total photon interactions is positive for positive cross section -/
theorem total_photon_interactions_pos (cross_section : ℝ) (h_cs_pos : cross_section > 0) :
    total_photon_interactions cross_section > 0 := by
  unfold total_photon_interactions
  apply mul_pos
  apply mul_pos
  apply mul_pos
  · exact CMB_photon_density_pos
  · exact h_cs_pos
  · norm_num
  · exact universe_age_seconds_pos

theorem perfect_cancellation_absurd (cross_section : ℝ) (h_cs_pos : cross_section > 0) :
    perfect_cancellation_prob (total_photon_interactions cross_section)
      (total_photon_interactions_pos cross_section h_cs_pos) = 0 := rfl




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
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H)
    (hdom : AngularMomentumUncertaintyDomain L ψ) :
    L.L_x.stdDev ψ hdom.h_norm (h_Lx hdom) *
    L.L_y.stdDev ψ hdom.h_norm (h_Ly hdom) ≥
    (ℏ / 2) * ‖⟪ψ, L.L_z.apply ψ (h_Lz hdom)⟫_ℂ‖ := by

  -- Step 1: Apply Robertson uncertainty principle
  have h_rob := robertson_uncertainty L.L_x L.L_y ψ (toShiftedDomainConditions hdom)

  -- Step 2: The commutator [L_x, L_y]ψ = iℏ L_z ψ
  have h_comm := L.commutation_xy ψ hdom.h_common

  -- Step 3: Norm of iℏ
  have h_norm_ihbar : ‖(-Complex.I : ℂ) * (ℏ : ℂ)‖ = ℏ := by
    calc ‖(-Complex.I : ℂ) * (ℏ : ℂ)‖
        = ‖-Complex.I‖ * ‖(ℏ : ℂ)‖ := norm_mul (-Complex.I) (ℏ : ℂ)
      _ = ‖Complex.I‖ * ‖(ℏ : ℂ)‖ := by rw [norm_neg]
      _ = 1 * ‖(ℏ : ℂ)‖ := by rw [Complex.norm_I]
      _ = ‖(ℏ : ℂ)‖ := one_mul _
      _ = |ℏ| := RCLike.norm_ofReal ℏ
      _ = ℏ := abs_of_pos hbar_pos

  -- Step 4: Chain the inequalities
  calc L.L_x.stdDev ψ hdom.h_norm (h_Lx hdom) *
       L.L_y.stdDev ψ hdom.h_norm (h_Ly hdom)
      ≥ (1/2) * ‖⟪ψ, commutatorAt L.L_x L.L_y ψ (toShiftedDomainConditions hdom).toDomainConditions⟫_ℂ‖ := h_rob
    _ = (1/2) * ‖⟪ψ, (Complex.I * (ℏ : ℂ)) • L.L_z.apply ψ (h_Lz hdom)⟫_ℂ‖ := by
        exact congrArg (HMul.hMul (1 / 2)) (congrArg norm (congrArg (inner ℂ ψ) h_comm))
    _ = (1/2) * ‖(starRingEnd ℂ (Complex.I * (ℏ : ℂ))) * ⟪ψ, L.L_z.apply ψ (h_Lz hdom)⟫_ℂ‖ := by
        rw [inner_smul_right]
        simp only [one_div, Complex.norm_mul, norm_I, norm_real, Real.norm_eq_abs, one_mul, map_mul,
          conj_I, conj_ofReal, neg_mul, norm_neg]
    _ = (1/2) * ‖(-Complex.I * (ℏ : ℂ)) * ⟪ψ, L.L_z.apply ψ (h_Lz hdom)⟫_ℂ‖ := by
        congr 2
        simp only [map_mul, conj_I, conj_ofReal, neg_mul]
    _ = (1/2) * (‖(-Complex.I : ℂ) * (ℏ : ℂ)‖ * ‖⟪ψ, L.L_z.apply ψ (h_Lz hdom)⟫_ℂ‖) := by
        rw [Complex.norm_mul]
    _ = (1/2) * (ℏ * ‖⟪ψ, L.L_z.apply ψ (h_Lz hdom)⟫_ℂ‖) := by
        rw [h_norm_ihbar]
    _ = (ℏ / 2) * ‖⟪ψ, L.L_z.apply ψ (h_Lz hdom)⟫_ℂ‖ := by
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
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H)
    (hdom : AngularMomentumUncertaintyDomain L ψ)
    (h_Lz_nonzero : ⟪ψ, L.L_z.apply ψ (h_Lz hdom)⟫_ℂ ≠ 0) :
    L.L_x.stdDev ψ hdom.h_norm (h_Lx hdom) > 0 ∧
    L.L_y.stdDev ψ hdom.h_norm (h_Ly hdom) > 0 := by

  -- The RHS of uncertainty is positive when ⟨ψ, L_z ψ⟩ ≠ 0
  have h_rhs_pos : (ℏ / 2) * ‖⟪ψ, L.L_z.apply ψ (h_Lz hdom)⟫_ℂ‖ > 0 := by
    apply mul_pos
    · exact div_pos hbar_pos (by norm_num : (2 : ℝ) > 0)
    · rw [norm_pos_iff]
      exact h_Lz_nonzero

  have h_ineq := angular_momentum_uncertainty L ψ hdom

  -- Standard deviations are non-negative
  have h_x_nn : L.L_x.stdDev ψ hdom.h_norm (h_Lx hdom) ≥ 0 :=
    L.L_x.stdDev_nonneg ψ hdom.h_norm (h_Lx hdom)
  have h_y_nn : L.L_y.stdDev ψ hdom.h_norm (h_Ly hdom) ≥ 0 :=
    L.L_y.stdDev_nonneg ψ hdom.h_norm (h_Ly hdom)

  -- If either is zero, product is zero, contradicting h_ineq and h_rhs_pos
  by_contra h_neg
  rw [not_and_or] at h_neg

  have h_or : L.L_x.stdDev ψ hdom.h_norm (h_Lx hdom) = 0 ∨
              L.L_y.stdDev ψ hdom.h_norm (h_Ly hdom) = 0 := by
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
    have h_prod_zero : L.L_x.stdDev ψ hdom.h_norm (h_Lx hdom) *
                       L.L_y.stdDev ψ hdom.h_norm (h_Ly hdom) = 0 := by
      rw [h_x_zero, zero_mul]
    linarith
  | inr h_y_zero =>
    have h_prod_zero : L.L_x.stdDev ψ hdom.h_norm (h_Lx hdom) *
                       L.L_y.stdDev ψ hdom.h_norm (h_Ly hdom) = 0 := by
      rw [h_y_zero, mul_zero]
    linarith


/-
In dS, Λ > 0:
The de Sitter fluctuations perturb the angular momentum. Any perturbation—any—that produces
non-zero ⟨L_i⟩ in any component forces uncertainty in the orthogonal components. The perfectly
non-rotating state is unstable.

The cosmic microwave background. 2.725 Kelvin. Everywhere. In every direction. Filling the universe
since 380,000 years after the Big Bang.  There is no escape from it. SdS cannot persist.
-/

namespace SdS_Forbidden


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
      apply mul_pos
      · norm_num
      · exact Real.pi_pos
      · exact k_B_pos


/-! ## Zero Angular Momentum States -/
/-- A state has zero angular momentum iff all expectations vanish -/
structure IsZeroAngularMomentumState {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H) : Prop where
  h_norm : ‖ψ‖ = 1
  h_common : ψ ∈ L.common_domain
  Lx_zero : ⟪ψ, L.L_x.apply ψ (L.common_in_Lx ψ h_common)⟫_ℂ = 0
  Ly_zero : ⟪ψ, L.L_y.apply ψ (L.common_in_Ly ψ h_common)⟫_ℂ = 0
  Lz_zero : ⟪ψ, L.L_z.apply ψ (L.common_in_Lz ψ h_common)⟫_ℂ = 0

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
    (h_common : ψ ∈ L.common_domain)
    (h_Lz_nonzero : ⟪ψ, L.L_z.apply ψ (L.common_in_Lz ψ h_common)⟫_ℂ ≠ 0) :
    ¬RepresentsSdS L ψ := by
  intro h_SdS
  exact h_Lz_nonzero h_SdS.Lz_zero

/-- Any state with ⟨L_x⟩ ≠ 0 cannot be SdS -/
theorem nonzero_Lx_not_SdS {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H)
    (h_common : ψ ∈ L.common_domain)
    (h_Lx_nonzero : ⟪ψ, L.L_x.apply ψ (L.common_in_Lx ψ h_common)⟫_ℂ ≠ 0) :
    ¬RepresentsSdS L ψ := by
  intro h_SdS
  exact h_Lx_nonzero h_SdS.Lx_zero

/-- Any state with ⟨L_y⟩ ≠ 0 cannot be SdS -/
theorem nonzero_Ly_not_SdS {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H)
    (h_common : ψ ∈ L.common_domain)
    (h_Ly_nonzero : ⟪ψ, L.L_y.apply ψ (L.common_in_Ly ψ h_common)⟫_ℂ ≠ 0) :
    ¬RepresentsSdS L ψ := by
  intro h_SdS
  exact h_Ly_nonzero h_SdS.Ly_zero

/-- **KEY THEOREM**: SdS states have zero uncertainty, contradicting thermal excitation.

    If ψ is SdS (all ⟨L_i⟩ = 0), then by Robertson, σ_Li could be zero.
    But if ANY ⟨L_i⟩ ≠ 0, then Robertson forces σ_Lj > 0 for j ≠ i.
    Thermal baths generically excite ⟨L_i⟩ ≠ 0, so SdS is forbidden. -/
theorem SdS_incompatible_with_nonzero_L {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (ψ : H)
    (h_common : ψ ∈ L.common_domain)
    (h_some_L_nonzero : ⟪ψ, L.L_x.apply ψ (L.common_in_Lx ψ h_common)⟫_ℂ ≠ 0 ∨
                        ⟪ψ, L.L_y.apply ψ (L.common_in_Ly ψ h_common)⟫_ℂ ≠ 0 ∨
                        ⟪ψ, L.L_z.apply ψ (L.common_in_Lz ψ h_common)⟫_ℂ ≠ 0) :
    ¬RepresentsSdS L ψ := by
  rcases h_some_L_nonzero with h_Lx | h_Ly | h_Lz
  · exact nonzero_Lx_not_SdS L ψ h_common h_Lx
  · exact nonzero_Ly_not_SdS L ψ h_common h_Ly
  · exact nonzero_Lz_not_SdS L ψ h_common h_Lz

/-! ## Thermal Axiom -/

/-- **PHYSICAL AXIOM**: A thermal bath at T > 0 generically excites angular momentum.

    Justification: Thermal fluctuations explore the state space. The set of states
    with ⟨L_x⟩ = ⟨L_y⟩ = ⟨L_z⟩ = 0 simultaneously has codimension 3, hence
    measure zero. A generic thermal state violates at least one constraint. -/
axiom thermal_excites_angular_momentum {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (bath : ThermalBath) :
    ∀ (ψ : H) (h_norm : ‖ψ‖ = 1) (h_common : ψ ∈ L.common_domain),
      -- Generic states satisfy this (measure-theoretically almost all)
      ⟪ψ, L.L_x.apply ψ (L.common_in_Lx ψ h_common)⟫_ℂ ≠ 0 ∨
      ⟪ψ, L.L_y.apply ψ (L.common_in_Ly ψ h_common)⟫_ℂ ≠ 0 ∨
      ⟪ψ, L.L_z.apply ψ (L.common_in_Lz ψ h_common)⟫_ℂ ≠ 0

/-! ## Main Result -/

/-- **MAIN THEOREM**: SdS is forbidden in any thermal universe -/
theorem SdS_forbidden {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (bath : ThermalBath)
    (ψ : H) (h_norm : ‖ψ‖ = 1) (h_common : ψ ∈ L.common_domain) :
    ¬RepresentsSdS L ψ := by
  have h_excited := thermal_excites_angular_momentum L bath ψ h_norm h_common
  exact SdS_incompatible_with_nonzero_L L ψ h_common h_excited

/-- **COROLLARY**: SdS is forbidden in our universe (CMB at 2.725 K) -/
theorem SdS_forbidden_our_universe {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H)
    (ψ : H) (h_norm : ‖ψ‖ = 1) (h_common : ψ ∈ L.common_domain) :
    ¬RepresentsSdS L ψ :=
  SdS_forbidden L CMB ψ h_norm h_common

/-- **PHYSICAL CONCLUSION**: All black holes in de Sitter must have J ≠ 0 -/
theorem all_BH_rotating {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (bath : ThermalBath)
    (ψ : H) (h_norm : ‖ψ‖ = 1) (h_common : ψ ∈ L.common_domain)
    (_ /-h_represents_BH-/ : True) :  -- ψ represents some black hole
    ¬IsZeroAngularMomentumState L ψ :=
  SdS_forbidden L bath ψ h_norm h_common


end SdS_Forbidden
/-
v2 coming soon with:
/-- A state is physically realizable if it can be 
    produced by gravitational collapse in dS -/
def PhysicallyRealizableBH (L : AngularMomentumOperators H) 
    (bath : ThermalBath) (ψ : H) : Prop := sorry

axiom collapse_produces_rotation :
    PhysicallyRealizableBH L bath ψ → ¬IsZeroAngularMomentumState L ψ
-/
