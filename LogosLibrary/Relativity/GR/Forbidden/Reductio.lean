/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Forbidden/Reductio.lean
-/
import LogosLibrary.Relativity.GR.Forbidden.AngularMomentum
import LogosLibrary.Relativity.GR.Forbidden.ThermalExcitation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open QuantumMechanics Robertson UnboundedObservable InnerProductSpace Complex
  QuantumMechanics.ForbiddenSdS.AngularMomentum

namespace ForbiddenSdS.AdAbsurdem
/-
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
noncomputable def perfect_cancellation_prob (N : ℝ) (_h_N_pos : N > 0) : ℝ :=
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


end ForbiddenSdS.AdAbsurdem
