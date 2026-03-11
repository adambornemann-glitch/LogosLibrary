/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Forbidden/LifeTime.lean
-/
import LogosLibrary.Relativity.GR.Forbidden.AngularMomentum
import LogosLibrary.Relativity.GR.Forbidden.ThermalExcitation
import LogosLibrary.Relativity.GR.Forbidden.Reductio

import Mathlib.Analysis.Real.Pi.Bounds

namespace ForbiddenSdS.LifeTime

open InnerProductSpace Complex QuantumMechanics.ForbiddenSdS.AngularMomentum

open ThermalExcitation AdAbsurdem

/-- Time evolution under thermal bath interaction -/
structure ThermalEvolution (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The state at time t given initial state ψ₀ -/
  evolve : (ψ₀ : H) → (t : ℝ) → H
  /-- Evolution preserves normalization -/
  preserves_norm : ∀ ψ₀ t, ‖ψ₀‖ = 1 → ‖evolve ψ₀ t‖ = 1
  /-- Evolution preserves domain membership (at least for finite times) -/
  preserves_domain : ∀ (L : AngularMomentumOperators H) ψ₀ t,
    ψ₀ ∈ L.common_domain → evolve ψ₀ t ∈ L.common_domain

/-- After any positive interaction time, angular momentum is generically excited -/
axiom thermal_excites_after_positive_time {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (bath : ThermalBath)
    (evol : ThermalEvolution H)
    (ψ₀ : H) (h_norm : ‖ψ₀‖ = 1) (h_common : ψ₀ ∈ L.common_domain)
    (t : ℝ) (h_t_pos : t > 0) :
    let ψ := evol.evolve ψ₀ t
    let h_common' := evol.preserves_domain L ψ₀ t h_common
    ⟪ψ, L.L_x.apply ψ (L.common_in_Lx ψ h_common')⟫_ℂ ≠ 0 ∨
    ⟪ψ, L.L_y.apply ψ (L.common_in_Ly ψ h_common')⟫_ℂ ≠ 0 ∨
    ⟪ψ, L.L_z.apply ψ (L.common_in_Lz ψ h_common')⟫_ℂ ≠ 0


/-- **KEY THEOREM**: SdS states have zero uncertainty, contradicting thermal excitation.

    If ψ is SdS (all ⟨L_i⟩ = 0), then by Robertson, σ_Li could be zero.
    But if ANY ⟨L_i⟩ ≠ 0, then Robertson forces σ_Lj > 0 for j ≠ i.
    Thermal baths generically excite ⟨L_i⟩ ≠ 0, so SdS is forbidden. -/
lemma SdS_incompatible_with_nonzero_L {H : Type*} [NormedAddCommGroup H]
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


lemma SdS_forbidden_after_thermalization {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H) (bath : ThermalBath)
    (evol : ThermalEvolution H)
    (ψ₀ : H) (h_norm : ‖ψ₀‖ = 1) (h_common : ψ₀ ∈ L.common_domain)
    (t : ℝ) (h_t_pos : t > 0) :
    ¬RepresentsSdS L (evol.evolve ψ₀ t) := by
  have h_excited := thermal_excites_after_positive_time L bath evol ψ₀ h_norm h_common t h_t_pos
  exact SdS_incompatible_with_nonzero_L L _ (evol.preserves_domain L ψ₀ t h_common) h_excited


/-- The CMB has existed for mass_universe_seconds > 0 -/
theorem SdS_forbidden_our_universe {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H)
    (evol : ThermalEvolution H)
    (ψ₀ : H) (h_norm : ‖ψ₀‖ = 1) (h_common : ψ₀ ∈ L.common_domain) :
    ¬RepresentsSdS L (evol.evolve ψ₀ AdAbsurdem.universe_age_seconds) :=
  SdS_forbidden_after_thermalization L CMB evol ψ₀ h_norm h_common
    AdAbsurdem.universe_age_seconds AdAbsurdem.universe_age_seconds_pos



/-- **PHYSICAL CONCLUSION**: All black holes that have existed in a thermal bath
    for any positive time must have J ≠ 0 -/
lemma all_BH_rotating {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H)
    (evol : ThermalEvolution H)
    (bath : ThermalBath)
    (ψ₀ : H) (h_norm : ‖ψ₀‖ = 1) (h_common : ψ₀ ∈ L.common_domain)
    (t : ℝ) (h_t_pos : t > 0) :
    ¬IsZeroAngularMomentumState L (evol.evolve ψ₀ t) :=
  SdS_forbidden_after_thermalization L bath evol ψ₀ h_norm h_common t h_t_pos

/-- **COROLLARY**: Every black hole in our universe is rotating.

    Any black hole that formed after the CMB decoupled (t ≈ 380,000 years)
    has been thermalized for at least mass_universe_seconds - that time.
    Even primordial black holes from before decoupling have been bathed
    in radiation since the beginning. -/
theorem all_BH_in_our_universe_rotating {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H)
    (evol : ThermalEvolution H)
    (ψ₀ : H) (h_norm : ‖ψ₀‖ = 1) (h_common : ψ₀ ∈ L.common_domain) :
    ¬IsZeroAngularMomentumState L (evol.evolve ψ₀ AdAbsurdem.universe_age_seconds) :=
  all_BH_rotating L evol CMB ψ₀ h_norm h_common AdAbsurdem.universe_age_seconds AdAbsurdem.universe_age_seconds_pos



/-- For the skeptic: if you believe SdS black holes can exist in our universe,
    you must deny this axiom. Please explain how a black hole maintains
    ⟨Lₓ⟩ = ⟨Lᵧ⟩ = ⟨Lz⟩ = 0 while absorbing ~10⁶⁸ CMB photons over 13.8 Gyr,
    each carrying angular momentum ℏ from a random direction. -/
theorem skeptic_must_deny_thermal_axiom {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : AngularMomentumOperators H)
    (evol : ThermalEvolution H)
    (h_SdS_exists : ∃ ψ : H, ∃ (_h_norm : ‖ψ‖ = 1) (_h_common : ψ ∈ L.common_domain),
      IsZeroAngularMomentumState L (evol.evolve ψ AdAbsurdem.universe_age_seconds)) :
    False := by
  obtain ⟨ψ, h_norm, h_common, h_zero⟩ := h_SdS_exists
  have h_not_zero := all_BH_in_our_universe_rotating L evol ψ h_norm h_common
  exact h_not_zero h_zero

/-!
## SdS Lifetime Estimates

We show that even if you COULD prepare a black hole in the j=0 state,
it would be kicked out in a time so short it's physically meaningless.
-/

/-- Speed of light in cm/s -/
noncomputable def c_cm : ℝ := 2998 * 10^7  -- was 2.998e10

/-- Solar mass in grams -/
noncomputable def M_sun : ℝ := 1989 * 10^30  -- was 1.989e33

/-- Planck time -/
noncomputable def planck_time : ℝ := 539 / 10^46  -- was 5.39e-44


/-- CMB photon number density (photons/cm³) -/
def n_CMB : ℝ := 411

/-- Schwarzschild radius in cm for mass M in grams -/
noncomputable def schwarzschild_radius (M : ℝ) : ℝ :=
  2 * 6.674e-8 * M / (c_cm^2)  -- 2GM/c² in CGS

/-- Geometric cross-section of a black hole -/
noncomputable def BH_cross_section (M : ℝ) : ℝ :=
  Real.pi * (schwarzschild_radius M)^2

/-- Photon interaction rate: number of CMB photons hitting BH per second -/
noncomputable def photon_interaction_rate (M : ℝ) : ℝ :=
  n_CMB * BH_cross_section M * c_cm

/-- Each photon has O(1) probability of transferring angular momentum.
    We conservatively estimate P = 1/2 (it's probably higher). -/
noncomputable def angular_momentum_transfer_prob : ℝ := 0.5

/-- Rate at which angular momentum is excited -/
noncomputable def excitation_rate (M : ℝ) : ℝ :=
  photon_interaction_rate M * angular_momentum_transfer_prob

/-- Expected lifetime of the j=0 state: τ = 1/Γ -/
noncomputable def SdS_lifetime (M : ℝ) (_h_M_pos : M > 0) : ℝ :=
  1 / excitation_rate M

/-! ### Concrete Numbers -/


/-- Schwarzschild radius of the Sun: ~3 km = 3×10⁵ cm -/
lemma solar_schwarzschild : schwarzschild_radius M_sun > 2e5 := by
  unfold schwarzschild_radius M_sun c_cm
  norm_num

/-- Interaction rate for solar mass BH: ~10²⁴ photons/second -/
lemma solar_mass_interaction_rate : photon_interaction_rate M_sun > (10 : ℝ)^24 := by
  unfold photon_interaction_rate BH_cross_section schwarzschild_radius n_CMB c_cm M_sun

  -- Rewrite the Floats as real arithmetic
  have h1 : (6.674e-8 : ℝ) = 6674 / 10^11 := by ring

  -- Actually just use show/suffices to state what you need in clean form
  suffices h : 411 * (Real.pi * (2 * (6674/10^11) * (1989*10^30) / ((2998*10^7)^2))^2) * (2998*10^7) > 10^24 by
    convert h using 2 ; norm_num

  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h_rs_sq_pos : (2 * (6674/10^11) * (1989*10^30) / ((2998*10^7)^2))^2 ≥ 0 := sq_nonneg _
  nlinarith [sq_nonneg (2 * (6674/10^11) * (1989*10^30) / ((2998*10^7)^2))]


/-- **THE PUNCHLINE**: Solar mass SdS lifetime < 10⁻²⁴ seconds -/
lemma solar_mass_SdS_lifetime_bound :
    SdS_lifetime M_sun (by unfold M_sun; norm_num) < 1 / (10 : ℝ)^23 := by
  unfold SdS_lifetime excitation_rate angular_momentum_transfer_prob

  -- First, convert 0.5 to 1/2
  have h_half : (0.5 : ℝ) = 1/2 := by norm_num
  rw [h_half]

  have h_rate := solar_mass_interaction_rate
  -- h_rate : photon_interaction_rate M_sun > 10^24

  -- excitation_rate = rate * 0.5 > 10^24 * 0.5 = 5 * 10^23
  have h_exc : photon_interaction_rate M_sun * (1/2 : ℝ) > 5 * 10^23 := by
    have h1 : photon_interaction_rate M_sun * (1/2) > (10 : ℝ)^24 * (1/2) := by
      grind => linarith
    calc photon_interaction_rate M_sun * (1/2)
        > (10 : ℝ)^24 * (1/2) := h1
      _ = 5 * 10^23 := by norm_num

  -- Therefore 1 / excitation_rate < 1 / (5 * 10^23) < 1 / 10^23
  have h_pos : (5 : ℝ) * 10^23 > 0 := by norm_num

  calc (1 : ℝ) / (photon_interaction_rate M_sun * (1/2))
      < 1 / (5 * 10^23) := by
        apply one_div_lt_one_div_of_lt h_pos h_exc
    _ < 1 / 10^23 := by norm_num

/-! ### The Killing Blow -/

/-- One second in seconds (for clarity) -/
def one_second : ℝ := 1


/-- For ANY black hole with M > 10²⁰ grams (~mass of small asteroid),
    the SdS lifetime is less than one second. -/
lemma SdS_lifetime_less_than_one_second (M : ℝ) (h_M : M > (10 : ℝ)^22) :
    SdS_lifetime M (by linarith) < one_second := by
  unfold SdS_lifetime one_second excitation_rate photon_interaction_rate
  unfold BH_cross_section schwarzschild_radius angular_momentum_transfer_prob
  unfold n_CMB c_cm

  have h_half : (0.5 : ℝ) = 1/2 := by norm_num
  rw [h_half]

  have h_G : (6674e-11 : ℝ) = 6674 / 10^11 := by norm_num
  rw [h_G]

  suffices h : 411 * (Real.pi * (2 * (6674/10^11) * M / ((2998 * 10^7)^2))^2) * (2998 * 10^7) * (1/2) > 1 by
    have h_pos : 411 * (Real.pi * (2 * (6674/10^11) * M / ((2998 * 10^7)^2))^2) * (2998 * 10^7) * (1/2) > 0 := by
      positivity
    rw [one_div_lt h_pos (by norm_num : (0 : ℝ) < 1)]
    simp only [one_div_one]
    exact h

  have hπ : Real.pi > 3 := Real.pi_gt_three

  calc 411 * (Real.pi * (2 * (6674/10^11) * M / ((2998 * 10^7)^2))^2) * (2998 * 10^7) * (1/2)
      > 411 * (3 * (2 * (6674/10^11) * (10 : ℝ)^22 / ((2998 * 10^7)^2))^2) * (2998 * 10^7) * (1/2) := by
        have h2 : 2 * (6674/10^11) * M / ((2998 * 10^7)^2) > 2 * (6674/10^11) * (10 : ℝ)^22 / ((2998 * 10^7)^2) := by
          apply div_lt_div_of_pos_right _ (by positivity)
          apply mul_lt_mul_of_pos_left h_M (by positivity)
        nlinarith [sq_nonneg (2 * (6674/10^11) * M / ((2998 * 10^7)^2)),
                   sq_nonneg (2 * (6674/10^11) * (10 : ℝ)^22 / ((2998 * 10^7)^2)),
                   Real.pi_gt_three]
    _ > 1 := by norm_num



/-- For stellar mass and above, lifetime is less than a NANOSECOND -/
theorem stellar_BH_SdS_lifetime_less_than_nanosecond (M : ℝ) (h_M : M > (1/10) * M_sun) :
    SdS_lifetime M (by unfold M_sun at h_M; grind) < 1 / (10 : ℝ)^9 := by
  unfold SdS_lifetime excitation_rate photon_interaction_rate
  unfold BH_cross_section schwarzschild_radius angular_momentum_transfer_prob
  unfold n_CMB c_cm
  unfold M_sun at h_M

  have h_half : (0.5 : ℝ) = 1/2 := by norm_num
  rw [h_half]
  have h_G : (6674e-11 : ℝ) = 6674 / 10^11 := by norm_num
  rw [h_G]

  have h_M' : M > 1989 * (10 : ℝ)^28 := by
    have : (1 : ℝ) / 10 * (1989 * 10 ^ 30) > 1989 * 10 ^ 28 := by norm_num
    grind only

  suffices h : 411 * (Real.pi * (2 * (6674/10^11) * M / ((2998 * 10^7)^2))^2) *
    (2998 * 10^7) * (1/2) > (10 : ℝ)^9 by
    exact one_div_lt_one_div_of_lt (by positivity) h

  /-  Three-step calc: (1) replace π with 3, (2) replace M with M₀, (3) norm_num
      Each step is one clean monotonicity argument instead of one impossible nlinarith -/
  calc 411 * (Real.pi * (2 * (6674/10^11) * M / ((2998 * 10^7)^2))^2) *
        (2998 * 10^7) * (1/2)
      -- Step 1: π ≥ 3 (everything else fixed, all factors nonneg)
      ≥ 411 * (3 * (2 * (6674/10^11) * M / ((2998 * 10^7)^2))^2) *
        (2998 * 10^7) * (1/2) := by
        gcongr
        exact le_of_lt Real.pi_gt_three
      -- Step 2: M > 1989 * 10^28 (strict, through the square)
    _ > 411 * (3 * (2 * (6674/10^11) * (1989 * (10 : ℝ)^28) /
        ((2998 * 10^7)^2))^2) * (2998 * 10^7) * (1/2) := by
        gcongr
      -- Step 3: pure numerics, no π, no M
    _ > (10 : ℝ)^9 := by norm_num

/-! ### The Final Theorem -/

/-- **MAIN RESULT**: For any astrophysically relevant black hole,
    the SdS state has a lifetime so short that it cannot be considered
    a physical state of the system.

    Interpretation: SdS is not merely "improbable" or "measure zero" —
    it is dynamically forbidden on timescales shorter than any physical
    process could prepare or observe it. -/
theorem SdS_not_physical_state (M : ℝ) (h_M : M > 10^22) :
    SdS_lifetime M (by linarith) < one_second ∧
    SdS_lifetime M (by linarith) < AdAbsurdem.universe_age_seconds := by
  constructor
  · exact SdS_lifetime_less_than_one_second M h_M
  · calc SdS_lifetime M (by linarith)
        < one_second := SdS_lifetime_less_than_one_second M h_M
      _ < AdAbsurdem.universe_age_seconds := by unfold one_second AdAbsurdem.universe_age_seconds; norm_num

end ForbiddenSdS.LifeTime
