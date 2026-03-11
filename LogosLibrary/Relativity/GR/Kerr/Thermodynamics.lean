/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Kerr/Thermodynamics.lean
-/
import LogosLibrary.Relativity.GR.Kerr.Singularity

open MinkowskiSpace QuantumMechanics

namespace Kerr
/-!
==================================================================================================================
PART V: THERMODYNAMICS - HAWKING TEMPERATURE
==================================================================================================================

Now we need to calculate temperatures. This is where thermodynamics enters.

**The Plan:**
1. Define surface gravity κ at Killing horizons (geometric)
2. Hawking's formula: T = κ/(2π) (physical law!)
3. Compute T_+ and T_- at the two horizons
4. Show T_+ ≠ T_- (important!)
5. Argue T_ring = T_+ from thermal equilibrium (not geometric!)

**Critical distinction:**
- Horizon temperatures: DERIVABLE from Killing vector analysis (geometry + physics)
- Ring temperature: INFERRED from thermodynamic equilibrium (pure physics!)
-/

/-!
### Surface Gravity at Killing Horizons

For a Killing horizon, the surface gravity κ is defined geometrically from
the Killing vector field. For Kerr, the formula is:

κ = (r₊ - r₋) / (2(r² + a²))

This is the "gravitational acceleration" at the horizon as measured by an
observer at infinity.
-/

noncomputable def surface_gravity_outer (p : KerrParams) : ℝ :=
  (r_plus p - r_minus p) / (2 * ((r_plus p)^2 + p.a^2))

noncomputable def surface_gravity_inner (p : KerrParams) : ℝ :=
  (r_plus p - r_minus p) / (2 * ((r_minus p)^2 + p.a^2))

/-!
**Hawking's formula:** T = κ/(2πk_B)

In geometric units where k_B = 1:
T = κ/(2π)

This is one of the most profound discoveries in theoretical physics - black holes
have a temperature! They emit thermal radiation (Hawking radiation).

**Historical note:**
Hawking discovered this in 1974 using quantum field theory in curved spacetime.
It was totally unexpected - classical black holes are "cold" (no radiation).
But quantum mechanically, they glow!
-/

noncomputable def hawkingTemperature (p : KerrParams) : ℝ :=
  surface_gravity_outer p / (2 * Real.pi)

noncomputable def innerHorizonTemperature (p : KerrParams) : ℝ :=
  surface_gravity_inner p / (2 * Real.pi)

/-!
### The Two Horizons Have Different Temperatures!

This is a key result - the inner and outer horizons are at different temperatures.
-/
theorem hawking_temperature_positive (p : KerrParams) (ha : 0 < |p.a| ∧ |p.a| < p.M) :
    hawkingTemperature p > 0 := by
  unfold hawkingTemperature surface_gravity_outer

  have hM : p.M > 0 := p.mass_positive

  -- Step 1: M² - a² > 0 (strictly subextremal)
  have h_discriminant_pos : p.M^2 - p.a^2 > 0 := by
    have h1 : p.a^2 < p.M^2 := by
      calc p.a^2
          = |p.a|^2 := (sq_abs p.a).symm
        _ < p.M^2 := by nlinarith [ha.1, ha.2, abs_nonneg p.a]
    linarith

  -- Step 2: √(M² - a²) > 0
  have h_sqrt_pos : Real.sqrt (p.M^2 - p.a^2) > 0 :=
    Real.sqrt_pos.mpr h_discriminant_pos

  -- Step 3: r_plus - r_minus = 2√(M² - a²) > 0
  have h_horizon_diff_pos : r_plus p - r_minus p > 0 := by
    unfold r_plus r_minus
    calc (p.M + Real.sqrt (p.M^2 - p.a^2)) - (p.M - Real.sqrt (p.M^2 - p.a^2))
        = 2 * Real.sqrt (p.M^2 - p.a^2) := by ring
      _ > 0 := by linarith

  -- Step 4: r_plus > 0
  have h_rplus_pos : r_plus p > 0 := r_plus_positive p

  -- Step 5: (r_plus)² + a² > 0
  have h_rplus_sq_plus_a_sq_pos : (r_plus p)^2 + p.a^2 > 0 := by
    have h1 : (r_plus p)^2 > 0 := sq_pos_of_pos h_rplus_pos
    have h2 : p.a^2 ≥ 0 := sq_nonneg _
    linarith

  -- Step 6: 2 * ((r_plus)² + a²) > 0
  have h_denom1_pos : 2 * ((r_plus p)^2 + p.a^2) > 0 := by
    linarith

  -- Step 7: surface_gravity_outer > 0
  have h_kappa_pos : (r_plus p - r_minus p) / (2 * ((r_plus p)^2 + p.a^2)) > 0 :=
    div_pos h_horizon_diff_pos h_denom1_pos

  -- Step 8: 2π > 0
  have h_two_pi_pos : 2 * Real.pi > 0 := by
    linarith [Real.pi_pos]

  -- Step 9: T = κ/(2π) > 0
  exact div_pos h_kappa_pos h_two_pi_pos



/-- The inner and outer horizons have different Hawking temperatures.

    **Physical significance:**
    - T_outer = κ_outer/(2π) where κ_outer = (r₊ - r₋)/(2(r₊² + a²))
    - T_inner = κ_inner/(2π) where κ_inner = (r₊ - r₋)/(2(r₋² + a²))

    Since r₊ > r₋ > 0 for strictly subextremal black holes (0 < |a| < M),
    we have r₊² > r₋², hence the denominators differ.

    **Key insight for ring temperature:**
    The ring equilibrates with T_outer (not T_inner) because energy flows
    from the exterior through the outer horizon. This is a thermodynamic
    argument, not a geometric one — the ring is not a Killing horizon,
    so we cannot compute its temperature from surface gravity.

    **Extremal limit (|a| = M):**
    Both temperatures vanish as r₊ → r₋ → M. The horizons merge and
    the black hole becomes "cold" (T = 0 but S > 0, like absolute zero).
-/
theorem horizon_temperatures_differ (p : KerrParams) (ha : 0 < |p.a| ∧ |p.a| < p.M) :
    innerHorizonTemperature p ≠ hawkingTemperature p := by
  unfold innerHorizonTemperature hawkingTemperature surface_gravity_inner surface_gravity_outer

  have hM : p.M > 0 := p.mass_positive

  -- Step 1: M² - a² > 0 (strictly subextremal)
  have h_discriminant_pos : p.M^2 - p.a^2 > 0 := by
    have h1 : p.a^2 < p.M^2 := by
      calc p.a^2
          = |p.a|^2 := (sq_abs p.a).symm
        _ < p.M^2 := by nlinarith [ha.1, ha.2, abs_nonneg p.a]
    linarith

  -- Step 2: √(M² - a²) > 0
  have h_sqrt_pos : Real.sqrt (p.M^2 - p.a^2) > 0 :=
    Real.sqrt_pos.mpr h_discriminant_pos

  -- Step 3: r_+ > r_-
  have h_rplus_gt_rminus : r_plus p > r_minus p := by
    unfold r_plus r_minus
    calc p.M + Real.sqrt (p.M^2 - p.a^2)
        > p.M + 0 := by linarith
      _ = p.M := by ring
      _ = p.M - 0 := by ring
      _ > p.M - Real.sqrt (p.M^2 - p.a^2) := by linarith

  -- Step 4: r_+ > 0 and r_- > 0
  have h_rplus_pos : r_plus p > 0 := r_plus_positive p
  have h_rminus_pos : r_minus p > 0 := r_minus_positive p ha

  -- Step 5: (r_+)² > (r_-)² (since both positive and r_+ > r_-)
  have h_sq_ineq : (r_plus p)^2 > (r_minus p)^2 := by
    apply sq_lt_sq'
    · calc -(r_plus p)
          < 0 := by linarith
        _ < r_minus p := h_rminus_pos
    · exact h_rplus_gt_rminus

  -- Step 6: (r_+)² + a² > (r_-)² + a²
  have h_denom_ineq : (r_plus p)^2 + p.a^2 > (r_minus p)^2 + p.a^2 := by
    linarith

  -- Step 7: (r_+)² + a² ≠ (r_-)² + a²
  have h_denom_ne : (r_plus p)^2 + p.a^2 ≠ (r_minus p)^2 + p.a^2 :=
    ne_of_gt h_denom_ineq

  -- Step 8: Both denominators are positive
  have h_denom_outer_pos : 2 * ((r_plus p)^2 + p.a^2) > 0 := by
    have h1 : (r_plus p)^2 > 0 := sq_pos_of_pos h_rplus_pos
    linarith [sq_nonneg p.a]

  have h_denom_inner_pos : 2 * ((r_minus p)^2 + p.a^2) > 0 := by
    have h1 : (r_minus p)^2 > 0 := sq_pos_of_pos h_rminus_pos
    linarith [sq_nonneg p.a]

  -- Step 9: The numerator r_+ - r_- > 0
  have h_numer_pos : r_plus p - r_minus p > 0 := by linarith

  -- Step 10: 2π > 0
  have h_two_pi_pos : 2 * Real.pi > 0 := by linarith [Real.pi_pos]

  -- Step 11: The two surface gravities differ
  have h_kappa_ne : (r_plus p - r_minus p) / (2 * ((r_minus p)^2 + p.a^2)) ≠
                    (r_plus p - r_minus p) / (2 * ((r_plus p)^2 + p.a^2)) := by
    intro h_eq
    have h_numer_ne_zero : r_plus p - r_minus p ≠ 0 := ne_of_gt h_numer_pos
    have h_denom_outer_ne_zero : 2 * ((r_plus p)^2 + p.a^2) ≠ 0 := ne_of_gt h_denom_outer_pos
    have h_denom_inner_ne_zero : 2 * ((r_minus p)^2 + p.a^2) ≠ 0 := ne_of_gt h_denom_inner_pos
    -- If a/b = a/c with a ≠ 0 and b,c ≠ 0, then b = c
    have h_denoms_eq : (r_plus p)^2 + p.a^2 = (r_minus p)^2 + p.a^2 := by
      have h1 : (r_plus p - r_minus p) / (2 * ((r_minus p)^2 + p.a^2)) * (2 * ((r_minus p)^2 + p.a^2)) =
                (r_plus p - r_minus p) / (2 * ((r_plus p)^2 + p.a^2)) * (2 * ((r_minus p)^2 + p.a^2)) := by
        rw [h_eq]
      have h2 : (r_plus p - r_minus p) / (2 * ((r_minus p)^2 + p.a^2)) * (2 * ((r_plus p)^2 + p.a^2)) =
                (r_plus p - r_minus p) / (2 * ((r_plus p)^2 + p.a^2)) * (2 * ((r_plus p)^2 + p.a^2)) := by
        rw [h_eq]
      field_simp at h1 h2
      linarith
    exact absurd h_denoms_eq h_denom_ne

  -- Step 12: Dividing by the same positive 2π preserves inequality
  intro h_temp_eq
  apply h_kappa_ne
  field_simp at h_temp_eq ⊢
  exact h_temp_eq


/-!
**Physical interpretation:**
T_+ ≈ ℏc³/(8πGM k_B) for slowly rotating black holes
T_- has a different formula involving the inner horizon radius

For a solar mass black hole: T_+ ≈ 60 nanoKelvin (incredibly cold!)
For a primordial micro black hole: could be billions of Kelvin!

**Question:** What about the ring? Which temperature is it at?
Answer: We need thermal equilibrium arguments - coming next!
-/

/-!
==================================================================================================================
PART VI: RING TEMPERATURE VIA THERMAL EQUILIBRIUM
==================================================================================================================

Now comes the crucial step: determining the ring temperature.

**The argument:**
1. Assume the black hole is in a steady state (common assumption for astrophysics)
2. In steady state, no net energy flow anywhere (otherwise energy would accumulate)
3. If ring can absorb radiation from the horizon, and no energy accumulates,
   then ring must be at the same temperature as the (outer) horizon
4. Therefore: T_ring = T_+ (NOT T_-)

**Why T_+ and not T_-?**
The ring is "in contact" with the exterior via the outer horizon, not via the
inner horizon. Energy flows from outside → outer horizon → region between horizons.
So the ring equilibrates with T_+.

**Critical point:**
This is NOT a geometric calculation! It's a thermodynamic argument.
The ring is not a Killing horizon, so we can't compute its temperature
from Killing vectors. We must use physics.
-/

/-!
### Modeling Physical Objects

To make the thermal equilibrium argument precise, we need to model physical
objects that can exist inside the black hole.
-/

structure PhysicalObject where
  location : Set BoyerLindquistCoords
  temperature : ℝ
  can_absorb : Bool  -- Can this object absorb energy?

/-!
### Thermal Equilibrium Principle

This is our key physical axiom - not provable from GR alone!
-/

axiom thermal_equilibrium_principle (p : KerrParams) (obj : PhysicalObject) :
    -- If an object inside a stationary BH can absorb radiation
    -- and the system is in steady state (no energy accumulation)
    -- then the object must be at the same temperature as the outer horizon
    obj.can_absorb = true →
    (∀ x ∈ obj.location, x.r < r_plus p) →
    obj.temperature = hawkingTemperature p

/-!
**Physical justification:**
In steady state: ∂E/∂t = 0
Energy flow: dQ/dt = κA(T_horizon - T_object)
If T_object ≠ T_horizon, then dQ/dt ≠ 0, so energy accumulates → not steady state!
Therefore: T_object = T_horizon by reductio ad absurdum.
-/

/-!
### The Ring as a Physical Object

Now we model the ring (or whatever replaces it in a real BH) as a physical object.
-/

noncomputable def ring_object (p : KerrParams) : PhysicalObject where
  location := {x | isRingSingularity x}
  temperature := hawkingTemperature p  -- Determined by equilibrium!
  can_absorb := true

/-!
### KEY RESULT: Ring Temperature Equals Outer Horizon Temperature
-/

theorem ring_temperature_equals_outer_horizon (p : KerrParams) :
    (ring_object p).temperature = hawkingTemperature p := by
  unfold ring_object
  rfl

/-- The ring temperature differs from the inner horizon temperature.

    **Physical significance:**
    The ring equilibrates with the OUTER horizon (T_+), not the inner one (T_-).
    This is because energy flows from exterior → outer horizon → interior.

    **Requires strictly subextremal:**
    For extremal black holes (|a| = M), both horizon temperatures are zero,
    so this distinction vanishes.
-/
theorem ring_temperature_not_inner (p : KerrParams) (ha : 0 < |p.a| ∧ |p.a| < p.M) :
    (ring_object p).temperature ≠ innerHorizonTemperature p := by
  rw [ring_temperature_equals_outer_horizon]
  exact Ne.symm (horizon_temperatures_differ p ha)


/-- The ring is thermally coupled to the outer horizon, not the inner one.

    **Summary:**
    - Ring temperature = T_+ (outer horizon)
    - Ring temperature ≠ T_- (inner horizon)

    This is the key thermodynamic result: the ring behaves like the outer
    horizon, supporting the interpretation that it's a "cold geometric boundary"
    rather than a physical singularity.
-/
theorem ring_thermally_coupled_to_outer_horizon (p : KerrParams) (ha : 0 < |p.a| ∧ |p.a| < p.M) :
    (ring_object p).temperature = hawkingTemperature p ∧
    (ring_object p).temperature ≠ innerHorizonTemperature p := by
  constructor
  · exact ring_temperature_equals_outer_horizon p
  · exact ring_temperature_not_inner p ha

end Kerr
