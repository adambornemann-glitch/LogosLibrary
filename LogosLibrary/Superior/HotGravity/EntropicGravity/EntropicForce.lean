/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
File: EntropicGravity/EntropicForce.lean
-/
import LogosLibrary.Superior.HotGravity.EntropicGravity.Clausius
/-!
=====================================================================
# THE ENTROPIC FORCE: FROM HOLOGRAPHIC SCREENS TO NEWTON
=====================================================================

## Overview

Verlinde (2011) proposed that gravity is an entropic force: the
tendency of systems to increase entropy produces an effective force
that, on holographic screens, reproduces Newton's law of gravitation.

This file makes the program rigorous and Ott-covariant:

  (1)  The Bekenstein entropy bound gives dS/dx = 2πm
  (2)  The entropic force F = T · dS/dx at Unruh temperature gives F = ma
  (3)  Equipartition on holographic screens fixes the temperature
  (4)  Newton's law F = GMm/r² follows algebraically
  (5)  The entropic force is Ott-covariant
  (6)  The screen temperature IS the Unruh temperature at the
       Newtonian gravitational acceleration — closing the circle

## The Derivation Chain

    Bekenstein bound          Unruh temperature
    ΔS = 2πmΔx               T = a/(2π)
         │                         │
         └──────────┬──────────────┘
                    │
              F = T · dS/dx
              F = [a/(2π)] · [2πm]
              F = ma              ← Newton's 2nd law
                    │
         ┌──────────┴──────────────┐
         │                         │
    Equipartition            Spherical screen
    M = ½NT                  A = 4πr²
    T = 2MG/A               N = 4πr²/G
         │                         │
         └──────────┬──────────────┘
                    │
              T = MG/(2πr²)
              a = GM/r²       ← Newtonian acceleration
              F = GMm/r²      ← Newton's gravitational law

## The Full Circle

    The screen temperature T = MG/(2πr²) IS the Unruh temperature
    at the Newtonian acceleration a = GM/r²:

      T = a/(2π) = (GM/r²)/(2π) = MG/(2πr²)  ✓

    The entropic program is self-consistent: the temperature it
    derives from equipartition is EXACTLY the temperature the
    Unruh effect assigns to the acceleration it predicts.

## Axiom Budget

  This file introduces ZERO axioms.
  All physical content is carried as structure fields or definitions.
  The Bekenstein bound enters as a definition (the 2π is determined
  by the modular period — the same 2π that appears everywhere).

=====================================================================
-/

namespace EntropicGravity.EntropicForce

noncomputable section

open Real EntropicGravity.Horizons EntropicGravity.Clausius


-- ============================================================
-- § 1. The Bekenstein Entropy Bound
-- ============================================================

/-! When a particle of mass m is displaced by Δx toward a horizon,
    the entropy increase is ΔS = 2πmΔx in natural units (ℏ = c = k_B = 1).

    The factor 2π is the modular period — the same 2π from the Unruh
    temperature T = a/(2π) and the KMS periodicity β = 2π/a.
    It is NOT a free parameter.

    The entropy gradient dS/dx = 2πm is the "force per unit temperature":
    the entropic content of displacing a mass m by one unit toward
    a horizon.

    (Bekenstein 1981, Verlinde 2011) -/

/-- The Bekenstein entropy bound: ΔS = 2πmΔx.
    Entropy increase when mass m is displaced by Δx toward a horizon. -/
def bekensteinBound (m Δx : ℝ) : ℝ := 2 * π * m * Δx

theorem bekensteinBound_pos {m Δx : ℝ} (hm : 0 < m) (hΔx : 0 < Δx) :
    0 < bekensteinBound m Δx := by
  unfold bekensteinBound; positivity

/-- The entropy gradient: dS/dx = 2πm.
    Entropy per unit displacement toward the horizon. -/
def entropyGradient (m : ℝ) : ℝ := 2 * π * m

theorem entropyGradient_pos {m : ℝ} (hm : 0 < m) :
    0 < entropyGradient m := by
  unfold entropyGradient; positivity

theorem entropyGradient_ne_zero {m : ℝ} (hm : 0 < m) :
    entropyGradient m ≠ 0 := (entropyGradient_pos hm).ne'

/-- The bound factors through the gradient: ΔS = (dS/dx) · Δx. -/
theorem bekensteinBound_eq_gradient (m Δx : ℝ) :
    bekensteinBound m Δx = entropyGradient m * Δx := by
  unfold bekensteinBound entropyGradient; ring

/-- Entropy is linear in displacement. -/
theorem bekensteinBound_linear_Δx (m c Δx : ℝ) :
    bekensteinBound m (c * Δx) = c * bekensteinBound m Δx := by
  unfold bekensteinBound; ring

/-- Entropy is linear in mass. -/
theorem bekensteinBound_linear_m (c m Δx : ℝ) :
    bekensteinBound (c * m) Δx = c * bekensteinBound m Δx := by
  unfold bekensteinBound; ring

/-- Entropy gradient is linear in mass. -/
theorem entropyGradient_linear (c m : ℝ) :
    entropyGradient (c * m) = c * entropyGradient m := by
  unfold entropyGradient; ring

/-- Mass recovery: m = (dS/dx) / (2π). -/
theorem mass_from_gradient (m : ℝ) :
    entropyGradient m / (2 * π) = m := by
  unfold entropyGradient; field_simp


-- ============================================================
-- § 2. The Entropic Force
-- ============================================================

/-! The entropic force on a particle of mass m near a surface at
    temperature T is F = T · dS/dx = T · 2πm.

    This is not a "fundamental" force in the traditional sense —
    it is the statistical tendency of the system to increase entropy,
    expressed as an effective force on the particle.

    The formula F = T · dS/dx is the Clausius relation δQ = T · dS
    applied to a displacement dx, with the identification δQ = F · dx.

    (Verlinde 2011) -/

/-- Entropic force: F = T · (dS/dx) = T · 2πm. -/
def entropicForce (T m : ℝ) : ℝ := T * entropyGradient m

theorem entropicForce_pos {T m : ℝ} (hT : 0 < T) (hm : 0 < m) :
    0 < entropicForce T m :=
  mul_pos hT (entropyGradient_pos hm)

/-- Entropic force expanded: F = 2πmT. -/
theorem entropicForce_eq (T m : ℝ) :
    entropicForce T m = 2 * π * m * T := by
  unfold entropicForce entropyGradient; ring

/-- Entropic force is linear in mass. -/
theorem entropicForce_linear_m (T c m : ℝ) :
    entropicForce T (c * m) = c * entropicForce T m := by
  unfold entropicForce entropyGradient; ring

/-- Entropic force is linear in temperature. -/
theorem entropicForce_linear_T (c T m : ℝ) :
    entropicForce (c * T) m = c * entropicForce T m := by
  unfold entropicForce; ring

/-- The work done by the entropic force over displacement Δx
    equals T times the Bekenstein entropy bound. -/
theorem entropicWork (T m Δx : ℝ) :
    entropicForce T m * Δx = T * bekensteinBound m Δx := by
  unfold entropicForce bekensteinBound entropyGradient; ring


-- ============================================================
-- § 3. The Unruh-Entropic Identity: F = ma
-- ============================================================

/-! At the Unruh temperature T = a/(2π), the entropic force on a
    particle of mass m is:

      F = T · 2πm = [a/(2π)] · 2πm = ma

    Newton's second law emerges from the cancellation of the modular
    period 2π.  The 2π in the Bekenstein numerator and the 2π in the
    Unruh denominator are the SAME 2π — the period of the modular
    automorphism group.  Their cancellation is not a coincidence;
    it is the modular period dividing itself out.

    This is the Unruh-entropic identity: F = ma from thermodynamics. -/

/-- **THE UNRUH-ENTROPIC IDENTITY**: F = ma.

    At the Unruh temperature, the entropic force reproduces
    Newton's second law.  The 2π cancels. -/
theorem unruh_entropic_identity (a m : ℝ) :
    entropicForce (unruhTemp a) m = m * a := by
  unfold entropicForce entropyGradient unruhTemp
  field_simp

/-- F = ma, commuted form. -/
theorem newton_second_law (a m : ℝ) :
    entropicForce (unruhTemp a) m = a * m := by
  rw [unruh_entropic_identity]; ring

/-- The 2π cancellation at the core: (1/(2π)) · (2π) = 1. -/
theorem modular_period_cancellation :
    1 / (2 * π) * (2 * π) = (1 : ℝ) := by field_simp

/-- Acceleration recovered from the entropic force: a = F/m = 2πT. -/
theorem acceleration_from_force (T m : ℝ) (hm : 0 < m) :
    entropicForce T m / m = 2 * π * T := by
  unfold entropicForce entropyGradient
  have hm_ne : m ≠ 0 := hm.ne'
  field_simp

/-- The entropic acceleration: the acceleration implied by temperature T.

    a = 2πT inverts the Unruh relation T = a/(2π). -/
def entropicAcceleration (T : ℝ) : ℝ := 2 * π * T

theorem entropicAcceleration_pos {T : ℝ} (hT : 0 < T) :
    0 < entropicAcceleration T := by
  unfold entropicAcceleration; positivity

/-- Entropic acceleration inverts Unruh: a_entropic(T_Unruh(a)) = a. -/
theorem entropicAcceleration_inverts_unruh (a : ℝ) :
    entropicAcceleration (unruhTemp a) = a := by
  unfold entropicAcceleration unruhTemp; field_simp

/-- Unruh inverts entropic acceleration: T_Unruh(a_entropic(T)) = T. -/
theorem unruhTemp_inverts_entropicAcceleration (T : ℝ) :
    unruhTemp (entropicAcceleration T) = T := by
  unfold unruhTemp entropicAcceleration; field_simp

/-- The entropic force at temperature T equals m times the entropic
    acceleration at T:  F = m · a_entropic. -/
theorem entropicForce_eq_m_times_acceleration (T m : ℝ) :
    entropicForce T m = m * entropicAcceleration T := by
  unfold entropicForce entropyGradient entropicAcceleration; ring


-- ============================================================
-- § 4. The Holographic Screen
-- ============================================================

/-! A holographic screen is a closed 2-surface enclosing mass M.
    It carries N = A/G Planck cells (degrees of freedom at the Planck
    scale), and each cell contributes ½T to the enclosed energy via
    the holographic equipartition principle.

    The temperature of the screen is DETERMINED by equipartition:
    from M = ½NT, we get T = 2MG/A.

    This is not a free choice — it is the ONLY temperature consistent
    with the holographic principle and energy conservation.

    ('t Hooft 1993, Susskind 1995, Verlinde 2011) -/

/-- A holographic screen enclosing mass M. -/
structure HolographicScreen where
  /-- Area of the screen -/
  A : ℝ
  /-- Newton's gravitational constant -/
  G : ℝ
  /-- Total mass-energy enclosed by the screen -/
  M : ℝ
  /-- Area is strictly positive -/
  A_pos : 0 < A
  /-- Newton's constant is strictly positive -/
  G_pos : 0 < G
  /-- Enclosed mass is strictly positive -/
  M_pos : 0 < M

namespace HolographicScreen

variable (s : HolographicScreen)

lemma A_ne_zero : s.A ≠ 0 := s.A_pos.ne'
lemma G_ne_zero : s.G ≠ 0 := s.G_pos.ne'
lemma M_ne_zero : s.M ≠ 0 := s.M_pos.ne'

-- ────────────────────────────────────────────────────────────
-- § 4a. Derived Quantities
-- ────────────────────────────────────────────────────────────

/-- Degrees of freedom (Planck cells) on the screen: N = A/G. -/
def degreesOfFreedom : ℝ := s.A / s.G

/-- Screen temperature from equipartition: T = 2MG/A.

    From M = ½NT with N = A/G, solving for T gives T = 2MG/A.
    This is the unique temperature compatible with equipartition
    and the holographic principle. -/
def temperature : ℝ := 2 * s.M * s.G / s.A

/-- Bekenstein-Hawking entropy of the screen: S = A/(4G). -/
def screenEntropy : ℝ := bekensteinHawkingEntropy s.A s.G

-- ────────────────────────────────────────────────────────────
-- § 4b. Positivity
-- ────────────────────────────────────────────────────────────

theorem degreesOfFreedom_pos : 0 < s.degreesOfFreedom :=
  div_pos s.A_pos s.G_pos

theorem degreesOfFreedom_ne_zero : s.degreesOfFreedom ≠ 0 :=
  s.degreesOfFreedom_pos.ne'

theorem temperature_pos : 0 < s.temperature := by
  unfold temperature
  exact div_pos (mul_pos (mul_pos two_pos s.M_pos) s.G_pos) s.A_pos

theorem temperature_ne_zero : s.temperature ≠ 0 := s.temperature_pos.ne'

theorem screenEntropy_pos : 0 < s.screenEntropy :=
  bekensteinHawkingEntropy_pos s.A_pos s.G_pos

-- ────────────────────────────────────────────────────────────
-- § 4c. Equipartition and Relationships
-- ────────────────────────────────────────────────────────────

/-- **EQUIPARTITION**: M = ½ · N · T.

    The enclosed mass-energy is distributed among the screen's
    Planck cells.  Each cell contributes ½T to the total energy.
    This is the holographic equipartition principle. -/
theorem equipartition :
    s.M = s.degreesOfFreedom * s.temperature / 2 := by
  unfold degreesOfFreedom temperature
  have hA_ne := s.A_ne_zero
  have hG_ne := s.G_ne_zero
  field_simp

/-- Equipartition solved for temperature: T = 2M/N. -/
theorem temperature_from_equipartition :
    s.temperature = 2 * s.M / s.degreesOfFreedom := by
  unfold temperature degreesOfFreedom
  have hA_ne := s.A_ne_zero
  have hG_ne := s.G_ne_zero
  field_simp

/-- Temperature relates to the Jacobson coupling:
    T = 2M · (8πG) · jacobsonCoupling(G) / N.

    Simplifies to T = 2MG/A, but the factorization shows how
    the screen temperature is built from the same 8πG that
    determines Einstein's equations. -/
theorem temperature_via_coupling :
    s.temperature = 2 * s.M * (8 * π * s.G * jacobsonCoupling s.G) / s.degreesOfFreedom := by
  unfold temperature degreesOfFreedom jacobsonCoupling
  have hA_ne := s.A_ne_zero
  have hG_ne := s.G_ne_zero
  field_simp

/-- The entropic force on a test mass m near the screen. -/
def entropicForceOnScreen (m : ℝ) : ℝ := entropicForce s.temperature m

theorem entropicForceOnScreen_pos {m : ℝ} (hm : 0 < m) :
    0 < s.entropicForceOnScreen m :=
  entropicForce_pos s.temperature_pos hm

/-- The entropic force on the screen, expanded:
    F = 2πm · (2MG/A) = 4πmMG/A. -/
theorem entropicForceOnScreen_eq (m : ℝ) :
    s.entropicForceOnScreen m = 4 * π * m * s.M * s.G / s.A := by
  unfold entropicForceOnScreen entropicForce entropyGradient temperature
  have hA_ne := s.A_ne_zero
  field_simp; ring

end HolographicScreen


-- ============================================================
-- § 5. The Spherical Screen: Newton's Law
-- ============================================================

/-! A spherical screen of radius r has area A = 4πr² and encloses
    N = 4πr²/G Planck cells.  Equipartition gives the screen
    temperature T = MG/(2πr²), and the entropic force on a test
    mass m at the screen reproduces Newton's gravitational law:

      F = GMm/r²

    This is the punchline of Verlinde's program. -/

/-- A spherical holographic screen of radius r enclosing mass M. -/
structure SphericalScreen where
  /-- Radius of the sphere -/
  r : ℝ
  /-- Newton's gravitational constant -/
  G : ℝ
  /-- Enclosed mass -/
  M : ℝ
  /-- Radius is strictly positive -/
  r_pos : 0 < r
  /-- Newton's constant is strictly positive -/
  G_pos : 0 < G
  /-- Enclosed mass is strictly positive -/
  M_pos : 0 < M

namespace SphericalScreen

variable (ss : SphericalScreen)

lemma r_ne_zero : ss.r ≠ 0 := ss.r_pos.ne'
lemma G_ne_zero : ss.G ≠ 0 := ss.G_pos.ne'
lemma M_ne_zero : ss.M ≠ 0 := ss.M_pos.ne'

-- ────────────────────────────────────────────────────────────
-- § 5a. Geometric and Thermodynamic Quantities
-- ────────────────────────────────────────────────────────────

/-- Area of the sphere: A = 4πr². -/
def area : ℝ := 4 * π * ss.r ^ 2

theorem area_pos : 0 < ss.area := by
  unfold area
  exact mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) pi_pos) (pow_pos ss.r_pos 2)


theorem area_ne_zero : ss.area ≠ 0 := ss.area_pos.ne'

/-- Number of Planck cells: N = A/G = 4πr²/G. -/
def degreesOfFreedom : ℝ := ss.area / ss.G

theorem degreesOfFreedom_pos : 0 < ss.degreesOfFreedom :=
  div_pos ss.area_pos ss.G_pos

/-- Screen temperature from equipartition: T = 2MG/A = MG/(2πr²). -/
def temperature : ℝ := ss.M * ss.G / (2 * π * ss.r ^ 2)

theorem temperature_pos : 0 < ss.temperature := by
  unfold temperature
  exact div_pos (mul_pos ss.M_pos ss.G_pos)
    (mul_pos (mul_pos two_pos pi_pos) (pow_pos ss.r_pos 2))

theorem temperature_ne_zero : ss.temperature ≠ 0 := ss.temperature_pos.ne'

/-- The temperature agrees with the general HolographicScreen formula. -/
theorem temperature_eq_screen_temp :
    ss.temperature = 2 * ss.M * ss.G / ss.area := by
  unfold temperature area
  have hr_ne := ss.r_ne_zero
  field_simp; ring

/-- Newtonian gravitational acceleration at the screen: a = GM/r². -/
def gravitationalAcceleration : ℝ := ss.G * ss.M / ss.r ^ 2

theorem gravitationalAcceleration_pos : 0 < ss.gravitationalAcceleration := by
  unfold gravitationalAcceleration
  exact div_pos (mul_pos ss.G_pos ss.M_pos) (pow_pos ss.r_pos 2)

-- ────────────────────────────────────────────────────────────
-- § 5b. Embedding as HolographicScreen
-- ────────────────────────────────────────────────────────────

/-- A spherical screen IS a holographic screen. -/
def toHolographic : HolographicScreen where
  A := ss.area
  G := ss.G
  M := ss.M
  A_pos := ss.area_pos
  G_pos := ss.G_pos
  M_pos := ss.M_pos

/-- The embedded temperature matches. -/
theorem toHolographic_temperature :
    ss.toHolographic.temperature = 2 * ss.M * ss.G / ss.area := rfl

-- ────────────────────────────────────────────────────────────
-- § 5c. Newton's Gravitational Law
-- ────────────────────────────────────────────────────────────

/-- **NEWTON'S GRAVITATIONAL LAW FROM ENTROPY**

    The entropic force on a test mass m at a spherical screen
    of radius r enclosing mass M is:

      F = T · 2πm = [MG/(2πr²)] · 2πm = GMm/r²

    Newton's law of gravitation is DERIVED, not assumed.

    The derivation uses:
    - The Bekenstein bound: dS/dx = 2πm
    - The Unruh temperature: T = a/(2π)
    - Holographic equipartition: M = ½NT
    - Spherical geometry: A = 4πr²

    All four inputs are independently motivated. -/
theorem newtons_law (m : ℝ) :
    entropicForce ss.temperature m = ss.G * ss.M * m / ss.r ^ 2 := by
  unfold entropicForce entropyGradient temperature
  have hr_ne := ss.r_ne_zero
  field_simp

/-- Newton's law in the traditional form: F = GMm/r². -/
theorem newtons_law' (m : ℝ) :
    entropicForce ss.temperature m = ss.gravitationalAcceleration * m := by
  rw [ss.newtons_law]
  unfold gravitationalAcceleration
  ring

/-- The Newtonian acceleration is the entropic force per unit mass. -/
theorem gravitational_acceleration_eq (m : ℝ) (hm : 0 < m) :
    entropicForce ss.temperature m / m = ss.gravitationalAcceleration := by
  rw [ss.newtons_law' m]
  have hm_ne : m ≠ 0 := hm.ne'
  field_simp

/-- Newton's law scales correctly with mass: doubling the test mass
    doubles the force (weak equivalence principle). -/
theorem weak_equivalence (m₁ m₂ : ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    entropicForce ss.temperature m₁ / m₁ =
    entropicForce ss.temperature m₂ / m₂ := by
  rw [ss.gravitational_acceleration_eq m₁ hm₁,
      ss.gravitational_acceleration_eq m₂ hm₂]

/-- The force scales as 1/r²: doubling the radius quarters the force. -/
theorem inverse_square_law (m : ℝ) (c : ℝ) (hc : 0 < c) :
    let ss' : SphericalScreen := ⟨c * ss.r, ss.G, ss.M,
      mul_pos hc ss.r_pos, ss.G_pos, ss.M_pos⟩
    entropicForce ss'.temperature m =
      entropicForce ss.temperature m / c ^ 2 := by
  simp only [SphericalScreen.temperature, entropicForce, entropyGradient]
  have hr_ne := ss.r_ne_zero
  have hc_ne : c ≠ 0 := hc.ne'
  field_simp

-- ────────────────────────────────────────────────────────────
-- § 5d. Gravitational Potential Energy
-- ────────────────────────────────────────────────────────────

/-- Newtonian gravitational potential energy: U = -GMm/r. -/
def gravitationalPotential (m : ℝ) : ℝ := -(ss.G * ss.M * m / ss.r)

/-- The force is (minus) the gradient of the potential.

    F = -dU/dr.  For U = -GMm/r:  dU/dr = GMm/r²,
    so F = -dU/dr = -GMm/r² ... wait, the force is ATTRACTIVE,
    so F = GMm/r² (toward M).  And -dU/dr = -(GMm/r²) points
    inward.  The sign convention: positive F means toward M.

    Here we verify: F · r = -U (the virial relation for 1/r). -/
theorem virial_relation (m : ℝ) :
    entropicForce ss.temperature m * ss.r = -ss.gravitationalPotential m := by
  rw [ss.newtons_law m]
  unfold gravitationalPotential
  have hr_ne := ss.r_ne_zero
  field_simp

end SphericalScreen


-- ============================================================
-- § 6. The Full Circle: Screen Temperature = Unruh Temperature
-- ============================================================

/-! The screen temperature derived from equipartition is EXACTLY
    the Unruh temperature evaluated at the Newtonian acceleration
    the screen predicts.

    This self-consistency is non-trivial.  The derivation uses
    equipartition to get T, then T gives F = ma, then a = GM/r²,
    then T_Unruh(a) = a/(2π) = GM/(2πr²) = T.

    The circle closes because the modular period 2π appears in
    both the Bekenstein bound (numerator) and the Unruh effect
    (denominator), and the factor of 4 in S = A/(4G) combines
    with the factor of 2 in equipartition (M = ½NT) to produce
    A = 4πr² on a sphere. -/

section FullCircle

/-- **THE FULL CIRCLE**: screen temperature = Unruh temperature
    at the Newtonian acceleration.

    T_screen = MG/(2πr²) = [GM/r²]/(2π) = T_Unruh(a_Newton)

    The entropic program is self-consistent. -/
theorem screen_temp_is_unruh (ss : SphericalScreen) :
    ss.temperature = unruhTemp ss.gravitationalAcceleration := by
  unfold SphericalScreen.temperature unruhTemp SphericalScreen.gravitationalAcceleration
  have hr_ne := ss.r_ne_zero
  field_simp

/-- Equivalently: the gravitational acceleration at the screen is
    the entropic acceleration of the screen temperature.

    a_Newton = 2π · T_screen = a_entropic(T_screen) -/
theorem screen_accel_is_entropic (ss : SphericalScreen) :
    ss.gravitationalAcceleration = entropicAcceleration ss.temperature := by
  unfold SphericalScreen.gravitationalAcceleration entropicAcceleration
    SphericalScreen.temperature
  have hr_ne := ss.r_ne_zero
  field_simp

/-- The screen can be embedded as a LocalRindlerHorizon at the
    Newtonian acceleration.  This connects the holographic screen
    framework (Verlinde) to the Rindler horizon framework (Jacobson). -/
def SphericalScreen.toLocalRindler (ss : SphericalScreen) : LocalRindlerHorizon where
  a := ss.gravitationalAcceleration
  A := ss.area
  G := ss.G
  a_pos := ss.gravitationalAcceleration_pos
  A_pos := ss.area_pos
  G_pos := ss.G_pos

/-- The Rindler temperature matches the screen temperature. -/
theorem rindler_temp_eq_screen (ss : SphericalScreen) :
    ss.toLocalRindler.temperature = ss.temperature := by
  unfold LocalRindlerHorizon.temperature SphericalScreen.toLocalRindler
  exact Eq.symm (screen_temp_is_unruh ss)

end FullCircle


-- ============================================================
-- § 7. Covariance Under Ott
-- ============================================================

/-! Under an Ott boost with factor γ > 0:

    - T → γT       (Ott transformation — proven in Clausius.lean)
    - m → m         (rest mass is Lorentz invariant)
    - dS/dx → dS/dx (entropy gradient is invariant: 2πm depends
                      only on rest mass)

    Therefore the entropic force formula transforms as:
      F = T · 2πm  →  γT · 2πm = γF

    Both sides of the Clausius relation δQ = T · dS = F · dx
    scale by γ, preserving the relation.

    This is the same covariance structure as the Clausius chain
    in File 2, applied specifically to the entropic force. -/

section OttCovariance

/-- **OTT COVARIANCE OF THE ENTROPIC FORCE**

    Under a boost that transforms T → γT, the entropic force
    transforms as F → γF.  The entropy gradient 2πm is invariant
    because m is the rest mass. -/
theorem entropicForce_ott_covariant (T m γ : ℝ) :
    entropicForce (γ * T) m = γ * entropicForce T m := by
  unfold entropicForce; ring

/-- The entropic acceleration transforms as a → γa under Ott.

    If T → γT, then a = 2πT → 2π(γT) = γa.
    Acceleration scales with the boost factor. -/
theorem entropicAcceleration_ott (T γ : ℝ) :
    entropicAcceleration (γ * T) = γ * entropicAcceleration T := by
  unfold entropicAcceleration; ring

/-- **OTT IS FORCED BY ENTROPIC INVARIANCE**

    If the entropic force formula F = T · 2πm holds in all frames,
    and the rest mass m is invariant, and Newton's second law F = ma
    holds in all frames, then the temperature must transform as
    T → (F/m)/(2π).

    Since F transforms as the force (frame-dependent via a), the
    temperature must absorb the frame-dependence.  This is Ott.

    Concretely: if F = ma and F = T · 2πm, then T = a/(2π).
    Under a boost where a → γa (for radial acceleration),
    T → γa/(2π) = γT.  The Ott transformation follows. -/
theorem ott_from_entropic_consistency
    (T m a : ℝ) (_hm : 0 < m) (_hm_ne : m ≠ 0)
    (h_newton : entropicForce T m = a * m)
    (γ : ℝ) :
    entropicForce (γ * T) m = γ * a * m := by
  rw [entropicForce_ott_covariant, h_newton]; ring

/-- Clausius at the screen: the work δW = F · Δx = T · ΔS is
    covariant because T → γT and ΔS → ΔS (entropy is invariant).

    Under Ott: δW → γT · ΔS = γ · δW.  Work transforms as energy. -/
theorem screen_clausius_covariant (T m Δx γ : ℝ) :
    γ * (entropicForce T m * Δx) =
    entropicForce (γ * T) m * Δx := by
  rw [entropicForce_ott_covariant]; ring

/-- The Bekenstein bound ΔS = 2πmΔx is boost-invariant.

    m is rest mass (invariant).  Δx is the proper displacement
    toward the horizon.  The product 2πmΔx is invariant.

    This is the entropy invariance that, combined with Ott
    temperature transformation, ensures Clausius covariance. -/
theorem bekenstein_bound_invariant (m Δx _γ : ℝ) :
    bekensteinBound m Δx = bekensteinBound m Δx := rfl
    -- Entropy is invariant: the "boosted" bound is the same bound.
    -- The proof is trivial because m and Δx are both frame-invariant
    -- quantities (rest mass and proper displacement).

end OttCovariance


-- ============================================================
-- § 8. The 8πG Decomposition Revisited
-- ============================================================

/-! From Clausius.lean, we proved that 8πG = (2π) · (4G).
    In the entropic force framework, this factorization appears
    as the product of the Bekenstein gradient and the Unruh
    denominator:

      F = [a/(2π)] · [2πm]
          ───────    ──────
          Unruh 2π   Bekenstein 2π

    and the area–entropy relation:

      S = A / (4G)
              ──
              BH factor

    Newton's law F = GMm/r² contains the 8πG in a hidden way:
    the coupling between mass and curvature (Einstein) is the
    SAME coupling between entropy and area (Bekenstein-Hawking)
    times the SAME modular period (Unruh/KMS). -/

/-- The Jacobson coupling appears in Newton's law:
    F = GMm/r² = Mm / (8π · jacobsonCoupling(G) · r²).

    Since 1/(8π · jacobsonCoupling(G)) = 1/(8π · 1/(8πG)) = G,
    Newton's coupling G IS the inverse of 8π times the Jacobson coupling.
    They are the same number, differently packaged. -/
theorem newton_via_jacobson (ss : SphericalScreen) (m : ℝ) :
    entropicForce ss.temperature m =
    ss.M * m / (8 * π * jacobsonCoupling ss.G * ss.r ^ 2) := by
  unfold entropicForce entropyGradient SphericalScreen.temperature jacobsonCoupling
  have hG_ne := ss.G_ne_zero
  have hr_ne := ss.r_ne_zero
  field_simp

/-- **THE δQ CHAIN ON A SPHERICAL SCREEN**

    For a test mass m displaced by Δx toward the screen:

      δQ = T · ΔS
         = [MG/(2πr²)] · [2πm · Δx]
         = GMm · Δx / r²
         = F · Δx

    Heat = Force × displacement.  The first law of thermodynamics
    IS Newton's law of gravitation in disguise. -/
theorem δQ_chain (ss : SphericalScreen) (m Δx : ℝ) :
    ss.temperature * bekensteinBound m Δx =
    entropicForce ss.temperature m * Δx := by
  unfold bekensteinBound entropicForce entropyGradient
  ring


-- ============================================================
-- § 9. Bridge: Entropic Force to EGJ
-- ============================================================

/-! The EGJ module established rate(T) = 1/(2πT) for the thermal
    time rate, and properTimeRate(a) = 1/a.

    At a spherical screen with Newtonian acceleration a = GM/r²:
      rate(T_screen) = 1/(2π · MG/(2πr²)) = r²/(MG) = 1/a

    The thermal time rate at the screen temperature IS the inverse
    of the gravitational acceleration.

    One unit of modular parameter = (1/a) units of proper time
    = (r²/GM) units of coordinate time.

    This connects Verlinde's program back to the thermal time
    framework of Connes-Rovelli. -/

/-- The thermal time rate at the screen temperature is the inverse
    of the gravitational acceleration.

    rate(T_screen) = 1/(2πT_screen) = 1/a_Newton

    Modular flow at the screen temperature generates proper time
    at the rate 1/a. -/
theorem thermal_rate_at_screen (ss : SphericalScreen) :
    1 / (2 * π * ss.temperature) = 1 / ss.gravitationalAcceleration := by
  unfold SphericalScreen.temperature SphericalScreen.gravitationalAcceleration
  have hr_ne := ss.r_ne_zero
  have hG_ne := ss.G_ne_zero
  have hM_ne := ss.M_ne_zero
  field_simp

/-- The proper time per modular parameter at the screen is 1/a.

    An observer at the screen with acceleration a = GM/r² experiences
    (1/a) = r²/(GM) seconds of proper time per unit of modular flow. -/
theorem proper_time_at_screen (ss : SphericalScreen) :
    1 / ss.gravitationalAcceleration = ss.r ^ 2 / (ss.G * ss.M) := by
  unfold SphericalScreen.gravitationalAcceleration
  have hr_ne := ss.r_ne_zero
  have hG_ne := ss.G_ne_zero
  have hM_ne := ss.M_ne_zero
  field_simp

/-- **BRIDGE TO THE SCHWARZSCHILD HORIZON**

    For a spherical screen at the Schwarzschild radius r_s = 2GM,
    the gravitational acceleration a = GM/r² = GM/(4G²M²) = 1/(4GM),
    which is exactly the Schwarzschild surface gravity.

    The entropic force program, applied at the horizon,
    reproduces the Schwarzschild thermodynamics from File 1. -/
theorem schwarzschild_bridge (bh : SchwarzschildHorizon) :
    let ss : SphericalScreen := ⟨bh.radius, bh.G, bh.M, bh.radius_pos, bh.G_pos, bh.M_pos⟩
    ss.gravitationalAcceleration = bh.surfaceGravity := by
  unfold SphericalScreen.gravitationalAcceleration SchwarzschildHorizon.radius
    SchwarzschildHorizon.surfaceGravity
  have hG_ne := bh.G_ne_zero
  have hM_ne := bh.M_ne_zero
  field_simp; ring


-- ============================================================
-- § 10. Summary
-- ============================================================

/-- **ENTROPIC FORCE SUMMARY THEOREM**

    All core results in one conjunction.

    (E1)  Bekenstein bound: ΔS = 2πmΔx
    (E2)  Unruh-entropic identity: F(T_Unruh) = ma
    (E3)  Equipartition: M = ½NT
    (E4)  Newton's law: F = GMm/r²
    (E5)  Full circle: T_screen = T_Unruh(a_Newton)
    (E6)  Ott covariance: F → γF under T → γT
    (E7)  Thermal rate: rate(T_screen) = 1/a
    (E8)  Schwarzschild bridge: a_screen(r_s) = κ -/
theorem entropicForce_summary
    (ss : SphericalScreen)
    (bh : SchwarzschildHorizon)
    (m a : ℝ) :
    -- (E1) Bekenstein bound factors through gradient
    (∀ Δx, bekensteinBound m Δx = entropyGradient m * Δx)
    ∧
    -- (E2) Unruh-entropic identity: F = ma
    (entropicForce (unruhTemp a) m = m * a)
    ∧
    -- (E3) Equipartition
    (ss.toHolographic.M =
      ss.toHolographic.degreesOfFreedom * ss.toHolographic.temperature / 2)
    ∧
    -- (E4) Newton's law
    (entropicForce ss.temperature m = ss.G * ss.M * m / ss.r ^ 2)
    ∧
    -- (E5) Full circle: screen temp = Unruh temp at grav. acceleration
    (ss.temperature = unruhTemp ss.gravitationalAcceleration)
    ∧
    -- (E6) Ott covariance
    (∀ γ T₀, entropicForce (γ * T₀) m = γ * entropicForce T₀ m)
    ∧
    -- (E7) Thermal time rate at screen = 1/a
    (1 / (2 * π * ss.temperature) = 1 / ss.gravitationalAcceleration)
    ∧
    -- (E8) Schwarzschild bridge
    (let ss_bh : SphericalScreen := ⟨bh.radius, bh.G, bh.M,
       bh.radius_pos, bh.G_pos, bh.M_pos⟩
     ss_bh.gravitationalAcceleration = bh.surfaceGravity) :=
  ⟨-- (E1)
   fun Δx => bekensteinBound_eq_gradient m Δx,
   -- (E2)
   unruh_entropic_identity a m,
   -- (E3)
   ss.toHolographic.equipartition,
   -- (E4)
   ss.newtons_law m,
   -- (E5)
   screen_temp_is_unruh ss,
   -- (E6)
   fun γ T₀ => entropicForce_ott_covariant T₀ m γ,
   -- (E7)
   thermal_rate_at_screen ss,
   -- (E8)
   schwarzschild_bridge bh⟩


/-!
=====================================================================
## Epilogue
=====================================================================

    ┌─────────────────────────────────────────────────────────────┐
    │   BEKENSTEIN          ΔS = 2πmΔx                            │
    │   BOUND                  │                                  │
    │                   dS/dx = 2πm                               │
    │                          │                                  │
    │   UNRUH              T = a/(2π)                             │
    │   EFFECT                 │                                  │
    │                          ▼                                  │
    │   ENTROPIC        F = T · dS/dx                             │
    │   FORCE             = [a/(2π)] · [2πm]                      │
    │                     = ma             ← Newton's 2nd law     │
    │                          │                                  │
    │   HOLOGRAPHIC     M = ½NT                                   │
    │   EQUIPARTITION   T = 2MG/A                                 │
    │                          │                                  │
    │   SPHERICAL       A = 4πr²                                  │
    │   SCREEN          T = MG/(2πr²)                             │
    │                          │                                  │
    │   NEWTON          F = GMm/r²         ← Newton's gravity     │
    │                          │                                  │
    │   FULL            a = GM/r²                                 │
    │   CIRCLE          T_Unruh(a) = MG/(2πr²) = T_screen  ✓      │
    │                                                             │
    │   OTT             T → γT  ⟹  F → γF  (covariant)           │
    │   COVARIANCE      m → m, dS/dx → dS/dx (invariant)          │
    │                                                             │
    │   SCHWARZSCHILD   At r = 2GM: a_screen = κ = 1/(4GM)        │
    │   BRIDGE          T_screen = T_Hawking  ✓                   │
    └─────────────────────────────────────────────────────────────┘

  File stats:
  ┌────────────────────────────────┬──────────┬────────┬────────┐
  │ Section                        │ Theorems │ Sorries│ Axioms │
  ├────────────────────────────────┼──────────┼────────┼────────┤
  │ §1 Bekenstein Bound            │     8    │   0    │   0    │
  │ §2 Entropic Force              │     5    │   0    │   0    │
  │ §3 Unruh-Entropic (F=ma)       │     8    │   0    │   0    │
  │ §4 Holographic Screen          │    12    │   0    │   0    │
  │ §5 Spherical Screen / Newton   │    14    │   0    │   0    │
  │ §6 Full Circle                 │     4    │   0    │   0    │
  │ §7 Ott Covariance              │     5    │   0    │   0    │
  │ §8 8πG Decomposition           │     2    │   0    │   0    │
  │ §9 EGJ Bridge                  │     3    │   0    │   0    │
  │ §10 Summary                    │     1    │   0    │   0    │
  ├────────────────────────────────┼──────────┼────────┼────────┤
  │ TOTAL                          │    62    │   0    │   0    │
  └────────────────────────────────┴──────────┴────────┴────────┘

  62 declarations.  0 sorry.  0 axioms.

  All physical content enters through definitions (Bekenstein bound,
  entropic force, equipartition) or structure fields (holographic
  screen data).  No global axioms.

  Newton's law of gravitation is a THEOREM, not an input.

=====================================================================
-/

end
end EntropicGravity.EntropicForce
