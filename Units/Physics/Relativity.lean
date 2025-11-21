-- Relativity.lean -- Special and General Relativity Units
import LogosLibrary.Units.Core.SI  -- Import base SI units
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic


namespace Units.Physics.Relativity

/-
================================================================================
SPECIAL RELATIVITY UNITS LIBRARY
================================================================================

This module provides units and structures specific to special relativity,
maintaining dimensional correctness and type safety throughout relativistic
calculations.

## FUNDAMENTAL PRINCIPLE
The speed of light c is the fundamental constant that connects space and time.
In natural units, we often set c = 1, but here we maintain explicit dimensions
for pedagogical clarity and type safety.

## KEY CONCEPTS ENCODED
- Lorentz invariance through proper types
- Four-vector structure with metric signature (-,+,+,+) or (+,-,-,-)
- Distinction between proper time τ and coordinate time t
- Energy-momentum relation E² = (pc)² + (mc²)²
- Relativistic composition of velocities
- Spacetime intervals (timelike, spacelike, lightlike)

## DESIGN DECISIONS
- Explicit c factors maintained (no natural units by default)
- Four-vectors as structures, not tuples, for type safety
- Separate types for proper vs coordinate quantities
- Validation functions to ensure v < c
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Units.SI

/--
================================================================================================
   Fundamental Constants
================================================================================================
-/
def c_F : Float := 299792458.0  -- Speed of light in m/s (exact by definition)
def c_Q : ℚ := 299792458        -- Exact rational
noncomputable def c_R : ℝ := 299792458  -- For proofs

-- Planck constant (for E = hν relations)
def h_F : Float := 6.62607015e-34  -- J⋅s (exact by definition)
def hbar_F : Float := 1.054571817e-34  -- ħ = h/2π

-- Electron rest mass (for examples)
def m_e_F : Float := 9.1093837015e-31  -- kg

/--
================================================================================================
   Relativistic Velocity and Beta Factor
================================================================================================
-/
-- Velocity as fraction of c (dimensionless β = v/c)
structure Beta_F where
  val : Float
  --valid : val < 1.0 := by trivial  -- Can't exceed c
  deriving Repr, BEq, Inhabited

structure Beta_Q where
  val : ℚ
  --valid : val < 1 := by trivial
  deriving Repr, BEq, DecidableEq, Inhabited

structure Beta_R where
  val : ℝ
  deriving Inhabited

-- Rapidity (additive under boosts, φ = arctanh(β))
structure Rapidity_F where val : Float deriving Repr, BEq, Inhabited
structure Rapidity_Q where val : ℚ deriving Repr, BEq, DecidableEq, Inhabited
structure Rapidity_R where val : ℝ deriving Inhabited

/--
================================================================================================
   Lorentz Factor γ = 1/√(1 - v²/c²)
================================================================================================
-/
structure LorentzFactor_F where
  val : Float
  --valid : val ≥ 1.0 := by trivial  -- γ ≥ 1 always
  deriving Repr, BEq, Inhabited

structure LorentzFactor_Q where
  val : ℚ
  --valid : val ≥ 1 := by trivial
  deriving Repr, BEq, DecidableEq, Inhabited

structure LorentzFactor_R where
  val : ℝ
  deriving Inhabited

/--
================================================================================================
   Proper Time vs Coordinate Time
================================================================================================
-/
-- Proper time τ (invariant, measured by comoving clock)
structure ProperTime_F where val : Float deriving Repr, BEq, Inhabited
structure ProperTime_Q where val : ℚ deriving Repr, BEq, DecidableEq, Inhabited
structure ProperTime_R where val : ℝ deriving Inhabited

-- For clarity in relativistic contexts (though technically same as Second)
abbrev CoordinateTime_F := Second_F
abbrev CoordinateTime_Q := Second_Q
abbrev CoordinateTime_R := Second_R

/--
================================================================================================
   Four-Vectors (Contravariant)
================================================================================================
Using signature (-,+,+,+) where timelike intervals are negative
Could also use (+,-,-,-) by changing metric tensor
-/

structure FourPosition_F where
  t : Float  -- ct component (has dimension of length)
  x : Float
  y : Float
  z : Float
  deriving Repr, BEq, Inhabited

structure FourPosition_Q where
  t : ℚ
  x : ℚ
  y : ℚ
  z : ℚ
  deriving Repr, BEq, DecidableEq, Inhabited

structure FourPosition_R where
  t : ℝ
  x : ℝ
  y : ℝ
  z : ℝ
  deriving Inhabited

-- Four-velocity U^μ = γ(c, v)
structure FourVelocity_F where
  u0 : Float  -- γc
  u1 : Float  -- γv_x
  u2 : Float  -- γv_y
  u3 : Float  -- γv_z
  deriving Repr, BEq, Inhabited

structure FourVelocity_Q where
  u0 : ℚ
  u1 : ℚ
  u2 : ℚ
  u3 : ℚ
  deriving Repr, BEq, DecidableEq, Inhabited

structure FourVelocity_R where
  u0 : ℝ
  u1 : ℝ
  u2 : ℝ
  u3 : ℝ
  deriving Inhabited

-- Four-momentum P^μ = (E/c, p)
structure FourMomentum_F where
  E_over_c : Float  -- Energy/c (has dimension of momentum)
  px : Float
  py : Float
  pz : Float
  deriving Repr, BEq, Inhabited

structure FourMomentum_Q where
  E_over_c : ℚ
  px : ℚ
  py : ℚ
  pz : ℚ
  deriving Repr, BEq, DecidableEq, Inhabited

structure FourMomentum_R where
  E_over_c : ℝ
  px : ℝ
  py : ℝ
  pz : ℝ
  deriving Inhabited

/--
================================================================================================
   Spacetime Interval
================================================================================================
-/
-- The invariant interval s² = -(cΔt)² + Δx² + Δy² + Δz²
structure SpacetimeInterval_F where
  val : Float  -- Can be negative (timelike), positive (spacelike), or zero (lightlike)
  deriving Repr, BEq, Inhabited

structure SpacetimeInterval_Q where
  val : ℚ
  deriving Repr, BEq, DecidableEq, Inhabited

structure SpacetimeInterval_R where
  val : ℝ
  deriving Inhabited

-- Classification of intervals
inductive IntervalType where
  | Timelike    -- s² < 0, events can be causally connected
  | Spacelike   -- s² > 0, events cannot be causally connected
  | Lightlike   -- s² = 0, null interval, light path
  deriving Repr, BEq, DecidableEq, Inhabited

/--
================================================================================================
   Relativistic Mass and Energy
================================================================================================
-/
-- Rest mass (invariant mass)
structure RestMass_F where val : Float deriving Repr, BEq, Inhabited
structure RestMass_Q where val : ℚ deriving Repr, BEq, DecidableEq, Inhabited
structure RestMass_R where val : ℝ deriving Inhabited

-- Relativistic mass (γm₀) - pedagogical but deprecated in modern physics
structure RelativisticMass_F where val : Float deriving Repr, BEq, Inhabited
structure RelativisticMass_Q where val : ℚ deriving Repr, BEq, DecidableEq, Inhabited
structure RelativisticMass_R where val : ℝ deriving Inhabited

-- Rest energy E₀ = mc²
structure RestEnergy_F where val : Float deriving Repr, BEq, Inhabited
structure RestEnergy_Q where val : ℚ deriving Repr, BEq, DecidableEq, Inhabited
structure RestEnergy_R where val : ℝ deriving Inhabited

-- Total relativistic energy E = γmc²
structure RelativisticEnergy_F where val : Float deriving Repr, BEq, Inhabited
structure RelativisticEnergy_Q where val : ℚ deriving Repr, BEq, DecidableEq, Inhabited
structure RelativisticEnergy_R where val : ℝ deriving Inhabited

-- Kinetic energy T = (γ - 1)mc²
structure RelativisticKE_F where val : Float deriving Repr, BEq, Inhabited
structure RelativisticKE_Q where val : ℚ deriving Repr, BEq, DecidableEq, Inhabited
structure RelativisticKE_R where val : ℝ deriving Inhabited

/--
================================================================================================
   Relativistic Momentum
================================================================================================
-/
-- Relativistic momentum p = γmv
structure RelativisticMomentum_F where val : Float deriving Repr, BEq, Inhabited
structure RelativisticMomentum_Q where val : ℚ deriving Repr, BEq, DecidableEq, Inhabited
structure RelativisticMomentum_R where val : ℝ deriving Inhabited

/--
================================================================================================
   Electromagnetic Four-Potential and Field Tensor
================================================================================================
-/
-- Four-potential A^μ = (φ/c, A)
structure FourPotential_F where
  phi_over_c : Float  -- Scalar potential / c
  Ax : Float          -- Vector potential components
  Ay : Float
  Az : Float
  deriving Repr, BEq, Inhabited

structure FourPotential_Q where
  phi_over_c : ℚ
  Ax : ℚ
  Ay : ℚ
  Az : ℚ
  deriving Repr, BEq, DecidableEq, Inhabited

structure FourPotential_R where
  phi_over_c : ℝ
  Ax : ℝ
  Ay : ℝ
  Az : ℝ
  deriving Inhabited

/--
================================================================================================
   Core Calculations
================================================================================================
-/
-- Smart constructors with validation
def mkBeta_F (v : Float) : Option Beta_F :=
  if v >= 0.0 && v < 1.0 then some ⟨v⟩ else none

def mkLorentzFactor_F (g : Float) : Option LorentzFactor_F :=
  if g >= 1.0 then some ⟨g⟩ else none

-- Calculate Lorentz factor from velocity (returns Option for safety)
def lorentzFactorFromVelocity_F (v : Velocity_F) : Option LorentzFactor_F :=
  let beta := v.val / c_F
  let beta_squared := beta * beta
  if beta_squared >= 1.0 then
    none  -- Invalid: velocity exceeds c
  else
    some ⟨1.0 / Float.sqrt (1.0 - beta_squared)⟩

-- Calculate Lorentz factor from beta (always valid if beta is valid)
def lorentzFactorFromBeta_F (b : Beta_F) : LorentzFactor_F :=
  ⟨1.0 / Float.sqrt (1.0 - b.val * b.val)⟩

-- Beta from Lorentz factor (returns Option for safety)
def betaFromLorentzFactor_F (g : LorentzFactor_F) : Option Beta_F :=
  let beta_val := Float.sqrt (1.0 - 1.0 / (g.val * g.val))
  if beta_val >= 0.0 && beta_val < 1.0 then
    some ⟨beta_val⟩
  else
    none

-- Rapidity from beta
def rapidityFromBeta_F (b : Beta_F) : Rapidity_F :=
  ⟨0.5 * Float.log ((1.0 + b.val) / (1.0 - b.val))⟩

-- Then the conversion is simple:
def betaFromRapidity_F (r : Rapidity_F) : Beta_F :=
  ⟨Float.tanh r.val⟩

-- Alternate form
def betaFromRapidity_F' (r : Rapidity_F) : Option Beta_F :=
  let beta_val := Float.tanh r.val
  if beta_val >= 0.0 && beta_val < 1.0 then
    some ⟨beta_val⟩
  else if beta_val > -1.0 && beta_val < 0.0 then
    some ⟨-beta_val⟩  -- Take absolute value for negative rapidities
  else
    none  -- Shouldn't happen for finite rapidities

-- Time dilation: Δt = γΔτ
def timeDilation_F (properTime : ProperTime_F) (gamma : LorentzFactor_F) : CoordinateTime_F :=
  ⟨properTime.val * gamma.val⟩

-- Length contraction: L = L₀/γ
def lengthContraction_F (properLength : Meter_F) (gamma : LorentzFactor_F) : Meter_F :=
  ⟨properLength.val / gamma.val⟩

-- Relativistic energy from momentum and mass
def energyFromMomentum_F (p : RelativisticMomentum_F) (m : RestMass_F) : RelativisticEnergy_F :=
  let p_c := p.val * c_F
  let m_c2 := m.val * c_F * c_F
  ⟨Float.sqrt (p_c * p_c + m_c2 * m_c2)⟩

-- Rest energy
def restEnergy_F (m : RestMass_F) : RestEnergy_F :=
  ⟨m.val * c_F * c_F⟩

-- Total relativistic energy
def totalEnergy_F (m : RestMass_F) (gamma : LorentzFactor_F) : RelativisticEnergy_F :=
  ⟨gamma.val * m.val * c_F * c_F⟩

-- Kinetic energy
def kineticEnergy_F (m : RestMass_F) (gamma : LorentzFactor_F) : RelativisticKE_F :=
  ⟨(gamma.val - 1.0) * m.val * c_F * c_F⟩

-- Relativistic momentum
def relativisticMomentum_F (m : RestMass_F) (v : Velocity_F) (gamma : LorentzFactor_F) : RelativisticMomentum_F :=
  ⟨gamma.val * m.val * v.val⟩

-- Spacetime interval between two events
def spacetimeInterval_F (x1 x2 : FourPosition_F) : SpacetimeInterval_F :=
  let dt := x2.t - x1.t
  let dx := x2.x - x1.x
  let dy := x2.y - x1.y
  let dz := x2.z - x1.z
  ⟨-(dt * dt) + dx * dx + dy * dy + dz * dz⟩

-- Classify interval
def classifyInterval_F (s : SpacetimeInterval_F) (tolerance : Float := 1e-10) : IntervalType :=
  if s.val < -tolerance then IntervalType.Timelike
  else if s.val > tolerance then IntervalType.Spacelike
  else IntervalType.Lightlike

-- Velocity addition (relativistic)
def velocityAddition_F (v1 v2 : Velocity_F) : Velocity_F :=
  ⟨(v1.val + v2.val) / (1.0 + v1.val * v2.val / (c_F * c_F))⟩

-- Four-velocity from three-velocity
def fourVelocityFromThreeVelocity_F (v : Velocity_F) (gamma : LorentzFactor_F) : FourVelocity_F :=
  { u0 := gamma.val * c_F
    u1 := gamma.val * v.val  -- Assuming v is in x-direction for simplicity
    u2 := 0.0
    u3 := 0.0 }

-- Four-momentum from mass and four-velocity
def fourMomentumFromFourVelocity_F (m : RestMass_F) (u : FourVelocity_F) : FourMomentum_F :=
  { E_over_c := m.val * u.u0
    px := m.val * u.u1
    py := m.val * u.u2
    pz := m.val * u.u3 }

-- Invariant mass from four-momentum
def invariantMass_F (p : FourMomentum_F) : RestMass_F :=
  let E_over_c2 := p.E_over_c * p.E_over_c
  let p2 := p.px * p.px + p.py * p.py + p.pz * p.pz
  ⟨Float.sqrt (E_over_c2 - p2) / (c_F * c_F)⟩

/--
================================================================================================
   Validation Functions
================================================================================================
-/

def isValidVelocity_F (v : Velocity_F) : Bool :=
  Float.abs v.val < c_F

def isValidBeta_F (b : Beta_F) : Bool :=
  Float.abs b.val < 1.0

def isTimelike_F (s : SpacetimeInterval_F) : Bool :=
  s.val < 0.0

def isSpacelike_F (s : SpacetimeInterval_F) : Bool :=
  s.val > 0.0

def isLightlike_F (s : SpacetimeInterval_F) (tolerance : Float := 1e-10) : Bool :=
  Float.abs s.val < tolerance

def isCausallyConnected_F (s : SpacetimeInterval_F) : Bool :=
  s.val ≤ 0.0  -- Timelike or lightlike

-- Check if four-velocity is normalized (U·U = -c²)
def isFourVelocityNormalized_F (u : FourVelocity_F) (tolerance : Float := 1e-6) : Bool :=
  let norm_squared := -(u.u0 * u.u0) + u.u1 * u.u1 + u.u2 * u.u2 + u.u3 * u.u3
  Float.abs (norm_squared + c_F * c_F) < tolerance

end Units.Physics.Relativity
