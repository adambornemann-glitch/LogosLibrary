/-
Author: Adam Bornemann
Created: 9/25/2025
Updated: 10/10/2025

================================================================================================
  SPECIAL RELATIVITY WITH LEAN 4 - LECTURE 1
  The Geometry of Spacetime and the Death of Absolute Simultaneity
================================================================================================

  ====================================================================
  THE CRISIS THAT BIRTHED RELATIVITY
  ====================================================================

  By 1900, physics had two crown jewels that HATED each other:
  1. Maxwell's Electromagnetism: Light travels at c in vacuum
  2. Galilean Relativity: Velocities add linearly (v₁ + v₂)

  Problem: If light travels at c, and you chase it at speed v,
  Galileo says you should see it moving at (c - v).
  Maxwell says NO - it's still c.

  ### ALBERT MICHELSON (1852-1931) & EDWARD MORLEY (1838-1923)

  They tried to measure Earth's motion through the "luminiferous aether"
  - the supposed medium for light waves. Their apparatus could detect
  velocity differences of ~5 km/s.

  Earth orbits at 30 km/s. They found: NOTHING. Zero. Null result.

  This wasn't measurement error. This was nature screaming that our
  assumptions were WRONG.

  ### HENDRIK LORENTZ (1853-1928): The Right Math, Wrong Physics

  Lorentz found transformations that preserved Maxwell's equations.
  But he thought they were a mathematical trick - objects "really"
  contracted due to electromagnetic forces in the aether.

  He had the equation. He didn't have the insight.

  ### HENRI POINCARÉ (1854-1912): So Close

  Poincaré understood the principle of relativity applied to ALL physics,
  not just mechanics. He even wrote down E = mc² implications.

  But he kept the aether. He couldn't let go of absolute time.

  ### ALBERT EINSTEIN (1879-1955): The Conceptual Revolution

  Einstein's genius wasn't the math - Lorentz had that.
  It wasn't even recognizing the problem - Poincaré saw it.

  Einstein's genius was TAKING THE EQUATIONS SERIOUSLY.

  If Maxwell's equations say c is constant, then c IS constant.
  If this breaks absolute time, then absolute time DOESN'T EXIST.

  While others added epicycles to save their assumptions,
  Einstein threw out the assumptions.

  ### Why This Matters for Formal Methods:

  Each physicist above made unstated assumptions:
  - Michelson-Morley: Space has a preferred reference frame
  - Lorentz: Time is absolute across all frames
  - Poincaré: Simultaneity is frame-independent

  In Lean, we CAN'T make unstated assumptions. Every assumption
  must be explicit. This forces intellectual honesty.
-/

import LogosLibrary.Units.Core
import LogosLibrary.Units.Relativity
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace SpecialRelativity.Lecture1

open Units.SI Units.Relativity

-- structure ElectromagneticWave   where val : Float deriving Repr, BEq, Inhabited

-- structure measured_speed   where val : Velocity_F deriving Repr, BEq, Inhabited

/-
  ====================================================================
  PART I: THE TWO POSTULATES - REALITY'S AXIOMS
  ====================================================================

  Einstein built special relativity on just TWO postulates.
  Everything else - time dilation, E=mc², twin paradox - follows
  by pure logic from these two statements.

  This is what physics SHOULD be: minimal assumptions, maximum consequences.
-/

-- The Inertial Frame type - a reference frame in uniform motion
structure InertialFrame where
  id : String  -- Just for labeling (like "Earth" or "Spaceship")
  velocity : Velocity_F  -- Velocity relative to some arbitrary "lab" frame
  deriving Repr, BEq

/-
  POSTULATE 1: The Principle of Relativity
  "The laws of physics are the same in all inertial frames"

  In Lean: Any physical law valid in one frame is valid in all frames.
  This is a SYMMETRY principle - physics has no preferred observer.
-/

axiom relativity_principle {α : Type} (physics_law : InertialFrame → α → Prop)
  (frame1 frame2 : InertialFrame) (system : α) :
  physics_law frame1 system ↔ physics_law frame2 system

/-
  POSTULATE 2: The Constancy of Light Speed
  "The speed of light in vacuum is the same in all inertial frames"

  This is the WILD one. It says if you measure light's speed while
  standing still OR while moving at 0.99c, you get the SAME answer.
-/

-- We'll define ElectromagneticWave properly later, placeholder for now
structure ElectromagneticWave where
  frequency : Frequency_F
  wavelength : Meter_F

def measured_speed (/-frame-/_ : InertialFrame) (/-wave-/_ : ElectromagneticWave) : Velocity_F :=
  ⟨c_F⟩  -- By the axiom, this is always c

axiom light_speed_invariance (frame : InertialFrame) :
  ∃ (c : Velocity_F), c.val = c_F ∧
  ∀ (light_signal : ElectromagneticWave),
    measured_speed frame light_signal = c

/-
  ### THE SHOCKING CONSEQUENCE:

  These two innocent-looking statements DESTROY absolute time.
  Watch how:

  If c is the same in all frames, and physics is the same in all frames,
  then two events that are simultaneous in one frame CANNOT be
  simultaneous in all frames.

  Simultaneity is relative. Time is relative. Space is relative.
  Only spacetime is absolute.
-/

/-
  ====================================================================
  PART II: THE LORENTZ TRANSFORMATION - THE MIXER OF SPACE AND TIME
  ====================================================================

  The Lorentz transformation tells us how to convert coordinates
  between reference frames. It's NOT just a change of variables.
  It's a rotation in spacetime.

  For simplicity, we consider motion along the x-axis only.
-/

-- Event in spacetime - a point in 4D
structure Event where
  t : Second_F    -- Time coordinate
  x : Meter_F     -- Spatial coordinates
  y : Meter_F
  z : Meter_F
  deriving Repr, BEq

-- The Lorentz transformation for motion in x-direction
def lorentz_transform (v : Velocity_F) (e : Event) : Event :=
  let gamma := lorentzFactorFromVelocity_F v
  match gamma with
  | none => e  -- Invalid velocity, return unchanged
  | some γ =>
    { t := ⟨γ.val * (e.t.val - v.val * e.x.val / (c_F * c_F))⟩
      x := ⟨γ.val * (e.x.val - v.val * e.t.val)⟩
      y := e.y
      z := e.z }

-- Inverse Lorentz transformation (just negate the velocity)
def inverse_lorentz_transform (v : Velocity_F) (e : Event) : Event :=
  lorentz_transform ⟨-v.val⟩ e

/-
  CRITICAL INSIGHT #1: Space and Time Mix!

  Look at the transformed time: t' = γ(t - vx/c²)

  The time in the new frame depends on BOTH time and position
  in the old frame! Space and time are not independent.

  This is why "now" has no universal meaning.
-/

-- Let's PROVE the transformations compose correctly
theorem lorentz_inverse_identity (v : Velocity_F) (e : Event)
  (h_valid : isValidVelocity_F v) :
  inverse_lorentz_transform v (lorentz_transform v e) = e := by
  sorry  -- Would require detailed algebra

/-
  ====================================================================
  PART III: TIME DILATION - MOVING CLOCKS RUN SLOW
  ====================================================================

  This isn't philosophy. It's geometry.
  A clock measures its path length through spacetime (proper time).
  Different paths = different lengths = different elapsed times.
-/

-- Proper time between two events in the same location (in rest frame)
def proper_time_interval (e1 e2 : Event) : ProperTime_F :=
  ⟨e2.t.val - e1.t.val⟩  -- Assumes events at same spatial location

-- Coordinate time between events (as measured in any frame)
def coordinate_time_interval (e1 e2 : Event) : CoordinateTime_F :=
  ⟨e2.t.val - e1.t.val⟩

-- THE FUNDAMENTAL TIME DILATION FORMULA
theorem time_dilation_formula (v : Velocity_F) (τ : ProperTime_F)
  (h_valid : isValidVelocity_F v) :
  ∃ (γ : LorentzFactor_F),
    let t := timeDilation_F τ γ
    t.val = τ.val * γ.val  := by

  unfold timeDilation_F
  -- Get Lorentz factor
  let gamma := lorentzFactorFromVelocity_F v
  cases gamma with
  | none => sorry -- Invalid case
  | some γ =>
    use γ



/-
  ### A Concrete Example: The Muon's Journey

  Muons are created in the upper atmosphere (~10 km up) by cosmic rays.
  They travel at ~0.998c toward Earth.
  Their rest-frame lifetime is 2.2 microseconds.

  Classical prediction: They travel 0.998c × 2.2μs = 660 meters
  They should NEVER reach Earth's surface.

  Reality: We detect them at sea level ALL THE TIME.

  Why? Time dilation!
  γ = 1/√(1 - 0.998²) ≈ 15.8
  Earth-frame lifetime: 15.8 × 2.2μs = 34.8μs
  Distance traveled: 0.998c × 34.8μs ≈ 10.4 km

  They make it! Special relativity isn't abstract - it's why
  we can detect cosmic ray muons at Earth's surface.
-/

def muon_example : Bool :=
  let v_muon := ⟨0.998 * c_F⟩  -- Muon velocity
  let tau_muon := ProperTime_F.mk 2.2e-6  -- Rest lifetime in seconds
  let gamma := lorentzFactorFromVelocity_F v_muon
  match gamma with
  | none => false
  | some γ =>
    let t_earth := timeDilation_F tau_muon γ
    let distance := (v_muon.val * t_earth.val)  -- Distance in Earth frame
    distance > 10000.0  -- Greater than 10 km

#eval muon_example  -- Should be true!

/-
  ====================================================================
  PART IV: LENGTH CONTRACTION - SPACE ITSELF SQUEEZES
  ====================================================================

  If time dilates, space must contract. They're two sides of the
  same geometric fact: the invariance of the spacetime interval.
-/

def proper_length := Meter_F  -- Length in rest frame

-- Length contraction formula
theorem length_contraction_formula (v : Velocity_F) (L₀ : Meter_F)
  (h_valid : isValidVelocity_F v) :
  ∃ (γ : LorentzFactor_F),
    let L := lengthContraction_F L₀ γ
    L.val = L₀.val / γ.val := by
  let gamma := lorentzFactorFromVelocity_F v
  cases gamma with
  | none => sorry
  | some γ =>
    use γ
    rfl

/-
  CRITICAL INSIGHT #2: Reciprocity

  If A sees B's clock running slow, B sees A's clock running slow.
  If A sees B contracted, B sees A contracted.

  This isn't a contradiction! It's because simultaneity is relative.
  A and B disagree on what "now" means at distant locations.
-/

/-
  ====================================================================
  PART V: THE INVARIANT INTERVAL - THE TRUE DISTANCE
  ====================================================================

  Space changes. Time changes. But spacetime interval? INVARIANT.
  This is the "true" distance between events - the thing all
  observers agree on.

  s² = -(cΔt)² + Δx² + Δy² + Δz²

  This is the Pythagorean theorem for spacetime, except with
  a minus sign that changes EVERYTHING.
-/

-- Calculate spacetime interval between two events
def spacetime_interval (e1 e2 : Event) : SpacetimeInterval_F :=
  let dt := e2.t.val - e1.t.val
  let dx := e2.x.val - e1.x.val
  let dy := e2.y.val - e1.y.val
  let dz := e2.z.val - e1.z.val
  let c_dt := c_F * dt
  ⟨-(c_dt * c_dt) + dx * dx + dy * dy + dz * dz⟩

-- THE KEY THEOREM: Interval is invariant under Lorentz transformation
theorem interval_invariance (v : Velocity_F) (e1 e2 : Event)
  (h_valid : isValidVelocity_F v) :
  let e1' := lorentz_transform v e1
  let e2' := lorentz_transform v e2
  spacetime_interval e1 e2 = spacetime_interval e1' e2' := by
  sorry  -- This is the fundamental theorem - worth proving in detail!

/-
  ### What the Interval Tells Us:

  s² < 0 (Timelike): Events can be causally connected.
                      One can cause the other.
                      There exists a frame where they happen
                      at the SAME place.

  s² > 0 (Spacelike): Events cannot be causally connected.
                      They're absolutely independent.
                      There exists a frame where they happen
                      at the SAME time.

  s² = 0 (Lightlike): Events connected by a light signal.
                      The boundary between cause and coincidence.
-/

-- Classify the causal relationship between events
def causal_classification (e1 e2 : Event) : IntervalType :=
  let s := spacetime_interval e1 e2
  classifyInterval_F s

-- Can one event cause the other?
def can_cause (e1 e2 : Event) : Bool :=
  let interval_type := causal_classification e1 e2
  match interval_type with
  | IntervalType.Timelike => true
  | IntervalType.Lightlike => true
  | IntervalType.Spacelike => false

/-
  ====================================================================
  PART VI: VELOCITY ADDITION - THE SPEED LIMIT OF THE UNIVERSE
  ====================================================================

  In Galileo's world: If you throw a ball at 20 m/s from a train
  moving at 30 m/s, the ball moves at 50 m/s relative to the ground.

  In Einstein's world: Velocities don't add linearly!

  v = (v₁ + v₂)/(1 + v₁v₂/c²)

  This ensures nothing ever exceeds c.
-/

-- Relativistic velocity addition
theorem velocity_addition_never_exceeds_c (v1 v2 : Velocity_F)
  (h1 : isValidVelocity_F v1) (h2 : isValidVelocity_F v2) :
  let v_total := velocityAddition_F v1 v2
  isValidVelocity_F v_total := by
  sorry  -- Would show |v_total| < c

-- Example: Adding two velocities each at 0.9c
def extreme_velocity_example : Velocity_F :=
  let v1 := Velocity_F.mk (0.9 * c_F)
  let v2 := Velocity_F.mk (0.9 * c_F)
  velocityAddition_F v1 v2

#eval extreme_velocity_example.val / c_F
-- Result: ~0.9945c, NOT 1.8c!

/-
  CRITICAL INSIGHT #3: c is Not Just a Speed, It's the Structure of Spacetime

  The speed of light isn't really about light. It's the conversion
  factor between space and time. Light just happens to travel at
  the maximum speed allowed by spacetime geometry.

  Asking "why can't we go faster than c?" is like asking
  "why can't we go norther than the North Pole?"

  It's not a limitation of our technology.
  It's the shape of reality itself.
-/

/-
  ====================================================================
  PART VII: SIMULTANEITY - THE RELATIVITY OF "NOW"
  ====================================================================

  This is the hardest concept to accept: there is no universal "now."
  Events that are simultaneous in one frame are NOT simultaneous
  in another.

  This isn't about signal delays or measurement problems.
  Simultaneity literally doesn't exist across space.
-/

-- Two events are simultaneous in a frame if they have the same time coordinate
def simultaneous_in_frame (e1 e2 : Event) : Bool :=
  e1.t.val == e2.t.val

-- The killer theorem: simultaneity is frame-dependent
theorem simultaneity_is_relative (v : Velocity_F) (e1 e2 : Event)
  (h_valid : isValidVelocity_F v)
  (h_sim : simultaneous_in_frame e1 e2)
  (h_diff_x : e1.x.val ≠ e2.x.val) :
  let e1' := lorentz_transform v e1
  let e2' := lorentz_transform v e2
  ¬(simultaneous_in_frame e1' e2') := by
  sorry  -- Would show t1' ≠ t2' when x1 ≠ x2

/-
  ### The Train and Lightning Example (Einstein's Favorite):

  A train moves at high speed. Lightning strikes both ends
  simultaneously in the ground frame.

  Person on platform: "Both strikes happened at the same time."
  Person on train: "The front strike happened first."

  BOTH ARE RIGHT. There is no "true" answer to which happened first.
  The order of spacelike-separated events is frame-dependent.

  This is why faster-than-light communication would break causality:
  you could send messages into your own past!
-/

/-
  ====================================================================
  PART VIII: E = mc² - THE MOST FAMOUS EQUATION
  ====================================================================

  This isn't a separate discovery. It falls out naturally from
  the geometry of spacetime. Mass is just rest energy.

  More precisely: E² = (pc)² + (mc²)²

  When p = 0 (at rest): E = mc²
  When m = 0 (photons): E = pc
-/

-- The energy-momentum relation
def energy_momentum_relation (m : RestMass_F) (p : RelativisticMomentum_F)
    : RelativisticEnergy_F :=
  energyFromMomentum_F p m

-- Rest energy
theorem rest_energy_formula (m : RestMass_F) :
  let E₀ := restEnergy_F m
  E₀.val = m.val * c_F * c_F := by
  rfl

-- For photons (m = 0)
def photon_energy (p : RelativisticMomentum_F) : RelativisticEnergy_F :=
  ⟨p.val * c_F⟩

/-
  ### Why This Matters:

  1 kg of matter contains:
  E = 1 kg × (3×10⁸ m/s)² = 9×10¹⁶ joules

  That's the energy output of a large power plant for YEARS.

  This isn't theoretical. The sun converts 4 million tons of
  matter to energy every SECOND. Nuclear weapons work because
  a tiny fraction of mass becomes energy.

  Mass and energy are the same thing, measured in different units.
-/
/-
  ====================================================================
  PART IX: COMPUTATIONAL LABORATORY - SEEING RELATIVITY IN ACTION
  ====================================================================

  Theory is beautiful, but NUMBERS make it real. Let's compute
  actual relativistic effects and see why they matter.

  Each example includes:
  - The physical setup
  - The calculation with intermediate steps
  - What the result MEANS
  - Why we should care
-/

section ComputationalExamples

/-
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  EXAMPLE 1: GPS SATELLITES - RELATIVITY IN YOUR POCKET
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  GPS satellites orbit at ~20,200 km altitude, moving at ~3.87 km/s.
  Without relativistic corrections, GPS would accumulate ~10 km of
  error PER DAY. Your phone wouldn't find your house - it would
  lose your entire city!

  Two effects compete:
  1. Satellites move fast → time dilation (clocks run slow)
  2. Satellites are higher in Earth's gravity well → GR effect (clocks run fast)

  Let's calculate the special relativistic part:
-/

def gps_time_dilation : IO Unit := do
  -- GPS satellite parameters
  let v_satellite := 3870.0  -- m/s orbital velocity
  let beta := v_satellite / c_F
  let gamma := 1.0 / Float.sqrt (1.0 - beta * beta)

  -- Time dilation per day
  let seconds_per_day := 86400.0
  let satellite_time := seconds_per_day / gamma
  let time_difference := seconds_per_day - satellite_time

  -- Convert to nanoseconds (GPS precision)
  let diff_nanoseconds := time_difference * 1e9

  IO.println s!"GPS SATELLITE TIME DILATION CALCULATION:"
  IO.println s!"========================================="
  IO.println s!"Orbital velocity: {v_satellite} m/s"
  IO.println s!"β = v/c: {beta}"
  IO.println s!"γ factor: {gamma}"
  IO.println s!""
  IO.println s!"Earth clocks advance: {seconds_per_day} seconds/day"
  IO.println s!"Satellite clocks advance: {satellite_time} seconds/day"
  IO.println s!"Satellite clocks LOSE: {diff_nanoseconds} nanoseconds/day"
  IO.println s!""
  IO.println s!"At light speed, 7 nanoseconds = 2.1 meters of position error!"
  IO.println s!"Without correction, GPS would be useless within hours."

#eval gps_time_dilation

/-
  NOTE: The actual GPS correction is ~38 microseconds/day AHEAD
  because General Relativity's gravitational time dilation
  (which speeds up the satellite clocks) dominates over
  Special Relativity's motion effect (which slows them down).

  This is ENGINEERING, not theory. Real satellites, real corrections.
-/

/-
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  EXAMPLE 2: PARTICLE ACCELERATOR - PROTONS AT THE LHC
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  The Large Hadron Collider accelerates protons to 0.999999991c.
  Let's see what happens to time, length, and energy at these speeds.
-/

def lhc_proton : IO Unit := do
  -- LHC parameters
  let v_proton := 0.999999991 * c_F
  let beta := v_proton / c_F
  let gamma := 1.0 / Float.sqrt (1.0 - beta * beta)

  -- Proton rest mass
  let m_proton := 1.67262192e-27  -- kg
  let rest_energy := m_proton * c_F * c_F / 1.602176634e-19  -- Convert to eV
  let total_energy := gamma * rest_energy
  let kinetic_energy := (gamma - 1.0) * rest_energy

  -- Time dilation: 1 second in lab = ? for proton
  let proton_second := 1.0 / gamma

  -- Length contraction: 27 km ring appears how long to proton?
  let ring_length := 27000.0  -- meters
  let contracted_length := ring_length / gamma

  IO.println s!"LHC PROTON RELATIVISTIC EFFECTS:"
  IO.println s!"================================="
  IO.println s!"Proton velocity: {beta} c"
  IO.println s!"Lorentz factor γ: {gamma}"
  IO.println s!""
  IO.println s!"ENERGY:"
  IO.println s!"  Rest energy: {rest_energy / 1e9} GeV"
  IO.println s!"  Total energy: {total_energy / 1e12} TeV"
  IO.println s!"  Kinetic energy: {kinetic_energy / 1e12} TeV"
  IO.println s!"  That's {gamma}× the rest mass!"
  IO.println s!""
  IO.println s!"TIME DILATION:"
  IO.println s!"  1 second in lab = {proton_second * 1e6} microseconds for proton"
  IO.println s!"  Proton 'sees' time pass {gamma}× faster in the lab"
  IO.println s!""
  IO.println s!"LENGTH CONTRACTION:"
  IO.println s!"  27 km ring appears as {contracted_length} meters to proton"
  IO.println s!"  The entire LHC is smaller than a football field in proton frame!"

#eval lhc_proton

/-
  THINK ABOUT THIS: From the proton's perspective, it crosses the
  "contracted" 3.6-meter ring in just 12 nanoseconds. From our
  perspective, it takes 90 microseconds to complete one orbit.
  Both are right! This is relativity.
-/

/-
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  EXAMPLE 3: INTERSTELLAR TRAVEL - THE TWIN PARADOX QUANTIFIED
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  A journey to Proxima Centauri (4.24 light-years away) at high speed.
  How much do the twins age differently?
-/

def interstellar_journey (v_fraction : Float) : IO Unit := do
  -- Journey parameters
  let distance := 4.24  -- light-years
  let /-v-/_ := v_fraction * c_F
  let beta := v_fraction
  let gamma := 1.0 / Float.sqrt (1.0 - beta * beta)

  -- Earth perspective (assuming instant acceleration)
  let earth_time_years := distance / v_fraction  -- one way
  let earth_round_trip := 2.0 * earth_time_years

  -- Traveler perspective
  let traveler_time_years := earth_time_years / gamma  -- one way
  let traveler_round_trip := 2.0 * traveler_time_years

  -- Age difference
  let age_difference := earth_round_trip - traveler_round_trip

  IO.println s!"INTERSTELLAR JOURNEY TO PROXIMA CENTAURI:"
  IO.println s!"=========================================="
  IO.println s!"Distance: {distance} light-years"
  IO.println s!"Travel speed: {v_fraction}c"
  IO.println s!"Lorentz factor γ: {gamma}"
  IO.println s!""
  IO.println s!"EARTH PERSPECTIVE:"
  IO.println s!"  Round trip takes: {earth_round_trip} years"
  IO.println s!""
  IO.println s!"TRAVELER PERSPECTIVE:"
  IO.println s!"  Round trip takes: {traveler_round_trip} years"
  IO.println s!"  Distance contracted to: {distance/gamma} light-years each way"
  IO.println s!""
  IO.println s!"TWIN PARADOX RESULT:"
  IO.println s!"  Traveling twin is {age_difference} years younger upon return!"
  IO.println s!"  Earth twin aged {earth_round_trip/traveler_round_trip}× faster"

-- Let's try different speeds
#eval interstellar_journey 0.5   -- 50% light speed
#eval interstellar_journey 0.9   -- 90% light speed
#eval interstellar_journey 0.99  -- 99% light speed
#eval interstellar_journey 0.999 -- 99.9% light speed

/-
  PATTERN RECOGNITION: Notice how the age difference explodes as
  v → c. At 0.999c, the traveler ages only 4 months while Earth
  ages 8.5 years! This isn't science fiction - it's geometry.
-/

/-
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  EXAMPLE 4: RELATIVISTIC COLLISION - WHEN 1 + 1 ≠ 2
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  Two spaceships approach Earth from opposite directions.
  How fast do they see each other moving?
-/
def relativistic_collision : IO Unit := do
  let speeds := [0.5, 0.7, 0.9, 0.99]

  IO.println s!"RELATIVISTIC VELOCITY ADDITION:"
  IO.println s!"================================"
  IO.println s!"Two objects approach each other, each at speed v"
  IO.println s!""
  IO.println s!"v/c         | Classical (v₁+v₂)    | Relativistic     | Difference"
  IO.println s!"-----------------------------------------------------------------"

  for v_over_c in speeds do
    -- Classical addition
    let classical := 2.0 * v_over_c
    -- Relativistic addition: (v₁ + v₂)/(1 + v₁v₂/c²)
    let relativistic := (2.0 * v_over_c) / (1.0 + v_over_c * v_over_c)
    let difference := classical - relativistic

    IO.println s!"{v_over_c}    | {classical}c            | {relativistic}c        | {difference}c"

  IO.println s!""
  IO.println s!"Key insight: The relativistic sum NEVER exceeds c!"
  IO.println s!"Even 0.99c + 0.99c = 0.999949c, not 1.98c"

  #eval relativistic_collision

/-
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  EXAMPLE 5: E = mc² IN ACTION - NUCLEAR BINDING ENERGY
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  When 4 hydrogen nuclei fuse into helium in the Sun, 0.7% of the
  mass becomes energy. Let's calculate the energy from 1 gram of
  hydrogen fusion.
-/

def fusion_energy : IO Unit := do
  -- Mass defect in hydrogen → helium fusion
  let mass_fraction_converted := 0.007  -- 0.7% of mass becomes energy
  let initial_mass_kg := 0.001  -- 1 gram = 0.001 kg
  let mass_converted := initial_mass_kg * mass_fraction_converted

  -- E = mc²
  let energy_joules := mass_converted * c_F * c_F

  -- Convert to more intuitive units
  let tnt_equivalent_tons := energy_joules / 4.184e9  -- 1 ton TNT = 4.184 GJ
  let kwh := energy_joules / 3.6e6  -- 1 kWh = 3.6 MJ
  let home_years := kwh / (10000.0)  -- Average home uses ~10,000 kWh/year

  IO.println s!"MASS-ENERGY CONVERSION IN FUSION:"
  IO.println s!"=================================="
  IO.println s!"Starting with: 1 gram of hydrogen"
  IO.println s!"Mass converted to energy: {mass_converted * 1e6} milligrams"
  IO.println s!""
  IO.println s!"ENERGY RELEASED:"
  IO.println s!"  {energy_joules / 1e12} TJ (terajoules)"
  IO.println s!"  {tnt_equivalent_tons} tons of TNT equivalent"
  IO.println s!"  {kwh / 1e6} million kWh"
  IO.println s!"  Could power an average home for {home_years} years!"
  IO.println s!""
  IO.println s!"The Sun converts 4 million tons to energy every second."
  IO.println s!"That's {4e9 * mass_fraction_converted} tons of pure energy/second!"

#eval fusion_energy

/-
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  EXAMPLE 6: DOPPLER SHIFT - WHY THE UNIVERSE IS EXPANDING
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  Light from receding galaxies is redshifted. Let's calculate
  the shift for various recession velocities.
-/

def relativistic_doppler (v_fraction : Float) (rest_wavelength : Float) : IO Unit := do
  let beta := v_fraction
  let /-gamma-/_ := 1.0 / Float.sqrt (1.0 - beta * beta)

  -- Relativistic Doppler formula for receding source
  let doppler_factor := Float.sqrt ((1.0 + beta) / (1.0 - beta))
  let observed_wavelength := rest_wavelength * doppler_factor
  let redshift_z := doppler_factor - 1.0

  IO.println s!"Recession velocity: {v_fraction}c"
  IO.println s!"Rest wavelength: {rest_wavelength} nm"
  IO.println s!"Observed wavelength: {observed_wavelength} nm"
  IO.println s!"Redshift z: {redshift_z}"
  IO.println s!"Light is shifted by factor: {doppler_factor}"
  IO.println s!""

def cosmological_redshifts : IO Unit := do
  IO.println s!"COSMOLOGICAL REDSHIFTS:"
  IO.println s!"======================="
  IO.println s!"Hydrogen alpha line (rest: 656.3 nm) from receding galaxies:"
  IO.println s!""

  -- Various recession speeds
  let speeds := [0.1, 0.3, 0.5, 0.7, 0.9]
  for v in speeds do
    relativistic_doppler v 656.3

#eval cosmological_redshifts

/-
  PROFOUND REALIZATION: The most distant galaxies we see have
  redshifts z > 10, meaning they're receding at > 0.98c!
  The expansion of space itself carries them away from us.
-/

/-
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  EXAMPLE 7: RELATIVISTIC MOMENTUM - WHY ACCELERATORS NEED MORE POWER
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  As particles approach c, their momentum grows without bound,
  making further acceleration increasingly difficult.
-/

def momentum_growth : IO Unit := do
  let m_electron := 9.109e-31  -- kg

  IO.println s!"ELECTRON MOMENTUM VS VELOCITY:"
  IO.println s!"==============================="
  IO.println s!"Electron rest mass: {m_electron} kg"
  IO.println s!""
  IO.println s!"v/c      | γ            | Classical p        | Relativistic p     | Ratio"
  IO.println s!"---------------------------------------------------------------------------"

  let velocities := [0.1, 0.5, 0.9, 0.99, 0.999, 0.9999]

  for v_frac in velocities do
    let v := v_frac * c_F
    let gamma := 1.0 / Float.sqrt (1.0 - v_frac * v_frac)
    let p_classical := m_electron * v
    let p_relativistic := gamma * m_electron * v
    let ratio := p_relativistic / p_classical

    IO.println s!"{v_frac}  | {gamma}  | {p_classical}  | {p_relativistic}  | {ratio}"

  IO.println s!""
  IO.println s!"At 0.9999c, relativistic momentum is 70× the classical value!"
  IO.println s!"This is why particle accelerators need exponentially more energy"
  IO.println s!"to achieve small increases in speed near c."


#eval momentum_growth

/-
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  MASTER EXAMPLE: COMPLETE SPACETIME DIAGRAM
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  Let's trace an event through multiple reference frames and see
  how coordinates transform while preserving the interval.
-/

def spacetime_diagram : IO Unit := do
  -- Define an event: light flash at specific spacetime point
  let event := Event.mk
    ⟨1.0⟩   -- 1 second after origin
    ⟨3e8⟩   -- 300,000 km from origin
    ⟨0.0⟩   -- y = 0
    ⟨0.0⟩   -- z = 0

  IO.println s!"SPACETIME EVENT IN MULTIPLE FRAMES:"
  IO.println s!"===================================="
  IO.println s!"Original event: t = {event.t.val} s, x = {event.x.val/1000} km"

  -- Calculate spacetime interval (invariant)
  let s_squared := -(c_F * event.t.val) * (c_F * event.t.val) + event.x.val * event.x.val
  IO.println s!"Spacetime interval s² = {s_squared} m²"

  if s_squared > 0 then
    IO.println s!"This is a SPACELIKE interval (no causal connection possible)"
  else if s_squared < 0 then
    IO.println s!"This is a TIMELIKE interval (causal connection possible)"
  else
    IO.println s!"This is a LIGHTLIKE interval (on the light cone)"

  IO.println s!""
  IO.println s!"Frame v/c | t' (s)       | x' (km)        | Interval check"
  IO.println s!"-------------------------------------------------------"

  -- Transform to different frames
  let velocities := [0.0, 0.3, 0.5, 0.7, 0.9]

  for v_frac in velocities do
    let v := Velocity_F.mk (v_frac * c_F)
    let transformed := lorentz_transform v event

    -- Verify interval is preserved
    let s_squared_prime := -(c_F * transformed.t.val) * (c_F * transformed.t.val) +
                            transformed.x.val * transformed.x.val

    IO.println s!"{v_frac}     | {transformed.t.val}  | {transformed.x.val/1000}  | {s_squared_prime}"

  IO.println s!""
  IO.println s!"Notice: The interval s² is THE SAME in all frames!"
  IO.println s!"This invariance is the foundation of relativity."

#eval spacetime_diagram

end ComputationalExamples

/-
  ### WHAT THESE EXAMPLES TEACH US:

  1. **Relativity is everywhere** - From GPS to particle physics,
     relativistic effects are ENGINEERING realities, not abstractions.

  2. **The universe has a speed limit** - No matter how you add
     velocities, you can't exceed c. It's built into the geometry.

  3. **Energy and mass are fungible** - The Sun shines because
     mass becomes energy. E = mc² is why stars exist.

  4. **Time is personal** - Your passage through time depends on
     your path through spacetime. Twin paradox isn't a paradox.

  5. **Space and time are projections** - Only spacetime intervals
     are real. Everything else depends on your reference frame.

  Run these examples. Modify the parameters. Build intuition.
  Reality at high speeds is stranger than fiction, but it's
  mathematically consistent and experimentally verified to
  extraordinary precision.
-/

/-
  ====================================================================
  NEXT LECTURE PREVIEW: Four-Vectors and Spacetime Geometry
  ====================================================================

  Next time, we'll see spacetime as a 4D geometric object where:
  - Rotations mix space with space (ordinary rotations)
  - "Rotations" mixing space with time are Lorentz boosts
  - Physics laws are tensor equations (coordinate-independent)
  - Electromagnetism unifies into a single tensor field
  - The path to General Relativity becomes clear

  We'll prove that Maxwell's equations REQUIRE special relativity.
  Magnetism is literally electricity viewed from a moving frame!
-/

/-
  ### EXERCISES FOR THE STUDENT:

  1. Prove that no massive object can reach the speed of light.
     Hint: What happens to γ as v → c?

     theorem cannot_reach_c (m : RestMass_F) (h_positive : m.val > 0) :
       ∀ (v : Velocity_F), v.val < c_F := by
       sorry

  2. The "Twin Paradox": Twin A stays on Earth, Twin B travels to
     a star 4 light-years away at 0.8c and returns.
     Calculate the age difference when they reunite.

     def twin_paradox_age_difference : Second_F := by
       sorry

  3. Prove that the spacetime interval provides a partial ordering
     on events (timelike separated events have a definite order).

  4. Show that the velocity addition formula is associative:
     (v₁ ⊕ v₂) ⊕ v₃ = v₁ ⊕ (v₂ ⊕ v₃)

  5. Derive length contraction from time dilation using the
     principle that light travels at c in all frames.

  6. Prove that if tachyons (faster-than-light particles) existed,
     they could violate causality by constructing a scenario where
     an effect precedes its cause.

  7. Advanced: Prove that the Lorentz transformations form a group
     (closure, associativity, identity, inverses).

  8. Challenge: Implement the Doppler shift formula and show why
     a receding galaxy's light is redshifted.

  REMEMBER: The goal isn't just to manipulate formulas. It's to
  understand that space and time are aspects of a single geometric
  entity - spacetime - and special relativity is just the geometry
  of flat spacetime.

  Every "paradox" in relativity dissolves when you think geometrically
  instead of trying to preserve Newtonian intuition.
-/

end SpecialRelativity.Lecture1
