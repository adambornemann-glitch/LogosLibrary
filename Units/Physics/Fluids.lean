-- Fluids.lean        -- Viscosity, flow rates, Reynolds/Mach, fluid mechanics
import LogosLibrary.Units.Core.SI
import LogosLibrary.Units.Physics.Mechanics
import LogosLibrary.Units.Physics.Thermal
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

open Units.Standard Units.Physics.Mechanics Units.Physics.Thermal
namespace Units.Physics.Fluids
/-
================================================================================
FLUID MECHANICS UNITS LIBRARY
================================================================================

This module provides type-safe units for fluid mechanics, rheology,
aerodynamics, hydraulics, and multiphase flow phenomena.
Following the triple-type architecture for maximum flexibility without type
conversion friction.

## COVERAGE
- Viscosity (dynamic, kinematic, bulk, extensional)
- Surface tension and interfacial energy
- Flow rates (volumetric, mass, molar)
- Pressure gradients and hydraulic head
- Permeability (porous media, Darcy flow)
- Compressibility and bulk modulus
- Dimensionless numbers (Re, Ma, Fr, We, Ca, St, Pr, Gr, Ra)
- Rheological properties (shear rate, strain rate)
- Aerodynamic coefficients (drag, lift, moment)
- Hydraulic conductivity and transmissivity
- Turbulence parameters (dissipation rate, intensity)
- Multiphase flow (void fraction, slip ratio, quality)

## USAGE PATTERNS
Float: CFD simulations, experimental measurements, pump/turbine calculations,
pipe flow analysis, rheometer data, wind tunnel testing, hydraulic design,
process control, real-time monitoring, drag calculations

ℚ: Exact flow rate ratios, mixing proportions, dimensionless group calculations,
stoichiometric flow rates, calibration factors, geometric similitude ratios

ℝ: Navier-Stokes solutions, boundary layer theory, potential flow analysis,
similarity solutions, asymptotic analysis, stability theory, formal verification
of conservation laws, continuum mechanics proofs
-/

set_option autoImplicit false
set_option linter.unusedVariables false

/--
================================================================================================
   Mathematical Constants for Float Calculations
================================================================================================
-/
def pi_F : Float := 3.14159265358979323846
def e_F : Float := 2.71828182845904523536
def sqrt2_F : Float := 1.41421356237309504880
def sqrt3_F : Float := 1.73205080756887729352
def g_standard_F : Float := 9.80665  -- Standard gravity (m/s²)
def R_gas_F : Float := 8.314462618  -- Universal gas constant (J/(mol·K))
def gamma_air_F : Float := 1.4  -- Specific heat ratio for air

/--
================================================================================================
   Dynamic Viscosity
================================================================================================
-/
-- Pascal-second: Pa·s = kg/(m·s)
structure PascalSecond_F where val : Float deriving Repr, BEq, Inhabited
structure PascalSecond_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PascalSecond_R where val : ℝ     deriving Inhabited

structure MilliPascalSecond_F where val : Float deriving Repr, BEq, Inhabited
structure MilliPascalSecond_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilliPascalSecond_R where val : ℝ     deriving Inhabited

-- Poise: P = 0.1 Pa·s (CGS unit)
structure Poise_F      where val : Float deriving Repr, BEq, Inhabited
structure Poise_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Poise_R      where val : ℝ     deriving Inhabited

structure Centipoise_F where val : Float deriving Repr, BEq, Inhabited
structure Centipoise_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Centipoise_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Kinematic Viscosity
================================================================================================
-/
-- Square meter per second: m²/s
structure M2PerSecond_F where val : Float deriving Repr, BEq, Inhabited
structure M2PerSecond_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure M2PerSecond_R where val : ℝ     deriving Inhabited

structure Mm2PerSecond_F where val : Float deriving Repr, BEq, Inhabited
structure Mm2PerSecond_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Mm2PerSecond_R where val : ℝ     deriving Inhabited

-- Stokes: St = cm²/s = 10⁻⁴ m²/s
structure Stokes_F     where val : Float deriving Repr, BEq, Inhabited
structure Stokes_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Stokes_R     where val : ℝ     deriving Inhabited

structure Centistokes_F where val : Float deriving Repr, BEq, Inhabited
structure Centistokes_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Centistokes_R where val : ℝ     deriving Inhabited

-- Saybolt Universal Seconds (empirical unit)
structure SUS_F        where val : Float deriving Repr, BEq, Inhabited
structure SUS_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SUS_R        where val : ℝ     deriving Inhabited

/--
================================================================================================
   Surface Tension
================================================================================================
-/
-- Newton per meter: N/m = kg/s²
structure NewtonPerMeter_F where val : Float deriving Repr, BEq, Inhabited
structure NewtonPerMeter_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NewtonPerMeter_R where val : ℝ     deriving Inhabited

structure MilliNewtonPerMeter_F where val : Float deriving Repr, BEq, Inhabited
structure MilliNewtonPerMeter_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilliNewtonPerMeter_R where val : ℝ     deriving Inhabited

-- Dyne per centimeter: dyn/cm (CGS)
structure DynePerCm_F  where val : Float deriving Repr, BEq, Inhabited
structure DynePerCm_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DynePerCm_R  where val : ℝ     deriving Inhabited

-- Interfacial energy: J/m²
structure JoulePerM2_F where val : Float deriving Repr, BEq, Inhabited
structure JoulePerM2_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JoulePerM2_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Flow Rates
================================================================================================
-/
-- Volumetric flow rate: m³/s
structure M3PerSecond_F where val : Float deriving Repr, BEq, Inhabited
structure M3PerSecond_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure M3PerSecond_R where val : ℝ     deriving Inhabited

structure LiterPerSecond_F where val : Float deriving Repr, BEq, Inhabited
structure LiterPerSecond_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LiterPerSecond_R where val : ℝ     deriving Inhabited

structure LiterPerMinute_F where val : Float deriving Repr, BEq, Inhabited
structure LiterPerMinute_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LiterPerMinute_R where val : ℝ     deriving Inhabited

structure LiterPerHour_F where val : Float deriving Repr, BEq, Inhabited
structure LiterPerHour_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LiterPerHour_R where val : ℝ     deriving Inhabited

-- Gallons per minute (US)
structure GallonPerMinute_F where val : Float deriving Repr, BEq, Inhabited
structure GallonPerMinute_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GallonPerMinute_R where val : ℝ     deriving Inhabited

-- Cubic feet per minute
structure CFM_F        where val : Float deriving Repr, BEq, Inhabited
structure CFM_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CFM_R        where val : ℝ     deriving Inhabited

-- Mass flow rate: kg/s
structure KgPerSecond_F where val : Float deriving Repr, BEq, Inhabited
structure KgPerSecond_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KgPerSecond_R where val : ℝ     deriving Inhabited

structure GramPerSecond_F where val : Float deriving Repr, BEq, Inhabited
structure GramPerSecond_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GramPerSecond_R where val : ℝ     deriving Inhabited

structure KgPerHour_F  where val : Float deriving Repr, BEq, Inhabited
structure KgPerHour_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KgPerHour_R  where val : ℝ     deriving Inhabited

-- Molar flow rate: mol/s
structure MolPerSecond_F where val : Float deriving Repr, BEq, Inhabited
structure MolPerSecond_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MolPerSecond_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Pressure Gradient and Hydraulic Head
================================================================================================
-/
-- Pressure gradient: Pa/m
structure PascalPerMeter_F where val : Float deriving Repr, BEq, Inhabited
structure PascalPerMeter_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PascalPerMeter_R where val : ℝ     deriving Inhabited

structure KPaPerMeter_F where val : Float deriving Repr, BEq, Inhabited
structure KPaPerMeter_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KPaPerMeter_R where val : ℝ     deriving Inhabited

-- Hydraulic gradient: dimensionless (m/m)
structure HydraulicGradient_F where val : Float deriving Repr, BEq, Inhabited
structure HydraulicGradient_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HydraulicGradient_R where val : ℝ     deriving Inhabited

-- Head loss coefficient: dimensionless
structure LossCoefficient_F where val : Float deriving Repr, BEq, Inhabited
structure LossCoefficient_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LossCoefficient_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Permeability and Porous Media
================================================================================================
-/
-- Permeability: m² (SI) or Darcy
structure Permeability_F where val : Float deriving Repr, BEq, Inhabited  -- m²
structure Permeability_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Permeability_R where val : ℝ     deriving Inhabited

structure Darcy_F      where val : Float deriving Repr, BEq, Inhabited  -- 1 D ≈ 10⁻¹² m²
structure Darcy_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Darcy_R      where val : ℝ     deriving Inhabited

structure Millidarcy_F where val : Float deriving Repr, BEq, Inhabited
structure Millidarcy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Millidarcy_R where val : ℝ     deriving Inhabited

-- Hydraulic conductivity: m/s
structure HydraulicConductivity_F where val : Float deriving Repr, BEq, Inhabited
structure HydraulicConductivity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HydraulicConductivity_R where val : ℝ     deriving Inhabited

-- Transmissivity: m²/s
structure Transmissivity_F where val : Float deriving Repr, BEq, Inhabited
structure Transmissivity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Transmissivity_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Compressibility and Bulk Properties
================================================================================================
-/
-- Compressibility: Pa⁻¹
structure Compressibility_F where val : Float deriving Repr, BEq, Inhabited
structure Compressibility_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Compressibility_R where val : ℝ     deriving Inhabited

-- Bulk modulus: Pa
structure BulkModulus_F where val : Float deriving Repr, BEq, Inhabited
structure BulkModulus_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BulkModulus_R where val : ℝ     deriving Inhabited

-- Speed of sound: m/s (using Velocity_F from Core.SI)

/--
================================================================================================
   Rheological Properties
================================================================================================
-/
-- Shear rate: s⁻¹
structure ShearRate_F  where val : Float deriving Repr, BEq, Inhabited
structure ShearRate_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ShearRate_R  where val : ℝ     deriving Inhabited

-- Strain rate: s⁻¹ (same units as shear rate but different context)
structure StrainRate_F where val : Float deriving Repr, BEq, Inhabited
structure StrainRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure StrainRate_R where val : ℝ     deriving Inhabited

-- Consistency index (power-law fluid): Pa·s^n
structure ConsistencyIndex_F where val : Float deriving Repr, BEq, Inhabited
structure ConsistencyIndex_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ConsistencyIndex_R where val : ℝ     deriving Inhabited

-- Flow behavior index: dimensionless
structure FlowIndex_F  where val : Float deriving Repr, BEq, Inhabited
structure FlowIndex_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FlowIndex_R  where val : ℝ     deriving Inhabited

-- Yield stress: Pa (using from Mechanics)

-- Storage modulus G': Pa
structure StorageModulus_F where val : Float deriving Repr, BEq, Inhabited
structure StorageModulus_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure StorageModulus_R where val : ℝ     deriving Inhabited

-- Loss modulus G'': Pa
structure LossModulus_F where val : Float deriving Repr, BEq, Inhabited
structure LossModulus_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LossModulus_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Dimensionless Numbers
================================================================================================
-/
-- Reynolds number: Re = ρvL/μ
structure Reynolds_F   where val : Float deriving Repr, BEq, Inhabited
structure Reynolds_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Reynolds_R   where val : ℝ     deriving Inhabited

-- Mach number: Ma = v/c
structure Mach_F       where val : Float deriving Repr, BEq, Inhabited
structure Mach_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Mach_R       where val : ℝ     deriving Inhabited

-- Froude number: Fr = v/√(gL)
structure Froude_F     where val : Float deriving Repr, BEq, Inhabited
structure Froude_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Froude_R     where val : ℝ     deriving Inhabited

-- Weber number: We = ρv²L/σ
structure Weber_F      where val : Float deriving Repr, BEq, Inhabited
structure Weber_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Weber_R      where val : ℝ     deriving Inhabited

-- Capillary number: Ca = μv/σ
structure Capillary_F  where val : Float deriving Repr, BEq, Inhabited
structure Capillary_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Capillary_R  where val : ℝ     deriving Inhabited

-- Strouhal number: St = fL/v
structure Strouhal_F   where val : Float deriving Repr, BEq, Inhabited
structure Strouhal_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Strouhal_R   where val : ℝ     deriving Inhabited

-- Euler number: Eu = Δp/(ρv²)
structure Euler_F      where val : Float deriving Repr, BEq, Inhabited
structure Euler_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Euler_R      where val : ℝ     deriving Inhabited

-- Cavitation number: Ca = (p - pv)/(½ρv²)
structure Cavitation_F where val : Float deriving Repr, BEq, Inhabited
structure Cavitation_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Cavitation_R where val : ℝ     deriving Inhabited

-- Drag coefficient: Cd
structure DragCoeff_F  where val : Float deriving Repr, BEq, Inhabited
structure DragCoeff_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DragCoeff_R  where val : ℝ     deriving Inhabited

-- Lift coefficient: Cl
structure LiftCoeff_F  where val : Float deriving Repr, BEq, Inhabited
structure LiftCoeff_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LiftCoeff_R  where val : ℝ     deriving Inhabited

-- Friction factor: f (Darcy or Fanning)
structure FrictionFactor_F where val : Float deriving Repr, BEq, Inhabited
structure FrictionFactor_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FrictionFactor_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Turbulence Parameters
================================================================================================
-/
-- Turbulent kinetic energy: m²/s²
structure TurbulentKE_F where val : Float deriving Repr, BEq, Inhabited
structure TurbulentKE_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TurbulentKE_R where val : ℝ     deriving Inhabited

-- Turbulent dissipation rate: m²/s³
structure Dissipation_F where val : Float deriving Repr, BEq, Inhabited
structure Dissipation_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Dissipation_R where val : ℝ     deriving Inhabited

-- Turbulence intensity: % (dimensionless)
structure TurbIntensity_F where val : Float deriving Repr, BEq, Inhabited
structure TurbIntensity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TurbIntensity_R where val : ℝ     deriving Inhabited

-- Eddy viscosity: Pa·s (same units as dynamic viscosity)
structure EddyViscosity_F where val : Float deriving Repr, BEq, Inhabited
structure EddyViscosity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EddyViscosity_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Multiphase Flow
================================================================================================
-/
-- Void fraction: dimensionless (0-1)
structure VoidFraction_F where val : Float deriving Repr, BEq, Inhabited
structure VoidFraction_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VoidFraction_R where val : ℝ     deriving Inhabited

-- Quality (vapor mass fraction): dimensionless (0-1)
structure Quality_F    where val : Float deriving Repr, BEq, Inhabited
structure Quality_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Quality_R    where val : ℝ     deriving Inhabited

-- Slip ratio: dimensionless
structure SlipRatio_F  where val : Float deriving Repr, BEq, Inhabited
structure SlipRatio_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SlipRatio_R  where val : ℝ     deriving Inhabited

-- Holdup: dimensionless (0-1)
structure Holdup_F     where val : Float deriving Repr, BEq, Inhabited
structure Holdup_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Holdup_R     where val : ℝ     deriving Inhabited

/--
================================================================================================
   Error Propagation & Measurement Helpers
================================================================================================
-/
-- Parametric Uncertainty Tracking with fluid context
structure FluidMeasured (α : Type) where
  value : α
  uncertainty : α
  temperature : Option Kelvin_F := none
  pressure : Option Pascal_F := none
  flow_regime : Option String := none  -- "laminar", "turbulent", "transitional"
  fluid_type : Option String := none   -- "Newtonian", "shear-thinning", etc.
  source : Option String := none
  deriving Repr, BEq, Inhabited

-- Measurement with uncertainty for viscosity
structure MeasuredViscosity_F where
  value : PascalSecond_F
  uncertainty : PascalSecond_F
  temperature : Option Kelvin_F := none
  shear_rate : Option ShearRate_F := none
  method : Option String := none  -- "capillary", "rotational", "falling ball"
  deriving Repr, BEq, Inhabited

-- Measurement with uncertainty for flow rate
structure MeasuredFlowRate_F where
  value : M3PerSecond_F
  uncertainty : M3PerSecond_F
  method : Option String := none  -- "orifice", "venturi", "turbine", "ultrasonic"
  calibration : Option String := none
  deriving Repr, BEq, Inhabited

-- Error propagation for Reynolds number
def reynoldsWithError_F (rho : FluidMeasured KgPerM3_F)
    (v : FluidMeasured Velocity_F) (L : FluidMeasured Meter_F)
    (mu : MeasuredViscosity_F) : FluidMeasured Reynolds_F :=
  let re := rho.value.val * v.value.val * L.value.val / mu.value.val
  let relErrorRho := rho.uncertainty.val / rho.value.val
  let relErrorV := v.uncertainty.val / v.value.val
  let relErrorL := L.uncertainty.val / L.value.val
  let relErrorMu := mu.uncertainty.val / mu.value.val
  let relError := Float.sqrt (relErrorRho^2 + relErrorV^2 + relErrorL^2 + relErrorMu^2)
  { value := ⟨re⟩
    uncertainty := ⟨re.abs * relError⟩
    source := some "Re = ρvL/μ" }

-- Error propagation for pressure drop (Darcy-Weisbach)
def pressureDropWithError_F (f : FluidMeasured FrictionFactor_F)
    (L : FluidMeasured Meter_F) (D : FluidMeasured Meter_F)
    (rho : FluidMeasured KgPerM3_F) (v : FluidMeasured Velocity_F)
    : FluidMeasured Pascal_F :=
  let dp := f.value.val * (L.value.val / D.value.val) * 0.5 * rho.value.val * v.value.val^2
  let relErrorF := f.uncertainty.val / f.value.val
  let relErrorL := L.uncertainty.val / L.value.val
  let relErrorD := D.uncertainty.val / D.value.val
  let relErrorRho := rho.uncertainty.val / rho.value.val
  let relErrorV := 2.0 * v.uncertainty.val / v.value.val  -- v is squared
  let relError := Float.sqrt (relErrorF^2 + relErrorL^2 + relErrorD^2 + relErrorRho^2 + relErrorV^2)
  { value := ⟨dp⟩
    uncertainty := ⟨dp * relError⟩
    source := some "Darcy-Weisbach equation" }

/--
================================================================================================
   Validation & Range Checking Helpers
================================================================================================
-/

-- Viscosity validation
def isValidViscosity_F (mu : PascalSecond_F) : Bool :=
  mu.val > 0.0

def isRealisticViscosity_F (mu : PascalSecond_F) : Bool :=
  mu.val > 0.0 && mu.val < 1e6  -- Up to very viscous materials like pitch

-- Reynolds number regime
def isLaminar_F (re : Reynolds_F) : Bool :=
  re.val < 2300.0  -- For pipe flow

def isTurbulent_F (re : Reynolds_F) : Bool :=
  re.val > 4000.0  -- For pipe flow

def isTransitional_F (re : Reynolds_F) : Bool :=
  2300.0 ≤ re.val && re.val ≤ 4000.0

-- Mach number regime
def isSubsonic_F (ma : Mach_F) : Bool :=
  ma.val < 0.8

def isTransonic_F (ma : Mach_F) : Bool :=
  0.8 ≤ ma.val && ma.val ≤ 1.2

def isSupersonic_F (ma : Mach_F) : Bool :=
  1.2 < ma.val && ma.val < 5.0

def isHypersonic_F (ma : Mach_F) : Bool :=
  ma.val ≥ 5.0

-- Froude number regime
def isSubcritical_F (fr : Froude_F) : Bool :=
  fr.val < 1.0

def isCritical_F (fr : Froude_F) : Bool :=
  0.95 ≤ fr.val && fr.val ≤ 1.05

def isSupercritical_F (fr : Froude_F) : Bool :=
  fr.val > 1.0

-- Flow rate validation
def isValidFlowRate_F (q : M3PerSecond_F) : Bool :=
  q.val ≥ 0.0

-- Void fraction validation
def isValidVoidFraction_F (alpha : VoidFraction_F) : Bool :=
  0.0 ≤ alpha.val && alpha.val ≤ 1.0

-- Quality validation
def isValidQuality_F (x : Quality_F) : Bool :=
  0.0 ≤ x.val && x.val ≤ 1.0

-- Drag coefficient validation
def isRealisticDragCoeff_F (cd : DragCoeff_F) : Bool :=
  0.0 < cd.val && cd.val < 10.0  -- Most objects

-- Surface tension validation
def isValidSurfaceTension_F (sigma : NewtonPerMeter_F) : Bool :=
  sigma.val ≥ 0.0

/--
================================================================================================
   Unit Conversions
================================================================================================
-/

-- Dynamic viscosity conversions
def pascalSecondToPoise_F (pas : PascalSecond_F) : Poise_F :=
  ⟨pas.val * 10.0⟩

def poiseToPascalSecond_F (p : Poise_F) : PascalSecond_F :=
  ⟨p.val / 10.0⟩

def pascalSecondToCentipoise_F (pas : PascalSecond_F) : Centipoise_F :=
  ⟨pas.val * 1000.0⟩

def centipoiseToPascalSecond_F (cp : Centipoise_F) : PascalSecond_F :=
  ⟨cp.val / 1000.0⟩

def pascalSecondToMilliPascalSecond_F (pas : PascalSecond_F) : MilliPascalSecond_F :=
  ⟨pas.val * 1000.0⟩

-- Kinematic viscosity conversions
def m2PerSecondToStokes_F (m2s : M2PerSecond_F) : Stokes_F :=
  ⟨m2s.val * 10000.0⟩

def stokesToM2PerSecond_F (st : Stokes_F) : M2PerSecond_F :=
  ⟨st.val / 10000.0⟩

def stokesToCentistokes_F (st : Stokes_F) : Centistokes_F :=
  ⟨st.val * 100.0⟩

def centistokesToStokes_F (cst : Centistokes_F) : Stokes_F :=
  ⟨cst.val / 100.0⟩

def m2PerSecondToCentistokes_F (m2s : M2PerSecond_F) : Centistokes_F :=
  ⟨m2s.val * 1e6⟩

-- Saybolt conversion (empirical formula)
def centistokesToSUS_F (cst : Centistokes_F) : SUS_F :=
  if cst.val < 40.0 then
    ⟨4.632 * cst.val + 1.0⟩
  else
    ⟨4.664 * cst.val - 1.25⟩

-- Surface tension conversions
def newtonPerMeterToDynePerCm_F (nm : NewtonPerMeter_F) : DynePerCm_F :=
  ⟨nm.val * 1000.0⟩

def dynePerCmToNewtonPerMeter_F (dyn : DynePerCm_F) : NewtonPerMeter_F :=
  ⟨dyn.val / 1000.0⟩

-- Flow rate conversions
def m3PerSecondToLiterPerSecond_F (m3s : M3PerSecond_F) : LiterPerSecond_F :=
  ⟨m3s.val * 1000.0⟩

def literPerSecondToM3PerSecond_F (ls : LiterPerSecond_F) : M3PerSecond_F :=
  ⟨ls.val / 1000.0⟩

def literPerMinuteToM3PerSecond_F (lpm : LiterPerMinute_F) : M3PerSecond_F :=
  ⟨lpm.val / 60000.0⟩

def m3PerSecondToGallonPerMinute_F (m3s : M3PerSecond_F) : GallonPerMinute_F :=
  ⟨m3s.val * 15850.32⟩  -- US gallons

def gallonPerMinuteToM3PerSecond_F (gpm : GallonPerMinute_F) : M3PerSecond_F :=
  ⟨gpm.val / 15850.32⟩

def m3PerSecondToCFM_F (m3s : M3PerSecond_F) : CFM_F :=
  ⟨m3s.val * 2118.88⟩

def cfmToM3PerSecond_F (cfm : CFM_F) : M3PerSecond_F :=
  ⟨cfm.val / 2118.88⟩

-- Mass flow rate conversions
def kgPerSecondToKgPerHour_F (kgs : KgPerSecond_F) : KgPerHour_F :=
  ⟨kgs.val * 3600.0⟩

def kgPerHourToKgPerSecond_F (kgh : KgPerHour_F) : KgPerSecond_F :=
  ⟨kgh.val / 3600.0⟩

-- Permeability conversions
def m2ToDarcy_F (m2 : Permeability_F) : Darcy_F :=
  ⟨m2.val / 9.869233e-13⟩

def darcyToM2_F (d : Darcy_F) : Permeability_F :=
  ⟨d.val * 9.869233e-13⟩

def darcyToMillidarcy_F (d : Darcy_F) : Millidarcy_F :=
  ⟨d.val * 1000.0⟩

/--
================================================================================================
   Common Fluid Mechanics Calculations
================================================================================================
-/

-- Reynolds number
def reynoldsNumber_F (rho : KgPerM3_F) (v : Velocity_F)
    (L : Meter_F) (mu : PascalSecond_F) : Reynolds_F :=
  ⟨rho.val * v.val * L.val / mu.val⟩

-- Alternative using kinematic viscosity
def reynoldsNumberKinematic_F (v : Velocity_F) (L : Meter_F)
    (nu : M2PerSecond_F) : Reynolds_F :=
  ⟨v.val * L.val / nu.val⟩

-- Mach number
def machNumber_F (v : Velocity_F) (c : Velocity_F) : Mach_F :=
  ⟨v.val / c.val⟩

-- Speed of sound in ideal gas
def speedOfSoundIdealGas_F (gamma : Float) (R : Float) (T : Kelvin_F)
    (M : Float) : Velocity_F :=  -- M is molar mass in kg/mol
  ⟨Float.sqrt (gamma * R * T.val / M)⟩

-- Froude number
def froudeNumber_F (v : Velocity_F) (L : Meter_F) : Froude_F :=
  ⟨v.val / Float.sqrt (g_standard_F * L.val)⟩

-- Weber number
def weberNumber_F (rho : KgPerM3_F) (v : Velocity_F) (L : Meter_F)
    (sigma : NewtonPerMeter_F) : Weber_F :=
  ⟨rho.val * v.val^2 * L.val / sigma.val⟩

-- Capillary number
def capillaryNumber_F (mu : PascalSecond_F) (v : Velocity_F)
    (sigma : NewtonPerMeter_F) : Capillary_F :=
  ⟨mu.val * v.val / sigma.val⟩

-- Strouhal number
def strouhalNumber_F (f : Hertz_F) (L : Meter_F) (v : Velocity_F) : Strouhal_F :=
  ⟨f.val * L.val / v.val⟩

-- Euler number
def eulerNumber_F (deltaP : Pascal_F) (rho : KgPerM3_F)
    (v : Velocity_F) : Euler_F :=
  ⟨deltaP.val / (rho.val * v.val^2)⟩

-- Kinematic viscosity from dynamic
def kinematicViscosity_F (mu : PascalSecond_F) (rho : KgPerM3_F) : M2PerSecond_F :=
  ⟨mu.val / rho.val⟩

-- Dynamic viscosity from kinematic
def dynamicViscosity_F (nu : M2PerSecond_F) (rho : KgPerM3_F) : PascalSecond_F :=
  ⟨nu.val * rho.val⟩

-- Pressure drop in pipe (Darcy-Weisbach)
def pressureDropPipe_F (f : FrictionFactor_F) (L : Meter_F) (D : Meter_F)
    (rho : KgPerM3_F) (v : Velocity_F) : Pascal_F :=
  ⟨f.val * (L.val / D.val) * 0.5 * rho.val * v.val^2⟩

-- Head loss
def headLoss_F (deltaP : Pascal_F) (rho : KgPerM3_F) : Meter_F :=
  ⟨deltaP.val / (rho.val * g_standard_F)⟩

-- Bernoulli equation (simplified)
def bernoulliPressure_F (p1 : Pascal_F) (rho : KgPerM3_F)
    (v1 : Velocity_F) (z1 : Meter_F)
    (v2 : Velocity_F) (z2 : Meter_F) : Pascal_F :=
  ⟨p1.val + 0.5 * rho.val * (v1.val^2 - v2.val^2) + rho.val * g_standard_F * (z1.val - z2.val)⟩

-- Hagen-Poiseuille flow rate (laminar pipe flow)
def hagenPoiseuilleFlow_F (deltaP : Pascal_F) (R : Meter_F)
    (L : Meter_F) (mu : PascalSecond_F) : M3PerSecond_F :=
  ⟨pi_F * deltaP.val * R.val^4 / (8.0 * mu.val * L.val)⟩

-- Stokes drag force on sphere
def stokesDrag_F (mu : PascalSecond_F) (R : Meter_F) (v : Velocity_F) : Newton_F :=
  ⟨6.0 * pi_F * mu.val * R.val * v.val⟩

-- Terminal velocity (Stokes regime)
def terminalVelocityStokes_F (rho_p : KgPerM3_F) (rho_f : KgPerM3_F)
    (R : Meter_F) (mu : PascalSecond_F) : Velocity_F :=
  ⟨2.0 * (rho_p.val - rho_f.val) * g_standard_F * R.val^2 / (9.0 * mu.val)⟩

-- Drag force
def dragForce_F (cd : DragCoeff_F) (rho : KgPerM3_F) (v : Velocity_F)
    (A : Meter2_F) : Newton_F :=
  ⟨0.5 * cd.val * rho.val * v.val^2 * A.val⟩

-- Lift force
def liftForce_F (cl : LiftCoeff_F) (rho : KgPerM3_F) (v : Velocity_F)
    (A : Meter2_F) : Newton_F :=
  ⟨0.5 * cl.val * rho.val * v.val^2 * A.val⟩

-- Hydrostatic pressure
def hydrostaticPressure_F (rho : KgPerM3_F) (h : Meter_F) : Pascal_F :=
  ⟨rho.val * g_standard_F * h.val⟩

-- Buoyancy force
def buoyancyForce_F (rho_fluid : KgPerM3_F) (V : Meter3_F) : Newton_F :=
  ⟨rho_fluid.val * g_standard_F * V.val⟩

-- Hydraulic diameter for non-circular ducts
def hydraulicDiameter_F (area : Meter2_F) (perimeter : Meter_F) : Meter_F :=
  ⟨4.0 * area.val / perimeter.val⟩

-- Power-law fluid viscosity
def powerLawViscosity_F (K : ConsistencyIndex_F) (n : FlowIndex_F)
    (gammaDot : ShearRate_F) : PascalSecond_F :=
  ⟨K.val * (gammaDot.val.abs ^ (n.val - 1.0))⟩

-- Turbulent kinetic energy from velocity fluctuations
def turbulentKineticEnergy_F (u_rms : Velocity_F) (v_rms : Velocity_F)
    (w_rms : Velocity_F) : TurbulentKE_F :=
  ⟨0.5 * (u_rms.val^2 + v_rms.val^2 + w_rms.val^2)⟩

-- Turbulence intensity
def turbulenceIntensity_F (u_rms : Velocity_F) (u_mean : Velocity_F)
    : TurbIntensity_F :=
  ⟨u_rms.val / u_mean.val⟩

-- Eddy viscosity from k-epsilon model
def eddyViscosity_F (rho : KgPerM3_F) (k : TurbulentKE_F)
    (epsilon : Dissipation_F) (C_mu : Float) : EddyViscosity_F :=
  ⟨C_mu * rho.val * k.val^2 / epsilon.val⟩

-- Two-phase flow: homogeneous density
def homogeneousDensity_F (rho_l : KgPerM3_F) (rho_g : KgPerM3_F)
    (alpha : VoidFraction_F) : KgPerM3_F :=
  ⟨(1.0 - alpha.val) * rho_l.val + alpha.val * rho_g.val⟩

-- Two-phase flow: mixture viscosity (McAdams correlation)
def mixtureViscosity_F (mu_l : PascalSecond_F) (mu_g : PascalSecond_F)
    (x : Quality_F) (rho_l : KgPerM3_F) (rho_g : KgPerM3_F) : PascalSecond_F :=
  let x_vol := x.val / (x.val + (1.0 - x.val) * rho_g.val / rho_l.val)
  ⟨1.0 / ((1.0 - x_vol) / mu_l.val + x_vol / mu_g.val)⟩

-- Darcy's law for porous media
def darcyVelocity_F (k : Permeability_F) (gradP : PascalPerMeter_F)
    (mu : PascalSecond_F) : Velocity_F :=
  ⟨k.val * gradP.val / mu.val⟩

-- Hydraulic conductivity
def hydraulicConductivityFromPerm_F (k : Permeability_F) (rho : KgPerM3_F)
    (mu : PascalSecond_F) : HydraulicConductivity_F :=
  ⟨k.val * rho.val * g_standard_F / mu.val⟩

-- Capillary pressure (Young-Laplace)
def capillaryPressure_F (sigma : NewtonPerMeter_F) (R : Meter_F) : Pascal_F :=
  ⟨2.0 * sigma.val / R.val⟩

-- Bond number (Eötvös number)
def bondNumber_F (rho_diff : KgPerM3_F) (L : Meter_F)
    (sigma : NewtonPerMeter_F) : Ratio_F :=
  ⟨rho_diff.val * g_standard_F * L.val^2 / sigma.val⟩

/--
================================================================================================
   Friction Factor Correlations
================================================================================================
-/

-- Blasius correlation (smooth pipes, turbulent)
def blasiusFrictionFactor_F (re : Reynolds_F) : FrictionFactor_F :=
  if re.val < 100000.0 then
    ⟨0.316 / (re.val ^ 0.25)⟩
  else
    ⟨0.0⟩  -- Not valid for Re > 100,000

-- Laminar friction factor
def laminarFrictionFactor_F (re : Reynolds_F) : FrictionFactor_F :=
  if re.val > 0.0 then
    ⟨64.0 / re.val⟩
  else
    ⟨0.0⟩

-- Colebrook-White (implicit - would need iterative solver)
-- This is just the structure; actual implementation would need Newton-Raphson
def colebrookWhiteGuess_F (re : Reynolds_F) (relRoughness : Float)
    : FrictionFactor_F :=
  -- Initial guess using Swamee-Jain approximation
  let term1 := relRoughness / 3.7
  let term2 := 5.74 / (re.val ^ 0.9)
  let logTerm := Float.log (term1 + term2) / Float.log 10.0
  ⟨0.25 / (logTerm^2)⟩

end Units.Physics.Fluids
