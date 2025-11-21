
-- Mechanics.lean      -- Force, torque, pressure, stress/strain
import LogosLibrary.Units.Core.SI
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Real.Pi.Irrational

namespace Units.Physics.Mechanics

open Units.Standard Real


/-
================================================================================
MECHANICS UNITS LIBRARY
================================================================================

This module provides type-safe units for classical mechanics, solid mechanics,
structural engineering, and material science.
Following the triple-type architecture for maximum flexibility without type
conversion friction.

## COVERAGE
- Forces and moments (Newton, pound-force, torque units)
- Pressure and stress (multiple unit systems)
- Strain and deformation (engineering and true strain)
- Elastic moduli (Young's, shear, bulk, Poisson's ratio)
- Fracture mechanics (stress intensity, J-integral, fracture toughness)
- Dynamics quantities (momentum, impulse, angular momentum)
- Work, energy, and power in mechanical context
- Viscosity and rheological properties
- Surface tension and interfacial mechanics
- Contact mechanics and tribology parameters

## USAGE PATTERNS
Float: Experimental measurements, sensor readings, numerical simulations,
finite element analysis, engineering calculations, real-time control systems,
fatigue testing, impact testing, material characterization

ℚ: Exact geometric ratios in crystalline materials, stoichiometric stress-strain
relationships, precise Poisson's ratios, calibration standards, discrete
dislocation dynamics, lattice mechanics

ℝ: Continuum mechanics theory, variational principles, energy minimization,
crack propagation models, constitutive law derivation, stability analysis,
formal verification of failure criteria
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
def phi_F : Float := 1.61803398874989484820  -- golden ratio

/--
================================================================================================
   Force & Weight
================================================================================================
-/
structure Newton_F     where val : Float deriving Repr, BEq, Inhabited
structure Newton_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Newton_R     where val : ℝ     deriving Inhabited

structure Kilonewton_F where val : Float deriving Repr, BEq, Inhabited
structure Kilonewton_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kilonewton_R where val : ℝ     deriving Inhabited

structure Meganewton_F where val : Float deriving Repr, BEq, Inhabited
structure Meganewton_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Meganewton_R where val : ℝ     deriving Inhabited

structure Millinewton_F where val : Float deriving Repr, BEq, Inhabited
structure Millinewton_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Millinewton_R where val : ℝ     deriving Inhabited

structure Micronewton_F where val : Float deriving Repr, BEq, Inhabited
structure Micronewton_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Micronewton_R where val : ℝ     deriving Inhabited

structure PoundForce_F where val : Float deriving Repr, BEq, Inhabited
structure PoundForce_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PoundForce_R where val : ℝ     deriving Inhabited

structure KilogramForce_F where val : Float deriving Repr, BEq, Inhabited
structure KilogramForce_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KilogramForce_R where val : ℝ     deriving Inhabited

structure Dyne_F       where val : Float deriving Repr, BEq, Inhabited
structure Dyne_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Dyne_R       where val : ℝ     deriving Inhabited

/--
================================================================================================
   Torque & Moment
================================================================================================
-/
structure NewtonMeter_F where val : Float deriving Repr, BEq, Inhabited
structure NewtonMeter_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NewtonMeter_R where val : ℝ     deriving Inhabited

structure NewtonCm_F   where val : Float deriving Repr, BEq, Inhabited
structure NewtonCm_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NewtonCm_R   where val : ℝ     deriving Inhabited

structure NewtonMm_F   where val : Float deriving Repr, BEq, Inhabited
structure NewtonMm_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NewtonMm_R   where val : ℝ     deriving Inhabited

structure FootPound_F  where val : Float deriving Repr, BEq, Inhabited
structure FootPound_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FootPound_R  where val : ℝ     deriving Inhabited

structure InchPound_F  where val : Float deriving Repr, BEq, Inhabited
structure InchPound_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure InchPound_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Pressure (expanding existing)
================================================================================================
-/
structure Pascal_F  where val : Float deriving Repr, BEq, Inhabited
structure Pascal_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Pascal_R  where val : ℝ     deriving Inhabited

structure Bar_F     where val : Float deriving Repr, BEq, Inhabited
structure Bar_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Bar_R     where val : ℝ     deriving Inhabited

structure Atm_F     where val : Float deriving Repr, BEq, Inhabited
structure Atm_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Atm_R     where val : ℝ     deriving Inhabited

structure Torr_F     where val : Float deriving Repr, BEq, Inhabited
structure Torr_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Torr_R     where val : ℝ     deriving Inhabited

structure MPa_F     where val : Float deriving Repr, BEq, Inhabited
structure MPa_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MPa_R     where val : ℝ     deriving Inhabited

structure GPa_F     where val : Float deriving Repr, BEq, Inhabited
structure GPa_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GPa_R     where val : ℝ     deriving Inhabited

structure KiloPascal_F where val : Float deriving Repr, BEq, Inhabited
structure KiloPascal_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KiloPascal_R where val : ℝ     deriving Inhabited

structure PSI_F        where val : Float deriving Repr, BEq, Inhabited -- pounds per square inch
structure PSI_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PSI_R        where val : ℝ     deriving Inhabited

structure KPSI_F       where val : Float deriving Repr, BEq, Inhabited
structure KPSI_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KPSI_R       where val : ℝ     deriving Inhabited

structure MmHg_F       where val : Float deriving Repr, BEq, Inhabited
structure MmHg_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MmHg_R       where val : ℝ     deriving Inhabited

structure InchHg_F     where val : Float deriving Repr, BEq, Inhabited
structure InchHg_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure InchHg_R     where val : ℝ     deriving Inhabited

structure MeterH2O_F   where val : Float deriving Repr, BEq, Inhabited
structure MeterH2O_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MeterH2O_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Stress (same units as pressure but conceptually different)
================================================================================================
-/
structure Stress_Pa_F  where val : Float deriving Repr, BEq, Inhabited
structure Stress_Pa_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Stress_Pa_R  where val : ℝ     deriving Inhabited

structure Stress_MPa_F where val : Float deriving Repr, BEq, Inhabited
structure Stress_MPa_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Stress_MPa_R where val : ℝ     deriving Inhabited

structure Stress_GPa_F where val : Float deriving Repr, BEq, Inhabited
structure Stress_GPa_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Stress_GPa_R where val : ℝ     deriving Inhabited

structure ShearStress_Pa_F where val : Float deriving Repr, BEq, Inhabited
structure ShearStress_Pa_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ShearStress_Pa_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Strain (dimensionless but distinct types for clarity)
================================================================================================
-/
structure Strain_F      where val : Float deriving Repr, BEq, Inhabited -- ΔL/L
structure Strain_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Strain_R      where val : ℝ     deriving Inhabited

structure Microstrain_F where val : Float deriving Repr, BEq, Inhabited -- με (×10⁻⁶)
structure Microstrain_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Microstrain_R where val : ℝ     deriving Inhabited

structure ShearStrain_F where val : Float deriving Repr, BEq, Inhabited
structure ShearStrain_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ShearStrain_R where val : ℝ     deriving Inhabited

structure TrueStrain_F  where val : Float deriving Repr, BEq, Inhabited -- ln(L/L₀)
structure TrueStrain_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TrueStrain_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Elastic Moduli
================================================================================================
-/
structure YoungModulus_Pa_F where val : Float deriving Repr, BEq, Inhabited
structure YoungModulus_Pa_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure YoungModulus_Pa_R where val : ℝ     deriving Inhabited

structure YoungModulus_GPa_F where val : Float deriving Repr, BEq, Inhabited
structure YoungModulus_GPa_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure YoungModulus_GPa_R where val : ℝ     deriving Inhabited

structure ShearModulus_Pa_F where val : Float deriving Repr, BEq, Inhabited
structure ShearModulus_Pa_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ShearModulus_Pa_R where val : ℝ     deriving Inhabited

structure ShearModulus_GPa_F where val : Float deriving Repr, BEq, Inhabited
structure ShearModulus_GPa_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ShearModulus_GPa_R where val : ℝ     deriving Inhabited

structure BulkModulus_Pa_F where val : Float deriving Repr, BEq, Inhabited
structure BulkModulus_Pa_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BulkModulus_Pa_R where val : ℝ     deriving Inhabited

structure BulkModulus_GPa_F where val : Float deriving Repr, BEq, Inhabited
structure BulkModulus_GPa_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BulkModulus_GPa_R where val : ℝ     deriving Inhabited

structure PoissonRatio_F where val : Float deriving Repr, BEq, Inhabited
structure PoissonRatio_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PoissonRatio_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Fracture Mechanics
================================================================================================
-/
-- Stress intensity factor: Pa·√m or MPa·√m
structure StressIntensity_PaSqrtM_F where val : Float deriving Repr, BEq, Inhabited
structure StressIntensity_PaSqrtM_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure StressIntensity_PaSqrtM_R where val : ℝ     deriving Inhabited

structure StressIntensity_MPaSqrtM_F where val : Float deriving Repr, BEq, Inhabited
structure StressIntensity_MPaSqrtM_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure StressIntensity_MPaSqrtM_R where val : ℝ     deriving Inhabited

-- J-integral: J/m² or N/m
structure JIntegral_F  where val : Float deriving Repr, BEq, Inhabited
structure JIntegral_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JIntegral_R  where val : ℝ     deriving Inhabited

-- Fracture toughness
structure FractureToughness_F where val : Float deriving Repr, BEq, Inhabited -- MPa·√m
structure FractureToughness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FractureToughness_R where val : ℝ     deriving Inhabited

-- Energy release rate: J/m²
structure EnergyReleaseRate_F where val : Float deriving Repr, BEq, Inhabited
structure EnergyReleaseRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EnergyReleaseRate_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Dynamics & Momentum
================================================================================================
-/
-- Linear momentum: kg·m/s
structure Momentum_F   where val : Float deriving Repr, BEq, Inhabited
structure Momentum_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Momentum_R   where val : ℝ     deriving Inhabited

-- Impulse: N·s
structure Impulse_F    where val : Float deriving Repr, BEq, Inhabited
structure Impulse_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Impulse_R    where val : ℝ     deriving Inhabited

-- Angular momentum: kg·m²/s
structure AngularMomentum_F where val : Float deriving Repr, BEq, Inhabited
structure AngularMomentum_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AngularMomentum_R where val : ℝ     deriving Inhabited

-- Moment of inertia: kg·m²
structure MomentOfInertia_F where val : Float deriving Repr, BEq, Inhabited
structure MomentOfInertia_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MomentOfInertia_R where val : ℝ     deriving Inhabited

-- Angular velocity: rad/s
structure RadPerS_F    where val : Float deriving Repr, BEq, Inhabited
structure RadPerS_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RadPerS_R    where val : ℝ     deriving Inhabited

-- Angular acceleration: rad/s²
structure RadPerS2_F   where val : Float deriving Repr, BEq, Inhabited
structure RadPerS2_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RadPerS2_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Work, Energy & Power
================================================================================================
-/
-- Work/Energy: Joule (N·m)
structure Work_J_F     where val : Float deriving Repr, BEq, Inhabited
structure Work_J_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Work_J_R     where val : ℝ     deriving Inhabited

structure Work_kJ_F    where val : Float deriving Repr, BEq, Inhabited
structure Work_kJ_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Work_kJ_R    where val : ℝ     deriving Inhabited

-- Power: Watt (J/s)
structure Power_W_F    where val : Float deriving Repr, BEq, Inhabited
structure Power_W_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Power_W_R    where val : ℝ     deriving Inhabited

structure Power_kW_F   where val : Float deriving Repr, BEq, Inhabited
structure Power_kW_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Power_kW_R   where val : ℝ     deriving Inhabited

structure Power_MW_F   where val : Float deriving Repr, BEq, Inhabited
structure Power_MW_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Power_MW_R   where val : ℝ     deriving Inhabited

structure Horsepower_F where val : Float deriving Repr, BEq, Inhabited
structure Horsepower_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Horsepower_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Surface Mechanics
================================================================================================
-/
-- Surface tension: N/m or mN/m
structure SurfaceTension_NPerM_F where val : Float deriving Repr, BEq, Inhabited
structure SurfaceTension_NPerM_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SurfaceTension_NPerM_R where val : ℝ     deriving Inhabited

structure SurfaceTension_mNPerM_F where val : Float deriving Repr, BEq, Inhabited
structure SurfaceTension_mNPerM_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SurfaceTension_mNPerM_R where val : ℝ     deriving Inhabited

-- Surface energy: J/m²
structure SurfaceEnergy_F where val : Float deriving Repr, BEq, Inhabited
structure SurfaceEnergy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SurfaceEnergy_R where val : ℝ     deriving Inhabited

-- Adhesion work
structure AdhesionWork_F where val : Float deriving Repr, BEq, Inhabited -- J/m²
structure AdhesionWork_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AdhesionWork_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Tribology & Contact Mechanics
================================================================================================
-/
-- Coefficient of friction (dimensionless)
structure FrictionCoeff_F where val : Float deriving Repr, BEq, Inhabited
structure FrictionCoeff_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FrictionCoeff_R where val : ℝ     deriving Inhabited

-- Wear rate: mm³/(N·m)
structure WearRate_F   where val : Float deriving Repr, BEq, Inhabited
structure WearRate_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WearRate_R   where val : ℝ     deriving Inhabited

-- Hardness: Various scales
structure Hardness_HV_F where val : Float deriving Repr, BEq, Inhabited -- Vickers
structure Hardness_HV_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Hardness_HV_R where val : ℝ     deriving Inhabited

structure Hardness_HB_F where val : Float deriving Repr, BEq, Inhabited -- Brinell
structure Hardness_HB_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Hardness_HB_R where val : ℝ     deriving Inhabited

structure Hardness_HRC_F where val : Float deriving Repr, BEq, Inhabited -- Rockwell C
structure Hardness_HRC_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Hardness_HRC_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Fatigue & Durability
================================================================================================
-/
-- Fatigue strength/limit: MPa
structure FatigueStrength_MPa_F where val : Float deriving Repr, BEq, Inhabited
structure FatigueStrength_MPa_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FatigueStrength_MPa_R where val : ℝ     deriving Inhabited

-- Cycles to failure
structure CyclesToFailure where val : ℕ deriving Repr, BEq, DecidableEq, Inhabited

-- Stress ratio
structure StressRatio_F where val : Float deriving Repr, BEq, Inhabited
structure StressRatio_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure StressRatio_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Compliance & Stiffness
================================================================================================
-/
-- Spring constant: N/m
structure SpringConstant_F where val : Float deriving Repr, BEq, Inhabited
structure SpringConstant_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpringConstant_R where val : ℝ     deriving Inhabited

-- Torsional stiffness: N·m/rad
structure TorsionalStiffness_F where val : Float deriving Repr, BEq, Inhabited
structure TorsionalStiffness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TorsionalStiffness_R where val : ℝ     deriving Inhabited

-- Compliance: m/N (inverse of stiffness)
structure Compliance_F where val : Float deriving Repr, BEq, Inhabited
structure Compliance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Compliance_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Error Propagation & Measurement Helpers
================================================================================================
-/
-- Parametric Uncertainty Tracking with source
structure Measured (α : Type) where
  value : α
  uncertainty : α
  source : Option String := none  -- "NIST 2022", etc.
  deriving Repr, BEq, Inhabited

-- Measured mechanics quantities
structure MeasuredForce_F where
  value : Newton_F
  uncertainty : Newton_F
  direction : Option (Float × Float × Float) := none -- unit vector
  point_of_application : Option String := none
  source : Option String := none
  deriving Repr, BEq, Inhabited

structure MeasuredStress_F where
  value : Stress_MPa_F
  uncertainty : Stress_MPa_F
  type : Option String := none -- "tensile", "compressive", "shear"
  temperature : Option Kelvin_F := none
  strain_rate : Option PerSecond_F := none
  deriving Repr, BEq, Inhabited

structure MeasuredStrain_F where
  value : Strain_F
  uncertainty : Strain_F
  type : Option String := none -- "elastic", "plastic", "total"
  measurement_method : Option String := none -- "extensometer", "DIC", "strain gauge"
  deriving Repr, BEq, Inhabited

structure MeasuredModulus_F where
  value : YoungModulus_GPa_F
  uncertainty : YoungModulus_GPa_F
  temperature : Option Kelvin_F := none
  test_standard : Option String := none -- "ASTM E8", etc.
  deriving Repr, BEq, Inhabited

-- Error propagation for stress calculation
def stressWithError_F (force : MeasuredForce_F) (area : Meter2_F)
    (areaError : Meter2_F) : MeasuredStress_F :=
  let stress := force.value.val / area.val
  let relErrorF := force.uncertainty.val / force.value.val
  let relErrorA := areaError.val / area.val
  let relError := Float.sqrt (relErrorF^2 + relErrorA^2)
  { value := ⟨stress * 1e-6⟩ -- Convert Pa to MPa
    uncertainty := ⟨stress * relError * 1e-6⟩
    type := some "normal"
    temperature := none
    strain_rate := none }

-- Error propagation for Young's modulus
def youngModulusWithError_F (stress : MeasuredStress_F)
    (strain : MeasuredStrain_F) : MeasuredModulus_F :=
  let E := stress.value.val / strain.value.val  -- Already in MPa
  let relErrorStress := stress.uncertainty.val / stress.value.val
  let relErrorStrain := strain.uncertainty.val / strain.value.val
  let relError := Float.sqrt (relErrorStress^2 + relErrorStrain^2)
  { value := ⟨E * 0.001⟩  -- Convert MPa to GPa
    uncertainty := ⟨E * relError * 0.001⟩
    temperature := stress.temperature
    test_standard := none }

-- Error propagation for torque
def torqueWithError_F (force : MeasuredForce_F) (leverArm : Meter_F)
    (leverArmError : Meter_F) : Measured NewtonMeter_F :=
  let torque := force.value.val * leverArm.val
  let relErrorF := force.uncertainty.val / force.value.val
  let relErrorL := leverArmError.val / leverArm.val
  let relError := Float.sqrt (relErrorF^2 + relErrorL^2)
  { value := ⟨torque⟩
    uncertainty := ⟨torque * relError⟩
    source := some "T = F × r" }

/--
================================================================================================
   Validation & Range Checking
================================================================================================
-/

-- Poisson's ratio validation (-1 < ν < 0.5 for isotropic materials)
def isValidPoissonRatio_F (nu : PoissonRatio_F) : Bool :=
  -1.0 < nu.val && nu.val < 0.5

def isThermodynamicallyStablePoissonRatio_F (nu : PoissonRatio_F) : Bool :=
  -1.0 < nu.val && nu.val ≤ 0.5  -- Equality allowed for incompressible materials

-- Moduli relationship validation (for isotropic materials)
def areModuliConsistent_F (E : YoungModulus_GPa_F) (G : ShearModulus_GPa_F)
    (nu : PoissonRatio_F) : Bool :=
  let G_calc := E.val / (2.0 * (1.0 + nu.val))
  (G.val - G_calc).abs / G.val < 0.01  -- Within 1% tolerance

-- Strain validation
def isPhysicalStrain_F (strain : Strain_F) : Bool :=
  strain.val > -1.0  -- Cannot compress to zero length

-- Friction coefficient validation
def isValidFrictionCoeff_F (mu : FrictionCoeff_F) : Bool :=
  mu.val ≥ 0.0  -- Must be non-negative

-- Fracture toughness validation (must be positive)
def isValidFractureToughness_F (K_IC : FractureToughness_F) : Bool :=
  K_IC.val > 0.0

/--
================================================================================================
   Unit Conversions
================================================================================================
-/

-- Force conversions
def newtonToPoundForce_F (n : Newton_F) : PoundForce_F :=
  ⟨n.val * 0.224809⟩

def poundForceToNewton_F (lbf : PoundForce_F) : Newton_F :=
  ⟨lbf.val * 4.44822⟩

def newtonToKilogramForce_F (n : Newton_F) : KilogramForce_F :=
  ⟨n.val / 9.80665⟩

-- Pressure conversions
def pascalToPSI_F (p : Pascal_F) : PSI_F :=
  ⟨p.val * 0.000145038⟩

def psiToPascal_F (psi : PSI_F) : Pascal_F :=
  ⟨psi.val * 6894.76⟩

def barToAtm_F (bar : Bar_F) : Atm_F :=
  ⟨bar.val / 1.01325⟩

def torrToMmHg_F (torr : Torr_F) : MmHg_F :=
  ⟨torr.val⟩  -- These are essentially the same

-- Torque conversions
def newtonMeterToFootPound_F (nm : NewtonMeter_F) : FootPound_F :=
  ⟨nm.val * 0.737562⟩

def footPoundToNewtonMeter_F (ftlb : FootPound_F) : NewtonMeter_F :=
  ⟨ftlb.val * 1.35582⟩

-- Power conversions
def wattToHorsepower_F (w : Power_W_F) : Horsepower_F :=
  ⟨w.val / 745.7⟩

def horsepowerToWatt_F (hp : Horsepower_F) : Power_W_F :=
  ⟨hp.val * 745.7⟩

-- Strain conversions
def strainToMicrostrain_F (s : Strain_F) : Microstrain_F :=
  ⟨s.val * 1e6⟩

def microstrainToStrain_F (us : Microstrain_F) : Strain_F :=
  ⟨us.val * 1e-6⟩

def engineeringToTrueStrain_F (eng : Strain_F) : TrueStrain_F :=
  ⟨Float.log (1.0 + eng.val)⟩

/--
================================================================================================
   Common Mechanics Calculations
================================================================================================
-/

-- Hooke's Law
def hookeStress_F (E : YoungModulus_GPa_F) (strain : Strain_F) : Stress_MPa_F :=
  ⟨E.val * 1000.0 * strain.val⟩

-- Shear modulus from Young's modulus and Poisson's ratio
def shearModulusFromE_F (E : YoungModulus_GPa_F) (nu : PoissonRatio_F)
    : ShearModulus_GPa_F :=
  ⟨E.val / (2.0 * (1.0 + nu.val))⟩

-- Bulk modulus from Young's modulus and Poisson's ratio
def bulkModulusFromE_F (E : YoungModulus_GPa_F) (nu : PoissonRatio_F)
    : BulkModulus_GPa_F :=
  ⟨E.val / (3.0 * (1.0 - 2.0 * nu.val))⟩

-- Stress concentration factor application
def concentratedStress_F (nominal : Stress_MPa_F) (Kt : Float) : Stress_MPa_F :=
  ⟨nominal.val * Kt⟩

-- Von Mises stress (for 3D stress state)
def vonMisesStress_F (σ1 σ2 σ3 : Stress_MPa_F) : Stress_MPa_F :=
  let term1 := (σ1.val - σ2.val)^2
  let term2 := (σ2.val - σ3.val)^2
  let term3 := (σ3.val - σ1.val)^2
  ⟨Float.sqrt (0.5 * (term1 + term2 + term3))⟩

-- Principal stress from 2D stress state
def principalStresses2D_F (σx σy : Stress_MPa_F) (τxy : ShearStress_Pa_F)
    : (Stress_MPa_F × Stress_MPa_F) :=
  let σ_avg := (σx.val + σy.val) / 2.0
  let R := Float.sqrt (((σx.val - σy.val) / 2.0)^2 + (τxy.val * 1e-6)^2)
  (⟨σ_avg + R⟩, ⟨σ_avg - R⟩)

-- Moment of inertia for rectangle
def rectangleMomentOfInertia_F (base height : Meter_F) : Float :=
  base.val * height.val^3 / 12.0

-- Centrifugal force
def centrifugalForce_F (mass : Kilogram_F) (radius : Meter_F)
    (omega : RadPerS_F) : Newton_F :=
  ⟨mass.val * radius.val * omega.val^2⟩

-- Spring energy
def springEnergy_F (k : SpringConstant_F) (x : Meter_F) : Work_J_F :=
  ⟨0.5 * k.val * x.val^2⟩

-- Impact force (simplified, assuming rigid body)
def impactForce_F (mass : Kilogram_F) (velocity : Float)
    (decelTime : Second_F) : Newton_F :=
  ⟨mass.val * velocity / decelTime.val⟩

-- Critical buckling load (Euler formula for pinned column)
def eulerBucklingLoad_F (E : YoungModulus_GPa_F) (I : Float) -- moment of inertia
    (length : Meter_F) : Newton_F :=
  let E_Pa := E.val * 1e9
  ⟨pi_F^2 * E_Pa * I / length.val^2⟩

-- Hertz contact stress
def hertzContactPressure_F (force : Newton_F) (radius1 radius2 : Meter_F)
    (E1 E2 : YoungModulus_GPa_F) (nu1 nu2 : PoissonRatio_F) : Stress_MPa_F :=
  let R_eff := (radius1.val * radius2.val) / (radius1.val + radius2.val)
  let E1_Pa := E1.val * 1e9
  let E2_Pa := E2.val * 1e9
  let E_eff_inv := (1.0 - nu1.val^2) / E1_Pa + (1.0 - nu2.val^2) / E2_Pa
  let E_eff := 1.0 / E_eff_inv
  let a := (3.0 * force.val * R_eff / (4.0 * E_eff))^(1.0/3.0)
  let p_max := 3.0 * force.val / (2.0 * pi_F * a^2)
  ⟨p_max * 1e-6⟩  -- Convert to MPa

-- Paris law for fatigue crack growth
def parisCrackGrowth_F (C : Float) (m : Float)
    (deltaK : StressIntensity_MPaSqrtM_F) : Float :=
  C * deltaK.val^m  -- da/dN in m/cycle

end Units.Physics.Mechanics
