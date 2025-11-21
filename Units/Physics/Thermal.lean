-- Thermal.lean        -- Heat transfer, thermal conductivity, entropy
import LogosLibrary.Units.Core.SI
import LogosLibrary.Units.Physics.Mechanics
import LogosLibrary.Units.Physics.Electromagnetism
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

namespace Units.Physics.Thermal

open Units.Standard Units.Physics.Mechanics Units.Physics.Electromagnetism

/-
================================================================================
THERMAL PHYSICS UNITS LIBRARY
================================================================================

This module provides type-safe units for thermal physics, heat transfer,
thermodynamics, and thermal properties of materials.
Following the triple-type architecture for maximum flexibility without type
conversion friction.

## COVERAGE
- Heat capacity and specific heat (mass and molar bases)
- Thermal conductivity (various unit systems)
- Heat transfer coefficients (convection, radiation)
- Thermal expansion coefficients (linear, volumetric)
- Thermal diffusivity and effusivity
- Heat flux and thermal power density
- Thermal resistance and conductance
- Stefan-Boltzmann radiation quantities
- Entropy production rates
- Phase transition quantities

## USAGE PATTERNS
Float: Experimental measurements, sensor readings, numerical simulations,
iterative algorithms, display/visualization, real-time computation,
engineering tolerances, HVAC calculations, thermal management systems

ℚ: Exact thermodynamic ratios, crystallographic thermal expansion tensors,
specific heat ratios (γ = Cp/Cv), thermal network analysis, calibration standards

ℝ: Theoretical proofs, continuous function analysis, calculus-based derivations,
mathematical physics formulations, thermodynamic limit calculations,
formal verification of physical laws, critical phenomena analysis
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
   Heat Capacity & Specific Heat
================================================================================================
-/
-- Mass-specific heat capacity (J/(kg·K))
structure JPerKgK_F    where val : Float deriving Repr, BEq, Inhabited
structure JPerKgK_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JPerKgK_R    where val : ℝ     deriving Inhabited

structure kJPerKgK_F   where val : Float deriving Repr, BEq, Inhabited
structure kJPerKgK_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure kJPerKgK_R   where val : ℝ     deriving Inhabited

-- Volume-specific heat capacity (J/(m³·K))
structure JPerM3K_F    where val : Float deriving Repr, BEq, Inhabited
structure JPerM3K_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JPerM3K_R    where val : ℝ     deriving Inhabited

structure kJPerM3K_F   where val : Float deriving Repr, BEq, Inhabited
structure kJPerM3K_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure kJPerM3K_R   where val : ℝ     deriving Inhabited

-- Total heat capacity (J/K) - extensive property
structure JPerK_F      where val : Float deriving Repr, BEq, Inhabited
structure JPerK_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JPerK_R      where val : ℝ     deriving Inhabited

structure kJPerK_F     where val : Float deriving Repr, BEq, Inhabited
structure kJPerK_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure kJPerK_R     where val : ℝ     deriving Inhabited

/--
================================================================================================
   Thermal Conductivity
================================================================================================
-/
-- SI: W/(m·K)
structure WPerMK_F     where val : Float deriving Repr, BEq, Inhabited
structure WPerMK_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WPerMK_R     where val : ℝ     deriving Inhabited

-- Common in materials: W/(cm·K)
structure WPerCmK_F    where val : Float deriving Repr, BEq, Inhabited
structure WPerCmK_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WPerCmK_R    where val : ℝ     deriving Inhabited

-- Imperial: BTU/(hr·ft·°F)
structure BTUPerHrFtF_F where val : Float deriving Repr, BEq, Inhabited
structure BTUPerHrFtF_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BTUPerHrFtF_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Heat Transfer Coefficients
================================================================================================
-/
-- Convection coefficient: W/(m²·K)
structure WPerM2K_F    where val : Float deriving Repr, BEq, Inhabited
structure WPerM2K_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WPerM2K_R    where val : ℝ     deriving Inhabited

structure kWPerM2K_F   where val : Float deriving Repr, BEq, Inhabited
structure kWPerM2K_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure kWPerM2K_R   where val : ℝ     deriving Inhabited

-- Overall heat transfer coefficient (U-value)
structure UValue_F     where val : Float deriving Repr, BEq, Inhabited  -- W/(m²·K)
structure UValue_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure UValue_R     where val : ℝ     deriving Inhabited

-- Imperial: BTU/(hr·ft²·°F)
structure BTUPerHrFt2F_F where val : Float deriving Repr, BEq, Inhabited
structure BTUPerHrFt2F_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BTUPerHrFt2F_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Thermal Expansion Coefficients
================================================================================================
-/
-- Linear expansion: K⁻¹
structure PerKelvin_F  where val : Float deriving Repr, BEq, Inhabited
structure PerKelvin_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PerKelvin_R  where val : ℝ     deriving Inhabited

-- Volumetric expansion: K⁻¹ (same units but conceptually different)
structure VolExpPerK_F where val : Float deriving Repr, BEq, Inhabited
structure VolExpPerK_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VolExpPerK_R where val : ℝ     deriving Inhabited

-- Sometimes given in ppm/K
structure PPMPerK_F    where val : Float deriving Repr, BEq, Inhabited
structure PPMPerK_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PPMPerK_R    where val : ℝ     deriving Inhabited

/--
================================================================================================
   Heat Flux & Thermal Power
================================================================================================
-/
-- Heat flux density: W/m²
structure WPerM2_F     where val : Float deriving Repr, BEq, Inhabited
structure WPerM2_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WPerM2_R     where val : ℝ     deriving Inhabited

structure kWPerM2_F    where val : Float deriving Repr, BEq, Inhabited
structure kWPerM2_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure kWPerM2_R    where val : ℝ     deriving Inhabited

structure MWPerM2_F    where val : Float deriving Repr, BEq, Inhabited
structure MWPerM2_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MWPerM2_R    where val : ℝ     deriving Inhabited

-- Heat generation rate: W/m³
structure WPerM3_F     where val : Float deriving Repr, BEq, Inhabited
structure WPerM3_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WPerM3_R     where val : ℝ     deriving Inhabited

structure kWPerM3_F    where val : Float deriving Repr, BEq, Inhabited
structure kWPerM3_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure kWPerM3_R    where val : ℝ     deriving Inhabited

/--
================================================================================================
   Thermal Resistance & Conductance
================================================================================================
-/
-- Thermal resistance: K/W
structure KPerW_F      where val : Float deriving Repr, BEq, Inhabited
structure KPerW_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KPerW_R      where val : ℝ     deriving Inhabited

-- Thermal conductance: W/K
structure WPerK_F      where val : Float deriving Repr, BEq, Inhabited
structure WPerK_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WPerK_R      where val : ℝ     deriving Inhabited

-- Specific thermal resistance (R-value): (m²·K)/W
structure M2KPerW_F    where val : Float deriving Repr, BEq, Inhabited
structure M2KPerW_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure M2KPerW_R    where val : ℝ     deriving Inhabited

-- Imperial R-value: (hr·ft²·°F)/BTU
structure RValueImp_F  where val : Float deriving Repr, BEq, Inhabited
structure RValueImp_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RValueImp_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Thermal Diffusivity & Effusivity
================================================================================================
-/
-- Thermal diffusivity: m²/s
structure M2PerS_F     where val : Float deriving Repr, BEq, Inhabited
structure M2PerS_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure M2PerS_R     where val : ℝ     deriving Inhabited

structure Cm2PerS_F    where val : Float deriving Repr, BEq, Inhabited
structure Cm2PerS_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Cm2PerS_R    where val : ℝ     deriving Inhabited

structure Mm2PerS_F    where val : Float deriving Repr, BEq, Inhabited
structure Mm2PerS_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Mm2PerS_R    where val : ℝ     deriving Inhabited

-- Thermal effusivity: J/(m²·K·s^0.5) = W·s^0.5/(m²·K)
structure ThermalEffusivity_F where val : Float deriving Repr, BEq, Inhabited
structure ThermalEffusivity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ThermalEffusivity_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Stefan-Boltzmann & Radiation
================================================================================================
-/
-- Emissive power: W/m² (same as heat flux but conceptually for radiation)
structure EmissivePower_F where val : Float deriving Repr, BEq, Inhabited
structure EmissivePower_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EmissivePower_R where val : ℝ     deriving Inhabited

-- Stefan-Boltzmann constant units: W/(m²·K⁴)
structure WPerM2K4_F   where val : Float deriving Repr, BEq, Inhabited
structure WPerM2K4_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WPerM2K4_R   where val : ℝ     deriving Inhabited

-- Radiation heat transfer coefficient (linearized): W/(m²·K)
structure RadiationCoeff_F where val : Float deriving Repr, BEq, Inhabited
structure RadiationCoeff_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RadiationCoeff_R where val : ℝ     deriving Inhabited

-- View factor (dimensionless)
structure ViewFactor_F where val : Float deriving Repr, BEq, Inhabited
structure ViewFactor_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ViewFactor_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Entropy & Entropy Production
================================================================================================
-/
-- Entropy: J/K
structure Entropy_F    where val : Float deriving Repr, BEq, Inhabited
structure Entropy_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Entropy_R    where val : ℝ     deriving Inhabited

-- Specific entropy: J/(kg·K)
structure SpecificEntropy_F where val : Float deriving Repr, BEq, Inhabited
structure SpecificEntropy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpecificEntropy_R where val : ℝ     deriving Inhabited

-- Entropy production rate: W/K
structure EntropyProdRate_F where val : Float deriving Repr, BEq, Inhabited
structure EntropyProdRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EntropyProdRate_R where val : ℝ     deriving Inhabited

-- Entropy flux: W/(m²·K)
structure EntropyFlux_F where val : Float deriving Repr, BEq, Inhabited
structure EntropyFlux_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EntropyFlux_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Phase Transitions
================================================================================================
-/
-- Latent heat: J/kg
structure LatentHeat_F where val : Float deriving Repr, BEq, Inhabited
structure LatentHeat_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LatentHeat_R where val : ℝ     deriving Inhabited

structure kJPerKg_F    where val : Float deriving Repr, BEq, Inhabited
structure kJPerKg_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure kJPerKg_R    where val : ℝ     deriving Inhabited

-- Enthalpy of fusion/vaporization: kJ/mol (already in Monolith as kJPerMol)
-- Clapeyron slope: Pa/K
structure PaPerK_F     where val : Float deriving Repr, BEq, Inhabited
structure PaPerK_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PaPerK_R     where val : ℝ     deriving Inhabited

structure kPaPerK_F    where val : Float deriving Repr, BEq, Inhabited
structure kPaPerK_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure kPaPerK_R    where val : ℝ     deriving Inhabited

/--
================================================================================================
   Thermal Comfort & HVAC
================================================================================================
-/
-- Clothing insulation: clo (1 clo = 0.155 m²·K/W)
structure Clo_F        where val : Float deriving Repr, BEq, Inhabited
structure Clo_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Clo_R        where val : ℝ     deriving Inhabited

-- Metabolic rate: met (1 met = 58.2 W/m²)
structure Met_F        where val : Float deriving Repr, BEq, Inhabited
structure Met_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Met_R        where val : ℝ     deriving Inhabited

-- Thermal sensation scale (PMV: predicted mean vote)
structure PMV_F        where val : Float deriving Repr, BEq, Inhabited
structure PMV_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PMV_R        where val : ℝ     deriving Inhabited

/--
================================================================================================
   Dimensionless Numbers
================================================================================================
-/
structure Nusselt_F    where val : Float deriving Repr, BEq, Inhabited  -- Nu
structure Nusselt_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Nusselt_R    where val : ℝ     deriving Inhabited

structure Prandtl_F    where val : Float deriving Repr, BEq, Inhabited  -- Pr
structure Prandtl_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Prandtl_R    where val : ℝ     deriving Inhabited

structure Grashof_F    where val : Float deriving Repr, BEq, Inhabited  -- Gr
structure Grashof_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Grashof_R    where val : ℝ     deriving Inhabited

structure Rayleigh_F   where val : Float deriving Repr, BEq, Inhabited  -- Ra
structure Rayleigh_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Rayleigh_R   where val : ℝ     deriving Inhabited

structure Peclet_F     where val : Float deriving Repr, BEq, Inhabited  -- Pe
structure Peclet_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Peclet_R     where val : ℝ     deriving Inhabited

structure Fourier_F    where val : Float deriving Repr, BEq, Inhabited  -- Fo
structure Fourier_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Fourier_R    where val : ℝ     deriving Inhabited

structure Biot_F       where val : Float deriving Repr, BEq, Inhabited  -- Bi
structure Biot_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Biot_R       where val : ℝ     deriving Inhabited

structure Stanton_F    where val : Float deriving Repr, BEq, Inhabited  -- St
structure Stanton_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Stanton_R    where val : ℝ     deriving Inhabited

/--
================================================================================================
   Error Propagation & Measurement Helpers
================================================================================================
-/
-- Parametric Uncertainty Tracking with source
structure Measured (α : Type) where
  value : α
  uncertainty : α
  temp_range : Option (Kelvin_F × Kelvin_F) := none
  temperature : Option Kelvin_F := none
  pressure : Option Pascal_F := none
  source : Option String := none  -- "NIST 2022", etc.
  deriving Repr, BEq, Inhabited

-- Measurement with uncertainty for thermal quantities
structure MeasuredThermalConductivity_F where
  value : WPerMK_F
  uncertainty : WPerMK_F
  temp_range : Option (Kelvin_F × Kelvin_F) := none
  source : Option String := none
  deriving Repr, BEq, Inhabited

structure MeasuredHeatCapacity_F where
  value : JPerKgK_F
  uncertainty : JPerKgK_F
  temperature : Option Kelvin_F := none
  pressure : Option Pascal_F := none
  source : Option String := none
  deriving Repr, BEq, Inhabited

structure MeasuredThermalExpansion_F where
  value : PerKelvin_F
  uncertainty : PerKelvin_F
  temp_range : Option (Kelvin_F × Kelvin_F) := none
  material_state : Option String := none  -- "solid", "liquid", etc.
  deriving Repr, BEq, Inhabited

-- Error propagation for heat transfer calculations
def heatFluxWithError_F (k : MeasuredThermalConductivity_F)
    (deltaT : Kelvin_F) (deltaTError : Kelvin_F)
    (thickness : Meter_F) (thicknessError : Meter_F) : Measured WPerM2_F :=
  let flux := k.value.val * deltaT.val / thickness.val
  -- Error prop: q = k*ΔT/L → δq/q = sqrt((δk/k)² + (δΔT/ΔT)² + (δL/L)²)
  let relErrorK := k.uncertainty.val / k.value.val
  let relErrorT := deltaTError.val / deltaT.val
  let relErrorL := thicknessError.val / thickness.val
  let relError := Float.sqrt (relErrorK^2 + relErrorT^2 + relErrorL^2)
  { value := ⟨flux⟩
    uncertainty := ⟨flux * relError⟩
    source := some "Heat flux calculation" }

-- Error propagation for thermal resistance
def thermalResistanceWithError_F (thickness : Meter_F) (thicknessError : Meter_F)
    (k : MeasuredThermalConductivity_F)
    (area : Meter2_F) (areaError : Meter2_F) : Measured KPerW_F :=
  let resistance := thickness.val / (k.value.val * area.val)
  let relErrorL := thicknessError.val / thickness.val
  let relErrorK := k.uncertainty.val / k.value.val
  let relErrorA := areaError.val / area.val
  let relError := Float.sqrt (relErrorL^2 + relErrorK^2 + relErrorA^2)
  { value := ⟨resistance⟩
    uncertainty := ⟨resistance * relError⟩
    source := some "R = L/(k*A)" }

-- Error propagation for Stefan-Boltzmann radiation
def radiationHeatTransferWithError_F (emissivity : Fraction_F) (emissivityError : Fraction_F)
    (area : Meter2_F) (areaError : Meter2_F)
    (T1 : Kelvin_F) (T1Error : Kelvin_F)
    (T2 : Kelvin_F) (T2Error : Kelvin_F)
    (sigma : Float) : Measured Watt_F :=  -- sigma = 5.67e-8 W/(m²·K⁴)
  let T1_4 := T1.val^4
  let T2_4 := T2.val^4
  let Q := emissivity.val * sigma * area.val * (T1_4 - T2_4)
  -- Approximate error for T⁴ term: δ(T⁴)/T⁴ ≈ 4·δT/T
  let relErrorE := emissivityError.val / emissivity.val
  let relErrorA := areaError.val / area.val
  let relErrorT1 := 4.0 * T1Error.val / T1.val
  let relErrorT2 := 4.0 * T2Error.val / T2.val
  -- Combine errors (simplified - assumes T1 > T2)
  let relError := Float.sqrt (relErrorE^2 + relErrorA^2 +
                              (T1_4/(T1_4-T2_4))^2 * relErrorT1^2 +
                              (T2_4/(T1_4-T2_4))^2 * relErrorT2^2)
  { value := ⟨Q⟩
    uncertainty := ⟨Q.abs * relError⟩
    source := some "Stefan-Boltzmann radiation" }

/--
================================================================================================
   Validation & Range Checking Helpers
================================================================================================
-/

-- Temperature validation
def isValidTemperature_F (T : Kelvin_F) : Bool :=
  T.val ≥ 0.0  -- Above absolute zero

def isValidTemperature_Q (T : Kelvin_Q) : Bool :=
  T.val ≥ 0

noncomputable def isValidTemperature_R (T : Kelvin_R) : Prop :=
  T.val ≥ 0

-- Practical temperature ranges for materials
def isRealisticMaterialTemp_F (T : Kelvin_F) : Bool :=
  T.val ≥ 0.0 && T.val ≤ 6000.0  -- Up to surface of the Sun

-- Thermal conductivity validation (must be positive)
def isValidThermalConductivity_F (k : WPerMK_F) : Bool :=
  k.val > 0.0

def isValidThermalConductivity_Q (k : WPerMK_Q) : Bool :=
  k.val > 0

-- Heat capacity validation (must be positive)
def isValidHeatCapacity_F (c : JPerKgK_F) : Bool :=
  c.val > 0.0

-- Emissivity validation (0 ≤ ε ≤ 1)
def isValidEmissivity_F (e : Fraction_F) : Bool :=
  0.0 ≤ e.val && e.val ≤ 1.0

-- View factor validation (0 ≤ F ≤ 1)
def isValidViewFactor_F (f : ViewFactor_F) : Bool :=
  0.0 ≤ f.val && f.val ≤ 1.0

/--
================================================================================================
   Unit Conversions with Error Propagation
================================================================================================
-/

-- Thermal conductivity conversions
def wPerMKToBTUPerHrFtF_F (k : WPerMK_F) : BTUPerHrFtF_F :=
  ⟨k.val * 0.5778⟩  -- Conversion factor

def wPerMKToBTUPerHrFtFWithError_F (k : MeasuredThermalConductivity_F)
    : Measured BTUPerHrFtF_F :=
  { value := ⟨k.value.val * 0.5778⟩
    uncertainty := ⟨k.uncertainty.val * 0.5778⟩
    source := k.source }

-- Heat transfer coefficient conversions
def wPerM2KToBTUPerHrFt2F_F (h : WPerM2K_F) : BTUPerHrFt2F_F :=
  ⟨h.val * 0.1761⟩

-- R-value conversions (SI to Imperial)
def m2KPerWToRValueImp_F (r : M2KPerW_F) : RValueImp_F :=
  ⟨r.val * 5.678⟩

-- Specific heat conversions
def jPerKgKToBTUPerLbF_F (c : JPerKgK_F) : Float :=
  c.val * 0.000238846  -- BTU/(lb·°F)

/--
================================================================================================
   Common Thermal Calculations
================================================================================================
-/

-- Thermal diffusivity from properties
def thermalDiffusivity_F (k : WPerMK_F) (density : KgPerM3_F)
    (cp : JPerKgK_F) : M2PerS_F :=
  ⟨k.val / (density.val * cp.val)⟩

def thermalDiffusivityWithError_F (k : MeasuredThermalConductivity_F)
    (density : Measured KgPerM3_F) (cp : MeasuredHeatCapacity_F)
    : Measured M2PerS_F :=
  let alpha := k.value.val / (density.value.val * cp.value.val)
  let relErrorK := k.uncertainty.val / k.value.val
  let relErrorRho := density.uncertainty.val / density.value.val
  let relErrorCp := cp.uncertainty.val / cp.value.val
  let relError := Float.sqrt (relErrorK^2 + relErrorRho^2 + relErrorCp^2)
  { value := ⟨alpha⟩
    uncertainty := ⟨alpha * relError⟩
    source := some "α = k/(ρ·cp)" }

-- Thermal effusivity calculation
def thermalEffusivity_F (k : WPerMK_F) (density : KgPerM3_F)
    (cp : JPerKgK_F) : ThermalEffusivity_F :=
  ⟨Float.sqrt (k.val * density.val * cp.val)⟩

-- Biot number calculation
def biotNumber_F (h : WPerM2K_F) (L_char : Meter_F)
    (k : WPerMK_F) : Biot_F :=
  ⟨h.val * L_char.val / k.val⟩

-- Nusselt number for forced convection (empirical correlations would go here)
def nusseltForcedConvectionPlate_F (reynolds : Float) (prandtl : Prandtl_F)
    : Nusselt_F :=
  if reynolds < 5e5 then
    ⟨0.664 * (reynolds^0.5) * (prandtl.val^(1.0/3.0))⟩  -- Laminar
  else
    ⟨0.037 * (reynolds^0.8) * (prandtl.val^(1.0/3.0))⟩  -- Turbulent

-- Overall heat transfer coefficient for composite wall
def overallHeatTransferComposite_F (h1 : WPerM2K_F) -- Conv coeff side 1
    (thicknesses : Array Meter_F) (conductivities : Array WPerMK_F)
    (h2 : WPerM2K_F) -- Conv coeff side 2
    : UValue_F :=
  let convResistance1 := 1.0 / h1.val
  let convResistance2 := 1.0 / h2.val
  let condResistances := (thicknesses.zip conductivities).map fun (L, k) =>
    L.val / k.val
  let totalResistance := convResistance1 + condResistances.foldl (· + ·) 0.0 + convResistance2
  ⟨1.0 / totalResistance⟩

-- Heat capacity ratio (γ = Cp/Cv)
def heatCapacityRatio_F (cp : JPerKgK_F) (cv : JPerKgK_F) : Ratio_F :=
  ⟨cp.val / cv.val⟩

-- Logarithmic mean temperature difference (LMTD)
def LMTD_F (deltaT1 : Kelvin_F) (deltaT2 : Kelvin_F) : Kelvin_F :=
  if (deltaT1.val - deltaT2.val).abs < 0.001 then
    ⟨(deltaT1.val + deltaT2.val) / 2.0⟩  -- Arithmetic mean for nearly equal
  else
    ⟨(deltaT1.val - deltaT2.val) / Float.log (deltaT1.val / deltaT2.val)⟩

/--
================================================================================================
   Dimensionless Number Calculations
================================================================================================
-/

def rayleighNumber_F (g : Float) -- gravitational acceleration (9.81 m/s²)
    (beta : PerKelvin_F) (deltaT : Kelvin_F) (L : Meter_F)
    (nu : Float) -- kinematic viscosity (m²/s)
    (alpha : M2PerS_F) : Rayleigh_F :=
  ⟨g * beta.val * deltaT.val * (L.val^3) / (nu * alpha.val)⟩

def prandtlNumber_F (cp : JPerKgK_F) (mu : Float) -- dynamic viscosity (Pa·s)
    (k : WPerMK_F) : Prandtl_F :=
  ⟨cp.val * mu / k.val⟩

def pecletNumber_F (velocity : Float) (L : Meter_F)
    (alpha : M2PerS_F) : Peclet_F :=
  ⟨velocity * L.val / alpha.val⟩

def fourierNumber_F (alpha : M2PerS_F) (time : Second_F)
    (L : Meter_F) : Fourier_F :=
  ⟨alpha.val * time.val / (L.val^2)⟩

end Units.Physics.Thermal
