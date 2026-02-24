-- Bio.lean        -- Biological concentrations, rates, medical units
import LogosLibrary.Units.Core
import LogosLibrary.Units.Chemistry
import LogosLibrary.Units.Mechanics
import LogosLibrary.Units.Electromagnetism
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

namespace Units.Bio

open Units.SI Units.Mechanics Units.Electromagnetism Chemistry

/-
================================================================================
BIOLOGICAL UNITS LIBRARY
================================================================================

This module provides type-safe units for biological systems, biochemistry,
medical measurements, and physiological processes.
Following the triple-type architecture for maximum flexibility without type
conversion friction.

## COVERAGE
- Molar and mass concentrations (mM, µM, nM, mg/dL, g/L)
- Enzyme kinetics (kcat, Km, Vmax, specific activity)
- Cell biology (cell density, doubling time, growth rates)
- Medical dosing (mg/kg, units/kg, IU)
- Vital signs and physiological rates
- pH, pKa, and acid-base chemistry
- Osmolarity and tonicity
- Biological energetics (ATP turnover, metabolic rates)
- Flow rates (perfusion, clearance, GFR)
- Lab values and clinical chemistry

## USAGE PATTERNS
Float: Clinical measurements, sensor data, real-time monitoring,
drug dosing calculations, iterative fitting of dose-response curves,
flow cytometry data, spectrophotometry readings, PCR cycles

ℚ: Stoichiometric ratios, dilution factors, molecular ratios,
exact concentration preparations, buffer calculations, unit conversions,
genetic ratios (Mendelian inheritance), exact molecular weights

ℝ: Theoretical models, continuous rate equations, Michaelis-Menten derivations,
population dynamics, pharmacokinetic models, diffusion equations,
formal proofs of biochemical equilibria, reaction-diffusion systems
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
def ln10_F : Float := 2.30258509299404568402
def sqrt2_F : Float := 1.41421356237309504880
def avogadro_F : Float := 6.02214076e23


/--
================================================================================================
   Mass Concentrations
================================================================================================
-/
-- Grams per liter: g/L
structure GPerL_F      where val : Float deriving Repr, BEq, Inhabited
structure GPerL_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GPerL_R      where val : ℝ     deriving Inhabited

-- Milligrams per liter: mg/L
structure MgPerL_F     where val : Float deriving Repr, BEq, Inhabited
structure MgPerL_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MgPerL_R     where val : ℝ     deriving Inhabited

-- Micrograms per liter: µg/L
structure UgPerL_F     where val : Float deriving Repr, BEq, Inhabited
structure UgPerL_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure UgPerL_R     where val : ℝ     deriving Inhabited

-- Clinical: mg/dL (milligrams per deciliter)
structure MgPerDL_F    where val : Float deriving Repr, BEq, Inhabited
structure MgPerDL_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MgPerDL_R    where val : ℝ     deriving Inhabited

-- Clinical: g/dL (grams per deciliter)
structure GPerDL_F     where val : Float deriving Repr, BEq, Inhabited
structure GPerDL_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GPerDL_R     where val : ℝ     deriving Inhabited

/--
================================================================================================
   Parts Per X Concentrations
================================================================================================
-/
-- Parts per million: ppm (mg/kg or mg/L for water)
structure PPM_F        where val : Float deriving Repr, BEq, Inhabited
structure PPM_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PPM_R        where val : ℝ     deriving Inhabited

-- Parts per billion: ppb (µg/kg or µg/L for water)
structure PPB_F        where val : Float deriving Repr, BEq, Inhabited
structure PPB_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PPB_R        where val : ℝ     deriving Inhabited

-- Parts per trillion: ppt (ng/kg or ng/L for water)
structure PPT_F        where val : Float deriving Repr, BEq, Inhabited
structure PPT_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PPT_R        where val : ℝ     deriving Inhabited


/--
================================================================================================
   Enzyme Kinetics
================================================================================================
-/
-- Turnover number: s⁻¹
structure Kcat_F       where val : Float deriving Repr, BEq, Inhabited
structure Kcat_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kcat_R       where val : ℝ     deriving Inhabited

-- Michaelis constant: M (or mM, µM)
structure Km_F         where val : Float deriving Repr, BEq, Inhabited
structure Km_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Km_R         where val : ℝ     deriving Inhabited

-- Maximum velocity: mol/(L·s) or µmol/(min·mg)
structure Vmax_F       where val : Float deriving Repr, BEq, Inhabited
structure Vmax_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Vmax_R       where val : ℝ     deriving Inhabited

-- Specific activity: units/mg or µmol/(min·mg)
structure SpecificActivity_F where val : Float deriving Repr, BEq, Inhabited
structure SpecificActivity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpecificActivity_R where val : ℝ     deriving Inhabited

-- Catalytic efficiency: M⁻¹s⁻¹
structure CatalyticEfficiency_F where val : Float deriving Repr, BEq, Inhabited
structure CatalyticEfficiency_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CatalyticEfficiency_R where val : ℝ     deriving Inhabited

-- International Units for enzyme activity
structure IU_F         where val : Float deriving Repr, BEq, Inhabited
structure IU_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure IU_R         where val : ℝ     deriving Inhabited

-- Katal: mol/s (SI unit for catalytic activity)
structure Katal_F      where val : Float deriving Repr, BEq, Inhabited
structure Katal_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Katal_R      where val : ℝ     deriving Inhabited

/--
================================================================================================
   Cell Biology
================================================================================================
-/
-- Cell density: cells/mL or cells/L
structure CellsPerML_F where val : Float deriving Repr, BEq, Inhabited
structure CellsPerML_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CellsPerML_R where val : ℝ     deriving Inhabited

structure CellsPerL_F  where val : Float deriving Repr, BEq, Inhabited
structure CellsPerL_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CellsPerL_R  where val : ℝ     deriving Inhabited

-- Growth rate: h⁻¹ or day⁻¹
structure GrowthRate_F where val : Float deriving Repr, BEq, Inhabited
structure GrowthRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GrowthRate_R where val : ℝ     deriving Inhabited

-- Doubling time: hours or minutes
structure DoublingTime_F where val : Float deriving Repr, BEq, Inhabited
structure DoublingTime_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DoublingTime_R where val : ℝ     deriving Inhabited

-- Optical density (OD) at specific wavelength (dimensionless)
structure OD600_F      where val : Float deriving Repr, BEq, Inhabited
structure OD600_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure OD600_R      where val : ℝ     deriving Inhabited

-- Colony forming units: CFU/mL
structure CFUPerML_F   where val : Float deriving Repr, BEq, Inhabited
structure CFUPerML_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CFUPerML_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Medical Dosing Units
================================================================================================
-/
-- Dose per body weight: mg/kg
structure MgPerKg_F    where val : Float deriving Repr, BEq, Inhabited
structure MgPerKg_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MgPerKg_R    where val : ℝ     deriving Inhabited

-- Micrograms per kilogram: µg/kg
structure UgPerKg_F    where val : Float deriving Repr, BEq, Inhabited
structure UgPerKg_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure UgPerKg_R    where val : ℝ     deriving Inhabited

-- Units per kilogram: U/kg (for insulin, heparin, etc.)
structure UnitsPerKg_F where val : Float deriving Repr, BEq, Inhabited
structure UnitsPerKg_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure UnitsPerKg_R where val : ℝ     deriving Inhabited

-- International units per liter: IU/L
structure IUPerL_F     where val : Float deriving Repr, BEq, Inhabited
structure IUPerL_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure IUPerL_R     where val : ℝ     deriving Inhabited

-- Milliequivalents: mEq
structure MEq_F        where val : Float deriving Repr, BEq, Inhabited
structure MEq_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MEq_R        where val : ℝ     deriving Inhabited

-- Milliequivalents per liter: mEq/L
structure MEqPerL_F    where val : Float deriving Repr, BEq, Inhabited
structure MEqPerL_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MEqPerL_R    where val : ℝ     deriving Inhabited

/--
================================================================================================
   Flow Rates and Clearance
================================================================================================
-/
-- Milliliters per minute: mL/min
structure MLPerMin_F   where val : Float deriving Repr, BEq, Inhabited
structure MLPerMin_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MLPerMin_R   where val : ℝ     deriving Inhabited

-- Liters per minute: L/min
structure LPerMin_F    where val : Float deriving Repr, BEq, Inhabited
structure LPerMin_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LPerMin_R    where val : ℝ     deriving Inhabited

-- Glomerular filtration rate: mL/min/1.73m²
structure GFR_F        where val : Float deriving Repr, BEq, Inhabited
structure GFR_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GFR_R        where val : ℝ     deriving Inhabited

-- Cardiac output: L/min
structure CardiacOutput_F where val : Float deriving Repr, BEq, Inhabited
structure CardiacOutput_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CardiacOutput_R where val : ℝ     deriving Inhabited

-- Perfusion: mL/(min·g) or mL/(min·100g)
structure Perfusion_F  where val : Float deriving Repr, BEq, Inhabited
structure Perfusion_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Perfusion_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Vital Signs
================================================================================================
-/
-- Heart rate: beats/min
structure BeatsPerMin_F where val : Float deriving Repr, BEq, Inhabited
structure BeatsPerMin_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BeatsPerMin_R where val : ℝ     deriving Inhabited

-- Respiratory rate: breaths/min
structure BreathsPerMin_F where val : Float deriving Repr, BEq, Inhabited
structure BreathsPerMin_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BreathsPerMin_R where val : ℝ     deriving Inhabited

-- Blood pressure: mmHg
structure MmHg_F       where val : Float deriving Repr, BEq, Inhabited
structure MmHg_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MmHg_R       where val : ℝ     deriving Inhabited

-- Oxygen saturation: % (0-100)
structure SpO2_F       where val : Float deriving Repr, BEq, Inhabited
structure SpO2_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpO2_R       where val : ℝ     deriving Inhabited

/--
================================================================================================
   Osmolarity and Tonicity
================================================================================================
-/
-- Osmolarity: mOsm/L
structure MOsmPerL_F   where val : Float deriving Repr, BEq, Inhabited
structure MOsmPerL_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MOsmPerL_R   where val : ℝ     deriving Inhabited

-- Osmolality: mOsm/kg
structure MOsmPerKg_F  where val : Float deriving Repr, BEq, Inhabited
structure MOsmPerKg_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MOsmPerKg_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Metabolic Rates
================================================================================================
-/
-- Metabolic rate: kcal/day or kJ/day
structure KcalPerDay_F where val : Float deriving Repr, BEq, Inhabited
structure KcalPerDay_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KcalPerDay_R where val : ℝ     deriving Inhabited

structure KJPerDay_F   where val : Float deriving Repr, BEq, Inhabited
structure KJPerDay_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KJPerDay_R   where val : ℝ     deriving Inhabited

-- Oxygen consumption: mL O₂/(min·kg)
structure VO2_F        where val : Float deriving Repr, BEq, Inhabited
structure VO2_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VO2_R        where val : ℝ     deriving Inhabited

-- ATP turnover rate: mol/(s·kg)
structure ATPTurnover_F where val : Float deriving Repr, BEq, Inhabited
structure ATPTurnover_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ATPTurnover_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Binding and Affinity
================================================================================================
-/
-- Dissociation constant: M (or nM, µM)
structure Kd_F         where val : Float deriving Repr, BEq, Inhabited
structure Kd_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kd_R         where val : ℝ     deriving Inhabited

-- Association constant: M⁻¹
structure Ka_F         where val : Float deriving Repr, BEq, Inhabited
structure Ka_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Ka_R         where val : ℝ     deriving Inhabited

-- IC50/EC50: concentration for 50% effect
structure IC50_F       where val : Float deriving Repr, BEq, Inhabited
structure IC50_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure IC50_R       where val : ℝ     deriving Inhabited

structure EC50_F       where val : Float deriving Repr, BEq, Inhabited
structure EC50_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EC50_R       where val : ℝ     deriving Inhabited

-- Hill coefficient (dimensionless)
structure HillCoeff_F  where val : Float deriving Repr, BEq, Inhabited
structure HillCoeff_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HillCoeff_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Error Propagation & Measurement Helpers
================================================================================================
-/
-- Parametric Uncertainty Tracking with biological context
structure BioMeasured (α : Type) where
  value : α
  uncertainty : α
  temperature : Option Celsius_F := none
  pH_condition : Option pH_F := none
  ionic_strength : Option Molar_F := none
  organism : Option String := none
  tissue : Option String := none
  source : Option String := none
  deriving Repr, BEq, Inhabited

-- Measurement with uncertainty for concentrations
structure MeasuredConcentration_F where
  value : Molar_F
  uncertainty : Molar_F
  method : Option String := none  -- "HPLC", "spectrophotometry", etc.
  source : Option String := none
  deriving Repr, BEq, Inhabited

structure MeasuredEnzymeActivity_F where
  value : SpecificActivity_F
  uncertainty : SpecificActivity_F
  temperature : Option Celsius_F := none
  pH : Option pH_F := none
  substrate : Option String := none
  deriving Repr, BEq, Inhabited

structure MeasuredBinding_F where
  kd : Kd_F
  kd_error : Kd_F
  method : Option String := none  -- "SPR", "ITC", "fluorescence"
  conditions : Option String := none
  deriving Repr, BEq, Inhabited

-- Error propagation for dilution
def dilutionWithError_F (initial : MeasuredConcentration_F)
    (dilutionFactor : Float) (dilutionError : Float) : MeasuredConcentration_F :=
  let finalConc := initial.value.val / dilutionFactor
  let relErrorConc := initial.uncertainty.val / initial.value.val
  let relErrorDilution := dilutionError / dilutionFactor
  let relError := Float.sqrt (relErrorConc^2 + relErrorDilution^2)
  { value := ⟨finalConc⟩
    uncertainty := ⟨finalConc * relError⟩
    method := some "Dilution"
    source := initial.source }

-- Error propagation for Michaelis-Menten
def michaelisMentenWithError_F (vmax : Vmax_F) (vmaxError : Vmax_F)
    (km : Km_F) (kmError : Km_F)
    (substrate : Molar_F) (substrateError : Molar_F) : BioMeasured Vmax_F :=
  let v := vmax.val * substrate.val / (km.val + substrate.val)
  -- Partial derivatives for error propagation
  let dvdVmax := substrate.val / (km.val + substrate.val)
  let dvdKm := -vmax.val * substrate.val / ((km.val + substrate.val)^2)
  let dvdS := vmax.val * km.val / ((km.val + substrate.val)^2)
  let errorV := Float.sqrt ((dvdVmax * vmaxError.val)^2 +
                           (dvdKm * kmError.val)^2 +
                           (dvdS * substrateError.val)^2)
  { value := ⟨v⟩
    uncertainty := ⟨errorV⟩
    source := some "Michaelis-Menten calculation" }

/--
================================================================================================
   Validation & Range Checking Helpers
================================================================================================
-/

-- pH validation
def isValidPH_F (p : pH_F) : Bool :=
  0.0 ≤ p.val && p.val ≤ 14.0

def isPhysiologicalPH_F (p : pH_F) : Bool :=
  7.35 ≤ p.val && p.val ≤ 7.45  -- Normal blood pH

-- Concentration validation
def isValidConcentration_F (c : Molar_F) : Bool :=
  c.val ≥ 0.0

def isValidConcentration_Q (c : Molar_Q) : Bool :=
  c.val ≥ 0

-- Cell density validation
def isRealisticCellDensity_F (d : CellsPerML_F) : Bool :=
  0.0 ≤ d.val && d.val ≤ 1e12  -- Upper limit for bacterial cultures

-- Heart rate validation
def isValidHeartRate_F (hr : BeatsPerMin_F) : Bool :=
  0.0 < hr.val && hr.val < 300.0

def isNormalRestingHR_F (hr : BeatsPerMin_F) : Bool :=
  60.0 ≤ hr.val && hr.val ≤ 100.0

-- Blood pressure validation
def isValidSystolic_F (bp : MmHg_F) : Bool :=
  50.0 ≤ bp.val && bp.val ≤ 250.0

def isNormalSystolic_F (bp : MmHg_F) : Bool :=
  90.0 ≤ bp.val && bp.val < 120.0

-- Oxygen saturation validation
def isValidSpO2_F (sat : SpO2_F) : Bool :=
  0.0 ≤ sat.val && sat.val ≤ 100.0

def isNormalSpO2_F (sat : SpO2_F) : Bool :=
  95.0 ≤ sat.val && sat.val ≤ 100.0

-- GFR validation
def isValidGFR_F (gfr : GFR_F) : Bool :=
  gfr.val ≥ 0.0

def isNormalGFR_F (gfr : GFR_F) : Bool :=
  90.0 ≤ gfr.val && gfr.val ≤ 120.0

-- Hill coefficient validation
def isValidHillCoeff_F (n : HillCoeff_F) : Bool :=
  n.val > 0.0  -- Must be positive

def isCooperative_F (n : HillCoeff_F) : Bool :=
  n.val > 1.0  -- Positive cooperativity

/--
================================================================================================
   Unit Conversions
================================================================================================
-/

-- Molar concentration conversions
def molarToMillimolar_F (m : Molar_F) : Millimolar_F :=
  ⟨m.val * 1000.0⟩

def millimolarToMicromolar_F (mm : Millimolar_F) : Micromolar_F :=
  ⟨mm.val * 1000.0⟩

def micromolarToNanomolar_F (um : Micromolar_F) : Nanomolar_F :=
  ⟨um.val * 1000.0⟩

def nanomolarToPicomolar_F (nm : Nanomolar_F) : Picomolar_F :=
  ⟨nm.val * 1000.0⟩

-- Mass concentration conversions
def mgPerDLToGPerL_F (mgdl : MgPerDL_F) : GPerL_F :=
  ⟨mgdl.val * 0.01⟩

def gPerDLToGPerL_F (gdl : GPerDL_F) : GPerL_F :=
  ⟨gdl.val * 10.0⟩

def mgPerLToPPM_F (mgl : MgPerL_F) : PPM_F :=
  ⟨mgl.val⟩  -- For aqueous solutions, mg/L ≈ ppm

def ugPerLToPPB_F (ugl : UgPerL_F) : PPB_F :=
  ⟨ugl.val⟩  -- For aqueous solutions, µg/L ≈ ppb

-- pH conversions
def pHToHConcentration_F (p : pH_F) : Molar_F :=
  ⟨10.0 ^ (-p.val)⟩

def hConcentrationToPH_F (h : Molar_F) : pH_F :=
  ⟨-Float.log h.val / ln10_F⟩

def pKaToPH_F (pka : pKa_F) (ratio : Float) : pH_F :=
  ⟨pka.val + Float.log ratio / ln10_F⟩  -- Henderson-Hasselbalch

-- Pressure conversions for medical use
def mmHgToPascal_F (mmhg : MmHg_F) : Pascal_F :=
  ⟨mmhg.val * 133.322⟩

def pascalToMmHg_F (pa : Pascal_F) : MmHg_F :=
  ⟨pa.val / 133.322⟩

-- Flow rate conversions
def mlPerMinToLPerMin_F (ml : MLPerMin_F) : LPerMin_F :=
  ⟨ml.val / 1000.0⟩

def lPerMinToMLPerMin_F (l : LPerMin_F) : MLPerMin_F :=
  ⟨l.val * 1000.0⟩

-- Energy conversions
def kcalToKJ_F (kcal : KcalPerDay_F) : KJPerDay_F :=
  ⟨kcal.val * 4.184⟩

def kjToKcal_F (kj : KJPerDay_F) : KcalPerDay_F :=
  ⟨kj.val / 4.184⟩

-- International units to katals
def iuToKatal_F (iu : IU_F) : Katal_F :=
  ⟨iu.val * 1.667e-8⟩  -- 1 IU = 1 µmol/min = 1.667×10⁻⁸ kat

/--
================================================================================================
   Common Biological Calculations
================================================================================================
-/

-- Calculate doubling time from growth rate
def doublingTimeFromGrowthRate_F (mu : GrowthRate_F) : DoublingTime_F :=
  ⟨Float.log 2.0 / mu.val⟩

-- Calculate growth rate from doubling time
def growthRateFromDoublingTime_F (td : DoublingTime_F) : GrowthRate_F :=
  ⟨Float.log 2.0 / td.val⟩

-- Michaelis-Menten velocity
def michaelisVelocity_F (vmax : Vmax_F) (s : Molar_F) (km : Km_F) : Vmax_F :=
  ⟨vmax.val * s.val / (km.val + s.val)⟩

-- Lineweaver-Burk transformation
def lineweaverBurk_F (v : Vmax_F) (s : Molar_F) : (Float × Float) :=
  (1.0 / s.val, 1.0 / v.val)

-- Hill equation for cooperative binding
def hillEquation_F (vmax : Vmax_F) (s : Molar_F)
    (k50 : EC50_F) (n : HillCoeff_F) : Vmax_F :=
  ⟨vmax.val * (s.val ^ n.val) / (k50.val ^ n.val + s.val ^ n.val)⟩

-- Catalytic efficiency
def catalyticEfficiency_F (kcat : Kcat_F) (km : Km_F) : CatalyticEfficiency_F :=
  ⟨kcat.val / km.val⟩

-- Henderson-Hasselbalch equation
def hendersonHasselbalch_F (pka : pKa_F) (acidConc : Molar_F)
    (baseConc : Molar_F) : pH_F :=
  ⟨pka.val + Float.log (baseConc.val / acidConc.val) / ln10_F⟩

-- Buffer capacity calculation
def bufferCapacity_F (totalConc : Molar_F) (pka : pKa_F) (ph : pH_F)
    : BufferCapacity_F :=
  let alpha := 10.0 ^ (ph.val - pka.val)
  let beta_val := ln10_F * totalConc.val * alpha / ((1.0 + alpha) ^ 2)
  ⟨beta_val⟩

-- Osmolarity calculation
def osmolarity_F (concentrations : Array Molar_F)
    (dissociationFactors : Array Float) : MOsmPerL_F :=
  let osmContributions := (concentrations.zip dissociationFactors).map fun (c, i) =>
    c.val * i * 1000.0  -- Convert to mOsm
  ⟨osmContributions.foldl (· + ·) 0.0⟩

-- eGFR calculation (MDRD formula simplified)
def eGFR_MDRD_F (creatinine : MgPerDL_F) (age : Float)
    (isFemale : Bool) (isBlack : Bool) : GFR_F :=
  let base := 175.0 * (creatinine.val ^ (-1.154)) * (age ^ (-0.203))
  let femaleAdj := if isFemale then 0.742 else 1.0
  let blackAdj := if isBlack then 1.212 else 1.0
  ⟨base * femaleAdj * blackAdj⟩

-- Body surface area (Dubois formula)
def bodySurfaceArea_F (weightKg : Float) (heightCm : Float) : Float :=
  0.007184 * (weightKg ^ 0.425) * (heightCm ^ 0.725)

-- Dose adjustment for BSA
def dosePerBSA_F (dose : MgPerKg_F) (weightKg : Float)
    (heightCm : Float) : Float :=
  let bsa := bodySurfaceArea_F weightKg heightCm
  dose.val * weightKg / bsa

-- Anion gap calculation
def anionGap_F (sodium : MEqPerL_F) (chloride : MEqPerL_F)
    (bicarbonate : MEqPerL_F) : MEqPerL_F :=
  ⟨sodium.val - (chloride.val + bicarbonate.val)⟩

-- Corrected calcium for albumin
def correctedCalcium_F (calcium : MgPerDL_F) (albumin : GPerDL_F) : MgPerDL_F :=
  ⟨calcium.val + 0.8 * (4.0 - albumin.val)⟩

-- Mean arterial pressure
def meanArterialPressure_F (systolic : MmHg_F) (diastolic : MmHg_F) : MmHg_F :=
  ⟨diastolic.val + (systolic.val - diastolic.val) / 3.0⟩

-- Cardiac index
def cardiacIndex_F (cardiacOutput : CardiacOutput_F) (bsa : Float) : Float :=
  cardiacOutput.val / bsa

-- Oxygen delivery
def oxygenDelivery_F (cardiacOutput : CardiacOutput_F) (hemoglobin : GPerDL_F)
    (spo2 : SpO2_F) : Float :=
  cardiacOutput.val * (hemoglobin.val * 1.34 * spo2.val / 100.0 + 0.003 * 100.0)

/--
================================================================================================
   Pharmacokinetics
================================================================================================
-/

-- Volume of distribution
structure Vd_F where val : Float deriving Repr, BEq, Inhabited  -- L/kg

-- Clearance
structure Clearance_F where val : Float deriving Repr, BEq, Inhabited  -- mL/min/kg

-- Half-life calculation
def halfLife_F (vd : Vd_F) (clearance : Clearance_F) : Float :=
  0.693 * vd.val * 1000.0 / clearance.val  -- Returns minutes

-- Loading dose calculation
def loadingDose_F (targetConc : MgPerL_F) (vd : Vd_F) (weightKg : Float) : Float :=
  targetConc.val * vd.val * weightKg

-- Maintenance dose calculation
def maintenanceDose_F (targetConc : MgPerL_F) (clearance : Clearance_F)
    (interval : Float) (weightKg : Float) : Float :=
  targetConc.val * clearance.val * interval * weightKg / 1000.0

/--
================================================================================================
   Statistical Helpers for Biological Data
================================================================================================
-/

-- IC50/EC50 fitting helper
structure DoseResponse_F where
  concentrations : Array Molar_F
  responses : Array Float  -- Normalized 0-100%
  deriving Repr, BEq, Inhabited

-- Simple IC50 estimation (would need proper curve fitting in practice)
def estimateIC50_F (data : DoseResponse_F) : Option IC50_F :=
  -- Find concentrations bracketing 50% response
  let pairs := data.concentrations.zip data.responses
  let below50 := pairs.filter (fun (_, r) => r < 50.0)
  let above50 := pairs.filter (fun (_, r) => r ≥ 50.0)
  match below50.back?, above50[0]?  with
  | some (c1, r1), some (c2, r2) =>
    -- Linear interpolation between bracketing points
    let fraction := (50.0 - r1) / (r2 - r1)
    let ic50 := c1.val + fraction * (c2.val - c1.val)
    some ⟨ic50⟩
  | _, _ => none

-- Z-factor for assay quality
def zFactor_F (positiveControl : Array Float) (negativeControl : Array Float) : Float :=
  let posMean := positiveControl.foldl (· + ·) 0.0 / positiveControl.size.toFloat
  let negMean := negativeControl.foldl (· + ·) 0.0 / negativeControl.size.toFloat
  let posSD := Float.sqrt (positiveControl.map (fun x => (x - posMean)^2) |>.foldl (· + ·) (0.0 / positiveControl.size.toFloat))
  let negSD := Float.sqrt (negativeControl.map (fun x => (x - negMean)^2) |>.foldl (· + ·) (0.0 / negativeControl.size.toFloat))
  1.0 - (3.0 * (posSD + negSD) / (posMean - negMean).abs)

end Units.Bio
