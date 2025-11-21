-- Radiation.lean -- Nuclear decay, dosimetry, cross sections, radiation protection
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import LogosLibrary.Units.Core

open Units.SI
/-
================================================================================
WAVE PHYSICS UNITS LIBRARY
================================================================================

This module provides type-safe units for radiation physics and chemistry acoustics.
Following the triple-type architecture for maximumflexibility without type conversion
friction.

## COVERAGE
- Radioactivity & decay - Becquerel, Curie, decay constants, half-lives, specific activity
- Absorbed dose - Gray, rad, and their subunits
- Equivalent dose - Sievert, rem, and their subunits
- Dose rates - Various time-based dose measurements
- Exposure - Legacy Roentgen units and SI equivalents
- Radiation weighting factors - w_R, w_T, Q, RBE
- Linear energy transfer & kerma - LET, kerma, CEMA
- Particle flux & fluence - Particle and energy flux/fluence measurements
- Cross sections - Barn and related units, macroscopic cross sections
- Attenuation & shielding - Linear/mass attenuation, HVL, TVL, buildup factors
- Neutron-specific - Lethargy, reactivity, dollars/cents, generation time
- Committed & collective doses - Person·Sv, intake coefficients

## USAGE PATTERNS
Float: Experimental measurements, sensor readings, numerical simulations,
iterative algorithms, display/visualization, real-time computation, engineering tolerances

ℚ: Exact stoichiometry, crystallographic ratios, unit cell parameters, Miller indices,
quantum number arithmetic, precise unit conversions, avoiding floating-point accumulation errors

ℝ: Theoretical proofs, continuous function analysis, calculus-based derivations,
mathematical physics formulations, thermodynamic limit calculations, formal verification of physical laws
-/
namespace Units.Radiation

/--
================================================================================================
   Radioactivity & Decay
================================================================================================
-/
structure Becquerel_F    where val : Float deriving Repr, BEq, Inhabited  -- Bq (s⁻¹)
structure Becquerel_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Becquerel_R    where val : ℝ     deriving Inhabited

structure Curie_F        where val : Float deriving Repr, BEq, Inhabited  -- Ci (3.7×10¹⁰ Bq)
structure Curie_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Curie_R        where val : ℝ     deriving Inhabited

structure Millicurie_F   where val : Float deriving Repr, BEq, Inhabited  -- mCi
structure Millicurie_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Millicurie_R   where val : ℝ     deriving Inhabited

structure Microcurie_F   where val : Float deriving Repr, BEq, Inhabited  -- μCi
structure Microcurie_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Microcurie_R   where val : ℝ     deriving Inhabited

structure DecayConstant_F where val : Float deriving Repr, BEq, Inhabited  -- s⁻¹
structure DecayConstant_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DecayConstant_R where val : ℝ     deriving Inhabited

structure HalfLife_F      where val : Float deriving Repr, BEq, Inhabited  -- seconds
structure HalfLife_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HalfLife_R      where val : ℝ     deriving Inhabited

structure HalfLifeYears_F where val : Float deriving Repr, BEq, Inhabited
structure HalfLifeYears_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HalfLifeYears_R where val : ℝ     deriving Inhabited

structure HalfLifeDays_F  where val : Float deriving Repr, BEq, Inhabited
structure HalfLifeDays_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HalfLifeDays_R  where val : ℝ     deriving Inhabited

structure MeanLifetime_F  where val : Float deriving Repr, BEq, Inhabited  -- τ = 1/λ
structure MeanLifetime_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MeanLifetime_R  where val : ℝ     deriving Inhabited

structure SpecificActivity_F where val : Float deriving Repr, BEq, Inhabited  -- Bq/kg
structure SpecificActivity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpecificActivity_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Absorbed Dose
================================================================================================
-/
structure Gray_F         where val : Float deriving Repr, BEq, Inhabited  -- Gy (J/kg)
structure Gray_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Gray_R         where val : ℝ     deriving Inhabited

structure Milligray_F    where val : Float deriving Repr, BEq, Inhabited  -- mGy
structure Milligray_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Milligray_R    where val : ℝ     deriving Inhabited

structure Microgray_F    where val : Float deriving Repr, BEq, Inhabited  -- μGy
structure Microgray_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Microgray_R    where val : ℝ     deriving Inhabited

structure Rad_F          where val : Float deriving Repr, BEq, Inhabited  -- rad (0.01 Gy)
structure Rad_Q          where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Rad_R          where val : ℝ     deriving Inhabited

structure Millirad_F     where val : Float deriving Repr, BEq, Inhabited  -- mrad
structure Millirad_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Millirad_R     where val : ℝ     deriving Inhabited

/--
================================================================================================
   Equivalent Dose
================================================================================================
-/
structure Sievert_F      where val : Float deriving Repr, BEq, Inhabited  -- Sv
structure Sievert_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Sievert_R      where val : ℝ     deriving Inhabited

structure Millisievert_F where val : Float deriving Repr, BEq, Inhabited  -- mSv
structure Millisievert_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Millisievert_R where val : ℝ     deriving Inhabited

structure Microsievert_F where val : Float deriving Repr, BEq, Inhabited  -- μSv
structure Microsievert_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Microsievert_R where val : ℝ     deriving Inhabited

structure Rem_F          where val : Float deriving Repr, BEq, Inhabited  -- rem (0.01 Sv)
structure Rem_Q          where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Rem_R          where val : ℝ     deriving Inhabited

structure Millirem_F     where val : Float deriving Repr, BEq, Inhabited  -- mrem
structure Millirem_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Millirem_R     where val : ℝ     deriving Inhabited

/--
================================================================================================
   Dose Rates
================================================================================================
-/
structure GrayPerHour_F      where val : Float deriving Repr, BEq, Inhabited  -- Gy/h
structure GrayPerHour_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GrayPerHour_R      where val : ℝ     deriving Inhabited

structure MilligrayPerHour_F where val : Float deriving Repr, BEq, Inhabited  -- mGy/h
structure MilligrayPerHour_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilligrayPerHour_R where val : ℝ     deriving Inhabited

structure SievertPerYear_F   where val : Float deriving Repr, BEq, Inhabited  -- Sv/y
structure SievertPerYear_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SievertPerYear_R   where val : ℝ     deriving Inhabited

structure MicrosievertPerHour_F where val : Float deriving Repr, BEq, Inhabited  -- μSv/h
structure MicrosievertPerHour_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MicrosievertPerHour_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Exposure (Legacy Units)
================================================================================================
-/
structure Roentgen_F     where val : Float deriving Repr, BEq, Inhabited  -- R (C/kg in air)
structure Roentgen_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Roentgen_R     where val : ℝ     deriving Inhabited

structure Milliroentgen_F where val : Float deriving Repr, BEq, Inhabited  -- mR
structure Milliroentgen_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Milliroentgen_R where val : ℝ     deriving Inhabited

structure CoulombPerKg_F  where val : Float deriving Repr, BEq, Inhabited  -- C/kg (SI exposure)
structure CoulombPerKg_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CoulombPerKg_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Radiation Weighting Factors
================================================================================================
-/
structure RadiationWeightingFactor_F where val : Float deriving Repr, BEq, Inhabited  -- w_R
structure RadiationWeightingFactor_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RadiationWeightingFactor_R where val : ℝ     deriving Inhabited

structure TissueWeightingFactor_F    where val : Float deriving Repr, BEq, Inhabited  -- w_T
structure TissueWeightingFactor_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TissueWeightingFactor_R    where val : ℝ     deriving Inhabited

structure QualityFactor_F            where val : Float deriving Repr, BEq, Inhabited  -- Q
structure QualityFactor_Q            where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure QualityFactor_R            where val : ℝ     deriving Inhabited

structure RelativeBiologicalEffect_F where val : Float deriving Repr, BEq, Inhabited  -- RBE
structure RelativeBiologicalEffect_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RelativeBiologicalEffect_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Linear Energy Transfer & Kerma
================================================================================================
-/
structure LET_F          where val : Float deriving Repr, BEq, Inhabited  -- keV/μm
structure LET_Q          where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LET_R          where val : ℝ     deriving Inhabited

structure Kerma_F        where val : Float deriving Repr, BEq, Inhabited  -- Gy
structure Kerma_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kerma_R        where val : ℝ     deriving Inhabited

structure KermaRate_F    where val : Float deriving Repr, BEq, Inhabited  -- Gy/s
structure KermaRate_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KermaRate_R    where val : ℝ     deriving Inhabited

structure CEMA_F         where val : Float deriving Repr, BEq, Inhabited  -- Converted energy per mass
structure CEMA_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CEMA_R         where val : ℝ     deriving Inhabited

/--
================================================================================================
   Particle Flux & Fluence
================================================================================================
-/
structure ParticleFlux_F     where val : Float deriving Repr, BEq, Inhabited  -- particles/cm²/s
structure ParticleFlux_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ParticleFlux_R     where val : ℝ     deriving Inhabited

structure ParticleFluence_F  where val : Float deriving Repr, BEq, Inhabited  -- particles/cm²
structure ParticleFluence_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ParticleFluence_R  where val : ℝ     deriving Inhabited

structure EnergyFlux_F       where val : Float deriving Repr, BEq, Inhabited  -- MeV/cm²/s
structure EnergyFlux_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EnergyFlux_R       where val : ℝ     deriving Inhabited

structure EnergyFluence_F    where val : Float deriving Repr, BEq, Inhabited  -- MeV/cm²
structure EnergyFluence_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EnergyFluence_R    where val : ℝ     deriving Inhabited

structure NeutronFlux_F      where val : Float deriving Repr, BEq, Inhabited  -- n/cm²/s
structure NeutronFlux_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NeutronFlux_R      where val : ℝ     deriving Inhabited

/--
================================================================================================
   Cross Sections
================================================================================================
-/
structure Barn_F         where val : Float deriving Repr, BEq, Inhabited  -- b (10⁻²⁸ m²)
structure Barn_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Barn_R         where val : ℝ     deriving Inhabited

structure Millibarn_F    where val : Float deriving Repr, BEq, Inhabited  -- mb
structure Millibarn_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Millibarn_R    where val : ℝ     deriving Inhabited

structure Microbarn_F    where val : Float deriving Repr, BEq, Inhabited  -- μb
structure Microbarn_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Microbarn_R    where val : ℝ     deriving Inhabited

structure Kilobarn_F     where val : Float deriving Repr, BEq, Inhabited  -- kb
structure Kilobarn_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kilobarn_R     where val : ℝ     deriving Inhabited

structure MacroscopicCrossSection_F where val : Float deriving Repr, BEq, Inhabited  -- cm⁻¹
structure MacroscopicCrossSection_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MacroscopicCrossSection_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Attenuation & Shielding
================================================================================================
-/
structure LinearAttenuation_F   where val : Float deriving Repr, BEq, Inhabited  -- cm⁻¹
structure LinearAttenuation_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LinearAttenuation_R   where val : ℝ     deriving Inhabited

structure MassAttenuation_F     where val : Float deriving Repr, BEq, Inhabited  -- cm²/g
structure MassAttenuation_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MassAttenuation_R     where val : ℝ     deriving Inhabited

structure HalfValueLayer_F      where val : Float deriving Repr, BEq, Inhabited  -- cm or mm
structure HalfValueLayer_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HalfValueLayer_R      where val : ℝ     deriving Inhabited

structure TenthValueLayer_F     where val : Float deriving Repr, BEq, Inhabited  -- cm or mm
structure TenthValueLayer_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TenthValueLayer_R     where val : ℝ     deriving Inhabited

structure MeanFreePath_F        where val : Float deriving Repr, BEq, Inhabited  -- cm
structure MeanFreePath_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MeanFreePath_R        where val : ℝ     deriving Inhabited

structure BuildupFactor_F       where val : Float deriving Repr, BEq, Inhabited  -- dimensionless
structure BuildupFactor_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BuildupFactor_R       where val : ℝ     deriving Inhabited

/--
================================================================================================
   Neutron-Specific Quantities
================================================================================================
-/
structure Lethargy_F            where val : Float deriving Repr, BEq, Inhabited  -- ln(E₀/E)
structure Lethargy_Q            where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Lethargy_R            where val : ℝ     deriving Inhabited

structure Reactivity_F          where val : Float deriving Repr, BEq, Inhabited  -- ρ (dimensionless)
structure Reactivity_Q          where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Reactivity_R          where val : ℝ     deriving Inhabited

structure Dollar_F              where val : Float deriving Repr, BEq, Inhabited  -- $ (reactivity unit)
structure Dollar_Q              where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Dollar_R              where val : ℝ     deriving Inhabited

structure Cent_F                where val : Float deriving Repr, BEq, Inhabited  -- ¢ (0.01$)
structure Cent_Q                where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Cent_R                where val : ℝ     deriving Inhabited

structure NeutronGenerationTime_F where val : Float deriving Repr, BEq, Inhabited  -- seconds
structure NeutronGenerationTime_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NeutronGenerationTime_R where val : ℝ     deriving Inhabited

structure DelayedNeutronFraction_F where val : Float deriving Repr, BEq, Inhabited  -- β
structure DelayedNeutronFraction_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DelayedNeutronFraction_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Committed & Collective Doses
================================================================================================
-/
structure CommittedDose_F       where val : Float deriving Repr, BEq, Inhabited  -- Sv
structure CommittedDose_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CommittedDose_R       where val : ℝ     deriving Inhabited

structure CollectiveDose_F      where val : Float deriving Repr, BEq, Inhabited  -- person·Sv
structure CollectiveDose_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CollectiveDose_R      where val : ℝ     deriving Inhabited

structure IntakeCoefficient_F   where val : Float deriving Repr, BEq, Inhabited  -- Sv/Bq
structure IntakeCoefficient_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure IntakeCoefficient_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Measurement Uncertainty for Common Radiation Quantities
================================================================================================
-/
structure ActivityWithError_F where
  value : Becquerel_F
  uncertainty : Becquerel_F
  deriving Repr, BEq, Inhabited

structure DoseWithError_F where
  value : Gray_F
  uncertainty : Gray_F
  deriving Repr, BEq, Inhabited

structure EquivalentDoseWithError_F where
  value : Sievert_F
  uncertainty : Sievert_F
  deriving Repr, BEq, Inhabited

structure CrossSectionWithError_F where
  value : Barn_F
  uncertainty : Barn_F
  deriving Repr, BEq, Inhabited

/--
================================================================================================
   Helper Functions
================================================================================================
-/

-- Constructor for positive activity
def mkActivity_F (v : Float) : Option Becquerel_F :=
  if 0.0 < v then some ⟨v⟩ else none

def mkActivity_Q (v : ℚ) : Option Becquerel_Q :=
  if 0.0 < v then some ⟨v⟩ else none

noncomputable def mkActivity_R (v : ℝ) : Option Becquerel_R :=
  if 0.0 < v then some ⟨v⟩ else none

-- Constructor for positive half-life
def mkHalfLife_F (v : Float) : Option HalfLife_F :=
  if 0.0 < v then some ⟨v⟩ else none

def mkHalfLife_Q (v : ℚ) : Option HalfLife_Q :=
  if 0.0 < v then some ⟨v⟩ else none

noncomputable def mkHalfLife_R (v : ℝ) : Option HalfLife_R :=
  if 0.0 < v then some ⟨v⟩ else none

-- Constructor for weighting factors (0-1)
def mkWeightingFactor_F (v : Float) : Option TissueWeightingFactor_F :=
  if 0.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

def mkWeightingFactor_Q (v : ℚ) : Option TissueWeightingFactor_Q :=
  if 0.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

noncomputable def mkWeightingFactor_R (v : ℝ) : Option TissueWeightingFactor_R :=
  if 0.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

-- Constructor for buildup factor (≥1)
def mkBuildupFactor_F (v : Float) : Option BuildupFactor_F :=
  if 1.0 ≤ v then some ⟨v⟩ else none

def mkBuildupFactor_Q (v : ℚ) : Option BuildupFactor_Q :=
  if 1.0 ≤ v then some ⟨v⟩ else none

noncomputable def mkBuildupFactor_R (v : ℝ) : Option BuildupFactor_R :=
  if 1.0 ≤ v then some ⟨v⟩ else none

end Units.Radiation
