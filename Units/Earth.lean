-- Earth.lean        -- Geophysics, atmospheric science, oceanography, earth systems
import LogosLibrary.Units.Core
import LogosLibrary.Units.Mechanics
import LogosLibrary.Units.Fluids
import LogosLibrary.Units.Chemistry
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

namespace Units.Earth

open SI Mechanics Chemistry Fluids

/-
================================================================================
EARTH SCIENCES UNITS LIBRARY
================================================================================

This module provides type-safe units for geophysics, atmospheric science,
oceanography, hydrology, seismology, and earth system science.
Following the triple-type architecture for maximum flexibility without type
conversion friction.

## COVERAGE
- Seismology (magnitude scales, seismic moment, wave velocities)
- Gravity and geodesy (gravity anomalies, geoid height, isostasy)
- Geomagnetism (field strength, declination, inclination, paleomagnetic)
- Atmospheric science (geopotential height, mixing ratios, optical depth)
- Oceanography (salinity, ocean heat content, sea level, tides)
- Hydrology (discharge, infiltration, hydraulic head, groundwater)
- Geology (porosity, permeability, stress/strain, heat flow)
- Climate (radiative forcing, climate sensitivity, carbon flux)
- Geodesy (coordinates, datum transformations, map projections)
- Glaciology (ice thickness, accumulation rates, ice velocity)
- Volcanology (VEI, eruption rate, tephra volume)

## USAGE PATTERNS
Float: Field measurements, GPS data, seismometer readings, weather stations,
ocean buoys, satellite observations, borehole logging, climate models,
real-time monitoring, hazard assessment

ℚ: Map scale ratios, coordinate transformations, grid references,
isotope ratios, mixing ratios, mineral proportions, stratigraphic ratios

ℝ: Geophysical inversions, potential field theory, wave propagation,
mantle convection models, climate sensitivity analysis, isostatic adjustment,
theoretical seismology, geodetic datum definitions
-/

set_option autoImplicit false
set_option linter.unusedVariables false

/--
================================================================================================
   Mathematical and Physical Constants for Earth Sciences
================================================================================================
-/
def pi_F : Float := 3.14159265358979323846
def g_standard_F : Float := 9.80665  -- Standard gravity (m/s²)
def g_equator_F : Float := 9.78033  -- Gravity at equator (m/s²)
def g_pole_F : Float := 9.83219  -- Gravity at poles (m/s²)
def R_earth_F : Float := 6371000.0  -- Mean Earth radius (m)
def R_equator_F : Float := 6378137.0  -- Equatorial radius (m)
def R_polar_F : Float := 6356752.314245  -- Polar radius (m)
def omega_earth_F : Float := 7.292115e-5  -- Earth rotation rate (rad/s)
def GM_earth_F : Float := 3.986004418e14  -- Geocentric gravitational constant (m³/s²)
def stefan_boltzmann_F : Float := 5.670374419e-8  -- Stefan-Boltzmann constant (W/(m²·K⁴))
def solar_constant_F : Float := 1361.0  -- Solar irradiance at 1 AU (W/m²)

/--
================================================================================================
   Seismology
================================================================================================
-/
-- Magnitude scales (dimensionless but different contexts)
structure RichterMagnitude_F where val : Float deriving Repr, BEq, Inhabited
structure RichterMagnitude_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RichterMagnitude_R where val : ℝ     deriving Inhabited

structure MomentMagnitude_F where val : Float deriving Repr, BEq, Inhabited
structure MomentMagnitude_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MomentMagnitude_R where val : ℝ     deriving Inhabited

structure BodyWaveMagnitude_F where val : Float deriving Repr, BEq, Inhabited
structure BodyWaveMagnitude_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BodyWaveMagnitude_R where val : ℝ     deriving Inhabited

structure SurfaceWaveMagnitude_F where val : Float deriving Repr, BEq, Inhabited
structure SurfaceWaveMagnitude_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SurfaceWaveMagnitude_R where val : ℝ     deriving Inhabited

-- Seismic moment: N·m
structure SeismicMoment_F where val : Float deriving Repr, BEq, Inhabited
structure SeismicMoment_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SeismicMoment_R where val : ℝ     deriving Inhabited

-- Seismic wave velocities (using Velocity_F from Core.SI)
structure PWaveVelocity_F where val : Float deriving Repr, BEq, Inhabited
structure SWaveVelocity_F where val : Float deriving Repr, BEq, Inhabited

-- Ground acceleration: m/s² or g
structure PGA_F        where val : Float deriving Repr, BEq, Inhabited  -- Peak ground acceleration
structure PGA_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PGA_R        where val : ℝ     deriving Inhabited

-- Ground velocity: m/s
structure PGV_F        where val : Float deriving Repr, BEq, Inhabited  -- Peak ground velocity
structure PGV_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PGV_R        where val : ℝ     deriving Inhabited

-- Ground displacement: m
structure PGD_F        where val : Float deriving Repr, BEq, Inhabited  -- Peak ground displacement
structure PGD_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PGD_R        where val : ℝ     deriving Inhabited

-- Seismic intensity (Modified Mercalli, JMA, etc.) - ordinal scale
structure SeismicIntensity_F where val : Float deriving Repr, BEq, Inhabited
structure SeismicIntensity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SeismicIntensity_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Gravity and Geodesy
================================================================================================
-/
-- Gravity anomaly: mGal (1 mGal = 10⁻⁵ m/s²)
structure MilliGal_F   where val : Float deriving Repr, BEq, Inhabited
structure MilliGal_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilliGal_R   where val : ℝ     deriving Inhabited

structure MicroGal_F   where val : Float deriving Repr, BEq, Inhabited
structure MicroGal_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MicroGal_R   where val : ℝ     deriving Inhabited

-- Geoid height: m
structure GeoidHeight_F where val : Float deriving Repr, BEq, Inhabited
structure GeoidHeight_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GeoidHeight_R where val : ℝ     deriving Inhabited

-- Gravity gradient: Eötvös (1 E = 10⁻⁹ s⁻²)
structure Eotvos_F     where val : Float deriving Repr, BEq, Inhabited
structure Eotvos_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Eotvos_R     where val : ℝ     deriving Inhabited

-- Isostatic adjustment rate: mm/yr
structure UpliftRate_F where val : Float deriving Repr, BEq, Inhabited
structure UpliftRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure UpliftRate_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Geomagnetism
================================================================================================
-/
-- Magnetic field strength: nT (nanotesla)
structure NanoTesla_F  where val : Float deriving Repr, BEq, Inhabited
structure NanoTesla_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NanoTesla_R  where val : ℝ     deriving Inhabited

-- Magnetic declination: degrees
structure Declination_F where val : Float deriving Repr, BEq, Inhabited
structure Declination_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Declination_R where val : ℝ     deriving Inhabited

-- Magnetic inclination: degrees
structure Inclination_F where val : Float deriving Repr, BEq, Inhabited
structure Inclination_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Inclination_R where val : ℝ     deriving Inhabited

-- Paleomagnetic intensity: μT
structure PaleoIntensity_F where val : Float deriving Repr, BEq, Inhabited
structure PaleoIntensity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PaleoIntensity_R where val : ℝ     deriving Inhabited

-- Magnetic susceptibility: dimensionless (SI) or emu/cm³ (CGS)
structure MagSusceptibility_SI_F where val : Float deriving Repr, BEq, Inhabited
structure MagSusceptibility_SI_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MagSusceptibility_SI_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Atmospheric Science
================================================================================================
-/
-- Geopotential height: m
structure GeopotentialHeight_F where val : Float deriving Repr, BEq, Inhabited
structure GeopotentialHeight_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GeopotentialHeight_R where val : ℝ     deriving Inhabited

-- Pressure levels: hPa (hectopascal)
structure HectoPascal_F where val : Float deriving Repr, BEq, Inhabited
structure HectoPascal_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HectoPascal_R where val : ℝ     deriving Inhabited

-- Mixing ratio: g/kg
structure MixingRatio_F where val : Float deriving Repr, BEq, Inhabited
structure MixingRatio_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MixingRatio_R where val : ℝ     deriving Inhabited

-- Specific humidity: kg/kg (dimensionless)
structure SpecificHumidity_F where val : Float deriving Repr, BEq, Inhabited
structure SpecificHumidity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpecificHumidity_R where val : ℝ     deriving Inhabited

-- Relative humidity: % (0-100)
structure RelativeHumidity_F where val : Float deriving Repr, BEq, Inhabited
structure RelativeHumidity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RelativeHumidity_R where val : ℝ     deriving Inhabited

-- Precipitable water: mm or kg/m²
structure PrecipitableWater_F where val : Float deriving Repr, BEq, Inhabited
structure PrecipitableWater_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PrecipitableWater_R where val : ℝ     deriving Inhabited

-- Precipitation rate: mm/hr
structure PrecipRate_F where val : Float deriving Repr, BEq, Inhabited
structure PrecipRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PrecipRate_R where val : ℝ     deriving Inhabited

-- Wind speed: m/s, km/h, knots
structure Knots_F      where val : Float deriving Repr, BEq, Inhabited
structure Knots_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Knots_R      where val : ℝ     deriving Inhabited

-- Atmospheric optical depth: dimensionless
structure OpticalDepth_F where val : Float deriving Repr, BEq, Inhabited
structure OpticalDepth_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure OpticalDepth_R where val : ℝ     deriving Inhabited

-- Aerosol optical depth: dimensionless
structure AOD_F        where val : Float deriving Repr, BEq, Inhabited
structure AOD_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AOD_R        where val : ℝ     deriving Inhabited

-- Ozone column: Dobson units (DU)
structure DobsonUnit_F where val : Float deriving Repr, BEq, Inhabited
structure DobsonUnit_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DobsonUnit_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Oceanography
================================================================================================
-/
-- Salinity: PSU (Practical Salinity Units) or g/kg
structure PSU_F        where val : Float deriving Repr, BEq, Inhabited
structure PSU_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PSU_R        where val : ℝ     deriving Inhabited

-- Ocean heat content: J/m²
structure OceanHeatContent_F where val : Float deriving Repr, BEq, Inhabited
structure OceanHeatContent_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure OceanHeatContent_R where val : ℝ     deriving Inhabited

-- Sea level: mm
structure SeaLevel_F   where val : Float deriving Repr, BEq, Inhabited
structure SeaLevel_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SeaLevel_R   where val : ℝ     deriving Inhabited

-- Sea level rise rate: mm/yr
structure SeaLevelRate_F where val : Float deriving Repr, BEq, Inhabited
structure SeaLevelRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SeaLevelRate_R where val : ℝ     deriving Inhabited

-- Ocean current velocity: cm/s
structure CurrentVelocity_F where val : Float deriving Repr, BEq, Inhabited
structure CurrentVelocity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CurrentVelocity_R where val : ℝ     deriving Inhabited

-- Tidal amplitude: m
structure TidalAmplitude_F where val : Float deriving Repr, BEq, Inhabited
structure TidalAmplitude_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TidalAmplitude_R where val : ℝ     deriving Inhabited

-- Wave height: m
structure WaveHeight_F where val : Float deriving Repr, BEq, Inhabited
structure WaveHeight_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WaveHeight_R where val : ℝ     deriving Inhabited

-- Wave period: s
structure WavePeriod_F where val : Float deriving Repr, BEq, Inhabited
structure WavePeriod_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WavePeriod_R where val : ℝ     deriving Inhabited

-- Mixed layer depth: m
structure MixedLayerDepth_F where val : Float deriving Repr, BEq, Inhabited
structure MixedLayerDepth_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MixedLayerDepth_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Hydrology
================================================================================================
-/
-- Discharge: m³/s
structure Discharge_F  where val : Float deriving Repr, BEq, Inhabited
structure Discharge_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Discharge_R  where val : ℝ     deriving Inhabited

-- Specific discharge: m/s
structure SpecificDischarge_F where val : Float deriving Repr, BEq, Inhabited
structure SpecificDischarge_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpecificDischarge_R where val : ℝ     deriving Inhabited

-- Infiltration rate: mm/hr
structure InfiltrationRate_F where val : Float deriving Repr, BEq, Inhabited
structure InfiltrationRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure InfiltrationRate_R where val : ℝ     deriving Inhabited

-- Evapotranspiration: mm/day
structure Evapotranspiration_F where val : Float deriving Repr, BEq, Inhabited
structure Evapotranspiration_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Evapotranspiration_R where val : ℝ     deriving Inhabited

-- Soil moisture: % or m³/m³
structure SoilMoisture_F where val : Float deriving Repr, BEq, Inhabited
structure SoilMoisture_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SoilMoisture_R where val : ℝ     deriving Inhabited

-- Water table depth: m
structure WaterTableDepth_F where val : Float deriving Repr, BEq, Inhabited
structure WaterTableDepth_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WaterTableDepth_R where val : ℝ     deriving Inhabited

-- Aquifer storage coefficient: dimensionless
structure Storativity_F where val : Float deriving Repr, BEq, Inhabited
structure Storativity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Storativity_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Geology and Rock Properties
================================================================================================
-/
-- Porosity: dimensionless (0-1)
structure Porosity_F   where val : Float deriving Repr, BEq, Inhabited
structure Porosity_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Porosity_R   where val : ℝ     deriving Inhabited

-- Rock density: g/cm³ (using GPerCm3_F from Core.SI)

-- Heat flow: mW/m²
structure HeatFlow_F   where val : Float deriving Repr, BEq, Inhabited
structure HeatFlow_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HeatFlow_R   where val : ℝ     deriving Inhabited

-- Thermal gradient: °C/km or K/km
structure ThermalGradient_F where val : Float deriving Repr, BEq, Inhabited
structure ThermalGradient_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ThermalGradient_R where val : ℝ     deriving Inhabited

-- Strain rate: s⁻¹
structure StrainRate_Geo_F where val : Float deriving Repr, BEq, Inhabited
structure StrainRate_Geo_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure StrainRate_Geo_R where val : ℝ     deriving Inhabited

-- Slip rate: mm/yr
structure SlipRate_F   where val : Float deriving Repr, BEq, Inhabited
structure SlipRate_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SlipRate_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Climate Science
================================================================================================
-/
-- Radiative forcing: W/m²
structure RadiativeForcing_F where val : Float deriving Repr, BEq, Inhabited
structure RadiativeForcing_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RadiativeForcing_R where val : ℝ     deriving Inhabited

-- Climate sensitivity: K/(W/m²) or °C per CO₂ doubling
structure ClimateSensitivity_F where val : Float deriving Repr, BEq, Inhabited
structure ClimateSensitivity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ClimateSensitivity_R where val : ℝ     deriving Inhabited

-- Carbon flux: GtC/yr (gigatonnes carbon per year)
structure CarbonFlux_F where val : Float deriving Repr, BEq, Inhabited
structure CarbonFlux_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CarbonFlux_R where val : ℝ     deriving Inhabited

-- CO₂ concentration: ppm (parts per million)
structure CO2_ppm_F    where val : Float deriving Repr, BEq, Inhabited
structure CO2_ppm_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CO2_ppm_R    where val : ℝ     deriving Inhabited

-- Greenhouse gas forcing: W/m²
structure GHGForcing_F where val : Float deriving Repr, BEq, Inhabited
structure GHGForcing_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GHGForcing_R where val : ℝ     deriving Inhabited

-- Albedo: dimensionless (0-1)
structure Albedo_F     where val : Float deriving Repr, BEq, Inhabited
structure Albedo_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Albedo_R     where val : ℝ     deriving Inhabited

/--
================================================================================================
   Geodesy and Coordinates
================================================================================================
-/
-- Latitude/Longitude: degrees
structure Latitude_F   where val : Float deriving Repr, BEq, Inhabited
structure Latitude_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Latitude_R   where val : ℝ     deriving Inhabited

structure Longitude_F  where val : Float deriving Repr, BEq, Inhabited
structure Longitude_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Longitude_R  where val : ℝ     deriving Inhabited

-- Elevation: m above sea level
structure Elevation_F  where val : Float deriving Repr, BEq, Inhabited
structure Elevation_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Elevation_R  where val : ℝ     deriving Inhabited

-- Map scale: dimensionless ratio
structure MapScale_F   where val : Float deriving Repr, BEq, Inhabited
structure MapScale_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MapScale_R   where val : ℝ     deriving Inhabited

-- Convergence angle: degrees
structure Convergence_F where val : Float deriving Repr, BEq, Inhabited
structure Convergence_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Convergence_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Glaciology
================================================================================================
-/
-- Ice thickness: m
structure IceThickness_F where val : Float deriving Repr, BEq, Inhabited
structure IceThickness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure IceThickness_R where val : ℝ     deriving Inhabited

-- Ice velocity: m/yr
structure IceVelocity_F where val : Float deriving Repr, BEq, Inhabited
structure IceVelocity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure IceVelocity_R where val : ℝ     deriving Inhabited

-- Accumulation rate: m/yr (water equivalent)
structure AccumulationRate_F where val : Float deriving Repr, BEq, Inhabited
structure AccumulationRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AccumulationRate_R where val : ℝ     deriving Inhabited

-- Mass balance: kg/(m²·yr)
structure MassBalance_F where val : Float deriving Repr, BEq, Inhabited
structure MassBalance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MassBalance_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Volcanology
================================================================================================
-/
-- Volcanic Explosivity Index: dimensionless (0-8)
structure VEI_F        where val : Float deriving Repr, BEq, Inhabited
structure VEI_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VEI_R        where val : ℝ     deriving Inhabited

-- Eruption rate: m³/s
structure EruptionRate_F where val : Float deriving Repr, BEq, Inhabited
structure EruptionRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EruptionRate_R where val : ℝ     deriving Inhabited

-- Tephra volume: km³
structure TephraVolume_F where val : Float deriving Repr, BEq, Inhabited
structure TephraVolume_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TephraVolume_R where val : ℝ     deriving Inhabited

-- Lava flow rate: m³/s
structure LavaFlowRate_F where val : Float deriving Repr, BEq, Inhabited
structure LavaFlowRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LavaFlowRate_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Error Propagation & Measurement Helpers
================================================================================================
-/
-- Parametric Uncertainty Tracking with earth science context
structure EarthMeasured (α : Type) where
  value : α
  uncertainty : α
  location : Option (Latitude_F × Longitude_F × Elevation_F) := none
  depth : Option Meter_F := none
  time : Option String := none  -- ISO timestamp
  instrument : Option String := none
  source : Option String := none
  deriving Repr, BEq, Inhabited

-- Seismic measurement with uncertainty
structure MeasuredSeismicEvent_F where
  magnitude : MomentMagnitude_F
  mag_uncertainty : MomentMagnitude_F
  depth : Meter_F
  depth_uncertainty : Meter_F
  location : (Latitude_F × Longitude_F)
  location_uncertainty : Meter_F  -- Epicenter uncertainty radius
  origin_time : String
  deriving Repr, BEq, Inhabited

-- Climate measurement with uncertainty
structure MeasuredClimateData_F where
  temperature : Celsius_F
  temp_uncertainty : Celsius_F
  station_id : Option String := none
  elevation : Option Elevation_F := none
  method : Option String := none  -- "satellite", "radiosonde", "surface"
  deriving Repr, BEq, Inhabited

-- Error propagation for moment magnitude
def momentMagnitudeWithError_F (M0 : EarthMeasured SeismicMoment_F)
    : EarthMeasured MomentMagnitude_F :=
  let Mw := (2.0/3.0) * (Float.log M0.value.val / Float.log 10.0 - 9.1)
  -- Error prop: δMw = (2/3) * δM0/(M0 * ln(10))
  let Mw_error := (2.0/3.0) * M0.uncertainty.val / (M0.value.val * Float.log 10.0)
  { value := ⟨Mw⟩
    uncertainty := ⟨Mw_error.abs⟩
    source := some "Mw = (2/3)(log M0 - 9.1)" }

-- Error propagation for gravity anomaly
def gravityAnomalyWithError_F (g_obs : EarthMeasured Acceleration_F)
    (g_theoretical : Acceleration_F) : EarthMeasured MilliGal_F :=
  let anomaly := (g_obs.value.val - g_theoretical.val) * 100000.0  -- Convert to mGal
  let anomaly_error := g_obs.uncertainty.val * 100000.0
  { value := ⟨anomaly⟩
    uncertainty := ⟨anomaly_error⟩
    source := some "Gravity anomaly calculation" }

/--
================================================================================================
   Validation & Range Checking Helpers
================================================================================================
-/

-- Magnitude validation
def isValidMagnitude_F (M : MomentMagnitude_F) : Bool :=
  -2.0 ≤ M.val && M.val ≤ 10.0

def isMajorEarthquake_F (M : MomentMagnitude_F) : Bool :=
  M.val ≥ 7.0

def isGreatEarthquake_F (M : MomentMagnitude_F) : Bool :=
  M.val ≥ 8.0

-- Latitude/Longitude validation
def isValidLatitude_F (lat : Latitude_F) : Bool :=
  -90.0 ≤ lat.val && lat.val ≤ 90.0

def isValidLongitude_F (lon : Longitude_F) : Bool :=
  -180.0 ≤ lon.val && lon.val ≤ 180.0

-- Salinity validation
def isValidSalinity_F (S : PSU_F) : Bool :=
  0.0 ≤ S.val && S.val ≤ 50.0

def isOceanicSalinity_F (S : PSU_F) : Bool :=
  30.0 ≤ S.val && S.val ≤ 40.0

-- Humidity validation
def isValidRelativeHumidity_F (RH : RelativeHumidity_F) : Bool :=
  0.0 ≤ RH.val && RH.val ≤ 100.0

-- Porosity validation
def isValidPorosity_F (phi : Porosity_F) : Bool :=
  0.0 ≤ phi.val && phi.val ≤ 1.0

-- Albedo validation
def isValidAlbedo_F (a : Albedo_F) : Bool :=
  0.0 ≤ a.val && a.val ≤ 1.0

-- VEI validation
def isValidVEI_F (vei : VEI_F) : Bool :=
  0.0 ≤ vei.val && vei.val ≤ 8.0

def isSupervolcanicEruption_F (vei : VEI_F) : Bool :=
  vei.val ≥ 8.0

-- Climate sensitivity validation
def isRealisticClimateSensitivity_F (cs : ClimateSensitivity_F) : Bool :=
  1.5 ≤ cs.val && cs.val ≤ 4.5  -- IPCC likely range

/--
================================================================================================
   Unit Conversions
================================================================================================
-/

-- Seismic conversions
def momentFromMagnitude_F (Mw : MomentMagnitude_F) : SeismicMoment_F :=
  ⟨10.0 ^ (1.5 * Mw.val + 9.1)⟩

def magnitudeFromMoment_F (M0 : SeismicMoment_F) : MomentMagnitude_F :=
  ⟨(2.0/3.0) * (Float.log M0.val / Float.log 10.0 - 9.1)⟩

-- Gravity conversions
def mgalToMS2_F (mgal : MilliGal_F) : Acceleration_F :=
  ⟨mgal.val * 1e-5⟩

def ms2ToMgal_F (a : Acceleration_F) : MilliGal_F :=
  ⟨a.val * 1e5⟩

-- Pressure conversions
def hPaToBar_F (hpa : HectoPascal_F) : Float :=
  hpa.val / 1000.0

def barToHPa_F (bar : Float) : HectoPascal_F :=
  ⟨bar * 1000.0⟩

def hPaToPascal_F (hpa : HectoPascal_F) : Pascal_F :=
  ⟨hpa.val * 100.0⟩

-- Wind speed conversions
def knotsToMS_F (kt : Knots_F) : Velocity_F :=
  ⟨kt.val * 0.514444⟩

def msToKnots_F (v : Velocity_F) : Knots_F :=
  ⟨v.val / 0.514444⟩

def knotsToKmH_F (kt : Knots_F) : KmPerH_F :=
  ⟨kt.val * 1.852⟩

-- Temperature gradient conversions
def cPerKmToKPerM_F (grad : ThermalGradient_F) : Float :=
  grad.val / 1000.0

-- Coordinate conversions (simplified)
def degreesToRadians_F (deg : Degree_F) : Radian_F :=
  ⟨deg.val * pi_F / 180.0⟩

def radiansToDegrees_F (rad : Radian_F) : Degree_F :=
  ⟨rad.val * 180.0 / pi_F⟩

-- DMS to decimal degrees
def dmsToDecimal_F (deg : Float) (min : Float) (sec : Float) : Float :=
  deg + min/60.0 + sec/3600.0

-- Decimal to DMS
def decimalToDMS_F (decimal : Float) : (Float × Float × Float) :=
  let deg := decimal.floor
  let min_decimal := (decimal - deg) * 60.0
  let min := min_decimal.floor
  let sec := (min_decimal - min) * 60.0
  (deg, min, sec)

/--
================================================================================================
   Common Earth Science Calculations
================================================================================================
-/

-- Seismic wave velocities from elastic moduli
def pWaveVelocity_F (K : BulkModulus_F) (mu : Pascal_F) (rho : KgPerM3_F) : PWaveVelocity_F :=
  ⟨Float.sqrt ((K.val + 4.0/3.0 * mu.val) / rho.val)⟩

def sWaveVelocity_F (mu : Pascal_F) (rho : KgPerM3_F) : SWaveVelocity_F :=
  ⟨Float.sqrt (mu.val / rho.val)⟩

-- Richter magnitude from amplitude
def richterMagnitude_F (amplitude : Float) (distance : Kilometer_F) : RichterMagnitude_F :=
  ⟨Float.log amplitude / Float.log 10.0 + 3.0 * Float.log distance.val / Float.log 10.0 - 2.92⟩

-- Gravity at latitude (simplified)
def gravityAtLatitude_F (lat : Latitude_F) : Acceleration_F :=
  let lat_rad := lat.val * pi_F / 180.0
  let g := g_equator_F + (g_pole_F - g_equator_F) * (Float.sin lat_rad)^2
  ⟨g⟩

-- Free-air gravity correction
def freeAirCorrection_F (h : Elevation_F) : MilliGal_F :=
  ⟨0.3086 * h.val⟩  -- 0.3086 mGal/m

-- Bouguer correction
def bouguerCorrection_F (h : Elevation_F) (rho : GPerCm3_F) : MilliGal_F :=
  ⟨0.04193 * rho.val * h.val⟩  -- Simple Bouguer

-- Barometric formula
def pressureAtAltitude_F (P0 : HectoPascal_F) (h : Elevation_F)
    (T : Kelvin_F) : HectoPascal_F :=
  let scale_height := 8434.5 * T.val / 288.15  -- Approximate scale height
  ⟨P0.val * Float.exp (-h.val / scale_height)⟩

-- Virtual temperature
def virtualTemperature_F (T : Kelvin_F) (q : SpecificHumidity_F) : Kelvin_F :=
  ⟨T.val * (1.0 + 0.608 * q.val)⟩

-- Potential temperature
def potentialTemperature_F (T : Kelvin_F) (P : HectoPascal_F) : Kelvin_F :=
  ⟨T.val * (1000.0 / P.val) ^ (0.286)⟩  -- R/cp for dry air

-- Dewpoint from temperature and RH
def dewpoint_F (T : Celsius_F) (RH : RelativeHumidity_F) : Celsius_F :=
  let a := 17.27
  let b := 237.7
  let gamma := (a * T.val / (b + T.val)) + Float.log (RH.val / 100.0)
  ⟨b * gamma / (a - gamma)⟩

-- Saturation vapor pressure (Magnus formula)
def saturationVaporPressure_F (T : Celsius_F) : HectoPascal_F :=
  ⟨6.1094 * Float.exp (17.625 * T.val / (T.val + 243.04))⟩

-- Relative humidity from T and Td
def relativeHumidityFromDewpoint_F (T : Celsius_F) (Td : Celsius_F)
    : RelativeHumidity_F :=
  let es_T := saturationVaporPressure_F T
  let es_Td := saturationVaporPressure_F Td
  ⟨100.0 * es_Td.val / es_T.val⟩

-- Geostrophic wind (simplified)
def geostrophicWind_F (gradP : PascalPerMeter_F) (rho : KgPerM3_F)
    (lat : Latitude_F) : Velocity_F :=
  let f := 2.0 * omega_earth_F * Float.sin (lat.val * pi_F / 180.0)  -- Coriolis
  ⟨gradP.val / (rho.val * f)⟩

-- Ocean density from temperature and salinity (simplified)
def seawaterDensity_F (T : Celsius_F) (S : PSU_F) : KgPerM3_F :=
  let rho0 := 1024.0  -- Reference density
  let alpha := 0.2  -- Thermal expansion coefficient (approximate)
  let beta := 0.78  -- Haline contraction coefficient (approximate)
  ⟨rho0 * (1.0 - alpha * (T.val - 10.0) / 1000.0 + beta * (S.val - 35.0) / 1000.0)⟩

-- Wave celerity (deep water)
def waveSpeed_F (period : WavePeriod_F) : Velocity_F :=
  ⟨g_standard_F * period.val / (2.0 * pi_F)⟩

-- Wave length (deep water)
def waveLength_F (period : WavePeriod_F) : Meter_F :=
  ⟨g_standard_F * period.val^2 / (2.0 * pi_F)⟩

-- Significant wave height from energy spectrum
def significantWaveHeight_F (H_rms : WaveHeight_F) : WaveHeight_F :=
  ⟨4.0 * H_rms.val / Float.sqrt 2.0⟩

-- Radiative forcing from CO2 (simplified)
def co2Forcing_F (C : CO2_ppm_F) (C0 : CO2_ppm_F) : RadiativeForcing_F :=
  ⟨5.35 * Float.log (C.val / C0.val)⟩  -- IPCC formula

-- Temperature response to forcing
def temperatureResponse_F (forcing : RadiativeForcing_F)
    (sensitivity : ClimateSensitivity_F) : Kelvin_F :=
  ⟨forcing.val * sensitivity.val⟩

-- Planetary albedo energy balance
def planetaryEnergyBalance_F (S : Float) (albedo : Albedo_F)
    (T : Kelvin_F) : RadiativeForcing_F :=
  let incoming := S * (1.0 - albedo.val) / 4.0
  let outgoing := stefan_boltzmann_F * T.val^4
  ⟨incoming - outgoing⟩

-- Darcy velocity in aquifer
def darcyVelocityGroundwater_F (K : HydraulicConductivity_F)
    (gradient : HydraulicGradient_F) : SpecificDischarge_F :=
  ⟨K.val * gradient.val⟩

-- Transmissivity from hydraulic conductivity
def transmissivity_F (K : HydraulicConductivity_F) (b : Meter_F) : Transmissivity_F :=
  ⟨K.val * b.val⟩

-- Specific yield calculation
def specificYield_F (porosity : Porosity_F) (specificRetention : Float) : Float :=
  porosity.val - specificRetention

-- Earthquake energy from magnitude
def earthquakeEnergy_F (Mw : MomentMagnitude_F) : Joule_F :=
  ⟨10.0 ^ (1.5 * Mw.val + 4.8)⟩  -- Energy in Joules

-- Distance from lat/lon (Haversine formula)
def haversineDistance_F (lat1 : Latitude_F) (lon1 : Longitude_F)
    (lat2 : Latitude_F) (lon2 : Longitude_F) : Kilometer_F :=
  let lat1_rad := lat1.val * pi_F / 180.0
  let lat2_rad := lat2.val * pi_F / 180.0
  let dlat_rad := (lat2.val - lat1.val) * pi_F / 180.0
  let dlon_rad := (lon2.val - lon1.val) * pi_F / 180.0
  let a := (Float.sin (dlat_rad/2.0))^2 +
           Float.cos lat1_rad * Float.cos lat2_rad * (Float.sin (dlon_rad/2.0))^2
  let c := 2.0 * Float.atan2 (Float.sqrt a) (Float.sqrt (1.0 - a))
  ⟨R_earth_F * c / 1000.0⟩

-- Ice sheet mass balance
def iceMassBalance_F (accumulation : AccumulationRate_F)
    (ablation : Float) (area : Float) : MassBalance_F :=
  ⟨(accumulation.val - ablation) * 1000.0 / area⟩  -- Convert to kg/m²/yr

-- Volcanic eruption column height (simplified)
def eruptionColumnHeight_F (rate : EruptionRate_F) : Kilometer_F :=
  ⟨0.236 * (rate.val ^ 0.25)⟩  -- Morton et al. scaling

-- P-wave travel time (simplified)
def pWaveTravelTime_F (distance : Kilometer_F) (v_avg : PWaveVelocity_F) : Second_F :=
  ⟨distance.val * 1000.0 / v_avg.val⟩

-- Magnetic inclination from latitude (dipole approximation)
def magneticInclination_F (lat : Latitude_F) : Inclination_F :=
  ⟨Float.atan (2.0 * Float.tan (lat.val * pi_F / 180.0)) * 180.0 / pi_F⟩

end Units.Earth
