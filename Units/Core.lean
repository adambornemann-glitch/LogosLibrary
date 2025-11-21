-- Core.lean        -- Core SI base and fundamental derived units
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

namespace Units.SI

/-
================================================================================
CORE SI UNITS LIBRARY
================================================================================

This module provides the foundational SI base units and the most fundamental
derived units that are used across multiple physics domains.
Following the triple-type architecture for maximum flexibility without type
conversion friction.

## COVERAGE
- SI base units: meter, kilogram, second, ampere, kelvin, mole, candela
- Fundamental derived units used everywhere:
  * Kinematics: velocity, acceleration
  * Time/Frequency: hertz, minute, hour
  * Energy/Power: joule, watt (used in mechanics, thermal, EM, chemistry)
  * Angular: radian, steradian
- Common prefixes for all base units (milli-, micro-, nano-, kilo-, mega-)
- Dimensionless quantities (ratios, fractions, angles)

## DESIGN PHILOSOPHY
Only units that are truly fundamental and used across multiple domains belong
here. Domain-specific units (Force, Pressure, Electric Field, etc.) belong
in their respective modules to avoid this becoming a monolithic file.

## USAGE PATTERNS
Float: Sensor data, real-time calculations, engineering applications,
numerical simulations, measurement data, control systems

ℚ: Exact ratios, unit conversions, calibration constants,
discrete counting, financial calculations, exact fractions

ℝ: Theoretical proofs, continuous analysis, calculus-based physics,
mathematical physics, formal verification, limit calculations
-/

set_option autoImplicit false
set_option linter.unusedVariables false

/--
================================================================================================
   Mathematical Constants for Float Calculations
================================================================================================
-/
def pi_F : Float := 3.14159265358979323846
def tau_F : Float := 6.28318530717958647692  -- 2π
def e_F : Float := 2.71828182845904523536
def sqrt2_F : Float := 1.41421356237309504880
def sqrt3_F : Float := 1.73205080756887729352
def ln2_F : Float := 0.693147180559945309417
def ln10_F : Float := 2.30258509299404568402

/--
================================================================================================
   Dimensionless Quantities
================================================================================================
-/
-- Pure ratios and fractions
structure Ratio_F      where val : Float deriving Repr, BEq, Inhabited
structure Ratio_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Ratio_R      where val : ℝ     deriving Inhabited

structure Fraction_F   where val : Float deriving Repr, BEq, Inhabited
structure Fraction_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Fraction_R   where val : ℝ     deriving Inhabited

structure Percent_F    where val : Float deriving Repr, BEq, Inhabited
structure Percent_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Percent_R    where val : ℝ     deriving Inhabited

-- Angles (dimensionless but with geometric meaning)
structure Radian_F     where val : Float deriving Repr, BEq, Inhabited
structure Radian_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Radian_R     where val : ℝ     deriving Inhabited

structure Degree_F     where val : Float deriving Repr, BEq, Inhabited
structure Degree_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Degree_R     where val : ℝ     deriving Inhabited

structure Steradian_F  where val : Float deriving Repr, BEq, Inhabited
structure Steradian_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Steradian_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Length - Meter (m) - SI Base Unit
================================================================================================
-/
-- Base unit
structure Meter_F      where val : Float deriving Repr, BEq, Inhabited
structure Meter_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Meter_R      where val : ℝ     deriving Inhabited

-- Submultiples
structure Decimeter_F  where val : Float deriving Repr, BEq, Inhabited
structure Decimeter_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Decimeter_R  where val : ℝ     deriving Inhabited

structure Centimeter_F where val : Float deriving Repr, BEq, Inhabited
structure Centimeter_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Centimeter_R where val : ℝ     deriving Inhabited

structure Millimeter_F where val : Float deriving Repr, BEq, Inhabited
structure Millimeter_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Millimeter_R where val : ℝ     deriving Inhabited

structure Micrometer_F where val : Float deriving Repr, BEq, Inhabited
structure Micrometer_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Micrometer_R where val : ℝ     deriving Inhabited

structure Nanometer_F  where val : Float deriving Repr, BEq, Inhabited
structure Nanometer_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Nanometer_R  where val : ℝ     deriving Inhabited

structure Picometer_F  where val : Float deriving Repr, BEq, Inhabited
structure Picometer_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Picometer_R  where val : ℝ     deriving Inhabited

structure Femtometer_F where val : Float deriving Repr, BEq, Inhabited
structure Femtometer_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Femtometer_R where val : ℝ     deriving Inhabited

-- Multiples
structure Kilometer_F  where val : Float deriving Repr, BEq, Inhabited
structure Kilometer_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kilometer_R  where val : ℝ     deriving Inhabited

structure Megameter_F  where val : Float deriving Repr, BEq, Inhabited
structure Megameter_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Megameter_R  where val : ℝ     deriving Inhabited

structure Gigameter_F  where val : Float deriving Repr, BEq, Inhabited
structure Gigameter_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Gigameter_R  where val : ℝ     deriving Inhabited

-- Area (m²)
structure Meter2_F     where val : Float deriving Repr, BEq, Inhabited
structure Meter2_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Meter2_R     where val : ℝ     deriving Inhabited

structure Cm2_F        where val : Float deriving Repr, BEq, Inhabited
structure Cm2_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Cm2_R        where val : ℝ     deriving Inhabited

structure Mm2_F        where val : Float deriving Repr, BEq, Inhabited
structure Mm2_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Mm2_R        where val : ℝ     deriving Inhabited

structure Km2_F        where val : Float deriving Repr, BEq, Inhabited
structure Km2_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Km2_R        where val : ℝ     deriving Inhabited

-- Volume (m³)
structure Meter3_F     where val : Float deriving Repr, BEq, Inhabited
structure Meter3_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Meter3_R     where val : ℝ     deriving Inhabited

structure Cm3_F        where val : Float deriving Repr, BEq, Inhabited
structure Cm3_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Cm3_R        where val : ℝ     deriving Inhabited

structure Mm3_F        where val : Float deriving Repr, BEq, Inhabited
structure Mm3_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Mm3_R        where val : ℝ     deriving Inhabited

-- Liter (special name for dm³)
structure Liter_F      where val : Float deriving Repr, BEq, Inhabited
structure Liter_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Liter_R      where val : ℝ     deriving Inhabited

structure Milliliter_F where val : Float deriving Repr, BEq, Inhabited
structure Milliliter_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Milliliter_R where val : ℝ     deriving Inhabited

structure Microliter_F where val : Float deriving Repr, BEq, Inhabited
structure Microliter_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Microliter_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Mass - Kilogram (kg) - SI Base Unit
================================================================================================
-/
-- Base unit
structure Kilogram_F   where val : Float deriving Repr, BEq, Inhabited
structure Kilogram_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kilogram_R   where val : ℝ     deriving Inhabited

-- Submultiples
structure Gram_F       where val : Float deriving Repr, BEq, Inhabited
structure Gram_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Gram_R       where val : ℝ     deriving Inhabited

structure Milligram_F  where val : Float deriving Repr, BEq, Inhabited
structure Milligram_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Milligram_R  where val : ℝ     deriving Inhabited

structure Microgram_F  where val : Float deriving Repr, BEq, Inhabited
structure Microgram_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Microgram_R  where val : ℝ     deriving Inhabited

structure Nanogram_F   where val : Float deriving Repr, BEq, Inhabited
structure Nanogram_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Nanogram_R   where val : ℝ     deriving Inhabited

structure Picogram_F   where val : Float deriving Repr, BEq, Inhabited
structure Picogram_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Picogram_R   where val : ℝ     deriving Inhabited

-- Multiples
structure MetricTon_F  where val : Float deriving Repr, BEq, Inhabited  -- 1000 kg
structure MetricTon_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MetricTon_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Time - Second (s) - SI Base Unit
================================================================================================
-/
-- Base unit
structure Second_F     where val : Float deriving Repr, BEq, Inhabited
structure Second_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Second_R     where val : ℝ     deriving Inhabited

structure PerSecond_F     where val : Float deriving Repr, BEq, Inhabited
structure PerSecond_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PerSecond_R     where val : ℝ     deriving Inhabited

-- Submultiples
structure Millisecond_F where val : Float deriving Repr, BEq, Inhabited
structure Millisecond_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Millisecond_R where val : ℝ     deriving Inhabited

structure Microsecond_F where val : Float deriving Repr, BEq, Inhabited
structure Microsecond_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Microsecond_R where val : ℝ     deriving Inhabited

structure Nanosecond_F where val : Float deriving Repr, BEq, Inhabited
structure Nanosecond_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Nanosecond_R where val : ℝ     deriving Inhabited

structure Picosecond_F where val : Float deriving Repr, BEq, Inhabited
structure Picosecond_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Picosecond_R where val : ℝ     deriving Inhabited

structure Femtosecond_F where val : Float deriving Repr, BEq, Inhabited
structure Femtosecond_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Femtosecond_R where val : ℝ     deriving Inhabited

-- Common time units
structure Minute_F     where val : Float deriving Repr, BEq, Inhabited
structure Minute_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Minute_R     where val : ℝ     deriving Inhabited

structure Hour_F       where val : Float deriving Repr, BEq, Inhabited
structure Hour_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Hour_R       where val : ℝ     deriving Inhabited

structure Day_F        where val : Float deriving Repr, BEq, Inhabited
structure Day_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Day_R        where val : ℝ     deriving Inhabited

structure Week_F       where val : Float deriving Repr, BEq, Inhabited
structure Week_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Week_R       where val : ℝ     deriving Inhabited

structure Year_F       where val : Float deriving Repr, BEq, Inhabited  -- 365.25 days
structure Year_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Year_R       where val : ℝ     deriving Inhabited

/--
================================================================================================
   Temperature - Kelvin (K) - SI Base Unit
================================================================================================
-/
structure Kelvin_F     where val : Float deriving Repr, BEq, Inhabited
structure Kelvin_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kelvin_R     where val : ℝ     deriving Inhabited

-- Common temperature scales (for convenience)
structure Celsius_F    where val : Float deriving Repr, BEq, Inhabited
structure Celsius_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Celsius_R    where val : ℝ     deriving Inhabited

structure Fahrenheit_F where val : Float deriving Repr, BEq, Inhabited
structure Fahrenheit_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Fahrenheit_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Electric Current - Ampere (A) - SI Base Unit
================================================================================================
-/
-- Moved to Electromagnetism.lean to keep all electrical units together

/-
================================================================================================
   Amount of Substance - Mole (mol) - SI Base Unit
================================================================================================
-/
structure Mole_F       where val : Float deriving Repr, BEq, Inhabited
structure Mole_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Mole_R       where val : ℝ     deriving Inhabited

structure Millimole_F  where val : Float deriving Repr, BEq, Inhabited
structure Millimole_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Millimole_R  where val : ℝ     deriving Inhabited

structure Micromole_F  where val : Float deriving Repr, BEq, Inhabited
structure Micromole_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Micromole_R  where val : ℝ     deriving Inhabited

structure Nanomole_F   where val : Float deriving Repr, BEq, Inhabited
structure Nanomole_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Nanomole_R   where val : ℝ     deriving Inhabited

structure Picomole_F   where val : Float deriving Repr, BEq, Inhabited
structure Picomole_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Picomole_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Luminous Intensity - Candela (cd) - SI Base Unit
================================================================================================
-/
structure Candela_F    where val : Float deriving Repr, BEq, Inhabited
structure Candela_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Candela_R    where val : ℝ     deriving Inhabited

-- Luminous flux: lumen (lm) = cd⋅sr
structure Lumen_F      where val : Float deriving Repr, BEq, Inhabited
structure Lumen_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Lumen_R      where val : ℝ     deriving Inhabited

-- Illuminance: lux (lx) = lm/m²
structure Lux_F        where val : Float deriving Repr, BEq, Inhabited
structure Lux_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Lux_R        where val : ℝ     deriving Inhabited

/--
================================================================================================
   Fundamental Derived Units - Kinematics
================================================================================================
-/
-- Velocity: m/s
structure Velocity_F   where val : Float deriving Repr, BEq, Inhabited
structure Velocity_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Velocity_R   where val : ℝ     deriving Inhabited

structure KmPerH_F     where val : Float deriving Repr, BEq, Inhabited  -- km/h
structure KmPerH_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KmPerH_R     where val : ℝ     deriving Inhabited

-- Acceleration: m/s²
structure Acceleration_F where val : Float deriving Repr, BEq, Inhabited
structure Acceleration_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Acceleration_R where val : ℝ     deriving Inhabited

-- Jerk: m/s³ (rate of change of acceleration)
structure Jerk_F       where val : Float deriving Repr, BEq, Inhabited
structure Jerk_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Jerk_R       where val : ℝ     deriving Inhabited

/--
================================================================================================
   Fundamental Derived Units - Frequency
================================================================================================
-/
-- Frequency: holder
structure Frequency_F      where val : Float deriving Repr, BEq, Inhabited
structure Frequency_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Frequency_R      where val : ℝ     deriving Inhabited

-- Hz = s⁻¹
structure Hertz_F      where val : Float deriving Repr, BEq, Inhabited
structure Hertz_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Hertz_R      where val : ℝ     deriving Inhabited

structure Kilohertz_F  where val : Float deriving Repr, BEq, Inhabited
structure Kilohertz_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kilohertz_R  where val : ℝ     deriving Inhabited

structure Megahertz_F  where val : Float deriving Repr, BEq, Inhabited
structure Megahertz_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Megahertz_R  where val : ℝ     deriving Inhabited

structure Gigahertz_F  where val : Float deriving Repr, BEq, Inhabited
structure Gigahertz_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Gigahertz_R  where val : ℝ     deriving Inhabited

-- Becquerel: Bq = s⁻¹ (radioactive decay)
structure Becquerel_F  where val : Float deriving Repr, BEq, Inhabited
structure Becquerel_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Becquerel_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Fundamental Derived Units - Energy
================================================================================================
-/
-- Energy: Joule (J) = kg⋅m²/s²
structure Joule_F      where val : Float deriving Repr, BEq, Inhabited
structure Joule_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Joule_R      where val : ℝ     deriving Inhabited

structure Kilojoule_F  where val : Float deriving Repr, BEq, Inhabited
structure Kilojoule_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kilojoule_R  where val : ℝ     deriving Inhabited

structure Megajoule_F  where val : Float deriving Repr, BEq, Inhabited
structure Megajoule_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Megajoule_R  where val : ℝ     deriving Inhabited

-- Electron volt (common in physics)
structure ElectronVolt_F where val : Float deriving Repr, BEq, Inhabited
structure ElectronVolt_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ElectronVolt_R where val : ℝ     deriving Inhabited

structure MeV_F        where val : Float deriving Repr, BEq, Inhabited
structure MeV_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MeV_R        where val : ℝ     deriving Inhabited

structure GeV_F        where val : Float deriving Repr, BEq, Inhabited
structure GeV_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GeV_R        where val : ℝ     deriving Inhabited

-- Calorie (for compatibility)
structure Calorie_F    where val : Float deriving Repr, BEq, Inhabited
structure Calorie_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Calorie_R    where val : ℝ     deriving Inhabited

structure Kilocalorie_F where val : Float deriving Repr, BEq, Inhabited
structure Kilocalorie_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kilocalorie_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Fundamental Derived Units - Power
================================================================================================
-/
-- Power: Watt (W) = J/s = kg⋅m²/s³
structure Watt_F       where val : Float deriving Repr, BEq, Inhabited
structure Watt_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Watt_R       where val : ℝ     deriving Inhabited

structure Milliwatt_F  where val : Float deriving Repr, BEq, Inhabited
structure Milliwatt_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Milliwatt_R  where val : ℝ     deriving Inhabited

structure Kilowatt_F   where val : Float deriving Repr, BEq, Inhabited
structure Kilowatt_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kilowatt_R   where val : ℝ     deriving Inhabited

structure Megawatt_F   where val : Float deriving Repr, BEq, Inhabited
structure Megawatt_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Megawatt_R   where val : ℝ     deriving Inhabited

structure Gigawatt_F   where val : Float deriving Repr, BEq, Inhabited
structure Gigawatt_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Gigawatt_R   where val : ℝ     deriving Inhabited

-- Horsepower (for compatibility)
structure Horsepower_F where val : Float deriving Repr, BEq, Inhabited
structure Horsepower_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Horsepower_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Fundamental Derived Units - Density
================================================================================================
-/
-- Density: kg/m³
structure KgPerM3_F    where val : Float deriving Repr, BEq, Inhabited
structure KgPerM3_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KgPerM3_R    where val : ℝ     deriving Inhabited

structure GPerCm3_F    where val : Float deriving Repr, BEq, Inhabited
structure GPerCm3_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GPerCm3_R    where val : ℝ     deriving Inhabited

structure GPerL_F      where val : Float deriving Repr, BEq, Inhabited
structure GPerL_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GPerL_R      where val : ℝ     deriving Inhabited

/--
================================================================================================
   Unit Conversions - Basic
================================================================================================
-/

-- Length conversions
def meterToKilometer_F (m : Meter_F) : Kilometer_F := ⟨m.val / 1000.0⟩
def kilometerToMeter_F (km : Kilometer_F) : Meter_F := ⟨km.val * 1000.0⟩
def meterToCentimeter_F (m : Meter_F) : Centimeter_F := ⟨m.val * 100.0⟩
def centimeterToMeter_F (cm : Centimeter_F) : Meter_F := ⟨cm.val / 100.0⟩
def meterToMillimeter_F (m : Meter_F) : Millimeter_F := ⟨m.val * 1000.0⟩
def millimeterToMeter_F (mm : Millimeter_F) : Meter_F := ⟨mm.val / 1000.0⟩
def meterToMicrometer_F (m : Meter_F) : Micrometer_F := ⟨m.val * 1e6⟩
def micrometerToMeter_F (um : Micrometer_F) : Meter_F := ⟨um.val / 1e6⟩
def meterToNanometer_F (m : Meter_F) : Nanometer_F := ⟨m.val * 1e9⟩
def nanometerToMeter_F (nm : Nanometer_F) : Meter_F := ⟨nm.val / 1e9⟩

-- Mass conversions
def kilogramToGram_F (kg : Kilogram_F) : Gram_F := ⟨kg.val * 1000.0⟩
def gramToKilogram_F (g : Gram_F) : Kilogram_F := ⟨g.val / 1000.0⟩
def gramToMilligram_F (g : Gram_F) : Milligram_F := ⟨g.val * 1000.0⟩
def milligramToGram_F (mg : Milligram_F) : Gram_F := ⟨mg.val / 1000.0⟩
def gramToMicrogram_F (g : Gram_F) : Microgram_F := ⟨g.val * 1e6⟩
def microgramToGram_F (ug : Microgram_F) : Gram_F := ⟨ug.val / 1e6⟩
def kilogramToMetricTon_F (kg : Kilogram_F) : MetricTon_F := ⟨kg.val / 1000.0⟩
def metricTonToKilogram_F (t : MetricTon_F) : Kilogram_F := ⟨t.val * 1000.0⟩

-- Time conversions
def secondToMillisecond_F (s : Second_F) : Millisecond_F := ⟨s.val * 1000.0⟩
def millisecondToSecond_F (ms : Millisecond_F) : Second_F := ⟨ms.val / 1000.0⟩
def secondToMicrosecond_F (s : Second_F) : Microsecond_F := ⟨s.val * 1e6⟩
def microsecondToSecond_F (us : Microsecond_F) : Second_F := ⟨us.val / 1e6⟩
def secondToNanosecond_F (s : Second_F) : Nanosecond_F := ⟨s.val * 1e9⟩
def nanosecondToSecond_F (ns : Nanosecond_F) : Second_F := ⟨ns.val / 1e9⟩
def secondToMinute_F (s : Second_F) : Minute_F := ⟨s.val / 60.0⟩
def minuteToSecond_F (m : Minute_F) : Second_F := ⟨m.val * 60.0⟩
def minuteToHour_F (m : Minute_F) : Hour_F := ⟨m.val / 60.0⟩
def hourToMinute_F (h : Hour_F) : Minute_F := ⟨h.val * 60.0⟩
def hourToDay_F (h : Hour_F) : Day_F := ⟨h.val / 24.0⟩
def dayToHour_F (d : Day_F) : Hour_F := ⟨d.val * 24.0⟩

-- Temperature conversions
def celsiusToKelvin_F (c : Celsius_F) : Kelvin_F := ⟨c.val + 273.15⟩
def kelvinToCelsius_F (k : Kelvin_F) : Celsius_F := ⟨k.val - 273.15⟩
def fahrenheitToCelsius_F (f : Fahrenheit_F) : Celsius_F := ⟨(f.val - 32.0) * 5.0 / 9.0⟩
def celsiusToFahrenheit_F (c : Celsius_F) : Fahrenheit_F := ⟨c.val * 9.0 / 5.0 + 32.0⟩
def fahrenheitToKelvin_F (f : Fahrenheit_F) : Kelvin_F :=
  celsiusToKelvin_F (fahrenheitToCelsius_F f)
def kelvinToFahrenheit_F (k : Kelvin_F) : Fahrenheit_F :=
  celsiusToFahrenheit_F (kelvinToCelsius_F k)

-- Volume conversions
def literToMilliliter_F (l : Liter_F) : Milliliter_F := ⟨l.val * 1000.0⟩
def milliliterToLiter_F (ml : Milliliter_F) : Liter_F := ⟨ml.val / 1000.0⟩
def literToMeter3_F (l : Liter_F) : Meter3_F := ⟨l.val / 1000.0⟩
def meter3ToLiter_F (m3 : Meter3_F) : Liter_F := ⟨m3.val * 1000.0⟩
def cm3ToMilliliter_F (cm3 : Cm3_F) : Milliliter_F := ⟨cm3.val⟩  -- 1 cm³ = 1 mL

-- Angle conversions
def radianToDegree_F (r : Radian_F) : Degree_F := ⟨r.val * 180.0 / pi_F⟩
def degreeToRadian_F (d : Degree_F) : Radian_F := ⟨d.val * pi_F / 180.0⟩

-- Velocity conversions
def mpsToKmph_F (mps : Velocity_F) : KmPerH_F := ⟨mps.val * 3.6⟩
def kmphToMps_F (kmph : KmPerH_F) : Velocity_F := ⟨kmph.val / 3.6⟩

-- Frequency conversions
def hertzToKilohertz_F (hz : Hertz_F) : Kilohertz_F := ⟨hz.val / 1000.0⟩
def kilohertzToHertz_F (khz : Kilohertz_F) : Hertz_F := ⟨khz.val * 1000.0⟩
def kilohertzToMegahertz_F (khz : Kilohertz_F) : Megahertz_F := ⟨khz.val / 1000.0⟩
def megahertzToKilohertz_F (mhz : Megahertz_F) : Kilohertz_F := ⟨mhz.val * 1000.0⟩
def megahertzToGigahertz_F (mhz : Megahertz_F) : Gigahertz_F := ⟨mhz.val / 1000.0⟩
def gigahertzToMegahertz_F (ghz : Gigahertz_F) : Megahertz_F := ⟨ghz.val * 1000.0⟩

-- Energy conversions
def jouleToKilojoule_F (j : Joule_F) : Kilojoule_F := ⟨j.val / 1000.0⟩
def kilojouleToJoule_F (kj : Kilojoule_F) : Joule_F := ⟨kj.val * 1000.0⟩
def jouleToCalorie_F (j : Joule_F) : Calorie_F := ⟨j.val / 4.184⟩
def calorieToJoule_F (cal : Calorie_F) : Joule_F := ⟨cal.val * 4.184⟩
def calorieToKilocalorie_F (cal : Calorie_F) : Kilocalorie_F := ⟨cal.val / 1000.0⟩
def kilocalorieToCalorie_F (kcal : Kilocalorie_F) : Calorie_F := ⟨kcal.val * 1000.0⟩
def jouleToElectronVolt_F (j : Joule_F) : ElectronVolt_F := ⟨j.val / 1.602176634e-19⟩
def electronVoltToJoule_F (ev : ElectronVolt_F) : Joule_F := ⟨ev.val * 1.602176634e-19⟩

-- Power conversions
def wattToKilowatt_F (w : Watt_F) : Kilowatt_F := ⟨w.val / 1000.0⟩
def kilowattToWatt_F (kw : Kilowatt_F) : Watt_F := ⟨kw.val * 1000.0⟩
def kilowattToMegawatt_F (kw : Kilowatt_F) : Megawatt_F := ⟨kw.val / 1000.0⟩
def megawattToKilowatt_F (mw : Megawatt_F) : Kilowatt_F := ⟨mw.val * 1000.0⟩
def wattToHorsepower_F (w : Watt_F) : Horsepower_F := ⟨w.val / 745.7⟩
def horsepowerToWatt_F (hp : Horsepower_F) : Watt_F := ⟨hp.val * 745.7⟩

-- Density conversions
def kgPerM3ToGPerCm3_F (kgm3 : KgPerM3_F) : GPerCm3_F := ⟨kgm3.val / 1000.0⟩
def gPerCm3ToKgPerM3_F (gcm3 : GPerCm3_F) : KgPerM3_F := ⟨gcm3.val * 1000.0⟩

-- Percent conversions
def fractionToPercent_F (f : Fraction_F) : Percent_F := ⟨f.val * 100.0⟩
def percentToFraction_F (p : Percent_F) : Fraction_F := ⟨p.val / 100.0⟩
def ratioToPercent_F (r : Ratio_F) : Percent_F := ⟨r.val * 100.0⟩
def percentToRatio_F (p : Percent_F) : Ratio_F := ⟨p.val / 100.0⟩

/--
================================================================================================
   Validation Helpers
================================================================================================
-/

-- Temperature validation
def isAboveAbsoluteZero_F (k : Kelvin_F) : Bool := k.val ≥ 0.0
def isAboveAbsoluteZero_Q (k : Kelvin_Q) : Bool := k.val ≥ 0
noncomputable def isAboveAbsoluteZero_R (k : Kelvin_R) : Prop := k.val ≥ 0

-- Physical length validation
def isPositiveLength_F (m : Meter_F) : Bool := m.val > 0.0
def isPositiveLength_Q (m : Meter_Q) : Bool := m.val > 0

-- Mass validation
def isPositiveMass_F (kg : Kilogram_F) : Bool := kg.val > 0.0
def isPositiveMass_Q (kg : Kilogram_Q) : Bool := kg.val > 0

-- Time validation
def isPositiveTime_F (s : Second_F) : Bool := s.val > 0.0
def isPositiveTime_Q (s : Second_Q) : Bool := s.val > 0

-- Frequency validation
def isPositiveFrequency_F (hz : Hertz_F) : Bool := hz.val ≥ 0.0
def isPositiveFrequency_Q (hz : Hertz_Q) : Bool := hz.val ≥ 0

-- Energy validation
def isPositiveEnergy_F (j : Joule_F) : Bool := j.val ≥ 0.0
def isPositiveEnergy_Q (j : Joule_Q) : Bool := j.val ≥ 0

-- Angle validation
def isValidRadian_F (r : Radian_F) : Bool := -tau_F ≤ r.val && r.val ≤ tau_F
def isValidDegree_F (d : Degree_F) : Bool := -360.0 ≤ d.val && d.val ≤ 360.0

-- Percentage validation
def isValidPercent_F (p : Percent_F) : Bool := 0.0 ≤ p.val && p.val ≤ 100.0
def isValidFraction_F (f : Fraction_F) : Bool := 0.0 ≤ f.val && f.val ≤ 1.0

/--
================================================================================================
   Basic Calculations
================================================================================================
-/

-- Kinematic calculations
def velocityFromDistanceTime_F (d : Meter_F) (t : Second_F) : Velocity_F :=
  ⟨d.val / t.val⟩

def accelerationFromVelocityTime_F (v : Velocity_F) (t : Second_F) : Acceleration_F :=
  ⟨v.val / t.val⟩

def distanceFromVelocityTime_F (v : Velocity_F) (t : Second_F) : Meter_F :=
  ⟨v.val * t.val⟩

-- Energy/Power calculations
def energyFromPowerTime_F (p : Watt_F) (t : Second_F) : Joule_F :=
  ⟨p.val * t.val⟩

def powerFromEnergyTime_F (e : Joule_F) (t : Second_F) : Watt_F :=
  ⟨e.val / t.val⟩

-- Density calculations
def densityFromMassVolume_F (m : Kilogram_F) (v : Meter3_F) : KgPerM3_F :=
  ⟨m.val / v.val⟩

def massFromDensityVolume_F (rho : KgPerM3_F) (v : Meter3_F) : Kilogram_F :=
  ⟨rho.val * v.val⟩

def volumeFromMassDensity_F (m : Kilogram_F) (rho : KgPerM3_F) : Meter3_F :=
  ⟨m.val / rho.val⟩

-- Area and volume calculations
def areaRectangle_F (l : Meter_F) (w : Meter_F) : Meter2_F :=
  ⟨l.val * w.val⟩

def areaCircle_F (r : Meter_F) : Meter2_F :=
  ⟨pi_F * r.val * r.val⟩

def volumeRectangular_F (l : Meter_F) (w : Meter_F) (h : Meter_F) : Meter3_F :=
  ⟨l.val * w.val * h.val⟩

def volumeSphere_F (r : Meter_F) : Meter3_F :=
  ⟨(4.0 / 3.0) * pi_F * r.val * r.val * r.val⟩

def volumeCylinder_F (r : Meter_F) (h : Meter_F) : Meter3_F :=
  ⟨pi_F * r.val * r.val * h.val⟩

-- Period/Frequency relation
def periodFromFrequency_F (f : Hertz_F) : Second_F :=
  if f.val == 0.0 then ⟨1e308⟩ else ⟨1.0 / f.val⟩  -- Max Float value

def frequencyFromPeriod_F (t : Second_F) : Hertz_F :=
  if t.val == 0.0 then ⟨0.0⟩ else ⟨1.0 / t.val⟩

-- Illuminance calculations
def luminousFlux_F (intensity : Candela_F) (solidAngle : Steradian_F) : Lumen_F :=
  ⟨intensity.val * solidAngle.val⟩

def illuminance_F (flux : Lumen_F) (area : Meter2_F) : Lux_F :=
  ⟨flux.val / area.val⟩

end Units.SI
