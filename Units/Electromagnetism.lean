-- Electromagnetism.lean        -- Electric, magnetic, and electromagnetic units
import LogosLibrary.Units.Core.SI
import LogosLibrary.Units.Physics.Mechanics
import LogosLibrary.Units.Physics.Waves
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Util.CountHeartbeats

namespace Units.Physics.Electromagnetism

open Units.Standard Units.Physics.Mechanics Units.Physics.Waves

/-
================================================================================
ELECTROMAGNETIC UNITS LIBRARY
================================================================================

This module provides type-safe units for electromagnetism, covering electrostatics,
magnetostatics, electrodynamics, AC circuits, and electromagnetic field theory.
Following the triple-type architecture for maximum flexibility without type
conversion friction.

## COVERAGE
- Electric field quantities (field strength, potential, flux)
- Electric charge and current (charge, current density, mobility)
- Capacitance and dielectric properties
- Magnetic field quantities (B-field, H-field, flux, vector potential)
- Inductance and magnetic materials
- Resistance, conductance, impedance (including complex)
- AC circuit analysis (reactance, admittance, phase angles)
- Electromagnetic energy and power (Poynting vector, energy density)
- Electromagnetic material properties (permittivity, permeability, susceptibility)
- Electromagnetic waves and propagation
- Practical units for electronics and power engineering

## USAGE PATTERNS
Float: Circuit measurements, sensor readings, power calculations,
signal processing, antenna measurements, motor control, battery management,
real-time control systems, RF engineering, electromagnetic simulations

ℚ: Exact resistance ratios, precise capacitor/inductor values,
voltage divider calculations, transformer ratios, impedance matching,
crystal oscillator frequencies, digital filter coefficients

ℝ: Maxwell equations solutions, electromagnetic field theory,
wave propagation analysis, antenna theory proofs, quantum electrodynamics,
relativistic electromagnetism, formal verification of circuit theorems
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
def mu0_F : Float := 1.25663706212e-6  -- Vacuum permeability (N/A²)
def epsilon0_F : Float := 8.8541878128e-12  -- Vacuum permittivity (F/m)
def c_F : Float := 299792458.0  -- Speed of light (m/s)
def e_charge_F : Float := 1.602176634e-19  -- Elementary charge (C)
def k_coulomb_F : Float := 8.9875517923e9  -- Coulomb constant (N⋅m²/C²)

/--
================================================================================================
   Electric Charge and Current
================================================================================================
-/
-- Charge: Coulombs (C) - already in Core.SI
structure Coulomb_F    where val : Float deriving Repr, BEq, Inhabited
structure Coulomb_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Coulomb_R    where val : ℝ     deriving Inhabited

structure MilliCoulomb_F where val : Float deriving Repr, BEq, Inhabited
structure MilliCoulomb_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilliCoulomb_R where val : ℝ     deriving Inhabited

structure MicroCoulomb_F where val : Float deriving Repr, BEq, Inhabited
structure MicroCoulomb_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MicroCoulomb_R where val : ℝ     deriving Inhabited

structure NanoCoulomb_F where val : Float deriving Repr, BEq, Inhabited
structure NanoCoulomb_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NanoCoulomb_R where val : ℝ     deriving Inhabited

structure PicoCoulomb_F where val : Float deriving Repr, BEq, Inhabited
structure PicoCoulomb_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PicoCoulomb_R where val : ℝ     deriving Inhabited

-- Current: Amperes (A) - already in Core.SI
structure Ampere_F     where val : Float deriving Repr, BEq, Inhabited
structure Ampere_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Ampere_R     where val : ℝ     deriving Inhabited

structure MilliAmpere_F where val : Float deriving Repr, BEq, Inhabited
structure MilliAmpere_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilliAmpere_R where val : ℝ     deriving Inhabited

structure MicroAmpere_F where val : Float deriving Repr, BEq, Inhabited
structure MicroAmpere_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MicroAmpere_R where val : ℝ     deriving Inhabited

structure NanoAmpere_F where val : Float deriving Repr, BEq, Inhabited
structure NanoAmpere_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NanoAmpere_R where val : ℝ     deriving Inhabited

structure PicoAmpere_F where val : Float deriving Repr, BEq, Inhabited
structure PicoAmpere_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PicoAmpere_R where val : ℝ     deriving Inhabited

-- Current density: A/m²
structure APerM2_F     where val : Float deriving Repr, BEq, Inhabited
structure APerM2_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure APerM2_R     where val : ℝ     deriving Inhabited

-- Surface charge density: C/m²
structure CPerM2_F     where val : Float deriving Repr, BEq, Inhabited
structure CPerM2_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CPerM2_R     where val : ℝ     deriving Inhabited

-- Linear charge density: C/m
structure CPerM_F      where val : Float deriving Repr, BEq, Inhabited
structure CPerM_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CPerM_R      where val : ℝ     deriving Inhabited

-- Volume charge density: C/m³
structure CPerM3_F     where val : Float deriving Repr, BEq, Inhabited
structure CPerM3_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CPerM3_R     where val : ℝ     deriving Inhabited

/--
================================================================================================
   Electric Potential and Field
================================================================================================
-/
-- Voltage: Volts (V)
structure Volt_F       where val : Float deriving Repr, BEq, Inhabited
structure Volt_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Volt_R       where val : ℝ     deriving Inhabited

structure KiloVolt_F   where val : Float deriving Repr, BEq, Inhabited
structure KiloVolt_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KiloVolt_R   where val : ℝ     deriving Inhabited

structure MilliVolt_F  where val : Float deriving Repr, BEq, Inhabited
structure MilliVolt_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilliVolt_R  where val : ℝ     deriving Inhabited

structure MicroVolt_F  where val : Float deriving Repr, BEq, Inhabited
structure MicroVolt_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MicroVolt_R  where val : ℝ     deriving Inhabited

-- Wattages: Watts (w)
-- structure Watt_F     where val : Float deriving Repr, BEq, Inhabited
-- structure Watt_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
-- structure Watt_R     where val : ℝ     deriving Inhabited


-- Electric field: V/m or N/C
structure VPerM_F      where val : Float deriving Repr, BEq, Inhabited
structure VPerM_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VPerM_R      where val : ℝ     deriving Inhabited

structure KVPerM_F     where val : Float deriving Repr, BEq, Inhabited
structure KVPerM_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KVPerM_R     where val : ℝ     deriving Inhabited

structure MVPerM_F     where val : Float deriving Repr, BEq, Inhabited
structure MVPerM_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MVPerM_R     where val : ℝ     deriving Inhabited

-- Electric flux: V⋅m
structure VoltMeter_F  where val : Float deriving Repr, BEq, Inhabited
structure VoltMeter_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VoltMeter_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Resistance and Conductance
================================================================================================
-/
-- Resistance: Ohms (Ω)
structure Ohm_F        where val : Float deriving Repr, BEq, Inhabited
structure Ohm_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Ohm_R        where val : ℝ     deriving Inhabited

structure KiloOhm_F    where val : Float deriving Repr, BEq, Inhabited
structure KiloOhm_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KiloOhm_R    where val : ℝ     deriving Inhabited

structure MegaOhm_F    where val : Float deriving Repr, BEq, Inhabited
structure MegaOhm_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MegaOhm_R    where val : ℝ     deriving Inhabited

structure MilliOhm_F   where val : Float deriving Repr, BEq, Inhabited
structure MilliOhm_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilliOhm_R   where val : ℝ     deriving Inhabited

-- Conductance: Siemens (S) = 1/Ω
structure Siemens_F    where val : Float deriving Repr, BEq, Inhabited
structure Siemens_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Siemens_R    where val : ℝ     deriving Inhabited

structure MilliSiemens_F where val : Float deriving Repr, BEq, Inhabited
structure MilliSiemens_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilliSiemens_R where val : ℝ     deriving Inhabited

structure MicroSiemens_F where val : Float deriving Repr, BEq, Inhabited
structure MicroSiemens_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MicroSiemens_R where val : ℝ     deriving Inhabited

-- Resistivity: Ω⋅m
structure OhmMeter_F   where val : Float deriving Repr, BEq, Inhabited
structure OhmMeter_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure OhmMeter_R   where val : ℝ     deriving Inhabited

-- Conductivity: S/m
structure SPerM_F      where val : Float deriving Repr, BEq, Inhabited
structure SPerM_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SPerM_R      where val : ℝ     deriving Inhabited

-- Sheet resistance: Ω/□ (ohms per square)
structure OhmPerSquare_F where val : Float deriving Repr, BEq, Inhabited
structure OhmPerSquare_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure OhmPerSquare_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Capacitance
================================================================================================
-/
-- Capacitance: Farads (F)
structure Farad_F      where val : Float deriving Repr, BEq, Inhabited
structure Farad_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Farad_R      where val : ℝ     deriving Inhabited

structure MilliFarad_F where val : Float deriving Repr, BEq, Inhabited
structure MilliFarad_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilliFarad_R where val : ℝ     deriving Inhabited

structure MicroFarad_F where val : Float deriving Repr, BEq, Inhabited
structure MicroFarad_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MicroFarad_R where val : ℝ     deriving Inhabited

structure NanoFarad_F  where val : Float deriving Repr, BEq, Inhabited
structure NanoFarad_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NanoFarad_R  where val : ℝ     deriving Inhabited

structure PicoFarad_F  where val : Float deriving Repr, BEq, Inhabited
structure PicoFarad_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PicoFarad_R  where val : ℝ     deriving Inhabited

-- Permittivity: F/m
structure FPerM_F      where val : Float deriving Repr, BEq, Inhabited
structure FPerM_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FPerM_R      where val : ℝ     deriving Inhabited

-- Relative permittivity (dielectric constant): dimensionless
structure RelPermittivity_F where val : Float deriving Repr, BEq, Inhabited
structure RelPermittivity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RelPermittivity_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Inductance
================================================================================================
-/
-- Inductance: Henries (H)
structure Henry_F      where val : Float deriving Repr, BEq, Inhabited
structure Henry_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Henry_R      where val : ℝ     deriving Inhabited

structure MilliHenry_F where val : Float deriving Repr, BEq, Inhabited
structure MilliHenry_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilliHenry_R where val : ℝ     deriving Inhabited

structure MicroHenry_F where val : Float deriving Repr, BEq, Inhabited
structure MicroHenry_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MicroHenry_R where val : ℝ     deriving Inhabited

structure NanoHenry_F  where val : Float deriving Repr, BEq, Inhabited
structure NanoHenry_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NanoHenry_R  where val : ℝ     deriving Inhabited

-- Permeability: H/m
structure HPerM_F      where val : Float deriving Repr, BEq, Inhabited
structure HPerM_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HPerM_R      where val : ℝ     deriving Inhabited

-- Relative permeability: dimensionless
structure RelPermeability_F where val : Float deriving Repr, BEq, Inhabited
structure RelPermeability_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RelPermeability_R where val : ℝ     deriving Inhabited

-- Mutual inductance: H (same units, different context)
structure MutualInductance_F where val : Float deriving Repr, BEq, Inhabited
structure MutualInductance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MutualInductance_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Magnetic Field
================================================================================================
-/
-- Magnetic flux density: Tesla (T)
structure Tesla_F      where val : Float deriving Repr, BEq, Inhabited
structure Tesla_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Tesla_R      where val : ℝ     deriving Inhabited

structure MilliTesla_F where val : Float deriving Repr, BEq, Inhabited
structure MilliTesla_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilliTesla_R where val : ℝ     deriving Inhabited

structure MicroTesla_F where val : Float deriving Repr, BEq, Inhabited
structure MicroTesla_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MicroTesla_R where val : ℝ     deriving Inhabited

structure NanoTesla_F  where val : Float deriving Repr, BEq, Inhabited
structure NanoTesla_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NanoTesla_R  where val : ℝ     deriving Inhabited

-- Gauss (CGS unit): 1 G = 10⁻⁴ T
structure Gauss_F      where val : Float deriving Repr, BEq, Inhabited
structure Gauss_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Gauss_R      where val : ℝ     deriving Inhabited

-- Magnetic field strength: A/m
structure APerM_F      where val : Float deriving Repr, BEq, Inhabited
structure APerM_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure APerM_R      where val : ℝ     deriving Inhabited

-- Oersted (CGS unit): 1 Oe = (1000/4π) A/m
structure Oersted_F    where val : Float deriving Repr, BEq, Inhabited
structure Oersted_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Oersted_R    where val : ℝ     deriving Inhabited

-- Magnetic flux: Weber (Wb)
structure Weber_F      where val : Float deriving Repr, BEq, Inhabited
structure Weber_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Weber_R      where val : ℝ     deriving Inhabited

structure MilliWeber_F where val : Float deriving Repr, BEq, Inhabited
structure MilliWeber_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilliWeber_R where val : ℝ     deriving Inhabited

structure MicroWeber_F where val : Float deriving Repr, BEq, Inhabited
structure MicroWeber_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MicroWeber_R where val : ℝ     deriving Inhabited

-- Maxwell (CGS unit): 1 Mx = 10⁻⁸ Wb
structure Maxwell_F    where val : Float deriving Repr, BEq, Inhabited
structure Maxwell_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Maxwell_R    where val : ℝ     deriving Inhabited

-- Magnetic vector potential: Wb/m
structure WbPerM_F     where val : Float deriving Repr, BEq, Inhabited
structure WbPerM_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WbPerM_R     where val : ℝ     deriving Inhabited

/--
================================================================================================
   AC Circuit Quantities
================================================================================================
-/
-- Complex impedance using Float pair (real, imaginary)
structure ComplexFloat where
  re : Float
  im : Float
  deriving Repr, BEq, Inhabited

-- Complex impedance using Logos's ComplexFloat type
structure Impedance_C  where val : ComplexFloat deriving Repr, Inhabited


-- Reactance: Ω (same units as resistance but conceptually different)
structure Reactance_F  where val : Float deriving Repr, BEq, Inhabited
structure Reactance_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Reactance_R  where val : ℝ     deriving Inhabited

-- Admittance: S (siemens)
structure Admittance_F where val : Float deriving Repr, BEq, Inhabited
structure Admittance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Admittance_R where val : ℝ     deriving Inhabited

-- Complex admittance
structure Admittance_C where val : ℂ     deriving Inhabited

-- Susceptance: S (imaginary part of admittance)
structure Susceptance_F where val : Float deriving Repr, BEq, Inhabited
structure Susceptance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Susceptance_R where val : ℝ     deriving Inhabited

-- Phase angle: radians or degrees
structure PhaseRad_F   where val : Float deriving Repr, BEq, Inhabited
structure PhaseRad_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PhaseRad_R   where val : ℝ     deriving Inhabited

structure PhaseDeg_F   where val : Float deriving Repr, BEq, Inhabited
structure PhaseDeg_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PhaseDeg_R   where val : ℝ     deriving Inhabited

-- Power factor: dimensionless (0-1)
structure PowerFactor_F where val : Float deriving Repr, BEq, Inhabited
structure PowerFactor_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PowerFactor_R where val : ℝ     deriving Inhabited

-- Quality factor: dimensionless
structure QFactor_F    where val : Float deriving Repr, BEq, Inhabited
structure QFactor_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure QFactor_R    where val : ℝ     deriving Inhabited

/--
================================================================================================
   Electromagnetic Power & Energy
================================================================================================
-/
-- Apparent power: VA (volt-amperes)
structure VoltAmpere_F where val : Float deriving Repr, BEq, Inhabited
structure VoltAmpere_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VoltAmpere_R where val : ℝ     deriving Inhabited

structure KVA_F        where val : Float deriving Repr, BEq, Inhabited
structure KVA_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KVA_R        where val : ℝ     deriving Inhabited

structure MVA_F        where val : Float deriving Repr, BEq, Inhabited
structure MVA_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MVA_R        where val : ℝ     deriving Inhabited

-- Reactive power: VAR (volt-amperes reactive)
structure VAR_F        where val : Float deriving Repr, BEq, Inhabited
structure VAR_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VAR_R        where val : ℝ     deriving Inhabited

structure KVAR_F       where val : Float deriving Repr, BEq, Inhabited
structure KVAR_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KVAR_R       where val : ℝ     deriving Inhabited

structure MVAR_F       where val : Float deriving Repr, BEq, Inhabited
structure MVAR_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MVAR_R       where val : ℝ     deriving Inhabited

-- Energy density: J/m³
structure JPerM3_F     where val : Float deriving Repr, BEq, Inhabited
structure JPerM3_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JPerM3_R     where val : ℝ     deriving Inhabited

-- Poynting vector: W/m²
structure PoyntingVector_F where val : Float deriving Repr, BEq, Inhabited
structure PoyntingVector_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PoyntingVector_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Electromagnetic Material Properties
================================================================================================
-/
-- Electric susceptibility: dimensionless
structure ElecSusceptibility_F where val : Float deriving Repr, BEq, Inhabited
structure ElecSusceptibility_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ElecSusceptibility_R where val : ℝ     deriving Inhabited

-- Magnetic susceptibility: dimensionless
structure MagSusceptibility_F where val : Float deriving Repr, BEq, Inhabited
structure MagSusceptibility_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MagSusceptibility_R where val : ℝ     deriving Inhabited

-- Electric dipole moment: C⋅m
structure ElecDipoleMoment_F where val : Float deriving Repr, BEq, Inhabited
structure ElecDipoleMoment_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ElecDipoleMoment_R where val : ℝ     deriving Inhabited

-- Magnetic dipole moment: A⋅m²
structure MagDipoleMoment_F where val : Float deriving Repr, BEq, Inhabited
structure MagDipoleMoment_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MagDipoleMoment_R where val : ℝ     deriving Inhabited

-- Polarization: C/m²
structure Polarization_F where val : Float deriving Repr, BEq, Inhabited
structure Polarization_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Polarization_R where val : ℝ     deriving Inhabited

-- Magnetization: A/m
structure Magnetization_F where val : Float deriving Repr, BEq, Inhabited
structure Magnetization_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Magnetization_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Mobility and Transport
================================================================================================
-/
-- Charge carrier mobility: m²/(V⋅s)
structure Mobility_F   where val : Float deriving Repr, BEq, Inhabited
structure Mobility_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Mobility_R   where val : ℝ     deriving Inhabited

-- Drift velocity: m/s (using from Mechanics)

-- Hall coefficient: m³/C
structure HallCoeff_F  where val : Float deriving Repr, BEq, Inhabited
structure HallCoeff_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HallCoeff_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Error Propagation & Measurement Helpers
================================================================================================
-/
-- Parametric Uncertainty Tracking with electromagnetic context
structure EMeasured (α : Type) where
  value : α
  uncertainty : α
  frequency : Option Hertz_F := none
  temperature : Option Kelvin_F := none
  magnetic_field : Option Tesla_F := none
  source : Option String := none
  deriving Repr, BEq, Inhabited

-- Measurement with uncertainty for voltage
structure MeasuredVoltage_F where
  value : Volt_F
  uncertainty : Volt_F
  frequency : Option Hertz_F := none
  rms : Bool := false  -- true for RMS, false for peak
  deriving Repr, BEq, Inhabited

-- Measurement with uncertainty for current
structure MeasuredCurrent_F where
  value : Ampere_F
  uncertainty : Ampere_F
  frequency : Option Hertz_F := none
  rms : Bool := false
  deriving Repr, BEq, Inhabited

-- Measurement with uncertainty for impedance
structure MeasuredImpedance_F where
  magnitude : Ohm_F
  phase : PhaseRad_F
  mag_uncertainty : Ohm_F
  phase_uncertainty : PhaseRad_F
  frequency : Hertz_F
  deriving Repr, BEq, Inhabited

-- Error propagation for Ohm's law
def ohmLawWithError_F (v : MeasuredVoltage_F) (i : MeasuredCurrent_F)
    : EMeasured Ohm_F :=
  let r := v.value.val / i.value.val
  let relErrorV := v.uncertainty.val / v.value.val
  let relErrorI := i.uncertainty.val / i.value.val
  let relError := Float.sqrt (relErrorV^2 + relErrorI^2)
  { value := ⟨r⟩
    uncertainty := ⟨r * relError⟩
    source := some "V = IR" }

-- Error propagation for power
def powerWithError_F (v : MeasuredVoltage_F) (i : MeasuredCurrent_F)
    : EMeasured Watt_F :=
  let p := v.value.val * i.value.val
  let relErrorV := v.uncertainty.val / v.value.val
  let relErrorI := i.uncertainty.val / i.value.val
  let relError := Float.sqrt (relErrorV^2 + relErrorI^2)
  { value := ⟨p⟩
    uncertainty := ⟨p * relError⟩
    source := some "P = VI" }

-- Error propagation for capacitive reactance
def capacitiveReactanceWithError_F (c : EMeasured Farad_F) (f : Hertz_F)
    : EMeasured Reactance_F :=
  let xc := 1.0 / (2.0 * pi_F * f.val * c.value.val)
  let relErrorC := c.uncertainty.val / c.value.val
  let relError := relErrorC  -- f assumed exact
  { value := ⟨xc⟩
    uncertainty := ⟨xc * relError⟩
    frequency := some f
    source := some "Xc = 1/(2πfC)" }

-- Error propagation for inductive reactance
def inductiveReactanceWithError_F (l : EMeasured Henry_F) (f : Hertz_F)
    : EMeasured Reactance_F :=
  let xl := 2.0 * pi_F * f.val * l.value.val
  let relErrorL := l.uncertainty.val / l.value.val
  let relError := relErrorL  -- f assumed exact
  { value := ⟨xl⟩
    uncertainty := ⟨xl * relError⟩
    frequency := some f
    source := some "XL = 2πfL" }

/--
================================================================================================
   Validation & Range Checking Helpers
================================================================================================
-/

-- Voltage validation
def isValidVoltage_F (v : Volt_F) : Bool :=
  v.val.abs < 1e9  -- Below gigavolt range for safety

def isSafeVoltage_F (v : Volt_F) : Bool :=
  v.val.abs < 50.0  -- SELV (Safety Extra-Low Voltage)

def isMainsVoltage_F (v : Volt_F) : Bool :=
  (100.0 ≤ v.val && v.val ≤ 127.0) ||  -- Japan/US 110-120V
  (220.0 ≤ v.val && v.val ≤ 240.0)      -- Europe/Asia 220-240V

-- Current validation
def isValidCurrent_F (i : Ampere_F) : Bool :=
  i.val.abs < 1e6  -- Below megaampere

def isSafeCurrent_F (i : MilliAmpere_F) : Bool :=
  i.val.abs < 30.0  -- Below typical GFCI trip threshold

-- Resistance validation
def isValidResistance_F (r : Ohm_F) : Bool :=
  r.val ≥ 0.0  -- Must be non-negative

def isValidResistance_Q (r : Ohm_Q) : Bool :=
  r.val ≥ 0

-- Capacitance validation
def isValidCapacitance_F (c : Farad_F) : Bool :=
  c.val > 0.0  -- Must be positive

def isRealisticCapacitance_F (c : Farad_F) : Bool :=
  c.val > 0.0 && c.val < 10000.0  -- Supercaps go up to ~10kF

-- Inductance validation
def isValidInductance_F (l : Henry_F) : Bool :=
  l.val ≥ 0.0  -- Can be zero for ideal wire

-- Power factor validation
def isValidPowerFactor_F (pf : PowerFactor_F) : Bool :=
  0.0 ≤ pf.val && pf.val ≤ 1.0

def isLeadingPowerFactor_F (pf : PowerFactor_F) (phase : PhaseRad_F) : Bool :=
  isValidPowerFactor_F pf && phase.val > 0.0

def isLaggingPowerFactor_F (pf : PowerFactor_F) (phase : PhaseRad_F) : Bool :=
  isValidPowerFactor_F pf && phase.val < 0.0

-- Frequency validation
def isValidFrequency_F (f : Hertz_F) : Bool :=
  f.val ≥ 0.0

def isDCFrequency_F (f : Hertz_F) : Bool :=
  f.val < 0.001  -- Less than 1 mHz considered DC

def isAudioFrequency_F (f : Hertz_F) : Bool :=
  20.0 ≤ f.val && f.val ≤ 20000.0

def isRadioFrequency_F (f : Hertz_F) : Bool :=
  3000.0 ≤ f.val && f.val ≤ 3e11  -- 3 kHz to 300 GHz

-- Material property validation
def isValidPermittivity_F (eps : RelPermittivity_F) : Bool :=
  eps.val ≥ 1.0  -- Must be ≥ 1 (vacuum)

def isValidPermeability_F (mu : RelPermeability_F) : Bool :=
  mu.val > 0.0  -- Must be positive

/--
================================================================================================
   Unit Conversions
================================================================================================
-/

-- Charge conversions
def coulombToMilliCoulomb_F (c : Coulomb_F) : MilliCoulomb_F :=
  ⟨c.val * 1000.0⟩

def coulombToMicroCoulomb_F (c : Coulomb_F) : MicroCoulomb_F :=
  ⟨c.val * 1e6⟩

def coulombToNanoCoulomb_F (c : Coulomb_F) : NanoCoulomb_F :=
  ⟨c.val * 1e9⟩

def coulombToPicoCoulomb_F (c : Coulomb_F) : PicoCoulomb_F :=
  ⟨c.val * 1e12⟩

-- Current conversions
def ampereToMilliAmpere_F (a : Ampere_F) : MilliAmpere_F :=
  ⟨a.val * 1000.0⟩

def ampereToMicroAmpere_F (a : Ampere_F) : MicroAmpere_F :=
  ⟨a.val * 1e6⟩

def milliAmpereToAmpere_F (ma : MilliAmpere_F) : Ampere_F :=
  ⟨ma.val / 1000.0⟩

-- Voltage conversions
def voltToMilliVolt_F (v : Volt_F) : MilliVolt_F :=
  ⟨v.val * 1000.0⟩

def voltToKiloVolt_F (v : Volt_F) : KiloVolt_F :=
  ⟨v.val / 1000.0⟩

def milliVoltToVolt_F (mv : MilliVolt_F) : Volt_F :=
  ⟨mv.val / 1000.0⟩

-- Resistance conversions
def ohmToKiloOhm_F (r : Ohm_F) : KiloOhm_F :=
  ⟨r.val / 1000.0⟩

def ohmToMegaOhm_F (r : Ohm_F) : MegaOhm_F :=
  ⟨r.val / 1e6⟩

def kiloOhmToOhm_F (kr : KiloOhm_F) : Ohm_F :=
  ⟨kr.val * 1000.0⟩

-- Capacitance conversions
def faradToMicroFarad_F (f : Farad_F) : MicroFarad_F :=
  ⟨f.val * 1e6⟩

def microFaradToNanoFarad_F (uf : MicroFarad_F) : NanoFarad_F :=
  ⟨uf.val * 1000.0⟩

def nanoFaradToPicoFarad_F (nf : NanoFarad_F) : PicoFarad_F :=
  ⟨nf.val * 1000.0⟩

-- Inductance conversions
def henryToMilliHenry_F (h : Henry_F) : MilliHenry_F :=
  ⟨h.val * 1000.0⟩

def milliHenryToMicroHenry_F (mh : MilliHenry_F) : MicroHenry_F :=
  ⟨mh.val * 1000.0⟩

def microHenryToNanoHenry_F (uh : MicroHenry_F) : NanoHenry_F :=
  ⟨uh.val * 1000.0⟩

-- Magnetic field conversions
def teslaToGauss_F (t : Tesla_F) : Gauss_F :=
  ⟨t.val * 10000.0⟩

def gaussToTesla_F (g : Gauss_F) : Tesla_F :=
  ⟨g.val / 10000.0⟩

def teslaToMilliTesla_F (t : Tesla_F) : MilliTesla_F :=
  ⟨t.val * 1000.0⟩

def aPerMToOersted_F (a : APerM_F) : Oersted_F :=
  ⟨a.val * 4.0 * pi_F / 1000.0⟩

def oerstedToAPerM_F (oe : Oersted_F) : APerM_F :=
  ⟨oe.val * 1000.0 / (4.0 * pi_F)⟩

-- Magnetic flux conversions
def weberToMaxwell_F (wb : Weber_F) : Maxwell_F :=
  ⟨wb.val * 1e8⟩

def maxwellToWeber_F (mx : Maxwell_F) : Weber_F :=
  ⟨mx.val / 1e8⟩

-- Phase conversions
def radToDeg_F (r : PhaseRad_F) : PhaseDeg_F :=
  ⟨r.val * 180.0 / pi_F⟩

def degToRad_F (d : PhaseDeg_F) : PhaseRad_F :=
  ⟨d.val * pi_F / 180.0⟩

-- Power conversions
def wattToVoltAmpere_F (w : Watt_F) (pf : PowerFactor_F) : VoltAmpere_F :=
  ⟨w.val / pf.val⟩

def voltAmpereToWatt_F (va : VoltAmpere_F) (pf : PowerFactor_F) : Watt_F :=
  ⟨va.val * pf.val⟩

def voltAmpereToKVA_F (va : VoltAmpere_F) : KVA_F :=
  ⟨va.val / 1000.0⟩

def kvaToMVA_F (kva : KVA_F) : MVA_F :=
  ⟨kva.val / 1000.0⟩

-- Conductance/Resistance conversions
def ohmToSiemens_F (r : Ohm_F) : Siemens_F :=
  if r.val == 0.0 then ⟨0.0⟩ else ⟨1.0 / r.val⟩

def siemensToOhm_F (s : Siemens_F) : Ohm_F :=
  if s.val == 0.0 then ⟨1e308⟩ else ⟨1.0 / s.val⟩  -- Max Float value for infinite resistance

/--
================================================================================================
   Common Electromagnetic Calculations
================================================================================================
-/

-- Coulomb's law force
def coulombForce_F (q1 : Coulomb_F) (q2 : Coulomb_F) (r : Meter_F) : Newton_F :=
  ⟨k_coulomb_F * q1.val * q2.val / (r.val^2)⟩

-- Electric field from point charge
def electricFieldPointCharge_F (q : Coulomb_F) (r : Meter_F) : VPerM_F :=
  ⟨k_coulomb_F * q.val / (r.val^2)⟩

-- Capacitance of parallel plate capacitor
def parallelPlateCapacitance_F (eps_r : RelPermittivity_F) (area : Meter2_F)
    (d : Meter_F) : Farad_F :=
  ⟨epsilon0_F * eps_r.val * area.val / d.val⟩

-- Inductance of solenoid
def solenoidInductance_F (mu_r : RelPermeability_F) (n : Float) -- turns
    (area : Meter2_F) (length : Meter_F) : Henry_F :=
  ⟨mu0_F * mu_r.val * n^2 * area.val / length.val⟩

-- RC time constant
def rcTimeConstant_F (r : Ohm_F) (c : Farad_F) : Second_F :=
  ⟨r.val * c.val⟩

-- RL time constant
def rlTimeConstant_F (l : Henry_F) (r : Ohm_F) : Second_F :=
  ⟨l.val / r.val⟩

-- Resonant frequency
def resonantFrequency_F (l : Henry_F) (c : Farad_F) : Hertz_F :=
  ⟨1.0 / (2.0 * pi_F * Float.sqrt (l.val * c.val))⟩

-- Q factor of RLC circuit
def qFactorRLC_F (r : Ohm_F) (l : Henry_F) (c : Farad_F) : QFactor_F :=
  ⟨(1.0 / r.val) * Float.sqrt (l.val / c.val)⟩

-- Impedance calculations
def impedanceSeries_F (r : Ohm_F) (x : Reactance_F) : Impedance_C :=
  { val := { re := r.val, im := x.val } }

def impedanceMagnitude_F (z : Impedance_C) : Ohm_F :=
  ⟨Float.sqrt (z.val.re^2 + z.val.im^2)⟩


def impedancePhase_F (z : Impedance_C) : PhaseRad_F :=
  ⟨Float.atan2 z.val.im z.val.re⟩


def impedanceParallel_F (z1 : Impedance_C) (z2 : Impedance_C) : Impedance_C :=
  let z1z2_re := z1.val.re * z2.val.re - z1.val.im * z2.val.im
  let z1z2_im := z1.val.re * z2.val.im + z1.val.im * z2.val.re
  let z1pz2_re := z1.val.re + z2.val.re
  let z1pz2_im := z1.val.im + z2.val.im
  let denom := z1pz2_re^2 + z1pz2_im^2
  { val := { re := (z1z2_re * z1pz2_re + z1z2_im * z1pz2_im) / denom,
             im := (z1z2_im * z1pz2_re - z1z2_re * z1pz2_im) / denom } }

-- Capacitive reactance
def capacitiveReactance_F (c : Farad_F) (f : Hertz_F) : Reactance_F :=
  ⟨-1.0 / (2.0 * pi_F * f.val * c.val)⟩  -- Negative for capacitive

-- Inductive reactance
def inductiveReactance_F (l : Henry_F) (f : Hertz_F) : Reactance_F :=
  ⟨2.0 * pi_F * f.val * l.val⟩  -- Positive for inductive

-- Power factor from impedance
def powerFactorFromImpedance_F (z : Impedance_C) : PowerFactor_F :=
  let mag := Float.sqrt (z.val.re^2 + z.val.im^2)
  if mag == 0.0 then ⟨1.0⟩ else ⟨z.val.re.abs / mag⟩

-- Three-phase power
def threePhasePower_F (v_line : Volt_F) (i_line : Ampere_F)
    (pf : PowerFactor_F) : Watt_F :=
  ⟨sqrt3_F * v_line.val * i_line.val * pf.val⟩

-- Magnetic force on moving charge
def lorentzForce_F (q : Coulomb_F) (v : Velocity_F) (b : Tesla_F)
    (angle : PhaseRad_F) : Newton_F :=
  ⟨q.val * v.val * b.val * Float.sin angle.val⟩

-- Magnetic field from current
def magneticFieldFromWire_F (i : Ampere_F) (r : Meter_F) : Tesla_F :=
  ⟨mu0_F * i.val / (2.0 * pi_F * r.val)⟩

-- Faraday's law induced voltage
def inducedVoltage_F (flux_change : Weber_F) (time : Second_F) : Volt_F :=
  ⟨flux_change.val / time.val⟩

-- Motional EMF
def motionalEMF_F (b : Tesla_F) (l : Meter_F) (v : Velocity_F) : Volt_F :=
  ⟨b.val * l.val * v.val⟩

-- Energy stored in capacitor
def capacitorEnergy_F (c : Farad_F) (v : Volt_F) : Joule_F :=
  ⟨0.5 * c.val * v.val^2⟩

-- Energy stored in inductor
def inductorEnergy_F (l : Henry_F) (i : Ampere_F) : Joule_F :=
  ⟨0.5 * l.val * i.val^2⟩

-- Electric field energy density
def electricFieldEnergyDensity_F (e : VPerM_F) (eps_r : RelPermittivity_F)
    : JPerM3_F :=
  ⟨0.5 * epsilon0_F * eps_r.val * e.val^2⟩

-- Magnetic field energy density
def magneticFieldEnergyDensity_F (b : Tesla_F) (mu_r : RelPermeability_F)
    : JPerM3_F :=
  ⟨b.val^2 / (2.0 * mu0_F * mu_r.val)⟩

-- Poynting vector magnitude
def poyntingVectorMagnitude_F (e : VPerM_F) (b : Tesla_F) : PoyntingVector_F :=
  ⟨e.val * b.val / mu0_F⟩

-- Skin depth
def skinDepth_F (rho : OhmMeter_F) (mu_r : RelPermeability_F)
    (f : Hertz_F) : Meter_F :=
  ⟨Float.sqrt (rho.val / (pi_F * mu0_F * mu_r.val * f.val))⟩

-- Antenna calculations
def dipoleRadiationResistance_F (l : Meter_F) (lambda : Meter_F) : Ohm_F :=
  ⟨80.0 * pi_F^2 * (l.val / lambda.val)^2⟩

def antennaGainToEffectiveArea_F (gain : Ratio_F) (lambda : Meter_F) : Meter2_F :=
  ⟨gain.val * lambda.val^2 / (4.0 * pi_F)⟩

-- Transformer calculations
def transformerVoltageRatio_F (n_primary : Float) (n_secondary : Float)
    (v_primary : Volt_F) : Volt_F :=
  ⟨v_primary.val * n_secondary / n_primary⟩

def transformerCurrentRatio_F (n_primary : Float) (n_secondary : Float)
    (i_secondary : Ampere_F) : Ampere_F :=
  ⟨i_secondary.val * n_secondary / n_primary⟩

/--
================================================================================================
   Electromagnetic Wave Calculations
================================================================================================
-/

-- Wave impedance in medium
def waveImpedance_F (mu_r : RelPermeability_F) (eps_r : RelPermittivity_F) : Ohm_F :=
  ⟨Float.sqrt ((mu0_F * mu_r.val) / (epsilon0_F * eps_r.val))⟩

-- Wave velocity in medium
def waveVelocity_F (mu_r : RelPermeability_F) (eps_r : RelPermittivity_F)
    : Velocity_F :=
  ⟨c_F / Float.sqrt (mu_r.val * eps_r.val)⟩

-- Refractive index
def refractiveIndex_F (eps_r : RelPermittivity_F) (mu_r : RelPermeability_F)
    : Ratio_F :=
  ⟨Float.sqrt (eps_r.val * mu_r.val)⟩

-- Wavelength in medium
def wavelengthInMedium_F (lambda_vacuum : Meter_F) (n : Ratio_F) : Meter_F :=
  ⟨lambda_vacuum.val / n.val⟩

-- Critical angle for total internal reflection
def criticalAngle_F (n1 : Ratio_F) (n2 : Ratio_F) : PhaseRad_F :=
  if n1.val > n2.val then
    ⟨Float.asin (n2.val / n1.val)⟩
  else
    ⟨pi_F / 2.0⟩  -- No total internal reflection

/--
================================================================================================
   Semiconductor and Electronics Calculations
================================================================================================
-/

-- Drift velocity
def driftVelocity_F (mu : Mobility_F) (e_field : VPerM_F) : Velocity_F :=
  ⟨mu.val * e_field.val⟩

-- Conductivity from carrier concentration
def semiconductorConductivity_F (n : Float) -- electrons/m³
    (mu_e : Mobility_F) (p : Float) -- holes/m³
    (mu_h : Mobility_F) : SPerM_F :=
  ⟨e_charge_F * (n * mu_e.val + p * mu_h.val)⟩

-- Hall voltage
def hallVoltage_F (b : Tesla_F) (i : Ampere_F) (n : Float) -- carrier density
    (d : Meter_F) : Volt_F :=
  ⟨b.val * i.val / (n * e_charge_F * d.val)⟩

-- Junction capacitance
def junctionCapacitance_F (eps : FPerM_F) (area : Meter2_F)
    (w_depletion : Meter_F) : Farad_F :=
  ⟨eps.val * area.val / w_depletion.val⟩

-- MOSFET transconductance
def mosfetTransconductance_F (mu : Mobility_F) (cox : Farad_F)
    (w : Meter_F) (l : Meter_F) (vgs : Volt_F) (vth : Volt_F) : Siemens_F :=
  ⟨mu.val * cox.val * (w.val / l.val) * (vgs.val - vth.val)⟩

end Units.Physics.Electromagnetism
