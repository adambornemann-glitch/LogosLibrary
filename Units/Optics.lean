-- Optics.lean -- Photometry, radiometry, polarization, optical properties
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import LogosLibrary.Units.Core

open Units.SI
/-
================================================================================
OPTICS PHYSICS UNITS LIBRARY
================================================================================

This module provides type-safe units for optical physics, photonics,
and vision science. Following the triple-type architecture for maximum
flexibility without type conversion friction.

## COVERAGE
- Photometric units (candela, lumen, lux, foot-candle, nit, lambert)
- Radiometric units (irradiance, radiance, spectral power, photon flux)
- Optical properties (transmittance, reflectance, refractive index, absorptance)
- Polarization states (degree of polarization, extinction ratio, retardance)
- Birefringence and optical activity (specific rotation, Verdet constant)
- Lens parameters (diopters, focal length, f-number, numerical aperture)
- Optical system metrics (magnification, field of view, Abbe number)
- Color science (color temperature, chromaticity, CRI, dominant wavelength)
- Interferometry (coherence length/time, visibility, finesse, FSR)
- Laser parameters (power, pulse energy, peak power, beam quality M²)
- Nonlinear optics (nonlinear coefficients, damage threshold)
- Fiber optics (attenuation, chromatic dispersion, V-parameter)
- Vision and display (visual acuity, contrast ratio, PPI, refresh rate)
- Quantum optics basics (photon energy, PAR units)

## USAGE PATTERNS
Float: Experimental measurements, sensor readings, real-time imaging systems,
display calibration, laser power meters, spectrophotometry, optical design
software, beam profiling, polarimetry, colorimetry, photometry measurements,
machine vision, adaptive optics control, optical communications

ℚ: Exact transmission/reflection ratios, lens prescriptions, optical coatings
design, grating equations, precise refractive indices, f-stop sequences,
pixel pitch calculations, exact wavelength ratios, diffraction orders,
interference fringe analysis, optical path differences

ℝ: Wave optics theory, continuous field distributions, Fourier optics,
electromagnetic wave propagation, mode theory, nonlinear optics theory,
quantum optical states, coherence theory, radiative transfer equations,
scattering theory, optical theorem proofs, aberration theory
-/
namespace Units.Optics
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
   Photometric Units (Human Vision Weighted)
================================================================================================
-/
structure Candela_F      where val : Float deriving Repr, BEq, Inhabited  -- cd (SI base)
structure Candela_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Candela_R      where val : ℝ     deriving Inhabited

structure Lumen_F        where val : Float deriving Repr, BEq, Inhabited  -- lm = cd·sr
structure Lumen_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Lumen_R        where val : ℝ     deriving Inhabited

structure Lux_F          where val : Float deriving Repr, BEq, Inhabited  -- lx = lm/m²
structure Lux_Q          where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Lux_R          where val : ℝ     deriving Inhabited

structure FootCandle_F   where val : Float deriving Repr, BEq, Inhabited  -- fc = lm/ft²
structure FootCandle_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FootCandle_R   where val : ℝ     deriving Inhabited

structure Stilb_F        where val : Float deriving Repr, BEq, Inhabited  -- sb = cd/cm²
structure Stilb_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Stilb_R        where val : ℝ     deriving Inhabited

structure Nit_F          where val : Float deriving Repr, BEq, Inhabited  -- nt = cd/m²
structure Nit_Q          where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Nit_R          where val : ℝ     deriving Inhabited

structure Lambert_F      where val : Float deriving Repr, BEq, Inhabited  -- L = cd/cm²/π
structure Lambert_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Lambert_R      where val : ℝ     deriving Inhabited

structure Phot_F         where val : Float deriving Repr, BEq, Inhabited  -- ph = lm/cm²
structure Phot_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Phot_R         where val : ℝ     deriving Inhabited

structure LumenPerWatt_F where val : Float deriving Repr, BEq, Inhabited  -- luminous efficacy
structure LumenPerWatt_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LumenPerWatt_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Radiometric Units (Physical Power/Energy)
================================================================================================
-/
structure WattPerSteradian_F        where val : Float deriving Repr, BEq, Inhabited  -- W/sr
structure WattPerSteradian_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WattPerSteradian_R        where val : ℝ     deriving Inhabited

structure WattPerM2_F               where val : Float deriving Repr, BEq, Inhabited  -- W/m² (irradiance)
structure WattPerM2_Q               where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WattPerM2_R               where val : ℝ     deriving Inhabited

structure WattPerM2Sr_F             where val : Float deriving Repr, BEq, Inhabited  -- W/(m²·sr) (radiance)
structure WattPerM2Sr_Q             where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WattPerM2Sr_R             where val : ℝ     deriving Inhabited

structure WattPerM2Nm_F             where val : Float deriving Repr, BEq, Inhabited  -- spectral irradiance
structure WattPerM2Nm_Q             where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WattPerM2Nm_R             where val : ℝ     deriving Inhabited

structure JoulePerM2_F              where val : Float deriving Repr, BEq, Inhabited  -- radiant exposure
structure JoulePerM2_Q              where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JoulePerM2_R              where val : ℝ     deriving Inhabited

structure PhotonPerSecond_F         where val : Float deriving Repr, BEq, Inhabited  -- photon flux
structure PhotonPerSecond_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PhotonPerSecond_R         where val : ℝ     deriving Inhabited

structure PhotonPerM2S_F            where val : Float deriving Repr, BEq, Inhabited  -- photon flux density
structure PhotonPerM2S_Q            where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PhotonPerM2S_R            where val : ℝ     deriving Inhabited

structure PhotonEnergy_eV_F       where val : Float deriving Repr, BEq, Inhabited  -- eV (electron-volts)
structure PhotonEnergy_eV_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited  -- eV
structure PhotonEnergy_eV_R       where val : ℝ     deriving Inhabited  -- eV

structure MicroEinsteinPerM2S_F     where val : Float deriving Repr, BEq, Inhabited  -- μmol/(m²·s) PAR
structure MicroEinsteinPerM2S_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MicroEinsteinPerM2S_R     where val : ℝ     deriving Inhabited

structure WavelengthNM_F           where val : Float deriving Repr, BEq, Inhabited
structure WavelengthNM_Q           where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WavelengthNM_R           where val : ℝ     deriving Inhabited

structure WavelengthAng_F           where val : Float deriving Repr, BEq, Inhabited
structure WavelengthAng_Q           where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WavelengthAng_R           where val : ℝ     deriving Inhabited
/--
================================================================================================
   Optical Properties (Dimensionless ratios/fractions)
================================================================================================
-/
structure Transmittance_F    where val : Float deriving Repr, BEq, Inhabited  -- T (0-1)
structure Transmittance_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Transmittance_R    where val : ℝ     deriving Inhabited

structure Reflectance_F      where val : Float deriving Repr, BEq, Inhabited  -- R (0-1)
structure Reflectance_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Reflectance_R      where val : ℝ     deriving Inhabited

structure RefractiveIndex_F      where val : Float deriving Repr, BEq, Inhabited  -- ReI (0-1)
structure RefractiveIndex_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RefractiveIndex_R      where val : ℝ     deriving Inhabited

structure Absorptance_F      where val : Float deriving Repr, BEq, Inhabited  -- A (0-1)
structure Absorptance_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Absorptance_R      where val : ℝ     deriving Inhabited

structure Emissivity_F       where val : Float deriving Repr, BEq, Inhabited  -- ε (0-1)
structure Emissivity_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Emissivity_R       where val : ℝ     deriving Inhabited

structure OpticalDensity_F   where val : Float deriving Repr, BEq, Inhabited  -- OD = -log₁₀(T)
structure OpticalDensity_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure OpticalDensity_R   where val : ℝ     deriving Inhabited

structure Albedo_F           where val : Float deriving Repr, BEq, Inhabited  -- planetary reflectance
structure Albedo_Q           where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Albedo_R           where val : ℝ     deriving Inhabited

/--
================================================================================================
   Polarization & Birefringence
================================================================================================
-/
structure Birefringence_F           where val : Float deriving Repr, BEq, Inhabited
structure Birefringence_Q           where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Birefringence_R           where val : ℝ     deriving Inhabited

structure DegreeOfPolarization_F    where val : Float deriving Repr, BEq, Inhabited  -- DOP (0-1)
structure DegreeOfPolarization_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DegreeOfPolarization_R    where val : ℝ     deriving Inhabited

structure ExtinctionRatio_F         where val : Float deriving Repr, BEq, Inhabited  -- polarizer quality
structure ExtinctionRatio_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ExtinctionRatio_R         where val : ℝ     deriving Inhabited

structure Retardance_F              where val : Float deriving Repr, BEq, Inhabited  -- radians
structure Retardance_Q              where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Retardance_R              where val : ℝ     deriving Inhabited

structure RetardanceNM_F            where val : Float deriving Repr, BEq, Inhabited  -- optical path diff
structure RetardanceNM_Q            where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RetardanceNM_R            where val : ℝ     deriving Inhabited

structure SpecificRotation_F        where val : Float deriving Repr, BEq, Inhabited  -- deg·dm⁻¹·(g/mL)⁻¹
structure SpecificRotation_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpecificRotation_R        where val : ℝ     deriving Inhabited

structure OpticalRotation_F         where val : Float deriving Repr, BEq, Inhabited  -- degrees
structure OpticalRotation_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure OpticalRotation_R         where val : ℝ     deriving Inhabited

structure VerdetConstant_F          where val : Float deriving Repr, BEq, Inhabited  -- rad/(T·m)
structure VerdetConstant_Q          where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VerdetConstant_R          where val : ℝ     deriving Inhabited

structure CircularDichroism_F       where val : Float deriving Repr, BEq, Inhabited  -- mdeg
structure CircularDichroism_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CircularDichroism_R       where val : ℝ     deriving Inhabited

structure Ellipticity_F             where val : Float deriving Repr, BEq, Inhabited  -- mdeg
structure Ellipticity_Q             where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Ellipticity_R             where val : ℝ     deriving Inhabited

/--
================================================================================================
   Lens & Optical System Parameters
================================================================================================
-/
structure Diopter_F          where val : Float deriving Repr, BEq, Inhabited  -- m⁻¹ (optical power)
structure Diopter_Q          where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Diopter_R          where val : ℝ     deriving Inhabited

structure FocalLength_F      where val : Float deriving Repr, BEq, Inhabited  -- mm typical
structure FocalLength_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FocalLength_R      where val : ℝ     deriving Inhabited

structure FNumber_F          where val : Float deriving Repr, BEq, Inhabited  -- f-stop
structure FNumber_Q          where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FNumber_R          where val : ℝ     deriving Inhabited

structure NumericalAperture_F where val : Float deriving Repr, BEq, Inhabited  -- NA
structure NumericalAperture_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NumericalAperture_R where val : ℝ     deriving Inhabited

structure Magnification_F     where val : Float deriving Repr, BEq, Inhabited  -- dimensionless
structure Magnification_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Magnification_R     where val : ℝ     deriving Inhabited

structure AngularMagnification_F where val : Float deriving Repr, BEq, Inhabited
structure AngularMagnification_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AngularMagnification_R where val : ℝ     deriving Inhabited

structure FieldOfView_F       where val : Float deriving Repr, BEq, Inhabited  -- degrees or radians
structure FieldOfView_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FieldOfView_R       where val : ℝ     deriving Inhabited

structure AbbeNumber_F        where val : Float deriving Repr, BEq, Inhabited  -- V_d dispersion
structure AbbeNumber_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AbbeNumber_R        where val : ℝ     deriving Inhabited


/--
================================================================================================
   Color & Spectral Quantities
================================================================================================
-/
structure ColorTemperature_F  where val : Float deriving Repr, BEq, Inhabited  -- Kelvin
structure ColorTemperature_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ColorTemperature_R  where val : ℝ     deriving Inhabited

structure ChromaticityX_F     where val : Float deriving Repr, BEq, Inhabited  -- CIE x (0-1)
structure ChromaticityX_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ChromaticityX_R     where val : ℝ     deriving Inhabited

structure ChromaticityY_F     where val : Float deriving Repr, BEq, Inhabited  -- CIE y (0-1)
structure ChromaticityY_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ChromaticityY_R     where val : ℝ     deriving Inhabited

structure ColorRenderingIndex_F where val : Float deriving Repr, BEq, Inhabited  -- CRI (0-100)
structure ColorRenderingIndex_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ColorRenderingIndex_R where val : ℝ     deriving Inhabited

structure DominantWavelength_F  where val : Float deriving Repr, BEq, Inhabited  -- nm
structure DominantWavelength_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DominantWavelength_R  where val : ℝ     deriving Inhabited

structure SpectralPurity_F      where val : Float deriving Repr, BEq, Inhabited  -- (0-1)
structure SpectralPurity_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpectralPurity_R      where val : ℝ     deriving Inhabited

/--
================================================================================================
   Interferometry & Coherence
================================================================================================
-/
structure CoherenceLength_F     where val : Float deriving Repr, BEq, Inhabited  -- μm typical
structure CoherenceLength_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CoherenceLength_R     where val : ℝ     deriving Inhabited

structure CoherenceTime_F       where val : Float deriving Repr, BEq, Inhabited  -- fs to ps
structure CoherenceTime_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CoherenceTime_R       where val : ℝ     deriving Inhabited

structure VisibilityContrast_F  where val : Float deriving Repr, BEq, Inhabited  -- V (0-1)
structure VisibilityContrast_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VisibilityContrast_R  where val : ℝ     deriving Inhabited

structure Finesse_F             where val : Float deriving Repr, BEq, Inhabited  -- cavity quality
structure Finesse_Q             where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Finesse_R             where val : ℝ     deriving Inhabited

structure FreeSpectralRange_F   where val : Float deriving Repr, BEq, Inhabited  -- GHz typical
structure FreeSpectralRange_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FreeSpectralRange_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Laser & Nonlinear Optics
================================================================================================
-/
structure LaserPower_F          where val : Float deriving Repr, BEq, Inhabited  -- W
structure LaserPower_Q          where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LaserPower_R          where val : ℝ     deriving Inhabited

structure PulseEnergy_F         where val : Float deriving Repr, BEq, Inhabited  -- mJ, μJ, nJ
structure PulseEnergy_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PulseEnergy_R         where val : ℝ     deriving Inhabited

structure PeakPower_F           where val : Float deriving Repr, BEq, Inhabited  -- MW, GW
structure PeakPower_Q           where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PeakPower_R           where val : ℝ     deriving Inhabited

structure PulseDuration_F       where val : Float deriving Repr, BEq, Inhabited  -- fs, ps, ns
structure PulseDuration_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PulseDuration_R       where val : ℝ     deriving Inhabited

structure RepetitionRate_F      where val : Float deriving Repr, BEq, Inhabited  -- Hz, kHz, MHz
structure RepetitionRate_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RepetitionRate_R      where val : ℝ     deriving Inhabited

structure BeamDiameter_F        where val : Float deriving Repr, BEq, Inhabited  -- mm
structure BeamDiameter_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BeamDiameter_R        where val : ℝ     deriving Inhabited

structure BeamDivergence_F      where val : Float deriving Repr, BEq, Inhabited  -- mrad
structure BeamDivergence_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BeamDivergence_R      where val : ℝ     deriving Inhabited

structure BeamQualityM2_F       where val : Float deriving Repr, BEq, Inhabited  -- M² factor
structure BeamQualityM2_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BeamQualityM2_R       where val : ℝ     deriving Inhabited

structure NonlinearCoeff_F      where val : Float deriving Repr, BEq, Inhabited  -- pm/V
structure NonlinearCoeff_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NonlinearCoeff_R      where val : ℝ     deriving Inhabited

structure DamageThreshold_F     where val : Float deriving Repr, BEq, Inhabited  -- J/cm²
structure DamageThreshold_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DamageThreshold_R     where val : ℝ     deriving Inhabited

/--
================================================================================================
   Fiber Optics
================================================================================================
-/
structure AttenuationdBPerKm_F  where val : Float deriving Repr, BEq, Inhabited
structure AttenuationdBPerKm_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AttenuationdBPerKm_R  where val : ℝ     deriving Inhabited

structure ChromaticDispersion_F where val : Float deriving Repr, BEq, Inhabited  -- ps/(nm·km)
structure ChromaticDispersion_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ChromaticDispersion_R where val : ℝ     deriving Inhabited

structure ModeBirefringence_F   where val : Float deriving Repr, BEq, Inhabited
structure ModeBirefringence_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ModeBirefringence_R   where val : ℝ     deriving Inhabited

structure CouplingRatio_F       where val : Float deriving Repr, BEq, Inhabited  -- (0-1)
structure CouplingRatio_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CouplingRatio_R       where val : ℝ     deriving Inhabited

/--
================================================================================================
   Vision & Display
================================================================================================
-/
structure VisualAcuity_F        where val : Float deriving Repr, BEq, Inhabited  -- 20/20 = 1.0
structure VisualAcuity_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VisualAcuity_R        where val : ℝ     deriving Inhabited

structure ContrastRatio_F       where val : Float deriving Repr, BEq, Inhabited  -- display contrast
structure ContrastRatio_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ContrastRatio_R       where val : ℝ     deriving Inhabited

structure PixelPitch_F          where val : Float deriving Repr, BEq, Inhabited  -- mm
structure PixelPitch_Q          where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PixelPitch_R          where val : ℝ     deriving Inhabited

structure PixelsPerInch_F       where val : Float deriving Repr, BEq, Inhabited  -- PPI/DPI
structure PixelsPerInch_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PixelsPerInch_R       where val : ℝ     deriving Inhabited

structure RefreshRate_F         where val : Float deriving Repr, BEq, Inhabited  -- Hz
structure RefreshRate_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RefreshRate_R         where val : ℝ     deriving Inhabited

/--
================================================================================================
   Measurement Uncertainty for Common Optical Quantities
================================================================================================
-/
structure TransmittanceWithError_F where
  value : Transmittance_F
  uncertainty : Transmittance_F
  deriving Repr, BEq, Inhabited

structure ReflectanceWithError_F where
  value : Reflectance_F
  uncertainty : Reflectance_F
  deriving Repr, BEq, Inhabited

structure RefractiveIndexWithError_F where
  value : RefractiveIndex_F
  uncertainty : RefractiveIndex_F
  deriving Repr, BEq, Inhabited

structure FocalLengthWithError_F where
  value : FocalLength_F
  uncertainty : FocalLength_F
  deriving Repr, BEq, Inhabited

/--
================================================================================================
   Helper Functions
================================================================================================
-/

-- Constructor with range check for transmittance (0-1)
def mkTransmittance_F (v : Float) : Option Transmittance_F :=
  if 0.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

def mkTransmittance_Q (v : ℚ) : Option Transmittance_Q :=
  if 0.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

noncomputable def mkTransmittance_R (v : ℝ) : Option Transmittance_R :=
  if 0.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

-- Constructor with range check for reflectance (0-1)
def mkReflectance_F (v : Float) : Option Reflectance_F :=
  if 0.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

def mkReflectance_Q (v : ℚ) : Option Reflectance_Q :=
  if 0.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

noncomputable def mkReflectance_R (v : ℝ) : Option Reflectance_R :=
  if 0.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

-- Constructor for CRI (0-100)
def mkCRI_F (v : Float) : Option ColorRenderingIndex_F :=
  if 0.0 ≤ v && v ≤ 100.0 then some ⟨v⟩ else none

def mkCRI_Q (v : ℚ) : Option ColorRenderingIndex_Q :=
  if 0.0 ≤ v && v ≤ 100.0 then some ⟨v⟩ else none

noncomputable def mkCRI_R (v : ℝ) : Option ColorRenderingIndex_R :=
  if 0.0 ≤ v && v ≤ 100.0 then some ⟨v⟩ else none

/--
================================================================================================
   Validation & Range Checking Helpers
================================================================================================
-/

-- Refractive index validation (n ≥ 1 for normal materials, n < 1 for metamaterials)
def isValidRefractiveIndex_F (n : RefractiveIndex_F) : Bool :=
  n.val > 0.0  -- Must be positive

def isNormalRefractiveIndex_F (n : RefractiveIndex_F) : Bool :=
  n.val ≥ 1.0  -- Normal materials

def isMetamaterialIndex_F (n : RefractiveIndex_F) : Bool :=
  0.0 < n.val && n.val < 1.0

def isNormalMaterial_F (n : RefractiveIndex_F) : Bool :=
  n.val ≥ 1.0  -- Normal materials

def isMetamaterial_F (n : RefractiveIndex_F) : Bool :=
  0.0 < n.val && n.val < 1.0

-- Wavelength validation (must be positive)
def isValidWavelength_F (lambda : WavelengthNM_F) : Bool :=
  lambda.val > 0.0

-- Visible spectrum check (roughly 380-750 nm)
def isVisibleLight_F (lambda : WavelengthNM_F) : Bool :=
  380.0 ≤ lambda.val && lambda.val ≤ 750.0

def lightColor_F (lambda : WavelengthNM_F) : String :=
  if lambda.val < 380.0 then "ultraviolet"
  else if lambda.val < 450.0 then "violet"
  else if lambda.val < 485.0 then "blue"
  else if lambda.val < 500.0 then "cyan"
  else if lambda.val < 565.0 then "green"
  else if lambda.val < 590.0 then "yellow"
  else if lambda.val < 625.0 then "orange"
  else if lambda.val < 750.0 then "red"
  else "infrared"

-- Polarization validation (0 ≤ degree ≤ 1)
def isValidPolarizationDegree_F (p : DegreeOfPolarization_F) : Bool :=
  0.0 ≤ p.val && p.val ≤ 1.0

-- Transmittance/Reflectance validation (0 ≤ T,R ≤ 1)
def isValidTransmittance_F (T : Transmittance_F) : Bool :=
  0.0 ≤ T.val && T.val ≤ 1.0

def isValidReflectance_F (R : Reflectance_F) : Bool :=
  0.0 ≤ R.val && R.val ≤ 1.0

-- Absorption coefficient validation (must be non-negative)
def isValidAbsorptionCoeff_F (alpha : Absorptance_F) : Bool :=
  alpha.val ≥ 0.0

-- Finesse validation (Q > 1 for resonators)
def isValidFinesse_F (F : Finesse_F) : Bool :=
  F.val > 0.0

-- Numerical aperture validation (0 < NA ≤ n_medium)
def isValidNumericalAperture_F (NA : NumericalAperture_F) (n_medium : RefractiveIndex_F) : Bool :=
  0.0 < NA.val && NA.val ≤ n_medium.val

-- Coherence length validation
def isValidCoherenceLength_F (lc : CoherenceLength_F) : Bool :=
  lc.val > 0.0

-- Optical power validation (diopters can be positive or negative)
def isConvergingLens_F (D : Diopter_F) : Bool :=
  D.val > 0.0

def isDivergingLens_F (D : Diopter_F) : Bool :=
  D.val < 0.0

-- Diffraction order validation
def isValidDiffractionOrder (_ : DiffractionOrder) : Bool :=
  true  -- All integers are valid

-- Photon energy validation
def isValidPhotonEnergy_F (E : PhotonEnergy_eV_F) : Bool :=
  (E.val > 0.0)
--Optical property validations (all must be 0-1)

def isValidAbsorptance_F (a : Absorptance_F) : Bool :=
  0.0 ≤ a.val && a.val ≤ 1.0

def isValidEmissivity_F (e : Emissivity_F) : Bool :=
  0.0 ≤ e.val && e.val ≤ 1.0

def isValidAlbedo_F (a : Albedo_F) : Bool :=
  0.0 ≤ a.val && a.val ≤ 1.0

-- Conservation check: T + R + A = 1
def isEnergyConserved_F (T : Transmittance_F) (R : Reflectance_F) (A : Absorptance_F) : Bool :=
  (T.val + R.val + A.val - 1.0).abs < 0.001  -- Within 0.1% tolerance

-- Polarization validations
def isValidDegreeOfPolarization_F (dop : DegreeOfPolarization_F) : Bool :=
  0.0 ≤ dop.val && dop.val ≤ 1.0

def isFullyPolarized_F (dop : DegreeOfPolarization_F) : Bool :=
  (dop.val - 1.0).abs < 0.001

def isUnpolarized_F (dop : DegreeOfPolarization_F) : Bool :=
  dop.val < 0.001

-- Extinction ratio validation (should be > 1, often >> 1)
def isValidExtinctionRatio_F (er : ExtinctionRatio_F) : Bool :=
  er.val ≥ 1.0

def isHighQualityPolarizer_F (er : ExtinctionRatio_F) : Bool :=
  er.val > 1000.0  -- > 30 dB



-- F-number validation
def isValidFNumber_F (f : FNumber_F) : Bool :=
  f.val > 0.0

def isFastLens_F (f : FNumber_F) : Bool :=
  f.val < 2.0  -- f/2 or faster

-- Magnification checks
def isMagnifying_F (m : Magnification_F) : Bool :=
  m.val.abs > 1.0

def isDemagnifying_F (m : Magnification_F) : Bool :=
  m.val.abs < 1.0

def isInverted_F (m : Magnification_F) : Bool :=
  m.val < 0.0

-- Color temperature validation
def isValidColorTemperature_F (ct : ColorTemperature_F) : Bool :=
  ct.val > 0.0

def isDaylightColorTemp_F (ct : ColorTemperature_F) : Bool :=
  5000.0 ≤ ct.val && ct.val ≤ 6500.0

-- Chromaticity validation (must sum to ≤ 1)
def isValidChromaticity_F (x : ChromaticityX_F) (y : ChromaticityY_F) : Bool :=
  0.0 ≤ x.val && x.val ≤ 1.0 &&
  0.0 ≤ y.val && y.val ≤ 1.0 &&
  x.val + y.val ≤ 1.0

def isHighFinesseCavity_F (f : Finesse_F) : Bool :=
  f.val > 100.0

-- Laser beam quality validation
def isValidBeamQuality_F (m2 : BeamQualityM2_F) : Bool :=
  m2.val ≥ 1.0  -- Cannot be better than Gaussian

def isNearGaussianBeam_F (m2 : BeamQualityM2_F) : Bool :=
  m2.val < 1.5

-- Fiber attenuation check
def isLowLossFiber_F (att : AttenuationdBPerKm_F) : Bool :=
  att.val < 0.5  -- Typical for good telecom fiber at 1550nm

-- Visual acuity validation
def isNormalVision_F (va : VisualAcuity_F) : Bool :=
  va.val ≥ 1.0  -- 20/20 or better

/--
================================================================================================
   Unit Conversions with Error Propagation
================================================================================================
-/

-- Import note: These assume WavelengthNM_F, Joule_F, etc. from Monolith.lean

-- Optical density conversions
def transmittanceToOpticalDensity_F (T : Transmittance_F) : Option OpticalDensity_F :=
  if T.val > 0.0 then
    some ⟨-Float.log T.val / Float.log 10.0⟩
  else
    none  -- OD = ∞ for T = 0

def opticalDensityToTransmittance_F (od : OpticalDensity_F) : Transmittance_F :=
  ⟨10.0 ^ (-od.val)⟩

-- Luminous efficacy (typical photopic maximum ~683 lm/W at 555nm)
def photopicEfficacy_F : LumenPerWatt_F := ⟨683.0⟩

-- Lux to foot-candle
def luxToFootCandle_F (lx : Lux_F) : FootCandle_F :=
  ⟨lx.val * 0.0929⟩

def footCandleToLux_F (fc : FootCandle_F) : Lux_F :=
  ⟨fc.val / 0.0929⟩

-- Candela/m² to Lambert
def nitToLambert_F (nt : Nit_F) : Lambert_F :=
  ⟨nt.val / 3183.1⟩  -- 1 Lambert = π × 10⁴ / π cd/m²

-- Stilb to Nit
def stilbToNit_F (sb : Stilb_F) : Nit_F :=
  ⟨sb.val * 10000.0⟩  -- 1 sb = 10⁴ cd/m²

-- Focal length to diopter
def focalLengthToDiopter_F (f_mm : FocalLength_F) : Diopter_F :=
  ⟨1000.0 / f_mm.val⟩  -- Convert mm to m and invert

def diopterToFocalLength_F (D : Diopter_F) : FocalLength_F :=
  ⟨1000.0 / D.val⟩  -- Result in mm

-- With error propagation
def transmittanceWithError_F (measured : TransmittanceWithError_F)
    : Option OpticalDensity_F :=
  if measured.value.val > 0.0 then
    let od := -Float.log measured.value.val / Float.log 10.0
    -- Error: δ(OD) = δT / (T × ln(10))
    let _ /-odError-/ := measured.uncertainty.val / (measured.value.val * Float.log 10.0)
    some ⟨od⟩  -- Would need OpticalDensityWithError type
  else
    none

def refractiveIndexWithError_F (n : RefractiveIndexWithError_F)
    (_ /-angle-/ : Float) : Float :=
  -- Snell's law error propagation would go here
  let criticalAngle := Float.asin (1.0 / n.value.val)
  let _ /-errorAngle-/ := n.uncertainty.val / (n.value.val^2 * Float.sqrt (1.0 - (1.0/n.value.val)^2))
  criticalAngle

/--
================================================================================================
   Common Optics Calculations
================================================================================================
-/

-- Fresnel equations for normal incidence
def fresnelReflectanceNormal_F (n1 n2 : RefractiveIndex_F) : Reflectance_F :=
  let r := (n1.val - n2.val) / (n1.val + n2.val)
  ⟨r * r⟩

-- Anti-reflection coating condition (quarter-wave)
def idealARCoatingIndex_F (n_substrate : RefractiveIndex_F)
    (n_medium : RefractiveIndex_F) : RefractiveIndex_F :=
  ⟨Float.sqrt (n_substrate.val * n_medium.val)⟩

-- Numerical aperture from refractive indices
def numericalApertureFromIndices_F (n_core n_cladding : RefractiveIndex_F)
    : NumericalAperture_F :=
  ⟨Float.sqrt (n_core.val^2 - n_cladding.val^2)⟩

-- F-number from focal length and aperture diameter
def fNumberFromDiameter_F (focal_mm : FocalLength_F) (diameter_mm : Float) : FNumber_F :=
  ⟨focal_mm.val / diameter_mm⟩

-- Field of view from focal length and sensor size
def fieldOfView_F (sensorSize_mm : Float) (focal_mm : FocalLength_F) : FieldOfView_F :=
  ⟨2.0 * Float.atan (sensorSize_mm / (2.0 * focal_mm.val)) * 180.0 / pi_F⟩  -- In degrees

-- Abbe number from refractive indices
def abbeNumber_F (n_d n_F n_C : RefractiveIndex_F) : AbbeNumber_F :=
  ⟨(n_d.val - 1.0) / (n_F.val - n_C.val)⟩  -- Fraunhofer lines

-- Depth of focus
def depthOfFocus_F (f_number : FNumber_F) (coc_mm : Float) : Float :=
  2.0 * f_number.val * coc_mm  -- Circle of confusion

-- Polarization calculations
def malusLaw_F (I0 : Lux_F) (angle_rad : Float) : Lux_F :=
  ⟨I0.val * (Float.cos angle_rad)^2⟩

-- Extinction ratio to transmission
def extinctionToTransmission_F (er : ExtinctionRatio_F) : Transmittance_F :=
  ⟨1.0 / er.val⟩

-- Visibility/Contrast calculations
def michelsonContrast_F (I_max I_min : Lux_F) : VisibilityContrast_F :=
  if I_max.val + I_min.val > 0.0 then
    ⟨(I_max.val - I_min.val) / (I_max.val + I_min.val)⟩
  else
    ⟨0.0⟩

-- Simple lens equation
def gaussianLensEquation_F (object_dist_mm image_dist_mm : Float) : FocalLength_F :=
  ⟨1.0 / (1.0 / object_dist_mm + 1.0 / image_dist_mm)⟩

-- Magnification from object and image distances
def magnificationFromDistances_F (image_dist object_dist : Float) : Magnification_F :=
  ⟨-image_dist / object_dist⟩  -- Negative for real image

-- Resolution calculations
def pixelPitchFromPPI_F (ppi : PixelsPerInch_F) : PixelPitch_F :=
  ⟨25.4 / ppi.val⟩  -- Convert inch to mm

def ppiFromPixelPitch_F (pitch : PixelPitch_F) : PixelsPerInch_F :=
  ⟨25.4 / pitch.val⟩

-- Display gamma correction (simplified)
def gammaCorrection_F (input : Float) (gamma : Float) : Float :=
  input ^ (1.0 / gamma)

-- Laser calculations
def averagePowerFromPulse_F (energy : PulseEnergy_F) (rate : RepetitionRate_F)
    : LaserPower_F :=
  ⟨energy.val * rate.val⟩

def peakPowerFromPulse_F (energy : PulseEnergy_F) (duration : PulseDuration_F)
    : PeakPower_F :=
  ⟨energy.val / duration.val⟩

-- Beam parameter product (BPP)
def beamParameterProduct_F (waist_mm : Float) (divergence : BeamDivergence_F) : Float :=
  waist_mm * divergence.val  -- In mm·mrad

-- Fiber V-parameter (determines number of modes)
def fiberVParameter_F (core_radius_um : Float) (NA : NumericalAperture_F)
    (wavelength_nm : Float) : Float :=
  2.0 * pi_F * core_radius_um * NA.val / wavelength_nm

def isSingleMode_F (v_param : Float) : Bool :=
  v_param < 2.405  -- First zero of J₀ Bessel function

-- Chromatic dispersion delay
def dispersionDelay_F (dispersion : ChromaticDispersion_F)
    (length_km : Float) (spectral_width_nm : Float) : Float :=
  dispersion.val * length_km * spectral_width_nm  -- In ps


end Units.Optics
