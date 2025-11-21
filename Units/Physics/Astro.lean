-- Astro.lean        -- Astronomy, astrophysics, cosmology units
import LogosLibrary.Units.Core.SI
import LogosLibrary.Units.Physics.Radiation
import LogosLibrary.Units.Physics.Optics
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

namespace Units.Physics.Astro

open Units.Standard Units.Physics.Radiation Units.Physics.Optics

/-
================================================================================
ASTRONOMY AND ASTROPHYSICS UNITS LIBRARY
================================================================================

This module provides type-safe units for astronomy, astrophysics, cosmology,
stellar physics, galactic dynamics, and observational astronomy.
Following the triple-type architecture for maximum flexibility without type
conversion friction.

## COVERAGE
- Astronomical distances (parsec, AU, light-year, redshift distances)
- Stellar units (solar mass, radius, luminosity, temperature)
- Planetary units (Jupiter/Earth masses and radii)
- Time scales (Gyr, Myr, kyr, Julian years)
- Luminosity and flux (absolute/apparent magnitude, Jansky, erg/s)
- Angular measurements (arcsec, mas, μas)
- Cosmological parameters (Hubble constant, density parameters)
- Galactic units (kpc, Mpc, Gpc, galaxy masses)
- Radio astronomy (Jansky, antenna temperature, brightness)
- Spectroscopy (redshift, velocity dispersion, equivalent width)
- X-ray astronomy (counts/s, keV flux)
- Gravitational astronomy (strain, chirp mass)

## USAGE PATTERNS
Float: Observational data, telescope measurements, photometry, astrometry,
orbit calculations, ephemerides, real-time tracking, survey data processing,
CCD reductions, adaptive optics, interferometry

ℚ: Exact unit conversions, calendar calculations, coordinate transformations,
proper motion calculations, parallax ratios, magnitude systems,
orbital period ratios, resonances

ℝ: Theoretical models, cosmological solutions, stellar structure equations,
general relativity in strong fields, black hole thermodynamics,
N-body problems, galactic dynamics, dark matter profiles
-/

set_option autoImplicit false
set_option linter.unusedVariables false

/--
================================================================================================
   Mathematical and Physical Constants for Astronomy
================================================================================================
-/
def pi_F : Float := 3.14159265358979323846
def c_light_F : Float := 2.99792458e8  -- Speed of light (m/s)
def G_F : Float := 6.67430e-11  -- Gravitational constant (m³/(kg·s²))
def h_planck_F : Float := 6.62607015e-34  -- Planck constant (J·s)
def k_B_F : Float := 1.380649e-23  -- Boltzmann constant (J/K)
def stefan_boltzmann_F : Float := 5.670374419e-8  -- Stefan-Boltzmann (W/(m²·K⁴))

-- Astronomical constants
def AU_meters_F : Float := 1.495978707e11  -- Astronomical unit (m)
def pc_meters_F : Float := 3.0857e16  -- Parsec (m)
def ly_meters_F : Float := 9.4607e15  -- Light-year (m)
def solar_mass_F : Float := 1.98847e30  -- Solar mass (kg)
def solar_radius_F : Float := 6.96342e8  -- Solar radius (m)
def solar_luminosity_F : Float := 3.828e26  -- Solar luminosity (W)
def earth_mass_F : Float := 5.97237e24  -- Earth mass (kg)
def earth_radius_F : Float := 6.371e6  -- Earth radius (m)
def jupiter_mass_F : Float := 1.89819e27  -- Jupiter mass (kg)
def jupiter_radius_F : Float := 6.9911e7  -- Jupiter radius (m)
def H0_nominal_F : Float := 70.0  -- Nominal Hubble constant (km/s/Mpc)

/--
================================================================================================
   Astronomical Distances
================================================================================================
-/
-- Parsec and variants
structure Parsec_F     where val : Float deriving Repr, BEq, Inhabited
structure Parsec_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Parsec_R     where val : ℝ     deriving Inhabited

structure Kiloparsec_F where val : Float deriving Repr, BEq, Inhabited
structure Kiloparsec_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kiloparsec_R where val : ℝ     deriving Inhabited

structure Megaparsec_F where val : Float deriving Repr, BEq, Inhabited
structure Megaparsec_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Megaparsec_R where val : ℝ     deriving Inhabited

structure Gigaparsec_F where val : Float deriving Repr, BEq, Inhabited
structure Gigaparsec_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Gigaparsec_R where val : ℝ     deriving Inhabited

-- Astronomical Unit
structure AU_F         where val : Float deriving Repr, BEq, Inhabited
structure AU_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AU_R         where val : ℝ     deriving Inhabited

-- Light-year
structure LightYear_F  where val : Float deriving Repr, BEq, Inhabited
structure LightYear_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LightYear_R  where val : ℝ     deriving Inhabited

-- Light-time units
structure LightSecond_F where val : Float deriving Repr, BEq, Inhabited
structure LightMinute_F where val : Float deriving Repr, BEq, Inhabited
structure LightHour_F  where val : Float deriving Repr, BEq, Inhabited
structure LightDay_F   where val : Float deriving Repr, BEq, Inhabited

/--
================================================================================================
   Astronomical Time Scales
================================================================================================
-/
-- Gigayear (billion years)
structure Gigayear_F   where val : Float deriving Repr, BEq, Inhabited
structure Gigayear_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Gigayear_R   where val : ℝ     deriving Inhabited

-- Megayear (million years)
structure Megayear_F   where val : Float deriving Repr, BEq, Inhabited
structure Megayear_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Megayear_R   where val : ℝ     deriving Inhabited

-- Kiloyear (thousand years)
structure Kiloyear_F   where val : Float deriving Repr, BEq, Inhabited
structure Kiloyear_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kiloyear_R   where val : ℝ     deriving Inhabited

-- Julian year (exactly 365.25 days)
structure JulianYear_F where val : Float deriving Repr, BEq, Inhabited
structure JulianYear_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JulianYear_R where val : ℝ     deriving Inhabited

-- Julian day
structure JulianDay_F  where val : Float deriving Repr, BEq, Inhabited
structure JulianDay_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JulianDay_R  where val : ℝ     deriving Inhabited

-- Modified Julian Day (MJD = JD - 2400000.5)
structure MJD_F        where val : Float deriving Repr, BEq, Inhabited
structure MJD_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MJD_R        where val : ℝ     deriving Inhabited

/--
================================================================================================
   Stellar Units
================================================================================================
-/
-- Solar mass
structure SolarMass_F  where val : Float deriving Repr, BEq, Inhabited
structure SolarMass_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SolarMass_R  where val : ℝ     deriving Inhabited

-- Solar radius
structure SolarRadius_F where val : Float deriving Repr, BEq, Inhabited
structure SolarRadius_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SolarRadius_R where val : ℝ     deriving Inhabited

-- Solar luminosity
structure SolarLuminosity_F where val : Float deriving Repr, BEq, Inhabited
structure SolarLuminosity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SolarLuminosity_R where val : ℝ     deriving Inhabited

-- Effective temperature
structure EffectiveTemp_F where val : Float deriving Repr, BEq, Inhabited
structure EffectiveTemp_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EffectiveTemp_R where val : ℝ     deriving Inhabited

-- Surface gravity (log g in cgs)
structure LogG_F       where val : Float deriving Repr, BEq, Inhabited
structure LogG_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LogG_R       where val : ℝ     deriving Inhabited

-- Metallicity [Fe/H]
structure Metallicity_F where val : Float deriving Repr, BEq, Inhabited
structure Metallicity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Metallicity_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Planetary Units
================================================================================================
-/
-- Earth mass
structure EarthMass_F  where val : Float deriving Repr, BEq, Inhabited
structure EarthMass_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EarthMass_R  where val : ℝ     deriving Inhabited

-- Earth radius
structure EarthRadius_F where val : Float deriving Repr, BEq, Inhabited
structure EarthRadius_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EarthRadius_R where val : ℝ     deriving Inhabited

-- Jupiter mass
structure JupiterMass_F where val : Float deriving Repr, BEq, Inhabited
structure JupiterMass_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JupiterMass_R where val : ℝ     deriving Inhabited

-- Jupiter radius
structure JupiterRadius_F where val : Float deriving Repr, BEq, Inhabited
structure JupiterRadius_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JupiterRadius_R where val : ℝ     deriving Inhabited

-- Lunar mass
structure LunarMass_F  where val : Float deriving Repr, BEq, Inhabited
structure LunarMass_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LunarMass_R  where val : ℝ     deriving Inhabited

-- Lunar distance
structure LunarDistance_F where val : Float deriving Repr, BEq, Inhabited
structure LunarDistance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LunarDistance_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Angular Measurements
================================================================================================
-/
-- Arcsecond
structure Arcsecond_F  where val : Float deriving Repr, BEq, Inhabited
structure Arcsecond_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Arcsecond_R  where val : ℝ     deriving Inhabited

-- Milliarcsecond
structure Milliarcsec_F where val : Float deriving Repr, BEq, Inhabited
structure Milliarcsec_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Milliarcsec_R where val : ℝ     deriving Inhabited

-- Microarcsecond
structure Microarcsec_F where val : Float deriving Repr, BEq, Inhabited
structure Microarcsec_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Microarcsec_R where val : ℝ     deriving Inhabited

-- Arcminute
structure Arcminute_F  where val : Float deriving Repr, BEq, Inhabited
structure Arcminute_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Arcminute_R  where val : ℝ     deriving Inhabited

-- Solid angle: square degree
structure SquareDegree_F where val : Float deriving Repr, BEq, Inhabited
structure SquareDegree_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SquareDegree_R where val : ℝ     deriving Inhabited

-- Square arcminute
structure SquareArcmin_F where val : Float deriving Repr, BEq, Inhabited
structure SquareArcmin_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SquareArcmin_R where val : ℝ     deriving Inhabited

-- Square arcsecond
structure SquareArcsec_F where val : Float deriving Repr, BEq, Inhabited
structure SquareArcsec_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SquareArcsec_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Magnitude Systems
================================================================================================
-/
-- Apparent magnitude
structure ApparentMag_F where val : Float deriving Repr, BEq, Inhabited
structure ApparentMag_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ApparentMag_R where val : ℝ     deriving Inhabited

-- Absolute magnitude
structure AbsoluteMag_F where val : Float deriving Repr, BEq, Inhabited
structure AbsoluteMag_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AbsoluteMag_R where val : ℝ     deriving Inhabited

-- Bolometric magnitude
structure BolometricMag_F where val : Float deriving Repr, BEq, Inhabited
structure BolometricMag_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BolometricMag_R where val : ℝ     deriving Inhabited

-- Surface brightness: mag/arcsec²
structure SurfaceBrightness_F where val : Float deriving Repr, BEq, Inhabited
structure SurfaceBrightness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SurfaceBrightness_R where val : ℝ     deriving Inhabited

-- Color index (B-V, U-B, etc.)
structure ColorIndex_F where val : Float deriving Repr, BEq, Inhabited
structure ColorIndex_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ColorIndex_R where val : ℝ     deriving Inhabited

-- Extinction: mag/kpc
structure Extinction_F where val : Float deriving Repr, BEq, Inhabited
structure Extinction_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Extinction_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Flux and Luminosity
================================================================================================
-/
-- Jansky: 10⁻²⁶ W/(m²·Hz)
structure Jansky_F     where val : Float deriving Repr, BEq, Inhabited
structure Jansky_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Jansky_R     where val : ℝ     deriving Inhabited

structure MilliJansky_F where val : Float deriving Repr, BEq, Inhabited
structure MilliJansky_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilliJansky_R where val : ℝ     deriving Inhabited

structure MicroJansky_F where val : Float deriving Repr, BEq, Inhabited
structure MicroJansky_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MicroJansky_R where val : ℝ     deriving Inhabited

-- Erg per second: erg/s = 10⁻⁷ W
structure ErgPerSec_F  where val : Float deriving Repr, BEq, Inhabited
structure ErgPerSec_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ErgPerSec_R  where val : ℝ     deriving Inhabited

-- Erg per second per cm²: erg/(s·cm²)
structure ErgPerSecCm2_F where val : Float deriving Repr, BEq, Inhabited
structure ErgPerSecCm2_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ErgPerSecCm2_R where val : ℝ     deriving Inhabited

-- Photon flux: photons/(s·cm²)
structure PhotonFlux_F where val : Float deriving Repr, BEq, Inhabited
structure PhotonFlux_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PhotonFlux_R where val : ℝ     deriving Inhabited

-- AB magnitude flux unit
structure ABFlux_F     where val : Float deriving Repr, BEq, Inhabited
structure ABFlux_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ABFlux_R     where val : ℝ     deriving Inhabited

/--
================================================================================================
   Cosmological Parameters
================================================================================================
-/
-- Redshift
structure Redshift_F   where val : Float deriving Repr, BEq, Inhabited
structure Redshift_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Redshift_R   where val : ℝ     deriving Inhabited

-- Hubble parameter: km/(s·Mpc)
structure HubbleParam_F where val : Float deriving Repr, BEq, Inhabited
structure HubbleParam_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HubbleParam_R where val : ℝ     deriving Inhabited

-- Density parameter (Ω): dimensionless
structure DensityParam_F where val : Float deriving Repr, BEq, Inhabited
structure DensityParam_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DensityParam_R where val : ℝ     deriving Inhabited

-- Deceleration parameter
structure DecelerationParam_F where val : Float deriving Repr, BEq, Inhabited
structure DecelerationParam_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DecelerationParam_R where val : ℝ     deriving Inhabited

-- Comoving distance
structure ComovingDistance_F where val : Float deriving Repr, BEq, Inhabited
structure ComovingDistance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ComovingDistance_R where val : ℝ     deriving Inhabited

-- Luminosity distance
structure LuminosityDistance_F where val : Float deriving Repr, BEq, Inhabited
structure LuminosityDistance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LuminosityDistance_R where val : ℝ     deriving Inhabited

-- Angular diameter distance
structure AngularDistance_F where val : Float deriving Repr, BEq, Inhabited
structure AngularDistance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AngularDistance_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Spectroscopy
================================================================================================
-/
-- Equivalent width: Angstroms
structure EquivalentWidth_F where val : Float deriving Repr, BEq, Inhabited
structure EquivalentWidth_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EquivalentWidth_R where val : ℝ     deriving Inhabited

-- Velocity dispersion: km/s
structure VelocityDispersion_F where val : Float deriving Repr, BEq, Inhabited
structure VelocityDispersion_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VelocityDispersion_R where val : ℝ     deriving Inhabited

-- Radial velocity: km/s
structure RadialVelocity_F where val : Float deriving Repr, BEq, Inhabited
structure RadialVelocity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RadialVelocity_R where val : ℝ     deriving Inhabited

-- Proper motion: mas/yr
structure ProperMotion_F where val : Float deriving Repr, BEq, Inhabited
structure ProperMotion_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ProperMotion_R where val : ℝ     deriving Inhabited

-- Parallax: mas
structure Parallax_F   where val : Float deriving Repr, BEq, Inhabited
structure Parallax_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Parallax_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Radio Astronomy
================================================================================================
-/
-- Antenna temperature: K
structure AntennaTemp_F where val : Float deriving Repr, BEq, Inhabited
structure AntennaTemp_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AntennaTemp_R where val : ℝ     deriving Inhabited

-- Brightness temperature: K
structure BrightnessTemp_F where val : Float deriving Repr, BEq, Inhabited
structure BrightnessTemp_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BrightnessTemp_R where val : ℝ     deriving Inhabited

-- Flux density: Solar flux units (SFU = 10⁻²² W/(m²·Hz))
structure SFU_F        where val : Float deriving Repr, BEq, Inhabited
structure SFU_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SFU_R        where val : ℝ     deriving Inhabited

-- Dispersion measure: pc/cm³
structure DispersionMeasure_F where val : Float deriving Repr, BEq, Inhabited
structure DispersionMeasure_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DispersionMeasure_R where val : ℝ     deriving Inhabited

-- Rotation measure: rad/m²
structure RotationMeasure_F where val : Float deriving Repr, BEq, Inhabited
structure RotationMeasure_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RotationMeasure_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   X-ray Astronomy
================================================================================================
-/
-- Count rate: counts/s
structure CountRate_F  where val : Float deriving Repr, BEq, Inhabited
structure CountRate_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CountRate_R  where val : ℝ     deriving Inhabited

-- X-ray flux: keV/(s·cm²)
structure XRayFlux_F   where val : Float deriving Repr, BEq, Inhabited
structure XRayFlux_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure XRayFlux_R   where val : ℝ     deriving Inhabited

-- Hardness ratio: dimensionless
structure HardnessRatio_F where val : Float deriving Repr, BEq, Inhabited
structure HardnessRatio_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HardnessRatio_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Gravitational Wave Astronomy
================================================================================================
-/
-- Strain: dimensionless (ΔL/L)
structure GWStrain_F   where val : Float deriving Repr, BEq, Inhabited
structure GWStrain_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GWStrain_R   where val : ℝ     deriving Inhabited

-- Chirp mass: solar masses
structure ChirpMass_F  where val : Float deriving Repr, BEq, Inhabited
structure ChirpMass_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ChirpMass_R  where val : ℝ     deriving Inhabited

-- Gravitational wave luminosity: watts
structure GWLuminosity_F where val : Float deriving Repr, BEq, Inhabited
structure GWLuminosity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GWLuminosity_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Error Propagation & Measurement Helpers
================================================================================================
-/
-- Parametric Uncertainty Tracking with astronomical context
structure AstroMeasured (α : Type) where
  value : α
  uncertainty : α
  epoch : Option JulianDay_F := none
  observatory : Option String := none
  instrument : Option String := none
  filter : Option String := none  -- Photometric filter
  wavelength : Option Nanometer_F := none
  source : Option String := none
  deriving Repr, BEq, Inhabited

-- Measurement with uncertainty for magnitudes
structure MeasuredMagnitude_F where
  mag : ApparentMag_F
  mag_error : ApparentMag_F
  filter : String  -- "V", "B", "R", "I", etc.
  epoch : Option JulianDay_F := none
  deriving Repr, BEq, Inhabited

-- Parallax measurement with uncertainty
structure MeasuredParallax_F where
  parallax : Parallax_F
  parallax_error : Parallax_F
  correlation : Option Float := none  -- With proper motion
  source : Option String := none  -- "Gaia DR3", etc.
  deriving Repr, BEq, Inhabited

-- Error propagation for distance from parallax
def distanceFromParallaxWithError_F (p : MeasuredParallax_F)
    : AstroMeasured Parsec_F :=
  let d := 1.0 / (p.parallax.val / 1000.0)  -- Convert mas to arcsec
  -- Error prop: δd/d = δπ/π
  let d_error := d * (p.parallax_error.val / p.parallax.val)
  { value := ⟨d⟩
    uncertainty := ⟨d_error.abs⟩
    source := some "Parallax inversion" }

-- Error propagation for absolute magnitude
def absoluteMagWithError_F (m : MeasuredMagnitude_F) (d : AstroMeasured Parsec_F)
    : AstroMeasured AbsoluteMag_F :=
  let M := m.mag.val - 5.0 * Float.log (d.value.val / 10.0) / Float.log 10.0
  -- Error prop: δM = sqrt(δm² + (5/(ln 10) × δd/d)²)
  let d_term := 5.0 / Float.log 10.0 * d.uncertainty.val / d.value.val
  let M_error := Float.sqrt (m.mag_error.val^2 + d_term^2)
  { value := ⟨M⟩
    uncertainty := ⟨M_error⟩
    filter := some m.filter
    source := some "Distance modulus" }

/--
================================================================================================
   Validation & Range Checking Helpers
================================================================================================
-/

-- Magnitude validation
def isValidMagnitude_F (m : ApparentMag_F) : Bool :=
  -30.0 ≤ m.val && m.val ≤ 50.0  -- From brightest to faintest

def isNakedEyeVisible_F (m : ApparentMag_F) : Bool :=
  m.val ≤ 6.5

-- Redshift validation
def isValidRedshift_F (z : Redshift_F) : Bool :=
  z.val ≥ -1.0  -- Can be negative for blueshifts

def isCosmological_F (z : Redshift_F) : Bool :=
  z.val > 0.01  -- Beyond local peculiar velocities

def isHighRedshift_F (z : Redshift_F) : Bool :=
  z.val > 3.0

-- Parallax validation
def isValidParallax_F (p : Parallax_F) : Bool :=
  p.val > 0.0  -- Must be positive for real distances

def isReliableParallax_F (p : Parallax_F) (err : Parallax_F) : Bool :=
  p.val / err.val > 5.0  -- 5-sigma detection

-- Metallicity validation
def isValidMetallicity_F (feh : Metallicity_F) : Bool :=
  -5.0 ≤ feh.val && feh.val ≤ 1.0

def isMetalPoor_F (feh : Metallicity_F) : Bool :=
  feh.val < -1.0

def isMetalRich_F (feh : Metallicity_F) : Bool :=
  feh.val > 0.0

-- Color index validation
def isValidBV_F (bv : ColorIndex_F) : Bool :=
  -0.5 ≤ bv.val && bv.val ≤ 3.0  -- Typical range for stars

-- Hubble parameter validation
def isReasonableHubble_F (H : HubbleParam_F) : Bool :=
  50.0 ≤ H.val && H.val ≤ 100.0  -- Reasonable range

/--
================================================================================================
   Unit Conversions
================================================================================================
-/

-- Distance conversions
def parsecToMeter_F (pc : Parsec_F) : Meter_F :=
  ⟨pc.val * pc_meters_F⟩

def parsecToLightYear_F (pc : Parsec_F) : LightYear_F :=
  ⟨pc.val * 3.26156⟩

def parsecToAU_F (pc : Parsec_F) : AU_F :=
  ⟨pc.val * 206264.806⟩

def auToMeter_F (au : AU_F) : Meter_F :=
  ⟨au.val * AU_meters_F⟩

def auToParsec_F (au : AU_F) : Parsec_F :=
  ⟨au.val / 206264.806⟩

def lightYearToMeter_F (ly : LightYear_F) : Meter_F :=
  ⟨ly.val * ly_meters_F⟩

def lightYearToParsec_F (ly : LightYear_F) : Parsec_F :=
  ⟨ly.val / 3.26156⟩

def kiloparsecToParsec_F (kpc : Kiloparsec_F) : Parsec_F :=
  ⟨kpc.val * 1000.0⟩

def megaparsecToParsec_F (mpc : Megaparsec_F) : Parsec_F :=
  ⟨mpc.val * 1e6⟩

-- Angular conversions
def arcsecondToDegree_F (arcsec : Arcsecond_F) : Degree_F :=
  ⟨arcsec.val / 3600.0⟩

def arcsecondToRadian_F (arcsec : Arcsecond_F) : Radian_F :=
  ⟨arcsec.val * pi_F / 648000.0⟩

def milliarcsecToArcsec_F (mas : Milliarcsec_F) : Arcsecond_F :=
  ⟨mas.val / 1000.0⟩

def arcminuteToDegree_F (arcmin : Arcminute_F) : Degree_F :=
  ⟨arcmin.val / 60.0⟩

-- Mass conversions
def solarMassToKg_F (msun : SolarMass_F) : Kilogram_F :=
  ⟨msun.val * solar_mass_F⟩

def earthMassToKg_F (mearth : EarthMass_F) : Kilogram_F :=
  ⟨mearth.val * earth_mass_F⟩

def jupiterMassToKg_F (mjup : JupiterMass_F) : Kilogram_F :=
  ⟨mjup.val * jupiter_mass_F⟩

def earthMassToJupiterMass_F (me : EarthMass_F) : JupiterMass_F :=
  ⟨me.val * earth_mass_F / jupiter_mass_F⟩

def jupiterMassToSolarMass_F (mj : JupiterMass_F) : SolarMass_F :=
  ⟨mj.val * jupiter_mass_F / solar_mass_F⟩

-- Luminosity conversions
def solarLumToWatt_F (lsun : SolarLuminosity_F) : Watt_F :=
  ⟨lsun.val * solar_luminosity_F⟩

def ergPerSecToWatt_F (erg : ErgPerSec_F) : Watt_F :=
  ⟨erg.val * 1e-7⟩

def wattToSolarLum_F (w : Watt_F) : SolarLuminosity_F :=
  ⟨w.val / solar_luminosity_F⟩

-- Time conversions
def julianYearToSecond_F (jy : JulianYear_F) : Second_F :=
  ⟨jy.val * 365.25 * 86400.0⟩

def gigayearToSecond_F (gyr : Gigayear_F) : Second_F :=
  ⟨gyr.val * 1e9 * 365.25 * 86400.0⟩

def megayearToYear_F (myr : Megayear_F) : Year_F :=
  ⟨myr.val * 1e6⟩

-- Flux conversions
def janskyToWPerM2Hz_F (jy : Jansky_F) : Float :=
  jy.val * 1e-26

def maggieToJansky_F (ab : ABFlux_F) : Jansky_F :=
  ⟨ab.val * 3631.0⟩  -- AB magnitude zero point

def sfuToJansky_F (sfu : SFU_F) : Jansky_F :=
  ⟨sfu.val * 1e4⟩

/--
================================================================================================
   Common Astronomical Calculations
================================================================================================
-/

-- Distance from parallax
def distanceFromParallax_F (p : Parallax_F) : Parsec_F :=
  ⟨1000.0 / p.val⟩  -- p in mas, distance in pc

-- Parallax from distance
def parallaxFromDistance_F (d : Parsec_F) : Parallax_F :=
  ⟨1000.0 / d.val⟩  -- Returns mas

-- Distance modulus
def distanceModulus_F (d : Parsec_F) : Float :=
  5.0 * Float.log d.val / Float.log 10.0 - 5.0

-- Absolute magnitude from apparent magnitude and distance
def absoluteMagnitude_F (m : ApparentMag_F) (d : Parsec_F) : AbsoluteMag_F :=
  ⟨m.val - distanceModulus_F d⟩

-- Apparent magnitude from absolute magnitude and distance
def apparentMagnitude_F (M : AbsoluteMag_F) (d : Parsec_F) : ApparentMag_F :=
  ⟨M.val + distanceModulus_F d⟩

-- Luminosity from absolute magnitude
def luminosityFromAbsMag_F (M : AbsoluteMag_F) : SolarLuminosity_F :=
  ⟨10.0 ^ ((4.74 - M.val) / 2.5)⟩  -- Solar Mbol = 4.74

-- Stefan-Boltzmann for stars
def stellarLuminosity_F (R : SolarRadius_F) (T : EffectiveTemp_F)
    : SolarLuminosity_F :=
  let L_watts := 4.0 * pi_F * (R.val * solar_radius_F)^2 *
                 stefan_boltzmann_F * T.val^4
  ⟨L_watts / solar_luminosity_F⟩

-- Stellar radius from luminosity and temperature
def stellarRadius_F (L : SolarLuminosity_F) (T : EffectiveTemp_F)
    : SolarRadius_F :=
  let L_watts := L.val * solar_luminosity_F
  let R_meters := Float.sqrt (L_watts / (4.0 * pi_F * stefan_boltzmann_F * T.val^4))
  ⟨R_meters / solar_radius_F⟩

-- Pogson's law (magnitude difference to flux ratio)
def fluxRatio_F (m1 : ApparentMag_F) (m2 : ApparentMag_F) : Float :=
  10.0 ^ ((m2.val - m1.val) / 2.5)

-- Magnitude from flux ratio
def magnitudeDifference_F (f1 : Float) (f2 : Float) : Float :=
  -2.5 * Float.log (f1 / f2) / Float.log 10.0

-- Redshift to velocity (non-relativistic)
def redshiftToVelocity_F (z : Redshift_F) : Velocity_F :=
  ⟨z.val * c_light_F⟩  -- v = cz for z << 1

-- Redshift to velocity (relativistic)
def redshiftToVelocityRel_F (z : Redshift_F) : Velocity_F :=
  let v := c_light_F * ((1.0 + z.val)^2 - 1.0) / ((1.0 + z.val)^2 + 1.0)
  ⟨v⟩

-- Velocity to redshift (relativistic)
def velocityToRedshift_F (v : Velocity_F) : Redshift_F :=
  let beta := v.val / c_light_F
  ⟨Float.sqrt ((1.0 + beta) / (1.0 - beta)) - 1.0⟩

-- Hubble's law
def hubbleDistance_F (v : Velocity_F) (H0 : HubbleParam_F) : Megaparsec_F :=
  ⟨v.val / (H0.val * 1000.0)⟩  -- v in m/s, H0 in km/s/Mpc

-- Luminosity distance (simplified, z << 1)
def luminosityDistanceSimple_F (z : Redshift_F) (H0 : HubbleParam_F)
    : Megaparsec_F :=
  ⟨c_light_F * z.val / (H0.val * 1000.0)⟩

-- Angular size from physical size and distance
def angularSize_F (size : Meter_F) (distance : Parsec_F) : Arcsecond_F :=
  ⟨size.val / (distance.val * pc_meters_F) * 206264.806⟩

-- Physical size from angular size and distance
def physicalSize_F (theta : Arcsecond_F) (distance : Parsec_F) : AU_F :=
  ⟨theta.val * distance.val / 206264.806⟩

-- Kepler's third law
def orbitalPeriod_F (a : AU_F) (M : SolarMass_F) : JulianYear_F :=
  ⟨Float.sqrt (a.val^3 / M.val)⟩

-- Semi-major axis from period
def semiMajorAxis_F (P : JulianYear_F) (M : SolarMass_F) : AU_F :=
  ⟨(P.val^2 * M.val) ^ (1.0/3.0)⟩

-- Escape velocity
def escapeVelocity_F (M : SolarMass_F) (R : SolarRadius_F) : Velocity_F :=
  ⟨Float.sqrt (2.0 * G_F * M.val * solar_mass_F / (R.val * solar_radius_F))⟩

-- Schwarzschild radius
def schwarzschildRadius_F (M : SolarMass_F) : Kilometer_F :=
  ⟨2.0 * G_F * M.val * solar_mass_F / c_light_F^2 / 1000.0⟩

-- Eddington luminosity
def eddingtonLuminosity_F (M : SolarMass_F) : SolarLuminosity_F :=
  ⟨3.2e4 * M.val⟩  -- L_Edd/L_sun ≈ 3.2×10^4 × (M/M_sun)

-- Jeans mass (simplified)
def jeansMass_F (T : Kelvin_F) (n : Float) : SolarMass_F :=
  -- n is number density in cm^-3
  let M_j := 2.0e5 * (T.val / 10.0)^1.5 * (n / 1.0)^(-0.5)
  ⟨M_j⟩

-- Virial theorem for clusters
def virialMass_F (sigma : VelocityDispersion_F) (R : Kiloparsec_F)
    : SolarMass_F :=
  let M := 5.0 * sigma.val^2 * R.val * 1000.0 * pc_meters_F / G_F
  ⟨M / solar_mass_F⟩

-- Tully-Fisher relation (simplified)
def tullyFisherLuminosity_F (v_rot : Velocity_F) : SolarLuminosity_F :=
  ⟨1e10 * (v_rot.val / 200000.0)^4⟩  -- L ∝ v^4

-- Chirp mass from binary system
def chirpMass_F (m1 : SolarMass_F) (m2 : SolarMass_F) : ChirpMass_F :=
  let M_chirp := ((m1.val * m2.val)^3 / (m1.val + m2.val))^(1.0/5.0)
  ⟨M_chirp⟩

-- Roche limit (rigid body)
def rocheLimit_F (M_primary : SolarMass_F) (rho_satellite : KgPerM3_F)
    (R_primary : SolarRadius_F) : SolarRadius_F :=
  let rho_primary := M_primary.val * solar_mass_F /
                     (4.0/3.0 * pi_F * (R_primary.val * solar_radius_F)^3)
  ⟨2.456 * R_primary.val * (rho_primary / rho_satellite.val)^(1.0/3.0)⟩

-- Hill sphere radius
def hillRadius_F (m : SolarMass_F) (M : SolarMass_F) (a : AU_F)
    (e : Float) : AU_F :=
  ⟨a.val * (1.0 - e) * (m.val / (3.0 * M.val))^(1.0/3.0)⟩

-- Synodic period
def synodicPeriod_F (P1 : JulianYear_F) (P2 : JulianYear_F) : JulianYear_F :=
  ⟨1.0 / (1.0/P1.val - 1.0/P2.val).abs⟩

-- Proper motion total
def totalProperMotion_F (mu_ra : ProperMotion_F) (mu_dec : ProperMotion_F)
    : ProperMotion_F :=
  ⟨Float.sqrt (mu_ra.val^2 + mu_dec.val^2)⟩

-- Tangential velocity from proper motion
def tangentialVelocity_F (mu : ProperMotion_F) (d : Parsec_F)
    : Velocity_F :=
  ⟨4.74 * mu.val * d.val⟩  -- Returns km/s, convert to m/s

-- Space velocity
def spaceVelocity_F (v_radial : RadialVelocity_F) (v_tan : Velocity_F)
    : Velocity_F :=
  ⟨Float.sqrt ((v_radial.val * 1000.0)^2 + v_tan.val^2)⟩

end Units.Physics.Astro
