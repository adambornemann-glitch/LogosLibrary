-- Materials.lean        -- Materials science units and properties
import LogosLibrary.Units.Core.SI
import LogosLibrary.Units.Physics.Mechanics
import LogosLibrary.Units.Physics.Thermal
import LogosLibrary.Units.Physics.Electromagnetism
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

namespace Units.Materials

open Units.SI Units.Mechanics Units.Thermal Units.Electromagnetism

/-
================================================================================
MATERIALS SCIENCE UNITS LIBRARY
================================================================================

This module provides type-safe units for materials science, crystallography,
metallurgy, ceramics, polymers, and composite materials. Following the
triple-type architecture for maximum flexibility without type conversion friction.

## COVERAGE
- Hardness scales (Vickers, Rockwell, Brinell, Knoop, Mohs, Shore)
- Crystal structure (lattice parameters, Miller indices, d-spacing)
- Microstructure (grain size, texture, phase fractions)
- Diffusion and transport (diffusivity, mobility, permeation)
- Electronic properties (band gap, carrier density, mobility)
- Mechanical behavior (work hardening, creep, fatigue)
- Processing parameters (cooling rates, annealing, sintering)
- Surface properties (roughness, adhesion, wetting)
- Magnetic materials (coercivity, remanence, permeability)
- Corrosion (rates, potentials, passivation)
- Thin films and coatings (thickness, deposition rates)
- Composite properties (volume fraction, interface strength)

## USAGE PATTERNS
Float: Materials testing, quality control, process monitoring, failure analysis,
characterization data, industrial specifications, engineering design,
experimental measurements, real-time sensing

ℚ: Crystallographic calculations, stoichiometry, phase diagrams,
Miller indices, symmetry operations, exact compositions, atomic percentages,
lattice ratios, crystallographic directions

ℝ: Continuum mechanics modeling, phase field simulations, diffusion theory,
thermodynamic calculations, electronic structure theory, constitutive models,
fracture mechanics, statistical mechanics of defects
-/

set_option autoImplicit false
set_option linter.unusedVariables false

/--
================================================================================================
   Mathematical Constants for Materials Science
================================================================================================
-/
def sqrt2_F : Float := 1.41421356237309504880
def sqrt3_F : Float := 1.73205080756887729352
def pi_F : Float := 3.14159265358979323846
def goldenRatio_F : Float := 1.61803398874989484820
def avogadro_F : Float := 6.02214076e23

/--
================================================================================================
   Hardness Scales
================================================================================================
-/
-- Vickers hardness (HV) - kg/mm² or GPa
structure VickersHardness_F where val : Float deriving Repr, BEq, Inhabited
structure VickersHardness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VickersHardness_R where val : ℝ     deriving Inhabited

-- Rockwell hardness scales (dimensionless)
structure RockwellA_F  where val : Float deriving Repr, BEq, Inhabited
structure RockwellB_F  where val : Float deriving Repr, BEq, Inhabited
structure RockwellC_F  where val : Float deriving Repr, BEq, Inhabited
structure Rockwell15N_F where val : Float deriving Repr, BEq, Inhabited
structure Rockwell30N_F where val : Float deriving Repr, BEq, Inhabited
structure Rockwell45N_F where val : Float deriving Repr, BEq, Inhabited

-- Brinell hardness (HB) - kg/mm²
structure BrinellHardness_F where val : Float deriving Repr, BEq, Inhabited
structure BrinellHardness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BrinellHardness_R where val : ℝ     deriving Inhabited

-- Knoop hardness (HK) - kg/mm²
structure KnoopHardness_F where val : Float deriving Repr, BEq, Inhabited
structure KnoopHardness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KnoopHardness_R where val : ℝ     deriving Inhabited

-- Mohs scale (1-10)
structure MohsHardness_F where val : Float deriving Repr, BEq, Inhabited
structure MohsHardness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MohsHardness_R where val : ℝ     deriving Inhabited

-- Shore hardness (polymers/elastomers)
structure ShoreA_F     where val : Float deriving Repr, BEq, Inhabited
structure ShoreD_F     where val : Float deriving Repr, BEq, Inhabited
structure ShoreOO_F    where val : Float deriving Repr, BEq, Inhabited

-- Meyer hardness
structure MeyerHardness_F where val : Float deriving Repr, BEq, Inhabited
structure MeyerHardness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MeyerHardness_R where val : ℝ     deriving Inhabited

-- Nanoindentation hardness
structure NanoHardness_F where val : Float deriving Repr, BEq, Inhabited  -- GPa
structure NanoHardness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NanoHardness_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Crystal Structure and Crystallography
================================================================================================
-/
-- Lattice parameters
structure LatticeParam_a_F where val : Float deriving Repr, BEq, Inhabited  -- Angstroms
structure LatticeParam_b_F where val : Float deriving Repr, BEq, Inhabited
structure LatticeParam_c_F where val : Float deriving Repr, BEq, Inhabited
structure LatticeAngle_alpha_F where val : Float deriving Repr, BEq, Inhabited  -- degrees
structure LatticeAngle_beta_F  where val : Float deriving Repr, BEq, Inhabited
structure LatticeAngle_gamma_F where val : Float deriving Repr, BEq, Inhabited

-- Miller indices (integers)
structure MillerIndex where
  h : ℤ
  k : ℤ
  l : ℤ
  deriving Repr, BEq, DecidableEq, Inhabited

-- Miller-Bravais indices (hexagonal systems)
structure MillerBravaisIndex where
  h : ℤ
  k : ℤ
  i : ℤ  -- i = -(h+k)
  l : ℤ
  deriving Repr, BEq, DecidableEq, Inhabited

-- d-spacing (interplanar spacing)
structure DSpacing_F   where val : Float deriving Repr, BEq, Inhabited  -- Angstroms
structure DSpacing_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DSpacing_R   where val : ℝ     deriving Inhabited

-- Unit cell volume
structure UnitCellVolume_F where val : Float deriving Repr, BEq, Inhabited  -- ų
structure UnitCellVolume_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure UnitCellVolume_R where val : ℝ     deriving Inhabited

-- Atomic packing factor
structure PackingFactor_F where val : Float deriving Repr, BEq, Inhabited
structure PackingFactor_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PackingFactor_R where val : ℝ     deriving Inhabited

-- Coordination number
structure CoordinationNum where val : ℕ deriving Repr, BEq, DecidableEq, Inhabited

-- Burgers vector magnitude
structure BurgersVector_F where val : Float deriving Repr, BEq, Inhabited  -- Angstroms
structure BurgersVector_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BurgersVector_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Microstructure
================================================================================================
-/
-- Grain size (ASTM grain size number)
structure ASTMGrainSize_F where val : Float deriving Repr, BEq, Inhabited
structure ASTMGrainSize_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ASTMGrainSize_R where val : ℝ     deriving Inhabited

-- Average grain diameter
structure GrainDiameter_F where val : Float deriving Repr, BEq, Inhabited  -- micrometers
structure GrainDiameter_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GrainDiameter_R where val : ℝ     deriving Inhabited

-- Grain boundary energy
structure GBEnergy_F   where val : Float deriving Repr, BEq, Inhabited  -- J/m²
structure GBEnergy_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GBEnergy_R   where val : ℝ     deriving Inhabited

-- Dislocation density
structure DislocationDensity_F where val : Float deriving Repr, BEq, Inhabited  -- m⁻²
structure DislocationDensity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DislocationDensity_R where val : ℝ     deriving Inhabited

-- Phase fraction (volume or mass)
structure PhaseFraction_F where val : Float deriving Repr, BEq, Inhabited
structure PhaseFraction_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PhaseFraction_R where val : ℝ     deriving Inhabited

-- Texture coefficient
structure TextureCoeff_F where val : Float deriving Repr, BEq, Inhabited
structure TextureCoeff_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TextureCoeff_R where val : ℝ     deriving Inhabited

-- Porosity
structure Porosity_F   where val : Float deriving Repr, BEq, Inhabited  -- fraction
structure Porosity_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Porosity_R   where val : ℝ     deriving Inhabited

-- Void fraction
structure VoidFraction_F where val : Float deriving Repr, BEq, Inhabited
structure VoidFraction_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VoidFraction_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Diffusion and Transport
================================================================================================
-/
-- Diffusion coefficient/diffusivity
structure Diffusivity_F where val : Float deriving Repr, BEq, Inhabited  -- m²/s
structure Diffusivity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Diffusivity_R where val : ℝ     deriving Inhabited

-- Pre-exponential factor (D₀)
structure DiffusionD0_F where val : Float deriving Repr, BEq, Inhabited  -- m²/s
structure DiffusionD0_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DiffusionD0_R where val : ℝ     deriving Inhabited

-- Activation energy for diffusion
structure DiffusionEa_F where val : Float deriving Repr, BEq, Inhabited  -- kJ/mol
structure DiffusionEa_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DiffusionEa_R where val : ℝ     deriving Inhabited

-- Ionic conductivity
structure IonicConductivity_F where val : Float deriving Repr, BEq, Inhabited  -- S/m
structure IonicConductivity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure IonicConductivity_R where val : ℝ     deriving Inhabited

-- Permeability (gas/liquid through material)
structure Permeability_F where val : Float deriving Repr, BEq, Inhabited  -- Barrer
structure Permeability_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Permeability_R where val : ℝ     deriving Inhabited

-- Solubility (in materials)
structure Solubility_F where val : Float deriving Repr, BEq, Inhabited  -- mol/m³·Pa
structure Solubility_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Solubility_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Electronic and Band Structure
================================================================================================
-/
-- Band gap
structure BandGap_F    where val : Float deriving Repr, BEq, Inhabited  -- eV
structure BandGap_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BandGap_R    where val : ℝ     deriving Inhabited

-- Carrier concentration
structure ElectronDensity_F where val : Float deriving Repr, BEq, Inhabited  -- cm⁻³
structure HoleDensity_F where val : Float deriving Repr, BEq, Inhabited      -- cm⁻³

-- Carrier mobility
structure ElectronMobility_F where val : Float deriving Repr, BEq, Inhabited  -- cm²/V·s
structure HoleMobility_F where val : Float deriving Repr, BEq, Inhabited      -- cm²/V·s

-- Effective mass
structure EffectiveMass_F where val : Float deriving Repr, BEq, Inhabited  -- m*/m₀
structure EffectiveMass_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EffectiveMass_R where val : ℝ     deriving Inhabited

-- Work function
structure WorkFunction_F where val : Float deriving Repr, BEq, Inhabited  -- eV
structure WorkFunction_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WorkFunction_R where val : ℝ     deriving Inhabited

-- Fermi level
structure FermiLevel_F where val : Float deriving Repr, BEq, Inhabited  -- eV
structure FermiLevel_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FermiLevel_R where val : ℝ     deriving Inhabited

-- Dielectric constant (relative permittivity)
structure DielectricConst_F where val : Float deriving Repr, BEq, Inhabited
structure DielectricConst_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DielectricConst_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Mechanical Behavior
================================================================================================
-/
-- Work hardening coefficient (n-value)
structure WorkHardening_n_F where val : Float deriving Repr, BEq, Inhabited
structure WorkHardening_n_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WorkHardening_n_R where val : ℝ     deriving Inhabited

-- Strength coefficient (K-value)
structure StrengthCoeff_K_F where val : Float deriving Repr, BEq, Inhabited  -- MPa
structure StrengthCoeff_K_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure StrengthCoeff_K_R where val : ℝ     deriving Inhabited

-- Creep rate
structure CreepRate_F  where val : Float deriving Repr, BEq, Inhabited  -- s⁻¹
structure CreepRate_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CreepRate_R  where val : ℝ     deriving Inhabited

-- Creep stress exponent
structure CreepExponent_F where val : Float deriving Repr, BEq, Inhabited
structure CreepExponent_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CreepExponent_R where val : ℝ     deriving Inhabited

-- Fatigue strength
structure FatigueStrength_F where val : Float deriving Repr, BEq, Inhabited  -- MPa
structure FatigueStrength_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FatigueStrength_R where val : ℝ     deriving Inhabited

-- Fatigue life (cycles)
structure FatigueLife  where val : ℕ     deriving Repr, BEq, DecidableEq, Inhabited

-- Paris law constants
structure ParisC_F     where val : Float deriving Repr, BEq, Inhabited
structure ParisM_F     where val : Float deriving Repr, BEq, Inhabited

-- R-ratio (fatigue)
structure RRatio_F     where val : Float deriving Repr, BEq, Inhabited
structure RRatio_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RRatio_R     where val : ℝ     deriving Inhabited

-- Weibull modulus
structure WeibullModulus_F where val : Float deriving Repr, BEq, Inhabited
structure WeibullModulus_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WeibullModulus_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Processing Parameters
================================================================================================
-/
-- Cooling rate
structure CoolingRate_F where val : Float deriving Repr, BEq, Inhabited  -- K/s
structure CoolingRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CoolingRate_R where val : ℝ     deriving Inhabited

-- Heating rate
structure HeatingRate_F where val : Float deriving Repr, BEq, Inhabited  -- K/s
structure HeatingRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HeatingRate_R where val : ℝ     deriving Inhabited

-- Annealing temperature
structure AnnealTemp_F where val : Float deriving Repr, BEq, Inhabited  -- K or °C
structure AnnealTemp_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AnnealTemp_R where val : ℝ     deriving Inhabited

-- Sintering temperature
structure SinterTemp_F where val : Float deriving Repr, BEq, Inhabited  -- K or °C
structure SinterTemp_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SinterTemp_R where val : ℝ     deriving Inhabited

-- Homologous temperature (T/Tm)
structure HomologousTemp_F where val : Float deriving Repr, BEq, Inhabited
structure HomologousTemp_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HomologousTemp_R where val : ℝ     deriving Inhabited

-- Strain rate
structure StrainRate_F where val : Float deriving Repr, BEq, Inhabited  -- s⁻¹
structure StrainRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure StrainRate_R where val : ℝ     deriving Inhabited

-- Deposition rate (thin films)
structure DepositionRate_F where val : Float deriving Repr, BEq, Inhabited  -- nm/s
structure DepositionRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DepositionRate_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Surface Properties
================================================================================================
-/
-- Surface roughness (Ra, Rq, Rz)
structure Roughness_Ra_F where val : Float deriving Repr, BEq, Inhabited  -- nm or μm
structure Roughness_Rq_F where val : Float deriving Repr, BEq, Inhabited
structure Roughness_Rz_F where val : Float deriving Repr, BEq, Inhabited

-- Surface energy
structure SurfaceEnergy_F where val : Float deriving Repr, BEq, Inhabited  -- mJ/m²
structure SurfaceEnergy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SurfaceEnergy_R where val : ℝ     deriving Inhabited

-- Contact angle
structure ContactAngle_F where val : Float deriving Repr, BEq, Inhabited  -- degrees
structure ContactAngle_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ContactAngle_R where val : ℝ     deriving Inhabited

-- Adhesion energy
structure AdhesionEnergy_F where val : Float deriving Repr, BEq, Inhabited  -- J/m²
structure AdhesionEnergy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AdhesionEnergy_R where val : ℝ     deriving Inhabited

-- Work of adhesion
structure WorkOfAdhesion_F where val : Float deriving Repr, BEq, Inhabited  -- mJ/m²
structure WorkOfAdhesion_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WorkOfAdhesion_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Magnetic Materials
================================================================================================
-/
-- Coercivity
structure Coercivity_F where val : Float deriving Repr, BEq, Inhabited  -- A/m or Oe
structure Coercivity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Coercivity_R where val : ℝ     deriving Inhabited

-- Remanence
structure Remanence_F  where val : Float deriving Repr, BEq, Inhabited  -- T or G
structure Remanence_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Remanence_R  where val : ℝ     deriving Inhabited

-- Saturation magnetization
structure SaturationMag_F where val : Float deriving Repr, BEq, Inhabited  -- A/m
structure SaturationMag_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SaturationMag_R where val : ℝ     deriving Inhabited

-- Curie temperature
structure CurieTemp_F  where val : Float deriving Repr, BEq, Inhabited  -- K
structure CurieTemp_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CurieTemp_R  where val : ℝ     deriving Inhabited

-- Néel temperature
structure NeelTemp_F   where val : Float deriving Repr, BEq, Inhabited  -- K
structure NeelTemp_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NeelTemp_R   where val : ℝ     deriving Inhabited

-- Magnetic anisotropy constant
structure AnisotropyConst_F where val : Float deriving Repr, BEq, Inhabited  -- J/m³
structure AnisotropyConst_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AnisotropyConst_R where val : ℝ     deriving Inhabited

-- Exchange stiffness
structure ExchangeStiffness_F where val : Float deriving Repr, BEq, Inhabited  -- J/m
structure ExchangeStiffness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ExchangeStiffness_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Corrosion and Degradation
================================================================================================
-/
-- Corrosion rate
structure CorrosionRate_mpy_F where val : Float deriving Repr, BEq, Inhabited  -- mils/year
structure CorrosionRate_mmpy_F where val : Float deriving Repr, BEq, Inhabited  -- mm/year
structure CorrosionRate_ipy_F where val : Float deriving Repr, BEq, Inhabited  -- inches/year

-- Corrosion potential
structure CorrosionPotential_F where val : Float deriving Repr, BEq, Inhabited  -- V vs SHE
structure CorrosionPotential_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CorrosionPotential_R where val : ℝ     deriving Inhabited

-- Pitting potential
structure PittingPotential_F where val : Float deriving Repr, BEq, Inhabited  -- V
structure PittingPotential_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PittingPotential_R where val : ℝ     deriving Inhabited

-- Passivation current density
structure PassivationCurrent_F where val : Float deriving Repr, BEq, Inhabited  -- μA/cm²
structure PassivationCurrent_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PassivationCurrent_R where val : ℝ     deriving Inhabited

-- Tafel slope
structure TafelSlope_F where val : Float deriving Repr, BEq, Inhabited  -- mV/decade
structure TafelSlope_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TafelSlope_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Thin Films and Coatings
================================================================================================
-/
-- Film thickness
structure FilmThickness_F where val : Float deriving Repr, BEq, Inhabited  -- nm
structure FilmThickness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FilmThickness_R where val : ℝ     deriving Inhabited

-- Coating thickness
structure CoatingThickness_F where val : Float deriving Repr, BEq, Inhabited  -- μm
structure CoatingThickness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CoatingThickness_R where val : ℝ     deriving Inhabited

-- Residual stress (in films)
structure ResidualStress_F where val : Float deriving Repr, BEq, Inhabited  -- MPa
structure ResidualStress_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ResidualStress_R where val : ℝ     deriving Inhabited

-- Critical thickness (for epitaxy)
structure CriticalThickness_F where val : Float deriving Repr, BEq, Inhabited  -- nm
structure CriticalThickness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CriticalThickness_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Composite Materials
================================================================================================
-/
-- Fiber volume fraction
structure FiberVolumeFraction_F where val : Float deriving Repr, BEq, Inhabited
structure FiberVolumeFraction_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FiberVolumeFraction_R where val : ℝ     deriving Inhabited

-- Matrix volume fraction
structure MatrixVolumeFraction_F where val : Float deriving Repr, BEq, Inhabited
structure MatrixVolumeFraction_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MatrixVolumeFraction_R where val : ℝ     deriving Inhabited

-- Interface shear strength
structure InterfaceStrength_F where val : Float deriving Repr, BEq, Inhabited  -- MPa
structure InterfaceStrength_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure InterfaceStrength_R where val : ℝ     deriving Inhabited

-- Aspect ratio (fiber/particle)
structure AspectRatio_F where val : Float deriving Repr, BEq, Inhabited
structure AspectRatio_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AspectRatio_R where val : ℝ     deriving Inhabited

-- Critical fiber length
structure CriticalFiberLength_F where val : Float deriving Repr, BEq, Inhabited  -- mm
structure CriticalFiberLength_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CriticalFiberLength_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Validation Helpers
================================================================================================
-/

-- Hardness validation
def isValidVickers_F (hv : VickersHardness_F) : Bool :=
  hv.val > 0.0 && hv.val < 10000.0  -- Reasonable range

def isValidRockwellC_F (hrc : RockwellC_F) : Bool :=
  20.0 ≤ hrc.val && hrc.val ≤ 70.0  -- Typical HRC range

def isValidMohs_F (mohs : MohsHardness_F) : Bool :=
  1.0 ≤ mohs.val && mohs.val ≤ 10.0

-- Crystal structure validation
def isValidMillerIndex (m : MillerIndex) : Bool :=
  m.h.natAbs ≤ 10 && m.k.natAbs ≤ 10 && m.l.natAbs ≤ 10  -- Reasonable indices

def isValidPackingFactor_F (pf : PackingFactor_F) : Bool :=
  0.0 < pf.val && pf.val ≤ 0.74  -- Max is FCC/HCP packing

-- Microstructure validation
def isValidASTMGrainSize_F (g : ASTMGrainSize_F) : Bool :=
  -3.0 ≤ g.val && g.val ≤ 15.0  -- ASTM E112 range

def isValidPhaseFraction_F (f : PhaseFraction_F) : Bool :=
  0.0 ≤ f.val && f.val ≤ 1.0

def isValidPorosity_F (p : Porosity_F) : Bool :=
  0.0 ≤ p.val && p.val < 1.0

-- Electronic validation
def isValidBandGap_F (bg : BandGap_F) : Bool :=
  0.0 ≤ bg.val && bg.val ≤ 15.0  -- Up to wide bandgap materials

def isValidCarrierDensity_F (n : ElectronDensity_F) : Bool :=
  n.val > 0.0 && n.val < 1e25  -- Physical limits

-- Mechanical validation
def isValidWorkHardening_F (n : WorkHardening_n_F) : Bool :=
  0.0 ≤ n.val && n.val ≤ 1.0  -- Typical range

def isValidRRatio_F (r : RRatio_F) : Bool :=
  -1.0 ≤ r.val && r.val ≤ 1.0

-- Surface validation
def isValidContactAngle_F (ca : ContactAngle_F) : Bool :=
  0.0 ≤ ca.val && ca.val ≤ 180.0

-- Composite validation
def isValidVolumeFraction_F (vf : FiberVolumeFraction_F) : Bool :=
  0.0 ≤ vf.val && vf.val ≤ 1.0

def volumeFractionsSum_F (fiber : FiberVolumeFraction_F) (matrix : MatrixVolumeFraction_F)
    (voids : VoidFraction_F) : Bool :=
  (fiber.val + matrix.val + voids.val - 1.0).abs < 0.001

/--
================================================================================================
   Unit Conversions
================================================================================================
-/

-- Hardness conversions (approximate)
def vickersToRockwellC_F (hv : VickersHardness_F) : RockwellC_F :=
  -- Approximate conversion for steels
  if hv.val < 450.0 then
    ⟨0.0⟩  -- Below HRC range
  else if hv.val > 900.0 then
    ⟨68.0⟩  -- Maximum practical HRC
  else
    ⟨(hv.val - 230.0) / 10.0⟩

def rockwellCToVickers_F (hrc : RockwellC_F) : VickersHardness_F :=
  ⟨230.0 + 10.0 * hrc.val⟩

def brinellToVickers_F (hb : BrinellHardness_F) : VickersHardness_F :=
  ⟨hb.val * 1.05⟩  -- Approximate for most materials

def vickersToGPa_F (hv : VickersHardness_F) : Float :=
  hv.val * 0.009807  -- Convert kg/mm² to GPa

-- Grain size conversions
def astmToGrainDiameter_F (g : ASTMGrainSize_F) : GrainDiameter_F :=
  -- ASTM E112 formula: d = 2^((3-g)/2) * 25.4 μm
  ⟨25.4 * (2.0 ^ ((3.0 - g.val) / 2.0))⟩

def grainDiameterToASTM_F (d : GrainDiameter_F) : ASTMGrainSize_F :=
  ⟨3.0 - 2.0 * Float.log (d.val / 25.4) / Float.log 2.0⟩

-- Lattice parameter to unit cell volume (cubic)
def cubicVolume_F (a : LatticeParam_a_F) : UnitCellVolume_F :=
  ⟨a.val ^ 3⟩

-- Corrosion rate conversions
def mpyToMmpy_F (mpy : CorrosionRate_mpy_F) : CorrosionRate_mmpy_F :=
  ⟨mpy.val * 0.0254⟩

def mmpyToMpy_F (mmpy : CorrosionRate_mmpy_F) : CorrosionRate_mpy_F :=
  ⟨mmpy.val / 0.0254⟩

-- Angle conversions
def degreesToRadians_F (deg : ContactAngle_F) : Float :=
  deg.val * pi_F / 180.0

def radiansToDegrees_F (rad : Float) : ContactAngle_F :=
  ⟨rad * 180.0 / pi_F⟩

-- Film thickness conversions
def nmToAngstrom_F (nm : FilmThickness_F) : Float :=
  nm.val * 10.0

def angstromToNm_F (a : Float) : FilmThickness_F :=
  ⟨a / 10.0⟩

-- Temperature conversions
def celsiusToKelvin_F (c : Float) : Float :=
  c + 273.15

def kelvinToCelsius_F (k : Float) : Float :=
  k - 273.15

-- Homologous temperature
def homologousTemp_F (t : Float) (tm : Float) : HomologousTemp_F :=
  ⟨t / tm⟩

/--
================================================================================================
   Common Materials Calculations
================================================================================================
-/

-- Hall-Petch relation: σy = σ0 + k/√d
def hallPetch_F (sigma0 : Float) (k : Float) (d : GrainDiameter_F) : Float :=
  sigma0 + k / Float.sqrt (d.val / 1000.0)  -- Convert μm to mm

-- Arrhenius diffusion: D = D0 * exp(-Ea/RT)
def arrheniusDiffusion_F (d0 : DiffusionD0_F) (ea : DiffusionEa_F) (t : Float) : Diffusivity_F :=
  let r := 8.314  -- J/(mol·K)
  ⟨d0.val * Float.exp (-ea.val * 1000.0 / (r * t))⟩

-- d-spacing for cubic crystals
def dSpacingCubic_F (a : LatticeParam_a_F) (m : MillerIndex) : DSpacing_F :=
  let h2k2l2 := (m.h.toNat.toFloat)^2 + (m.k.toNat.toFloat)^2 + (m.l.toNat.toFloat)^2
  if h2k2l2 > 0.0 then
    ⟨a.val / Float.sqrt h2k2l2⟩
  else
    ⟨0.0⟩

-- Bragg's law: λ = 2d sinθ
def braggWavelength_F (d : DSpacing_F) (theta : Float) : Float :=
  2.0 * d.val * Float.sin (theta * pi_F / 180.0)

-- Atomic packing factor for FCC
def packingFactorFCC : PackingFactor_F :=
  ⟨0.74⟩  -- π/(3√2)

-- Atomic packing factor for BCC
def packingFactorBCC : PackingFactor_F :=
  ⟨0.68⟩  -- π√3/8

-- Atomic packing factor for simple cubic
def packingFactorSC : PackingFactor_F :=
  ⟨0.52⟩  -- π/6

-- Rule of mixtures for composites (upper bound)
def ruleOfMixtures_F (e_fiber : Float) (e_matrix : Float) (vf : FiberVolumeFraction_F)
    : Float :=
  e_fiber * vf.val + e_matrix * (1.0 - vf.val)

-- Inverse rule of mixtures (lower bound)
def inverseRuleOfMixtures_F (e_fiber : Float) (e_matrix : Float) (vf : FiberVolumeFraction_F)
    : Float :=
  1.0 / (vf.val / e_fiber + (1.0 - vf.val) / e_matrix)

-- Critical fiber length
def criticalFiberLength_F (sigma_f : Float) (d : Float) (tau : InterfaceStrength_F)
    : CriticalFiberLength_F :=
  ⟨sigma_f * d / (2.0 * tau.val)⟩

-- Peierls stress (simplified)
def peierlsStress_F (g : Float) (b : BurgersVector_F) (w : Float) : Float :=
  -- G: shear modulus, b: Burgers vector, w: dislocation width
  2.0 * g * Float.exp (-2.0 * pi_F * w / b.val)

-- Griffith criterion for brittle fracture
def griffithStress_F (e : Float) (gamma : SurfaceEnergy_F) (a : Float) : Float :=
  -- E: Young's modulus, γ: surface energy, a: crack length
  Float.sqrt (2.0 * e * gamma.val / (pi_F * a))

-- Work of adhesion (Young-Dupré equation)
def workOfAdhesion_F (gamma_l : SurfaceEnergy_F) (theta : ContactAngle_F)
    : WorkOfAdhesion_F :=
  ⟨gamma_l.val * (1.0 + Float.cos (theta.val * pi_F / 180.0))⟩

-- Wenzel roughness factor
def wenzelFactor_F (theta_rough : ContactAngle_F) (theta_smooth : ContactAngle_F) : Float :=
  Float.cos (theta_rough.val * pi_F / 180.0) / Float.cos (theta_smooth.val * pi_F / 180.0)

-- Steady-state creep rate (power law)
def creepRate_F (a : Float) (sigma : Float) (n : CreepExponent_F) (q : Float) (t : Float)
    : CreepRate_F :=
  -- A: constant, σ: stress, n: stress exponent, Q: activation energy, T: temperature
  let r := 8.314
  ⟨a * (sigma ^ n.val) * Float.exp (-q / (r * t))⟩

-- Paris law for fatigue crack growth
def parisLaw_F (c : ParisC_F) (m : ParisM_F) (deltaK : Float) : Float :=
  -- da/dN = C * (ΔK)^m
  c.val * (deltaK ^ m.val)

-- Weibull failure probability
def weibullProbability_F (sigma : Float) (sigma0 : Float) (m : WeibullModulus_F) : Float :=
  1.0 - Float.exp (-(sigma / sigma0) ^ m.val)

-- Carrier concentration (intrinsic semiconductor)
def intrinsicCarriers_F (nc : Float) (nv : Float) (eg : BandGap_F) (t : Float) : Float :=
  -- nc, nv: effective density of states, Eg: band gap, T: temperature
  let kb := 8.617e-5  -- eV/K
  Float.sqrt (nc * nv) * Float.exp (-eg.val / (2.0 * kb * t))

-- Electrical conductivity from carriers
def conductivity_F (n : ElectronDensity_F) (mu_n : ElectronMobility_F)
    (p : HoleDensity_F) (mu_p : HoleMobility_F) : Float :=
  let e := 1.602e-19  -- Elementary charge
  e * (n.val * mu_n.val + p.val * mu_p.val)

-- Tafel equation for corrosion
def tafelCurrent_F (i0 : Float) (eta : Float) (beta : TafelSlope_F) : Float :=
  -- i0: exchange current, η: overpotential, β: Tafel slope
  i0 * Float.exp (eta / (beta.val / 1000.0))

-- Corrosion rate from current density
def corrosionRateFromCurrent_F (i : Float) (m : Float) (n : Float) (rho : Float)
    : CorrosionRate_mmpy_F :=
  -- i: current density (μA/cm²), M: molecular weight, n: electrons, ρ: density
  ⟨0.00327 * i * m / (n * rho)⟩

-- Magnetocrystalline anisotropy energy
def anisotropyEnergy_F (k : AnisotropyConst_F) (theta : Float) : Float :=
  k.val * (Float.sin theta) ^ 2

-- Domain wall width
def domainWallWidth_F (a : ExchangeStiffness_F) (k : AnisotropyConst_F) : Float :=
  pi_F * Float.sqrt (a.val / k.val)

-- Curie-Weiss law
def curieWeissSusceptibility_F (c : Float) (t : Float) (tc : CurieTemp_F) : Float :=
  -- C: Curie constant, T: temperature, Tc: Curie temperature
  if t > tc.val then
    c / (t - tc.val)
  else
    1e10  -- Large value for ferromagnetic state

end Units.Materials
