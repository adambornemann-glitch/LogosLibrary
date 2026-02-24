-- Metallurgy.lean       -- Additive and subtractive metallurgical processing
import LogosLibrary.Units.Core
import LogosLibrary.Units.Mechanics
import LogosLibrary.Units.Thermal
import LogosLibrary.Units.Materials
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

namespace Units.Metallurgy

open Units.SI Units.Mechanics Units.Thermal Units.Materials

/-
================================================================================
METALLURGY UNITS LIBRARY
================================================================================

This module provides type-safe units for additive and subtractive metallurgical
processing: welding, casting, additive manufacturing, machining, surface
treatment, and joining. Following the triple-type architecture for maximum
flexibility without type conversion friction.

## COVERAGE

### Additive / Constructive Processes
- Welding (heat input, HAZ, dilution, preheat, interpass, weld geometry)
- Casting (superheat, fluidity, solidification, Chvorinov, riser design)
- Additive manufacturing (laser/electron beam parameters, energy density,
  build rate, scan strategy, powder characteristics)
- Brazing and soldering (joint clearance, wetting, capillary flow)
- Thermal spraying (particle velocity, deposition efficiency, splat)
- Electroplating and electroforming (current density, throwing power)
- Carburizing, nitriding, and thermochemical treatment (case depth,
  carbon potential, nitrogen potential, diffusion profiles)
- Sintering (densification, shrinkage, neck growth)
- Cladding (dilution, bond strength, overlay thickness)

### Subtractive / Removal Processes
- Machining (cutting speed, feed, depth of cut, MRR, specific energy,
  chip morphology, tool geometry)
- Grinding (wheel parameters, specific grinding energy, burn threshold)
- EDM (discharge energy, pulse parameters, electrode wear)
- ECM (current density, electrolyte flow, gap voltage)
- Chemical milling and etching (etch rate, etch factor, undercut)
- Laser cutting (kerf, assist gas, piercing)
- Waterjet cutting (pressure, abrasive parameters, standoff)
- Electropolishing (current density, surface finish improvement)

### Solidification and Thermal Processing
- Solidification parameters (thermal gradient, growth velocity, G/R ratio)
- Nucleation and grain refinement (undercooling, inoculant efficiency)
- Heat treatment response (Jominy, CCT/TTT, tempering parameter)
- Residual stress and distortion (eigenstrain, stress relief)

## USAGE PATTERNS
Float: Process monitoring, machine parameters, quality control, weld inspection,
NDT measurements, surface finish readings, production rates, tool wear tracking,
CNC programming values, real-time sensor data, shop-floor calculations

ℚ: Stoichiometric dilution ratios, exact alloy compositions, gear ratios in
drive trains, integer-related process parameters (number of passes, layers),
exact geometric ratios (step-over fractions, overlap ratios), crystallographic
orientation relationships (Kurdjumov-Sachs, Nishiyama-Wassermann)

ℝ: Continuum heat transfer modeling, solidification theory, diffusion
calculations, residual stress analysis, FEA boundary conditions, constitutive
modeling of material removal, thermodynamic driving forces, phase field
simulation parameters, analytical solutions to moving heat source problems
-/

set_option autoImplicit false
set_option linter.unusedVariables false

/--
================================================================================================
   Mathematical and Physical Constants for Metallurgy
================================================================================================
-/
def pi_F : Float := 3.14159265358979323846
def stefanBoltzmann_F : Float := 5.670374419e-8  -- W/(m²·K⁴)
def boltzmann_F : Float := 1.380649e-23           -- J/K
def R_gas_F : Float := 8.314462618                -- J/(mol·K)
def faraday_F : Float := 96485.33212              -- C/mol

/--
================================================================================================
   Welding Parameters
================================================================================================
-/

-- Arc/beam voltage
structure WeldVoltage_F where val : Float deriving Repr, BEq, Inhabited  -- V
structure WeldVoltage_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WeldVoltage_R where val : ℝ     deriving Inhabited

-- Welding current
structure WeldCurrent_F where val : Float deriving Repr, BEq, Inhabited  -- A
structure WeldCurrent_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WeldCurrent_R where val : ℝ     deriving Inhabited

-- Travel speed
structure TravelSpeed_F where val : Float deriving Repr, BEq, Inhabited  -- mm/s
structure TravelSpeed_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TravelSpeed_R where val : ℝ     deriving Inhabited

-- Wire feed rate
structure WireFeedRate_F where val : Float deriving Repr, BEq, Inhabited  -- m/min
structure WireFeedRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WireFeedRate_R where val : ℝ     deriving Inhabited

-- Heat input (arc energy per unit length)
structure HeatInput_F  where val : Float deriving Repr, BEq, Inhabited  -- kJ/mm
structure HeatInput_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HeatInput_R  where val : ℝ     deriving Inhabited

-- Arc efficiency factor (η)
structure ArcEfficiency_F where val : Float deriving Repr, BEq, Inhabited  -- dimensionless
structure ArcEfficiency_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ArcEfficiency_R where val : ℝ     deriving Inhabited

-- Preheat temperature
structure PreheatTemp_F where val : Float deriving Repr, BEq, Inhabited  -- °C
structure PreheatTemp_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PreheatTemp_R where val : ℝ     deriving Inhabited

-- Interpass temperature
structure InterpassTemp_F where val : Float deriving Repr, BEq, Inhabited  -- °C
structure InterpassTemp_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure InterpassTemp_R where val : ℝ     deriving Inhabited

-- Weld dilution (fraction of base metal in weld pool)
structure WeldDilution_F where val : Float deriving Repr, BEq, Inhabited  -- fraction
structure WeldDilution_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WeldDilution_R where val : ℝ     deriving Inhabited

-- Heat affected zone width
structure HAZWidth_F   where val : Float deriving Repr, BEq, Inhabited  -- mm
structure HAZWidth_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HAZWidth_R   where val : ℝ     deriving Inhabited

-- Weld bead geometry
structure BeadWidth_F  where val : Float deriving Repr, BEq, Inhabited  -- mm
structure BeadHeight_F where val : Float deriving Repr, BEq, Inhabited  -- mm
structure Penetration_F where val : Float deriving Repr, BEq, Inhabited  -- mm

-- Cooling time (Δt₈₋₅: time to cool 800→500°C)
structure CoolingTime_8_5_F where val : Float deriving Repr, BEq, Inhabited  -- s
structure CoolingTime_8_5_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CoolingTime_8_5_R where val : ℝ     deriving Inhabited

-- Carbon equivalent (weldability)
structure CarbonEquivalent_F where val : Float deriving Repr, BEq, Inhabited
structure CarbonEquivalent_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CarbonEquivalent_R where val : ℝ     deriving Inhabited

-- Welding process types
inductive WeldProcess
  | SMAW    -- Shielded metal arc (stick)
  | GMAW    -- Gas metal arc (MIG/MAG)
  | GTAW    -- Gas tungsten arc (TIG)
  | FCAW    -- Flux-cored arc
  | SAW     -- Submerged arc
  | PAW     -- Plasma arc
  | EBW     -- Electron beam
  | LBW     -- Laser beam
  | FSW     -- Friction stir
  | RSW     -- Resistance spot
  | ERW     -- Electric resistance
  deriving Repr, BEq, DecidableEq

-- Shielding gas composition
structure ShieldGasFlow_F where val : Float deriving Repr, BEq, Inhabited  -- L/min

-- Joint types
inductive JointType
  | Butt | Lap | Tee | Corner | Edge
  deriving Repr, BEq, DecidableEq

-- Weld position (AWS)
inductive WeldPosition
  | Flat_1G | Horizontal_2G | Vertical_3G | Overhead_4G
  | Flat_1F | Horizontal_2F | Vertical_3F | Overhead_4F
  | Pipe_5G | Pipe_6G | Pipe_6GR
  deriving Repr, BEq, DecidableEq

/--
================================================================================================
   Casting Parameters
================================================================================================
-/

-- Superheat (temperature above liquidus)
structure Superheat_F  where val : Float deriving Repr, BEq, Inhabited  -- °C or K
structure Superheat_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Superheat_R  where val : ℝ     deriving Inhabited

-- Pouring temperature
structure PouringTemp_F where val : Float deriving Repr, BEq, Inhabited  -- °C
structure PouringTemp_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PouringTemp_R where val : ℝ     deriving Inhabited

-- Mold temperature
structure MoldTemp_F   where val : Float deriving Repr, BEq, Inhabited  -- °C
structure MoldTemp_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MoldTemp_R   where val : ℝ     deriving Inhabited

-- Fluidity (spiral test length)
structure Fluidity_F   where val : Float deriving Repr, BEq, Inhabited  -- mm
structure Fluidity_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Fluidity_R   where val : ℝ     deriving Inhabited

-- Solidification time
structure SolidificationTime_F where val : Float deriving Repr, BEq, Inhabited  -- s
structure SolidificationTime_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SolidificationTime_R where val : ℝ     deriving Inhabited

-- Chvorinov mold constant
structure ChvorinovConst_F where val : Float deriving Repr, BEq, Inhabited  -- s/mm²
structure ChvorinovConst_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ChvorinovConst_R where val : ℝ     deriving Inhabited

-- Volume-to-surface-area ratio (modulus)
structure CastingModulus_F where val : Float deriving Repr, BEq, Inhabited  -- mm
structure CastingModulus_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CastingModulus_R where val : ℝ     deriving Inhabited

-- Shrinkage (volumetric)
structure SolidificationShrinkage_F where val : Float deriving Repr, BEq, Inhabited  -- fraction
structure SolidificationShrinkage_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SolidificationShrinkage_R where val : ℝ     deriving Inhabited

-- Riser modulus ratio (riser/casting)
structure RiserModulusRatio_F where val : Float deriving Repr, BEq, Inhabited
structure RiserModulusRatio_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RiserModulusRatio_R where val : ℝ     deriving Inhabited

-- Feeding distance
structure FeedingDistance_F where val : Float deriving Repr, BEq, Inhabited  -- mm
structure FeedingDistance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FeedingDistance_R where val : ℝ     deriving Inhabited

-- DAS (dendrite arm spacing)
structure DendriteArmSpacing_F where val : Float deriving Repr, BEq, Inhabited  -- μm
structure DendriteArmSpacing_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DendriteArmSpacing_R where val : ℝ     deriving Inhabited

-- Casting process types
inductive CastingProcess
  | Sand | Investment | DieCast_HotChamber | DieCast_ColdChamber
  | Permanent | Centrifugal | ContinuousCast | LostFoam
  | ShellMold | Squeeze | Semisolid
  deriving Repr, BEq, DecidableEq

/--
================================================================================================
   Additive Manufacturing Parameters
================================================================================================
-/

-- Laser/beam power
structure BeamPower_F  where val : Float deriving Repr, BEq, Inhabited  -- W
structure BeamPower_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BeamPower_R  where val : ℝ     deriving Inhabited

-- Scan speed
structure ScanSpeed_F  where val : Float deriving Repr, BEq, Inhabited  -- mm/s
structure ScanSpeed_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ScanSpeed_R  where val : ℝ     deriving Inhabited

-- Layer thickness
structure LayerThickness_F where val : Float deriving Repr, BEq, Inhabited  -- μm
structure LayerThickness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LayerThickness_R where val : ℝ     deriving Inhabited

-- Hatch spacing
structure HatchSpacing_F where val : Float deriving Repr, BEq, Inhabited  -- μm
structure HatchSpacing_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HatchSpacing_R where val : ℝ     deriving Inhabited

-- Beam spot diameter
structure SpotDiameter_F where val : Float deriving Repr, BEq, Inhabited  -- μm
structure SpotDiameter_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpotDiameter_R where val : ℝ     deriving Inhabited

-- Volumetric energy density
structure VolumetricEnergyDensity_F where val : Float deriving Repr, BEq, Inhabited  -- J/mm³
structure VolumetricEnergyDensity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VolumetricEnergyDensity_R where val : ℝ     deriving Inhabited

-- Linear energy density
structure LinearEnergyDensity_F where val : Float deriving Repr, BEq, Inhabited  -- J/mm
structure LinearEnergyDensity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LinearEnergyDensity_R where val : ℝ     deriving Inhabited

-- Build rate
structure BuildRate_F  where val : Float deriving Repr, BEq, Inhabited  -- cm³/hr
structure BuildRate_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BuildRate_R  where val : ℝ     deriving Inhabited

-- Powder characteristics
structure PowderD50_F  where val : Float deriving Repr, BEq, Inhabited  -- μm (median)
structure PowderD10_F  where val : Float deriving Repr, BEq, Inhabited  -- μm
structure PowderD90_F  where val : Float deriving Repr, BEq, Inhabited  -- μm
structure PowderFlowability_F where val : Float deriving Repr, BEq, Inhabited  -- s (Hall flow)
structure ApparentDensity_F where val : Float deriving Repr, BEq, Inhabited  -- % of theoretical
structure TapDensity_F where val : Float deriving Repr, BEq, Inhabited  -- % of theoretical

-- Hausner ratio (tap density / apparent density)
structure HausnerRatio_F where val : Float deriving Repr, BEq, Inhabited
structure HausnerRatio_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HausnerRatio_R where val : ℝ     deriving Inhabited

-- Melt pool dimensions
structure MeltPoolLength_F where val : Float deriving Repr, BEq, Inhabited  -- μm
structure MeltPoolWidth_F  where val : Float deriving Repr, BEq, Inhabited  -- μm
structure MeltPoolDepth_F  where val : Float deriving Repr, BEq, Inhabited  -- μm

-- Relative density (of built part)
structure RelativeDensity_F where val : Float deriving Repr, BEq, Inhabited  -- fraction
structure RelativeDensity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RelativeDensity_R where val : ℝ     deriving Inhabited

-- Scan strategy
inductive ScanStrategy
  | Raster | Island | Stripe | Chessboard | Spiral | Contour
  deriving Repr, BEq, DecidableEq

-- Scan rotation between layers
structure ScanRotation_F where val : Float deriving Repr, BEq, Inhabited  -- degrees
structure ScanRotation_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ScanRotation_R where val : ℝ     deriving Inhabited

-- AM process types
inductive AMProcess
  | SLM      -- Selective laser melting (LPBF)
  | EBM      -- Electron beam melting
  | DED_Laser -- Directed energy deposition (laser)
  | DED_Arc  -- Wire arc additive manufacturing (WAAM)
  | DED_EB   -- Electron beam wire feed
  | BJ       -- Binder jetting
  | SLS      -- Selective laser sintering
  | MJF      -- Multi jet fusion
  deriving Repr, BEq, DecidableEq

/--
================================================================================================
   Brazing and Soldering
================================================================================================
-/

-- Brazing temperature
structure BrazingTemp_F where val : Float deriving Repr, BEq, Inhabited  -- °C
structure BrazingTemp_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BrazingTemp_R where val : ℝ     deriving Inhabited

-- Joint clearance (gap)
structure JointClearance_F where val : Float deriving Repr, BEq, Inhabited  -- mm
structure JointClearance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JointClearance_R where val : ℝ     deriving Inhabited

-- Wetting angle (filler on substrate)
structure WettingAngle_F where val : Float deriving Repr, BEq, Inhabited  -- degrees
structure WettingAngle_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WettingAngle_R where val : ℝ     deriving Inhabited

-- Capillary rise
structure CapillaryRise_F where val : Float deriving Repr, BEq, Inhabited  -- mm
structure CapillaryRise_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CapillaryRise_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Thermal Spraying
================================================================================================
-/

-- Particle velocity
structure ParticleVelocity_F where val : Float deriving Repr, BEq, Inhabited  -- m/s
structure ParticleVelocity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ParticleVelocity_R where val : ℝ     deriving Inhabited

-- Standoff distance (spray gun to substrate)
structure StandoffDistance_F where val : Float deriving Repr, BEq, Inhabited  -- mm
structure StandoffDistance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure StandoffDistance_R where val : ℝ     deriving Inhabited

-- Deposition efficiency
structure DepositionEfficiency_F where val : Float deriving Repr, BEq, Inhabited  -- fraction
structure DepositionEfficiency_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DepositionEfficiency_R where val : ℝ     deriving Inhabited

-- Thermal spray process types
inductive ThermalSprayProcess
  | ArcSpray | FlameSpray | HVOF | HVAF | PlasmaSpray
  | Detonation | ColdSpray | WarmSpray
  deriving Repr, BEq, DecidableEq

/--
================================================================================================
   Electroplating and Surface Deposition
================================================================================================
-/

-- Plating current density
structure PlatingCurrentDensity_F where val : Float deriving Repr, BEq, Inhabited  -- A/dm²
structure PlatingCurrentDensity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PlatingCurrentDensity_R where val : ℝ     deriving Inhabited

-- Plating rate
structure PlatingRate_F where val : Float deriving Repr, BEq, Inhabited  -- μm/min
structure PlatingRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PlatingRate_R where val : ℝ     deriving Inhabited

-- Throwing power (uniformity)
structure ThrowingPower_F where val : Float deriving Repr, BEq, Inhabited  -- %
structure ThrowingPower_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ThrowingPower_R where val : ℝ     deriving Inhabited

-- Cathode efficiency
structure CathodeEfficiency_F where val : Float deriving Repr, BEq, Inhabited  -- fraction
structure CathodeEfficiency_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CathodeEfficiency_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Thermochemical Treatment (Carburizing, Nitriding, etc.)
================================================================================================
-/

-- Case depth (effective)
structure CaseDepth_F  where val : Float deriving Repr, BEq, Inhabited  -- mm
structure CaseDepth_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CaseDepth_R  where val : ℝ     deriving Inhabited

-- Total case depth
structure TotalCaseDepth_F where val : Float deriving Repr, BEq, Inhabited  -- mm
structure TotalCaseDepth_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TotalCaseDepth_R where val : ℝ     deriving Inhabited

-- Carbon potential
structure CarbonPotential_F where val : Float deriving Repr, BEq, Inhabited  -- wt% C
structure CarbonPotential_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CarbonPotential_R where val : ℝ     deriving Inhabited

-- Nitrogen potential
structure NitrogenPotential_F where val : Float deriving Repr, BEq, Inhabited  -- atm⁻¹/²
structure NitrogenPotential_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NitrogenPotential_R where val : ℝ     deriving Inhabited

-- Thermochemical process types
inductive ThermochemProcess
  | GasCarburizing | VacuumCarburizing | PlasmaCarburizing
  | GasNitriding | PlasmaGasNitriding | SaltBathNitriding
  | Carbonitriding | Nitrocarburizing
  | Boriding | Chromizing | Aluminizing
  deriving Repr, BEq, DecidableEq

/--
================================================================================================
   Sintering Parameters
================================================================================================
-/

-- Green density (before sintering)
structure GreenDensity_F where val : Float deriving Repr, BEq, Inhabited  -- % theoretical
structure GreenDensity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GreenDensity_R where val : ℝ     deriving Inhabited

-- Sintered density
structure SinteredDensity_F where val : Float deriving Repr, BEq, Inhabited  -- % theoretical
structure SinteredDensity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SinteredDensity_R where val : ℝ     deriving Inhabited

-- Linear shrinkage
structure LinearShrinkage_F where val : Float deriving Repr, BEq, Inhabited  -- fraction
structure LinearShrinkage_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LinearShrinkage_R where val : ℝ     deriving Inhabited

-- Neck size ratio (x/R in sintering models)
structure NeckRatio_F  where val : Float deriving Repr, BEq, Inhabited
structure NeckRatio_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NeckRatio_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Solidification Parameters
================================================================================================
-/

-- Thermal gradient at solid-liquid interface
structure ThermalGradient_F where val : Float deriving Repr, BEq, Inhabited  -- K/mm
structure ThermalGradient_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ThermalGradient_R where val : ℝ     deriving Inhabited

-- Solidification velocity (growth rate)
structure SolidificationVelocity_F where val : Float deriving Repr, BEq, Inhabited  -- mm/s
structure SolidificationVelocity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SolidificationVelocity_R where val : ℝ     deriving Inhabited

-- G/R ratio (morphology control parameter)
structure GRRatio_F    where val : Float deriving Repr, BEq, Inhabited  -- K·s/mm²
structure GRRatio_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GRRatio_R    where val : ℝ     deriving Inhabited

-- G×R product (cooling rate at interface)
structure GRProduct_F  where val : Float deriving Repr, BEq, Inhabited  -- K/s
structure GRProduct_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GRProduct_R  where val : ℝ     deriving Inhabited

-- Undercooling
structure Undercooling_F where val : Float deriving Repr, BEq, Inhabited  -- K
structure Undercooling_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Undercooling_R where val : ℝ     deriving Inhabited

-- Constitutional supercooling parameter
structure ConstitutionalSC_F where val : Float deriving Repr, BEq, Inhabited  -- K·s/mm²
structure ConstitutionalSC_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ConstitutionalSC_R where val : ℝ     deriving Inhabited

-- Partition coefficient (k₀)
structure PartitionCoeff_F where val : Float deriving Repr, BEq, Inhabited
structure PartitionCoeff_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PartitionCoeff_R where val : ℝ     deriving Inhabited

-- Liquidus slope (m)
structure LiquidusSlope_F where val : Float deriving Repr, BEq, Inhabited  -- K/wt%
structure LiquidusSlope_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LiquidusSlope_R where val : ℝ     deriving Inhabited

-- Solidification morphology
inductive SolidificationMorphology
  | Planar | Cellular | ColumnarDendritic | EquiaxedDendritic
  deriving Repr, BEq, DecidableEq

/--
================================================================================================
   Heat Treatment Response
================================================================================================
-/

-- Jominy distance
structure JominyDistance_F where val : Float deriving Repr, BEq, Inhabited  -- mm (1/16 in.)
structure JominyDistance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JominyDistance_R where val : ℝ     deriving Inhabited

-- Hardenability (ideal critical diameter)
structure IdealCritDiameter_F where val : Float deriving Repr, BEq, Inhabited  -- mm
structure IdealCritDiameter_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure IdealCritDiameter_R where val : ℝ     deriving Inhabited

-- Severity of quench (Grossmann H-value)
structure QuenchSeverity_F where val : Float deriving Repr, BEq, Inhabited  -- in⁻¹
structure QuenchSeverity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure QuenchSeverity_R where val : ℝ     deriving Inhabited

-- Tempering parameter (Hollomon-Jaffe)
structure TemperingParam_F where val : Float deriving Repr, BEq, Inhabited  -- T(C + log t) × 10⁻³
structure TemperingParam_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TemperingParam_R where val : ℝ     deriving Inhabited

-- Ms temperature (martensite start)
structure MsTemp_F     where val : Float deriving Repr, BEq, Inhabited  -- °C
structure MsTemp_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MsTemp_R     where val : ℝ     deriving Inhabited

-- Mf temperature (martensite finish)
structure MfTemp_F     where val : Float deriving Repr, BEq, Inhabited  -- °C
structure MfTemp_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MfTemp_R     where val : ℝ     deriving Inhabited

/--
================================================================================================
   Machining Parameters (Subtractive)
================================================================================================
-/

-- Cutting speed
structure CuttingSpeed_F where val : Float deriving Repr, BEq, Inhabited  -- m/min
structure CuttingSpeed_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CuttingSpeed_R where val : ℝ     deriving Inhabited

-- Spindle speed
structure SpindleSpeed_F where val : Float deriving Repr, BEq, Inhabited  -- RPM
structure SpindleSpeed_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpindleSpeed_R where val : ℝ     deriving Inhabited

-- Feed rate
structure FeedRate_F   where val : Float deriving Repr, BEq, Inhabited  -- mm/rev
structure FeedRate_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FeedRate_R   where val : ℝ     deriving Inhabited

-- Feed per tooth
structure FeedPerTooth_F where val : Float deriving Repr, BEq, Inhabited  -- mm/tooth
structure FeedPerTooth_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FeedPerTooth_R where val : ℝ     deriving Inhabited

-- Depth of cut
structure DepthOfCut_F where val : Float deriving Repr, BEq, Inhabited  -- mm
structure DepthOfCut_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DepthOfCut_R where val : ℝ     deriving Inhabited

-- Width of cut
structure WidthOfCut_F where val : Float deriving Repr, BEq, Inhabited  -- mm
structure WidthOfCut_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WidthOfCut_R where val : ℝ     deriving Inhabited

-- Material removal rate
structure MRR_F        where val : Float deriving Repr, BEq, Inhabited  -- mm³/min
structure MRR_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MRR_R        where val : ℝ     deriving Inhabited

-- Specific cutting energy
structure SpecificCuttingEnergy_F where val : Float deriving Repr, BEq, Inhabited  -- J/mm³
structure SpecificCuttingEnergy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpecificCuttingEnergy_R where val : ℝ     deriving Inhabited

-- Cutting force components
structure CuttingForce_F where val : Float deriving Repr, BEq, Inhabited  -- N
structure ThrustForce_F  where val : Float deriving Repr, BEq, Inhabited  -- N
structure FeedForce_F    where val : Float deriving Repr, BEq, Inhabited  -- N

-- Tool rake angle
structure RakeAngle_F  where val : Float deriving Repr, BEq, Inhabited  -- degrees
structure RakeAngle_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RakeAngle_R  where val : ℝ     deriving Inhabited

-- Tool clearance angle
structure ClearanceAngle_F where val : Float deriving Repr, BEq, Inhabited  -- degrees
structure ClearanceAngle_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ClearanceAngle_R where val : ℝ     deriving Inhabited

-- Nose radius
structure NoseRadius_F where val : Float deriving Repr, BEq, Inhabited  -- mm
structure NoseRadius_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NoseRadius_R where val : ℝ     deriving Inhabited

-- Tool wear (flank wear land)
structure FlankWear_F  where val : Float deriving Repr, BEq, Inhabited  -- mm
structure FlankWear_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FlankWear_R  where val : ℝ     deriving Inhabited

-- Crater wear depth
structure CraterWear_F where val : Float deriving Repr, BEq, Inhabited  -- mm

-- Tool life
structure ToolLife_F   where val : Float deriving Repr, BEq, Inhabited  -- min
structure ToolLife_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ToolLife_R   where val : ℝ     deriving Inhabited

-- Taylor exponent (n in VTⁿ = C)
structure TaylorExponent_F where val : Float deriving Repr, BEq, Inhabited
structure TaylorExponent_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TaylorExponent_R where val : ℝ     deriving Inhabited

-- Taylor constant
structure TaylorConstant_F where val : Float deriving Repr, BEq, Inhabited  -- m/min
structure TaylorConstant_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TaylorConstant_R where val : ℝ     deriving Inhabited

-- Chip thickness ratio
structure ChipThicknessRatio_F where val : Float deriving Repr, BEq, Inhabited
structure ChipThicknessRatio_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ChipThicknessRatio_R where val : ℝ     deriving Inhabited

-- Shear angle (Merchant)
structure ShearAngle_F where val : Float deriving Repr, BEq, Inhabited  -- degrees
structure ShearAngle_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ShearAngle_R where val : ℝ     deriving Inhabited

-- Machinability rating
structure MachinabilityRating_F where val : Float deriving Repr, BEq, Inhabited  -- % vs AISI 1212
structure MachinabilityRating_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MachinabilityRating_R where val : ℝ     deriving Inhabited

-- Chip morphology
inductive ChipType
  | Continuous | ContinuousWithBUE | Segmented | Discontinuous
  deriving Repr, BEq, DecidableEq

/--
================================================================================================
   Grinding Parameters (Subtractive)
================================================================================================
-/

-- Wheel speed
structure WheelSpeed_F where val : Float deriving Repr, BEq, Inhabited  -- m/s
structure WheelSpeed_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WheelSpeed_R where val : ℝ     deriving Inhabited

-- Specific grinding energy
structure SpecificGrindingEnergy_F where val : Float deriving Repr, BEq, Inhabited  -- J/mm³
structure SpecificGrindingEnergy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpecificGrindingEnergy_R where val : ℝ     deriving Inhabited

-- Equivalent chip thickness
structure EquivChipThickness_F where val : Float deriving Repr, BEq, Inhabited  -- μm
structure EquivChipThickness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EquivChipThickness_R where val : ℝ     deriving Inhabited

-- Grinding ratio (G-ratio: material removed / wheel worn)
structure GrindingRatio_F where val : Float deriving Repr, BEq, Inhabited
structure GrindingRatio_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GrindingRatio_R where val : ℝ     deriving Inhabited

-- Grinding burn threshold
structure BurnThreshold_F where val : Float deriving Repr, BEq, Inhabited  -- J/mm²

/--
================================================================================================
   EDM Parameters (Subtractive)
================================================================================================
-/

-- Discharge energy per pulse
structure DischargeEnergy_F where val : Float deriving Repr, BEq, Inhabited  -- mJ
structure DischargeEnergy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DischargeEnergy_R where val : ℝ     deriving Inhabited

-- Pulse on-time
structure PulseOnTime_F where val : Float deriving Repr, BEq, Inhabited  -- μs
structure PulseOnTime_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PulseOnTime_R where val : ℝ     deriving Inhabited

-- Pulse off-time
structure PulseOffTime_F where val : Float deriving Repr, BEq, Inhabited  -- μs
structure PulseOffTime_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PulseOffTime_R where val : ℝ     deriving Inhabited

-- Duty factor
structure DutyFactor_F where val : Float deriving Repr, BEq, Inhabited  -- fraction
structure DutyFactor_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DutyFactor_R where val : ℝ     deriving Inhabited

-- Gap voltage
structure GapVoltage_F where val : Float deriving Repr, BEq, Inhabited  -- V

-- Electrode wear ratio
structure ElectrodeWearRatio_F where val : Float deriving Repr, BEq, Inhabited  -- %
structure ElectrodeWearRatio_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ElectrodeWearRatio_R where val : ℝ     deriving Inhabited

-- White layer thickness (recast layer)
structure WhiteLayerThickness_F where val : Float deriving Repr, BEq, Inhabited  -- μm
structure WhiteLayerThickness_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WhiteLayerThickness_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   ECM Parameters (Subtractive)
================================================================================================
-/

-- Machining gap
structure ECMGap_F     where val : Float deriving Repr, BEq, Inhabited  -- mm
structure ECMGap_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ECMGap_R     where val : ℝ     deriving Inhabited

-- ECM current density
structure ECMCurrentDensity_F where val : Float deriving Repr, BEq, Inhabited  -- A/cm²
structure ECMCurrentDensity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ECMCurrentDensity_R where val : ℝ     deriving Inhabited

-- Electrolyte flow rate
structure ElectrolyteFlow_F where val : Float deriving Repr, BEq, Inhabited  -- L/min

-- Specific removal rate (Faraday-based)
structure ECMSpecificRemoval_F where val : Float deriving Repr, BEq, Inhabited  -- mm³/(A·min)
structure ECMSpecificRemoval_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ECMSpecificRemoval_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Chemical Milling and Etching (Subtractive)
================================================================================================
-/

-- Etch rate
structure EtchRate_F   where val : Float deriving Repr, BEq, Inhabited  -- μm/min
structure EtchRate_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EtchRate_R   where val : ℝ     deriving Inhabited

-- Etch factor (depth/undercut)
structure EtchFactor_F where val : Float deriving Repr, BEq, Inhabited
structure EtchFactor_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EtchFactor_R where val : ℝ     deriving Inhabited

-- Undercut distance
structure Undercut_F   where val : Float deriving Repr, BEq, Inhabited  -- μm
structure Undercut_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Undercut_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Laser Cutting (Subtractive)
================================================================================================
-/

-- Kerf width
structure KerfWidth_F  where val : Float deriving Repr, BEq, Inhabited  -- mm
structure KerfWidth_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KerfWidth_R  where val : ℝ     deriving Inhabited

-- Assist gas pressure
structure AssistGasPressure_F where val : Float deriving Repr, BEq, Inhabited  -- bar
structure AssistGasPressure_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AssistGasPressure_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Waterjet Cutting (Subtractive)
================================================================================================
-/

-- Water pressure
structure WaterjetPressure_F where val : Float deriving Repr, BEq, Inhabited  -- MPa
structure WaterjetPressure_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WaterjetPressure_R where val : ℝ     deriving Inhabited

-- Abrasive flow rate
structure AbrasiveFlowRate_F where val : Float deriving Repr, BEq, Inhabited  -- g/min
structure AbrasiveFlowRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AbrasiveFlowRate_R where val : ℝ     deriving Inhabited

-- Orifice diameter
structure OrificeDiameter_F where val : Float deriving Repr, BEq, Inhabited  -- mm
structure OrificeDiameter_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure OrificeDiameter_R where val : ℝ     deriving Inhabited

-- Mixing tube diameter
structure MixingTubeDiameter_F where val : Float deriving Repr, BEq, Inhabited  -- mm
structure MixingTubeDiameter_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MixingTubeDiameter_R where val : ℝ     deriving Inhabited

-- Taper angle (waterjet cut quality)
structure TaperAngle_F where val : Float deriving Repr, BEq, Inhabited  -- degrees

/--
================================================================================================
   Weld and Process Defects
================================================================================================
-/

inductive WeldDefect
  | Porosity | Slag | LackOfFusion | LackOfPenetration
  | Undercut | Overlap | Spatter | HotCrack | ColdCrack
  | LamellarTear | HydrogenEmbrittlement
  deriving Repr, BEq, DecidableEq

inductive AMDefect
  | GasPorosity | LackOfFusion | Balling | Keyholing
  | Delamination | Warping | SupportFailure
  | UnmeltedPowder | Cracking | SurfaceRoughness
  deriving Repr, BEq, DecidableEq

inductive CastingDefect
  | Shrinkage | GasPorosity | Misrun | ColdShut
  | HotTear | Inclusion | Segregation | Blowhole
  | MetalPenetration | SandInclusion | Scab
  deriving Repr, BEq, DecidableEq

inductive MachiningDefect
  | Chatter | BuiltUpEdge | BurrFormation | SurfaceTearing
  | ThermalDamage | WhiteLayer | WorkHardening | Smearing
  deriving Repr, BEq, DecidableEq

/--
================================================================================================
   Validation Helpers
================================================================================================
-/

-- Welding validation
def isValidHeatInput_F (hi : HeatInput_F) : Bool :=
  hi.val > 0.0 && hi.val < 100.0  -- kJ/mm, practical range

def isValidArcEfficiency_F (eta : ArcEfficiency_F) : Bool :=
  0.0 < eta.val && eta.val ≤ 1.0

def isValidDilution_F (d : WeldDilution_F) : Bool :=
  0.0 ≤ d.val && d.val ≤ 1.0

def isValidCarbonEquivalent_F (ce : CarbonEquivalent_F) : Bool :=
  0.0 ≤ ce.val && ce.val < 2.0

-- Casting validation
def isValidShrinkage_F (s : SolidificationShrinkage_F) : Bool :=
  0.0 ≤ s.val && s.val < 0.10  -- Most metals < 7% vol shrinkage

def isValidRiserRatio_F (r : RiserModulusRatio_F) : Bool :=
  r.val > 1.0  -- Riser must solidify after casting

-- AM validation
def isValidRelativeDensity_F (rd : RelativeDensity_F) : Bool :=
  0.0 < rd.val && rd.val ≤ 1.0

def isValidEnergyDensity_F (ed : VolumetricEnergyDensity_F) : Bool :=
  ed.val > 0.0 && ed.val < 1000.0  -- J/mm³, practical range

def isValidHausnerRatio_F (h : HausnerRatio_F) : Bool :=
  h.val ≥ 1.0 && h.val < 2.0  -- ≤1.25 = good flow

-- Machining validation
def isValidRakeAngle_F (r : RakeAngle_F) : Bool :=
  -30.0 ≤ r.val && r.val ≤ 45.0

def isValidFlankWear_F (w : FlankWear_F) (limit : Float := 0.3) : Bool :=
  0.0 ≤ w.val && w.val ≤ limit  -- mm, ISO 3685 criterion

def isValidTaylorExponent_F (n : TaylorExponent_F) : Bool :=
  0.0 < n.val && n.val < 1.0  -- Typically 0.1–0.9

-- EDM validation
def isValidDutyFactor_F (df : DutyFactor_F) : Bool :=
  0.0 < df.val && df.val < 1.0

-- Thermochemical validation
def isValidCarbonPotential_F (cp : CarbonPotential_F) : Bool :=
  0.0 < cp.val && cp.val ≤ 2.0  -- wt% C

-- Sintering validation
def isValidGreenDensity_F (gd : GreenDensity_F) : Bool :=
  30.0 ≤ gd.val && gd.val ≤ 99.0  -- % theoretical

-- Solidification validation
def isValidPartitionCoeff_F (k : PartitionCoeff_F) : Bool :=
  0.0 < k.val && k.val < 1.0  -- Most solutes in most solvents

-- Etch validation
def isValidEtchFactor_F (ef : EtchFactor_F) : Bool :=
  ef.val ≥ 1.0  -- Depth ≥ undercut for useful etching

/--
================================================================================================
   Unit Conversions
================================================================================================
-/

-- Heat input: Q = η·V·I / v  (kJ/mm)
def heatInput_F (eta : ArcEfficiency_F) (v : WeldVoltage_F) (i : WeldCurrent_F)
    (speed : TravelSpeed_F) : HeatInput_F :=
  ⟨eta.val * v.val * i.val / (speed.val * 1000.0)⟩

-- Volumetric energy density: E = P / (v · h · t)
def volumetricEnergyDensity_F (p : BeamPower_F) (v : ScanSpeed_F)
    (h : HatchSpacing_F) (t : LayerThickness_F) : VolumetricEnergyDensity_F :=
  ⟨p.val / (v.val * h.val * t.val * 1e-6)⟩  -- μm → mm conversion

-- Linear energy density: E_l = P / v
def linearEnergyDensity_F (p : BeamPower_F) (v : ScanSpeed_F) : LinearEnergyDensity_F :=
  ⟨p.val / v.val⟩

-- Build rate: BR = v · h · t
def buildRate_F (v : ScanSpeed_F) (h : HatchSpacing_F)
    (t : LayerThickness_F) : BuildRate_F :=
  ⟨v.val * h.val * t.val * 3.6e-3⟩  -- mm·μm·μm/s → cm³/hr

-- Cutting speed from RPM: V = π·D·N / 1000
def cuttingSpeedFromRPM_F (d : Float) (n : SpindleSpeed_F) : CuttingSpeed_F :=
  ⟨pi_F * d * n.val / 1000.0⟩

-- RPM from cutting speed
def rpmFromCuttingSpeed_F (v : CuttingSpeed_F) (d : Float) : SpindleSpeed_F :=
  ⟨v.val * 1000.0 / (pi_F * d)⟩

-- Material removal rate (turning): MRR = V · f · d
def mrrTurning_F (v : CuttingSpeed_F) (f : FeedRate_F) (d : DepthOfCut_F) : MRR_F :=
  ⟨v.val * f.val * d.val * 1000.0⟩  -- m/min · mm · mm → mm³/min

-- Material removal rate (milling): MRR = w · d · fz · z · N
def mrrMilling_F (w : WidthOfCut_F) (d : DepthOfCut_F) (fz : FeedPerTooth_F)
    (z : Nat) (n : SpindleSpeed_F) : MRR_F :=
  ⟨w.val * d.val * fz.val * z.toFloat * n.val⟩

-- Specific cutting energy: u = Fc · Vc / MRR
def specificCuttingEnergy_F (fc : CuttingForce_F) (v : CuttingSpeed_F)
    (mrr : MRR_F) : SpecificCuttingEnergy_F :=
  ⟨fc.val * v.val * 1000.0 / (60.0 * mrr.val)⟩  -- N·m/min → J, mm³/min

-- Hausner ratio
def hausnerRatio_F (tap : TapDensity_F) (apparent : ApparentDensity_F) : HausnerRatio_F :=
  ⟨tap.val / apparent.val⟩

-- Duty factor: t_on / (t_on + t_off)
def dutyFactor_F (ton : PulseOnTime_F) (toff : PulseOffTime_F) : DutyFactor_F :=
  ⟨ton.val / (ton.val + toff.val)⟩

-- ECM removal rate (Faraday's law): MRR = ηF · A · I / (z · F · ρ)
def ecmRemovalRate_F (eta : CathodeEfficiency_F) (atomicWeight : Float)
    (current : Float) (valence : Float) (density : Float) : Float :=
  eta.val * atomicWeight * current / (valence * faraday_F * density) * 1e6  -- mm³/s

/--
================================================================================================
   Common Metallurgical Calculations
================================================================================================
-/

-- Chvorinov's rule: t_s = B · (V/A)²
def chvorinovSolidificationTime_F (b : ChvorinovConst_F) (m : CastingModulus_F)
    : SolidificationTime_F :=
  ⟨b.val * m.val ^ 2⟩

-- Constitutional supercooling criterion: G/R ≥ ΔT₀/D
-- (planar front stability)
def constitutionalSCCriterion_F (g : ThermalGradient_F) (r : SolidificationVelocity_F)
    (freezingRange : Float) (diff : Diffusivity_F) : Bool :=
  g.val / r.val ≥ freezingRange / (diff.val * 1e6)  -- unit alignment

-- G/R ratio
def grRatio_F (g : ThermalGradient_F) (r : SolidificationVelocity_F) : GRRatio_F :=
  ⟨g.val / r.val⟩

-- G×R product (local cooling rate at interface)
def grProduct_F (g : ThermalGradient_F) (r : SolidificationVelocity_F) : GRProduct_F :=
  ⟨g.val * r.val⟩

-- Secondary dendrite arm spacing: λ₂ = A · ε̇⁻ⁿ (cooling rate correlation)
def secondaryDAS_F (a : Float) (coolingRate : Float) (n : Float)
    : DendriteArmSpacing_F :=
  ⟨a * coolingRate ^ (-n)⟩

-- Scheil equation: Cs = k₀ · C₀ · (1 - fs)^(k₀-1)
def scheilConcentration_F (k0 : PartitionCoeff_F) (c0 : Float)
    (fs : Float) : Float :=
  k0.val * c0 * (1.0 - fs) ^ (k0.val - 1.0)

-- Freezing range from partition coefficient: ΔT₀ = m · C₀ · (1 - 1/k₀)
def freezingRange_F (m : LiquidusSlope_F) (c0 : Float)
    (k0 : PartitionCoeff_F) : Float :=
  m.val * c0 * (1.0 - 1.0 / k0.val)

-- Carbon equivalent (IIW formula): CE = C + Mn/6 + (Cr+Mo+V)/5 + (Ni+Cu)/15
def carbonEquivalentIIW_F (c mn cr mo v ni cu : Float) : CarbonEquivalent_F :=
  ⟨c + mn / 6.0 + (cr + mo + v) / 5.0 + (ni + cu) / 15.0⟩

-- Pcm formula (Ito-Bessyo): Pcm = C + Si/30 + Mn/20 + Cu/20 + Ni/60 + Cr/20 + Mo/15 + V/10 + 5B
def carbonEquivalentPcm_F (c si mn cu ni cr mo v b : Float) : CarbonEquivalent_F :=
  ⟨c + si / 30.0 + mn / 20.0 + cu / 20.0 + ni / 60.0 + cr / 20.0 + mo / 15.0 + v / 10.0 + 5.0 * b⟩

-- Rosenthal equation (2D, thin plate): T - T₀ = (Q/2πkt) · exp(-Vr/2α)
-- (simplified peak temperature at distance y from weld centerline)
def rosenthalPeakTemp2D_F (heatInputPerLength : Float) (k : Float)
    (thickness : Float) (speed : TravelSpeed_F) (alpha : Float)
    (y : Float) (t0 : Float) : Float :=
  let q := heatInputPerLength
  t0 + q / (2.0 * pi_F * k * thickness) *
    Float.exp (-speed.val * y / (2.0 * alpha * 1000.0))

-- Cooling time Δt₈₋₅ for thick plate (2D Rosenthal)
def coolingTime85_ThickPlate_F (heatInput : HeatInput_F) (t0 : Float) : CoolingTime_8_5_F :=
  let q := heatInput.val * 1000.0  -- kJ/mm → J/mm
  ⟨q / (2.0 * pi_F * 0.028) * (1.0 / (500.0 - t0) - 1.0 / (800.0 - t0))⟩
  -- k ≈ 0.028 J/(mm·s·K) for steel; simplified

-- Taylor tool life: V · T^n = C
def taylorToolLife_F (v : CuttingSpeed_F) (n : TaylorExponent_F)
    (c : TaylorConstant_F) : ToolLife_F :=
  ⟨(c.val / v.val) ^ (1.0 / n.val)⟩

-- Merchant shear angle: φ = π/4 - β/2 + α/2
def merchantShearAngle_F (frictionAngle : Float) (rake : RakeAngle_F) : ShearAngle_F :=
  ⟨45.0 - frictionAngle / 2.0 + rake.val / 2.0⟩

-- Chip thickness ratio: r = t₀/tc = sin φ / cos(φ - α)
def chipRatio_F (phi : ShearAngle_F) (alpha : RakeAngle_F) : ChipThicknessRatio_F :=
  let phi_rad := phi.val * pi_F / 180.0
  let alpha_rad := alpha.val * pi_F / 180.0
  ⟨Float.sin phi_rad / Float.cos (phi_rad - alpha_rad)⟩

-- Hollomon-Jaffe tempering parameter: P = T(K) · (C + log₁₀ t(hr))
def hollomonJaffe_F (t : Float) (time_hr : Float) (c : Float := 20.0) : TemperingParam_F :=
  ⟨t * (c + Float.log time_hr / Float.log 10.0) / 1000.0⟩

-- Approximate Ms temperature (Andrews formula for steel):
-- Ms(°C) = 539 - 423C - 30.4Mn - 17.7Ni - 12.1Cr - 7.5Mo - 7.5Si
def andrewsMs_F (c mn ni cr mo si : Float) : MsTemp_F :=
  ⟨539.0 - 423.0 * c - 30.4 * mn - 17.7 * ni - 12.1 * cr - 7.5 * mo - 7.5 * si⟩

-- Case depth from diffusion: x ≈ K · √(D·t)
def caseDepthEstimate_F (d : Diffusivity_F) (t : Float) (k : Float := 2.0)
    : CaseDepth_F :=
  ⟨k * Float.sqrt (d.val * t) * 1000.0⟩  -- m → mm

-- Plating thickness from Faraday's law: h = (M · I · t) / (z · F · ρ · A)
def platingThickness_F (atomicWeight : Float) (currentDensity : PlatingCurrentDensity_F)
    (time : Float) (valence : Float) (density : Float) : Float :=
  atomicWeight * currentDensity.val * time / (valence * faraday_F * density) * 1e4  -- cm → μm

-- Capillary rise in brazing: h = 2γcosθ / (ρgd)
def capillaryRiseBrazing_F (surfaceTension : Float) (theta : WettingAngle_F)
    (density : Float) (gap : JointClearance_F) : CapillaryRise_F :=
  let g := 9.81
  ⟨2.0 * surfaceTension * Float.cos (theta.val * pi_F / 180.0) /
    (density * g * gap.val * 0.001)⟩  -- mm → m, result in mm

-- Specific grinding energy: u = Ft · vs / (vw · ap · b)
def specificGrindingEnergy_F (ft : Float) (vs : WheelSpeed_F)
    (vw : Float) (ap : Float) (b : Float) : SpecificGrindingEnergy_F :=
  ⟨ft * vs.val / (vw * ap * b)⟩

-- Etch factor: EF = depth / undercut
def etchFactor_F (depth : Float) (undercut : Undercut_F) : EtchFactor_F :=
  ⟨depth / undercut.val⟩

-- Solidification morphology from G/R
def predictMorphology_F (gr : GRRatio_F) (criticalGR : Float) : SolidificationMorphology :=
  if gr.val > criticalGR * 10.0 then .Planar
  else if gr.val > criticalGR * 2.0 then .Cellular
  else if gr.val > criticalGR * 0.1 then .ColumnarDendritic
  else .EquiaxedDendritic

-- Sintering linear shrinkage from density: ΔL/L₀ = 1 - (ρ_green/ρ_sintered)^(1/3)
def sinteringShrinkage_F (green : GreenDensity_F) (sintered : SinteredDensity_F)
    : LinearShrinkage_F :=
  ⟨1.0 - (green.val / sintered.val) ^ (1.0 / 3.0)⟩

end Units.Metallurgy
