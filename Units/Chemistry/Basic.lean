-- Chemistry.lean        -- Reaction kinetics, equilibria, thermochemistry, electrochemistry
import LogosLibrary.Units.Core.SI
import LogosLibrary.Units.Physics.Thermal
import LogosLibrary.Units.Physics.Mechanics
--import LogosLibrary.Units.Bio
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

namespace Units.Chemistry.Basic

open Units.SI Units.Thermal Units.Mechanics

/-
================================================================================
CHEMISTRY UNITS LIBRARY
================================================================================

This module provides type-safe units for chemical kinetics, equilibria,
thermochemistry, electrochemistry, and analytical chemistry.
Following the triple-type architecture for maximum flexibility without type
conversion friction.

## COVERAGE
- Reaction kinetics (rate constants for all orders, activation energy)
- pH and Acid-Base
- Equilibrium constants (Ka, Kb, Ksp, Kw, Kp, Kc)
- Concentration units (molarity, molality, normality, mole fraction)
- Thermochemistry (enthalpy, Gibbs energy, entropy changes)
- Electrochemistry (potential, current density, charge transfer)
- Spectroscopy (wavenumber, absorbance, quantum yield)
- Activity and fugacity coefficients
- Partial pressure and Henry's law constants
- Surface chemistry (adsorption, surface coverage)
- Catalysis (turnover frequency, selectivity)
- Chemical potential and fugacity

## USAGE PATTERNS
Float: Experimental measurements, titration calculations, pH measurements,
spectrophotometer readings, electrochemical sensors, calorimetry data,
chromatography analysis, reaction monitoring, process control

ℚ: Exact stoichiometric ratios, balanced equations, oxidation states,
molecular formulas, dilution factors, standard solutions, gravimetric factors,
equivalent weights, exact atomic masses

ℝ: Theoretical models, statistical mechanics, quantum chemistry calculations,
transition state theory, Marcus theory, RRKM theory, formal thermodynamic
derivations, chemical potential analysis, phase equilibria proofs
-/

set_option autoImplicit false
set_option linter.unusedVariables false

/--
================================================================================================
   Mathematical and Physical Constants for Float Calculations
================================================================================================
-/
def pi_F : Float := 3.14159265358979323846
def e_F : Float := 2.71828182845904523536
def ln10_F : Float := 2.30258509299404568402
def R_gas_F : Float := 8.314462618  -- Universal gas constant (J/(mol·K))
def F_const_F : Float := 96485.33212  -- Faraday constant (C/mol)
def N_A_F : Float := 6.02214076e23  -- Avogadro's number
def k_B_F : Float := 1.380649e-23  -- Boltzmann constant (J/K)
def h_planck_F : Float := 6.62607015e-34  -- Planck constant (J·s)
def c_light_F : Float := 2.99792458e8  -- Speed of light (m/s)


/--
================================================================================================
  Derived Constants
================================================================================================
-/
structure RateConstant_F   where val : Float deriving Repr, BEq, Inhabited
structure RateConstant_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RateConstant_R   where val : ℝ     deriving Inhabited

structure CollisionFreq_F   where val : Float deriving Repr, BEq, Inhabited
structure CollisionFreq_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CollisionFreq_R   where val : ℝ     deriving Inhabited
/--
================================================================================================
   Concentration Units
================================================================================================
-/
-- Molarity: mol/L (already in Bio as Molar_F, but we'll add chemistry-specific ones)

-- Molality: mol/kg solvent
structure Molality_F   where val : Float deriving Repr, BEq, Inhabited
structure Molality_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Molality_R   where val : ℝ     deriving Inhabited

structure MilliMolality_F where val : Float deriving Repr, BEq, Inhabited
structure MilliMolality_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MilliMolality_R where val : ℝ     deriving Inhabited

-- Normality: eq/L
structure Normality_F  where val : Float deriving Repr, BEq, Inhabited
structure Normality_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Normality_R  where val : ℝ     deriving Inhabited

-- Mole fraction: dimensionless
structure MoleFraction_F where val : Float deriving Repr, BEq, Inhabited
structure MoleFraction_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MoleFraction_R where val : ℝ     deriving Inhabited

-- Mass fraction: dimensionless
structure MassFraction_F where val : Float deriving Repr, BEq, Inhabited
structure MassFraction_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MassFraction_R where val : ℝ     deriving Inhabited

-- Volume fraction: dimensionless
structure VolumeFraction_F where val : Float deriving Repr, BEq, Inhabited
structure VolumeFraction_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VolumeFraction_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Molar Concentrations
================================================================================================
-/
-- Base molar concentration: mol/L = M
structure Molar_F      where val : Float deriving Repr, BEq, Inhabited
structure Molar_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Molar_R      where val : ℝ     deriving Inhabited

-- Millimolar: mmol/L = mM
structure Millimolar_F where val : Float deriving Repr, BEq, Inhabited
structure Millimolar_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Millimolar_R where val : ℝ     deriving Inhabited

-- Micromolar: µmol/L = µM
structure Micromolar_F where val : Float deriving Repr, BEq, Inhabited
structure Micromolar_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Micromolar_R where val : ℝ     deriving Inhabited

-- Nanomolar: nmol/L = nM
structure Nanomolar_F  where val : Float deriving Repr, BEq, Inhabited
structure Nanomolar_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Nanomolar_R  where val : ℝ     deriving Inhabited

-- Picomolar: pmol/L = pM
structure Picomolar_F  where val : Float deriving Repr, BEq, Inhabited
structure Picomolar_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Picomolar_R  where val : ℝ     deriving Inhabited
/--
================================================================================================
   Reaction Kinetics
================================================================================================
-/
-- Zero-order rate constant: mol/(L·s)
structure RateZeroOrder_F where val : Float deriving Repr, BEq, Inhabited
structure RateZeroOrder_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RateZeroOrder_R where val : ℝ     deriving Inhabited

-- First-order rate constant: s⁻¹
structure RateFirstOrder_F where val : Float deriving Repr, BEq, Inhabited
structure RateFirstOrder_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RateFirstOrder_R where val : ℝ     deriving Inhabited

-- Second-order rate constant: L/(mol·s) or M⁻¹s⁻¹
structure RateSecondOrder_F where val : Float deriving Repr, BEq, Inhabited
structure RateSecondOrder_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RateSecondOrder_R where val : ℝ     deriving Inhabited

-- Third-order rate constant: L²/(mol²·s) or M⁻²s⁻¹
structure RateThirdOrder_F where val : Float deriving Repr, BEq, Inhabited
structure RateThirdOrder_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RateThirdOrder_R where val : ℝ     deriving Inhabited

-- Activation energy: J/mol or kJ/mol
structure ActivationEnergy_F where val : Float deriving Repr, BEq, Inhabited
structure ActivationEnergy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ActivationEnergy_R where val : ℝ     deriving Inhabited

-- Pre-exponential factor (Arrhenius): same units as rate constant
structure PreExponential_F where val : Float deriving Repr, BEq, Inhabited
structure PreExponential_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PreExponential_R where val : ℝ     deriving Inhabited

-- Half-life: s (or any time unit)
structure HalfLife_F   where val : Float deriving Repr, BEq, Inhabited
structure HalfLife_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HalfLife_R   where val : ℝ     deriving Inhabited

-- Reaction rate: mol/(L·s)
structure ReactionRate_F where val : Float deriving Repr, BEq, Inhabited
structure ReactionRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ReactionRate_R where val : ℝ     deriving Inhabited
/--
================================================================================================
   pH and Acid-Base
================================================================================================
-/
-- pH units (dimensionless but constrained 0-14 typically)
structure pH_F         where val : Float deriving Repr, BEq, Inhabited
structure pH_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure pH_R         where val : ℝ     deriving Inhabited

-- pKa units (acid dissociation constant)
structure pKa_F        where val : Float deriving Repr, BEq, Inhabited
structure pKa_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure pKa_R        where val : ℝ     deriving Inhabited

-- Buffer capacity: mol/(L·pH unit)
structure BufferCapacity_F where val : Float deriving Repr, BEq, Inhabited
structure BufferCapacity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BufferCapacity_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Equilibrium Constants
================================================================================================
-/
-- Equilibrium constant (concentration-based): dimensionless or (mol/L)^Δn
structure Kc_F         where val : Float deriving Repr, BEq, Inhabited
structure Kc_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kc_R         where val : ℝ     deriving Inhabited

-- Equilibrium constant (pressure-based): dimensionless or (bar)^Δn
structure Kp_F         where val : Float deriving Repr, BEq, Inhabited
structure Kp_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kp_R         where val : ℝ     deriving Inhabited

-- Acid dissociation constant: mol/L
structure Ka_F         where val : Float deriving Repr, BEq, Inhabited
structure Ka_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Ka_R         where val : ℝ     deriving Inhabited

-- Base dissociation constant: mol/L
structure Kb_F         where val : Float deriving Repr, BEq, Inhabited
structure Kb_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kb_R         where val : ℝ     deriving Inhabited

-- Solubility product: (mol/L)^n
structure Ksp_F        where val : Float deriving Repr, BEq, Inhabited
structure Ksp_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Ksp_R        where val : ℝ     deriving Inhabited

-- Water dissociation constant: (mol/L)²
structure Kw_F         where val : Float deriving Repr, BEq, Inhabited
structure Kw_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kw_R         where val : ℝ     deriving Inhabited

-- Formation constant: L/mol or higher powers
structure Kf_F         where val : Float deriving Repr, BEq, Inhabited
structure Kf_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kf_R         where val : ℝ     deriving Inhabited

-- Distribution coefficient: dimensionless
structure Kd_Chem_F    where val : Float deriving Repr, BEq, Inhabited
structure Kd_Chem_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kd_Chem_R    where val : ℝ     deriving Inhabited

/--
================================================================================================
   Thermochemistry
================================================================================================
-/
-- Enthalpy change: J/mol or kJ/mol
structure DeltaH_F     where val : Float deriving Repr, BEq, Inhabited
structure DeltaH_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DeltaH_R     where val : ℝ     deriving Inhabited

structure DeltaH_kJ_F  where val : Float deriving Repr, BEq, Inhabited
structure DeltaH_kJ_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DeltaH_kJ_R  where val : ℝ     deriving Inhabited

-- Gibbs free energy change: J/mol or kJ/mol
structure DeltaG_F     where val : Float deriving Repr, BEq, Inhabited
structure DeltaG_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DeltaG_R     where val : ℝ     deriving Inhabited

structure DeltaG_kJ_F  where val : Float deriving Repr, BEq, Inhabited
structure DeltaG_kJ_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DeltaG_kJ_R  where val : ℝ     deriving Inhabited

-- Entropy change: J/(mol·K)
structure DeltaS_F     where val : Float deriving Repr, BEq, Inhabited
structure DeltaS_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DeltaS_R     where val : ℝ     deriving Inhabited

-- Heat capacity (molar): J/(mol·K)
structure MolarHeatCapacity_F where val : Float deriving Repr, BEq, Inhabited
structure MolarHeatCapacity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MolarHeatCapacity_R where val : ℝ     deriving Inhabited

-- Chemical potential: J/mol
structure ChemicalPotential_F where val : Float deriving Repr, BEq, Inhabited
structure ChemicalPotential_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ChemicalPotential_R where val : ℝ     deriving Inhabited

-- Fugacity: Pa (same units as pressure)
structure Fugacity_F   where val : Float deriving Repr, BEq, Inhabited
structure Fugacity_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Fugacity_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Electrochemistry
================================================================================================
-/
-- Electrode potential: V
structure ElectrodePotential_F where val : Float deriving Repr, BEq, Inhabited
structure ElectrodePotential_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ElectrodePotential_R where val : ℝ     deriving Inhabited

-- Standard potential: V
structure StandardPotential_F where val : Float deriving Repr, BEq, Inhabited
structure StandardPotential_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure StandardPotential_R where val : ℝ     deriving Inhabited

-- Overpotential: V
structure Overpotential_F where val : Float deriving Repr, BEq, Inhabited
structure Overpotential_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Overpotential_R where val : ℝ     deriving Inhabited

-- Current density: A/m² or A/cm²
structure CurrentDensity_F where val : Float deriving Repr, BEq, Inhabited
structure CurrentDensity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CurrentDensity_R where val : ℝ     deriving Inhabited

-- Exchange current density: A/m²
structure ExchangeCurrentDensity_F where val : Float deriving Repr, BEq, Inhabited
structure ExchangeCurrentDensity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ExchangeCurrentDensity_R where val : ℝ     deriving Inhabited

-- Charge: C (coulombs) - could import from Electromagnetism
structure Charge_F     where val : Float deriving Repr, BEq, Inhabited
structure Charge_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Charge_R     where val : ℝ     deriving Inhabited

-- Specific charge: C/kg
structure SpecificCharge_F where val : Float deriving Repr, BEq, Inhabited
structure SpecificCharge_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpecificCharge_R where val : ℝ     deriving Inhabited

-- Conductivity (ionic): S/m
structure IonicConductivity_F where val : Float deriving Repr, BEq, Inhabited
structure IonicConductivity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure IonicConductivity_R where val : ℝ     deriving Inhabited

-- Molar conductivity: S·m²/mol
structure MolarConductivity_F where val : Float deriving Repr, BEq, Inhabited
structure MolarConductivity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MolarConductivity_R where val : ℝ     deriving Inhabited

-- Transfer coefficient: dimensionless
structure TransferCoeff_F where val : Float deriving Repr, BEq, Inhabited
structure TransferCoeff_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TransferCoeff_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Spectroscopy
================================================================================================
-/
-- Wavenumber: cm⁻¹
structure Wavenumber_F where val : Float deriving Repr, BEq, Inhabited
structure Wavenumber_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Wavenumber_R where val : ℝ     deriving Inhabited

-- Absorbance: dimensionless (A = -log₁₀(T))
structure Absorbance_F where val : Float deriving Repr, BEq, Inhabited
structure Absorbance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Absorbance_R where val : ℝ     deriving Inhabited

-- Transmittance: dimensionless (0-1)
structure Transmittance_F where val : Float deriving Repr, BEq, Inhabited
structure Transmittance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Transmittance_R where val : ℝ     deriving Inhabited

-- Molar absorptivity: L/(mol·cm)
structure MolarAbsorptivity_F where val : Float deriving Repr, BEq, Inhabited
structure MolarAbsorptivity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MolarAbsorptivity_R where val : ℝ     deriving Inhabited

-- Chemical shift: ppm (NMR)
structure ChemicalShift_F where val : Float deriving Repr, BEq, Inhabited
structure ChemicalShift_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ChemicalShift_R where val : ℝ     deriving Inhabited

-- Coupling constant: Hz (NMR)
structure CouplingConstant_F where val : Float deriving Repr, BEq, Inhabited
structure CouplingConstant_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CouplingConstant_R where val : ℝ     deriving Inhabited

-- Mass-to-charge ratio: m/z or Th (Thomson)
structure MassToCharge_F where val : Float deriving Repr, BEq, Inhabited
structure MassToCharge_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MassToCharge_R where val : ℝ     deriving Inhabited

-- Quantum yield: dimensionless (0-1)
structure QuantumYield_F where val : Float deriving Repr, BEq, Inhabited
structure QuantumYield_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure QuantumYield_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Activity and Fugacity Coefficients
================================================================================================
-/
-- Activity coefficient: dimensionless
structure ActivityCoeff_F where val : Float deriving Repr, BEq, Inhabited
structure ActivityCoeff_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ActivityCoeff_R where val : ℝ     deriving Inhabited

-- Fugacity coefficient: dimensionless
structure FugacityCoeff_F where val : Float deriving Repr, BEq, Inhabited
structure FugacityCoeff_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FugacityCoeff_R where val : ℝ     deriving Inhabited

-- Osmotic coefficient: dimensionless
structure OsmoticCoeff_F where val : Float deriving Repr, BEq, Inhabited
structure OsmoticCoeff_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure OsmoticCoeff_R where val : ℝ     deriving Inhabited

-- Ionic strength: mol/L
structure IonicStrength_F where val : Float deriving Repr, BEq, Inhabited
structure IonicStrength_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure IonicStrength_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Partial Pressure and Gas Phase
================================================================================================
-/
-- Partial pressure: Pa, kPa, bar, atm
structure PartialPressure_F where val : Float deriving Repr, BEq, Inhabited
structure PartialPressure_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PartialPressure_R where val : ℝ     deriving Inhabited

-- Henry's law constant: Pa·m³/mol or atm/(mol/L)
structure HenryConstant_F where val : Float deriving Repr, BEq, Inhabited
structure HenryConstant_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure HenryConstant_R where val : ℝ     deriving Inhabited

-- Vapor pressure: Pa
structure VaporPressure_F where val : Float deriving Repr, BEq, Inhabited
structure VaporPressure_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VaporPressure_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Surface Chemistry and Catalysis
================================================================================================
-/
-- Surface coverage: dimensionless (0-1)
structure SurfaceCoverage_F where val : Float deriving Repr, BEq, Inhabited
structure SurfaceCoverage_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SurfaceCoverage_R where val : ℝ     deriving Inhabited

-- Adsorption rate: mol/(m²·s)
structure AdsorptionRate_F where val : Float deriving Repr, BEq, Inhabited
structure AdsorptionRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AdsorptionRate_R where val : ℝ     deriving Inhabited

-- Turnover frequency: s⁻¹
structure TurnoverFreq_F where val : Float deriving Repr, BEq, Inhabited
structure TurnoverFreq_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TurnoverFreq_R where val : ℝ     deriving Inhabited

-- Turnover number: dimensionless
structure TurnoverNumber_F where val : Float deriving Repr, BEq, Inhabited
structure TurnoverNumber_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TurnoverNumber_R where val : ℝ     deriving Inhabited

-- Selectivity: dimensionless (%)
structure Selectivity_F where val : Float deriving Repr, BEq, Inhabited
structure Selectivity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Selectivity_R where val : ℝ     deriving Inhabited

-- Yield: dimensionless (%)
structure Yield_F      where val : Float deriving Repr, BEq, Inhabited
structure Yield_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Yield_R      where val : ℝ     deriving Inhabited

/--
================================================================================================
   Error Propagation & Measurement Helpers
================================================================================================
-/
-- Parametric Uncertainty Tracking with chemistry context
structure ChemMeasured (α : Type) where
  value : α
  uncertainty : α
  temperature : Option Kelvin_F := none
  pressure : Option Pascal_F := none
  pH : Option pH_F := none
  ionic_strength : Option IonicStrength_F := none
  method : Option String := none
  source : Option String := none
  deriving Repr, BEq, Inhabited

-- Measurement with uncertainty for equilibrium constants
structure MeasuredEquilibrium_F where
  K_value : Kc_F
  K_uncertainty : Kc_F
  temperature : Kelvin_F
  method : Option String := none  -- "spectrophotometry", "potentiometry", etc.
  deriving Repr, BEq, Inhabited

-- Measurement with uncertainty for rate constants
structure MeasuredRateConstant_F where
  k_value : Float  -- Generic, as units vary with order
  k_uncertainty : Float
  temperature : Kelvin_F
  order : Float
  method : Option String := none  -- "stopped-flow", "flash photolysis", etc.
  deriving Repr, BEq, Inhabited

-- Error propagation for Arrhenius equation
def arrheniusWithError_F (A : ChemMeasured PreExponential_F)
    (Ea : ChemMeasured ActivationEnergy_F) (T : Kelvin_F) (T_error : Kelvin_F)
    : ChemMeasured RateFirstOrder_F :=
  let k := A.value.val * Float.exp (-Ea.value.val / (R_gas_F * T.val))
  let relErrorA := A.uncertainty.val / A.value.val
  let absErrorEa := Ea.uncertainty.val / (R_gas_F * T.val)
  let absErrorT := Ea.value.val * T_error.val / (R_gas_F * T.val^2)
  let relError := Float.sqrt (relErrorA^2 + (absErrorEa + absErrorT)^2)
  { value := ⟨k⟩
    uncertainty := ⟨k * relError⟩
    temperature := some T
    source := some "Arrhenius equation" }

-- Error propagation for pH from H⁺ concentration
def pHWithError_F (h_conc : ChemMeasured Molar_F) : ChemMeasured pH_F :=
  let pH_val := -Float.log h_conc.value.val / ln10_F
  -- Error prop: δpH = |δ[H⁺]| / (ln(10) × [H⁺])
  let pH_error := h_conc.uncertainty.val / (ln10_F * h_conc.value.val)
  { value := ⟨pH_val⟩
    uncertainty := ⟨pH_error.abs⟩
    source := some "pH = -log[H⁺]" }

-- Error propagation for equilibrium constant from concentrations
def equilibriumConstantWithError_F (products : Array (ChemMeasured Molar_F))
    (product_stoich : Array Float) (reactants : Array (ChemMeasured Molar_F))
    (reactant_stoich : Array Float) : ChemMeasured Kc_F :=
  -- K = Π[products]^νᵢ / Π[reactants]^νⱼ
  let K_num := (products.zip product_stoich).foldl (init := 1.0) fun acc (c, n) =>
    acc * (c.value.val ^ n)
  let K_den := (reactants.zip reactant_stoich).foldl (init := 1.0) fun acc (c, n) =>
    acc * (c.value.val ^ n)
  let K := K_num / K_den
  -- Relative error propagation
  let relErrorProducts := (products.zip product_stoich).foldl (init := 0.0) fun acc (c, n) =>
    acc + (n * c.uncertainty.val / c.value.val)^2
  let relErrorReactants := (reactants.zip reactant_stoich).foldl (init := 0.0) fun acc (c, n) =>
    acc + (n * c.uncertainty.val / c.value.val)^2
  let relError := Float.sqrt (relErrorProducts + relErrorReactants)
  { value := ⟨K⟩
    uncertainty := ⟨K * relError⟩
    source := some "Equilibrium calculation" }

/--
================================================================================================
   Validation & Range Checking Helpers
================================================================================================
-/

-- pH validation
def isValidpH_F (p : pH_F) : Bool :=
  -2.0 ≤ p.val && p.val ≤ 16.0  -- Extended range for strong acids/bases

def isNeutralpH_F (p : pH_F) : Bool :=
  6.5 ≤ p.val && p.val ≤ 7.5  -- Near neutral at 25°C

-- Concentration validation
def isPositiveConcentration_F (c : Molar_F) : Bool :=
  c.val ≥ 0.0

def isSaturated_F (c : Molar_F) (solubility : Molar_F) : Bool :=
  c.val ≥ solubility.val

-- Equilibrium constant validation
def isValidEquilibrium_F (K : Kc_F) : Bool :=
  K.val > 0.0  -- Must be positive

def isFavoredForward_F (K : Kc_F) : Bool :=
  K.val > 1.0

def isFavoredReverse_F (K : Kc_F) : Bool :=
  K.val < 1.0

-- Rate constant validation
def isValidRateConstant_F (k : Float) : Bool :=
  k ≥ 0.0  -- Must be non-negative

-- Mole fraction validation
def isValidMoleFraction_F (x : MoleFraction_F) : Bool :=
  0.0 ≤ x.val && x.val ≤ 1.0

-- Activity coefficient validation
def isIdealBehavior_F (gamma : ActivityCoeff_F) : Bool :=
  0.95 ≤ gamma.val && gamma.val ≤ 1.05  -- Close to 1

-- Quantum yield validation
def isValidQuantumYield_F (phi : QuantumYield_F) : Bool :=
  0.0 ≤ phi.val && phi.val ≤ 1.0

-- Electrode potential validation
def isOxidizing_F (E : StandardPotential_F) : Bool :=
  E.val > 0.0  -- Positive potential

def isReducing_F (E : StandardPotential_F) : Bool :=
  E.val < 0.0  -- Negative potential

-- Absorbance validation
def isValidAbsorbance_F (A : Absorbance_F) : Bool :=
  A.val ≥ 0.0 && A.val ≤ 3.0  -- Typical spectrophotometer range

-- Transmittance validation
def isValidTransmittance_F (T : Transmittance_F) : Bool :=
  0.0 ≤ T.val && T.val ≤ 1.0

/--
================================================================================================
   Unit Conversions
================================================================================================
-/

-- Energy conversions (thermochemistry)
def jPerMolToKJPerMol_F (j : DeltaH_F) : DeltaH_kJ_F :=
  ⟨j.val / 1000.0⟩

def kjPerMolToJPerMol_F (kj : DeltaH_kJ_F) : DeltaH_F :=
  ⟨kj.val * 1000.0⟩

def kcalPerMolToKJPerMol_F (kcal : Float) : DeltaH_kJ_F :=
  ⟨kcal * 4.184⟩

-- pH/pKa conversions
def KaToPKa_F (ka : Ka_F) : pKa_F :=
  ⟨-Float.log ka.val / ln10_F⟩

def pKaToKa_F (pka : pKa_F) : Ka_F :=
  ⟨10.0 ^ (-pka.val)⟩

def KbToPKb_F (kb : Kb_F) : Float :=
  -Float.log kb.val / ln10_F

def pKbToKb_F (pkb : Float) : Kb_F :=
  ⟨10.0 ^ (-pkb)⟩

-- Concentration conversions
def molarityToMolality_F (M : Molar_F) (solvent_density : KgPerM3_F)
    (solute_MW : Float) : Molality_F :=
  -- m = M / (ρ_solvent - M * MW_solute/1000)
  let denom := solvent_density.val / 1000.0 - M.val * solute_MW / 1000.0
  ⟨M.val / denom⟩

def molalityToMolarity_F (m : Molality_F) (solvent_density : KgPerM3_F)
    (solute_MW : Float) : Molar_F :=
  -- M = m * ρ_solvent / (1 + m * MW_solute/1000)
  let num := m.val * solvent_density.val / 1000.0
  let denom := 1.0 + m.val * solute_MW / 1000.0
  ⟨num / denom⟩

def molarityToNormality_F (M : Molar_F) (n_equiv : Float) : Normality_F :=
  ⟨M.val * n_equiv⟩

def normalityToMolarity_F (N : Normality_F) (n_equiv : Float) : Molar_F :=
  ⟨N.val / n_equiv⟩

-- Spectroscopy conversions
def absorbanceToTransmittance_F (A : Absorbance_F) : Transmittance_F :=
  ⟨10.0 ^ (-A.val)⟩

def transmittanceToAbsorbance_F (T : Transmittance_F) : Absorbance_F :=
  if T.val > 0.0 then
    ⟨-Float.log T.val / ln10_F⟩
  else
    ⟨3.0⟩  -- Max absorbance for T = 0

def wavenumberToWavelength_F (nu : Wavenumber_F) : Float :=
  1.0 / (nu.val * 100.0)  -- Returns wavelength in meters

def wavelengthToWavenumber_F (lambda : Float) : Wavenumber_F :=
  ⟨1.0 / (lambda * 100.0)⟩  -- Input wavelength in meters

def wavenumberToFrequency_F (nu : Wavenumber_F) : Hertz_F :=
  ⟨nu.val * 100.0 * c_light_F⟩

def frequencyToWavenumber_F (f : Hertz_F) : Wavenumber_F :=
  ⟨f.val / (c_light_F * 100.0)⟩

-- Pressure conversions for gas phase
def pascalToBar_F (pa : PartialPressure_F) : Float :=
  pa.val / 100000.0

def barToPascal_F (bar : Float) : PartialPressure_F :=
  ⟨bar * 100000.0⟩

def pascalToAtm_F (pa : PartialPressure_F) : Float :=
  pa.val / 101325.0

def atmToPascal_F (atm : Float) : PartialPressure_F :=
  ⟨atm * 101325.0⟩

/--
================================================================================================
   Common Chemistry Calculations
================================================================================================
-/

-- pH calculations
def pHFromHConcentration_F (h : Molar_F) : pH_F :=
  ⟨-Float.log h.val / ln10_F⟩

def hConcentrationFromPH_F (p : pH_F) : Molar_F :=
  ⟨10.0 ^ (-p.val)⟩

def pOHFromPH_F (p : pH_F) : Float :=
  14.0 - p.val  -- At 25°C

def pHFromPOH_F (poh : Float) : pH_F :=
  ⟨14.0 - poh⟩  -- At 25°C

-- Buffer calculations (Henderson-Hasselbalch)
def bufferPH_F (pka : pKa_F) (acid : Molar_F) (base : Molar_F) : pH_F :=
  ⟨pka.val + Float.log (base.val / acid.val) / ln10_F⟩

-- Arrhenius equation
def arrheniusRateConstant_F (A : PreExponential_F) (Ea : ActivationEnergy_F)
    (T : Kelvin_F) : RateFirstOrder_F :=
  ⟨A.val * Float.exp (-Ea.val / (R_gas_F * T.val))⟩

-- Activation energy from two rate constants
def activationEnergy_F (k1 : RateFirstOrder_F) (T1 : Kelvin_F)
    (k2 : RateFirstOrder_F) (T2 : Kelvin_F) : ActivationEnergy_F :=
  let Ea := R_gas_F * Float.log (k2.val / k1.val) / (1.0/T1.val - 1.0/T2.val)
  ⟨Ea⟩

-- Van't Hoff equation
def vantHoffDeltaH_F (K1 : Kc_F) (T1 : Kelvin_F) (K2 : Kc_F) (T2 : Kelvin_F)
    : DeltaH_F :=
  let deltaH := -R_gas_F * Float.log (K2.val / K1.val) / (1.0/T2.val - 1.0/T1.val)
  ⟨deltaH⟩

-- Gibbs energy from equilibrium constant
def gibbsFromK_F (K : Kc_F) (T : Kelvin_F) : DeltaG_F :=
  ⟨-R_gas_F * T.val * Float.log K.val⟩

-- Equilibrium constant from Gibbs
def kFromGibbs_F (deltaG : DeltaG_F) (T : Kelvin_F) : Kc_F :=
  ⟨Float.exp (-deltaG.val / (R_gas_F * T.val))⟩

-- Gibbs-Helmholtz equation
def gibbsFromEnthalpyEntropy_F (deltaH : DeltaH_F) (deltaS : DeltaS_F)
    (T : Kelvin_F) : DeltaG_F :=
  ⟨deltaH.val - T.val * deltaS.val⟩

-- Reaction quotient
def reactionQuotient_F (products : Array Molar_F) (product_stoich : Array Float)
    (reactants : Array Molar_F) (reactant_stoich : Array Float) : Float :=
  let Q_num := (products.zip product_stoich).foldl (init := 1.0) fun acc (c, n) =>
    acc * (c.val ^ n)
  let Q_den := (reactants.zip reactant_stoich).foldl (init := 1.0) fun acc (c, n) =>
    acc * (c.val ^ n)
  Q_num / Q_den

-- Nernst equation
def nernstPotential_F (E0 : StandardPotential_F) (n : Float) (Q : Float)
    (T : Kelvin_F) : ElectrodePotential_F :=
  ⟨E0.val - (R_gas_F * T.val / (n * F_const_F)) * Float.log Q⟩

-- Nernst at 25°C (simplified)
def nernstPotential25C_F (E0 : StandardPotential_F) (n : Float) (Q : Float)
    : ElectrodePotential_F :=
  ⟨E0.val - (0.0592 / n) * Float.log Q / ln10_F⟩

-- Faraday's laws
def chargeFromMoles_F (n : Mole_F) (z : Float) : Charge_F :=
  ⟨n.val * z * F_const_F⟩

def molesFromCharge_F (Q : Charge_F) (z : Float) : Mole_F :=
  ⟨Q.val / (z * F_const_F)⟩

def massElectrolysis_F (Q : Charge_F) (M : Float) (z : Float) : Gram_F :=
  ⟨Q.val * M / (z * F_const_F)⟩

-- Beer-Lambert law
def absorbance_F (epsilon : MolarAbsorptivity_F) (c : Molar_F)
    (l : Float) : Absorbance_F :=  -- l in cm
  ⟨epsilon.val * c.val * l⟩

def concentrationFromAbsorbance_F (A : Absorbance_F) (epsilon : MolarAbsorptivity_F)
    (l : Float) : Molar_F :=
  ⟨A.val / (epsilon.val * l)⟩

-- Half-life calculations
def halfLifeFirstOrder_F (k : RateFirstOrder_F) : HalfLife_F :=
  ⟨Float.log 2.0 / k.val⟩

def halfLifeZeroOrder_F (c0 : Molar_F) (k : RateZeroOrder_F) : HalfLife_F :=
  ⟨c0.val / (2.0 * k.val)⟩

def halfLifeSecondOrder_F (c0 : Molar_F) (k : RateSecondOrder_F) : HalfLife_F :=
  ⟨1.0 / (k.val * c0.val)⟩

-- Integrated rate laws
def firstOrderConcentration_F (c0 : Molar_F) (k : RateFirstOrder_F)
    (t : Second_F) : Molar_F :=
  ⟨c0.val * Float.exp (-k.val * t.val)⟩

def zeroOrderConcentration_F (c0 : Molar_F) (k : RateZeroOrder_F)
    (t : Second_F) : Molar_F :=
  let c := c0.val - k.val * t.val
  ⟨if c > 0.0 then c else 0.0⟩

def secondOrderConcentration_F (c0 : Molar_F) (k : RateSecondOrder_F)
    (t : Second_F) : Molar_F :=
  ⟨c0.val / (1.0 + k.val * c0.val * t.val)⟩

-- Ionic strength
def ionicStrength_F (concentrations : Array Molar_F) (charges : Array Float)
    : IonicStrength_F :=
  let I := 0.5 * (concentrations.zip charges).foldl (init := 0.0) fun acc (c, z) =>
    acc + c.val * z^2
  ⟨I⟩

-- Debye-Hückel (limiting law)
def activityCoeffDebyeHuckel_F (z : Float) (I : IonicStrength_F) : ActivityCoeff_F :=
  let A := 0.509  -- For water at 25°C
  ⟨10.0 ^ (-A * z^2 * Float.sqrt I.val)⟩

-- Clausius-Clapeyron equation
def vaporPressure_F (P1 : VaporPressure_F) (T1 : Kelvin_F)
    (deltaH_vap : DeltaH_F) (T2 : Kelvin_F) : VaporPressure_F :=
  let P2 := P1.val * Float.exp (-deltaH_vap.val / R_gas_F * (1.0/T2.val - 1.0/T1.val))
  ⟨P2⟩

-- Raoult's law
def vaporPressureRaoult_F (P_pure : VaporPressure_F) (x : MoleFraction_F)
    : PartialPressure_F :=
  ⟨P_pure.val * x.val⟩

-- Henry's law
def henryLawConcentration_F (k_H : HenryConstant_F) (p : PartialPressure_F)
    : Molar_F :=
  ⟨p.val / k_H.val⟩

-- Osmotic pressure
def osmoticPressure_F (c : Molar_F) (T : Kelvin_F) (i : Float) : Pascal_F :=
  ⟨i * c.val * R_gas_F * T.val⟩  -- i is van't Hoff factor

-- Freezing point depression
def freezingPointDepression_F (Kf : Float) (m : Molality_F) (i : Float) : Kelvin_F :=
  ⟨Kf * m.val * i⟩

-- Boiling point elevation
def boilingPointElevation_F (Kb : Float) (m : Molality_F) (i : Float) : Kelvin_F :=
  ⟨Kb * m.val * i⟩

-- Butler-Volmer equation (simplified)
def currentDensityBV_F (j0 : ExchangeCurrentDensity_F) (alpha : TransferCoeff_F)
    (eta : Overpotential_F) (T : Kelvin_F) (n : Float) : CurrentDensity_F :=
  let f := F_const_F / (R_gas_F * T.val)
  ⟨j0.val * (Float.exp (alpha.val * n * f * eta.val) -
            Float.exp (-(1.0 - alpha.val) * n * f * eta.val))⟩

-- Tafel equation (high overpotential approximation)
def tafelSlope_F (T : Kelvin_F) (alpha : TransferCoeff_F) (n : Float) : Float :=
  2.303 * R_gas_F * T.val / (alpha.val * n * F_const_F)

-- Langmuir isotherm
def langmuirCoverage_F (K_ads : Float) (p : PartialPressure_F) : SurfaceCoverage_F :=
  ⟨K_ads * p.val / (1.0 + K_ads * p.val)⟩

-- BET isotherm (simplified, single point)
def betSurfaceArea_F (V_ads : Float) (V_mono : Float) (A_molecule : Float)
    : Float :=  -- Returns m²/g
  V_ads / V_mono * N_A_F * A_molecule / 1e20

-- Conversion and yield
def percentYield_F (actual : Mole_F) (theoretical : Mole_F) : Yield_F :=
  ⟨(actual.val / theoretical.val) * 100.0⟩

def selectivity_F (desired : Mole_F) (total : Mole_F) : Selectivity_F :=
  ⟨(desired.val / total.val) * 100.0⟩

-- Collision frequency (gas phase)
def collisionFrequency_F (n : Float) (sigma : Float) (T : Kelvin_F)
    (M : Float) : Float :=  -- n = number density, sigma = collision cross-section
  let v_avg := Float.sqrt (8.0 * k_B_F * T.val / (pi_F * M))
  n * sigma * v_avg

end Units.Chemistry.Basic
