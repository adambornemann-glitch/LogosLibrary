/-
Author: Adam Bornemann
Created: 9/19/2025
Updated: 10/5/2025
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Nat.Basic
import Batteries.Data.String.Matcher


/- ================================================================
   LEVEL 0.0: VALUE STRUCTS
   ================================================================ -/

/- Battery Specific Value Structs -/
structure g.cm3 where val : Float
  deriving Repr
structure MS.m where val : Float
  deriving Repr
structure Angstrom where val : Float
  deriving Repr
structure Volt where val : Float
  deriving Repr, BEq
structure Kelvin where val : Float
  deriving Repr
structure GPa where val : Float
  deriving Repr
structure MPa where val : Float
  deriving Repr
structure KJ.mol where val : Float
  deriving Repr
structure J.kgK where val : Float
  deriving Repr
structure W.mK where val : Float
  deriving Repr
/- Other Chem Value Structs -/
structure pm where val : Nat

/- ================================================================
   LEVEL 0.1: VOLTAGE TYPE STRUCTS
   ================================================================ -/

/- Reference electrode for potential measurements -/
inductive RefElectrode
  | SHE     -- Standard Hydrogen Electrode (0V by definition)
  | Li_Li   -- Li/Li+ (-3.04V vs SHE)
  | AgCl    -- Ag/AgCl (+0.197V vs SHE)
  | SCE     -- Saturated Calomel (+0.241V vs SHE)
  deriving Repr, BEq

/- Electrode potential with reference -/
structure ElectrodePotential where
  voltage : Volt
  reference : RefElectrode
  deriving Repr

/- Operating voltage window -/
structure VoltageWindow where
  min : Volt
  max : Volt
  nominal : Volt
  deriving Repr

/- Voltage with state of charge dependency -/
structure VoltageProfile where
  ocv : Float → Volt           -- Open Circuit Voltage as function of SoC (0-1)
  loadVoltage : Float → Float → Volt  -- SoC → C-rate → Voltage
  cutoffVoltage : Volt
  chargeVoltage : Volt


/- ================================================================
   LEVEL 0.2: THERMAL TYPE STRUCT
   ================================================================ -/

/- Thermal property structures -/
structure ThermalProps where
  specificHeat : J.kgK           -- Specific heat capacity
  thermalConductivity : W.mK     -- Thermal conductivity
  thermalRunawayTemp : Kelvin    -- Critical temperature
  operatingMin : Kelvin          -- Minimum operating temp
  operatingMax : Kelvin          -- Maximum operating temp
  optimalTemp : Kelvin           -- Best performance temp

/- ================================================================
   LEVEL 0.3: DENDRITE TYPE STRUCT
   ================================================================ -/

/- Dendrite suppression mechanisms -/
inductive DendriteSuppression
  | None                    -- No suppression
  | SolidElectrolyte       -- Physical barrier (glass, ceramic)
  | PolymerCoating         -- Artificial SEI
  | ElectrolyteAdditives   -- LiNO3, FEC, etc.
  | CurrentDensityControl  -- Low current operation
  | PressureApplication    -- Stack pressure (7+ MPa)
  | AlloyingStrategy       -- Li-Mg, Li-Al, etc.
  | HostStructure          -- 3D scaffolds, Li metal in carbon
  | PulsedCharging         -- Rest periods for relaxation
  deriving Repr, BEq

/- Dendrite growth model parameters -/
structure DendriteGrowth where
  nucleationRate : Float      -- Sites/cm²/s
  growthVelocity : Float      -- μm/cycle
  criticalLength : Float      -- μm before short circuit
  morphology : String         -- "mossy", "needle", "fractal"
  onsetCurrent : Float        -- mA/cm² threshold
  deriving Repr


/- ================================================================
   LEVEL 0.4: BATTERY PROPS TYPE STRUCT
   ================================================================ -/

structure BatteryPropsV2 where
  atomicNumber                  : Nat
  symbol                        : String
  atomicMass                    : Float
  valenceElectrons              : Nat
  density                       : g.cm3 -- g/cm³
  conductivityElectric          : MS.m  -- MS/m
  reductionPotential            : ElectrodePotential  -- Now with reference!
  ionicRadius                   : Angstrom  -- Å for most common ion
  volumeExpansion               : Float -- % for Li insertion
  formsDendrites                : Bool
  maxCRate                      : Float  -- C (1C = full charge in 1 hour)
  coulombicEfficiency           : Float  -- % (first cycle)
  capacityFade                  : Float  -- % per 100 cycles
  voltageWindow                 : VoltageWindow  -- Operating range
  deriving Repr


inductive ElementClass
| AlkaliMetal | AlkalineEarth | TransitionMetal | PostTransition
| Metalloid | OtherNonmetal | Halogen | NobleGas
| Lanthanide | Actinide | Unknown


open Batteries

/- ================================================================
   LEVEL 0.5: COMPOUND AND COMPOSITE MATERIALS
   ================================================================ -/

/- Compound stoichiometry representation -/
structure CompoundElement where
  element : BatteryPropsV2
  ratio : Float
  oxidationState : Int
  deriving Repr

/- Crystal structure types -/
inductive CrystalStructure
  | Layered     -- LCO, NMC, NCA (prone to degradation)
  | Spinel      -- LMO, LNMO (stable 3D structure)
  | Olivine     -- LFP (very stable, channels for Li)
  | RockSalt    -- LTO (zero-strain)
  | Amorphous   -- Some conversion materials
  | Perovskite  -- Next-gen solid electrolytes
  deriving Repr, BEq

/- Compound material properties -/
structure CompoundProps where
  name : String
  formula : String
  components : List CompoundElement
  crystalStructure : CrystalStructure
  theoreticalCapacity : Float  -- mAh/g
  practicalCapacity : Float    -- mAh/g
  voltageVsLi : VoltageWindow  -- Operating window vs Li/Li+
  density : g.cm3
  ionicConductivity : MS.m
  electronicConductivity : MS.m
  volumeChange : Float         -- % during cycling
  thermalStability : Kelvin    -- Decomposition temperature
  oxygenRelease : Bool         -- Releases O2 on decomposition?
  costPerKg : Float           -- $/kg
  cycleLife : Nat             -- 80% capacity retention
  cRateCapability : Float     -- Maximum C-rate
  firstCycleEfficiency : Float -- %
  deriving Repr

/- ================================================================
   LEVEL 0.6: COMPREHENSIVE MULTI-PHYSICS STRUCT
   ================================================================ -/

structure BatteryClaim where
  -- Basic specs
  chemistry : String
  energyDensity : Float     -- Wh/kg
  capacity : Float          -- mAh/g
  cycles : Nat
  -- Voltage claims
  cellVoltage : Float       -- V
  chargeVoltage : Float     -- V
  voltageEfficiency : Float -- %
  -- Thermal claims
  minOperatingTemp : Float  -- °C
  maxOperatingTemp : Float  -- °C
  chargeMinutes : Nat
  coolingType : String
  coldWeatherRange : Float  -- km at -20°C
  -- Cost/scale
  costPerKWh : Float        -- $/kWh
  productionScale : String  -- "lab", "pilot", "mass"
  deriving Repr



 /- ================================================================
   LEVEL 1: THE ELEMENT & COMPOUND BATTERY DATABASE
   ================================================================ -/

/-    Battery Databse by pure elements   -/
def batteryDatabase : List BatteryPropsV2 := [
  -- ANODES (negative electrodes)
  { atomicNumber := 3, symbol := "Li", atomicMass := 6.94, valenceElectrons := 1,
    density := ⟨0.534⟩, conductivityElectric := ⟨11.0⟩,
    reductionPotential := ⟨⟨-3.04⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.76⟩,
    volumeExpansion := 380.0, formsDendrites := true, maxCRate := 1.0,
    coulombicEfficiency := 85.0, capacityFade := 20.0,
    voltageWindow := ⟨⟨-0.05⟩, ⟨0.5⟩, ⟨0.0⟩⟩ : BatteryPropsV2 },  -- Lithium metal

  { atomicNumber := 6, symbol := "C", atomicMass := 12.01, valenceElectrons := 4,
    density := ⟨2.26⟩, conductivityElectric := ⟨0.1⟩,
    reductionPotential := ⟨⟨-0.13⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.16⟩,
    volumeExpansion := 12.0, formsDendrites := false, maxCRate := 10.0,
    coulombicEfficiency := 95.0, capacityFade := 0.1,
    voltageWindow := ⟨⟨0.01⟩, ⟨2.0⟩, ⟨0.1⟩⟩ : BatteryPropsV2 },  -- Graphite

  { atomicNumber := 14, symbol := "Si", atomicMass := 28.09, valenceElectrons := 4,
    density := ⟨2.33⟩, conductivityElectric := ⟨0.001⟩,
    reductionPotential := ⟨⟨-0.14⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.40⟩,
    volumeExpansion := 400.0, formsDendrites := false, maxCRate := 0.5,
    coulombicEfficiency := 70.0, capacityFade := 50.0,
    voltageWindow := ⟨⟨0.05⟩, ⟨1.5⟩, ⟨0.4⟩⟩ : BatteryPropsV2 },  -- Silicon

  { atomicNumber := 22, symbol := "Ti", atomicMass := 47.87, valenceElectrons := 4,
    density := ⟨4.54⟩, conductivityElectric := ⟨2.4⟩,
    reductionPotential := ⟨⟨-1.63⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.60⟩,
    volumeExpansion := 0.1, formsDendrites := false, maxCRate := 30.0,
    coulombicEfficiency := 99.5, capacityFade := 0.01,
    voltageWindow := ⟨⟨1.2⟩, ⟨2.5⟩, ⟨1.55⟩⟩ : BatteryPropsV2 },  -- Titanium (LTO)

  { atomicNumber := 30, symbol := "Zn", atomicMass := 65.38, valenceElectrons := 2,
    density := ⟨7.13⟩, conductivityElectric := ⟨17.0⟩,
    reductionPotential := ⟨⟨-0.76⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.74⟩,
    volumeExpansion := 5.0, formsDendrites := true, maxCRate := 5.0,
    coulombicEfficiency := 95.0, capacityFade := 10.0,
    voltageWindow := ⟨⟨-0.2⟩, ⟨0.2⟩, ⟨0.0⟩⟩ : BatteryPropsV2 },  -- Zinc

  { atomicNumber := 31, symbol := "Ga", atomicMass := 69.72, valenceElectrons := 3,
    density := ⟨5.91⟩, conductivityElectric := ⟨7.4⟩,
    reductionPotential := ⟨⟨-0.55⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.62⟩,
    volumeExpansion := 20.0, formsDendrites := false, maxCRate := 2.0,
    coulombicEfficiency := 90.0, capacityFade := 5.0,
    voltageWindow := ⟨⟨0.1⟩, ⟨1.0⟩, ⟨0.5⟩⟩ : BatteryPropsV2 },  -- Gallium

  { atomicNumber := 32, symbol := "Ge", atomicMass := 72.63, valenceElectrons := 4,
    density := ⟨5.32⟩, conductivityElectric := ⟨0.0⟩,
    reductionPotential := ⟨⟨-0.12⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.53⟩,
    volumeExpansion := 370.0, formsDendrites := false, maxCRate := 0.5,
    coulombicEfficiency := 75.0, capacityFade := 40.0,
    voltageWindow := ⟨⟨0.3⟩, ⟨1.6⟩, ⟨0.6⟩⟩ : BatteryPropsV2 },  -- Germanium

  { atomicNumber := 50, symbol := "Sn", atomicMass := 118.71, valenceElectrons := 4,
    density := ⟨7.29⟩, conductivityElectric := ⟨9.1⟩,
    reductionPotential := ⟨⟨-0.14⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.69⟩,
    volumeExpansion := 260.0, formsDendrites := false, maxCRate := 1.0,
    coulombicEfficiency := 80.0, capacityFade := 30.0,
    voltageWindow := ⟨⟨0.1⟩, ⟨0.9⟩, ⟨0.4⟩⟩ : BatteryPropsV2 },  -- Tin

  -- ALKALI/ALKALINE FOR ALTERNATIVE CHEMISTRIES
  { atomicNumber := 11, symbol := "Na", atomicMass := 22.99, valenceElectrons := 1,
    density := ⟨0.968⟩, conductivityElectric := ⟨23.0⟩,
    reductionPotential := ⟨⟨-2.71⟩, RefElectrode.SHE⟩, ionicRadius := ⟨1.02⟩,
    volumeExpansion := 100.0, formsDendrites := true, maxCRate := 2.0,
    coulombicEfficiency := 88.0, capacityFade := 15.0,
    voltageWindow := ⟨⟨-0.1⟩, ⟨0.1⟩, ⟨0.0⟩⟩ : BatteryPropsV2 },  -- Sodium

  { atomicNumber := 12, symbol := "Mg", atomicMass := 24.31, valenceElectrons := 2,
    density := ⟨1.738⟩, conductivityElectric := ⟨22.0⟩,
    reductionPotential := ⟨⟨-2.37⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.72⟩,
    volumeExpansion := 130.0, formsDendrites := true, maxCRate := 0.5,
    coulombicEfficiency := 85.0, capacityFade := 25.0,
    voltageWindow := ⟨⟨-0.2⟩, ⟨0.3⟩, ⟨0.0⟩⟩ : BatteryPropsV2 },  -- Magnesium

  { atomicNumber := 13, symbol := "Al", atomicMass := 26.98, valenceElectrons := 3,
    density := ⟨2.70⟩, conductivityElectric := ⟨38.0⟩,
    reductionPotential := ⟨⟨-1.66⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.53⟩,
    volumeExpansion := 96.0, formsDendrites := false, maxCRate := 1.0,
    coulombicEfficiency := 92.0, capacityFade := 8.0,
    voltageWindow := ⟨⟨-0.3⟩, ⟨0.5⟩, ⟨0.0⟩⟩ : BatteryPropsV2 },  -- Aluminum

  { atomicNumber := 19, symbol := "K", atomicMass := 39.10, valenceElectrons := 1,
    density := ⟨0.856⟩, conductivityElectric := ⟨14.0⟩,
    reductionPotential := ⟨⟨-2.93⟩, RefElectrode.SHE⟩, ionicRadius := ⟨1.38⟩,
    volumeExpansion := 60.0, formsDendrites := true, maxCRate := 1.0,
    coulombicEfficiency := 90.0, capacityFade := 12.0,
    voltageWindow := ⟨⟨-0.15⟩, ⟨0.15⟩, ⟨0.0⟩⟩ : BatteryPropsV2 },  -- Potassium

  { atomicNumber := 20, symbol := "Ca", atomicMass := 40.08, valenceElectrons := 2,
    density := ⟨1.55⟩, conductivityElectric := ⟨29.0⟩,
    reductionPotential := ⟨⟨-2.84⟩, RefElectrode.SHE⟩, ionicRadius := ⟨1.00⟩,
    volumeExpansion := 80.0, formsDendrites := true, maxCRate := 0.5,
    coulombicEfficiency := 82.0, capacityFade := 20.0,
    voltageWindow := ⟨⟨-0.5⟩, ⟨0.5⟩, ⟨0.0⟩⟩ : BatteryPropsV2 },  -- Calcium

  -- CATHODE MATERIALS (positive electrodes)
  { atomicNumber := 8, symbol := "O", atomicMass := 16.00, valenceElectrons := 2,
    density := ⟨0.0014⟩, conductivityElectric := ⟨0.0⟩,
    reductionPotential := ⟨⟨2.07⟩, RefElectrode.SHE⟩, ionicRadius := ⟨1.40⟩,
    volumeExpansion := 0.0, formsDendrites := false, maxCRate := 0.1,
    coulombicEfficiency := 50.0, capacityFade := 30.0,
    voltageWindow := ⟨⟨2.0⟩, ⟨3.2⟩, ⟨2.96⟩⟩ : BatteryPropsV2 },  -- Oxygen (Li-air)

  { atomicNumber := 16, symbol := "S", atomicMass := 32.06, valenceElectrons := 2,
    density := ⟨2.07⟩, conductivityElectric := ⟨0.0⟩,
    reductionPotential := ⟨⟨2.01⟩, RefElectrode.SHE⟩, ionicRadius := ⟨1.84⟩,
    volumeExpansion := 80.0, formsDendrites := false, maxCRate := 0.2,
    coulombicEfficiency := 80.0, capacityFade := 40.0,
    voltageWindow := ⟨⟨1.5⟩, ⟨2.8⟩, ⟨2.1⟩⟩ : BatteryPropsV2 },  -- Sulfur

  { atomicNumber := 23, symbol := "V", atomicMass := 50.94, valenceElectrons := 5,
    density := ⟨6.11⟩, conductivityElectric := ⟨5.0⟩,
    reductionPotential := ⟨⟨-1.18⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.54⟩,
    volumeExpansion := 10.0, formsDendrites := false, maxCRate := 5.0,
    coulombicEfficiency := 95.0, capacityFade := 2.0,
    voltageWindow := ⟨⟨2.5⟩, ⟨4.0⟩, ⟨3.4⟩⟩ : BatteryPropsV2 },  -- Vanadium

  { atomicNumber := 25, symbol := "Mn", atomicMass := 54.94, valenceElectrons := 4,
    density := ⟨7.47⟩, conductivityElectric := ⟨0.7⟩,
    reductionPotential := ⟨⟨1.51⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.83⟩,
    volumeExpansion := 6.5, formsDendrites := false, maxCRate := 20.0,
    coulombicEfficiency := 98.0, capacityFade := 0.5,
    voltageWindow := ⟨⟨3.0⟩, ⟨4.3⟩, ⟨4.0⟩⟩ : BatteryPropsV2 },  -- Manganese

  { atomicNumber := 26, symbol := "Fe", atomicMass := 55.85, valenceElectrons := 3,
    density := ⟨7.87⟩, conductivityElectric := ⟨10.0⟩,
    reductionPotential := ⟨⟨0.77⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.61⟩,
    volumeExpansion := 1.0, formsDendrites := false, maxCRate := 30.0,
    coulombicEfficiency := 99.0, capacityFade := 0.05,
    voltageWindow := ⟨⟨2.5⟩, ⟨3.65⟩, ⟨3.45⟩⟩ : BatteryPropsV2 },  -- Iron (LFP)

  { atomicNumber := 27, symbol := "Co", atomicMass := 58.93, valenceElectrons := 3,
    density := ⟨8.90⟩, conductivityElectric := ⟨17.0⟩,
    reductionPotential := ⟨⟨1.92⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.65⟩,
    volumeExpansion := 2.0, formsDendrites := false, maxCRate := 5.0,
    coulombicEfficiency := 98.0, capacityFade := 0.2,
    voltageWindow := ⟨⟨3.0⟩, ⟨4.2⟩, ⟨3.9⟩⟩ : BatteryPropsV2 },  -- Cobalt

  { atomicNumber := 28, symbol := "Ni", atomicMass := 58.69, valenceElectrons := 2,
    density := ⟨8.91⟩, conductivityElectric := ⟨14.0⟩,
    reductionPotential := ⟨⟨1.96⟩, RefElectrode.SHE⟩, ionicRadius := ⟨0.69⟩,
    volumeExpansion := 2.5, formsDendrites := false, maxCRate := 3.0,
    coulombicEfficiency := 97.0, capacityFade := 0.3,
    voltageWindow := ⟨⟨3.0⟩, ⟨4.3⟩, ⟨3.8⟩⟩ : BatteryPropsV2 }  -- Nickel
]

/- Common cathode compounds database -/
def cathodeCompounds : List CompoundProps := [
  { name := "LFP",
    formula := "LiFePO₄",
    components := [], -- Would need Fe, P, O elements
    crystalStructure := CrystalStructure.Olivine,
    theoreticalCapacity := 170,
    practicalCapacity := 160,
    voltageVsLi := ⟨⟨3.2⟩, ⟨3.6⟩, ⟨3.45⟩⟩,
    density := ⟨3.6⟩,
    ionicConductivity := ⟨0.000001⟩,  -- Needs coating
    electronicConductivity := ⟨0.00001⟩,  -- Poor, needs carbon
    volumeChange := 6.8,
    thermalStability := ⟨543⟩,  -- 270°C - very safe
    oxygenRelease := false,
    costPerKg := 15,
    cycleLife := 4000,
    cRateCapability := 10.0,
    firstCycleEfficiency := 95 },

  { name := "NMC622",
    formula := "LiNi₀.₆Mn₀.₂Co₀.₂O₂",
    components := [],
    crystalStructure := CrystalStructure.Layered,
    theoreticalCapacity := 276,
    practicalCapacity := 180,
    voltageVsLi := ⟨⟨3.0⟩, ⟨4.3⟩, ⟨3.7⟩⟩,
    density := ⟨4.7⟩,
    ionicConductivity := ⟨0.001⟩,
    electronicConductivity := ⟨0.1⟩,
    volumeChange := 2.5,
    thermalStability := ⟨483⟩,  -- 210°C
    oxygenRelease := true,
    costPerKg := 40,
    cycleLife := 1500,
    cRateCapability := 3.0,
    firstCycleEfficiency := 88 },

  { name := "NMC811",
    formula := "LiNi₀.₈Mn₀.₁Co₀.₁O₂",
    components := [],
    crystalStructure := CrystalStructure.Layered,
    theoreticalCapacity := 280,
    practicalCapacity := 200,
    voltageVsLi := ⟨⟨2.8⟩, ⟨4.3⟩, ⟨3.7⟩⟩,
    density := ⟨4.7⟩,
    ionicConductivity := ⟨0.001⟩,
    electronicConductivity := ⟨0.1⟩,
    volumeChange := 3.5,
    thermalStability := ⟨453⟩,  -- 180°C - less stable!
    oxygenRelease := true,
    costPerKg := 35,
    cycleLife := 800,  -- Worse than NMC622!
    cRateCapability := 2.0,
    firstCycleEfficiency := 85 },

  { name := "LCO",
    formula := "LiCoO₂",
    components := [],
    crystalStructure := CrystalStructure.Layered,
    theoreticalCapacity := 274,
    practicalCapacity := 140,
    voltageVsLi := ⟨⟨3.0⟩, ⟨4.2⟩, ⟨3.9⟩⟩,
    density := ⟨5.1⟩,
    ionicConductivity := ⟨0.0001⟩,
    electronicConductivity := ⟨0.001⟩,
    volumeChange := 2.0,
    thermalStability := ⟨423⟩,  -- 150°C - dangerous!
    oxygenRelease := true,
    costPerKg := 80,  -- Expensive due to cobalt
    cycleLife := 500,
    cRateCapability := 1.0,
    firstCycleEfficiency := 92 },

  { name := "NCA",
    formula := "LiNi₀.₈Co₀.₁₅Al₀.₀₅O₂",
    components := [],
    crystalStructure := CrystalStructure.Layered,
    theoreticalCapacity := 279,
    practicalCapacity := 195,
    voltageVsLi := ⟨⟨3.0⟩, ⟨4.3⟩, ⟨3.7⟩⟩,
    density := ⟨4.65⟩,
    ionicConductivity := ⟨0.001⟩,
    electronicConductivity := ⟨0.1⟩,
    volumeChange := 3.0,
    thermalStability := ⟨423⟩,  -- 150°C
    oxygenRelease := true,
    costPerKg := 50,
    cycleLife := 1000,
    cRateCapability := 1.5,
    firstCycleEfficiency := 87 },

  { name := "LMO",
    formula := "LiMn₂O₄",
    components := [],
    crystalStructure := CrystalStructure.Spinel,
    theoreticalCapacity := 148,
    practicalCapacity := 120,
    voltageVsLi := ⟨⟨3.0⟩, ⟨4.3⟩, ⟨4.0⟩⟩,
    density := ⟨4.2⟩,
    ionicConductivity := ⟨0.0001⟩,
    electronicConductivity := ⟨0.001⟩,
    volumeChange := 7.5,
    thermalStability := ⟨523⟩,  -- 250°C - quite safe
    oxygenRelease := true,
    costPerKg := 10,  -- Very cheap!
    cycleLife := 300,  -- Mn dissolution issue
    cRateCapability := 10.0,  -- Excellent power
    firstCycleEfficiency := 90 }
]

/- Common anode compounds -/
def anodeCompounds : List CompoundProps := [
  { name := "LTO",
    formula := "Li₄Ti₅O₁₂",
    components := [],
    crystalStructure := CrystalStructure.Spinel,
    theoreticalCapacity := 175,
    practicalCapacity := 170,
    voltageVsLi := ⟨⟨1.4⟩, ⟨1.7⟩, ⟨1.55⟩⟩,  -- High voltage = safe!
    density := ⟨3.5⟩,
    ionicConductivity := ⟨0.001⟩,
    electronicConductivity := ⟨0.00001⟩,
    volumeChange := 0.2,  -- "Zero-strain"!
    thermalStability := ⟨773⟩,  -- 500°C
    oxygenRelease := false,
    costPerKg := 30,
    cycleLife := 20000,  -- Incredible!
    cRateCapability := 10.0,
    firstCycleEfficiency := 95 },

  { name := "Si-C composite",
    formula := "Si₀.₁C₀.₉",
    components := [],
    crystalStructure := CrystalStructure.Amorphous,
    theoreticalCapacity := 700,
    practicalCapacity := 450,
    voltageVsLi := ⟨⟨0.05⟩, ⟨1.0⟩, ⟨0.3⟩⟩,
    density := ⟨2.3⟩,
    ionicConductivity := ⟨0.0001⟩,
    electronicConductivity := ⟨1.0⟩,
    volumeChange := 60,  -- Still problematic
    thermalStability := ⟨673⟩,
    oxygenRelease := false,
    costPerKg := 50,
    cycleLife := 500,
    cRateCapability := 1.0,
    firstCycleEfficiency := 75 }
]

/- ================================================================
   LEVEL 2.0: VOLTAGE OPERATIONS
   ================================================================ -/

namespace Volt

def add (v1 v2 : Volt) : Volt := ⟨v1.val + v2.val⟩
def sub (v1 v2 : Volt) : Volt := ⟨v1.val - v2.val⟩
def mul (v : Volt) (scalar : Float) : Volt := ⟨v.val * scalar⟩
def div (v : Volt) (scalar : Float) : Volt := ⟨v.val / scalar⟩

instance : Add Volt where add := add
instance : Sub Volt where sub := sub

def abs (v : Volt) : Volt := ⟨Float.abs v.val⟩
def isValid (v : Volt) : Bool := v.val > -10 && v.val < 10  -- Sanity check

end Volt

/- Convert between reference electrodes -/
def toSHE (ep : ElectrodePotential) : Volt :=
  match ep.reference with
  | RefElectrode.SHE => ep.voltage
  | RefElectrode.Li_Li => ⟨ep.voltage.val - 3.04⟩
  | RefElectrode.AgCl => ⟨ep.voltage.val + 0.197⟩
  | RefElectrode.SCE => ⟨ep.voltage.val + 0.241⟩

def fromSHE (v : Volt) (ref : RefElectrode) : ElectrodePotential :=
  match ref with
  | RefElectrode.SHE => ⟨v, ref⟩
  | RefElectrode.Li_Li => ⟨⟨v.val + 3.04⟩, ref⟩
  | RefElectrode.AgCl => ⟨⟨v.val - 0.197⟩, ref⟩
  | RefElectrode.SCE => ⟨⟨v.val - 0.241⟩, ref⟩

/- Cell voltage calculation -/
def cellVoltage (cathode anode : ElectrodePotential) : Volt :=
  (toSHE cathode) - (toSHE anode)

/- Validate voltage window -/
def VoltageWindow.isValid (vw : VoltageWindow) : Bool :=
  vw.min.val < vw.nominal.val && vw.nominal.val < vw.max.val

def VoltageWindow.contains (vw : VoltageWindow) (v : Volt) : Bool :=
  vw.min.val ≤ v.val && v.val ≤ vw.max.val

/- ================================================================
   LEVEL 2.1: VOLTAGE-AWARE CALCULATIONS
   ================================================================ -/

/- Update the capacity calculation functions for BatteryPropsV2 -/
def theoreticalCapacityV2 (bp : BatteryPropsV2) : Float :=
  (bp.valenceElectrons.toFloat * 26801) / bp.atomicMass

def practicalCapacityV2 (bp : BatteryPropsV2) : Float :=
  theoreticalCapacityV2 bp * bp.coulombicEfficiency / 100

def capacityAfterCyclesV2 (bp : BatteryPropsV2) (cycles : Nat) : Float :=
  practicalCapacityV2 bp * (1 - bp.capacityFade * cycles.toFloat / 10000)

/- Calculate energy with proper voltage handling -/
def energyDensity (anode cathode : BatteryPropsV2) (soc : Float) : Float :=
  let voltage := cellVoltage cathode.reductionPotential anode.reductionPotential
  let capacity := min (practicalCapacityV2 anode) (practicalCapacityV2 cathode)
  voltage.val * capacity * soc

/- Voltage sag under load (simplified Peukert) -/
def voltageSag (nominal : Volt) (cRate : Float) (resistance : Float) : Volt :=
  ⟨nominal.val - (cRate * resistance)⟩

/- Check if voltage claim is thermodynamically possible -/
def validateVoltage (claimed : Volt) (cathode anode : BatteryPropsV2) : String :=
  let theoretical := cellVoltage cathode.reductionPotential anode.reductionPotential
  let overpotential := ⟨0.2⟩  -- Typical overpotential losses
  let practical := theoretical - overpotential

  if claimed.val > theoretical.val then
    s!"BS: Claims {claimed.val}V but theoretical max is {theoretical.val}V"
  else if claimed.val > practical.val then
    s!"Suspicious: {claimed.val}V claimed, but {practical.val}V more realistic"
  else
    "Voltage claim is plausible"

/- ================================================================
   LEVEL 2.2: VOLTAGE-BASED BS DETECTION
   ================================================================ -/

def voltageBS (claims : List (String × Float)) : List String :=
  claims.filterMap fun (claim, value) =>
    match claim with
    | "voltage_V" =>
      if value > 5.0 then
        some s!"BS: {value}V exceeds Li-ion theoretical limit (~4.7V)"
      else if value > 4.3 then
        some s!"Warning: {value}V is very aggressive, stability issues likely"
      else none
    | "pack_voltage" =>
      if value > 1000 then
        some s!"Safety: {value}V requires extensive insulation and arc protection"
      else none
    | "charge_voltage" =>
      if value > 4.25 then  -- for Li-ion
        some s!"Dangerous: {value}V charge will cause thermal runaway"
      else none
    | _ => none

/- Check voltage efficiency claims -/
def voltageEfficiency (chargeV : Volt) (dischargeV : Volt) : Float :=
  (dischargeV.val / chargeV.val) * 100

def validateVoltageEfficiency (claimed : Float) (chemistry : String) : String :=
  let typical := match chemistry with
    | "Li-ion" => 95.0
    | "Lead-acid" => 85.0
    | "NiMH" => 90.0
    | _ => 90.0

  if claimed > 99 then
    s!"BS: {claimed}% voltage efficiency violates thermodynamics"
  else if claimed > typical + 5 then
    s!"Suspicious: {claimed}% efficiency is unusually high for {chemistry}"
  else
    "Plausible voltage efficiency"

/- ================================================================
   LEVEL 3.0: THERMAL CALCULATIONS
   ================================================================ -/


/- Arrhenius temperature dependence -/
def arrheniusFactor (activation : KJ.mol) (temp : Kelvin) (refTemp : Kelvin) : Float :=
  let R := 8.314  -- J/(mol·K)
  Float.exp ((activation.val * 1000 / R) * (1 / refTemp.val - 1 / temp.val))

/- Temperature-adjusted conductivity -/
def conductivityAtTemp (baseConduc : MS.m) (temp : Kelvin) : MS.m :=
  let factor := if temp.val < 273 then
                  0.3  -- Massive drop below freezing
                else if temp.val < 298 then
                  0.7 + (temp.val - 273) * 0.012  -- Linear improvement
                else if temp.val < 333 then
                  1.0 + (temp.val - 298) * 0.005  -- Slight improvement
                else
                  0.8  -- Degradation at high temps
  ⟨baseConduc.val * factor⟩

/- Capacity vs temperature (empirical Li-ion model) -/
def capacityTempFactor (temp : Kelvin) : Float :=
  let t := temp.val
  if t < 233 then 0.05      -- -40°C: ~5% capacity
  else if t < 253 then 0.50  -- -20°C: 50% capacity
  else if t < 273 then 0.70  -- 0°C: 70% capacity
  else if t < 298 then 0.85 + (t - 273) * 0.006  -- 25°C: 100%
  else if t < 318 then 1.0   -- 25-45°C: optimal
  else if t < 333 then 0.95  -- 45-60°C: slight loss
  else 0.80                  -- >60°C: degradation

/- Heat generation during charge/discharge -/
def jouleHeating (current : Float) (resistance : Float) (time : Float) : KJ.mol :=
  ⟨current * current * resistance * time / 1000⟩

/- Heat dissipation requirement -/
def heatDissipationPower (batteryMass : Float) (cRate : Float) (efficiency : Float) : Float :=
  let energyDensity := 200.0  -- Wh/kg typical
  let powerIn := batteryMass * energyDensity * cRate
  powerIn * (1 - efficiency / 100)  -- Watts of heat

/- Time to thermal runaway -/
def thermalRunawayTime (initialTemp : Kelvin) (runawayTemp : Kelvin)
                       (heatGenRate : Float) (coolingPower : Float)
                       (mass : Float) (specificHeat : J.kgK) : Float :=
  let netHeatRate := heatGenRate - coolingPower
  if netHeatRate <= 0 then
    999999  -- No runaway
  else
    let tempRise := runawayTemp.val - initialTemp.val
    let energyNeeded := mass * specificHeat.val * tempRise
    energyNeeded / netHeatRate / 60  -- Minutes to runaway

/- Cold weather range loss -/
def coldWeatherRange (nominalRange : Float) (ambientTemp : Kelvin)
                     (heatingPower : Float) : Float :=
  let batteryCapacityFactor := capacityTempFactor ambientTemp
  let heatingEnergyPerKm := if ambientTemp.val < 273 then
                              heatingPower * 60 / 60  -- kWh/km for cabin heat
                            else 0
  let availableRange := nominalRange * batteryCapacityFactor
  let heatingLoss := heatingEnergyPerKm * nominalRange * 0.15  -- 15% for heating
  availableRange - heatingLoss

/- Fast charging thermal limit -/
def maxChargingRate (batteryTemp : Kelvin) (coolingCapacity : Float) : Float :=
  let baseRate := if batteryTemp.val < 283 then 0.5   -- <10°C: 0.5C max
                  else if batteryTemp.val < 298 then 1.0  -- 10-25°C: 1C
                  else if batteryTemp.val < 313 then 2.0  -- 25-40°C: 2C
                  else 0.3  -- >40°C: severely limited
  let coolingBonus := coolingCapacity / 1000  -- kW cooling = +1C rate
  baseRate + coolingBonus

/- ================================================================
  LEVEL 3.1: THERMAL BULLSHIT DETECTION
   ================================================================ -/

/- Check if claimed operating range is physically possible -/
def thermalRangeBS (minTemp maxTemp : Kelvin) (chemistry : String) : String :=
  match chemistry with
  | "Li-ion" =>
    if minTemp.val < 223 then  -- -50°C
      s!"BS: Li-ion electrolyte freezes at -40°C, can't operate at {minTemp.val - 273}°C"
    else if maxTemp.val > 333 then  -- 60°C
      s!"BS: Li-ion separator melts at 60°C, claimed {maxTemp.val - 273}°C operation impossible"
    else "Plausible temperature range"
  | "Li-metal" =>
    if minTemp.val < 233 then
      s!"BS: Li metal becomes brittle below -40°C"
    else if maxTemp.val > 323 then
      s!"Dangerous: Li melts at 180°C, but dendrites form aggressively above 50°C"
    else "Temperature range OK for Li-metal"
  | _ => "Unknown chemistry thermal limits"

/- Fast charging thermal reality check -/
def fastChargeThermalBS (chargeMinutes : Nat) (batteryKWh : Float)
                        (coolingType : String) : String :=
  let chargePower := batteryKWh * 60 / chargeMinutes.toFloat  -- kW
  let heatGenerated := chargePower * 0.1  -- ~10% becomes heat

  let maxCooling := match coolingType with
    | "none" => 0.5      -- Passive cooling only
    | "air" => 2.0       -- Air cooling
    | "liquid" => 10.0   -- Liquid cooling
    | "immersion" => 50.0 -- Immersion cooling
    | _ => 1.0

  if heatGenerated > maxCooling * 2 then
    s!"BS: {chargeMinutes}-min charging generates {heatGenerated}kW heat, " ++
    s!"{coolingType} cooling can only handle {maxCooling}kW. Battery will catch fire."
  else if heatGenerated > maxCooling then
    s!"Warning: Heat generation ({heatGenerated}kW) exceeds cooling capacity ({maxCooling}kW)"
  else
    "Thermal management adequate"

/- Cold weather performance claims -/
def coldWeatherBS (claimedRange : Float) (temp : Kelvin) (chemistry : String) : String :=
  let realCapacityFactor := capacityTempFactor temp
  let heatingLoss := if temp.val < 273 then 0.2 else 0  -- 20% loss to heating

  -- Chemistry-specific adjustments
  let chemistryFactor := match chemistry with
    | "Li-ion" => 1.0      -- Baseline
    | "LFP" => 0.8         -- LFP worse in cold
    | "NMC" => 0.9         -- NMC slightly worse
    | "Li-metal" => 0.7    -- Li-metal terrible in cold
    | "Na-ion" => 1.1      -- Na-ion actually better
    | _ => 1.0

  let realRange := claimedRange * realCapacityFactor * chemistryFactor * (1 - heatingLoss)

  if temp.val < 233 && claimedRange > realRange * 1.2 then  -- -40°C
    s!"BS: {chemistry} at {temp.val - 273}°C, real range is {realRange}km, not {claimedRange}km"
  else if temp.val < 253 && claimedRange > realRange * 1.1 then  -- -20°C
    s!"Suspicious: {chemistry} at {temp.val - 273}°C, expecting ~{realRange}km, claimed {claimedRange}km"
  else
    s!"Cold weather range plausible for {chemistry}"

/- Thermal cycling degradation -/
def thermalCyclingDegradation (minTemp maxTemp : Kelvin) (cycles : Nat) : Float :=
  let deltaT := maxTemp.val - minTemp.val
  let stressFactor := deltaT / 50  -- Every 50°C delta doubles stress
  let baseDegradation := 0.001  -- 0.1% per cycle baseline
  baseDegradation * stressFactor * cycles.toFloat

/- Desert/extreme heat operation -/
def extremeHeatBS (ambientTemp : Kelvin) (claimedLife : Nat) : String :=
  if ambientTemp.val > 323 then  -- 50°C ambient
    let acceleratedAging := arrheniusFactor ⟨50⟩ ambientTemp ⟨298⟩
    let realLife := claimedLife.toFloat / acceleratedAging
    if realLife < 365 then
      s!"BS: At {ambientTemp.val - 273}°C, battery dies in {realLife} days, not {claimedLife} days"
    else
      s!"Warning: {acceleratedAging}x faster degradation at {ambientTemp.val - 273}°C"
  else
    "Temperature within normal operating range"

/- Comprehensive thermal BS check -/
def thermalBSCheck (claims : List (String × Float)) : List String :=
  claims.filterMap fun (claim, value) =>
    match claim with
    | "operating_temp_min_C" =>
      if value < -50 then some s!"BS: {value}°C below any battery electrolyte freezing point"
      else if value < -40 then some s!"Warning: {value}°C requires special Arctic electrolyte"
      else none
    | "operating_temp_max_C" =>
      if value > 80 then some s!"BS: {value}°C exceeds separator melting point"
      else if value > 60 then some s!"Dangerous: {value}°C risks thermal runaway"
      else none
    | "charge_rate_0C" =>
      if value > 0.5 then some s!"BS: Charging at {value}C at 0°C causes Li plating"
      else none
    | "capacity_-20C_percent" =>
      if value > 70 then some s!"BS: No Li-ion maintains {value}% capacity at -20°C"
      else none
    | "capacity_60C_percent" =>
      if value > 95 then some s!"BS: High temp degradation prevents {value}% capacity at 60°C"
      else none
    | _ => none

/- Example thermal validation -/
def validateThermalClaim (batteryType : String) (test : String) : String :=
  match batteryType, test with
  | "Li-ion", "Alaska winter" =>
    coldWeatherBS 500 ⟨233⟩ "Li-ion"  -- -40°C test
  | "Li-ion", "Death Valley summer" =>
    extremeHeatBS ⟨323⟩ 1000  -- 50°C ambient
  | "Li-ion", "5-minute charge" =>
    fastChargeThermalBS 5 75 "liquid"  -- 75kWh in 5 min
  | "LFP", "Nordic operation" =>
    let temp : Kelvin := ⟨248⟩  -- -25°C (correct syntax)
    s!"LFP at -25°C: {capacityTempFactor temp * 100}% capacity, needs pre-heating"
  | _, _ => "Unknown test scenario"

/- Detect impossible thermal management claims -/
def thermalMgmtBS (packSize : Float) (coolingType : String)
                  (claimedTempRise : Float) (cRate : Float) : String :=
  let heatGen := heatDissipationPower packSize cRate 92  -- 92% efficiency typical
  let coolingCapacity := match coolingType with
    | "passive" => packSize * 5    -- 5W/kg passive
    | "air" => packSize * 20        -- 20W/kg forced air
    | "liquid" => packSize * 100    -- 100W/kg liquid
    | "phase_change" => packSize * 200  -- 200W/kg phase change
    | _ => packSize * 10

  let steadyStateTempRise := heatGen / (coolingCapacity * 0.1)  -- Simplified

  if claimedTempRise < steadyStateTempRise * 0.5 then
    s!"BS: {coolingType} cooling can't limit temp rise to {claimedTempRise}°C at {cRate}C"
  else
    s!"Thermal claim plausible with {coolingType} cooling"

/- ================================================================
   LEVEL 4.0: DENDRITE-AWARE VALIDATION
   ================================================================ -/

/- Calculate dendrite growth rate based on current density -/
def dendriteGrowthRate (formsDendrites : Bool) (currentDensity : Float)
                       (suppression : DendriteSuppression) : Float :=
  if not formsDendrites then 0
  else
    let baseRate :=
      if currentDensity < 0.5 then 0.01      -- Very slow
      else if currentDensity < 1.0 then 0.1   -- Slow growth
      else if currentDensity < 2.0 then 1.0   -- Significant
      else if currentDensity < 5.0 then 5.0   -- Rapid
      else 20.0                               -- Catastrophic

    -- Suppression effectiveness (0 = no suppression, 1 = complete)
    let suppressionFactor := match suppression with
      | DendriteSuppression.None => 1.0
      | DendriteSuppression.SolidElectrolyte => 0.05  -- 95% reduction
      | DendriteSuppression.PolymerCoating => 0.3
      | DendriteSuppression.ElectrolyteAdditives => 0.4
      | DendriteSuppression.CurrentDensityControl => 0.2
      | DendriteSuppression.PressureApplication => 0.15
      | DendriteSuppression.AlloyingStrategy => 0.25
      | DendriteSuppression.HostStructure => 0.35
      | DendriteSuppression.PulsedCharging => 0.5

    baseRate * suppressionFactor  -- μm/cycle

/- Cycles to short circuit from dendrite penetration -/
def cyclesToShortCircuit (formsDendrites : Bool) (separatorThickness : Float)
                         (currentDensity : Float) (suppression : DendriteSuppression) : Nat :=
  if not formsDendrites then 999999
  else
    let growthRate := dendriteGrowthRate formsDendrites currentDensity suppression
    if growthRate <= 0 then 999999
    else (separatorThickness / growthRate).toUInt32.toNat

/- Critical current density for dendrite formation (Sand's time) -/
def sandsCriticalCurrent (ionicConductivity : MS.m) (transference : Float)
                         (concentration : Float) : Float :=
  -- J* = 2 * z * F * D * C / (t+ * L)
  -- Simplified: higher conductivity and transference number = higher critical current
  let baseCurrent := 2.0  -- mA/cm² typical for Li
  baseCurrent * (ionicConductivity.val / 10) * transference * (concentration / 1.0)

/- ================================================================
   LEVEL 4.1: DENDRITE-AWARE VALIDATION
   ================================================================ -/

/- Validate cycle life claims for dendrite-forming materials -/
def dendriteCycleValidation (element : BatteryPropsV2) (claimedCycles : Nat)
                            (cRate : Float) (suppression : Option String) : String :=
  if not element.formsDendrites then
    "No dendrite risk for this material"
  else
    -- Convert C-rate to approximate current density (mA/cm²)
    let currentDensity := cRate * 3.0  -- Rough approximation

    -- Parse suppression mechanism
    let suppressionType := match suppression with
      | some "solid-state" => DendriteSuppression.SolidElectrolyte
      | some "polymer" => DendriteSuppression.PolymerCoating
      | some "additives" => DendriteSuppression.ElectrolyteAdditives
      | some "pressure" => DendriteSuppression.PressureApplication
      | some "alloy" => DendriteSuppression.AlloyingStrategy
      | some "host" => DendriteSuppression.HostStructure
      | some "pulsed" => DendriteSuppression.PulsedCharging
      | _ => DendriteSuppression.None

    -- Calculate realistic cycle life with dendrites
    let separatorThickness := 25.0  -- μm typical
    let maxCycles := cyclesToShortCircuit true separatorThickness currentDensity suppressionType

    -- Generate validation message
    if suppression.isNone && claimedCycles > 100 then
      s!"🚫 BS: {element.symbol} forms dendrites. Without suppression, max ~100 cycles, not {claimedCycles}"
    else if claimedCycles > maxCycles * 2 then
      s!"❌ BS: Even with {suppression.getD "no"} suppression, {element.symbol} limited to ~{maxCycles} cycles at {cRate}C"
    else if claimedCycles > maxCycles then
      s!"⚠️ Suspicious: {claimedCycles} cycles claimed, but dendrites limit to ~{maxCycles} with {suppression.getD "no"} suppression"
    else
      s!"✓ Plausible with {suppression.getD "no"} dendrite suppression"

/- Comprehensive dendrite BS detection -/
def dendriteBS (material : String) (claims : List (String × Float))
               (suppression : Option String) : List String :=
  -- Find the material in database
  let element := batteryDatabase.find? (fun e => e.symbol == material)

  match element with
  | none => ["Unknown material"]
  | some elem =>
    if not elem.formsDendrites then []
    else
      claims.filterMap fun (claim, value) =>
        match claim with
        | "cycles" =>
          let validation := dendriteCycleValidation elem value.toUInt32.toNat
                              (claims.find? (·.1 == "c_rate") |>.map (·.2) |>.getD 1.0)
                              suppression
          if validation.containsSubstr "BS" || validation.containsSubstr "Suspicious" then
            some validation
          else none

        | "coulombic_efficiency" =>
          if elem.formsDendrites && suppression.isNone && value > 95 then
            some s!"BS: {material} with dendrites can't achieve {value}% CE without suppression"
          else none

        | "c_rate" =>
          if elem.formsDendrites && value > 2.0 && suppression.isNone then
            some s!"BS: {value}C rate with dendrite-forming {material} = instant short circuit"
          else if elem.formsDendrites && value > 5.0 then
            some s!"BS: No suppression technology enables {value}C with {material}"
          else none

        | "safety_rating" =>
          if elem.formsDendrites && value > 4 && suppression.isNone then
            some s!"BS: Dendrite-forming {material} can't have safety rating {value}/5"
          else none

        | _ => none

/- Dendrite-temperature interaction -/
def dendriteTempInteraction (temp : Kelvin) (formsDendrites : Bool)
                           (suppression : DendriteSuppression) : String :=
  if not formsDendrites then "No dendrite concern"
  else if temp.val < 273 then  -- Below 0°C
    match suppression with
    | DendriteSuppression.SolidElectrolyte =>
      "⚠️ Solid electrolyte brittle at low temp, dendrite breakthrough risk"
    | DendriteSuppression.PolymerCoating =>
      "❌ Polymer coating ineffective below 0°C, dendrites guaranteed"
    | _ => "❌ Dendrite growth accelerated at low temperature"
  else if temp.val > 333 then  -- Above 60°C
    "⚠️ High temp increases dendrite growth rate via enhanced diffusion"
  else
    "Temperature acceptable for dendrite suppression"

/- Multi-factor dendrite risk assessment -/
structure DendriteRisk where
  material : String
  formsDendrites : Bool
  currentDensity : Float      -- mA/cm²
  temperature : Kelvin
  pressure : Float            -- MPa
  electrolyte : String
  suppression : List DendriteSuppression
  deriving Repr

def assessDendriteRisk (risk : DendriteRisk) : String :=
  if not risk.formsDendrites then
    s!"✅ {risk.material} does not form dendrites"
  else
    -- Calculate combined suppression effectiveness
    let totalSuppression := risk.suppression.foldl (fun acc s =>
      let factor := match s with
        | DendriteSuppression.SolidElectrolyte => 0.95
        | DendriteSuppression.PressureApplication => 0.85
        | DendriteSuppression.PolymerCoating => 0.7
        | DendriteSuppression.ElectrolyteAdditives => 0.6
        | DendriteSuppression.CurrentDensityControl => 0.8
        | DendriteSuppression.AlloyingStrategy => 0.75
        | DendriteSuppression.HostStructure => 0.65
        | DendriteSuppression.PulsedCharging => 0.5
        | DendriteSuppression.None => 0
      acc * (1 - factor * 0.5)  -- Diminishing returns on multiple methods
    ) 1.0

    -- Temperature modifier
    let tempModifier :=
      if risk.temperature.val < 273 then 2.0    -- Dendrites worse in cold
      else if risk.temperature.val > 323 then 1.5
      else 1.0

    -- Current density risk
    let currentRisk :=
      if risk.currentDensity > 5 then "EXTREME"
      else if risk.currentDensity > 2 then "HIGH"
      else if risk.currentDensity > 1 then "MODERATE"
      else "LOW"

    -- Final risk score
    let finalRisk := totalSuppression * tempModifier * risk.currentDensity

    if finalRisk > 5 then
      s!"🚫 CATASTROPHIC: {risk.material} will fail in <10 cycles. Current: {currentRisk}, Temp effect: {tempModifier}x"
    else if finalRisk > 2 then
      s!"❌ SEVERE: Dendrite shorts expected in <100 cycles"
    else if finalRisk > 0.5 then
      s!"⚠️ MODERATE: Dendrites manageable with care, ~1000 cycles possible"
    else
      s!"✓ CONTROLLED: Suppression adequate for >5000 cycles"

/- Integration with comprehensive validation -/
def addDendriteCheck (claim : BatteryClaim) (material : String)
                     (suppression : Option String) : String :=
  let dendriteSection := "\\nDENDRITE ANALYSIS:\\n"

  -- Check if material forms dendrites
  let elem := batteryDatabase.find? (fun e => e.symbol == material)

  match elem with
  | none => dendriteSection ++ "Cannot assess dendrite risk - unknown material\\n"
  | some e =>
    if not e.formsDendrites then
      dendriteSection ++ s!"✓ {material} does not form dendrites\\n"
    else
      -- Calculate current density from charge rate
      let chargeCRate := 60.0 / claim.chargeMinutes.toFloat
      let currentDensity := chargeCRate * 3.0  -- Approximation

      let dendriteRisk := assessDendriteRisk {
        material := material
        formsDendrites := true
        currentDensity := currentDensity
        temperature := ⟨273 + claim.minOperatingTemp⟩
        pressure := if suppression == some "pressure" then 10.0 else 0.1
        electrolyte := if suppression == some "solid-state" then "solid" else "liquid"
        suppression := match suppression with
          | some s => [match s with
            | "solid-state" => DendriteSuppression.SolidElectrolyte
            | "pressure" => DendriteSuppression.PressureApplication
            | _ => DendriteSuppression.ElectrolyteAdditives]
          | none => [DendriteSuppression.None]
      }

      let cycleCheck := if claim.cycles > 1000 && suppression.isNone then
        s!"❌ {claim.cycles} cycles impossible with dendrite-forming {material}\\n"
      else ""

      dendriteSection ++ dendriteRisk ++ "\\n" ++ cycleCheck


/- ================================================================
   LEVEL 5.0: COMPOUND AND COMPOSITE MATERIALS
   ================================================================ -/

/- Find compound by name or formula -/
def findCompound (nameOrFormula : String) : Option CompoundProps :=
  (cathodeCompounds ++ anodeCompounds).find?
    (fun c => c.name == nameOrFormula || c.formula == nameOrFormula)

/- Helper for formatting floats to N decimal places -/
def toFixedDecimals (f : Float) (decimals : Nat) : String :=
  let multiplier := (10 ^ decimals).toFloat
  let rounded := (f * multiplier).round / multiplier
  rounded.toString

/- Calculate full cell properties from compounds -/
def fullCellProps (anode cathode : CompoundProps) : String :=
  let voltage := cathode.voltageVsLi.nominal.val - anode.voltageVsLi.nominal.val
  let capacity := min anode.practicalCapacity cathode.practicalCapacity
  let energy := voltage * capacity
  let cycleLife := min anode.cycleLife cathode.cycleLife
  let maxCRate := min anode.cRateCapability cathode.cRateCapability
  let cost := anode.costPerKg + cathode.costPerKg
  s!"{anode.name}/{cathode.name}: {toFixedDecimals voltage 2}V, {capacity.round}mAh/g, " ++
  s!"{energy.round}Wh/kg, {cycleLife} cycles, {toFixedDecimals maxCRate 1}C max, ${cost.round}/kg"

/- ================================================================
   LEVEL 5.1: COMPOUND-BASED BS DETECTION
   ================================================================ -/

/- Validate compound chemistry claims -/
def compoundChemistryBS (compound : String) (claimedCapacity : Float)
                        (claimedCycles : Nat) : String :=
  match findCompound compound with
  | some c =>
    let capacityBS := if claimedCapacity > c.theoreticalCapacity then
      s!"BS: {compound} theoretical limit is {c.theoreticalCapacity} mAh/g, not {claimedCapacity}"
    else if claimedCapacity > c.practicalCapacity * 1.2 then
      s!"Suspicious: {compound} typically achieves {c.practicalCapacity} mAh/g, claimed {claimedCapacity}"
    else "Capacity plausible"

    let cycleBS := if claimedCycles > c.cycleLife * 2 then
      s!"BS: {compound} typical life is {c.cycleLife} cycles, not {claimedCycles}"
    else "Cycle life plausible"

    s!"{capacityBS}\\n{cycleBS}"
  | none => s!"Unknown compound: {compound}"

/- Safety comparison of compounds -/
def safetyClaim (compound : String) (claim : String) : String :=
  match findCompound compound, claim with
  | some c, "no thermal runaway" =>
    if c.thermalStability.val < 473 then  -- <200°C
      s!"BS: {compound} decomposes at {c.thermalStability.val - 273}°C, can undergo thermal runaway"
    else if c.oxygenRelease then
      s!"Dangerous: {compound} releases oxygen on decomposition, accelerates fire"
    else
      s!"{compound} is relatively safe (stable to {c.thermalStability.val - 273}°C)"
  | some c, "fireproof" =>
    if c.oxygenRelease then
      s!"BS: {compound} releases oxygen, definitely not fireproof"
    else if c.thermalStability.val < 523 then
      s!"False: {compound} decomposes at {c.thermalStability.val - 273}°C"
    else
      "Relatively fire-resistant"
  | _, _ => "Cannot validate safety claim"

/- NMC ratio progression reality check -/
def nmcProgressionBS (nickelContent : Float) (claim : String) : String :=
  -- Higher Ni = higher capacity but worse stability
  let stabilityTemp := 493 - nickelContent * 0.5  -- Approximation
  let cycleLife := (2000 * (1 - nickelContent / 100)).toUInt32.toNat  -- Option 1
  -- OR: let cycleLife := ((2000 * (1 - nickelContent / 100)).floor).natAbs  -- Option 2
  let practicalCapacity := 140 + nickelContent * 0.8

  match claim with
  | "higher capacity and longer life" =>
    s!"BS: At {nickelContent}% Ni, you get {practicalCapacity} mAh/g BUT only {cycleLife} cycles"
  | "safer than LFP" =>
    if nickelContent > 60 then
      s!"BS: NMC{nickelContent} decomposes at {stabilityTemp}°C, LFP stable to 270°C"
    else "Safety claim needs verification"
  | _ => "Claim needs specific validation"

/- Solid-state with compounds -/
def solidStateCompoundBS (cathode : String) (electrolyte : String)
                         (claimedConductivity : Float) : String :=
  match findCompound cathode with
  | some _ =>
    let interfaceResistance := match electrolyte with
      | "sulfide" => 10.0    -- Low resistance
      | "oxide" => 1000.0    -- High resistance
      | "polymer" => 100.0   -- Medium resistance
      | _ => 500.0

    let maxConductivity := 10.0 / (1 + interfaceResistance / 100)

    if claimedConductivity > maxConductivity then
      s!"BS: {cathode}/{electrolyte} interface limits conductivity to {maxConductivity} mS/cm"
    else
      "Conductivity claim plausible for solid-state"
  | none => "Unknown cathode compound"

/- Helper function for cleaner evaluation -/
def evalFullCell (anodeName cathodeName : String) : String :=
  match anodeCompounds.find? (·.name == anodeName),
        cathodeCompounds.find? (·.name == cathodeName) with
  | some anode, some cathode => fullCellProps anode cathode
  | _, _ => s!"Compound not found: {anodeName} or {cathodeName}"




#eval evalFullCell "LTO" "LFP"
-- "LTO/LFP: 1.90V, 170mAh/g, 323Wh/kg, 4000 cycles, 10.0C max, $45/kg"

#eval evalFullCell "Si-C composite" "NMC811"
-- "Si-C composite/NMC811: 3.40V, 200mAh/g, 680Wh/kg, 500 cycles, 1.0C max, $85/kg"

/- Test real battery chemistry combinations -/
#eval match anodeCompounds.find? (·.name == "LTO"),
           cathodeCompounds.find? (·.name == "LFP") with
  | some anode, some cathode => fullCellProps anode cathode
  | _, _ => "Compound not found"
-- "LTO/LFP: 1.90V, 170mAh/g, 323Wh/kg, 4000 cycles, 10.0C max, $45/kg"

#eval match anodeCompounds.find? (·.name == "Si-C composite"),
           cathodeCompounds.find? (·.name == "NMC811") with
  | some anode, some cathode => fullCellProps anode cathode
  | _, _ => "Compound not found"
-- "Si-C composite/NMC811: 3.40V, 200mAh/g, 680Wh/kg, 500 cycles, 1.0C max, $85/kg"

#eval compoundChemistryBS "NMC811" 250 2000
-- "Suspicious: NMC811 typically achieves 200.000000 mAh/g, claimed 250.000000
-- BS: NMC811 typical life is 800 cycles, not 2000"

#eval compoundChemistryBS "LFP" 180 10000
-- "Capacity plausible
-- BS: LFP typical life is 4000 cycles, not 10000"

#eval safetyClaim "NMC811" "no thermal runaway"
-- "BS: NMC811 decomposes at 180°C, can undergo thermal runaway"

#eval safetyClaim "LFP" "fireproof"
-- "Relatively fire-resistant"

#eval nmcProgressionBS 90 "higher capacity and longer life"
-- "BS: At 90.000000% Ni, you get 212.000000 mAh/g BUT only 200 cycles"



/- ================================================================
   LEVEL 6.0: COMPREHENSIVE MULTI-PHYSICS VALIDATION
   ================================================================ -/

/- ================================================================
   LEVEL 5.0: COMPREHENSIVE MULTI-PHYSICS VALIDATION WITH DENDRITES
   ================================================================ -/

def comprehensiveValidation (claim : BatteryClaim) : String :=
  -- Header
  let header := s!"=== {claim.chemistry} Battery Validation ===\\n"

  -- Detect if chemistry involves dendrite-forming materials
  let dendriteRisk := claim.chemistry.containsSubstr "Li-metal" ||
                      claim.chemistry.containsSubstr "Li-Metal" ||
                      claim.chemistry.containsSubstr "Zn" ||
                      claim.chemistry.containsSubstr "zinc" ||
                      claim.chemistry.containsSubstr "Na-metal" ||
                      claim.chemistry.containsSubstr "Mg"

  -- Infer suppression from chemistry name or cooling type
  let likelySuppression :=
    if claim.chemistry.containsSubstr "solid" || claim.chemistry.containsSubstr "Solid" then
      some "solid-state"
    else if claim.chemistry.containsSubstr "polymer" || claim.chemistry.containsSubstr "Polymer" then
      some "polymer"
    else if claim.chemistry.containsSubstr "alloy" || claim.chemistry.containsSubstr "Alloy" then
      some "alloy"
    else if claim.costPerKWh > 300 then  -- Expensive might mean advanced suppression
      some "advanced"
    else
      none

  -- VOLTAGE ANALYSIS (unchanged)
  let voltageChecks := s!"VOLTAGE ANALYSIS:\\n"
  let voltageIssues :=
    if claim.cellVoltage > 4.7 then
      s!"❌ Cell voltage {claim.cellVoltage}V exceeds Li-ion theoretical limit\\n"
    else if claim.cellVoltage > 4.3 then
      s!"⚠️ Cell voltage {claim.cellVoltage}V requires special electrolyte\\n"
    else
      s!"✓ Cell voltage {claim.cellVoltage}V is plausible\\n"

  let chargeVoltageIssues :=
    if claim.chargeVoltage > (claim.cellVoltage + 0.5) then
      s!"❌ Charge voltage {claim.chargeVoltage}V will cause electrolyte decomposition\\n"
    else if claim.chargeVoltage > 4.3 then
      s!"⚠️ Charge voltage {claim.chargeVoltage}V is aggressive\\n"
    else
      s!"✓ Charge voltage acceptable\\n"

  let efficiencyIssues :=
    if claim.voltageEfficiency > 99 then
      s!"❌ {claim.voltageEfficiency}% efficiency violates thermodynamics\\n"
    else if claim.voltageEfficiency > 95 then
      s!"⚠️ {claim.voltageEfficiency}% efficiency is optimistic\\n"
    else
      s!"✓ Voltage efficiency realistic\\n"

  -- THERMAL ANALYSIS (unchanged)
  let thermalChecks := s!"\\nTHERMAL ANALYSIS:\\n"

  let tempRangeIssues :=
    if claim.minOperatingTemp < -50 then
      s!"❌ {claim.minOperatingTemp}°C: Electrolyte frozen solid\\n"
    else if claim.maxOperatingTemp > 80 then
      s!"❌ {claim.maxOperatingTemp}°C: Separator melted, fire imminent\\n"
    else
      s!"✓ Temperature range feasible\\n"

  let chargePower := 75.0 * 60 / claim.chargeMinutes.toFloat
  let heatGen := chargePower * 0.1
  let maxCooling := match claim.coolingType with
    | "none" => 0.5
    | "air" => 2.0
    | "liquid" => 10.0
    | _ => 1.0

  let chargingIssues :=
    if heatGen > maxCooling * 2 then
      s!"❌ {claim.chargeMinutes}-min charge: {heatGen}kW heat vs {maxCooling}kW cooling = FIRE\\n"
    else if heatGen > maxCooling then
      s!"⚠️ Thermal management marginal during fast charge\\n"
    else
      s!"✓ Fast charging thermally manageable\\n"

  let coldCapacity := capacityTempFactor ⟨253⟩
  let voltageSagCold := 0.9
  let realColdRange := claim.coldWeatherRange * coldCapacity * voltageSagCold * 0.8

  let coldWeatherIssues :=
    if claim.coldWeatherRange > realColdRange * 1.5 then
      s!"❌ Cold range claim: {claim.coldWeatherRange}km impossible, max {realColdRange}km\\n"
    else
      s!"✓ Cold weather range plausible\\n"

  -- NEW: DENDRITE ANALYSIS
  let dendriteChecks := s!"\\nDENDRITE ANALYSIS:\\n"

  let dendriteIssues := if not dendriteRisk then
    s!"✓ Chemistry does not involve dendrite-forming materials\\n"
  else
    -- Calculate charge C-rate and current density
    let chargeCRate := 60.0 / claim.chargeMinutes.toFloat
    let currentDensity := chargeCRate * 3.0  -- Approximation: mA/cm²

    -- Estimate max cycles with dendrites
    let separatorThickness := 25.0  -- μm typical
    let suppressionFactor := match likelySuppression with
      | some "solid-state" => 0.05
      | some "polymer" => 0.3
      | some "alloy" => 0.25
      | some "advanced" => 0.1
      | _ => 1.0

    let dendriteGrowthRate :=
      if currentDensity < 1.0 then 0.1 * suppressionFactor
      else if currentDensity < 2.0 then 1.0 * suppressionFactor
      else if currentDensity < 5.0 then 5.0 * suppressionFactor
      else 20.0 * suppressionFactor  -- μm/cycle

    let maxDendriteCycles := if dendriteGrowthRate > 0 then
      (separatorThickness / dendriteGrowthRate).toUInt32.toNat
    else 999999

    -- Build dendrite assessment
    let dendriteCycleCheck :=
      if likelySuppression.isNone && claim.cycles > 100 then
        s!"❌ {claim.chemistry} forms dendrites: max ~100 cycles without suppression, not {claim.cycles}\\n"
      else if claim.cycles > maxDendriteCycles * 2 then
        s!"❌ Even with {likelySuppression.getD "no"} suppression, limited to ~{maxDendriteCycles} cycles at {chargeCRate}C\\n"
      else if claim.cycles > maxDendriteCycles then
        s!"⚠️ {claim.cycles} cycles suspicious: dendrites limit to ~{maxDendriteCycles} cycles\\n"
      else
        s!"✓ Cycle life plausible with {likelySuppression.getD "assumed"} dendrite suppression\\n"

    let dendriteChargeCheck :=
      if chargeCRate > 2.0 && likelySuppression.isNone then
        s!"❌ {chargeCRate}C charging with dendrites = instant short circuit\\n"
      else if chargeCRate > 5.0 && dendriteRisk then
        s!"❌ No suppression enables {chargeCRate}C with dendrite-forming materials\\n"
      else ""

    let dendriteColdCheck :=
      if claim.minOperatingTemp < -10 && dendriteRisk then
        s!"⚠️ Dendrite growth accelerated at {claim.minOperatingTemp}°C\\n"
      else ""

    dendriteCycleCheck ++ dendriteChargeCheck ++ dendriteColdCheck

  -- COMBINED STRESS TESTS (enhanced with dendrites)
  let combinedChecks := s!"\\nCOMBINED STRESS TESTS:\\n"

  let highVoltHighTemp :=
    if claim.cellVoltage > 4.2 && claim.maxOperatingTemp > 60 then
      s!"❌ CRITICAL: {claim.cellVoltage}V + {claim.maxOperatingTemp}°C = rapid degradation\\n"
    else ""

  -- Enhanced: Fast charge + cold + dendrites = disaster
  let fastChargeCold :=
    if claim.chargeMinutes < 30 && claim.minOperatingTemp < -10 then
      if dendriteRisk then
        s!"❌ CRITICAL: Fast charging + {claim.minOperatingTemp}°C + dendrites = guaranteed failure\\n"
      else
        s!"❌ CRITICAL: Fast charging at {claim.minOperatingTemp}°C = lithium plating\\n"
    else ""

  -- NEW: Dendrite + voltage efficiency incompatibility
  let dendriteEfficiencyConflict :=
    if dendriteRisk && likelySuppression.isNone && claim.voltageEfficiency > 95 then
      s!"❌ Dendrite dead lithium formation prevents {claim.voltageEfficiency}% efficiency\\n"
    else ""

  let thermalCyclingStress := (claim.maxOperatingTemp - claim.minOperatingTemp) / 50
  let adjustedCycleLife := (claim.cycles.toFloat / (1 + thermalCyclingStress)).toUInt32.toNat
  let cycleLifeIssues :=
    if thermalCyclingStress > 2 && claim.cycles > adjustedCycleLife * 2 then
      s!"❌ Thermal cycling stress reduces life to ~{adjustedCycleLife} cycles, not {claim.cycles}\\n"
    else ""

  let maxEnergy := claim.cellVoltage * claim.capacity
  let energyIssues :=
    if claim.energyDensity > maxEnergy * 1.2 then
      s!"❌ Energy {claim.energyDensity}Wh/kg impossible with {claim.cellVoltage}V × {claim.capacity}mAh/g\\n"
    else ""

  -- ECONOMIC ANALYSIS (enhanced)
  let costChecks := s!"\\nECONOMIC ANALYSIS:\\n"
  let costIssues :=
    if claim.costPerKWh < 100 && claim.productionScale == "lab" then
      s!"❌ ${claim.costPerKWh}/kWh impossible at lab scale\\n"
    else if claim.costPerKWh < 80 then
      s!"❌ ${claim.costPerKWh}/kWh below raw material costs\\n"
    else if dendriteRisk && likelySuppression.isSome && claim.costPerKWh < 150 then
      s!"⚠️ ${claim.costPerKWh}/kWh seems low for dendrite suppression technology\\n"
    else
      s!"✓ Cost plausible for {claim.productionScale} production\\n"

  -- Overall assessment (now includes dendrite issues)
  let criticalCount :=
    [voltageIssues, chargeVoltageIssues, chargingIssues, coldWeatherIssues,
     dendriteIssues, highVoltHighTemp, fastChargeCold, dendriteEfficiencyConflict,
     cycleLifeIssues, energyIssues, costIssues]
    |>.filter (fun s => s.containsSubstr "❌")
    |>.length

  let warningCount :=
    [voltageIssues, chargeVoltageIssues, efficiencyIssues, chargingIssues,
     dendriteIssues, costIssues]
    |>.filter (fun s => s.containsSubstr "⚠️")
    |>.length

  let verdict := s!"\\n=== VERDICT ===\\n"
  let finalAssessment :=
    if criticalCount >= 3 then
      s!"🚫 TOTAL BS: {criticalCount} critical violations, {warningCount} warnings\\n" ++
      s!"This battery violates fundamental physics and cannot exist.\\n"
    else if criticalCount >= 1 then
      s!"❌ HIGHLY SUSPICIOUS: {criticalCount} critical issues, {warningCount} warnings\\n" ++
      s!"Major claims are impossible or extremely misleading.\\n"
    else if warningCount >= 3 then  -- Increased threshold for warnings
      s!"⚠️ QUESTIONABLE: {warningCount} warnings\\n" ++
      s!"Claims are exaggerated but not impossible.\\n"
    else
      s!"✅ PLAUSIBLE: Claims appear realistic.\\n"

  -- Special dendrite verdict addendum
  let dendriteAddendum := if dendriteRisk && criticalCount >= 1 then
    s!"Note: Dendrite-forming chemistry requires advanced suppression for claimed performance.\\n"
  else ""

  -- Compile full report
  header ++ voltageChecks ++ voltageIssues ++ chargeVoltageIssues ++ efficiencyIssues ++
  thermalChecks ++ tempRangeIssues ++ chargingIssues ++ coldWeatherIssues ++
  dendriteChecks ++ dendriteIssues ++
  combinedChecks ++ highVoltHighTemp ++ fastChargeCold ++ dendriteEfficiencyConflict ++
  cycleLifeIssues ++ energyIssues ++
  costChecks ++ costIssues ++
  verdict ++ finalAssessment ++ dendriteAddendum



-- Realistic claim (Tesla Model 3 like)
#eval comprehensiveValidation {
  chemistry := "NMC622",
  energyDensity := 250,
  capacity := 180,
  cycles := 1500,
  cellVoltage := 3.7,
  chargeVoltage := 4.2,
  voltageEfficiency := 92,
  minOperatingTemp := -20,
  maxOperatingTemp := 50,
  chargeMinutes := 30,
  coolingType := "liquid",
  coldWeatherRange := 300,
  costPerKWh := 150,
  productionScale := "mass"
}
/-
"=== NMC622 Battery Validation ===
VOLTAGE ANALYSIS:
✓ Cell voltage 3.700000V is plausible
✓ Charge voltage acceptable
✓ Voltage efficiency realistic

THERMAL ANALYSIS:
✓ Temperature range feasible
⚠️  Thermal management marginal during fast charge
❌ Cold range claim: 300.000000km impossible, max 151.200000km

DENDRITE ANALYSIS:
✓ Chemistry does not involve dendrite-forming materials

COMBINED STRESS TESTS:
--
ECONOMIC ANALYSIS:
✓ Cost plausible for mass production

=== VERDICT ===
❌ HIGHLY SUSPICIOUS: 1 critical issues, 1 warnings
Major claims are impossible or extremely misleading."
-/

-- Optimistic but possible claim
#eval comprehensiveValidation {
  chemistry := "NMC811",
  energyDensity := 300,
  capacity := 200,
  cycles := 1000,
  cellVoltage := 3.8,
  chargeVoltage := 4.3,
  voltageEfficiency := 95,
  minOperatingTemp := -30,
  maxOperatingTemp := 60,
  chargeMinutes := 15,
  coolingType := "liquid",
  coldWeatherRange := 400,
  costPerKWh := 120,
  productionScale := "pilot"
}
/-
"=== NMC811 Battery Validation ===
VOLTAGE ANALYSIS:
✓ Cell voltage 3.800000V is plausible
✓ Charge voltage acceptable
✓ Voltage efficiency realistic

THERMAL ANALYSIS:
Temperature range feasible
❌ 15-min charge: 30.000000kW heat vs 10.000000kW cooling = FIRE
❌ Cold range claim: 400.000000km impossible, max 201.600000km

DENDRITE ANALYSIS:
✓ Chemistry does not involve dendrite-forming materials

COMBINED STRESS TESTS:
❌ CRITICAL: Fast charging at -30.000000°C = lithium plating

ECONOMIC ANALYSIS:
✓ Cost plausible for pilot production

=== VERDICT ===
🚫 TOTAL BS: 3 critical violations, 0 warnings
This battery violates fundamental physics and cannot exist."
-/


-- Total BS claim (typical breakthrough announcement)
#eval comprehensiveValidation {
  chemistry := "Revolutionary Li-Metal",
  energyDensity := 500,
  capacity := 400,
  cycles := 5000,
  cellVoltage := 4.5,
  chargeVoltage := 4.8,
  voltageEfficiency := 99,
  minOperatingTemp := -50,
  maxOperatingTemp := 90,
  chargeMinutes := 5,
  coolingType := "air",
  coldWeatherRange := 600,
  costPerKWh := 50,
  productionScale := "lab"
}
/-
"=== Revolutionary Li-Metal Battery Validation ===
VOLTAGE ANALYSIS:
⚠️  Cell voltage 4.500000V requires special electrolyte
⚠️  Charge voltage 4.800000V is aggressive
⚠️  99.000000% efficiency is optimistic

THERMAL ANALYSIS:
❌ 90.000000°C: Separator melted, fire imminent
❌ 5-min charge: 90.000000kW heat vs 2.000000kW cooling = FIRE
❌ Cold range claim: 600.000000km impossible, max 302.400000km

DENDRITE ANALYSIS:
❌ Revolutionary Li-Metal forms dendrites: max ~100 cycles without suppression, not 5000
❌ 12.000000C charging with dendrites = instant short circuit
⚠️ Dendrite growth accelerated at -50.000000°C

COMBINED STRESS TESTS:
❌ CRITICAL: 4.500000V + 90.000000°C = rapid degradation
❌ CRITICAL: Fast charging at -50.000000°C = lithium plating
❌ Thermal cycling stress reduces life to ~1315 cycles, not 5000

ECONOMIC ANALYSIS:
❌ $50.000000/kWh impossible at lab scale

=== VERDICT ===
🚫 TOTAL BS: 9 critical violations, 4 warnings
This battery violates fundamental physics and cannot exist."
-/

-- Create a one-liner BS detector
def quickBS (energy : Float) (cycles : Nat) (chargeMin : Nat) (cost : Float) : String :=
  let violations :=
    (if energy > 400 then 1 else 0) +
    (if cycles > 3000 && energy > 250 then 1 else 0) +
    (if chargeMin < 10 then 1 else 0) +
    (if cost < 100 then 1 else 0)

  if violations >= 3 then "🚫 TOTAL BS"
  else if violations >= 2 then "❌ HIGHLY SUSPICIOUS"
  else if violations >= 1 then "⚠️  QUESTIONABLE"
  else "✅ PLAUSIBLE"

#eval quickBS 500 5000 5 50  -- "🚫 TOTAL BS"
#eval quickBS 300 2000 15 120 -- "⚠️  QUESTIONABLE"
#eval quickBS 250 1500 30 150 -- "✅ PLAUSIBLE"
