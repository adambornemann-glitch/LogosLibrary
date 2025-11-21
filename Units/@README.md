# Units: Foundation Layer

**Lines**: ~14,000  
**Status**: ✅ Stable  
**Purpose**: Type-safe dimensional analysis for all of Logos Library

---

## Overview

The Units section is the **foundation** of Logos Library. Every physical quantity in the library - from Planck's constant to black hole masses - must use this units system.

**Core principle**: The type system enforces dimensional correctness. You cannot add a length to a time. You cannot multiply energies without getting the right dimensions. The compiler catches dimensional errors.

---

## Quick Start
```lean
import LogosLibrary.Units.Core.SI
import LogosLibrary.Units.Physics.Quantum

-- Define a length with type safety
def hydrogen_radius : Length := 
  ⟨5.29e-11, by units⟩  -- Bohr radius in meters

-- Define energy
def ionization_energy : Energy := 
  ⟨13.6 * eV, by units⟩  -- Electron volts

-- The type system prevents nonsense
def bad_sum := hydrogen_radius + ionization_energy  -- ❌ TYPE ERROR!

-- But physically meaningful operations work
def photon_energy (λ : Length) : Energy :=
  h * c / λ  -- ✅ Dimensions check out!

-- Example computation
#eval photon_energy ⟨656e-9, by units⟩  -- Red Hα line
-- Result: Energy with correct value
```

---

## The Triple-Type Architecture

We support **three number types** for different use cases:

### **Float** - Engineering & Numerical Work
```lean
-- Fast, approximate calculations
def resistor_power (V : Voltage Float) (I : Current Float) : Power Float :=
  V * I

-- Good for: simulations, engineering, rough estimates
-- Precision: ~15 decimal digits
-- Speed: Fast (native CPU operations)
```

**When to use**: 
- Numerical simulations
- Engineering calculations  
- Quick estimates
- Performance-critical code

### **ℚ** - Exact Rational Calculations
```lean
-- Exact arithmetic, no rounding errors
def stoichiometry (moles_H2O : Moles ℚ) : Moles ℚ :=
  2 * moles_H2O  -- Exactly 2, not 1.9999999...

-- Good for: chemistry, exact ratios, accounting
-- Precision: Infinite (stored as numerator/denominator)
-- Speed: Slower than Float, but exact
```

**When to use**:
- Chemical stoichiometry
- Exact ratios and fractions
- When rounding errors are unacceptable
- Formal proofs requiring exact values

### **ℝ** - Theoretical Proofs
```lean
-- Real analysis for formal verification
theorem energy_momentum_relation (E : Energy ℝ) (p : Momentum ℝ) (m : Mass ℝ) :
  E^2 = (p * c)^2 + (m * c^2)^2 := by
  -- Formal proof using real number properties

-- Good for: theorems, continuous mathematics, limits
-- Precision: Mathematical (not computational)
-- Speed: Not for computation (proof objects only)
```

**When to use**:
- Deep theorem proofs (Robertson, Stone, etc.)
- Continuous analysis
- Formal mathematical arguments
- When you need real number completeness

---

## Directory Structure
```
Units/
├── Core/                    # Foundation (use this)
│   ├── SI.lean              # Base SI units (m, kg, s, A, K, mol, cd)
│   ├── Constants.lean       # Fundamental constants (c, ℏ, G, kB, e)
│   ├── Prefixes.lean        # SI prefixes (nano-, micro-, kilo-, mega-)
│   └── Derived.lean         # Derived units (N, J, W, V, Ω, etc.)
│
├── Physics/                 # Domain-specific physics units
│   ├── Quantum.lean         # ℏ, electron mass, fine structure, etc.
│   ├── Astronomy.lean       # Parsec, light-year, solar mass, AU
│   ├── Mechanics.lean       # Force, energy, momentum, torque
│   ├── Fluids.lean          # Viscosity, flow rate, Reynolds number
│   ├── Optics.lean          # Refractive index, focal length, luminance
│   ├── Waves.lean           # Wavelength, frequency, wave number
│   ├── Thermal.lean         # Heat capacity, thermal conductivity
│   ├── EM.lean              # Permittivity, permeability, impedance
│   ├── Relativity.lean      # Four-momentum, proper time, curvature
│   └── Radiation.lean       # Becquerel, Gray, Sievert, dose
│
├── Chemistry/               # Chemistry-specific units
│   ├── Crystallography.lean # Unit cells, lattice parameters
│   ├── Materials.lean       # Young's modulus, hardness, thermal expansion
│   └── Minerals.lean        # Density, composition, crystal systems
│
└── Information/             # Information theory units
    ├── Quantum.lean         # Qubit measures, entanglement entropy
    └── Statistics.lean      # Shannon entropy, mutual information
```

---

## Design Philosophy

### **Only Fundamentals in Core**

The `Core/` directory contains **only** truly universal constants:
```lean
-- ✅ In Core/Constants.lean
def c : Velocity ℝ := ⟨299792458, by units⟩              -- Speed of light
def ℏ : Action ℝ := ⟨1.054571817e-34, by units⟩         -- Planck constant
def G : GravitationalConstant ℝ := ⟨6.67430e-11, by units⟩  -- Newton's G
def kB : BoltzmannConstant ℝ := ⟨1.380649e-23, by units⟩    -- Boltzmann
def e : Charge ℝ := ⟨1.602176634e-19, by units⟩         -- Elementary charge
```

**Everything else goes in domain modules**:
```lean
-- ❌ NOT in Core
-- ✅ In Physics/Astronomy.lean
def hubble_constant : HubbleParameter := ...

-- ❌ NOT in Core  
-- ✅ In Physics/Quantum.lean
def fine_structure_constant : Dimensionless := e^2 / (4 * π * ε₀ * ℏ * c)
```

**Why this matters**: Keeps Core minimal and universally applicable. Domain-specific constants belong with their domains.

---

## How to Use Units

### **Import What You Need**
```lean
-- For basic SI units
import LogosLibrary.Units.Core.SI
import LogosLibrary.Units.Core.Constants

-- For specific physics domains
import LogosLibrary.Units.Physics.Quantum
import LogosLibrary.Units.Physics.Astronomy

-- For chemistry
import LogosLibrary.Units.Chemistry.Materials
```

### **Define Quantities with Units**
```lean
-- Explicit type annotation (recommended for clarity)
def proton_mass : Mass Float := ⟨1.672621898e-27, by units⟩

-- Type inference (when obvious from context)
def compute_energy (m : Mass Float) : Energy Float :=
  m * c^2

-- With prefixes
def wavelength : Length Float := ⟨650 * nano, by units⟩  -- 650 nm
def capacitance : Capacitance Float := ⟨100 * micro, by units⟩  -- 100 μF
```

### **Dimensional Analysis Enforced**
```lean
-- ✅ Type-safe operations
def kinetic_energy (m : Mass) (v : Velocity) : Energy :=
  (1/2) * m * v^2  -- Dimensions: M * (L/T)^2 = M*L^2/T^2 ✓

def momentum (m : Mass) (v : Velocity) : Momentum :=
  m * v  -- Dimensions: M * L/T ✓

-- ❌ Compiler catches dimensional errors
def nonsense (E : Energy) (t : Time) : Mass :=
  E + t  -- TYPE ERROR: Cannot add Energy to Time!

def also_nonsense (L : Length) : Energy :=
  L * L  -- TYPE ERROR: Length^2 ≠ Energy!
```

### **Unit Conversions**
```lean
-- Built-in conversions for common cases
def energy_in_eV (E : Energy Float) : Float :=
  E.to_eV  -- Convert to electron volts

def distance_in_parsecs (d : Length Float) : Float :=
  d.to_parsec  -- Convert to parsecs

-- Custom conversions via dimensional analysis
def frequency_to_wavelength (f : Frequency) : Length :=
  c / f  -- λ = c/f (type-safe!)
```

---

## Adding New Units

### **Step 1: Determine Where It Belongs**

- **Truly fundamental?** → `Core/Constants.lean` (rare!)
- **Physics domain?** → `Physics/[Domain].lean`
- **Chemistry?** → `Chemistry/[Domain].lean`
- **New domain?** → Create new file in appropriate section

### **Step 2: Define the Unit**
```lean
-- Example: Adding a new constant to Physics/Quantum.lean

/-- Rydberg constant for hydrogen
Used in atomic spectroscopy: 1/λ = R∞ * (1/n₁² - 1/n₂²)
Source: CODATA 2018
-/
def rydberg_constant : WaveNumber ℝ := 
  ⟨10973731.568160, by units⟩  -- m⁻¹

/-- Fine structure constant
α = e²/(4πε₀ℏc) ≈ 1/137
Dimensionless coupling constant of electromagnetism
-/
def fine_structure_constant : Dimensionless ℝ :=
  e^2 / (4 * π * ε₀ * ℏ * c)
```

### **Step 3: Add Documentation**

Every constant needs:
- Doc comment explaining what it is
- Physical context (what it's used for)
- Source citation (CODATA year, paper, etc.)
- Dimensions explicit in type

### **Step 4: Add Tests**
```lean
-- In Tests/Units/Physics/Quantum.lean

theorem fine_structure_value_approx :
  abs (fine_structure_constant.val - 1/137.036) < 0.001 := by
  norm_num
  -- Verify the computed value matches known value

theorem rydberg_unit_check :
  rydberg_constant.dimension = WaveNumber.dimension := by
  rfl  -- Type system guarantees this
```

---

## Common Patterns

### **Dimensionless Quantities**
```lean
-- Ratios are dimensionless
def efficiency (E_out : Energy) (E_in : Energy) : Dimensionless :=
  E_out / E_in

def mass_ratio (m1 : Mass) (m2 : Mass) : Dimensionless :=
  m1 / m2

-- Reynolds number (dimensionless fluid flow parameter)
def reynolds_number (ρ : Density) (v : Velocity) (L : Length) (μ : Viscosity) : Dimensionless :=
  ρ * v * L / μ
```

### **Compound Units**
```lean
-- Force = Mass * Acceleration
def force_from_ma (m : Mass) (a : Acceleration) : Force :=
  m * a  -- Type checks: M * L/T² = Force ✓

-- Power = Energy / Time
def power_from_energy (E : Energy) (t : Time) : Power :=
  E / t  -- Type checks: Energy/Time = Power ✓

-- Pressure = Force / Area
def pressure_from_force (F : Force) (A : Area) : Pressure :=
  F / A  -- Type checks: Force/Length² = Pressure ✓
```

### **Derived Constants**
```lean
-- Compton wavelength: λ_C = h/(m*c)
def compton_wavelength (m : Mass) : Length :=
  h / (m * c)

-- Schwarzschild radius: r_s = 2GM/c²
def schwarzschild_radius (M : Mass) : Length :=
  2 * G * M / c^2

-- Thermal de Broglie wavelength: λ_th = h/√(2πmkT)
def thermal_wavelength (m : Mass) (T : Temperature) : Length :=
  h / Real.sqrt (2 * π * m * kB * T)
```

---

## Type Safety Examples

### **What the Type System Prevents**
```lean
-- ❌ Adding incompatible dimensions
def bad1 (E : Energy) (m : Mass) := E + m
-- Error: type mismatch, Energy ≠ Mass

-- ❌ Wrong exponent
def bad2 (v : Velocity) := v^3  -- Returns Velocity^3, not Energy!

-- ❌ Forgetting a factor
def bad3 (m : Mass) (v : Velocity) : Energy := m * v
-- Error: Momentum ≠ Energy (missing a velocity factor)

-- ❌ Wrong division
def bad4 (E : Energy) (m : Mass) : Velocity := E / m
-- Error: Energy/Mass = (Velocity)² ≠ Velocity
```

### **What the Type System Allows**
```lean
-- ✅ Correct kinetic energy
def KE (m : Mass) (v : Velocity) : Energy := (1/2) * m * v^2

-- ✅ Correct velocity from energy
def v_from_E (E : Energy) (m : Mass) : Velocity := 
  Real.sqrt (2 * E / m)

-- ✅ Correct potential energy
def PE (m : Mass) (g : Acceleration) (h : Length) : Energy :=
  m * g * h
```

---

## Performance Notes

### **Float vs ℚ vs ℝ**
```lean
-- Float: Fast, approximate
#eval (1.0 : Float) / 3.0  
-- Result: 0.333333... (15-17 digits)
-- Time: ~1 nanosecond

-- ℚ: Exact, slower
#eval (1 : ℚ) / 3  
-- Result: 1/3 (exact fraction)
-- Time: ~100 nanoseconds

-- ℝ: Not for computation!
-- Used only in proofs, not evaluated
```

**Recommendation**: Use Float for numerical work, ℚ for exact arithmetic, ℝ for theorems.

---

## Common Tasks

### **Task: Add a new physical constant**

1. Determine which domain file (e.g., `Physics/Quantum.lean`)
2. Look up the value from CODATA or authoritative source
3. Add definition with documentation
4. Add test verifying approximate value
5. Use in your physics code

### **Task: Define a new unit combination**
```lean
-- Want: Energy density (Energy per Volume)
type EnergyDensity := Energy / Volume

-- Now you can use it:
def vacuum_energy_density : EnergyDensity ℝ := 
  ⟨6e-10, by units⟩  -- J/m³ (dark energy)
```

### **Task: Convert between unit systems**
```lean
-- CGS to SI
def energy_cgs_to_si (E_erg : Float) : Energy Float :=
  ⟨E_erg * 1e-7, by units⟩  -- 1 erg = 10⁻⁷ J

-- Atomic units to SI
def energy_au_to_si (E_hartree : Float) : Energy Float :=
  ⟨E_hartree * 4.359744e-18, by units⟩  -- 1 hartree ≈ 4.36e-18 J
```

---

## Integration with Other Sections

### **Classes Use Units**
```lean
-- In Classes/QuantumMechanics/Lecture3.lean
import LogosLibrary.Units.Physics.Quantum

def hydrogen_ground_state_energy : Energy ℝ :=
  -13.6 * eV  -- Uses units from Physics/Quantum
```

### **Deep Theorems Use Units**
```lean
-- In DeepTheorems/Quantum/Uncertainty/Robertson.lean
import LogosLibrary.Units.Core.SI
import LogosLibrary.Units.Physics.Quantum

theorem position_momentum_uncertainty (Δx : Length ℝ) (Δp : Momentum ℝ) :
  Δx * Δp ≥ ℏ / 2 := by
  -- Proof uses typed units throughout
```

### **Detectors Use Units**
```lean
-- In Detectors/Battery/Thermodynamic.lean
import LogosLibrary.Units.Physics.Thermal

def thermal_runaway_check (Q : Energy) (m : Mass) (Cp : HeatCapacity) : Bool :=
  let ΔT := Q / (m * Cp)
  ΔT.val > 150  -- Check if temp rise exceeds 150 K
```

---

## Testing Your Units
```bash
# Test all units compile
lake build Units

# Run unit tests
lake test Units

# Verify specific domain
lake build Units.Physics.Quantum
```

---

## Guidelines

### **DO:**
- ✅ Always use typed units (never raw `Float` for physical quantities)
- ✅ Document sources for physical constants (CODATA year, paper, etc.)
- ✅ Add tests for new constants (verify approximate values)
- ✅ Put domain-specific units in appropriate domain files
- ✅ Use descriptive variable names (`planck_constant`, not `h_val`)

### **DON'T:**
- ❌ Add constants to Core unless truly fundamental
- ❌ Use magic numbers without units (e.g., `6.626e-34` without type)
- ❌ Forget the `by units` tactic when defining quantities
- ❌ Mix unit systems without explicit conversions
- ❌ Use deprecated or non-standard units without justification

---

## Troubleshooting

### **Error: "type mismatch in unit definition"**
```lean
-- ❌ Wrong
def bad_energy : Energy := 13.6

-- ✅ Correct
def good_energy : Energy := ⟨13.6, by units⟩
```

### **Error: "cannot add Energy to Mass"**

This is the type system working! You're trying to add incompatible dimensions. Check your physics.

### **Error: "units don't match in equation"**
```lean
-- Check dimensions on both sides
-- Left side: Energy (M*L²/T²)
-- Right side: Must also be Energy

-- Common mistake: Forgetting a factor
def E_wrong (m : Mass) (v : Velocity) := m * v  -- This is Momentum!
def E_right (m : Mass) (v : Velocity) := m * v^2  -- This is Energy ✓
```

---

## For New Contributors

**Start here:**
1. Read this README
2. Look at `Core/SI.lean` - see how base units are defined
3. Pick a domain file (e.g., `Physics/Quantum.lean`) - see how constants are added
4. Try adding a simple constant to an existing domain
5. Write a test for it
6. Submit PR

**Example first contribution**: Add a missing physical constant to an existing domain file.

---

## Further Reading

- `Core/SI.lean` - Base unit definitions
- `Core/Constants.lean` - Fundamental constants
- [CODATA](https://physics.nist.gov/cuu/Constants/) - Authoritative physical constant values
- [SI Brochure](https://www.bipm.org/en/publications/si-brochure/) - Official SI definitions

---

**The Units section is complete and stable. Everything else in Logos Library builds on this foundation.**

*Questions? Open an issue or check existing unit definitions for examples.*
