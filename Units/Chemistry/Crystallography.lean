-- Crystallography.lean -- Mineralogy, crystallography, and crystal physics units
import LogosLibrary.Units.Core.SI
import LogosLibrary.Units.Chemistry.Materials
import LogosLibrary.Units.Geology.Earth
import LogosLibrary.Units.Physics.Optics
import LogosLibrary.Units.Physics.Mechanics
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

namespace Units.Crystallography

open SI Materials Earth Optics Mechanics

/-
================================================================================
CRYSTALLOGRAPHY AND MINERALOGY UNITS LIBRARY
================================================================================

This module provides type-safe units for crystallography, mineralogy, X-ray
diffraction, and crystal physics. It builds upon the modular units system,
reusing standard units where appropriate and defining only domain-specific
crystallographic quantities. Following the triple-type architecture for
maximum flexibility without type conversion friction.

## COVERAGE
- Crystal geometry (lattice parameters, unit cells, crystal systems)
- Miller indices and crystallographic directions/planes
- Space groups, point groups, and Bravais lattices
- X-ray diffraction (d-spacing, Bragg angles, structure factors)
- Optical crystallography (2V angle, extinction angles, optical orientation)
- Crystal chemistry (site occupancy, coordination, bond valence)
- Physical properties tensors (elastic, thermal expansion, etc.)
- Mineral identification indices (Gladstone-Dale, compatibility)
- Crystallographic databases (ICSD numbers, Strukturbericht symbols)
- Reciprocal space (reciprocal lattice vectors, Brillouin zones)

## USAGE PATTERNS
Float: XRD peak positions, measured angles, refined parameters, EPMA analyses,
optical microscopy measurements, goniometer readings, structure refinements,
crystal orientation mapping, texture analysis, precession measurements

ℚ: Exact Miller indices, rational lattice ratios, systematic absences,
crystallographic site multiplicities, exact symmetry operations, Hermann-Mauguin
symbols, Wyckoff positions, exact fractional coordinates, Z values

ℝ: Continuous electron density, Fourier synthesis, structure factor calculations,
thermal displacement parameters, continuous reciprocal space, scattering theory,
tensor properties, group theory representations, modulated structures
-/

set_option autoImplicit false
set_option linter.unusedVariables false

/--
================================================================================================
   Reused Types from Other Modules
================================================================================================
-/

-- From Core.SI
abbrev Angstrom_F := Nanometer_F  -- Will need conversion factor of 10
abbrev Angstrom_Q := Nanometer_Q
abbrev Angstrom_R := Nanometer_R

abbrev Volume_F := Meter3_F
abbrev Volume_Q := Meter3_Q
abbrev Volume_R := Meter3_R

-- From Materials
abbrev Density_F := GPerCm3_F
abbrev Density_Q := GPerCm3_Q
abbrev Density_R := GPerCm3_R

abbrev Hardness_F := Materials.MohsHardness_F
abbrev Hardness_Q := Materials.MohsHardness_Q
abbrev Hardness_R := Materials.MohsHardness_R

-- From Earth
abbrev Porosity_F := Earth.Porosity_F
abbrev Porosity_Q := Earth.Porosity_Q
abbrev Porosity_R := Earth.Porosity_R

abbrev SpecificGravity_F := Ratio_F  -- Dimensionless
abbrev SpecificGravity_Q := Ratio_Q
abbrev SpecificGravity_R := Ratio_R

-- From Optics
abbrev RefractiveIndex_F := Optics.RefractiveIndex_F
abbrev RefractiveIndex_Q := Optics.RefractiveIndex_Q
abbrev RefractiveIndex_R := Optics.RefractiveIndex_R

abbrev Birefringence_F := Optics.Birefringence_F
abbrev Birefringence_Q := Optics.Birefringence_Q
abbrev Birefringence_R := Optics.Birefringence_R

-- From Mechanics
abbrev ElasticModulus_F := Pascal_F
abbrev ElasticModulus_Q := Pascal_Q
abbrev ElasticModulus_R := Pascal_R

/--
================================================================================================
   Crystal Systems and Symmetry
================================================================================================
-/

inductive CrystalSystem
  | Triclinic    -- a≠b≠c, α≠β≠γ≠90°
  | Monoclinic   -- a≠b≠c, α=γ=90°≠β
  | Orthorhombic -- a≠b≠c, α=β=γ=90°
  | Tetragonal   -- a=b≠c, α=β=γ=90°
  | Trigonal     -- a=b=c, α=β=γ≠90° (rhombohedral axes)
  | Hexagonal    -- a=b≠c, α=β=90°, γ=120°
  | Cubic        -- a=b=c, α=β=γ=90°
  deriving Repr, BEq, DecidableEq

inductive BravaisLattice
  | P  -- Primitive
  | I  -- Body-centered
  | F  -- Face-centered
  | C  -- C-centered (base-centered)
  | A  -- A-centered
  | B  -- B-centered
  | R  -- Rhombohedral
  deriving Repr, BEq, DecidableEq

-- 32 crystallographic point groups
inductive PointGroup
  -- Triclinic
  | C1 | Ci
  -- Monoclinic
  | C2 | Cs | C2h
  -- Orthorhombic
  | D2 | C2v | D2h
  -- Tetragonal
  | C4 | S4 | C4h | D4 | C4v | D2d | D4h
  -- Trigonal
  | C3 | C3i | D3 | C3v | D3d
  -- Hexagonal
  | C6 | C3h | C6h | D6 | C6v | D3h | D6h
  -- Cubic
  | T | Th | O | Td | Oh
  deriving Repr, BEq, DecidableEq

-- Space group with validation
structure SpaceGroupNumber where
  val : Nat
  inv : 1 ≤ val ∧ val ≤ 230
  deriving DecidableEq

-- Hermann-Mauguin symbol (simplified representation)
structure HermannMauguinSymbol where
  lattice : BravaisLattice
  pointGroup : String  -- Full symbol like "4/mmm"
  deriving Repr, BEq

/--
================================================================================================
   Miller Indices and Crystallographic Directions
================================================================================================
-/

structure MillerIndex where
  h : ℤ
  k : ℤ
  l : ℤ
  deriving Repr, BEq, DecidableEq

-- Miller-Bravais for hexagonal
structure MillerBravaisIndex where
  h : ℤ
  k : ℤ
  i : ℤ  -- Constraint: i = -(h+k)
  l : ℤ
  deriving Repr, BEq, DecidableEq

-- Direction vs plane distinction
structure CrystalDirection where
  indices : MillerIndex  -- [uvw]
  deriving Repr, BEq, DecidableEq

structure CrystalPlane where
  indices : MillerIndex  -- (hkl)
  deriving Repr, BEq, DecidableEq

-- Zone axis
structure ZoneAxis where
  direction : CrystalDirection
  deriving Repr, BEq, DecidableEq

/--
================================================================================================
   Lattice Parameters and Unit Cell
================================================================================================
-/

structure LatticeParameters_F where
  a : Angstrom_F
  b : Angstrom_F
  c : Angstrom_F
  alpha : Degree_F
  beta : Degree_F
  gamma : Degree_F
  deriving Repr, BEq

structure LatticeParameters_Q where
  a : Angstrom_Q
  b : Angstrom_Q
  c : Angstrom_Q
  alpha : Degree_Q
  beta : Degree_Q
  gamma : Degree_Q
  deriving Repr, BEq, DecidableEq

structure LatticeParameters_R where
  a : Angstrom_R
  b : Angstrom_R
  c : Angstrom_R
  alpha : Degree_R
  beta : Degree_R
  gamma : Degree_R

-- Unit cell volume
structure UnitCellVolume_F where val : Float deriving Repr, BEq  -- Ų
structure UnitCellVolume_Q where val : ℚ deriving Repr, BEq, DecidableEq
structure UnitCellVolume_R where val : ℝ

-- Z value (formula units per cell)
structure FormulaUnitsPerCell where val : Nat deriving Repr, BEq, DecidableEq

/--
================================================================================================
   X-ray Diffraction Units
================================================================================================
-/

-- D-spacing
structure DSpacing_F where val : Angstrom_F deriving Repr, BEq
structure DSpacing_Q where val : Angstrom_Q deriving Repr, BEq, DecidableEq
structure DSpacing_R where val : Angstrom_R

-- Bragg angles
structure ThetaDegree_F where val : Degree_F deriving Repr, BEq
structure ThetaDegree_Q where val : Degree_Q deriving Repr, BEq, DecidableEq
structure ThetaDegree_R where val : Degree_R

structure TwoThetaDegree_F where val : Degree_F deriving Repr, BEq
structure TwoThetaDegree_Q where val : Degree_Q deriving Repr, BEq, DecidableEq
structure TwoThetaDegree_R where val : Degree_R

-- Structure factor (complex)
structure StructureFactor_F where
  real : Float
  imag : Float
  deriving Repr, BEq

structure StructureFactor_Q where
  real : ℚ
  imag : ℚ
  deriving Repr, BEq, DecidableEq

structure StructureFactor_R where
  real : ℝ
  imag : ℝ

-- Temperature factor
structure BFactor_F where val : Float deriving Repr, BEq  -- Ų
structure BFactor_Q where val : ℚ deriving Repr, BEq, DecidableEq
structure BFactor_R where val : ℝ

-- Peak intensities
structure RelativeIntensity_F where val : Float deriving Repr, BEq  -- 0-100 or 0-1
structure RelativeIntensity_Q where val : ℚ deriving Repr, BEq, DecidableEq
structure RelativeIntensity_R where val : ℝ

structure FWHM_F where val : Degree_F deriving Repr, BEq
structure FWHM_Q where val : Degree_Q deriving Repr, BEq, DecidableEq
structure FWHM_R where val : Degree_R

/--
================================================================================================
   Reciprocal Space
================================================================================================
-/

structure ReciprocalAngstrom_F where val : Float deriving Repr, BEq  -- Ų⁻¹
structure ReciprocalAngstrom_Q where val : ℚ deriving Repr, BEq, DecidableEq
structure ReciprocalAngstrom_R where val : ℝ

structure ReciprocalVector_F where
  h : ReciprocalAngstrom_F
  k : ReciprocalAngstrom_F
  l : ReciprocalAngstrom_F
  deriving Repr, BEq

structure ReciprocalVector_Q where
  h : ReciprocalAngstrom_Q
  k : ReciprocalAngstrom_Q
  l : ReciprocalAngstrom_Q
  deriving Repr, BEq, DecidableEq

structure ReciprocalVector_R where
  h : ReciprocalAngstrom_R
  k : ReciprocalAngstrom_R
  l : ReciprocalAngstrom_R

-- Scattering vector
structure ScatteringVector_F where val : ReciprocalAngstrom_F deriving Repr, BEq
structure ScatteringVector_Q where val : ReciprocalAngstrom_Q deriving Repr, BEq, DecidableEq
structure ScatteringVector_R where val : ReciprocalAngstrom_R

/--
================================================================================================
   Optical Crystallography
================================================================================================
-/

-- 2V angle (optic axial angle)
structure TwoV_F where val : Degree_F deriving Repr, BEq
structure TwoV_Q where val : Degree_Q deriving Repr, BEq, DecidableEq
structure TwoV_R where val : Degree_R

-- Extinction angle
structure ExtinctionAngle_F where val : Degree_F deriving Repr, BEq
structure ExtinctionAngle_Q where val : Degree_Q deriving Repr, BEq, DecidableEq
structure ExtinctionAngle_R where val : Degree_R

-- Optical orientation
inductive OpticalSign
  | Positive  -- (+)
  | Negative  -- (-)
  deriving Repr, BEq, DecidableEq

inductive OpticalCharacter
  | Uniaxial
  | Biaxial
  deriving Repr, BEq, DecidableEq

/--
================================================================================================
   Crystal Chemistry
================================================================================================
-/

-- Site occupancy
structure SiteOccupancy_F where
  val : Float
  inv : 0 ≤ val ∧ val ≤ 1
  deriving Repr

structure SiteOccupancy_Q where
  val : ℚ
  inv : 0 ≤ val ∧ val ≤ 1
  deriving Repr, DecidableEq

structure SiteOccupancy_R where
  val : ℝ
  inv : 0 ≤ val ∧ val ≤ 1

-- Coordination number
structure CoordinationNumber where
  val : Nat
  inv : 2 ≤ val ∧ val ≤ 12
  deriving Repr, DecidableEq

-- Bond valence
structure BondValence_F where val : Float deriving Repr, BEq
structure BondValence_Q where val : ℚ deriving Repr, BEq, DecidableEq
structure BondValence_R where val : ℝ

-- Oxidation state
structure OxidationState where val : ℤ deriving Repr, BEq, DecidableEq

/--
================================================================================================
   Physical Properties
================================================================================================
-/

-- Cleavage
inductive CleavageQuality
  | Perfect
  | Good
  | Fair
  | Poor
  | None
  deriving Repr, BEq, DecidableEq

structure CleavagePlane where
  plane : CrystalPlane
  quality : CleavageQuality
  deriving Repr, BEq, DecidableEq

-- Fracture
inductive FractureType
  | Conchoidal
  | Irregular
  | Splintery
  | Hackly
  | Fibrous
  | Even
  deriving Repr, BEq, DecidableEq

-- Tenacity
inductive Tenacity
  | Brittle
  | Malleable
  | Sectile
  | Ductile
  | Flexible
  | Elastic
  deriving Repr, BEq, DecidableEq

-- Luster
inductive Luster
  | Metallic
  | Submetallic
  | Vitreous
  | Resinous
  | Adamantine
  | Pearly
  | Silky
  | Greasy
  | Dull
  deriving Repr, BEq, DecidableEq

-- Crystal habit
inductive CrystalHabit
  | Acicular
  | Bladed
  | Columnar
  | Cubic
  | Dendritic
  | Equant
  | Fibrous
  | Granular
  | Massive
  | Platy
  | Prismatic
  | Radiating
  | Tabular
  deriving Repr, BEq, DecidableEq

/--
================================================================================================
   Elastic Properties Tensor
================================================================================================
-/

-- 6x6 Voigt notation for elastic constants
structure ElasticTensor_F where
  c11 : ElasticModulus_F
  c12 : ElasticModulus_F
  c13 : ElasticModulus_F
  c14 : ElasticModulus_F
  c15 : ElasticModulus_F
  c16 : ElasticModulus_F
  c22 : ElasticModulus_F
  c23 : ElasticModulus_F
  c24 : ElasticModulus_F
  c25 : ElasticModulus_F
  c26 : ElasticModulus_F
  c33 : ElasticModulus_F
  c34 : ElasticModulus_F
  c35 : ElasticModulus_F
  c36 : ElasticModulus_F
  c44 : ElasticModulus_F
  c45 : ElasticModulus_F
  c46 : ElasticModulus_F
  c55 : ElasticModulus_F
  c56 : ElasticModulus_F
  c66 : ElasticModulus_F
  deriving Repr, BEq

/--
================================================================================================
   Validation Functions
================================================================================================
-/

-- Crystal system validation
def verifyCubicLattice_F (params : LatticeParameters_F) : Bool :=
  params.a.val == params.b.val && params.b.val == params.c.val &&
  params.alpha.val == 90 && params.beta.val == 90 && params.gamma.val == 90

def verifyHexagonalLattice_F (params : LatticeParameters_F) : Bool :=
  params.a.val == params.b.val && params.a.val != params.c.val &&
  params.alpha.val == 90 && params.beta.val == 90 && params.gamma.val == 120

def verifyTetragonalLattice_F (params : LatticeParameters_F) : Bool :=
  params.a.val == params.b.val && params.a.val != params.c.val &&
  params.alpha.val == 90 && params.beta.val == 90 && params.gamma.val == 90

def verifyOrthorhombicLattice_F (params : LatticeParameters_F) : Bool :=
  params.a.val != params.b.val && params.b.val != params.c.val && params.a.val != params.c.val &&
  params.alpha.val == 90 && params.beta.val == 90 && params.gamma.val == 90

def verifyMonoclinicLattice_F (params : LatticeParameters_F) : Bool :=
  params.a.val != params.b.val && params.b.val != params.c.val && params.a.val != params.c.val &&
  params.alpha.val == 90 && params.gamma.val == 90 && params.beta.val != 90

-- Miller index validation
def isValidMillerIndex (m : MillerIndex) : Bool :=
  m.h.natAbs ≤ 20 && m.k.natAbs ≤ 20 && m.l.natAbs ≤ 20  -- Reasonable range

def mkMillerBravaisIndex (h k l : ℤ) : MillerBravaisIndex :=
  ⟨h, k, -(h + k), l⟩

-- Mohs hardness validation
def isValidMohsHardness_F (h : Hardness_F) : Bool :=
  1.0 ≤ h.val && h.val ≤ 10.0

-- 2V angle validation
def isValidTwoV_F (twoV : TwoV_F) : Bool :=
  0.0 ≤ twoV.val.val && twoV.val.val ≤ 180.0

-- -- Site occupancy validation
-- def mkSiteOccupancy_F (v : Float) : Option SiteOccupancy_F :=
--   if 0 ≤ v && v ≤ 1 then some ⟨v, by sorry⟩ else none

-- def mkCoordinationNumber (n : Nat) : Option CoordinationNumber :=
--   if 2 ≤ n && n ≤ 12 then some ⟨n, by sorry⟩ else none

/--
================================================================================================
   Unit Conversions
================================================================================================
-/

-- Angstrom conversions (1 nm = 10 Å)
def angstromToNm_F (a : Angstrom_F) : Nanometer_F := ⟨a.val / 10.0⟩
def nmToAngstrom_F (nm : Nanometer_F) : Angstrom_F := ⟨nm.val * 10.0⟩

-- Unit cell volume from lattice parameters (general triclinic case)
def unitCellVolume_F (p : LatticeParameters_F) : UnitCellVolume_F :=
  let a := p.a.val / 10.0  -- Convert to nm
  let b := p.b.val / 10.0
  let c := p.c.val / 10.0
  let alpha := p.alpha.val * SI.pi_F / 180.0
  let beta := p.beta.val * SI.pi_F / 180.0
  let gamma := p.gamma.val * SI.pi_F / 180.0
  let cosAlpha := Float.cos alpha
  let cosBeta := Float.cos beta
  let cosGamma := Float.cos gamma
  let volume := a * b * c * Float.sqrt (
    1.0 + 2.0 * cosAlpha * cosBeta * cosGamma
    - cosAlpha * cosAlpha - cosBeta * cosBeta - cosGamma * cosGamma
  )
  ⟨volume * 1000.0⟩  -- Convert nm³ to ų

-- Bragg angle conversions
def thetaToTwoTheta_F (theta : ThetaDegree_F) : TwoThetaDegree_F :=
  ⟨⟨theta.val.val * 2.0⟩⟩

def twoThetaToTheta_F (twoTheta : TwoThetaDegree_F) : ThetaDegree_F :=
  ⟨⟨twoTheta.val.val / 2.0⟩⟩

-- Density calculation
def calculateDensity_F (molWeight : Float) (z : FormulaUnitsPerCell)
    (volume : UnitCellVolume_F) : Density_F :=
  let avogadro := 6.022e23
  ⟨molWeight * z.val.toFloat / (volume.val * avogadro * 1e-24)⟩

/--
================================================================================================
   Common Crystallographic Calculations
================================================================================================
-/

-- d-spacing for cubic system
def dSpacingCubic_F (a : Angstrom_F) (m : MillerIndex) : DSpacing_F :=
  let h2k2l2 := (m.h.toNat.toFloat)^2 + (m.k.toNat.toFloat)^2 + (m.l.toNat.toFloat)^2
  if h2k2l2 > 0.0 then
    ⟨⟨a.val / Float.sqrt h2k2l2⟩⟩
  else
    ⟨⟨0.0⟩⟩

-- d-spacing for hexagonal system
def dSpacingHexagonal_F (a c : Angstrom_F) (m : MillerBravaisIndex) : DSpacing_F :=
  let term1 := (4.0/3.0) * ((m.h.toNat.toFloat)^2 + (m.h.toNat.toFloat * m.k.toNat.toFloat) +
                            (m.k.toNat.toFloat)^2) / (a.val^2)
  let term2 := (m.l.toNat.toFloat)^2 / (c.val^2)
  if term1 + term2 > 0.0 then
    ⟨⟨1.0 / Float.sqrt (term1 + term2)⟩⟩
  else
    ⟨⟨0.0⟩⟩

-- Bragg's law: λ = 2d sinθ
def braggWavelength_F (d : DSpacing_F) (theta : ThetaDegree_F) : Float :=
  2.0 * d.val.val / 10.0 * Float.sin (theta.val.val * SI.pi_F / 180.0)  -- Result in nm

-- Scattering vector magnitude
def scatteringVectorMagnitude_F (theta : ThetaDegree_F) (lambda_nm : Float) : ScatteringVector_F :=
  ⟨⟨4.0 * SI.pi_F * Float.sin (theta.val.val * SI.pi_F / 180.0) / lambda_nm * 10.0⟩⟩

-- Structure factor amplitude
def structureFactorAmplitude_F (f : StructureFactor_F) : Float :=
  Float.sqrt (f.real * f.real + f.imag * f.imag)

-- Structure factor phase
def structureFactorPhase_F (f : StructureFactor_F) : Float :=
  Float.atan2 f.imag f.real

-- Gladstone-Dale compatibility index
def gladstoneDaleCompatibility_F (measured_n : RefractiveIndex_F)
    (calculated_n : RefractiveIndex_F) : Float :=
  (measured_n.val - calculated_n.val).abs / calculated_n.val

-- 2V from refractive indices (biaxial)
def calculate2V_F (n_alpha n_beta n_gamma : RefractiveIndex_F) : TwoV_F :=
  let v_squared := ((n_alpha.val - n_beta.val) / (n_beta.val - n_gamma.val)) *
                   ((n_gamma.val + n_alpha.val) / (n_gamma.val - n_alpha.val))
  ⟨⟨2.0 * Float.acos (Float.sqrt v_squared) * 180.0 / SI.pi_F⟩⟩

-- Zone axis from two planes
def zoneAxis_F (p1 p2 : CrystalPlane) : CrystalDirection :=
  let h1 := p1.indices.h
  let k1 := p1.indices.k
  let l1 := p1.indices.l
  let h2 := p2.indices.h
  let k2 := p2.indices.k
  let l2 := p2.indices.l
  ⟨⟨k1 * l2 - l1 * k2, l1 * h2 - h1 * l2, h1 * k2 - k1 * h2⟩⟩

-- Check if direction lies in plane
def directionInPlane (d : CrystalDirection) (p : CrystalPlane) : Bool :=
  d.indices.h * p.indices.h + d.indices.k * p.indices.k + d.indices.l * p.indices.l == 0

-- Lattice parameter refinement from peak positions (simplified cubic)
def refineLatticeParameter_F (twoTheta : List TwoThetaDegree_F)
    (indices : List MillerIndex) (lambda_nm : Float) : Option Angstrom_F :=
  if twoTheta.length != indices.length || twoTheta.length == 0 then
    none
  else
    let pairs := List.zip twoTheta indices
    let a_values := pairs.map fun (angle, miller) =>
      let theta_rad := angle.val.val / 2.0 * SI.pi_F / 180.0
      let h2k2l2 := (miller.h.toNat.toFloat)^2 + (miller.k.toNat.toFloat)^2 +
                    (miller.l.toNat.toFloat)^2
      if h2k2l2 > 0.0 && Float.sin theta_rad > 0.0 then
        lambda_nm * 10.0 * Float.sqrt h2k2l2 / (2.0 * Float.sin theta_rad)
      else
        0.0
    let valid_a := a_values.filter (· > 0.0)
    if valid_a.length > 0 then
      some ⟨valid_a.foldl (· + ·) 0.0 / valid_a.length.toFloat⟩
    else
      none

end Units.Crystallography
