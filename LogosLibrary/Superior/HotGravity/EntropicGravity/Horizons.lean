/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
File: EntropicGravity/Horizons.lean
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import LogosLibrary.Relativity.Thermodynamics.Jacobson
/-!
=====================================================================
# HORIZON THERMODYNAMICS: THE DATA LAYER
=====================================================================

## Overview

This file establishes the foundational structures for entropic gravity:
the Bekenstein-Hawking area-entropy relation and the local Rindler
horizon as a Curry-Howard structure.

Every physical law is a TYPE (a structure field).  Inhabiting the
structure provides the proof.  Consistency is established by canonical
instances.  Consequences are theorems on the structure.

    Physical Law  ←→  Structure field (type)
    Consistency   ←→  Canonical instance (inhabitant)
    Consequence   ←→  Theorem on structure (function on proofs)

## What This File Provides

  §1  Planck scale definitions in natural units (ℏ = c = k_B = 1)
  §2  Bekenstein-Hawking entropy: S = A/(4G)
  §3  LocalRindlerHorizon: the main Curry-Howard structure
  §4  HorizonChange: entropy change from area change
  §5  SchwarzschildHorizon: the concrete canonical instance
  §6  Bridge to ElingGuedensJacobson (modular-intrinsic layer)

## Axiom Budget

  This file introduces ZERO axioms.
  All physical content is carried as structure fields.

## Dependencies

  - ElingGuedensJacobson (for boostTemp, unruhTemp — reproduced here,
    swap to imports when wiring the full project)
  - Mathlib (trigonometric basics, for π)

=====================================================================
-/

namespace EntropicGravity.Horizons

noncomputable section

open Real

/-!
=====================================================================
## Reproduced from ElingGuedensJacobson
=====================================================================

These definitions are reproduced verbatim from ElingGuedensJacobson.lean
so this file compiles standalone.  In the full project, replace with
the import and open the namespace.
-/

/-- Boost temperature: T_boost = 1/(2π) in natural units (ℏ = 1).
    The temperature of the Minkowski vacuum with respect to the
    boost Hamiltonian. (Bisognano-Wichmann 1975) -/
def boostTemp : ℝ := 1 / (2 * π)

lemma boostTemp_pos : 0 < boostTemp := by unfold boostTemp; positivity
lemma boostTemp_ne_zero : boostTemp ≠ 0 := boostTemp_pos.ne'

/-- Unruh temperature: T_U = a/(2π) in natural units.
    What a uniformly accelerating observer measures. (Unruh 1976) -/
def unruhTemp (a : ℝ) : ℝ := a / (2 * π)

lemma unruhTemp_pos {a : ℝ} (ha : 0 < a) : 0 < unruhTemp a := by
  unfold unruhTemp; positivity

lemma unruhTemp_ne_zero {a : ℝ} (ha : 0 < a) : unruhTemp a ≠ 0 :=
  (unruhTemp_pos ha).ne'

/-- Unruh temperature factors through the boost temperature. -/
theorem unruhTemp_eq_a_mul_boost (a : ℝ) :
    unruhTemp a = a * boostTemp := by
  unfold unruhTemp boostTemp; ring


-- ============================================================
-- § 1. Planck Scale in Natural Units
-- ============================================================

/-! In natural units (ℏ = c = k_B = 1), the Planck length squared
    equals Newton's constant: ℓ_P² = ℏG/c³ = G.

    The Planck area is the fundamental unit of horizon entropy:
    each Planck cell contributes ¼ nat of Bekenstein-Hawking entropy. -/

/-- Planck area equals G in natural units. -/
def planckArea (G : ℝ) : ℝ := G

/-- The number of Planck cells on a surface of area A. -/
def planckCellCount (A G : ℝ) : ℝ := A / G

theorem planckCellCount_pos {A G : ℝ} (hA : 0 < A) (hG : 0 < G) :
    0 < planckCellCount A G := by
  unfold planckCellCount; positivity


-- ============================================================
-- § 2. Bekenstein-Hawking Entropy
-- ============================================================

/-- Bekenstein-Hawking entropy: S = A/(4G).

    The factor of 4 is the deepest mystery in quantum gravity.
    Here it is simply a definition — the INPUT to the framework.
    Everything else follows from it.

    (Bekenstein 1973, Hawking 1975) -/
def bekensteinHawkingEntropy (A G : ℝ) : ℝ := A / (4 * G)

theorem bekensteinHawkingEntropy_pos {A G : ℝ} (hA : 0 < A) (hG : 0 < G) :
    0 < bekensteinHawkingEntropy A G := by
  unfold bekensteinHawkingEntropy; positivity

/-- Entropy per Planck cell: each cell carries ¼ nat. -/
theorem entropy_per_planck_cell (A G : ℝ) (hG : 0 < G) :
    bekensteinHawkingEntropy A G = planckCellCount A G / 4 := by
  unfold bekensteinHawkingEntropy planckCellCount
  have hG_ne : G ≠ 0 := hG.ne'
  field_simp

/-- Entropy is extensive: additive over disjoint horizon patches. -/
theorem entropy_additive (A₁ A₂ G : ℝ) :
    bekensteinHawkingEntropy (A₁ + A₂) G =
    bekensteinHawkingEntropy A₁ G + bekensteinHawkingEntropy A₂ G := by
  unfold bekensteinHawkingEntropy; ring

/-- Entropy scales linearly with area. -/
theorem entropy_linear (c A G : ℝ) :
    bekensteinHawkingEntropy (c * A) G = c * bekensteinHawkingEntropy A G := by
  unfold bekensteinHawkingEntropy; ring

/-- Area recovered from entropy: A = 4GS. -/
theorem area_from_entropy (S G : ℝ) (hG : 0 < G) :
    bekensteinHawkingEntropy (4 * G * S) G = S := by
  unfold bekensteinHawkingEntropy
  have hG_ne : G ≠ 0 := hG.ne'
  field_simp


-- ============================================================
-- § 3. LocalRindlerHorizon: The Curry-Howard Structure
-- ============================================================

/-- A local Rindler horizon patch.

    This is the fundamental thermodynamic object in entropic gravity.
    An accelerated observer near any point in spacetime perceives an
    approximate Rindler horizon carrying:

    - Proper acceleration `a` (from the observer's 4-acceleration)
    - Area `A` (of the local horizon patch)
    - Gravitational constant `G` (setting the Planck scale)

    All physical laws are FIELDS, not axioms.  Positivity constraints
    are proof data carried by the structure.  No `axiom` declarations.

    To construct a LocalRindlerHorizon IS to prove that a consistent
    thermodynamic horizon exists.  The type system enforces physics. -/
structure LocalRindlerHorizon where
  /-- Proper acceleration of the Rindler observer -/
  a : ℝ
  /-- Area of the local horizon patch -/
  A : ℝ
  /-- Newton's gravitational constant -/
  G : ℝ
  /-- Acceleration is strictly positive -/
  a_pos : 0 < a
  /-- Area is strictly positive -/
  A_pos : 0 < A
  /-- Newton's constant is strictly positive -/
  G_pos : 0 < G

namespace LocalRindlerHorizon

variable (h : LocalRindlerHorizon)

-- ────────────────────────────────────────────────────────────
-- § 3a. Derived Quantities
-- ────────────────────────────────────────────────────────────

/-- Unruh temperature: T = a/(2π).
    The temperature of the thermal bath seen by the accelerated observer. -/
def temperature : ℝ := unruhTemp h.a

/-- Bekenstein-Hawking entropy: S = A/(4G). -/
def entropy : ℝ := bekensteinHawkingEntropy h.A h.G

/-- Inverse temperature: β = 2π/a. -/
def inverseBeta : ℝ := 2 * π / h.a

/-- Number of Planck cells on the horizon. -/
def bitCount : ℝ := planckCellCount h.A h.G

-- ────────────────────────────────────────────────────────────
-- § 3b. Positivity and Non-Zero Lemmas
-- ────────────────────────────────────────────────────────────

lemma a_ne_zero : h.a ≠ 0 := h.a_pos.ne'
lemma A_ne_zero : h.A ≠ 0 := h.A_pos.ne'
lemma G_ne_zero : h.G ≠ 0 := h.G_pos.ne'

theorem temperature_pos : 0 < h.temperature := unruhTemp_pos h.a_pos
theorem temperature_ne_zero : h.temperature ≠ 0 := h.temperature_pos.ne'

theorem entropy_pos : 0 < h.entropy :=
  bekensteinHawkingEntropy_pos h.A_pos h.G_pos
theorem entropy_ne_zero : h.entropy ≠ 0 := h.entropy_pos.ne'

theorem inverseBeta_pos : 0 < h.inverseBeta := by
  unfold inverseBeta
  exact div_pos (mul_pos two_pos pi_pos) h.a_pos

theorem bitCount_pos : 0 < h.bitCount := planckCellCount_pos h.A_pos h.G_pos

-- ────────────────────────────────────────────────────────────
-- § 3c. Relationships Between Derived Quantities
-- ────────────────────────────────────────────────────────────

/-- β · T = 1: inverse temperature and temperature are reciprocals. -/
theorem beta_temp_reciprocal :
    h.inverseBeta * h.temperature = 1 := by
  unfold inverseBeta temperature unruhTemp
  have ha_ne : h.a ≠ 0 := h.a_ne_zero
  field_simp

/-- T · β = 1 (commuted form). -/
theorem temp_beta_reciprocal :
    h.temperature * h.inverseBeta = 1 := by
  rw [mul_comm]; exact h.beta_temp_reciprocal

/-- β = 1/T. -/
theorem inverseBeta_eq_inv_temp :
    h.inverseBeta = 1 / h.temperature := by
  rw [eq_div_iff h.temperature_ne_zero]
  exact h.beta_temp_reciprocal

/-- T = 1/β. -/
theorem temperature_eq_inv_beta :
    h.temperature = 1 / h.inverseBeta := by
  rw [eq_div_iff h.inverseBeta_pos.ne']
  exact h.temp_beta_reciprocal

/-- Temperature factors through boost temperature:
    T_U = a · T_boost. -/
theorem temperature_eq_a_mul_boost :
    h.temperature = h.a * boostTemp :=
  unruhTemp_eq_a_mul_boost h.a

/-- Entropy = bitCount / 4. -/
theorem entropy_eq_bitCount_div_4 :
    h.entropy = h.bitCount / 4 :=
  entropy_per_planck_cell h.A h.G h.G_pos

/-- Area recovered from entropy: A = 4GS. -/
theorem area_eq_4G_entropy :
    h.A = 4 * h.G * h.entropy := by
  unfold entropy bekensteinHawkingEntropy
  have hG_ne : h.G ≠ 0 := h.G_ne_zero
  field_simp

-- ────────────────────────────────────────────────────────────
-- § 3d. Monotonicity and Scaling
-- ────────────────────────────────────────────────────────────

/-- Hotter horizons correspond to larger acceleration. -/
theorem hotter_means_more_accelerated (h₂ : LocalRindlerHorizon)
    (hacc : h.a < h₂.a) :
    h.temperature < h₂.temperature := by
  unfold temperature unruhTemp
  exact div_lt_div_of_pos_right hacc (by positivity)

/-- Larger horizons (at the same G) have more entropy. -/
theorem larger_means_more_entropy (h₂ : LocalRindlerHorizon)
    (hG : h.G = h₂.G) (harea : h.A < h₂.A) :
    h.entropy < h₂.entropy := by
  unfold entropy bekensteinHawkingEntropy; rw [hG]
  exact div_lt_div_of_pos_right harea (mul_pos (by norm_num : (0:ℝ) < 4) h₂.G_pos)

-- ────────────────────────────────────────────────────────────
-- § 3e. The Boltzmann Ratio Invariance
-- ────────────────────────────────────────────────────────────

/-- For any energy E = a · E₀ (scaling with acceleration, as boost
    energies do), the ratio E/T is acceleration-independent:

      (a · E₀) / T_U = E₀ / T_boost = 2π E₀

    This is the thermodynamic root of why the modular Hamiltonian
    H/T is Lorentz invariant. The acceleration drops out. -/
theorem boltzmann_ratio_invariant (E₀ : ℝ) :
    (h.a * E₀) / h.temperature = E₀ / boostTemp := by
  unfold temperature
  rw [unruhTemp_eq_a_mul_boost]
  have ha_ne : h.a ≠ 0 := h.a_ne_zero
  have hb_ne : boostTemp ≠ 0 := boostTemp_ne_zero
  field_simp

/-- The Boltzmann ratio made explicit: E/T = 2πE₀. -/
theorem boltzmann_ratio_explicit (E₀ : ℝ) :
    (h.a * E₀) / h.temperature = 2 * π * E₀ := by
  rw [h.boltzmann_ratio_invariant E₀]
  unfold boostTemp; field_simp

end LocalRindlerHorizon


-- ============================================================
-- § 4. HorizonChange: Entropy Change from Area Change
-- ============================================================

/-- An infinitesimal change in a horizon.

    Carries both the original horizon data and the area change dA.
    This is the INPUT to the Clausius relation (File 2).

    The area change encodes geometric content (Raychaudhuri).
    The entropy change dS = dA/(4G) is derived.
    The heat flow δQ = T · dS follows from Clausius. -/
structure HorizonChange where
  /-- The horizon undergoing change -/
  horizon : LocalRindlerHorizon
  /-- Change in horizon area (positive = expansion) -/
  dA : ℝ

namespace HorizonChange

variable (δ : HorizonChange)

/-- Entropy change: dS = dA/(4G). -/
def dS : ℝ := δ.dA / (4 * δ.horizon.G)

/-- Heat flow implied by Clausius: δQ = T · dS. -/
def δQ : ℝ := δ.horizon.temperature * δ.dS

/-- If area increases, entropy increases. -/
theorem dS_pos_of_dA_pos (h : 0 < δ.dA) : 0 < δ.dS := by
  unfold dS;
  rw [propext (div_pos_iff_of_pos_left h)]
  norm_num
  unfold horizon
  exact δ.1.G_pos

/-- If area increases, heat flow is positive. -/
theorem δQ_pos_of_dA_pos (h : 0 < δ.dA) : 0 < δ.δQ := by
  unfold δQ
  exact mul_pos δ.horizon.temperature_pos (δ.dS_pos_of_dA_pos h)

/-- dS scales linearly with dA. -/
theorem dS_linear (c : ℝ) :
    (⟨δ.horizon, c * δ.dA⟩ : HorizonChange).dS = c * δ.dS := by
  unfold dS; ring

/-- The Clausius relation holds by construction:  δQ = T · dS. -/
theorem clausius_by_construction :
    δ.δQ = δ.horizon.temperature * δ.dS := rfl

/-- dS in Planck cells: each new cell adds ¼ nat. -/
theorem dS_in_planck_cells :
    δ.dS = (δ.dA / δ.horizon.G) / 4 := by
  unfold dS
  have hG_ne : δ.horizon.G ≠ 0 := δ.horizon.G_ne_zero
  field_simp

/-- Heat flow in terms of acceleration and area change:
    δQ = a · dA / (8πG). -/
theorem δQ_explicit :
    δ.δQ = δ.horizon.a * δ.dA / (8 * π * δ.horizon.G) := by
  unfold δQ dS LocalRindlerHorizon.temperature unruhTemp
  have hG_ne : δ.horizon.G ≠ 0 := δ.horizon.G_ne_zero
  field_simp; ring

end HorizonChange


-- ============================================================
-- § 5. Schwarzschild Horizon: The Canonical Instance
-- ============================================================

/-- A Schwarzschild black hole in natural units.

    Mass M and gravitational constant G determine everything:
    - Schwarzschild radius: r_s = 2GM
    - Horizon area: A = 16πG²M²
    - Hawking temperature: T_H = 1/(8πGM)
    - Entropy: S = 4πGM²

    This is a CONCRETE INSTANCE — proving the LocalRindlerHorizon
    structure is inhabited in the physically relevant case.
    (Schwarzschild 1916, Hawking 1975) -/
structure SchwarzschildHorizon where
  /-- Black hole mass -/
  M : ℝ
  /-- Newton's gravitational constant -/
  G : ℝ
  /-- Mass is strictly positive -/
  M_pos : 0 < M
  /-- Newton's constant is strictly positive -/
  G_pos : 0 < G

namespace SchwarzschildHorizon

variable (bh : SchwarzschildHorizon)

lemma M_ne_zero : bh.M ≠ 0 := bh.M_pos.ne'
lemma G_ne_zero : bh.G ≠ 0 := bh.G_pos.ne'

-- ────────────────────────────────────────────────────────────
-- § 5a. Derived Quantities
-- ────────────────────────────────────────────────────────────

/-- Schwarzschild radius: r_s = 2GM. -/
def radius : ℝ := 2 * bh.G * bh.M

/-- Horizon area: A = 16πG²M². -/
def area : ℝ := 16 * π * bh.G ^ 2 * bh.M ^ 2

/-- Hawking temperature: T_H = 1/(8πGM). -/
def hawkingTemp : ℝ := 1 / (8 * π * bh.G * bh.M)

/-- Surface gravity: κ = 1/(4GM). -/
def surfaceGravity : ℝ := 1 / (4 * bh.G * bh.M)

/-- Bekenstein-Hawking entropy: S = A/(4G). -/
def entropy : ℝ := bekensteinHawkingEntropy bh.area bh.G

-- ────────────────────────────────────────────────────────────
-- § 5b. Positivity
-- ────────────────────────────────────────────────────────────

theorem radius_pos : 0 < bh.radius := by
  unfold radius; exact mul_pos (mul_pos two_pos bh.G_pos) bh.M_pos

theorem area_pos : 0 < bh.area := by
  unfold area
  have : (0:ℝ) < 16 * π := by positivity
  exact mul_pos (mul_pos this (pow_pos bh.G_pos 2)) (pow_pos bh.M_pos 2)

theorem hawkingTemp_pos : 0 < bh.hawkingTemp := by
  unfold hawkingTemp
  exact div_pos one_pos (mul_pos (mul_pos (by positivity : (0:ℝ) < 8 * π) bh.G_pos) bh.M_pos)

theorem surfaceGravity_pos : 0 < bh.surfaceGravity := by
  unfold surfaceGravity
  exact div_pos one_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) bh.G_pos) bh.M_pos)

-- ────────────────────────────────────────────────────────────
-- § 5c. Key Relationships
-- ────────────────────────────────────────────────────────────

/-- Entropy evaluates to 4πGM². -/
theorem entropy_eq : bh.entropy = 4 * π * bh.G * bh.M ^ 2 := by
  unfold entropy bekensteinHawkingEntropy area
  have hG_ne : bh.G ≠ 0 := bh.G_ne_zero
  field_simp; ring

theorem entropy_pos : 0 < bh.entropy := by
  rw [bh.entropy_eq]
  exact mul_pos (mul_pos (by positivity : (0:ℝ) < 4 * π) bh.G_pos) (pow_pos bh.M_pos 2)

/-- **Hawking = Unruh at surface gravity**: T_H = κ/(2π).
    The Hawking temperature IS the Unruh temperature evaluated
    at the surface gravity.  A deep fact linking black hole
    thermodynamics to the equivalence principle. -/
theorem hawkingTemp_eq_unruh :
    bh.hawkingTemp = unruhTemp bh.surfaceGravity := by
  unfold hawkingTemp surfaceGravity unruhTemp
  have hG_ne : bh.G ≠ 0 := bh.G_ne_zero
  have hM_ne : bh.M ≠ 0 := bh.M_ne_zero
  field_simp; ring

/-- **First law of black hole mechanics**: T_H · dS/dM = 1.

    For Schwarzschild, S = 4πGM², so dS/dM = 8πGM.
    And T_H = 1/(8πGM).  Their product is unity. -/
theorem first_law :
    bh.hawkingTemp * (8 * π * bh.G * bh.M) = 1 := by
  unfold hawkingTemp
  have hG_ne : bh.G ≠ 0 := bh.G_ne_zero
  have hM_ne : bh.M ≠ 0 := bh.M_ne_zero
  field_simp

/-- **Negative heat capacity**: smaller black holes are hotter.

    T_H ∝ 1/M, so M₁ < M₂ implies T(M₂) < T(M₁).
    Black holes get hotter as they evaporate — the hallmark
    of a system with negative heat capacity. -/
theorem negative_heat_capacity (bh₂ : SchwarzschildHorizon)
    (hG : bh.G = bh₂.G) (hM : bh.M < bh₂.M) :
    bh₂.hawkingTemp < bh.hawkingTemp := by
  unfold hawkingTemp; rw [hG]
  have h8πG : (0:ℝ) < 8 * π * bh₂.G := mul_pos (by positivity : (0:ℝ) < 8 * π) bh₂.G_pos
  apply div_lt_div_of_pos_left one_pos
  · exact mul_pos h8πG bh.M_pos
  · exact mul_lt_mul_of_pos_left hM h8πG

-- ────────────────────────────────────────────────────────────
-- § 5d. Embedding as LocalRindlerHorizon
-- ────────────────────────────────────────────────────────────

/-- A Schwarzschild black hole IS a local Rindler horizon
    at its surface gravity.  This embedding connects the
    concrete example to the abstract framework.

    The type system enforces: every Schwarzschild BH inherits
    all theorems proven for LocalRindlerHorizon. -/
def toLocalRindler : LocalRindlerHorizon where
  a := bh.surfaceGravity
  A := bh.area
  G := bh.G
  a_pos := bh.surfaceGravity_pos
  A_pos := bh.area_pos
  G_pos := bh.G_pos

/-- The embedded temperature matches the Hawking temperature. -/
theorem toLocalRindler_temperature :
    bh.toLocalRindler.temperature = bh.hawkingTemp := by
  unfold LocalRindlerHorizon.temperature toLocalRindler
  exact bh.hawkingTemp_eq_unruh.symm

/-- The embedded entropy matches the BH entropy. -/
theorem toLocalRindler_entropy :
    bh.toLocalRindler.entropy = bh.entropy := rfl

end SchwarzschildHorizon


-- ============================================================
-- § 6. Bridge to ElingGuedensJacobson
-- ============================================================

/-! The EGJ module (ElingGuedensJacobson.lean) established:

    - boostTemp = 1/(2π): the modular-intrinsic temperature
    - unruhTemp a = a · boostTemp: the observer-dependent temperature
    - BWThermalTimeMap: rate(T) = 1/(2πT), uniquely forced
    - properTimeRate a = 1/a: modular parameter → proper time
    - jacobson_consistency: two routes to physical time agree

    The bridge: the temperature of a LocalRindlerHorizon IS the
    EGJ unruhTemp, and the energy/temperature ratio invariance
    (§3e above) IS the modular Hamiltonian invariance from EGJ.

    The thermal time at the Hawking temperature gives the rate of
    proper time at the horizon:

      rate(T_H) = 1/(2π T_H) = 1/(2π · κ/(2π)) = 2π/κ = 4GM·(2π)

    This is the modular flow parameter → Schwarzschild time conversion. -/

/-- The thermal time rate at the Hawking temperature
    equals the inverse surface gravity (times 2π).

    This connects the abstract rate(T) = 1/(2πT) from EGJ
    to the concrete Schwarzschild geometry. -/
theorem schwarzschild_thermal_rate (bh : SchwarzschildHorizon) :
    1 / (2 * π * bh.hawkingTemp) = 4 * bh.G * bh.M := by
  unfold SchwarzschildHorizon.hawkingTemp
  have hG_ne : bh.G ≠ 0 := bh.G_ne_zero
  have hM_ne : bh.M ≠ 0 := bh.M_ne_zero
  field_simp; ring

/-- Surface gravity from boost temperature and Hawking temperature:
    κ = T_H / T_boost = 8πGM · (1/(2π)) ... wait, let's just show
    that κ = 2 · (2π) · T_H, confirming the Unruh relation. -/
theorem surfaceGravity_eq_2pi_hawkingTemp (bh : SchwarzschildHorizon) :
    bh.surfaceGravity = 2 * π * bh.hawkingTemp := by
  unfold SchwarzschildHorizon.surfaceGravity SchwarzschildHorizon.hawkingTemp
  have hG_ne : bh.G ≠ 0 := bh.G_ne_zero
  have hM_ne : bh.M ≠ 0 := bh.M_ne_zero
  field_simp; ring

/-- The modular period of a Schwarzschild black hole:
    β = 1/T_H = 8πGM.

    This is the imaginary time period in the Euclidean section.
    The Euclidean Schwarzschild metric is smooth at r = 2GM
    if and only if the Euclidean time has period β = 8πGM.

    Thermodynamics KNOWS the geometry. -/
theorem schwarzschild_inverse_temp (bh : SchwarzschildHorizon) :
    1 / bh.hawkingTemp = 8 * π * bh.G * bh.M := by
  unfold SchwarzschildHorizon.hawkingTemp
  have hG_ne : bh.G ≠ 0 := bh.G_ne_zero
  have hM_ne : bh.M ≠ 0 := bh.M_ne_zero
  field_simp

/-- **The Bekenstein-Hawking product**: T_H · S = M/2.

    Temperature times entropy equals half the mass.
    This is the Smarr relation for Schwarzschild. -/
theorem bekenstein_hawking_product (bh : SchwarzschildHorizon) :
    bh.hawkingTemp * bh.entropy = bh.M / 2 := by
  rw [bh.entropy_eq]
  unfold SchwarzschildHorizon.hawkingTemp
  have hG_ne : bh.G ≠ 0 := bh.G_ne_zero
  have hM_ne : bh.M ≠ 0 := bh.M_ne_zero
  field_simp; ring


-- ============================================================
-- § 7. Summary
-- ============================================================

/-- **HORIZONS SUMMARY THEOREM**

    All core relationships in one conjunction.
    Given a Schwarzschild black hole with mass M and constant G:

    (H1)  T_H = κ/(2π)          (Hawking = Unruh)
    (H2)  S = 4πGM²             (Bekenstein-Hawking)
    (H3)  T_H · dS/dM = 1       (First law)
    (H4)  β = 8πGM              (Euclidean period)
    (H5)  T_H · S = M/2         (Smarr relation) -/
theorem horizons_summary (bh : SchwarzschildHorizon) :
    -- (H1) Hawking = Unruh at surface gravity
    (bh.hawkingTemp = unruhTemp bh.surfaceGravity)
    ∧
    -- (H2) Entropy = 4πGM²
    (bh.entropy = 4 * π * bh.G * bh.M ^ 2)
    ∧
    -- (H3) First law: T · dS/dM = 1
    (bh.hawkingTemp * (8 * π * bh.G * bh.M) = 1)
    ∧
    -- (H4) Inverse temperature = 8πGM
    (1 / bh.hawkingTemp = 8 * π * bh.G * bh.M)
    ∧
    -- (H5) Smarr relation: TS = M/2
    (bh.hawkingTemp * bh.entropy = bh.M / 2) :=
  ⟨bh.hawkingTemp_eq_unruh,
   bh.entropy_eq,
   bh.first_law,
   schwarzschild_inverse_temp bh,
   bekenstein_hawking_product bh⟩

end
end EntropicGravity.Horizons
