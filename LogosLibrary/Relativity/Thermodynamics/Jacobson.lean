/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
/-! # Bisognano-Wichmann Thermal Time Uniqueness

Derives t = τ/(2πT) from BW normalization + universality.
No Ott. No Lorentz covariance. Entirely modular-intrinsic.

## Temperature hierarchy (following Eling-Guedens-Jacobson)

The BW theorem gives the vacuum density matrix ρ = Z⁻¹exp(-H_B/T_boost)
where H_B is the boost Hamiltonian and T_boost = ℏ/2π.

T_boost is *not* the Unruh temperature. The boost generates translations
of a dimensionless hyperbolic angle, not proper time. Re-scaling to
proper time on an orbit of acceleration `a` gives T_U = ℏa/2π = a·T_boost.

At unit acceleration these coincide, but they are conceptually distinct:
- T_boost: modular-intrinsic, universal, acceleration-independent
- T_U: observer-dependent, carries the acceleration as external data
-/
namespace ElingGuedensJacobson
noncomputable section

open Real

-- ============================================================
-- § 1. Boost temperature: the modular-intrinsic quantity
-- ============================================================

/-- The modular temperature: the temperature of the Minkowski vacuum
    with respect to the modular Hamiltonian of a Rindler wedge.
    This is T_boost = ℏ/(2πk_B) = 1/(2π) in natural units.
    It is LORENTZ INVARIANT because it parameterizes the modular
    automorphism group itself, not any observer's proper time. -/
def modularTemperature : ℝ := 1 / (2 * π)

lemma boostTemp_pos : 0 < modularTemperature := by unfold modularTemperature; positivity

lemma boostTemp_ne_zero : modularTemperature ≠ 0 := boostTemp_pos.ne'

-- ============================================================
-- § 2. Unruh temperature: the observer-dependent quantity
-- ============================================================

/-- Unruh temperature: T_U = ℏa/2π = a/(2π) in natural units.
This is what a uniformly accelerating observer actually measures.
It requires the acceleration `a` as external data beyond the
modular structure. (Unruh 1976, Jacobson 1995) -/
def unruhTemp (a : ℝ) : ℝ := a / (2 * π)

lemma unruhTemp_pos {a : ℝ} (ha : 0 < a) : 0 < unruhTemp a := by
  unfold unruhTemp; positivity

/-- The Unruh temperature factors through the boost temperature. -/
theorem unruhTemp_eq_a_mul_boost (a : ℝ) :
    unruhTemp a = a * modularTemperature := by
  unfold unruhTemp modularTemperature; ring

/-- At unit acceleration, Unruh and boost temperatures coincide. -/
theorem unruhTemp_unit_accel : unruhTemp 1 = modularTemperature := by
  simp [unruhTemp_eq_a_mul_boost]

-- ============================================================
-- § 3. BWThermalTimeMap: the core uniqueness structure
-- ============================================================

/-- A thermal time rate function constrained by BW + universality.

Physical time is `t = rate(T) · τ` where τ is the modular parameter
(dimensionless hyperbolic angle) and T is the boost temperature of
the state. The axioms uniquely force `rate(T) = 1/(2πT)`. -/
structure BWThermalTimeMap where
  /-- Physical time per unit modular parameter, as a function of temperature -/
  rate : ℝ → ℝ
  /-- Positive temperature ⟹ positive rate -/
  rate_pos : ∀ T, 0 < T → 0 < rate T
  /-- BW normalization: at the boost temperature, modular flow IS boost flow,
      so one unit of modular parameter = one unit of hyperbolic angle.
      rate(T_boost) = 1 encodes: "the modular automorphism group of the
      vacuum generates boosts." -/
  bw_normalize : rate modularTemperature = 1
  /-- Universality: rate(T)·T is the same constant for all T > 0.
      The functional form relating modular flow to physical time is
      state-independent. (Eventually derivable from Connes cocycle — Approach 5.) -/
  thermal_scale : ∀ T₁ T₂, 0 < T₁ → 0 < T₂ → rate T₁ * T₁ = rate T₂ * T₂

namespace BWThermalTimeMap

variable (m : BWThermalTimeMap)

-- ============================================================
-- § 3a. Core uniqueness chain
-- ============================================================

/-- The universal constant: rate(T)·T = 1/(2π) for all T > 0. -/
theorem rate_mul_temp (T : ℝ) (hT : 0 < T) :
    m.rate T * T = modularTemperature := by
  have := m.thermal_scale T modularTemperature hT boostTemp_pos
  rw [m.bw_normalize, one_mul] at this
  exact this

/-- **Main uniqueness**: rate(T) = 1/(2πT). Forced by the axioms. -/
theorem rate_unique (T : ℝ) (hT : 0 < T) :
    m.rate T = 1 / (2 * π * T) := by
  have h := m.rate_mul_temp T hT
  unfold modularTemperature at h
  have hT_ne : T ≠ 0 := hT.ne'
  field_simp at h ⊢
  linarith

/-- Physical time from temperature and modular parameter. -/
def thermalTime (T τ : ℝ) : ℝ := m.rate T * τ

/-- **The payoff**: t = τ/(2πT), no alternatives. -/
theorem thermalTime_eq (T τ : ℝ) (hT : 0 < T) :
    m.thermalTime T τ = τ / (2 * π * T) := by
  simp only [thermalTime, m.rate_unique T hT]
  ring

/-- Any two BWThermalTimeMaps agree on ℝ>0. The axioms leave zero room. -/
theorem ext_rate (m₁ m₂ : BWThermalTimeMap) (T : ℝ) (hT : 0 < T) :
    m₁.rate T = m₂.rate T := by
  rw [m₁.rate_unique T hT, m₂.rate_unique T hT]

-- ============================================================
-- § 3b. Derived properties
-- ============================================================

/-- rate is strictly anti-monotone: hotter systems → slower thermal clocks. -/
theorem rate_strictAntiOn (T₁ T₂ : ℝ) (h1 : 0 < T₁) (h2 : 0 < T₂) (hlt : T₁ < T₂) :
    m.rate T₂ < m.rate T₁ := by
  rw [m.rate_unique T₁ h1, m.rate_unique T₂ h2]
  apply div_lt_div_of_pos_left (by positivity)
  · positivity
  · exact mul_lt_mul_of_pos_left hlt (by positivity)

/-- KMS consistency: one full modular cycle (Δτ = 2π) gives exactly one
thermal period (Δt = β = 1/T). Connects Approach 3 back to Approach 1. -/
theorem kms_period_consistency (T : ℝ) (hT : 0 < T) :
    m.thermalTime T (2 * π) = 1 / T := by
  rw [m.thermalTime_eq T (2 * π) hT]
  have hT_ne : T ≠ 0 := hT.ne'
  field_simp

/-- Temperature scaling: if temperature scales by c, rate scales by 1/c. -/
theorem rate_temp_scale (T c : ℝ) (hT : 0 < T) (hc : 0 < c) :
    m.rate (c * T) = m.rate T / c := by
  have hcT : 0 < c * T := mul_pos hc hT
  rw [m.rate_unique (c * T) hcT, m.rate_unique T hT]
  have hc_ne : c ≠ 0 := hc.ne'
  have hT_ne : T ≠ 0 := hT.ne'
  field_simp

/-- Modular parameter recovery: τ = 2πT·t. -/
theorem modular_param_recovery (T t : ℝ) (hT : 0 < T) :
    m.thermalTime T (2 * π * T * t) = t := by
  rw [m.thermalTime_eq T _ hT]
  have hT_ne : T ≠ 0 := hT.ne'
  field_simp

/-- **Ott as consequence, not input**: if temperature transforms as T ↦ T/γ,
then physical time transforms as t ↦ γt. Derived from BW, not assumed. -/
theorem ott_as_consequence (T τ γ : ℝ) (hT : 0 < T) (hγ : 0 < γ) :
    m.thermalTime (T / γ) τ = γ * m.thermalTime T τ := by
  have hTγ : 0 < T / γ := div_pos hT hγ
  rw [m.thermalTime_eq (T / γ) τ hTγ, m.thermalTime_eq T τ hT]
  have hT_ne : T ≠ 0 := hT.ne'
  have hγ_ne : γ ≠ 0 := hγ.ne'
  field_simp

/-- The conjugate product: rate(T) · T · 2π = 1 for all T > 0. -/
theorem conjugate_product (T : ℝ) (hT : 0 < T) :
    m.rate T * T * (2 * π) = 1 := by
  rw [m.rate_unique T hT]
  have hT_ne : T ≠ 0 := hT.ne'
  field_simp

-- ============================================================
-- § 4. Acceleration layer: boost → Unruh → proper time
-- ============================================================

/-- Proper time rate for an observer with acceleration `a`.
The Unruh temperature is T_U = a/(2π), so the thermal time rate
at T_U determines how modular parameter maps to proper time
along that observer's worldline. -/
def properTimeRate (a : ℝ) : ℝ := m.rate (unruhTemp a)

/-- The proper time rate at acceleration `a` is 1/a. One unit of
modular parameter corresponds to 1/a units of proper time. -/
theorem properTimeRate_eq {a : ℝ} (ha : 0 < a) :
    m.properTimeRate a = 1 / a := by
  unfold properTimeRate
  rw [m.rate_unique (unruhTemp a) (unruhTemp_pos ha)]
  unfold unruhTemp
  have ha_ne : a ≠ 0 := ha.ne'
  field_simp

/-- Proper time elapsed for an observer with acceleration `a`
over modular parameter interval `τ`. -/
def properTime (a τ : ℝ) : ℝ := m.properTimeRate a * τ

/-- Proper time = τ/a. At unit acceleration, proper time = modular parameter. -/
theorem properTime_eq {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    m.properTime a τ = τ / a := by
  unfold properTime
  rw [m.properTimeRate_eq ha]
  ring

/-- At unit acceleration, modular parameter IS proper time.
This is the "canonical" case where the BW theorem applies directly. -/
theorem properTime_unit_accel (τ : ℝ) :
    m.properTime 1 τ = τ := by
  unfold properTime properTimeRate
  simp [unruhTemp_unit_accel, m.bw_normalize]

/-- Acceleration scaling: doubling acceleration halves proper time per
unit of modular parameter. The thermal clock ticks faster for
more accelerated observers. -/
theorem properTime_accel_scale {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (τ : ℝ) :
    m.properTime (c * a) τ = m.properTime a τ / c := by
  rw [m.properTime_eq (mul_pos hc ha), m.properTime_eq ha]
  have hc_ne : c ≠ 0 := hc.ne'
  have ha_ne : a ≠ 0 := ha.ne'
  field_simp

/-- The Jacobson δQ/T integrand structure: on a local Rindler horizon with
acceleration `a`, the heat flux uses χᵃ = -λkᵃ where λ is affine.
The ratio δQ/T involves T_boost = ℏ/2π (not T_Unruh), because the
boost Hamiltonian generates hyperbolic angle, not proper time.

This theorem confirms: thermal time computed at T_boost with
modular parameter τ/a equals proper time computed at acceleration a
with modular parameter τ. The two routes to physical time agree. -/
theorem jacobson_consistency {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    m.thermalTime modularTemperature (τ / a) = m.properTime a τ := by
  rw [m.thermalTime_eq modularTemperature _ boostTemp_pos]
  rw [m.properTime_eq ha]
  unfold modularTemperature
  have ha_ne : a ≠ 0 := ha.ne'
  field_simp

end BWThermalTimeMap

-- ============================================================
-- § 5. Canonical instance
-- ============================================================

/-- The canonical map. Proves the axioms are consistent (the structure is inhabited). -/
def BWThermalTimeMap.canonical : BWThermalTimeMap where
  rate T := 1 / (2 * π * T)
  rate_pos T hT := by positivity
  bw_normalize := by unfold modularTemperature; field_simp
  thermal_scale T₁ T₂ hT₁ hT₂ := by
    have : T₁ ≠ 0 := hT₁.ne'
    have : T₂ ≠ 0 := hT₂.ne'
    field_simp

-- ============================================================
-- § 6. KMS State: packaging thermal data
-- ============================================================

/-- A KMS thermal state on a von Neumann algebra.

Packages inverse temperature β and temperature T with the constraint
β · T = 1 (natural units with ℏ = k_B = 1). Both strictly positive.

The structure makes it impossible to construct a state with negative
temperature, inconsistent β and T, or zero/infinite temperature. -/
structure KMSState where
  /-- Inverse temperature β = 1/T -/
  β : ℝ
  /-- Temperature T = 1/β -/
  T : ℝ
  /-- Inverse temperature is strictly positive -/
  β_pos : 0 < β
  /-- Temperature is strictly positive -/
  T_pos : 0 < T
  /-- The fundamental KMS duality: β and T are reciprocals.
      Packaged as β · T = 1 to avoid division in the axiom. -/
  thermal_duality : β * T = 1

namespace KMSState

/-- Construct a KMS state from temperature alone. -/
def ofTemp (T : ℝ) (hT : 0 < T) : KMSState where
  β := 1 / T
  T := T
  β_pos := div_pos one_pos hT
  T_pos := hT
  thermal_duality := by field_simp

/-- Construct a KMS state from inverse temperature alone. -/
def ofInvTemp (β : ℝ) (hβ : 0 < β) : KMSState where
  β := β
  T := 1 / β
  β_pos := hβ
  T_pos := div_pos one_pos hβ
  thermal_duality := by field_simp

lemma β_eq_inv_T (k : KMSState) : k.β = 1 / k.T := by
  rw [eq_div_iff k.T_pos.ne']; exact k.thermal_duality

lemma T_eq_inv_β (k : KMSState) : k.T = 1 / k.β := by
  rw [eq_div_iff k.β_pos.ne']; exact (mul_comm k.T k.β).trans k.thermal_duality

lemma β_ne_zero (k : KMSState) : k.β ≠ 0 := k.β_pos.ne'
lemma T_ne_zero (k : KMSState) : k.T ≠ 0 := k.T_pos.ne'

end KMSState

-- ============================================================
-- § 7. Modular period and ThermalTimeMap (Approach 1)
-- ============================================================

/-- The modular period from Tomita-Takesaki theory. -/
def modularPeriod : ℝ := 2 * π

lemma modularPeriod_pos : 0 < modularPeriod := mul_pos two_pos pi_pos
lemma modularPeriod_ne_zero : modularPeriod ≠ 0 := modularPeriod_pos.ne'

/-- Boost temperature and modular period are reciprocals. -/
theorem boostTemp_eq_inv_modularPeriod : modularTemperature = 1 / modularPeriod := by
  unfold modularTemperature modularPeriod
  exact (div_eq_div_iff_comm (2 * π) 1 (2 * π)).mp rfl

/-- A thermal time map constrained by KMS periodicity.

The map has the form t = c(T) · τ where c(T) satisfies:
one modular cycle (2π) = one thermal period (β = 1/T). -/
structure ThermalTimeMap where
  /-- Proportionality constant: physical time is t = c(T) · τ -/
  c : ℝ → ℝ
  /-- Forward modular flow gives forward physical time -/
  c_pos : ∀ T, 0 < T → 0 < c T
  /-- KMS periodicity: c(T) · 2π = β -/
  kms_period : ∀ (k : KMSState), c k.T * modularPeriod = k.β

namespace ThermalTimeMap

variable (f : ThermalTimeMap)

/-- Physical time from temperature and modular parameter. -/
def time (T τ : ℝ) : ℝ := f.c T * τ

/-- KMS periodicity forces c(T) · (2πT) = 1. -/
theorem c_times_2piT_eq_one (k : KMSState) :
    f.c k.T * (modularPeriod * k.T) = 1 := by
  calc f.c k.T * (modularPeriod * k.T)
      = f.c k.T * modularPeriod * k.T := by ring
    _ = k.β * k.T := by rw [f.kms_period k]
    _ = 1 := k.thermal_duality

/-- **KMS uniqueness**: c(T) = 1/(2πT). Forced by periodicity matching. -/
theorem unique (k : KMSState) :
    f.c k.T = 1 / (modularPeriod * k.T) := by
  rw [eq_div_iff (mul_pos modularPeriod_pos k.T_pos).ne']
  exact f.c_times_2piT_eq_one k

/-- KMS uniqueness with 2π explicit. -/
theorem unique' (k : KMSState) :
    f.c k.T = 1 / (2 * π * k.T) := by
  have h := f.unique k; simp only [modularPeriod] at h; exact h

/-- The thermal time formula: t = τ/(2πT). -/
theorem time_formula (k : KMSState) (τ : ℝ) :
    f.time k.T τ = τ / (modularPeriod * k.T) := by
  unfold time; rw [f.unique k]; ring

/-- The β-form: t = βτ/(2π). -/
theorem time_formula_β (k : KMSState) (τ : ℝ) :
    f.time k.T τ = k.β * τ / modularPeriod := by
  rw [f.time_formula k τ, k.β_eq_inv_T]
  field_simp

/-- One full modular cycle gives one thermal period. -/
theorem full_cycle_is_thermal_period (k : KMSState) :
    f.time k.T modularPeriod = k.β := by
  unfold time; exact f.kms_period k

/-- Scaling invariant: c(T) · T = 1/(2π), independent of temperature. -/
theorem scaling_invariant (k : KMSState) :
    f.c k.T * k.T = 1 / modularPeriod := by
  rw [f.unique k]
  have := k.T_ne_zero
  have := modularPeriod_ne_zero
  field_simp

/-- Any two ThermalTimeMaps produce the same physical time. -/
theorem ext_time (g : ThermalTimeMap) (k : KMSState) (τ : ℝ) :
    f.time k.T τ = g.time k.T τ := by
  rw [f.time_formula k τ, g.time_formula k τ]

end ThermalTimeMap

/-- The canonical ThermalTimeMap: c(T) = 1/(2πT). -/
def ThermalTimeMap.canonical : ThermalTimeMap where
  c T := 1 / (modularPeriod * T)
  c_pos T hT := div_pos one_pos (mul_pos modularPeriod_pos hT)
  kms_period k := by
    have hT_ne := k.T_ne_zero
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff (mul_ne_zero modularPeriod_ne_zero hT_ne)]
    calc modularPeriod
        = 1 * modularPeriod := (one_mul _).symm
      _ = (k.β * k.T) * modularPeriod := by rw [k.thermal_duality]
      _ = k.β * (modularPeriod * k.T) := by ring

-- ============================================================
-- § 8. The Rindler / Bisognano-Wichmann anchor
-- ============================================================

/-- The Rindler KMS state: β = 2π, T = 1/(2π).
This is the Bisognano-Wichmann value for the Minkowski vacuum
restricted to a Rindler wedge. -/
def rindlerKMSState : KMSState :=
  KMSState.ofInvTemp modularPeriod modularPeriod_pos

lemma rindlerKMSState_T : rindlerKMSState.T = modularTemperature := by
  show 1 / modularPeriod = modularTemperature
  unfold modularTemperature modularPeriod
  rfl

lemma rindlerKMSState_β : rindlerKMSState.β = modularPeriod := rfl

/-- **BW anchor**: at the Rindler value β = 2π, physical time = modular time.
The modular flow of the vacuum on a Rindler wedge IS the boost flow. -/
theorem time_eq_modular_at_rindler (f : ThermalTimeMap) (τ : ℝ) :
    f.time rindlerKMSState.T τ = τ := by
  rw [f.time_formula rindlerKMSState]
  show τ / (modularPeriod * (1 / modularPeriod)) = τ
  have := modularPeriod_ne_zero
  field_simp

-- ============================================================
-- § 9. Bridge: Approach 1 and Approach 3 agree
-- ============================================================

/-- The Rindler KMS temperature equals the boost temperature.
This is the identification that makes the two approaches compatible:
Approach 1 (KMS periodicity) and Approach 3 (BW normalization) use
the same distinguished temperature T = 1/(2π). -/
theorem rindler_is_boost : rindlerKMSState.T = modularTemperature :=
  rindlerKMSState_T

/-- **Bridge theorem**: BWThermalTimeMap and ThermalTimeMap produce
the same rate at any KMS temperature.

Approach 1 (KMS periodicity alone) and Approach 3 (BW + universality)
are not just compatible — they are *provably identical* on their
common domain. Two roads, one destination. -/
theorem approaches_agree (m : BWThermalTimeMap) (f : ThermalTimeMap) (k : KMSState) :
    m.rate k.T = f.c k.T := by
  rw [m.rate_unique k.T k.T_pos, f.unique' k]

/-- **Bridge theorem (physical time form)**: both approaches give the
same physical time for any temperature and modular parameter. -/
theorem approaches_agree_time (m : BWThermalTimeMap) (f : ThermalTimeMap)
    (k : KMSState) (τ : ℝ) :
    m.thermalTime k.T τ = f.time k.T τ := by
  unfold BWThermalTimeMap.thermalTime ThermalTimeMap.time
  rw [approaches_agree m f k]

/-- **Monotonicity**: hotter KMS states → less physical time per modular cycle.
(Matches `BWThermalTimeMap.rate_strictAntiOn` from Approach 3.) -/
theorem kms_c_antitone (f : ThermalTimeMap) (k₁ k₂ : KMSState) (h : k₁.T < k₂.T) :
    f.c k₂.T < f.c k₁.T := by
  rw [f.unique' k₁, f.unique' k₂]
  have := k₁.T_pos
  have := k₂.T_pos
  apply div_lt_div_of_pos_left (by positivity)
  · positivity
  · exact mul_lt_mul_of_pos_left h (by positivity)

end

/-!
# Two-Thermometer Argument

## The Challenge

Two uniformly accelerated observers, both with proper acceleration `a`,
have relative velocity `v` between them.  Both measure the Unruh
temperature T = a/(2π).  The same temperature, despite nonzero γ.

If Ott (T → γT) applied, one should see the other's temperature as
γT ≠ T.  They do not.  What gives?

## The Resolution

The Ott transformation governs **observed temperature**: when Observer B,
moving at velocity v relative to a thermal system S, measures S's
temperature.  The thermal system is external to B.  B's motion relative
to S determines the boost.

The Unruh temperature is **intrinsic**: each observer's own Rindler
horizon produces a thermal bath visible only to that observer.  Observer A
does not "observe Observer B's Unruh bath."  A and B each have their own
wedge, their own horizon, their own modular flow.

The relative velocity between A and B is irrelevant because they are
measuring **different thermal systems** (their own respective horizons),
not the same system from different frames.

## The Formalization Strategy

We define:
  1. `ThermalMeasurement` — the general act of measuring temperature
  2. `IntrinsicMeasurement` — temperature from your own horizon (Unruh)
  3. `ObservedMeasurement` — temperature of an external system (Ott applies)

We prove:
  - Intrinsic measurements depend only on acceleration, not relative velocity
  - Observed measurements transform under Ott
  - The Two-Thermometer scenario involves two intrinsic measurements
  - Therefore Ott does not apply, and the equal temperatures are expected
  - This is consistent with Ott, not a refutation of it
-/

namespace JacobsonThermometers

noncomputable section

open Real

-- Import the key definitions from existing files.
-- Adjust these to match your actual namespace/import structure.
-- We use generic versions here for self-containedness.

variable (lorentzGamma : (v : ℝ) → |v| < 1 → ℝ)
variable (gamma_pos : ∀ v hv, lorentzGamma v hv > 0)
variable (gamma_ge_one : ∀ v hv, lorentzGamma v hv ≥ 1)
variable (gamma_gt_one : ∀ v hv, v ≠ 0 → lorentzGamma v hv > 1)
variable (gamma_ne_zero : ∀ v hv, lorentzGamma v hv ≠ 0)

/-!
## §1. The Unruh Temperature Is Intrinsic
-/

/-- The Unruh temperature depends on proper acceleration alone. -/
def unruhTemp (a : ℝ) : ℝ := a / (2 * π)

lemma unruhTemp_pos {a : ℝ} (ha : 0 < a) : 0 < unruhTemp a :=
  div_pos ha (mul_pos two_pos pi_pos)

/-- **JACOBSON'S SCENARIO.**

    Two observers, A and B, both uniformly accelerated with the
    same proper acceleration `a`, with relative velocity `v`
    between them.

    Key physical point: each observer measures the temperature
    of their OWN Rindler horizon, not the other's. -/
structure TwoThermometers where
  /-- Common proper acceleration -/
  a : ℝ
  /-- Acceleration is positive -/
  ha : 0 < a
  /-- Relative velocity between A and B -/
  v : ℝ
  /-- Subluminal -/
  hv : |v| < 1

namespace TwoThermometers

variable (s : TwoThermometers)

/-- Observer A measures their own Unruh temperature. -/
def tempA : ℝ := unruhTemp s.a

/-- Observer B measures their own Unruh temperature. -/
def tempB : ℝ := unruhTemp s.a

/-- **JACOBSON'S OBSERVATION.** Both observers measure the same temperature.
    This is immediate: both have the same acceleration, and the Unruh
    temperature depends only on acceleration. The relative velocity
    between A and B does not enter. -/
theorem both_measure_same : s.tempA = s.tempB := rfl

/-- The temperatures are equal regardless of relative velocity.
    Changing v does not change what either observer measures. -/
theorem velocity_irrelevant (s₁ s₂ : TwoThermometers)
    (h_same_a : s₁.a = s₂.a) :
    s₁.tempA = s₂.tempA := by
  unfold tempA unruhTemp; rw [h_same_a]

end TwoThermometers


/-!
## §2. The Scope of Ott

Ott applies when an observer measures the temperature of a thermal
system that is **external** to them — a system with its own rest frame
(or at least its own well-defined thermal state) that the observer
is boosted relative to.

We formalize this as a type-level distinction.
-/

/-- A thermal system with a well-defined temperature in some frame. -/
structure ThermalSystem where
  /-- Temperature in the system's rest frame (or natural frame) -/
  T_rest : ℝ
  hT : 0 < T_rest

/-- An observation of an external thermal system by a boosted observer.
    This is the scenario where Ott applies. -/
structure OttObservation where
  /-- The thermal system being observed -/
  system : ThermalSystem
  /-- The observer's velocity relative to the system -/
  v : ℝ
  hv : |v| < 1

/-- **OTT APPLIES TO EXTERNAL OBSERVATIONS.**
    The observed temperature is γT. -/
def OttObservation.observedTemp (obs : OttObservation)
    (γ : (v : ℝ) → |v| < 1 → ℝ) : ℝ :=
  γ obs.v obs.hv * obs.system.T_rest

/-- The observed temperature is strictly greater for v ≠ 0. -/
lemma OttObservation.hotter_when_moving (obs : OttObservation)
    (γ : (v : ℝ) → |v| < 1 → ℝ)
    (hγ_gt : ∀ v hv, v ≠ 0 → γ v hv > 1)
    (hv_ne : obs.v ≠ 0) :
    obs.observedTemp γ > obs.system.T_rest :=
  (lt_mul_iff_one_lt_left obs.system.hT).mpr (hγ_gt obs.v obs.hv hv_ne)


/-!
## §3. Why Jacobson's Scenario Is Not An Ott Observation

The crucial point: in Jacobson's scenario, neither observer is
performing an OttObservation of the other's thermal bath.

Each observer has their own Rindler wedge W_A, W_B. The thermal
state on W_A is the vacuum restricted to W_A. The thermal state
on W_B is the vacuum restricted to W_B. These are DIFFERENT
algebras with DIFFERENT states.

Observer A's thermometer responds to the modular flow of the
vacuum on W_A. Observer B's thermometer responds to the modular
flow of the vacuum on W_B. Neither is "looking at" the other's
thermal bath.

For Ott to apply, Observer A would need to somehow measure the
temperature of W_B's thermal state. But A's detector couples to
A's own Rindler horizon, not B's.
-/

/-- The source of a temperature measurement. -/
inductive ThermalSource
  /-- Temperature from your own horizon (Unruh, intrinsic) -/
  | intrinsic
  /-- Temperature of an external system you are boosted relative to -/
  | external

/-- A temperature measurement tagged with its source type. -/
structure TaggedMeasurement where
  temperature : ℝ
  source : ThermalSource

/-- Observer A's measurement in Jacobson's scenario: intrinsic. -/
def jacobsonA (s : TwoThermometers) : TaggedMeasurement :=
  { temperature := s.tempA, source := .intrinsic }

/-- Observer B's measurement in Jacobson's scenario: intrinsic. -/
def jacobsonB (s : TwoThermometers) : TaggedMeasurement :=
  { temperature := s.tempB, source := .intrinsic }

/-- **OTT APPLIES ONLY TO EXTERNAL OBSERVATIONS.**
    This is a definitional statement: we define the scope of Ott
    as applying to external measurements only. -/
def ottApplies (m : TaggedMeasurement) : Prop :=
  m.source = .external

/-- **JACOBSON'S SCENARIO: OTT DOES NOT APPLY.**
    Both measurements are intrinsic. -/
theorem jacobsonA_not_ott (s : TwoThermometers) :
    ¬ ottApplies (jacobsonA s) := by
  unfold ottApplies jacobsonA; simp only [reduceCtorEq, not_false_eq_true]

theorem jacobsonB_not_ott (s : TwoThermometers) :
    ¬ ottApplies (jacobsonB s) := by
  unfold ottApplies jacobsonB; simp only [reduceCtorEq, not_false_eq_true]


/-!
## §4. The Consistency Theorem

Jacobson's scenario is not a counterexample to Ott.
It is an example of a scenario outside Ott's scope.

Ott says: "If you observe an external thermal system while
boosted, you see γT."

Jacobson's scenario has: "Two observers, each seeing their own
intrinsic thermal bath."

These do not conflict. We prove the conjunction:
  (1) Jacobson's observers agree on temperature (both measure a/(2π))
  (2) Ott is consistent: IF either observer could somehow observe
      an external system at temperature T, they would see γT
  (3) The scenario does not involve any external observation
-/

/-- **THE CONSISTENCY THEOREM.**

    Jacobson's two-thermometer scenario is consistent with Ott.
    The equal temperatures are expected (not a violation) because
    both measurements are intrinsic to each observer's own horizon.
    Ott governs external observations, which do not occur here. -/
theorem jacobson_consistent (s : TwoThermometers)
    (γ : (v : ℝ) → |v| < 1 → ℝ)
    (hγ_gt : ∀ v hv, v ≠ 0 → γ v hv > 1)
    (_hγ_pos : ∀ v hv, γ v hv > 0) :
    -- (1) Both observers measure the same temperature
    s.tempA = s.tempB
    ∧
    -- (2) If an external system at temperature T existed,
    --     a boosted observer would see γT (Ott works)
    (∀ (sys : ThermalSystem) (v : ℝ) (hv : |v| < 1) (_hv_ne : v ≠ 0),
      γ v hv * sys.T_rest > sys.T_rest)
    ∧
    -- (3) Neither measurement in Jacobson's scenario is external
    (¬ ottApplies (jacobsonA s) ∧ ¬ ottApplies (jacobsonB s)) :=
  ⟨rfl,
   fun sys v hv hv_ne =>
     (lt_mul_iff_one_lt_left sys.hT).mpr (hγ_gt v hv hv_ne),
   jacobsonA_not_ott s, jacobsonB_not_ott s⟩


/-!
## §5. The Counterfactual: What If B Observed A's Bath?

To make the distinction fully concrete: suppose Observer B could
somehow couple a detector to Observer A's Rindler wedge (not their
own). Then B would be performing an external observation of a
thermal system at temperature T_A = a/(2π), while boosted by v
relative to A. In THIS case, Ott applies and B would measure γT_A.

This counterfactual scenario is physically different from Jacobson's
actual scenario. We formalize it to show the Ott machinery works
correctly when the scope conditions are met.
-/

/-- The counterfactual: B observes A's bath externally. -/
def counterfactualObservation (s : TwoThermometers) : OttObservation :=
  { system := { T_rest := unruhTemp s.a, hT := unruhTemp_pos s.ha },
    v := s.v,
    hv := s.hv }

/-- In the counterfactual, B sees γT_A ≠ T_A (for v ≠ 0).
    This is NOT what happens in Jacobson's actual scenario. -/
theorem counterfactual_gives_ott (s : TwoThermometers)
    (γ : (v : ℝ) → |v| < 1 → ℝ)
    (hγ_gt : ∀ v hv, v ≠ 0 → γ v hv > 1)
    (hv_ne : s.v ≠ 0) :
    (counterfactualObservation s).observedTemp γ > unruhTemp s.a :=
  (counterfactualObservation s).hotter_when_moving γ hγ_gt hv_ne

/-- **THE FULL PICTURE.** In one theorem:

    (a) Jacobson's actual scenario: both observers measure a/(2π).
        Equal temperatures. Ott does not apply. No contradiction.

    (b) The counterfactual (B observes A's bath): B would measure
        γ · a/(2π) > a/(2π). Ott applies and gives a different
        temperature. As expected.

    The difference between (a) and (b) is not "whether Ott is true."
    It is "what is being measured." -/
theorem full_resolution (s : TwoThermometers)
    (γ : (v : ℝ) → |v| < 1 → ℝ)
    (hγ_gt : ∀ v hv, v ≠ 0 → γ v hv > 1)
    (_hγ_pos : ∀ v hv, γ v hv > 0)
    (hv_ne : s.v ≠ 0) :
    -- (a) Actual scenario: equal temperatures, Ott not in scope
    (s.tempA = s.tempB ∧ ¬ ottApplies (jacobsonA s))
    ∧
    -- (b) Counterfactual: Ott applies, gives γT > T
    ((counterfactualObservation s).observedTemp γ > unruhTemp s.a) :=
  ⟨⟨rfl, jacobsonA_not_ott s⟩,
   counterfactual_gives_ott s γ hγ_gt hv_ne⟩


/-!
## Epilogue

The two phenomena coexist:
  • Intrinsic: T_U = a/(2π), independent of relative velocity
  • External: T_obs = γT_rest, dependent on relative velocity

Jacobson's scenario is the first. Ott governs the second.
No contradiction.

### Connection to T_boost vs T_U

This resolution is consistent with the Eling-Guedens-Jacobson
temperature hierarchy:

  T_boost = ℏ/(2π) — modular-intrinsic, Lorentz invariant
  T_U = a · T_boost — observer-dependent, but intrinsic to each observer

T_boost does not transform because it parameterizes the modular
structure itself. T_U does not transform under boosts between
observers of equal acceleration because each observer has their
own T_U determined by their own `a`. Neither is an external
observation of the other's thermal state.
-/

end
end JacobsonThermometers

end ElingGuedensJacobson
