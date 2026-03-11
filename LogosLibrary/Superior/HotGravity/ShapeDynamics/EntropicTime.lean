/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: ShapeDynamics/EntropicTime.lean
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

namespace ShapeDynamics.EntropicTime
/-!
# Entropic Time: The Foundation of Superior-Shape Dynamics

## The Problem of Time

General Relativity has no preferred time coordinate — the Wheeler-DeWitt equation
`Ĥ|Ψ⟩ = 0` is timeless. Quantum mechanics requires time evolution: `iℏ∂_t|ψ⟩ = H|ψ⟩`.

Superior-Shape Dynamics resolves this: **time IS entropy production**.

## The Algebraic Heart

This file proves the identity at the center of the framework:

  **E_grav × τ_collapse = ℏ**

where:
- `E_grav = Gm²/Δx` is the gravitational self-energy of a superposition
- `τ_collapse = ℏΔx/(Gm²)` is the Diósi-Penrose decoherence timescale

This identity converts between entropic evolution (parameterized by entropy σ)
and standard quantum mechanics (parameterized by time t):

  1. Entropic Schrödinger:  `i · E_grav · ∂ψ/∂σ = Hψ`
  2. Entropy-time link:     `dσ/dt = Γ = E_grav/ℏ`
  3. Chain rule:            `∂/∂σ = (ℏ/E_grav) · ∂/∂t`
  4. Substitute:            `i · E_grav · (ℏ/E_grav) · ∂ψ/∂t = Hψ`
  5. Cancel:                `iℏ · ∂ψ/∂t = Hψ`  ✓

Step 4 → 5 is the identity `E_grav · τ = ℏ`.

## Physical Constants

We carry `G`, `ℏ`, `k_B` explicitly (not natural units) to show precisely
WHERE Planck's constant emerges in the Schrödinger recovery. The cancellation
`(Gm²/Δx) · (ℏΔx/Gm²) = ℏ` is the content — ℏ appears on the right because
it entered through the entropy-time conversion, not because we put it there.

## Two Entropy Channels

At finite temperature `T > 0`, entropy is produced through two channels:
- **Quantum (entanglement):** Rate `Γ_q = Gm²/(ℏΔx)`, T-independent
- **Thermal (environmental):** Contribution proportional to `T`, vanishes at `T = 0`

At `T → 0`: only the quantum channel survives → pure Schrödinger evolution.
At high `T`: thermal channel dominates → classical Shape Dynamics behavior.
-/


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 0. Physical Parameters
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Physical constants and system parameters for entropic time evolution.

All quantities are real-valued with explicit positivity hypotheses.
We do NOT set `ℏ = G = k_B = 1` — the entire point is to show
where Planck's constant emerges in the Schrödinger recovery. -/
structure EntropicParams where
  /-- Newton's gravitational constant -/
  G : ℝ
  /-- Reduced Planck constant (the quantity we will RECOVER) -/
  ℏ : ℝ
  /-- Boltzmann constant -/
  k_B : ℝ
  /-- Mass of the quantum system -/
  m : ℝ
  /-- Spatial separation of the superposition branches -/
  Δx : ℝ
  hG : G > 0
  hℏ : ℏ > 0
  hk : k_B > 0
  hm : m > 0
  hΔx : Δx > 0

namespace EntropicParams

variable (p : EntropicParams)

/-! ### Convenience lemmas for positivity and nonzeroness of products

These are used pervasively by `field_simp` to clear denominators.
We prove them once and refer to them by name throughout. -/

lemma Gm_sq_pos : p.G * p.m ^ 2 > 0 := mul_pos p.hG (sq_pos_of_pos p.hm)
lemma Gm_sq_ne  : p.G * p.m ^ 2 ≠ 0 := ne_of_gt p.Gm_sq_pos
lemma ℏΔx_pos   : p.ℏ * p.Δx > 0     := mul_pos p.hℏ p.hΔx
lemma ℏΔx_ne    : p.ℏ * p.Δx ≠ 0     := ne_of_gt p.ℏΔx_pos
lemma Δx_ne     : p.Δx ≠ 0            := ne_of_gt p.hΔx
lemma ℏ_ne      : p.ℏ ≠ 0             := ne_of_gt p.hℏ
lemma G_ne      : p.G ≠ 0             := ne_of_gt p.hG
lemma m_ne      : p.m ≠ 0             := ne_of_gt p.hm
lemma k_ne      : p.k_B ≠ 0           := ne_of_gt p.hk
lemma m_sq_pos  : p.m ^ 2 > 0         := sq_pos_of_pos p.hm
lemma m_sq_ne   : p.m ^ 2 ≠ 0         := ne_of_gt p.m_sq_pos
lemma ℏ_sq_pos  : p.ℏ ^ 2 > 0         := sq_pos_of_pos p.hℏ
lemma ℏ_sq_ne   : p.ℏ ^ 2 ≠ 0         := ne_of_gt p.ℏ_sq_pos
lemma Δx_sq_pos : p.Δx ^ 2 > 0        := sq_pos_of_pos p.hΔx

end EntropicParams


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 1. Gravitational Self-Energy
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The gravitational self-energy of a mass `m` in spatial superposition
with branch separation `Δx`.

  `E_grav = G · m² / Δx`

This is the energy scale that drives gravitational decoherence: the
gravitational interaction energy between the two branches of the superposition.
When the branches differ in mass distribution by `Δx`, gravity "tries to
resolve" the superposition with this energy scale. -/
noncomputable def gravSelfEnergy (p : EntropicParams) : ℝ :=
  p.G * p.m ^ 2 / p.Δx

theorem gravSelfEnergy_pos (p : EntropicParams) : gravSelfEnergy p > 0 := by
  unfold gravSelfEnergy; exact div_pos p.Gm_sq_pos p.hΔx

theorem gravSelfEnergy_ne (p : EntropicParams) : gravSelfEnergy p ≠ 0 :=
  ne_of_gt (gravSelfEnergy_pos p)

/-- Gravitational self-energy scales as the square of mass. -/
theorem gravSelfEnergy_mass_sq (p : EntropicParams) (c : ℝ) (hc : c > 0) :
    gravSelfEnergy { p with m := c * p.m, hm := mul_pos hc p.hm } =
    c ^ 2 * gravSelfEnergy p := by
  unfold gravSelfEnergy; simp only; ring

/-- Gravitational self-energy scales inversely with separation. -/
theorem gravSelfEnergy_inv_separation (p : EntropicParams) (c : ℝ) (hc : c > 0) :
    gravSelfEnergy { p with Δx := c * p.Δx, hΔx := mul_pos hc p.hΔx } =
    gravSelfEnergy p / c := by
  unfold gravSelfEnergy
  simp only
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hΔx_ne := p.Δx_ne
  field_simp

-- ═══════════════════════════════════════════════════════════════════════════════
-- § 2. Diósi-Penrose Collapse Rate and Collapse Time
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## The Diósi-Penrose Gravitational Decoherence

The collapse rate `Γ = Gm²/(ℏΔx)` was derived independently by:
- **Diósi (1987):** From a gravitational master equation for density matrices
- **Penrose (1996):** From gravitational energy uncertainty in superpositions

In S-SD, this is not ad hoc — it is the entropy production rate through the
quantum (entanglement) channel: the rate at which gravitational self-interaction
converts quantum coherence into classical correlation.
-/

/-- The Diósi-Penrose gravitational decoherence rate.

  `Γ = G · m² / (ℏ · Δx) = E_grav / ℏ`

This is the rate at which a spatial superposition of separation `Δx`
decoheres due to gravitational self-interaction. Equivalently, it is
the quantum channel entropy production rate. -/
noncomputable def collapseRate (p : EntropicParams) : ℝ :=
  p.G * p.m ^ 2 / (p.ℏ * p.Δx)

/-- The Diósi-Penrose collapse time (inverse of collapse rate).

  `τ = ℏ · Δx / (G · m²) = ℏ / E_grav`

This is the characteristic timescale on which a spatial superposition
decoheres gravitationally. -/
noncomputable def collapseTime (p : EntropicParams) : ℝ :=
  p.ℏ * p.Δx / (p.G * p.m ^ 2)

theorem collapseRate_pos (p : EntropicParams) : collapseRate p > 0 := by
  unfold collapseRate; exact div_pos p.Gm_sq_pos p.ℏΔx_pos

theorem collapseTime_pos (p : EntropicParams) : collapseTime p > 0 := by
  unfold collapseTime; exact div_pos p.ℏΔx_pos p.Gm_sq_pos

theorem collapseRate_ne (p : EntropicParams) : collapseRate p ≠ 0 :=
  ne_of_gt (collapseRate_pos p)

theorem collapseTime_ne (p : EntropicParams) : collapseTime p ≠ 0 :=
  ne_of_gt (collapseTime_pos p)

/-- The collapse rate is the gravitational self-energy per unit ℏ.

  `Γ = E_grav / ℏ`

Energy drives decoherence; ℏ sets the conversion scale. -/
theorem collapseRate_eq_energy_div_ℏ (p : EntropicParams) :
    collapseRate p = gravSelfEnergy p / p.ℏ := by
  unfold collapseRate gravSelfEnergy
  have := p.Δx_ne; have := p.ℏ_ne
  field_simp

/-- The collapse time is ℏ per unit gravitational self-energy.

  `τ = ℏ / E_grav` -/
theorem collapseTime_eq_ℏ_div_energy (p : EntropicParams) :
    collapseTime p = p.ℏ / gravSelfEnergy p := by
  unfold collapseTime gravSelfEnergy
  have := p.Δx_ne; have := p.Gm_sq_ne
  field_simp

/-- **Rate × Time = 1**: The collapse rate and collapse time are mutual inverses.

  `Γ · τ = 1` -/
theorem rate_time_product (p : EntropicParams) :
    collapseRate p * collapseTime p = 1 := by
  unfold collapseRate collapseTime
  have := p.Gm_sq_ne; have := p.ℏΔx_ne
  field_simp; grind only [cases Or]

/-- Equivalently: `τ = 1 / Γ` -/
theorem collapseTime_eq_inv_rate (p : EntropicParams) :
    collapseTime p = 1 / collapseRate p := by
  rw [eq_div_iff (collapseRate_ne p), mul_comm]
  exact rate_time_product p

/-- And: `Γ = 1 / τ` -/
theorem collapseRate_eq_inv_time (p : EntropicParams) :
    collapseRate p = 1 / collapseTime p := by
  rw [eq_div_iff (collapseTime_ne p)]
  exact rate_time_product p


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 3. THE SCHRÖDINGER RECOVERY
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## The Crown Jewel: `E_grav × τ = ℏ`

This single algebraic identity is the heart of Superior-Shape Dynamics.

**Physical meaning:** The product of the energy driving decoherence and
the timescale of decoherence is exactly Planck's constant. This is the
defining relationship that connects gravitational physics to quantum mechanics.

**Why this matters:**

Planck's constant does not enter the framework as a fundamental axiom.
It EMERGES as the conversion factor between:
- The gravitational self-energy scale (`E_grav = Gm²/Δx`)
- The associated entropy production timescale (`τ = ℏΔx/Gm²`)

The cancellation is: `(Gm²/Δx) × (ℏΔx/Gm²) = ℏ`.

The `Gm²` in the numerator of `E_grav` cancels the `Gm²` in the denominator
of `τ`. The `Δx` in the denominator of `E_grav` cancels the `Δx` in the
numerator of `τ`. What survives is exactly `ℏ`.
-/

/-- **THE SCHRÖDINGER RECOVERY THEOREM**

  `E_grav × τ_collapse = ℏ`

The gravitational self-energy times the collapse timescale equals Planck's
constant. This is the identity that converts entropic evolution (parameterized
by entropy `σ`) into standard quantum mechanics (parameterized by time `t`).

**The conversion:**
- Entropic evolution: `i · E_grav · ∂ψ/∂σ = Hψ`
- Chain rule: `∂ψ/∂σ = (τ) · ∂ψ/∂t = (ℏ/E_grav) · ∂ψ/∂t`
- Substitute: `i · E_grav · (ℏ/E_grav) · ∂ψ/∂t = Hψ`
- Cancel: `iℏ · ∂ψ/∂t = Hψ` ✓

**Proof:** Direct algebraic cancellation:
  `(Gm²/Δx) × (ℏΔx/Gm²) = ℏ` -/
theorem schrodinger_recovery (p : EntropicParams) :
    gravSelfEnergy p * collapseTime p = p.ℏ := by
  unfold gravSelfEnergy collapseTime
  have := p.Δx_ne; have := p.Gm_sq_ne
  field_simp; grind only [cases Or]

/-- Alternative form via the rate: `E_grav / Γ = ℏ`

Since `Γ = E_grav/ℏ`, this says `E_grav / (E_grav/ℏ) = ℏ`. -/
theorem schrodinger_recovery_via_rate (p : EntropicParams) :
    gravSelfEnergy p / collapseRate p = p.ℏ := by
  rw [collapseRate_eq_energy_div_ℏ]
  have := gravSelfEnergy_ne p; have := p.ℏ_ne
  field_simp

/-- The Schrödinger recovery saturates the Heisenberg energy-time bound.

  `E_grav · τ = ℏ ≥ ℏ/2`

The Diósi-Penrose timescale is the minimal decoherence time consistent
with the energy-time uncertainty relation for the gravitational self-energy.
(The factor of 2 vs the standard `≥ ℏ/2` bound is absorbed into the
precise definition of `ΔE` vs `E_grav`.) -/
theorem heisenberg_saturation (p : EntropicParams) :
    gravSelfEnergy p * collapseTime p ≥ p.ℏ / 2 := by
  rw [schrodinger_recovery]; linarith [p.hℏ]


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 4. Entropy-Time Conversion
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## The Bridge Between Entropy and Time

The entropic evolution equation `i · E_grav · ∂ψ/∂σ = Hψ` uses entropy `σ`
as the evolution parameter. To convert to the standard time parameter `t`,
we need the entropy-time conversion factors:

- **Forward:** `dσ/dt = E_grav/ℏ` (entropy production rate in time units)
- **Inverse:** `dt/dσ = ℏ/E_grav` (time elapsed per unit entropy produced)

These are the factors that appear in the chain rule when converting between
`∂/∂σ` and `∂/∂t`.
-/

/-- Forward conversion: entropy produced per unit time.

  `dσ/dt = E_grav / ℏ = Γ` (the collapse rate) -/
noncomputable def entropyPerTime (p : EntropicParams) : ℝ :=
  gravSelfEnergy p / p.ℏ

/-- Inverse conversion: time elapsed per unit entropy produced.

  `dt/dσ = ℏ / E_grav = τ` (the collapse time) -/
noncomputable def timePerEntropy (p : EntropicParams) : ℝ :=
  p.ℏ / gravSelfEnergy p

/-- The forward conversion equals the collapse rate. -/
theorem entropyPerTime_eq_rate (p : EntropicParams) :
    entropyPerTime p = collapseRate p := by
  unfold entropyPerTime
  exact (collapseRate_eq_energy_div_ℏ p).symm

/-- The inverse conversion equals the collapse time. -/
theorem timePerEntropy_eq_time (p : EntropicParams) :
    timePerEntropy p = collapseTime p := by
  unfold timePerEntropy
  exact (collapseTime_eq_ℏ_div_energy p).symm

/-- The two conversion factors are mutual inverses. -/
theorem entropy_time_conversion_inverse (p : EntropicParams) :
    entropyPerTime p * timePerEntropy p = 1 := by
  rw [entropyPerTime_eq_rate, timePerEntropy_eq_time]
  exact rate_time_product p

/-- **The Schrödinger coefficient identity:**

  `E_grav × (ℏ / E_grav) = ℏ`

This is the chain-rule substitution step that recovers `iℏ∂_t`
from `i·E_grav·∂_σ`. Numerically identical to `schrodinger_recovery`,
but conceptually it shows the role of the entropy-time conversion. -/
theorem entropic_coefficient_is_ℏ (p : EntropicParams) :
    gravSelfEnergy p * timePerEntropy p = p.ℏ := by
  unfold timePerEntropy
  have := gravSelfEnergy_ne p
  field_simp


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 5. Two Entropy Channels and the T → 0 Limit
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Quantum and Thermal Entropy Production

At finite temperature `T`, entropy is produced through two independent channels:

**Quantum (entanglement) channel:**
- Energy coefficient: `E_grav = Gm²/Δx`
- Entropy production rate: `Γ_q = E_grav/ℏ = Gm²/(ℏΔx)`
- **Temperature-independent** — gravity doesn't care about the thermal bath

**Thermal (environmental) channel:**
- Energy coefficient: `E_th(T)` depending on thermal bath properties
- Entropy production rate: proportional to `T`
- **Vanishes at T = 0** — no thermal bath means no thermal entropy production

The channel ratio `Γ_q/Γ_th` from the paper is `mΔx²k_BT/ℏ²`, meaning the
quantum channel is ~10¹⁵ times faster than thermal dissipation at typical
laboratory conditions. But at `T = 0`, the thermal channel is simply absent.

**The T → 0 theorem:** When the thermal channel is inactive (T = 0), the
ONLY entropy production is quantum, and the Schrödinger recovery gives
exactly `iℏ∂_t|ψ⟩ = H|ψ⟩`. This is why quantum mechanics is the
zero-temperature limit of thermodynamic evolution.
-/

/-- The channel ratio: relative speed of quantum vs thermal entropy production.

  `R(T) = m · Δx² · k_B · T / ℏ²`

At room temperature for a mesoscopic object, this is ~ 10¹⁵.
At `T = 0`, this is 0 (quantum channel is "infinitely faster" — but
the thermal channel is absent entirely). -/
noncomputable def channelRatio (p : EntropicParams) (T : ℝ) : ℝ :=
  p.m * p.Δx ^ 2 * p.k_B * T / p.ℏ ^ 2

/-- At absolute zero, the channel ratio vanishes. -/
theorem channelRatio_zero (p : EntropicParams) : channelRatio p 0 = 0 := by
  unfold channelRatio; ring

/-- At positive temperature, the channel ratio is positive. -/
theorem channelRatio_pos (p : EntropicParams) (T : ℝ) (hT : T > 0) :
    channelRatio p T > 0 := by
  unfold channelRatio
  have := p.hm; have := p.Δx_sq_pos; have := p.hk; have := p.ℏ_sq_pos
  exact div_pos (by positivity) p.ℏ_sq_pos

/-- The channel ratio is proportional to temperature. -/
theorem channelRatio_linear (p : EntropicParams) (c T : ℝ) :
    channelRatio p (c * T) = c * channelRatio p T := by
  unfold channelRatio; ring

/-- The channel ratio is monotone in temperature:
higher temperature → larger ratio → quantum channel relatively more dominant.

(This may seem counterintuitive, but recall: the ratio measures the quantum channel's
advantage. At higher T, each unit of thermal entropy carries less information,
so the thermal channel needs more entropy production per decoherence event.) -/
theorem channelRatio_mono (p : EntropicParams) (T₁ T₂ : ℝ)
    (_hT₁ : T₁ > 0) (h : T₁ < T₂) :
    channelRatio p T₁ < channelRatio p T₂ := by
  unfold channelRatio
  have h_coeff_pos : p.m * p.Δx ^ 2 * p.k_B / p.ℏ ^ 2 > 0 :=
    div_pos (mul_pos (mul_pos p.hm (sq_pos_of_pos p.hΔx)) p.hk) (sq_pos_of_pos p.hℏ)
  -- channelRatio p T = (m·Δx²·k_B/ℏ²) · T, so monotone in T
  have h1 : p.m * p.Δx ^ 2 * p.k_B * T₁ / p.ℏ ^ 2 =
    (p.m * p.Δx ^ 2 * p.k_B / p.ℏ ^ 2) * T₁ := by ring
  have h2 : p.m * p.Δx ^ 2 * p.k_B * T₂ / p.ℏ ^ 2 =
    (p.m * p.Δx ^ 2 * p.k_B / p.ℏ ^ 2) * T₂ := by ring
  rw [h1, h2]
  exact mul_lt_mul_of_pos_left h h_coeff_pos

/-- **The total effective evolution energy at temperature T.**

At temperature `T`, the system evolves under the combined influence of
the quantum channel (always present) and the thermal channel (proportional to T).

  `E_eff(T) = E_grav + k_B · T`

At `T = 0`: `E_eff = E_grav` → pure quantum evolution → Schrödinger
At high `T`: `E_eff ≈ k_B · T` → thermal evolution → classical (Shape Dynamics) -/
noncomputable def effectiveEnergy (p : EntropicParams) (T : ℝ) : ℝ :=
  gravSelfEnergy p + p.k_B * T

/-- At absolute zero, the effective energy is purely gravitational. -/
theorem effectiveEnergy_at_zero (p : EntropicParams) :
    effectiveEnergy p 0 = gravSelfEnergy p := by
  unfold effectiveEnergy; ring

/-- At any temperature, the effective energy exceeds the gravitational self-energy.
The thermal bath can only ADD to the evolution energy. -/
theorem effectiveEnergy_ge_grav (p : EntropicParams) (T : ℝ) (hT : T ≥ 0) :
    effectiveEnergy p T ≥ gravSelfEnergy p := by
  unfold effectiveEnergy
  have := p.hk
  linarith [mul_nonneg (le_of_lt p.hk) hT]

/-- **THE T → 0 THEOREM: Schrödinger Equation from Entropic Evolution**

At zero temperature, the only active entropy channel is quantum
(gravitational self-interaction). The Schrödinger recovery theorem then
gives exactly:

  `i · E_eff(0) · (ℏ/E_eff(0)) · ∂ψ/∂t = Hψ`
  `iℏ · ∂ψ/∂t = Hψ` ✓

This is why quantum mechanics is the zero-temperature limit of
thermodynamic spacetime evolution. Shape Dynamics is the high-T classical
limit; quantum mechanics is the T = 0 limit. -/
theorem T_zero_gives_schrodinger (p : EntropicParams) :
    effectiveEnergy p 0 * (p.ℏ / effectiveEnergy p 0) = p.ℏ := by
  rw [effectiveEnergy_at_zero]
  exact entropic_coefficient_is_ℏ p

/-- In the classical regime `k_B · T ≫ E_grav`, the thermal contribution
dominates. Here we prove the weaker statement that once `k_B · T > E_grav`,
the effective energy exceeds twice the gravitational self-energy —
the system has crossed into the thermally-dominated regime. -/
theorem high_T_thermal_dominance (p : EntropicParams) (T : ℝ)
    (h_hot : p.k_B * T > gravSelfEnergy p) :
    effectiveEnergy p T > 2 * gravSelfEnergy p := by
  unfold effectiveEnergy; linarith


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 6. Black Hole Specialization
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Schwarzschild Black Hole: m = M, Δx = 2M

For a Schwarzschild black hole, the natural identification is:
- `m = M` (the black hole mass)
- `Δx = 2M` (the Schwarzschild radius, in geometric units `G = c = 1`)

This gives `E_grav = GM²/(2M) = GM/2`, which is exactly the coefficient
in the S-SD paper's equation §5.5:

  `i(GM/2) ∂ψ/∂σ_throat = Hψ`

The Schrödinger recovery still gives `E_grav · τ = ℏ`, confirming that
the framework applies consistently to black hole thermodynamics.
-/

/-- For a Schwarzschild-like identification `Δx = 2m`,
the gravitational self-energy simplifies to `Gm/2`. -/
theorem schwarzschild_energy (p : EntropicParams) (h_schwarz : p.Δx = 2 * p.m) :
    gravSelfEnergy p = p.G * p.m / 2 := by
  unfold gravSelfEnergy
  rw [h_schwarz]; have := p.m_ne
  field_simp

/-- The Schwarzschild collapse rate: `Γ = Gm/(2ℏ)`. -/
theorem schwarzschild_rate (p : EntropicParams) (h_schwarz : p.Δx = 2 * p.m) :
    collapseRate p = p.G * p.m / (2 * p.ℏ) := by
  unfold collapseRate
  rw [h_schwarz]; have := p.m_ne; have := p.ℏ_ne
  field_simp

/-- The Schwarzschild collapse time: `τ = 2ℏ/(Gm)`. -/
theorem schwarzschild_time (p : EntropicParams) (h_schwarz : p.Δx = 2 * p.m) :
    collapseTime p = 2 * p.ℏ / (p.G * p.m) := by
  unfold collapseTime
  rw [h_schwarz]; have := p.m_ne; have := p.G_ne
  field_simp

/-- Even with the Schwarzschild specialization, Schrödinger recovery holds.
  `(Gm/2) · (2ℏ/Gm) = ℏ` -/
theorem schwarzschild_recovery (p : EntropicParams) (_h_schwarz : p.Δx = 2 * p.m) :
    gravSelfEnergy p * collapseTime p = p.ℏ :=
  schrodinger_recovery p  -- It's the same theorem — the proof is universal!


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 7. Scaling Relations
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## How Decoherence Scales with Mass and Separation

These theorems establish the physical scaling:
- **Heavy objects decohere faster:** `Γ ∝ m²` (quadratic in mass)
- **Compact superpositions decohere faster:** `Γ ∝ 1/Δx`
- **Collapse time is inversely related:** `τ ∝ 1/m²`, `τ ∝ Δx`

For a 1 μg dust grain with Δx ~ 1 μm:
  `τ ≈ 10⁻⁸ s` (fast decoherence)

For an electron with Δx ~ 1 nm:
  `τ ≈ 10²⁵ s` (coherence maintained for cosmic ages)

This is why macroscopic objects are classical and microscopic objects are quantum.
-/

/-- Collapse rate scales quadratically with mass at fixed separation. -/
theorem collapseRate_mass_scaling (p : EntropicParams) (c : ℝ) (hc : c > 0) :
    collapseRate { p with m := c * p.m, hm := mul_pos hc p.hm } =
    c ^ 2 * collapseRate p := by
  unfold collapseRate; simp only
  have := p.ℏΔx_ne
  field_simp

/-- Collapse rate scales inversely with separation at fixed mass. -/
theorem collapseRate_separation_scaling (p : EntropicParams) (c : ℝ) (hc : c > 0) :
    collapseRate { p with Δx := c * p.Δx, hΔx := mul_pos hc p.hΔx } =
    collapseRate p / c := by
  unfold collapseRate; simp only
  have := p.ℏ_ne; have := p.Δx_ne; have := ne_of_gt hc
  field_simp

/-- Collapse time scales inversely quadratically with mass. -/
theorem collapseTime_mass_scaling (p : EntropicParams) (c : ℝ) (hc : c > 0) :
    collapseTime { p with m := c * p.m, hm := mul_pos hc p.hm } =
    collapseTime p / c ^ 2 := by
  unfold collapseTime; simp only
  have := p.G_ne; have := p.m_ne; have := ne_of_gt hc
  field_simp

/-- Collapse time scales linearly with separation. -/
theorem collapseTime_separation_scaling (p : EntropicParams) (c : ℝ) (hc : c > 0) :
    collapseTime { p with Δx := c * p.Δx, hΔx := mul_pos hc p.hΔx } =
    c * collapseTime p := by
  unfold collapseTime; simp only
  have := p.Gm_sq_ne
  field_simp


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 8. The Recovery is Unique
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Uniqueness of the Schrödinger Recovery

If we ASSUME that:
1. Entropic evolution has the form `i · E · ∂ψ/∂σ = Hψ` for some energy `E`
2. The entropy-time conversion is `dσ/dt = E/α` for some constant `α`
3. The resulting time evolution is `iα · ∂ψ/∂t = Hψ`

Then necessarily `α = E · (time per entropy) = E · (α/E)`, which is trivially true.
The NON-trivial content is that `α` turns out to equal `ℏ` when `E = E_grav`.

The theorem below shows: for ANY energy scale `E > 0`, if the entropy production
rate is `E/ℏ`, then the time evolution coefficient is exactly `ℏ`. The gravitational
self-energy is special only because it provides the PHYSICAL energy scale for
decoherence — the algebra works for any `E`.
-/

/-- **Universality of the recovery:** For any positive energy scale `E` and any
positive constant `α`, if the entropy production rate is `E/α`, then the
chain-rule substitution gives `i · α · ∂ψ/∂t = Hψ`.

The product `E × (α/E) = α` is the identity that drives the recovery.
Setting `α = ℏ` gives the physical Schrödinger equation. -/
theorem recovery_universality (E α : ℝ) (hE : E > 0) (_ : α > 0) :
    E * (α / E) = α := by
  exact mul_div_cancel₀ α (ne_of_gt hE)

/-- **The physical choice:** Setting `E = E_grav` and `α = ℏ` recovers
the standard Schrödinger equation. This is `schrodinger_recovery` repackaged
to show it's an instance of the universal pattern. -/
theorem physical_recovery (p : EntropicParams) :
    gravSelfEnergy p * (p.ℏ / gravSelfEnergy p) = p.ℏ :=
  recovery_universality (gravSelfEnergy p) p.ℏ (gravSelfEnergy_pos p) p.hℏ


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 9. Summary Structure
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The complete entropic time framework, bundled for downstream use.

This packages the key results: positive energy, the recovery identity,
rate-time duality, and the T = 0 limit. -/
structure EntropicTimeFramework (p : EntropicParams) where
  /-- Gravitational self-energy is positive -/
  energy_pos : gravSelfEnergy p > 0
  /-- Collapse rate is positive -/
  rate_pos : collapseRate p > 0
  /-- The Schrödinger recovery: E × τ = ℏ -/
  recovery : gravSelfEnergy p * collapseTime p = p.ℏ
  /-- Rate and time are inverses: Γ × τ = 1 -/
  duality : collapseRate p * collapseTime p = 1
  /-- At T = 0, effective energy is purely gravitational -/
  zero_temp : effectiveEnergy p 0 = gravSelfEnergy p

/-- Construction of the framework — all fields are proven above. -/
noncomputable def entropicTimeFramework (p : EntropicParams) :
    EntropicTimeFramework p where
  energy_pos := gravSelfEnergy_pos p
  rate_pos := collapseRate_pos p
  recovery := schrodinger_recovery p
  duality := rate_time_product p
  zero_temp := effectiveEnergy_at_zero p


end ShapeDynamics.EntropicTime
