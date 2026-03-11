/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: CommonResources/Cosmology.lean
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

namespace Quintet
/-!
# The Quintet: Energy, Mass, Information, Temperature, Boltzmann

## The Fundamental Relation

  **E = I · k_B · T · ln 2**

This connects five quantities:
- `E` : Energy
- `m` : Mass (via `E = mc²`)
- `I` : Information content (in bits)
- `T` : Temperature (environmental, following Ott)
- `k_B`: Boltzmann constant

Solving for information: `I = E / (k_B · T · ln 2)`.

This is not a new equation — it is Landauer's principle read backwards.
Landauer says: erasing one bit costs at least `k_B · T · ln 2` energy.
The Quintet says: a system with energy `E` at temperature `T` carries
at most `I = E / (k_B · T · ln 2)` bits of information.

## Lorentz Invariance of Information

Under the Ott transformation:
- Energy transforms: `E → γE`
- Temperature transforms: `T → γT`
- Information: `I = γE / (k_B · γT · ln 2) = E / (k_B · T · ln 2) = I`

**Information content is Lorentz invariant** — which is physically necessary,
since information is counting (microstates, correlations, bits). Counting
doesn't depend on your reference frame.

Under the (incorrect) Landsberg transformation `T' = T`:
- `I' = γE / (k_B · T · ln 2) = γI`
- Information changes with velocity — absurd.

## Connection to Entropic Time

The gravitational information content `I_grav = E_grav / (k_B · T · ln 2)`
diverges as `T → 0`: at zero temperature, the gravitational self-energy
encodes infinite information. This is the quantum limit — the system is
maximally coherent, carrying unbounded information in its quantum state.

At high `T`, `I_grav → 0`: thermal noise washes out gravitational correlations.
This is the classical limit where Shape Dynamics applies.
-/


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 0. ln 2 Positivity
-- ═══════════════════════════════════════════════════════════════════════════════

/-! We establish `Real.log 2 > 0` once and use it everywhere.
This is the factor that converts between nats and bits. -/

theorem log_two_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
theorem log_two_ne : Real.log 2 ≠ 0 := ne_of_gt log_two_pos


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 1. Landauer Energy
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## The Thermodynamic Cost of One Bit

Landauer's principle (1961): erasing one bit of information in a thermal
environment at temperature `T` requires dissipating at least `k_B · T · ln 2`
energy into the environment.

This is not merely an engineering limitation. It is a consequence of the
second law: information erasure is a logically irreversible operation,
and irreversibility requires entropy production, which at temperature `T`
costs energy `T · ΔS`.

The factor `ln 2` converts between natural units (nats) and bits.
-/

/-- The Landauer energy: minimum energy to erase one bit at temperature `T`.

  `E_L(T) = k_B · T · ln 2`

This is the energy floor set by the second law for any irreversible
single-bit operation in a thermal bath at temperature `T`. -/
noncomputable def landauerEnergy (k_B T : ℝ) : ℝ :=
  k_B * T * Real.log 2

theorem landauerEnergy_pos (k_B T : ℝ) (hk : k_B > 0) (hT : T > 0) :
    landauerEnergy k_B T > 0 := by
  unfold landauerEnergy
  exact mul_pos (mul_pos hk hT) log_two_pos

theorem landauerEnergy_ne (k_B T : ℝ) (hk : k_B > 0) (hT : T > 0) :
    landauerEnergy k_B T ≠ 0 :=
  ne_of_gt (landauerEnergy_pos k_B T hk hT)

/-- At absolute zero, the Landauer energy vanishes — erasure is free.
(But there's nothing to erase: see `informationContent` divergence.) -/
theorem landauerEnergy_at_zero (k_B : ℝ) : landauerEnergy k_B 0 = 0 := by
  unfold landauerEnergy; ring

/-- The Landauer energy is linear in temperature. -/
theorem landauerEnergy_linear (k_B c T : ℝ) :
    landauerEnergy k_B (c * T) = c * landauerEnergy k_B T := by
  unfold landauerEnergy; ring


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 2. Information Content
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Bits in a Thermal System

Given a system with energy `E` at temperature `T`, the maximum number of bits
it can encode is `I = E / (k_B · T · ln 2)`.

This is Landauer's principle inverted: if each bit costs `k_B T ln 2` to erase
(i.e., to distinguish from thermal noise), then `E` worth of energy above the
thermal floor can encode at most `E / (k_B T ln 2)` distinguishable bits.
-/

/-- The information content: maximum bits encodable in energy `E` at temperature `T`.

  `I = E / (k_B · T · ln 2)` -/
noncomputable def informationContent (E k_B T : ℝ) : ℝ :=
  E / (k_B * T * Real.log 2)

theorem informationContent_pos (E k_B T : ℝ) (hE : E > 0) (hk : k_B > 0) (hT : T > 0) :
    informationContent E k_B T > 0 := by
  unfold informationContent
  exact div_pos hE (mul_pos (mul_pos hk hT) log_two_pos)

/-- The information content equals energy divided by Landauer energy. -/
theorem informationContent_eq_div_landauer (E k_B T : ℝ) :
    informationContent E k_B T = E / landauerEnergy k_B T := by
  unfold informationContent landauerEnergy ; rfl


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 3. The Quintet Relation
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## E = I · k_B · T · ln 2

The Quintet relation is tautological given our definition of `I`, but its
content is physical: energy, information, and temperature are three views
of the same thing. Any two determine the third.
-/

/-- **The Quintet:** `E = I(E, T) · k_B · T · ln 2`

Energy equals information content times the Landauer cost per bit. -/
theorem quintet (E k_B T : ℝ) (hk : k_B > 0) (hT : T > 0) :
    informationContent E k_B T * landauerEnergy k_B T = E := by
  unfold informationContent landauerEnergy
  have h_denom : k_B * T * Real.log 2 ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos hk hT) log_two_pos)
  field_simp

/-- Solving the Quintet for temperature:
`T = E / (I · k_B · ln 2)` -/
theorem quintet_solve_T (E I k_B T : ℝ) (hk : k_B > 0) (hT : T > 0) (hI : I > 0)
    (h : I = informationContent E k_B T) :
    T = E / (I * k_B * Real.log 2) := by
  rw [h]; unfold informationContent
  have h_kT : k_B * T > 0 := mul_pos hk hT
  have h_denom : k_B * T * Real.log 2 > 0 := mul_pos h_kT log_two_pos
  have h_denom_ne := ne_of_gt h_denom
  have h_I_pos : E / (k_B * T * Real.log 2) > 0 := div_pos (by nlinarith [mul_pos hI (landauerEnergy_pos k_B T hk hT), quintet E k_B T hk hT]) h_denom
  have h_I_ne := ne_of_gt h_I_pos
  field_simp
  subst h
  grind only [cases Or]


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 4. Lorentz Invariance of Information (Ott)
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Information Doesn't Depend on Your Reference Frame

Under a Lorentz boost with factor `γ > 0`:

**Ott transformation** (correct):
- Energy: `E → γE`
- Temperature: `T → γT`
- Information: `I = γE / (k_B · γT · ln 2) = E / (k_B · T · ln 2) = I` ✓

**Landsberg transformation** (incorrect):
- Energy: `E → γE`
- Temperature: `T → T` (invariant — Landsberg's claim)
- Information: `I = γE / (k_B · T · ln 2) = γI` ✗

Information scaling with velocity is absurd: the number of distinguishable
microstates cannot depend on who's watching. This is another independent
proof that Landsberg is wrong — complementing the five arguments in
`RelativisticTemperature.lean`.

We carry `γ > 0` as a parameter rather than importing the full Lorentz
machinery. Setting `γ = lorentzGamma v hv` recovers the physical case.
-/

/-- **Information is Lorentz invariant under Ott.**

If energy transforms as `E → γE` and temperature transforms as `T → γT`
(the Ott prescription), then information content is unchanged.

  `I(γE, γT) = I(E, T)` -/
theorem information_ott_invariant (E k_B T γ : ℝ) (hγ : γ > 0)
    (hk : k_B > 0) (hT : T > 0) :
    informationContent (γ * E) k_B (γ * T) = informationContent E k_B T := by
  unfold informationContent
  have hγ_ne := ne_of_gt hγ
  have hkT_ne := ne_of_gt (mul_pos hk hT)
  have hlog_ne := log_two_ne
  field_simp

/-- **Information is NOT Lorentz invariant under Landsberg.**

If energy transforms as `E → γE` but temperature stays `T' = T`,
then information scales by `γ`.

  `I(γE, T) = γ · I(E, T)` -/
theorem information_landsberg_scales (E k_B T γ : ℝ) :
    informationContent (γ * E) k_B T = γ * informationContent E k_B T := by
  unfold informationContent; field_simp

/-- **The Landsberg discrepancy:** Under Landsberg, boosted information
exceeds rest-frame information by a factor of `γ - 1` times `I`.

For `γ > 1` (any nonzero velocity), the boosted observer attributes MORE
information to the system — violating the principle that counting is
frame-independent. -/
theorem landsberg_information_discrepancy (E k_B T γ : ℝ) :
    informationContent (γ * E) k_B T - informationContent E k_B T =
    (γ - 1) * informationContent E k_B T := by
  rw [information_landsberg_scales]; ring

/-- If `γ > 1`, Landsberg strictly increases the information content. -/
theorem landsberg_information_increases (E k_B T γ : ℝ)
    (hE : E > 0) (hk : k_B > 0) (hT : T > 0) (hγ : γ > 1) :
    informationContent (γ * E) k_B T > informationContent E k_B T := by
  rw [information_landsberg_scales]
  have hI := informationContent_pos E k_B T hE hk hT
  nlinarith


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 5. Landauer Energy Transforms Correctly Under Ott
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## The Landauer Bound is Lorentz Covariant Under Ott

Under Ott (`T → γT`), the Landauer energy transforms as `E_L → γE_L`.
Since the system energy also transforms as `E → γE`, the inequality
`E ≥ I · E_L` is preserved: if the bound holds in one frame, it holds
in all frames.

Under Landsberg (`T → T`), the Landauer energy is unchanged but the system
energy increases, making the bound trivially easier to satisfy in the boosted
frame — but then transforming BACK yields a violation. (This is proven in
`RelativisticTemperature.lean` as `landsberg_violates_reverse`.)
-/

/-- The Landauer energy transforms homogeneously under Ott: `E_L(γT) = γ · E_L(T)`. -/
theorem landauerEnergy_ott (k_B T γ : ℝ) :
    landauerEnergy k_B (γ * T) = γ * landauerEnergy k_B T := by
  unfold landauerEnergy; ring

/-- Under Ott, if the Landauer bound holds at rest, it holds when boosted.

  `E ≥ I · E_L(T)` implies `γE ≥ I · E_L(γT)` -/
theorem landauer_bound_ott_preserved (E k_B T γ : ℝ) (hγ : γ > 0)
    (hk : k_B > 0) (hT : T > 0)
    (h_bound : E ≥ informationContent E k_B T * landauerEnergy k_B T) :
    γ * E ≥ informationContent (γ * E) k_B (γ * T) * landauerEnergy k_B (γ * T) := by
  -- Under Ott: I is invariant, E_L scales by γ, and γE = γ · E
  rw [information_ott_invariant E k_B T γ hγ hk hT]
  rw [landauerEnergy_ott]
  -- Need: γ * E ≥ I(E,T) * (γ * E_L(T))
  -- i.e.: γ * E ≥ γ * (I(E,T) * E_L(T))
  -- Which follows from: E ≥ I(E,T) * E_L(T) (the hypothesis)
  nlinarith


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 6. Gravitational Information
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## How Many Bits Does Gravity Carry?

The gravitational self-energy `E_grav = Gm²/Δx` encodes information
at the rate set by the Landauer floor:

  `I_grav = E_grav / (k_B · T · ln 2) = Gm² / (Δx · k_B · T · ln 2)`

This is the information content of the gravitational correlation between
the two branches of a spatial superposition.

**Key behavior:**
- `T → 0`: `I_grav → ∞` — the quantum limit, maximal coherence
- `T → ∞`: `I_grav → 0` — thermal noise drowns gravitational correlations
- Fixed `T`: `I_grav ∝ m²/Δx` — heavy, compact superpositions carry more
  gravitational information

This connects EntropicTime to the Quintet: the collapse rate `Γ = E_grav/ℏ`
is the rate at which gravitational information is converted from quantum
coherence to classical correlation.
-/

/-- Gravitational information: bits encoded in the gravitational self-energy.

  `I_grav = Gm² / (Δx · k_B · T · ln 2)` -/
noncomputable def gravInformation (G m Δx k_B T : ℝ) : ℝ :=
  informationContent (G * m ^ 2 / Δx) k_B T

/-- Gravitational information is positive for physical parameters. -/
theorem gravInformation_pos (G m Δx k_B T : ℝ)
    (hG : G > 0) (hm : m > 0) (hΔx : Δx > 0) (hk : k_B > 0) (hT : T > 0) :
    gravInformation G m Δx k_B T > 0 := by
  unfold gravInformation
  exact informationContent_pos _ k_B T (div_pos (mul_pos hG (sq_pos_of_pos hm)) hΔx) hk hT

/-- Gravitational information is Lorentz invariant under Ott. -/
theorem gravInformation_ott_invariant (G m Δx k_B T γ : ℝ) (hγ : γ > 0)
    (hk : k_B > 0) (hT : T > 0) :
    informationContent (γ * (G * m ^ 2 / Δx)) k_B (γ * T) =
    gravInformation G m Δx k_B T := by
  unfold gravInformation
  exact information_ott_invariant _ k_B T γ hγ hk hT

/-- Gravitational information scales quadratically with mass. -/
theorem gravInformation_mass_scaling (G m Δx k_B T c : ℝ) :
    gravInformation G (c * m) Δx k_B T =
    c ^ 2 * gravInformation G m Δx k_B T := by
  unfold gravInformation informationContent
  field_simp

/-- Gravitational information scales inversely with separation. -/
theorem gravInformation_separation_scaling (G m Δx k_B T c : ℝ)
    (hc : c > 0) (hΔx : Δx > 0) :
    gravInformation G m (c * Δx) k_B T =
    gravInformation G m Δx k_B T / c := by
  unfold gravInformation informationContent
  have hc_ne := ne_of_gt hc
  have hΔx_ne := ne_of_gt hΔx
  field_simp

/-- Gravitational information scales inversely with temperature.
Halving the temperature doubles the information content. -/
theorem gravInformation_temp_scaling (G m Δx k_B T c : ℝ)
    (hc : c > 0) (hT : T > 0) (hk : k_B > 0) :
    gravInformation G m Δx k_B (c * T) =
    gravInformation G m Δx k_B T / c := by
  unfold gravInformation informationContent
  have hc_ne := ne_of_gt hc
  have hT_ne := ne_of_gt hT
  have hk_ne := ne_of_gt hk
  field_simp


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 7. The Information-Entropy Connection
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Bits and Nats: Information vs Entropy

Thermodynamic entropy is measured in nats (natural units):
  `S = k_B · ln Ω`

Information is measured in bits:
  `I = log₂ Ω = ln Ω / ln 2`

The conversion: `I = S / (k_B · ln 2)`.

So the Quintet `E = I · k_B · T · ln 2` is just the first law `E = T · S`
with the bit-nat conversion made explicit.

This is why `ln 2` appears everywhere: it's the conversion factor between
the physicist's entropy (nats) and the information theorist's entropy (bits).
-/

/-- Information in bits equals entropy (in natural units) divided by `k_B · ln 2`. -/
theorem bits_from_entropy (S k_B : ℝ) (hk : k_B > 0) :
    S / (k_B * Real.log 2) = S / k_B / Real.log 2 := by
  have := ne_of_gt hk
  field_simp

/-- The Quintet is the first law with bit-nat conversion.

Given `E = T · S` (first law) and `I = S / (k_B · ln 2)` (bit-nat conversion),
we recover `E = I · k_B · T · ln 2`. -/
theorem quintet_from_first_law (E T S k_B : ℝ) (hk : k_B > 0) (hT : T > 0)
    (h_first_law : E = T * S)
    (I : ℝ) (h_info : I = S / (k_B * Real.log 2)) :
    E = I * (k_B * T * Real.log 2) := by
  rw [h_info, h_first_law]
  have hk_ne := ne_of_gt hk
  have hlog_ne := log_two_ne
  field_simp

/-- Conversely, the first law follows from the Quintet plus bit-nat conversion.

Given `E = I · k_B · T · ln 2` and `S = I · k_B · ln 2`, we get `E = T · S`. -/
theorem first_law_from_quintet (E I T S k_B : ℝ) (_hk : k_B > 0) (_hT : T > 0)
    (h_quintet : E = I * (k_B * T * Real.log 2))
    (h_entropy : S = I * (k_B * Real.log 2)) :
    E = T * S := by
  rw [h_quintet, h_entropy]; ring


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 8. The Sixth Kill Shot: Information Invariance
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## An Independent Argument for Ott over Landsberg

The five "kill shots" against Landsberg in `RelativisticTemperature.lean` use:
1. Landauer's bound
2. Entropy invariance
3. Free energy
4. Boltzmann exponent
5. Gibbs entropy

Here we add a sixth: **information invariance**.

The number of bits in a system is a count of distinguishable microstates.
Counting cannot depend on the observer's velocity. Therefore `I' = I`,
which forces `T' = γT` (Ott).

Under Landsberg: `I' = γI`, meaning a boosted observer sees MORE microstates.
This violates the principle that microstate counting is frame-independent.
-/

/-- **The sixth kill shot:** If we demand information invariance (`I' = I`)
and energy transforms as `E' = γE`, then temperature must transform as `T' = γT`.

Proof: `I = E/(kT ln 2) = γE/(k T' ln 2)` forces `T' = γT`. -/
theorem ott_from_information_invariance
    (E k_B T T' γ : ℝ) (hE : E ≠ 0) (hk : k_B > 0) (hT : T > 0) (hγ : γ > 0)
    (_h_energy : E' = γ * E)
    (h_info : informationContent (γ * E) k_B T' =
              informationContent E k_B T)
    (hT' : T' > 0) :
    T' = γ * T := by
  unfold informationContent at h_info
  have hk_ne := ne_of_gt hk
  have hT_ne := ne_of_gt hT
  have hT'_ne := ne_of_gt hT'
  have hlog_ne := log_two_ne
  have hγ_ne := ne_of_gt hγ
  field_simp at h_info
  -- h_info : γ * E * (k_B * T * log 2) = E * (k_B * T' * log 2)
  -- Factor out E * k_B * log 2 (all nonzero) to get γ * T = T'
  have h : γ * T = T' := by
    have h_prod_ne : E * k_B * Real.log 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hE hk_ne) hlog_ne
    nlinarith [mul_left_cancel₀ h_prod_ne (by grind only : E * k_B * Real.log 2 * (γ * T) = E * k_B * Real.log 2 * T')]
  linarith

/-- **Landsberg contradicts information invariance:** Under Landsberg (`T' = T`),
the information content of a boosted system differs from the rest frame by
a factor of exactly `γ`. -/
theorem landsberg_violates_information_invariance
    (E k_B T γ : ℝ) (hE : E > 0) (hk : k_B > 0) (hT : T > 0) (hγ : γ > 1) :
    informationContent (γ * E) k_B T ≠ informationContent E k_B T := by
  rw [information_landsberg_scales]
  intro h
  have hI := informationContent_pos E k_B T hE hk hT
  nlinarith


-- ═══════════════════════════════════════════════════════════════════════════════
-- § 9. Summary Bundle
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The complete Quintet framework, bundled for downstream use. -/
structure QuintetFramework (E k_B T : ℝ) where
  /-- Information is well-defined (positive Landauer energy) -/
  landauer_pos : landauerEnergy k_B T > 0
  /-- The Quintet relation: I · E_L = E -/
  quintet_rel : informationContent E k_B T * landauerEnergy k_B T = E
  /-- Information is Ott-invariant -/
  ott_invariant : ∀ γ : ℝ, γ > 0 →
    informationContent (γ * E) k_B (γ * T) = informationContent E k_B T

/-- Construction of the framework for physical parameters. -/
noncomputable def quintetFramework (E k_B T : ℝ) (hk : k_B > 0) (hT : T > 0) :
    QuintetFramework E k_B T where
  landauer_pos := landauerEnergy_pos k_B T hk hT
  quintet_rel := quintet E k_B T hk hT
  ott_invariant γ hγ := information_ott_invariant E k_B T γ hγ hk hT


end Quintet
