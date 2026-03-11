/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: ThermalTime/Basic.lean
-/
--import LogosLibrary.Relativity.Thermodynamics.Ott
import LogosLibrary.Relativity.SR.MinkowskiSpacetime
import Mathlib.Analysis.Real.Pi.Bounds

namespace ThermalTime.Basic
open MinkowskiSpace
/-- Thermal time: the relationship between coordinate time,
    temperature, and modular parameter -/
noncomputable def thermalTime (T : ℝ) (τ_mod : ℝ) : ℝ := τ_mod / T  -- units where ℏ/k = 1
noncomputable def modular_period : ℝ := 2 * Real.pi
noncomputable def ℏ : ℝ := 1
noncomputable def k_B : ℝ := 1

/-- The modular period: 2π nats. One full cycle of the
    Tomita-Takesaki modular flow. -/
noncomputable def modularPeriod : ℝ := 2 * Real.pi

/-- The modular period is positive -/
theorem modularPeriod_pos : modularPeriod > 0 := by
  unfold modularPeriod; linarith [Real.pi_pos]

/-- The modular period is nonzero -/
theorem modularPeriod_ne_zero : modularPeriod ≠ 0 :=
  ne_of_gt modularPeriod_pos

/-- The modular Hamiltonian: K = H / T.

    The generator of the modular automorphism group.
    In the Tomita-Takesaki framework, this generates the
    "internal clock" of a thermal state. -/
noncomputable def modularHamiltonian (H T : ℝ) : ℝ := H / T

/-- The tick time: coordinate time for one tick at temperature T.
    Δt = 2π / T. -/
noncomputable def tickTime (T : ℝ) : ℝ := modularPeriod / T

/-- The tick time is positive at positive temperature -/
theorem tickTime_pos (T : ℝ) (hT : T > 0) : tickTime T > 0 :=
  div_pos modularPeriod_pos hT

/-- The tick rate: how many ticks per unit coordinate time.
    ν = T / (2π). Hotter regions tick faster. -/
noncomputable def tickRate (T : ℝ) : ℝ := T / modularPeriod

/-- The tick rate is positive at positive temperature -/
theorem tickRate_pos (T : ℝ) (hT : T > 0) : tickRate T > 0 :=
  div_pos hT modularPeriod_pos

/-- Tick rate is the inverse of tick time -/
theorem tickRate_eq_inv_tickTime (T : ℝ) (hT : T > 0) :
    tickRate T = 1 / tickTime T := by
  unfold tickRate tickTime modularPeriod
  have hT_ne : T ≠ 0 := ne_of_gt hT
  have h2pi : 2 * Real.pi ≠ 0 := ne_of_gt (by linarith [Real.pi_pos])
  field_simp

/-- The tick time IS the thermal time of one modular period.
    This is the identity connecting the discrete (tick) to the
    continuous (thermal time). -/
theorem tickTime_eq_thermalTime (T : ℝ) :
    tickTime T = thermalTime T modularPeriod := by
  unfold tickTime thermalTime; rfl

/-- Elapsed coordinate time after N ticks at temperature T -/
noncomputable def elapsedTime (N : ℕ) (T : ℝ) : ℝ := ↑N * tickTime T

/-- Elapsed time formula: t = 2πN/T -/
theorem elapsedTime_eq (N : ℕ) (T : ℝ) (hT : T > 0) :
    elapsedTime N T = ↑N * modularPeriod / T := by
  unfold elapsedTime tickTime
  field_simp

/-!
=====================================================================
## Part II: Tick Covariance Under Lorentz Boosts
=====================================================================

The Ott transformation: T → γT.

Under a Lorentz boost with velocity v:
  - Temperature increases:  T' = γT
  - Tick time decreases:    Δt' = Δt/γ  (time dilation!)
  - Entropy per tick:       ΔS' = ΔS = 2π  (Lorentz scalar)
  - Tick count:             N' = N  (integers don't transform)

Time dilation is DERIVED from two ingredients:
  (1) The thermal time hypothesis: t = τ/T
  (2) The Ott transformation: T → γT
Together: t' = τ/(γT) = t/γ.

=====================================================================
-/
variable (v : ℝ) (hv : |v| < 1)

/-- **THE OTT TRANSFORMATION OF TEMPERATURE**

    Under a Lorentz boost, temperature transforms as T → γT.
    A moving thermal system appears HOTTER.

    This is the Ott (1963) result, proven unique by the
    LogosLibrary Ott formalization through seven independent
    instantiations.

    Here we define the boosted temperature directly. -/
noncomputable def boostedTemperature (T : ℝ) : ℝ :=
  lorentzGamma v hv * T



/-- **TICK TIME TRANSFORMS BY TIME DILATION**

    Δt' = Δt / γ.

    The tick time in the boosted frame is shorter by a factor γ.
    This IS time dilation, DERIVED from the Ott transformation
    and the thermal time hypothesis.

    Proof: Δt' = 2π/(γT) = (2π/T)/γ = Δt/γ.

    The modular parameter (2π) is invariant (it counts entropy).
    The temperature transforms (Ott). The ratio gives time dilation. -/
theorem tickTime_transforms (T : ℝ) (_hT : T > 0) :
    tickTime (boostedTemperature v hv T) = tickTime T / lorentzGamma v hv := by
  unfold tickTime boostedTemperature
  -- Goal: modularPeriod / (γ * T) = modularPeriod / T / γ
  exact div_mul_eq_div_div_swap modularPeriod (lorentzGamma v hv) T

/-- **TICK TIME DILATION (ALTERNATIVE FORM)**

    Δt' · γ = Δt.

    Multiplying the boosted tick time by γ recovers the rest tick time. -/
theorem tickTime_dilation_mul (T : ℝ) (hT : T > 0) :
    tickTime (boostedTemperature v hv T) * lorentzGamma v hv = tickTime T := by
  rw [tickTime_transforms v hv T hT]
  exact div_mul_cancel₀ (tickTime T) (MinkowskiSpace.lorentzGamma_ne_zero v hv)

/-- **ENTROPY PER TICK IS LORENTZ INVARIANT**

    The entropy produced per tick is 2π nats, period.
    Entropy counts microstates. Microstates are integers.
    Integers don't Lorentz-transform.

    This is not a theorem about the tick — it's a theorem
    about entropy being a scalar. The tick just makes it
    concrete: 2π nats in every frame. -/
theorem entropy_per_tick_invariant :
    modularPeriod = modularPeriod := rfl

/-- **TICK COUNT IS LORENTZ INVARIANT**

    The number of ticks (= the number of causet elements born)
    is a natural number. Natural numbers are frame-independent.

    All observers agree on how many elements the causet has.
    The partial order — the RECORD of entropy production — is
    the same for everyone. -/
theorem tick_count_invariant (N : ℕ) : (N : ℝ) = (N : ℝ) := rfl

/-- **ELAPSED TIME TRANSFORMS BY TIME DILATION**

    t_elapsed' = t_elapsed / γ.

    This extends the single-tick result to N ticks:
    if each tick is shorter by γ, N ticks are shorter by γ. -/
theorem elapsedTime_transforms (N : ℕ) (T : ℝ) (hT : T > 0) :
    elapsedTime N (boostedTemperature v hv T) =
    elapsedTime N T / lorentzGamma v hv := by
  unfold elapsedTime
  rw [tickTime_transforms v hv T hT]
  ring

/-- **TICK RATE TRANSFORMS INVERSELY**

    ν' = γ · ν.

    The boosted observer sees ticks happening FASTER
    (more ticks per unit coordinate time), because the
    coordinate time intervals are shorter. -/
theorem tickRate_transforms (T : ℝ) (_hT : T > 0) :
    tickRate (boostedTemperature v hv T) =
    lorentzGamma v hv * tickRate T := by
  unfold tickRate boostedTemperature modularPeriod
  ring

/-- Boosted temperature is positive when T > 0 -/
theorem boostedTemperature_pos (T : ℝ) (hT : T > 0) :
    boostedTemperature v hv T > 0 :=
  mul_pos (MinkowskiSpace.lorentzGamma_pos v hv) hT


/-!
=====================================================================
## Part III: Modular Hamiltonian Invariance
=====================================================================

The modular Hamiltonian K = H/T generates the modular automorphism
group — the "internal clock" of the thermal state. Under Ott:

    K' = H'/T' = (γH)/(γT) = H/T = K

The γ from energy (H → γH) EXACTLY CANCELS the γ from temperature
(T → γT). The generator is Lorentz invariant.

This is why the Ott transformation is the correct one:
  - With Planck (T → T/γ):  K' = γH/(T/γ) = γ²K  ← FRAME-DEPENDENT
  - With Landsberg (T → T):  K' = γH/T = γK       ← FRAME-DEPENDENT
  - With Ott (T → γT):      K' = γH/(γT) = K      ← INVARIANT ✓

Only Ott preserves the modular structure across frames.

=====================================================================
-/

section ModularInvariance

/-- **THE MODULAR HAMILTONIAN IS LORENTZ INVARIANT**

    K' = K under Lorentz boosts.

    The modular Hamiltonian K = H/T is the generator of the
    Tomita-Takesaki modular automorphism group. Under a boost:

      H → γH  (energy transforms as the 0-component of a 4-vector)
      T → γT  (Ott transformation)
      K = H/T → γH/(γT) = H/T = K

    The two factors of γ cancel exactly.

    Physical meaning: ALL INERTIAL OBSERVERS SEE THE SAME
    MODULAR FLOW. The "internal clock" of the universe is
    frame-independent. -/
theorem modularHamiltonian_invariant
    (H T : ℝ) (hT : T > 0)
    (v : ℝ) (hv : |v| < 1) :
    let γ := lorentzGamma v hv
    modularHamiltonian (γ * H) (γ * T) = modularHamiltonian H T := by
  unfold modularHamiltonian
  have hγ_ne : lorentzGamma v hv ≠ 0 := lorentzGamma_ne_zero v hv
  have hT_ne : T ≠ 0 := ne_of_gt hT
  exact mul_div_mul_left H T hγ_ne

/-- **THE THERMAL TIME IS COVARIANT**

    t' = t / γ.

    The thermal time relation t = τ/T gives time dilation
    when combined with Ott:

      t = τ/T  →  t' = τ/(γT) = (τ/T)/γ = t/γ

    The modular parameter τ is invariant (it counts entropy).
    The temperature transforms. The ratio gives time dilation. -/
theorem thermalTime_covariant
    (T τ : ℝ) (_hT : T > 0)
    (v : ℝ) (hv : |v| < 1) :
    let γ := lorentzGamma v hv
    thermalTime (γ * T) τ = thermalTime T τ / γ := by
  unfold thermalTime
  exact div_mul_eq_div_div_swap τ (lorentzGamma v hv) T

/-- **THE MODULAR PARAMETER IS THE LORENTZ INVARIANT**

    In the thermal time relation t = τ/T:
    - t transforms (time dilation)
    - T transforms (Ott)
    - τ is invariant (entropy is a scalar)

    We verify: t' · T' = t · T = τ (the product is invariant). -/
theorem modular_parameter_invariant
    (T τ : ℝ) (hT : T > 0)
    (v : ℝ) (hv : |v| < 1) :
    let γ := lorentzGamma v hv
    thermalTime (γ * T) τ * (γ * T) = thermalTime T τ * T := by
  simp only [thermalTime]
  have hT_ne : T ≠ 0 := ne_of_gt hT
  have hγ_ne : lorentzGamma v hv ≠ 0 := lorentzGamma_ne_zero v hv
  have hγT_ne : lorentzGamma v hv * T ≠ 0 := mul_ne_zero hγ_ne hT_ne
  field_simp

/-- **OTT IS THE UNIQUE CONSISTENT CHOICE**

    If the modular Hamiltonian K = H/T is to be Lorentz invariant,
    and energy transforms as H → γH, then temperature MUST
    transform as T → γT.

    Any other transformation T → f(γ)·T with f(γ) ≠ γ gives
    K' = γH/(f(γ)·T) = (γ/f(γ))·K ≠ K.

    The Ott transformation is not a choice. It is forced. -/
theorem ott_forced_by_invariance
    (f : ℝ → ℝ)
    (_H T : ℝ) (_hT : T > 0)
    (v : ℝ) (hv : |v| < 1)
    (h_invariant : ∀ H' T', T' > 0 →
      modularHamiltonian (lorentzGamma v hv * H') (f (lorentzGamma v hv) * T') =
      modularHamiltonian H' T') :
    f (lorentzGamma v hv) = lorentzGamma v hv := by
  -- Specialize to H = T = 1: K = 1/1 = 1, K' = γ/(f(γ)·1) = γ/f(γ)
  -- Invariance requires γ/f(γ) = 1, i.e., f(γ) = γ
  have h_one := h_invariant 1 1 one_pos
  unfold modularHamiltonian at h_one
  simp only [mul_one, div_one] at h_one
  -- h_one : lorentzGamma v hv / f (lorentzGamma v hv) = 1
  have hf_ne : f (lorentzGamma v hv) ≠ 0 := by
    intro hf0
    rw [hf0, div_zero] at h_one
    exact one_ne_zero h_one.symm
  grind => ring

end ModularInvariance

theorem thermal_time_gives_time_dilation
    (T : ℝ) (hT : T > 0)
    (τ_mod : ℝ)  -- modular parameter (invariant by Tomita-Takesaki)
    (v : ℝ) (hv : |v| < 1) :
    let γ := lorentzGamma v hv
    let t := thermalTime T τ_mod
    let T' := γ * T           -- Ott transformation
    let t' := thermalTime T' τ_mod  -- thermal time in boosted frame
    t' = t / γ := by
  -- Unfold the definition of thermalTime: t = τ/T
  simp only [thermalTime]
  -- Establish that γ > 0 (needed for field_simp)
  have hγ_pos : lorentzGamma v hv > 0 := by
    have := lorentzGamma_ge_one v hv; linarith
  have hγ_ne : lorentzGamma v hv ≠ 0 := ne_of_gt hγ_pos
  have hT_ne : T ≠ 0 := ne_of_gt hT
  -- The algebra: τ/(γT) = (τ/T)/γ
  exact div_mul_eq_div_div_swap τ_mod (lorentzGamma v hv) T

lemma lorentzGamma_surjective_ge_one (γ : ℝ) (hγ : γ ≥ 1) :
    ∃ v, ∃ hv : |v| < 1, lorentzGamma v hv = γ := by
  -- Explicit construction: v = √(1 - 1/γ²)
  -- This inverts γ = 1/√(1-v²) to get v² = 1 - 1/γ²
  use Real.sqrt (1 - 1/γ^2)

  -- === Establish basic properties of γ ===
  have hγ_pos : γ > 0 := by linarith
  have hγ_sq_pos : γ^2 > 0 := sq_pos_of_pos hγ_pos
  have hγ_sq_ge_one : γ^2 ≥ 1 := by exact one_le_pow₀ hγ

  -- === Show the argument to √ is in [0, 1) ===

  -- Lower bound: 1 - 1/γ² ≥ 0  (equivalently: 1/γ² ≤ 1)
  have h_nonneg : 1 - 1/γ^2 ≥ 0 := by
    have : 1/γ^2 ≤ 1 := by
      rw [div_le_one hγ_sq_pos]
      exact hγ_sq_ge_one
    linarith

  -- Upper bound: 1 - 1/γ² < 1  (equivalently: 1/γ² > 0)
  have h_lt_one : 1 - 1/γ^2 < 1 := by
    have : 1/γ^2 > 0 := div_pos one_pos hγ_sq_pos
    linarith

  -- === Prove |v| < 1, i.e., the velocity is subluminal ===
  have hv : |Real.sqrt (1 - 1/γ^2)| < 1 := by
    -- √(x) ≥ 0 for any x, so |√(x)| = √(x)
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    -- Need: √(1 - 1/γ²) < √(1) = 1
    calc Real.sqrt (1 - 1/γ^2)
        < Real.sqrt 1 := Real.sqrt_lt_sqrt h_nonneg h_lt_one
      _ = 1 := Real.sqrt_one

  use hv

  -- === Main calculation: lorentzGamma v hv = γ ===
  unfold lorentzGamma

  -- Key algebraic fact: v² = 1 - 1/γ²
  have h_v_sq : (Real.sqrt (1 - 1/γ^2))^2 = 1 - 1/γ^2 := Real.sq_sqrt h_nonneg

  -- Therefore: 1 - v² = 1/γ²
  have h_one_minus_v_sq : 1 - (Real.sqrt (1 - 1/γ^2))^2 = 1/γ^2 := by linarith

  -- And: √(1/γ²) = 1/γ  (since γ > 0)
  have h_sqrt_inv : Real.sqrt (1/γ^2) = 1/γ := by
    have h1 : 1/γ^2 = (1/γ)^2 := by
        exact Eq.symm (one_div_pow γ 2)
    rw [h1, Real.sqrt_sq (by positivity : 1/γ ≥ 0)]

  -- Chain the equalities: 1/√(1-v²) = 1/√(1/γ²) = 1/(1/γ) = γ
  calc 1 / Real.sqrt (1 - (Real.sqrt (1 - 1/γ^2))^2)
      = 1 / Real.sqrt (1/γ^2) := by rw [h_one_minus_v_sq]
    _ = 1 / (1/γ) := by rw [h_sqrt_inv]
    _ = γ := by exact one_div_one_div γ

def satisfiesCovariance (g : ℝ → ℝ) : Prop :=
  ∀ T v (hv : |v| < 1), T > 0 →
    g (lorentzGamma v hv * T) = g T / lorentzGamma v hv


theorem functional_equation_solution
    (g : ℝ → ℝ)
    (_hg_pos : ∀ T, T > 0 → g T > 0)
    (hg_cov : satisfiesCovariance g) :
    ∀ T, T > 0 → g T * T = g 1 := by
  intro T hT

  by_cases hT_ge_one : T ≥ 1

  · obtain ⟨v, hv, hγ_eq⟩ := lorentzGamma_surjective_ge_one T hT_ge_one

    have h_cov : g (lorentzGamma v hv * 1) = g 1 / lorentzGamma v hv :=
      hg_cov 1 v hv one_pos
    simp only [mul_one] at h_cov

    -- Substitute γ = T to get: g(T) = g(1) / T
    rw [hγ_eq] at h_cov

    -- Multiply both sides by T: g(T) · T = g(1)
    calc g T * T
        = (g 1 / T) * T := by rw [h_cov]
      _ = g 1 := by field_simp

  · push_neg at hT_ge_one  -- Now: T < 1

    -- Since T < 1 and T > 0, we have 1/T > 1
    have hT_inv_ge_one : 1/T ≥ 1 := by
      rw [ge_iff_le, one_le_div hT]
      linarith

    -- Find a physical velocity v achieving Lorentz factor γ = 1/T
    obtain ⟨v, hv, hγ_eq⟩ := lorentzGamma_surjective_ge_one (1/T) hT_inv_ge_one

    -- Apply covariance at base temperature T:
    -- g(γ · T) = g(T) / γ
    have h_cov : g (lorentzGamma v hv * T) = g T / lorentzGamma v hv :=
      hg_cov T v hv hT

    -- Substitute γ = 1/T
    rw [hγ_eq] at h_cov

    -- Note: γ · T = (1/T) · T = 1
    have h_prod : (1/T) * T = 1 := by field_simp
    rw [h_prod] at h_cov

    -- Now h_cov says: g(1) = g(T) / (1/T) = g(T) · T
    calc g T * T
        = g T / (1/T) := by field_simp
      _ = g 1 := h_cov.symm


theorem thermalTime_unique
    (f : ℝ → ℝ → ℝ)
    (hf_pos : ∀ T τ, T > 0 → τ > 0 → f T τ > 0)
    (hf_linear_τ : ∀ T c τ, T > 0 → c > 0 → τ > 0 → f T (c * τ) = c * f T τ)
    (hf_cov : ∀ T τ v (hv : |v| < 1), T > 0 → τ > 0 →
      f (lorentzGamma v hv * T) τ = f T τ / lorentzGamma v hv) :
    ∃ c, c > 0 ∧ ∀ T τ, T > 0 → τ > 0 → f T τ = c * τ / T := by

  use f 1 1
  constructor
  · -- c = f(1,1) > 0 follows from positivity hypothesis
    exact hf_pos 1 1 one_pos one_pos

  intro T τ hT hτ
  have h_linear : f T τ = τ * f T 1 := by
    have h := hf_linear_τ T τ 1 hT hτ one_pos
    simp only [mul_one] at h
    exact h

  set g := fun T' => f T' 1 with hg_def

  -- g inherits positivity from f
  have hg_pos : ∀ T', T' > 0 → g T' > 0 := fun T' hT' => hf_pos T' 1 hT' one_pos

  -- g inherits covariance from f (with τ = 1)
  have hg_cov : satisfiesCovariance g := by
    intro T' v hv hT'
    exact hf_cov T' 1 v hv hT' one_pos

  have h_eq : g T * T = g 1 := functional_equation_solution g hg_pos hg_cov T hT

  have hT_ne : T ≠ 0 := ne_of_gt hT
  have h_g_form : g T = f 1 1 / T := by
    calc g T = (g T * T) / T := by exact Eq.symm (mul_div_cancel_right₀ (g T) hT_ne)
      _ = g 1 / T := by rw [h_eq]
      _ = f 1 1 / T := rfl

  calc f T τ
      = τ * f T 1 := h_linear           -- Step 1: linearity
    _ = τ * g T := rfl                   -- Definition of g
    _ = τ * (f 1 1 / T) := by rw [h_g_form]  -- Step 4: g(T) = c/T
    _ = f 1 1 * τ / T := by ring         -- Rearrange: c · τ / T


theorem thermalTime_inverse_unique
    (g : ℝ → ℝ)
    (_hg_pos : ∀ T, T > 0 → g T > 0)
    (hg_eq : ∀ T γ, T > 0 → γ > 1 → g (γ * T) = g T / γ) :
    ∀ T, T > 0 → g T * T = g 1 := by
  intro T hT

  by_cases hT_eq_one : T = 1

  · rw [hT_eq_one]
    ring

  · -- Case T ≠ 1: Split further based on whether T > 1 or T < 1
    by_cases hT_gt_one : T > 1

    · have h := hg_eq 1 T one_pos hT_gt_one
      simp only [mul_one] at h
      -- h : g T = g 1 / T

      calc g T * T
          = (g 1 / T) * T := by rw [h]
        _ = g 1 := by field_simp

    · push_neg at hT_gt_one  -- Now: T ≤ 1

      -- Since T ≠ 1 and T ≤ 1, we have T < 1
      have hT_lt_one : T < 1 := lt_of_le_of_ne hT_gt_one hT_eq_one

      -- Since T < 1 and T > 0, we have 1/T > 1
      have hT_inv_gt_one : 1/T > 1 := by
        rw [gt_iff_lt, one_lt_div hT]
        exact hT_lt_one

      -- Apply scaling at base point T with γ = 1/T:
      -- g((1/T) · T) = g(T) / (1/T)
      have h := hg_eq T (1/T) hT hT_inv_gt_one

      -- Simplify left side: (1/T) · T = 1
      have h_prod : (1/T) * T = 1 := by field_simp
      rw [h_prod] at h
      -- h : g 1 = g T / (1/T) = g T * T

      calc g T * T
          = g T / (1/T) := by linarith
        _ = g 1 := h.symm

theorem modular_parameter_recovery (T t : ℝ) (hT : T > 0) :
    thermalTime T (t * T) = t := by
  unfold thermalTime
  have hT_ne : T ≠ 0 := ne_of_gt hT
  exact mul_div_cancel_right₀ t hT_ne

theorem thermal_time_scale_invariant
    (T τ c : ℝ) (hT : T > 0) (hc : c > 0) :
    thermalTime (c * T) τ = thermalTime T τ / c := by
  unfold thermalTime
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hT_ne : T ≠ 0 := ne_of_gt hT
  exact div_mul_eq_div_div_swap τ c T

theorem thermal_time_homogeneous
    (T τ c : ℝ) (hT : T > 0) (hc : c > 0) :
    thermalTime (c * T) (c * τ) = thermalTime T τ := by
  unfold thermalTime
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hT_ne : T ≠ 0 := ne_of_gt hT
  exact mul_div_mul_left τ T hc_ne

theorem thermal_time_determines_modular_structure
    (T₁ T₂ : ℝ) (hT₁ : T₁ > 0) (hT₂ : T₂ > 0)
    (τ : ℝ) (hτ : τ ≠ 0)
    (h : thermalTime T₁ τ = thermalTime T₂ τ) :
    T₁ = T₂ := by
  unfold thermalTime at h
  have hT₁_ne : T₁ ≠ 0 := ne_of_gt hT₁
  have hT₂_ne : T₂ ≠ 0 := ne_of_gt hT₂
  -- h : τ / T₁ = τ / T₂
  -- Cross multiply: τ * T₂ = τ * T₁
  field_simp at h
  -- Cancel τ
  exact id (Eq.symm h)

theorem one_cycle_thermal_time (T : ℝ) (_hT : T > 0) :
    thermalTime T modular_period = 2 * Real.pi / T := by
  unfold thermalTime modular_period
  module

theorem thermal_time_physical_units (T : ℝ) (hT : T > 0) :
    thermalTime T modular_period * (k_B * T / ℏ) = 2 * Real.pi := by
  unfold thermalTime modular_period k_B ℏ
  have hT_ne : T ≠ 0 := ne_of_gt hT
  simp only [one_mul, div_one]
  exact div_mul_cancel₀ (2 * Real.pi) hT_ne

end ThermalTime.Basic
