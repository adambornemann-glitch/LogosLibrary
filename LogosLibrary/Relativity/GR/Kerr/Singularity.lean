/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Kerr/Singularity.lean
-/
import LogosLibrary.Relativity.GR.Kerr.Metric

open MinkowskiSpace QuantumMechanics

namespace Kerr
/-!
==================================================================================================================
PART IV: THE RING "SINGULARITY"
==================================================================================================================

Now we come to the main event: the ring at r = 0, θ = π/2.

**Central question:**
Is this a real physical singularity where the laws of physics break down?
Or is it a mathematical artifact of the VACUUM Kerr solution?

**Strategy:**
1. First, locate the ring precisely (where Σ = 0)
2. Show it's NOT a Killing horizon (Δ ≠ 0 there!)
3. Prove it's reachable in finite proper time
4. Calculate its temperature (requires thermodynamics!)
5. Compute complexity stored there (finite!)
6. Argue it's a "cold geometric boundary" like the horizon
-/

/-!
### Step 1: Locating the Ring

The ring is defined by Σ = 0. Let's prove exactly where this occurs.
-/

/-- The ring singularity location -/
def isRingSingularity (x : BoyerLindquistCoords) : Prop :=
  x.r = 0 ∧ x.θ = Real.pi / 2

/-- KEY THEOREM: Σ = 0 if and only if we're at the ring

    This is the precise mathematical location of the "singularity".

    **Proof sketch:**
    Σ = r² + a²cos²θ = 0
    Since r² ≥ 0 and a²cos²θ ≥ 0, both terms must vanish:
    - r² = 0  ⟹  r = 0
    - a²cos²θ = 0  ⟹  cos θ = 0 (since a ≠ 0)  ⟹  θ = π/2 (in range (0,π))
-/
/- The ring singularity is characterized by Σ = 0, which occurs at r = 0, θ = π/2.
    This is outside the Boyer-Lindquist coordinate chart (which requires r > 0). -/
theorem ring_singularity_characterization (p : KerrParams) (r θ : ℝ)
    (ha : p.a ≠ 0) (hθ_range : 0 < θ ∧ θ < Real.pi) :
    Sigma_K p r θ = 0 ↔ r = 0 ∧ θ = Real.pi / 2 := by
  unfold Sigma_K
  constructor
  · intro h
    -- Forward direction: Σ = 0 ⟹ r = 0 ∧ θ = π/2
    have hr : r = 0 := by
      by_contra hr'
      have h_r_sq_pos : r^2 > 0 := sq_pos_of_ne_zero hr'
      have h_a_cos_nonneg : p.a^2 * (Real.cos θ)^2 ≥ 0 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith
    have hcos : Real.cos θ = 0 := by
      have h_prod : p.a^2 * (Real.cos θ)^2 = 0 := by
        simp only [hr, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at h
        exact h
      have ha_sq_pos : p.a^2 > 0 := sq_pos_of_ne_zero ha
      have h_cos_sq_zero : (Real.cos θ)^2 = 0 :=
        (mul_eq_zero.mp h_prod).resolve_left (ne_of_gt ha_sq_pos)
      exact sq_eq_zero_iff.mp h_cos_sq_zero
    have hθ_eq : θ = Real.pi / 2 := by
      rw [Real.cos_eq_zero_iff] at hcos
      obtain ⟨k, hk⟩ := hcos
      have hpi_pos : Real.pi > 0 := Real.pi_pos
      have h_pi_half_pos : Real.pi / 2 > 0 := by linarith
      -- From 0 < θ, we get 2k + 1 > 0
      have h_pos : (2 : ℝ) * ↑k + 1 > 0 := by
        have h1 : 0 < θ := hθ_range.1
        rw [hk] at h1
        have h1' : 0 < (2 * ↑k + 1) * (Real.pi / 2) := by linarith
        exact (mul_pos_iff_of_pos_right h_pi_half_pos).mp h1'
      -- From θ < π, we get 2k + 1 < 2
      have h_lt : (2 : ℝ) * ↑k + 1 < 2 := by
        have h2 : θ < Real.pi := hθ_range.2
        rw [hk] at h2
        have h2' : (2 * ↑k + 1) * (Real.pi / 2) < Real.pi := by linarith
        calc (2 : ℝ) * ↑k + 1
            = ((2 : ℝ) * ↑k + 1) * (Real.pi / 2) / (Real.pi / 2) := by field_simp
          _ < Real.pi / (Real.pi / 2) := by
              apply div_lt_div_of_pos_right h2' h_pi_half_pos
          _ = 2 := by field_simp
      -- So k = 0
      have hk_eq : k = 0 := by
        have h1 : (k : ℝ) > -1/2 := by linarith
        have h2 : (k : ℝ) < 1/2 := by linarith
        have h3 : (k : ℤ) ≥ 0 := by
          by_contra hc
          push_neg at hc
          have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hc
          linarith
        have h4 : (k : ℤ) ≤ 0 := by
          by_contra hc
          push_neg at hc
          have : (k : ℝ) ≥ 1 := by exact_mod_cast hc
          linarith
        exact le_antisymm h4 h3
      rw [hk_eq] at hk
      simp at hk
      exact hk
    exact ⟨hr, hθ_eq⟩
  · -- Reverse direction: r = 0 ∧ θ = π/2 ⟹ Σ = 0
    intro ⟨hr, hθ⟩
    simp [hr, hθ, Real.cos_pi_div_two]

/-!
**Pedagogical note:**
In Schwarzschild (a = 0), we have Σ = r², so Σ = 0 means r = 0 for ALL θ.
The "singularity" is a POINT.

In Kerr (a ≠ 0), Σ = 0 requires BOTH r = 0 AND θ = π/2. This picks out
a specific ring in the equatorial plane!

**Why a ring?**
In oblate spheroidal coordinates (more natural for Kerr), this is a ring
of coordinate radius a. It's the "center" of the oblate coordinate system.
-/

/-- In Schwarzschild, the singularity is a point (all θ) -/
theorem schwarzschild_singularity_is_point (M : ℝ) (hM : 0 < M)
    (x : BoyerLindquistCoords) :
    Sigma_K (schwarzschildParams M hM) x.r x.θ = 0 ↔ x.r = 0 := by
  unfold Sigma_K schwarzschildParams
  simp

/-!
### Step 2: The Ring is NOT a Killing Horizon

This is crucial! The horizons r_± are where Δ = 0. But at the ring:
-/

/-- At the ring (r = 0), Δ = a², which is nonzero for rotating black holes.
    This proves the ring is NOT a Killing horizon (horizons have Δ = 0). -/
theorem ring_not_horizon (p : KerrParams) (ha : p.a ≠ 0) :
    Δ p 0 ≠ 0 := by
  unfold Δ
  have h_eq : (0 : ℝ)^2 - 2 * p.M * 0 + p.a^2 = p.a^2 := by
    calc (0 : ℝ)^2 - 2 * p.M * 0 + p.a^2
        = 0 - 0 + p.a^2 := by ring
      _ = p.a^2 := by ring
  rw [h_eq]
  exact ne_of_gt (sq_pos_of_ne_zero ha)

/-- More explicitly: Δ = a² at the ring -/
theorem ring_delta_nonzero (p : KerrParams) (ha : p.a ≠ 0) :
    Δ p 0 = p.a^2 ∧ p.a^2 ≠ 0 := by
  unfold Δ
  constructor
  · ring
  · exact ne_of_gt (sq_pos_of_ne_zero ha)

/-!
**This is THE KEY GEOMETRIC FACT:**

At horizons:     Δ = 0,  Σ ≠ 0  →  Can compute surface gravity geometrically
At the ring:     Δ ≠ 0,  Σ = 0  →  CANNOT compute surface gravity geometrically!

The ring is a DIFFERENT kind of surface than the horizons. It's not a Killing
horizon, so we can't apply the standard Killing horizon formulas to compute
temperature.

**Implication:**
Ring temperature cannot be derived from geometry alone. We need THERMODYNAMICS.
-/

theorem ring_no_geometric_temperature (p : KerrParams) (ha : p.a ≠ 0) :
    -- Horizons satisfy Δ = 0
    Δ p (r_plus p) = 0 ∧
    Δ p (r_minus p) = 0 ∧
    -- Ring does NOT
    Δ p 0 ≠ 0 := by
  constructor
  · exact (delta_zero_at_horizons p).1
  constructor
  · exact (delta_zero_at_horizons p).2
  · rw [(ring_delta_nonzero p ha).1]
    exact (ring_delta_nonzero p ha).2

end Kerr
