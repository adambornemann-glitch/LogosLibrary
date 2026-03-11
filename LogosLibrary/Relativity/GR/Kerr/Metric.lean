/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann

==================================================================================================================
  THE KERR METRIC: A Rigorous Treatment of Rotating Black Holes
==================================================================================================================

**Notation and Conventions:**

- G = c = ℏ = 1 (geometric units)
- M: black hole mass (dimension: length, ~1.5 km for solar mass)
- a: spin parameter = J/M (dimension: length)
- r, θ, φ: Boyer-Lindquist spatial coordinates
- t: Boyer-Lindquist time coordinate
- Σ ≡ r² + a²cos²θ (vanishes at ring)
- Δ ≡ r² - 2Mr + a² (vanishes at horizons)
- ρ² ≡ r² + a² (auxiliary function)

-/
import LogosLibrary.Relativity.SR.MinkowskiSpacetime
import LogosLibrary.QuantumMechanics.Uncertainty.UnboundedOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

open MinkowskiSpace QuantumMechanics

namespace Kerr
/-- Kerr spacetime parameters

    Physical constraints:
    - M > 0 (positive mass, obviously)
    - |a| ≤ M (subextremal condition - prevents naked singularities)

    If |a| > M, we'd have a "naked singularity" - the ring would be visible from
    infinity. This probably can't happen in nature (cosmic censorship conjecture),
    but even if it could, the formulas would be different.
-/
structure KerrParams where
  M : ℝ  -- Mass parameter (in geometric units, dimension: length)
  a : ℝ  -- Spin parameter = J/M where J is angular momentum
  mass_positive : 0 < M
  subextremal : |a| ≤ M  -- No naked singularities allowed

/-- Boyer-Lindquist coordinates for Kerr spacetime

    These coordinates cover the exterior region and can be analytically continued
    through the horizons (using Kerr-Schild or other coordinates).

    Coordinate ranges:
    - t ∈ (-∞, ∞) (time)
    - r ∈ (0, ∞) (radial-like coordinate)
    - θ ∈ (0, π) (polar angle from north pole)
    - φ ∈ [0, 2π) (azimuthal angle)

    We enforce r > 0 and 0 < θ < π to avoid coordinate singularities.
-/
structure BoyerLindquistCoords where
  t : ℝ   -- Time coordinate
  r : ℝ   -- Radial coordinate
  θ : ℝ   -- Polar angle (colatitude)
  φ : ℝ   -- Azimuthal angle
  r_positive : 0 < r
  θ_range : 0 < θ ∧ θ < π  -- Exclude poles to avoid coordinate issues

/-- Σ (Sigma): The key function that vanishes at the ring singularity

    Definition: Σ ≡ r² + a² cos² θ

    **Physical meaning:**
    This is essentially the "effective radial coordinate" taking into account
    the oblate spheroidal structure. It measures distance from the symmetry axis.

    **Critical property:**
    Σ = 0 occurs ONLY at r = 0 AND θ = π/2 (equatorial plane at origin)
    This is the location of the "ring singularity"

    **Why "ring"?**
    At r = 0, θ = π/2, we're at the center of the equatorial plane.
    In oblate spheroidal coordinates, this traces out a ring of radius a!
-/
noncomputable def Sigma_K (p : KerrParams) (r θ : ℝ) : ℝ :=
  r^2 + p.a^2 * Real.cos θ^2

/-- Δ (Delta): The key function that vanishes at event horizons

    Definition: Δ ≡ r² - 2Mr + a²

    **Physical meaning:**
    This determines the causal structure - where can light escape?
    Δ = 0 marks the boundaries (horizons) between regions.

    **Mathematical structure:**
    This is a quadratic in r:
    Δ = (r - r₊)(r - r₋)
    where r₊ = M + √(M² - a²) (outer horizon)
          r₋ = M - √(M² - a²) (inner horizon)

    **Why two horizons?**
    Rotation creates two distinct surfaces:
    - Outer horizon: true event horizon (no escape)
    - Inner horizon: Cauchy horizon (weird causal structure)
-/
noncomputable def Δ (p : KerrParams) (r : ℝ) : ℝ :=
  r^2 - 2 * p.M * r + p.a^2

-- Alternative name to avoid conflicts with other Delta definitions
noncomputable def Delta_K (p : KerrParams) (r : ℝ) : ℝ :=
  r^2 - 2 * p.M * r + p.a^2

/-- ρ² (rho squared): Auxiliary radial function

    Definition: ρ² ≡ r² + a²

    This appears in the metric components and is related to the
    "circumferential radius" - if you measure the circumference of
    a circle at radius r in the equatorial plane, you get 2πρ, not 2πr!
-/
noncomputable def rho_sq (p : KerrParams) (r : ℝ) : ℝ :=
  r^2 + p.a^2

/-!
### Basic Properties of These Functions

Before diving into the full metric, let's establish some simple facts about
Σ, Δ, and ρ². These will be useful later.
-/

/-- Σ is always positive except at the ring -/
theorem Sigma_K_nonneg (p : KerrParams) (r θ : ℝ) :
    Sigma_K p r θ ≥ 0 := by
  unfold Sigma_K
  apply add_nonneg
  · exact sq_nonneg r
  · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- ρ² is always positive (for r > 0) -/
theorem rho_sq_pos (p : KerrParams) (r : ℝ) (hr : 0 < r) :
    rho_sq p r > 0 := by
  unfold rho_sq
  have : r^2 > 0 := sq_pos_of_ne_zero (ne_of_gt hr)
  linarith [sq_nonneg p.a]

/-!
### Schwarzschild Limit (a = 0)

Before tackling the full rotating case, let's check that when a = 0,
we recover the familiar Schwarzschild solution.

**Physical picture:**
If the black hole isn't rotating (a = 0), all the complexity should disappear
and we should get back the simple spherically symmetric case.

This is a crucial consistency check - any good generalization should reduce
to the known special case!
-/

/-- Schwarzschild parameters: non-rotating black hole -/
def schwarzschildParams (M : ℝ) (hM : 0 < M) : KerrParams :=
  ⟨M, 0, hM, by simp; linarith⟩

/-- In Schwarzschild limit, Σ reduces to r² -/
theorem schwarzschild_limit_sigma (M r θ : ℝ) (hM : 0 < M) :
    Sigma_K (schwarzschildParams M hM) r θ = r^2 := by
  unfold Sigma_K schwarzschildParams
  simp

/-- In Schwarzschild limit, Δ reduces to r² - 2Mr -/
theorem schwarzschild_limit_delta (M r : ℝ) (hM : 0 < M) :
    Δ (schwarzschildParams M hM) r = r^2 - 2*M*r := by
  unfold Δ schwarzschildParams
  ring

/-
### The Full Kerr Metric Tensor

Now we're ready for the complete metric. In Boyer-Lindquist coordinates:

ds² = -(1 - 2Mr/Σ)dt² - (4Mar sin²θ/Σ) dt dφ
      + (Σ/Δ)dr² + Σ dθ²
      + ((r² + a²)² - a²Δ sin²θ)/Σ sin²θ dφ²

**What this means:**
- g_tt: Time-time component (gravitational redshift)
- g_tφ: Time-azimuthal coupling (frame dragging!)
- g_rr: Radial-radial component (proper distance in radial direction)
- g_θθ: Angular component
- g_φφ: Azimuthal component (proper distance around rotation axis)

**Key feature:**
The g_tφ term is the frame-dragging - spacetime itself is rotating with the
black hole! This is the signature of rotation in GR.
-/
noncomputable def kerrMetric (p : KerrParams) (x : BoyerLindquistCoords)
    (v w : Fin 4 → ℝ) : ℝ :=
  let r := x.r
  let θ := x.θ
  let sin_θ := Real.sin θ
  let Sigma_val := Sigma_K p r θ
  let Delta_val := Delta_K p r
  let rho2_val := rho_sq p r
  -- Metric components (these are the g_μν values)
  let g_tt := -(1 - 2 * p.M * r / Sigma_val)
  let g_tphi := -2 * p.M * p.a * r * sin_θ^2 / Sigma_val
  let g_rr := Sigma_val / Delta_val
  let g_theta_theta := Sigma_val
  let g_phi_phi := (rho2_val^2 - p.a^2 * Delta_val * sin_θ^2) / Sigma_val * sin_θ^2
  -- Compute g_μν v^μ w^ν (metric contraction)
  g_tt * v 0 * w 0 +
  g_rr * v 1 * w 1 +
  g_theta_theta * v 2 * w 2 +
  g_phi_phi * v 3 * w 3 +
  2 * g_tphi * v 0 * w 3  -- Cross term g_tφ appears twice (symmetry)

-- Convenient notation
notation "⟪" v ", " w "⟫_K[" p "," x "]" => kerrMetric p x v w

noncomputable def r_plus (p : KerrParams) : ℝ :=
  p.M + Real.sqrt (p.M^2 - p.a^2)

noncomputable def r_minus (p : KerrParams) : ℝ :=
  p.M - Real.sqrt (p.M^2 - p.a^2)

/-- The outer horizon exists and is positive -/
theorem r_plus_positive (p : KerrParams) : r_plus p > 0 := by
  unfold r_plus
  have h : p.M^2 - p.a^2 ≥ 0 := by
    have hab : |p.a| ≤ p.M := p.subextremal
    have : p.a^2 ≤ p.M^2 := by
      calc p.a^2
          = |p.a|^2 := (sq_abs p.a).symm
        _ ≤ p.M^2 := by nlinarith [hab, abs_nonneg p.a, p.mass_positive]
    linarith
  have : Real.sqrt (p.M^2 - p.a^2) ≥ 0 := Real.sqrt_nonneg _
  linarith [p.mass_positive]

/-- The inner horizon is positive for rotating black holes -/
theorem r_minus_positive (p : KerrParams) (ha : 0 < |p.a| ∧ |p.a| < p.M) :
    r_minus p > 0 := by
  unfold r_minus
  have ha' : p.a ≠ 0 := by
    intro ha_zero
    rw [ha_zero, abs_zero] at ha
    linarith [ha.1]
  have hab : p.M^2 - p.a^2 > 0 := by
    have : p.a^2 < p.M^2 := by
      calc p.a^2
          = |p.a|^2 := (sq_abs p.a).symm
        _ < p.M^2 := by nlinarith [ha.1, ha.2, abs_nonneg p.a, p.mass_positive]
    linarith
  have : Real.sqrt (p.M^2 - p.a^2) < p.M := by
    rw [Real.sqrt_lt' p.mass_positive]
    have : p.a^2 > 0 := sq_pos_of_ne_zero ha'
    linarith
  linarith

/-- The horizons are ordered correctly: 0 < r₋ < r₊ (for rotating BH) -/
theorem horizons_ordered (p : KerrParams) (ha : 0 < |p.a| ∧ |p.a| < p.M) :
    0 < r_minus p ∧ r_minus p < r_plus p := by
  constructor
  · exact r_minus_positive p ha
  · unfold r_plus r_minus
    have : Real.sqrt (p.M^2 - p.a^2) > 0 := by
      apply Real.sqrt_pos.mpr
      have : p.a^2 < p.M^2 := by
        calc p.a^2 = |p.a|^2 := (sq_abs p.a).symm
          _ < p.M^2 := by nlinarith [ha.1, ha.2, abs_nonneg p.a, p.mass_positive]
      linarith
    linarith

/-!
### The Horizons ARE Where Δ Vanishes (Verification)

This is a crucial check - we've defined r_± as the solutions to Δ = 0,
but let's verify this explicitly.
-/

theorem delta_zero_at_horizons (p : KerrParams) :
    Δ p (r_plus p) = 0 ∧ Δ p (r_minus p) = 0 := by
  unfold Δ r_plus r_minus
  have h_nonneg : p.M^2 - p.a^2 ≥ 0 := by
    have : p.a^2 ≤ p.M^2 := by
      calc p.a^2 = |p.a|^2 := (sq_abs p.a).symm
        _ ≤ p.M^2 := by nlinarith [p.subextremal, abs_nonneg p.a, p.mass_positive]
    linarith
  have hs : (Real.sqrt (p.M^2 - p.a^2))^2 = p.M^2 - p.a^2 :=
    Real.sq_sqrt h_nonneg
  constructor
  · -- At r_+ = M + √(M² - a²)
    calc (p.M + Real.sqrt (p.M^2 - p.a^2))^2
          - 2 * p.M * (p.M + Real.sqrt (p.M^2 - p.a^2)) + p.a^2
        = p.M^2 + 2*p.M*Real.sqrt (p.M^2 - p.a^2)
          + (Real.sqrt (p.M^2 - p.a^2))^2
          - 2*p.M^2 - 2*p.M*Real.sqrt (p.M^2 - p.a^2) + p.a^2 := by ring
      _ = (Real.sqrt (p.M^2 - p.a^2))^2 - p.M^2 + p.a^2 := by ring
      _ = (p.M^2 - p.a^2) - p.M^2 + p.a^2 := by rw [hs]
      _ = 0 := by ring
  · -- At r_- = M - √(M² - a²)
    calc (p.M - Real.sqrt (p.M^2 - p.a^2))^2
          - 2 * p.M * (p.M - Real.sqrt (p.M^2 - p.a^2)) + p.a^2
        = p.M^2 - 2*p.M*Real.sqrt (p.M^2 - p.a^2)
          + (Real.sqrt (p.M^2 - p.a^2))^2
          - 2*p.M^2 + 2*p.M*Real.sqrt (p.M^2 - p.a^2) + p.a^2 := by ring
      _ = (Real.sqrt (p.M^2 - p.a^2))^2 - p.M^2 + p.a^2 := by ring
      _ = (p.M^2 - p.a^2) - p.M^2 + p.a^2 := by rw [hs]
      _ = 0 := by ring

/-!
**Pedagogical point:**
Notice the calculation is identical for both horizons! This is because Δ is
symmetric under r → 2M - r (up to the overall sign). This is NOT an accident -
it's related to a deep symmetry of the Kerr metric.
-/

/-- In Schwarzschild limit (a=0), both horizons coincide at r = 2M -/
theorem schwarzschild_limit_horizons (M : ℝ) (hM : 0 < M) :
    let p := schwarzschildParams M hM
    r_plus p = 2 * M ∧ r_minus p = 0 := by
  unfold schwarzschildParams r_plus r_minus
  simp
  constructor
  · have : Real.sqrt (M^2) = |M| := Real.sqrt_sq_eq_abs M
    have : |M| = M := abs_of_pos hM
    linarith
  · have : Real.sqrt (M^2) = M := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hM]
    linarith

noncomputable def r_ergosphere (p : KerrParams) (θ : ℝ) : ℝ :=
  p.M + Real.sqrt (p.M^2 - p.a^2 * Real.cos θ^2)

/-- Frame-dragging angular velocity Ω = -g_tφ / g_φφ

    **Physical meaning:**
    This is how fast a stationary observer (if they could exist) would
    see the spacetime rotating around them. Inside the ergosphere, all
    observers MUST rotate with Ω > 0.
-/
noncomputable def frameDraggingOmega (p : KerrParams) (x : BoyerLindquistCoords) : ℝ :=
  let r := x.r
  let θ := x.θ
  let sin_θ := Real.sin θ
  let Δ_val := Δ p r
  let rho_sq_val := rho_sq p r
  -- Ω = -g_tφ / g_φφ
  (2 * p.M * p.a * r) / (rho_sq_val^2 - p.a^2 * Δ_val * sin_θ^2)

/-!
**Key theorem:** Inside the ergosphere, Ω > 0 and you MUST co-rotate!

(We won't prove this fully here, but the idea is that g_tt < 0 outside ergosphere
means timelike vectors can point in the "stationary" direction ∂_t. Inside the
ergosphere where g_tt > 0, you need a component in the φ direction to be timelike.)
-/

theorem ergosphere_forces_rotation (p : KerrParams) (x : BoyerLindquistCoords)
    (ha : p.a ≠ 0)
    (_ /-h-/ : x.r < r_ergosphere p x.θ) :
    frameDraggingOmega p x ≠ 0 := by
  unfold frameDraggingOmega
  have hr : x.r > 0 := x.r_positive
  have hM : p.M > 0 := p.mass_positive
  -- Numerator: 2 * M * a * r ≠ 0
  have h_num : 2 * p.M * p.a * x.r ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    · norm_num
    · exact ne_of_gt hM
    · exact ha
    · exact ne_of_gt hr
  -- Denominator: (r² + a²)² - a²Δsin²θ > 0
  have h_denom_pos : (rho_sq p x.r)^2 - p.a^2 * Δ p x.r * (Real.sin x.θ)^2 > 0 := by
    unfold rho_sq Δ
    -- Key identity: (r² + a²)² - a²(r² - 2Mr + a²) = r(r³ + ra² + 2Ma²)
    have h_identity : (x.r^2 + p.a^2)^2 - p.a^2 * (x.r^2 - 2*p.M*x.r + p.a^2) =
                      x.r * (x.r^3 + x.r * p.a^2 + 2 * p.M * p.a^2) := by ring
    have h_identity_pos : (x.r^2 + p.a^2)^2 - p.a^2 * (x.r^2 - 2*p.M*x.r + p.a^2) > 0 := by
      rw [h_identity]
      apply mul_pos hr
      have h1 : x.r^3 > 0 := pow_pos hr 3
      have h2 : x.r * p.a^2 ≥ 0 := mul_nonneg (le_of_lt hr) (sq_nonneg _)
      have h3 : 2 * p.M * p.a^2 ≥ 0 := by
        apply mul_nonneg
        · apply mul_nonneg; norm_num; exact le_of_lt hM
        · exact sq_nonneg _
      linarith
    by_cases hΔ : x.r^2 - 2*p.M*x.r + p.a^2 ≤ 0
    · -- Case Δ ≤ 0: subtracted term is ≤ 0
      have h1 : p.a^2 * (x.r^2 - 2*p.M*x.r + p.a^2) * (Real.sin x.θ)^2 ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg
        · apply mul_nonpos_of_nonneg_of_nonpos
          · exact sq_nonneg p.a
          · exact hΔ
        · exact sq_nonneg (Real.sin x.θ)
      have h2 : (x.r^2 + p.a^2)^2 > 0 :=
        sq_pos_of_pos (add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) (sq_nonneg _))
      linarith
    · -- Case Δ > 0: use sin²θ ≤ 1
      push_neg at hΔ
      have h_sin_le : (Real.sin x.θ)^2 ≤ 1 := Real.sin_sq_le_one x.θ
      have h_a2Δ_nonneg : p.a^2 * (x.r^2 - 2*p.M*x.r + p.a^2) ≥ 0 := by
        apply mul_nonneg
        · exact sq_nonneg p.a
        · exact le_of_lt hΔ
      calc (x.r^2 + p.a^2)^2 - p.a^2 * (x.r^2 - 2*p.M*x.r + p.a^2) * (Real.sin x.θ)^2
          ≥ (x.r^2 + p.a^2)^2 - p.a^2 * (x.r^2 - 2*p.M*x.r + p.a^2) * 1 := by
            have : p.a^2 * (x.r^2 - 2*p.M*x.r + p.a^2) * (Real.sin x.θ)^2 ≤
                   p.a^2 * (x.r^2 - 2*p.M*x.r + p.a^2) * 1 := by
              apply mul_le_mul_of_nonneg_left h_sin_le h_a2Δ_nonneg
            linarith
        _ = (x.r^2 + p.a^2)^2 - p.a^2 * (x.r^2 - 2*p.M*x.r + p.a^2) := by ring
        _ > 0 := h_identity_pos

  exact div_ne_zero h_num (ne_of_gt h_denom_pos)

/-- The tt-component of the Kerr metric: g_tt = -(1 - 2Mr/Σ) -/
noncomputable def g_tt (p : KerrParams) (r θ : ℝ) : ℝ :=
  -(1 - 2 * p.M * r / Sigma_K p r θ)

/-- The inner boundary of the ergosphere (where g_tt = 0 on the inside) -/
noncomputable def r_ergosphere_inner (p : KerrParams) (θ : ℝ) : ℝ :=
  p.M - Real.sqrt (p.M^2 - p.a^2 * (Real.cos θ)^2)

/-- Inside the ergosphere (between inner and outer static limits),
    the t-direction becomes spacelike (g_tt > 0).

    Physical meaning: No observer can remain stationary with respect to
    infinity — spacetime itself is dragged around by the rotating black hole.
    Any physical observer MUST have angular velocity Ω > 0. -/
theorem ergosphere_t_spacelike (p : KerrParams) (x : BoyerLindquistCoords)
    (h_upper : x.r < r_ergosphere p x.θ)
    (h_lower : x.r > r_ergosphere_inner p x.θ) :
    g_tt p x.r x.θ > 0 := by
  unfold g_tt r_ergosphere r_ergosphere_inner at *
  have hr : x.r > 0 := x.r_positive
  have hM : p.M > 0 := p.mass_positive
  -- Sigma > 0 (we're not at the ring)
  have hSigma_pos : Sigma_K p x.r x.θ > 0 := by
    unfold Sigma_K
    have h1 : x.r^2 > 0 := sq_pos_of_pos hr
    have h2 : p.a^2 * (Real.cos x.θ)^2 ≥ 0 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  -- We need to show: -(1 - 2Mr/Σ) > 0
  -- Rewrite as: 2Mr/Σ - 1 > 0, i.e., 2Mr/Σ > 1, i.e., 2Mr > Σ
  rw [neg_sub]
  suffices 1 < 2 * p.M * x.r / Sigma_K p x.r x.θ by linarith
  rw [one_lt_div hSigma_pos]
  -- Goal: Σ < 2Mr, i.e., r² + a²cos²θ < 2Mr
  unfold Sigma_K
  -- Let s = √(M² - a²cos²θ). The condition becomes |r - M| < s.
  set s := Real.sqrt (p.M^2 - p.a^2 * (Real.cos x.θ)^2) with hs_def
  -- From hypotheses: M - s < r < M + s
  have h_lt_upper : x.r < p.M + s := h_upper
  have h_gt_lower : x.r > p.M - s := h_lower
  -- Need: M² - a²cos²θ ≥ 0 for s to be well-defined
  have h_discriminant : p.M^2 - p.a^2 * (Real.cos x.θ)^2 ≥ 0 := by
    have h1 : (Real.cos x.θ)^2 ≤ 1 := Real.cos_sq_le_one x.θ
    have h2 : p.a^2 * (Real.cos x.θ)^2 ≤ p.a^2 * 1 := by
      apply mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    have h3 : p.a^2 ≤ p.M^2 := by
      have := p.subextremal
      calc p.a^2 = |p.a|^2 := (sq_abs p.a).symm
        _ ≤ p.M^2 := by nlinarith [abs_nonneg p.a, hM]
    linarith
  -- Key identity: r² - 2Mr + a²cos²θ = (r - M)² - s²
  have h_identity : x.r^2 - 2*p.M*x.r + p.a^2*(Real.cos x.θ)^2 =
                    (x.r - p.M)^2 - s^2 := by
    have hs_sq : s^2 = p.M^2 - p.a^2 * (Real.cos x.θ)^2 :=
      Real.sq_sqrt h_discriminant
    calc x.r^2 - 2*p.M*x.r + p.a^2*(Real.cos x.θ)^2
        = (x.r - p.M)^2 - p.M^2 + p.a^2*(Real.cos x.θ)^2 := by ring
      _ = (x.r - p.M)^2 - (p.M^2 - p.a^2*(Real.cos x.θ)^2) := by ring
      _ = (x.r - p.M)^2 - s^2 := by rw [hs_sq]
  -- We need (r - M)² < s², i.e., |r - M| < s
  -- This follows from M - s < r < M + s
  have h_abs_lt : |x.r - p.M| < s := by
    rw [abs_lt]
    constructor
    · -- -s < r - M, i.e., M - s < r
      linarith
    · -- r - M < s, i.e., r < M + s
      linarith
  have h_sq_lt : (x.r - p.M)^2 < s^2 := by
    have := sq_lt_sq' (by linarith : -s < x.r - p.M) (by linarith : x.r - p.M < s)
    simp only at this
    exact this
  -- Therefore r² + a²cos²θ < 2Mr
  calc x.r^2 + p.a^2 * (Real.cos x.θ)^2
      = x.r^2 - 2*p.M*x.r + p.a^2*(Real.cos x.θ)^2 + 2*p.M*x.r := by ring
    _ = (x.r - p.M)^2 - s^2 + 2*p.M*x.r := by rw [h_identity]
    _ < 0 - s^2 + 2*p.M*x.r + s^2 := by linarith [h_sq_lt]
    _ = 2 * p.M * x.r := by ring

  end Kerr
