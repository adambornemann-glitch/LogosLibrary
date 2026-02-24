import LogosLibrary.Relativity.SR.MinkowskiSpacetime
import LogosLibrary.QuantumMechanics.Uncertainty.UnboundedOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real


open MinkowskiSpace QuantumMechanics

namespace Kerr.Components
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

end Kerr.Components
