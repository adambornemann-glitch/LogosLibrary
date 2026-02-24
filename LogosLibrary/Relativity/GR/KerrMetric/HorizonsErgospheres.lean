import LogosLibrary.Relativity.GR.KerrMetric.Components


namespace Kerr.Horizons
open Kerr.Components

noncomputable def r_plus (p : KerrParams) : ℝ :=
  p.M + Real.sqrt (p.M^2 - p.a^2)

noncomputable def r_minus (p : KerrParams) : ℝ :=
  p.M - Real.sqrt (p.M^2 - p.a^2)

/-!
### Basic Horizon Properties

Let's prove these horizons behave sensibly.
-/

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


/-!
### The Ergosphere: Where Spacetime Itself Rotates

The ergosphere is defined by g_tt = 0. Inside it, NO observer can remain stationary -
they're forced to rotate with the black hole!

**Mathematical condition:**
g_tt = 0  ⟺  1 - 2Mr/Σ = 0  ⟺  Σ = 2Mr  ⟺  r² + a²cos²θ = 2Mr

Solving for r:
r_E(θ) = M + √(M² - a²cos²θ)

**Key observation:**
This depends on θ! The ergosphere is NOT spherical - it's oblate, "squashed"
along the rotation axis.
-/

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
  rw [gt_iff_lt, sub_pos, one_lt_div hSigma_pos]

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

end Kerr.Horizons
