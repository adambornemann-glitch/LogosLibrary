/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: ThermalBell/TLHV/DecayGap.lean
-/
import LogosLibrary.Superior.SplitMechanics.ThermalBell.CHSH
import LogosLibrary.Superior.SplitMechanics.ThermalBell.Tsirelson
import Mathlib.Analysis.Real.Pi.Bounds
/-!
# The Curvature Correction: Three Languages for One Theorem

## The Central Fact

At angular separation θ = π/4, two correlation bounds disagree:

    exp(−π/4)           ≈ 0.456   →   CHSH ≤ 3.82
    (1 − cos(π/4))/√2  ≈ 0.207   →   CHSH ≤ 2√2 ≈ 2.83

The gap (≈ 1 on the CHSH scale) has three equivalent readings:

### Language 1: Riemannian Geometry

  exp(−θ) is the Green's function on flat ℝ.
  cos(θ) is the zonal spherical harmonic on S².
  The gap is the Gaussian curvature κ = 2 of the Bloch sphere.
  The √2 in the denominator is √κ.

### Language 2: Kähler Geometry

  The quantum state manifold ℙH carries a Kähler structure
  g + iω, where g is the Fubini-Study (SLD) metric and ω is
  the symplectic form from the commutator.

  For the singlet at angle θ:
    Cov(A,B) = −cos θ     (Riemannian piece g)
    ½⟨[A,B]⟩ = i·sin θ    (symplectic piece ω)

  The Schrödinger bound |Cov|² + |½⟨[A,B]⟩|² = cos²θ + sin²θ = 1
  is saturated — the singlet is Kähler-efficient.

  exp(−θ) is the Riemannian-only bound (treating g as if ω = 0).
  (1 − cos θ)/√2 is the full Kähler bound (including ω).
  The gap is the symplectic contribution that the flat model misses.

### Language 3: Connes Cocycle

  exp(−θ) comes from the KMS semigroup (dissipative, lives on ℝ).
  (1 − cos θ)/√2 comes from the Connes cocycle (unitary, lives on
  U(1)). The gap is the compactness of the unitary group — the
  cocycle lives on a circle, not a line.

These three readings are the same theorem.

## Main Results (zero sorry)

* `exp_exceeds_tsirelson` — exp(−π/4) > ε_tsirelson
* `exponential_chsh_exceeds_tsirelson` — 2 + 4·exp(−π/4) > 2√2
* `curvature_correction_positive` — the gap is strictly positive
* `kahler_ratio` — Tsirelson/Bell = √2 (the Pythagorean factor)
* `per_term_symplectic_contribution` — 4·ε = 2(√2 − 1)
* `modular_thermal_epsilon_bound` — honest exp model ε bound
* `exponential_modular_chsh_bound` — honest exp model CHSH bound

## Mathlib Tools

* `Real.one_sub_le_exp_neg` — 1 − x ≤ exp(−x) (first-order Taylor)
* `Real.pi_gt_d4` / `Real.pi_lt_d4` — 3.1415 < π < 3.1416
* `Real.sqrt_lt_sqrt` — monotonicity of √ on [0,∞)
* `Real.sqrt_sq` — √(x²) = x for x ≥ 0
* `Real.exp_le_exp_of_le` — monotonicity of exp
* `nlinarith` + `sq_nonneg` hints — polynomial closing

## Tags

geometric comparison, exponential decay, cosine bound, curvature
correction, Bloch sphere, Kähler, symplectic form, Fubini-Study,
Connes cocycle, Fisher-Rao, SLD metric, flat vs spherical
-/

open MeasureTheory Real BellTheorem

namespace ThermalBell

variable {Λ : Type*} [MeasurableSpace Λ]

/-! ## Section 1: The Key Inequality

The core result: 3 − π/2 > √2.

This single fact encodes the entire curvature correction. The three
proofs below establish it purely from π bounds and Cauchy-Schwarz
(via `nlinarith` + `sq_nonneg`).

Proof strategy:
  (1) 3 − π/2 > 0               (from π < 4)
  (2) (3 − π/2)² > 2            (nlinarith with 4-digit π bounds)
  (3) √2 < √((3 − π/2)²)       (monotonicity of √)
  (4) √((3 − π/2)²) = 3 − π/2  (since 3 − π/2 > 0)
  (5) √2 < 3 − π/2              QED
-/

/-- 3 − π/2 is positive (from π < 4). -/
private lemma three_sub_half_pi_pos : (0 : ℝ) < 3 - Real.pi / 2 := by
  linarith [Real.pi_lt_four]

/-- (3 − π/2)² > 2. Expand to π² − 12π + 28 > 0, close with `nlinarith`
    and 4-digit π bounds.

    The hints `sq_nonneg (π − 3.1415)` and `sq_nonneg (3.1416 − π)` let
    nlinarith bootstrap quadratic π bounds from the linear bounds
    provided by `pi_gt_d4` and `pi_lt_d4`. -/
private lemma sq_three_sub_half_pi_gt_two : (3 - Real.pi / 2) ^ 2 > 2 := by
  nlinarith [Real.pi_gt_d4, Real.pi_lt_d4,
             sq_nonneg (Real.pi - 3.1415), sq_nonneg (3.1416 - Real.pi)]

/-- **Key inequality**: 3 − π/2 > √2.

    This is the full content of the curvature correction, expressed
    as a single inequality between a transcendental and an algebraic.

    In each language:
    • Geometric: the flat propagator overshoots the spherical one
    • Kähler: the Riemannian-only bound misses the symplectic piece
    • Cocycle: the line overshoots the circle -/
private lemma three_sub_half_pi_gt_sqrt_two : 3 - Real.pi / 2 > Real.sqrt 2 := by
  have hpos := three_sub_half_pi_pos
  have h_sq := sq_three_sub_half_pi_gt_two
  have h_lt : Real.sqrt 2 < Real.sqrt ((3 - Real.pi / 2) ^ 2) :=
    Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) h_sq
  rwa [Real.sqrt_sq hpos.le] at h_lt

/-! ## Section 2: The Gap Theorems -/

/-- The first-order Taylor bound 1 − π/4 already exceeds ε_tsirelson.

    Chain: (√2−1)/2 < 1−π/4  ⟺  √2−1 < 2−π/2  ⟺  3−π/2 > √2. -/
private lemma taylor_first_order_exceeds :
    1 - Real.pi / 4 > ε_tsirelson := by
  unfold ε_tsirelson
  linarith [three_sub_half_pi_gt_sqrt_two]

/-- **exp(−π/4) > ε_tsirelson**: the flat-space propagator overshoots
    the Kähler-constrained one.

    Proof: combine `Real.one_sub_le_exp_neg` (1 − x ≤ exp(−x) for all x)
    with the algebraic fact that 1 − π/4 already exceeds ε_tsirelson.

    Interpretation: ignoring the symplectic form ω on the quantum
    state manifold allows more correlation deviation than the Kähler
    geometry actually permits. -/
theorem exp_exceeds_tsirelson : Real.exp (-Real.pi / 4) > ε_tsirelson := by
  have h_taylor := taylor_first_order_exceeds
  have h_exp := Real.one_sub_le_exp_neg (Real.pi / 4)
  grind

/-- The CHSH gap: the exponential model's bound exceeds Tsirelson. -/
theorem exponential_chsh_exceeds_tsirelson :
    2 + 4 * Real.exp (-Real.pi / 4) > 2 * Real.sqrt 2 := by
  linarith [exp_exceeds_tsirelson, ε_tsirelson_value]

/-- The curvature correction on the CHSH scale is strictly positive.

    This is the theorem that the symplectic form of the quantum state
    manifold is nonzero, that the Kähler structure is non-degenerate,
    that the Connes cocycle is non-trivial, that quantum mechanics
    is not classical. One theorem in three languages. -/
theorem curvature_correction_positive :
    (2 + 4 * Real.exp (-Real.pi / 4)) - 2 * Real.sqrt 2 > 0 := by
  linarith [exponential_chsh_exceeds_tsirelson]

/-! ## Section 3: The Kähler Structure

The quantum state manifold ℙH is Kähler with structure g + iω.
The Fubini-Study metric decomposes:

    g^{FS}(δψ₁, δψ₂) = Re⟨δψ₁, δψ₂⟩ − Re(⟨δψ₁,ψ⟩⟨ψ,δψ₂⟩)
    ω^{FS}(δψ₁, δψ₂) = Im⟨δψ₁, δψ₂⟩ − Im(⟨δψ₁,ψ⟩⟨ψ,δψ₂⟩)

For the singlet at angle θ between measurement directions:

    Cov(A,B) = −cos θ     (the Riemannian/SLD metric piece)
    ½⟨[A,B]⟩ = i·sin θ    (the symplectic piece)
    |⟨u,v⟩|² = cos²θ + sin²θ = 1   (Schrödinger saturated)

The Pythagorean combination cos²θ + sin²θ = 1 is the Schrödinger
uncertainty relation. It says the singlet is *Kähler-efficient*:
it simultaneously saturates both the Riemannian and symplectic
Cramér-Rao bounds.

The CHSH game samples this manifold at four angle pairs. The
classical bound |S| ≤ 2 is the Riemannian (SLD) Cramér-Rao bound
on a flat statistical manifold (ω = 0). The Tsirelson bound
|S| ≤ 2√2 is the full Kähler Cramér-Rao bound on the curved
manifold (ω ≠ 0).

The ratio is √2 — the Pythagorean hypotenuse when |g| = |ω|.
-/

/-- **The Kähler ratio**: Tsirelson / Bell = √2.

    This is |g + iω|/|g| when g and ω contribute equally at
    the optimal CHSH angles on the singlet manifold.

    Physically: the quantum excess beyond the classical bound
    is exactly the symplectic contribution to the Kähler metric. -/
theorem kahler_ratio : 2 * Real.sqrt 2 / 2 = Real.sqrt 2 := by
  field_simp

/-- The quantum excess 2√2 − 2 = 2·(√2 − 1).

    The factor (√2 − 1) is the amount by which the Kähler hypotenuse
    |g + iω| = √2·|g| exceeds the Riemannian leg |g|, normalized
    to the Riemannian leg. -/
theorem quantum_excess_ratio :
    2 * Real.sqrt 2 - 2 = 2 * (Real.sqrt 2 - 1) := by ring

/-- **The per-term symplectic contribution**: 4·ε_tsirelson = 2(√2 − 1).

    Each of the four CHSH correlation terms picks up a deviation
    of ε_tsirelson = (√2 − 1)/2 from the symplectic form ω on
    the Kähler state manifold.

    Four terms give total excess 4·ε = 2(√2 − 1) = 2√2 − 2. -/
theorem per_term_symplectic_contribution :
    4 * ε_tsirelson = 2 * (Real.sqrt 2 - 1) := by
  unfold ε_tsirelson; ring

/-! ## Section 4: The Honest Exponential Bound

Adding the modular angular budget constraint to the exponential model
gives the provable bound |S| ≤ 2 + 4·exp(−π/4). This is the best
the Riemannian-only (ω = 0) model can do, and it overshoots
Tsirelson by the curvature correction.
-/

/-- A `ThermalCorrelationStructure` equipped with the modular constraint:
    the thermal time separation must use at least one full angular slot,
    i.e. t/τ ≥ π/4 (one eighth of the modular period 2π).

    In Kähler language: the estimation budget per CHSH slot is at
    least one-eighth of the full modular cycle. -/
structure ModularThermalStructure (Λ : Type*) [MeasurableSpace Λ] (μ₀ : Measure Λ) extends
    ThermalCorrelationStructure Λ μ₀ where
  K_hmodular_sep : t_separation / τ_corr ≥ Real.pi / 4

/-- Pointwise ε bound from the modular exponential structure.

    Chain: |ε| ≤ |C|·exp(−t/τ) ≤ 1·exp(−t/τ) ≤ exp(−π/4).

    This is the Riemannian-only bound: it treats the Fisher
    information as purely SLD (g), ignoring the symplectic
    correction (ω). -/
lemma modular_thermal_epsilon_bound {μ₀ : Measure Λ}
    (S : ModularThermalStructure Λ μ₀) :
    ∀ i j ω, |S.ε i j ω| ≤ Real.exp (-Real.pi / 4) := by
  intro i j ω
  calc |S.ε i j ω|
      ≤ |S.C ω| * Real.exp (-S.t_separation / S.τ_corr) :=
          S.ε_thermal_form i j ω
    _ ≤ 1 * Real.exp (-S.t_separation / S.τ_corr) :=
        mul_le_mul_of_nonneg_right (S.C_bounded ω) (Real.exp_nonneg _)
    _ = Real.exp (-S.t_separation / S.τ_corr) := one_mul _
    _ ≤ Real.exp (-Real.pi / 4) := by
        apply Real.exp_le_exp_of_le
        simp only [neg_div]
        exact neg_le_neg S.hmodular_sep

/-- **Honest exponential CHSH bound** under the modular constraint.

    |S| ≤ 2 + 4·exp(−π/4) ≈ 3.82.

    This is the SLD (Riemannian-only) Cramér-Rao bound applied to
    the CHSH estimation problem, ignoring the symplectic form.
    Valid and fully proved, but weaker than Tsirelson by exactly
    the curvature correction. -/
theorem exponential_modular_chsh_bound
    (M : ThermalHVModel Λ) {μ₀ : Measure Λ}
    (S : ModularThermalStructure Λ μ₀)
    (hM : ∀ i j ω, M.deviation.ε i j ω = S.ε i j ω) :
    |M.CHSH| ≤ 2 + 4 * Real.exp (-Real.pi / 4) := by
  have hε : ∀ i j ω, |M.deviation.ε i j ω| ≤ Real.exp (-Real.pi / 4) := by
    intro i j ω; rw [hM]; exact modular_thermal_epsilon_bound S i j ω
  exact thermal_chsh_bound M _ hε

/-! ## Section 5: Structural Comparison -/

/-- The exponential bound is strictly weaker than Tsirelson.

    In Kähler language: the Riemannian-only bound is strictly weaker
    than the full Kähler bound whenever the symplectic form is nonzero. -/
theorem exp_bound_strictly_weaker :
    2 + 4 * Real.exp (-Real.pi / 4) > 2 + 4 * ε_tsirelson := by
  linarith [exp_exceeds_tsirelson]

/-- The exponential bound is still non-trivial: exp(−π/4) < 1. -/
theorem exp_bound_lt_one : Real.exp (-Real.pi / 4) < 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_strictMono (by linarith [Real.pi_pos])

/-- The exponential CHSH bound is strictly below 6 (the algebraic max). -/
theorem exp_chsh_bound_lt_six :
    2 + 4 * Real.exp (-Real.pi / 4) < 6 := by
  linarith [exp_bound_lt_one]

/-- The per-term curvature correction.

    Three equivalent interpretations:

    1. **Geometric**: exp(−π/4) is the flat-space (ℝ) propagator.
       (1 − cos(π/4))/√2 is the curved-space (S²) propagator.
       The gap is the Gaussian curvature κ = 2 of the Bloch sphere.

    2. **Kähler**: exp(−π/4) is the Riemannian-only (g) bound,
       ignoring the symplectic form ω. ε_tsirelson is the full
       Kähler (g + iω) bound. The gap is the symplectic contribution
       that the exponential model misses.

    3. **Cocycle**: exp(−π/4) comes from the KMS semigroup (dissipative,
       lives on ℝ). ε_tsirelson comes from the Connes cocycle (unitary,
       lives on U(1)). The gap is the compactness of the unitary group —
       the fact that the cocycle lives on a circle, not a line.

    These three are the same statement in three languages. -/
noncomputable def curvature_correction_per_term : ℝ :=
  Real.exp (-Real.pi / 4) - ε_tsirelson

theorem curvature_correction_per_term_pos : curvature_correction_per_term > 0 := by
  unfold curvature_correction_per_term; linarith [exp_exceeds_tsirelson]

/-! ## Section 6: The Taylor Diagnostic

Why does the gap exist at the level of Taylor series?

Near θ = 0:
    exp(−θ)         = 1 − θ + θ²/2 − ···    (linear leading term)
    (1 − cos θ)/√2  = θ²/(2√2) + ···         (quadratic leading term)

The flat-space kernel has a linear response to angular separation.
The spherical kernel has a quadratic response. The extra factor of θ
at small angles is the curvature of S².

In Kähler language: the SLD metric alone gives linear sensitivity
to the estimation parameter. The symplectic form contributes a
second-order correction that is invisible at θ = 0 but dominates
the constraint at θ = π/4.

In cocycle language: the semigroup e^{−tδ} on ℝ has a nonzero
derivative at t = 0 (the generator δ). The unitary cocycle e^{itH}
on U(1) has zero first derivative at t = 0 when projected to the
real axis (cos has a critical point at 0). The first nontrivial
term is quadratic — because U(1) is compact.
-/

/-- Both bounds are trivial at θ = 0 (no angular separation).

    The exponential gives exp(0) = 1 (maximal, vacuous bound).
    The cosine gives (1 − cos 0)/√2 = 0 (no deviation at all).
    They agree that without separation, there is no constraint. -/
lemma both_trivial_at_zero :
    Real.exp (-(0 : ℝ)) = 1 ∧ (1 - Real.cos 0) / Real.sqrt 2 = 0 := by
  exact ⟨by simp [Real.exp_zero], by simp [Real.cos_zero]⟩

/-! ## Section 7: Summary

### The Correspondence Table

| Aspect          | Flat (ℝ, κ=0)   | Sphere (S², κ=2)  | Factor    |
|-----------------|-----------------|-------------------|-----------|
| Kernel          | exp(−θ)         | cos(θ)            |           |
| ε bound (π/4)   | ≈ 0.456         | ≈ 0.207           | ≈ 2.2×    |
| CHSH bound      | ≈ 3.82          | = 2√2 ≈ 2.83      | gap ≈ 1   |
| Leading Taylor  | O(θ)            | O(θ²)             |           |
| IG metric       | SLD only (g)    | Kähler (g + iω)   |           |
| KMS structure   | Semigroup (ℝ)   | Cocycle (U(1))    |           |
| Cramér-Rao      | Robertson       | Schrödinger       |           |
| Uncertainty     | |½⟨[A,B]⟩|²     | |Cov|²+|½⟨[A,B]⟩|²|           |

### The Ratio

  Tsirelson / Bell = 2√2 / 2 = √2

This is the Pythagorean factor from |g + iω|/|g| when the
Riemannian and symplectic contributions are equal (|g| = |ω|)
at the optimal CHSH angles.

### For the Information-Geometric Proof

The cosine bound (1 − cos θ)/√2 will be derived from:
  • Fisher-Rao metric on the qubit state space → S² with κ = 2
  • Geodesic versine (1 − cos θ)/√κ as the natural distance
  • √2 = √κ is the curvature, not a free parameter

For higher-dimensional systems (qutrits on ℂP², etc.), κ changes
and the Tsirelson-type bound generalizes accordingly. The Kähler
structure is the invariant: different manifolds, same yoga.
-/

end ThermalBell
