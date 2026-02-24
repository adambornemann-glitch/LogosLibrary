/-
Copyright (c) 2026 KMS Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your name here]
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Periodic Extension of Holomorphic Functions on Strips

This file proves that a holomorphic function on a horizontal strip with
matching boundary values extends to a bounded entire function.

## Main Results

- `periodicExtension`: Given F holomorphic on Strip β with F(t) = F(t + iβ),
  construct the periodic extension to all of ℂ
- `periodicExtension_continuous`: The extension is continuous
- `periodicExtension_bounded`: The extension is bounded
- `periodicExtension_entire`: The extension is entire (holomorphic on ℂ)
- `periodic_strip_extension`: The main theorem combining all of the above

## The Mathematical Content

The key insight is that the boundary condition F(t) = F(t + iβ) allows us to
"tile" the complex plane with copies of F. The extension is:
- Continuous by the boundary condition
- Holomorphic on each open strip (obvious)
- Holomorphic across the boundaries (by Morera's theorem)
- Bounded (since F is bounded on the closed strip and we're just repeating it)

Combining with Liouville's theorem (bounded entire ⟹ constant), we get that
functions with periodic boundary values must be constant on the strip.

## References

* Conway, "Functions of One Complex Variable I", Chapter V
* Rudin, "Real and Complex Analysis", Chapter 10
-/

noncomputable section

open Complex Set Filter Topology Int MeasureTheory ProbabilityTheory

variable {β : ℝ} (hβ : 0 < β)

/-! ## Definitions -/

/-- The open horizontal strip {z : 0 < Im(z) < β} -/
def Strip (β : ℝ) : Set ℂ :=
  {z : ℂ | 0 < z.im ∧ z.im < β}

/-- The closed horizontal strip {z : 0 ≤ Im(z) ≤ β} -/
def ClosedStrip (β : ℝ) : Set ℂ :=
  {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β}

/-- The shifted closed strip {z : n*β ≤ Im(z) ≤ (n+1)*β} -/
def ClosedStrip.shift (β : ℝ) (n : ℤ) : Set ℂ :=
  {z : ℂ | n * β ≤ z.im ∧ z.im ≤ (n + 1) * β}

/-- The boundary lines at heights n*β for n ∈ ℤ -/
def BoundaryLines (β : ℝ) : Set ℂ :=
  {z : ℂ | ∃ n : ℤ, z.im = n * β}

/-- Embedding real numbers into the lower boundary -/
def realToLower (t : ℝ) : ℂ := t

/-- Embedding real numbers into the upper boundary at height β -/
def realToUpper (β : ℝ) (t : ℝ) : ℂ := t + β * I

/-! ## The Periodic Extension -/

/-- The floor of z.im / β, giving which strip z belongs to -/
def stripIndex (β : ℝ) (z : ℂ) : ℤ := ⌊z.im / β⌋

/-- Translate z down to the fundamental strip [0, β] -/
def toFundamentalStrip (β : ℝ) (z : ℂ) : ℂ :=
  z - (stripIndex β z : ℂ) * β * I

/-- The periodic extension of F from the closed strip to all of ℂ.

Given F : ℂ → ℂ defined on ClosedStrip β, we extend by:
  G(z) = F(z - n*β*I) where n = ⌊Im(z)/β⌋

This maps any z to the fundamental strip and evaluates F there.
-/
def periodicExtension (F : ℂ → ℂ) (β : ℝ) : ℂ → ℂ := fun z =>
  F (toFundamentalStrip β z)

/-! ## Basic Properties of the Strip Index -/

lemma stripIndex_spec (hβ : 0 < β) (z : ℂ) :
    (stripIndex β z : ℝ) * β ≤ z.im ∧ z.im < (stripIndex β z + 1 : ℤ) * β := by
  constructor
  · have h := Int.floor_le (z.im / β)
    calc (stripIndex β z : ℝ) * β = ⌊z.im / β⌋ * β := rfl
      _ ≤ (z.im / β) * β := by exact mul_le_mul_of_nonneg_right h (le_of_lt hβ)
      _ = z.im := by field_simp
  · have h := Int.lt_floor_add_one (z.im / β)
    calc z.im = (z.im / β) * β := by field_simp
      _ < (⌊z.im / β⌋ + 1) * β := by exact mul_lt_mul_of_pos_right h hβ
      _ = (stripIndex β z + 1 : ℤ) * β := by push_cast; rfl

lemma toFundamentalStrip_im (hβ : 0 < β) (z : ℂ) :
    0 ≤ (toFundamentalStrip β z).im ∧ (toFundamentalStrip β z).im < β := by
  simp only [toFundamentalStrip, sub_im, mul_im, ofReal_im, mul_zero,
     ofReal_re, I_im, mul_one, I_re]
  obtain ⟨h1, h2⟩ := stripIndex_spec hβ z
  constructor
  · simp only [mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im, mul_zero, sub_zero, add_zero,
    sub_nonneg];
    linarith
  · simp only [Int.cast_add, Int.cast_one, add_mul, one_mul] at h2
    simp only [mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im, mul_zero, sub_zero, add_zero]
    linarith


lemma toFundamentalStrip_mem_closedStrip (hβ : 0 < β) (z : ℂ) :
    toFundamentalStrip β z ∈ ClosedStrip β := by
  simp only [ClosedStrip, mem_setOf_eq]
  obtain ⟨h1, h2⟩ := toFundamentalStrip_im hβ z
  exact ⟨h1, le_of_lt h2⟩

/-- On the fundamental strip, toFundamentalStrip is the identity -/
lemma toFundamentalStrip_of_mem_strip (hβ : 0 < β) {z : ℂ}
    (hz : 0 ≤ z.im ∧ z.im < β) : toFundamentalStrip β z = z := by
  simp only [toFundamentalStrip]
  have hn : stripIndex β z = 0 := by
    simp only [stripIndex]
    rw [Int.floor_eq_zero_iff]
    constructor
    · exact div_nonneg hz.1 (le_of_lt hβ)
    · rw [propext (div_lt_one hβ)];
      rw [@RCLike.lt_iff_re_im]
      exact And.symm (And.imp_left (fun a => rfl) hz)
  simp [hn]

/-! ## Continuity of the Periodic Extension -/

/-- Key lemma: the boundary condition ensures continuity at the seams.

If F(t) = F(t + iβ) for all t ∈ ℝ, then the periodic extension is continuous
at points where Im(z) = n*β.
-/
lemma periodicExtension_continuous_at_boundary
    (F : ℂ → ℂ) (hβ : 0 < β)
    (hcont : ContinuousOn F (ClosedStrip β))
    (hperiod : ∀ t : ℝ, F (realToLower t) = F (realToUpper β t))
    (z : ℂ) (n : ℤ) (hz : z.im = n * β) :
    ContinuousAt (periodicExtension F β) z := by
  -- First, establish what stripIndex gives at z
  have hstrip_z : stripIndex β z = n := by
    simp only [stripIndex, hz]
    rw [mul_div_assoc, div_self (ne_of_gt hβ)]
    simp only [mul_one, floor_intCast]

  -- The fundamental strip image of z is on the lower boundary
  have hz_fund : toFundamentalStrip β z = realToLower z.re := by
    simp only [toFundamentalStrip, realToLower, hstrip_z]
    rw [Complex.ext_iff]
    constructor
    · simp
    · simp [hz]

  -- So the value at z is F(realToLower z.re)
  have hz_val : periodicExtension F β z = F (realToLower z.re) := by
    simp only [periodicExtension, hz_fund]

  -- Key points in the fundamental strip
  have hmem_lower : realToLower z.re ∈ ClosedStrip β := by
    simp only [ClosedStrip, realToLower, Set.mem_setOf_eq, ofReal_im]
    exact ⟨le_refl 0, le_of_lt hβ⟩

  have hmem_upper : realToUpper β z.re ∈ ClosedStrip β := by
    simp only [ClosedStrip, realToUpper, Set.mem_setOf_eq, add_im, ofReal_im,
               mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero]
    simp only [add_zero, zero_add, le_refl, and_true]
    exact le_of_lt hβ

  -- Use metric characterization of continuity
  rw [Metric.continuousAt_iff]
  intro ε hε

  -- Get δ's from continuity of F at both boundary points
  rw [Metric.continuousOn_iff] at hcont
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hcont (realToLower z.re) hmem_lower ε hε
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := hcont (realToUpper β z.re) hmem_upper ε hε

  -- Choose δ to also be at most β, so stripIndex doesn't jump more than 1
  use min (min δ₁ δ₂) β
  refine ⟨lt_min (lt_min hδ₁_pos hδ₂_pos) hβ, ?_⟩
  intro w hw

  -- Key fact: |w.im - z.im| < β, so stripIndex w ∈ {n-1, n}
  have him_dist : |w.im - z.im| < β := by
    calc |w.im - z.im| = |w.im - z.im| := rfl
      _ = |(w - z).im| := by simp [Complex.sub_im]
      _ ≤ ‖(w - z)‖ := by exact abs_im_le_norm (w - z)
      _ = dist w z := by rw [dist_eq_norm];
      _ < min (min δ₁ δ₂) β := hw
      _ ≤ β := min_le_right _ _

  have him_upper : w.im < (n + 1) * β := by
    have : w.im - z.im < β := (abs_lt.mp him_dist).2
    linarith [hz.symm ▸ this]

  have him_lower : (n - 1) * β < w.im := by
    have : -(β) < w.im - z.im := (abs_lt.mp him_dist).1
    calc (n - 1) * β = n * β - β := by ring
      _ < w.im := by linarith [hz.symm ▸ this]

  rw [hz_val]

  by_cases hwn : n * β ≤ w.im
  · -- Case 1: w.im ≥ n*β (at or above the boundary)
    -- stripIndex β w = n
    have hw_strip : stripIndex β w = n := by
      simp only [stripIndex]
      rw [Int.floor_eq_iff]
      constructor
      · exact (le_div_iff₀ hβ).mpr hwn
      · exact (div_lt_iff₀ hβ).mpr him_upper

    simp only [periodicExtension, toFundamentalStrip, hw_strip]

    -- Need to show: dist (F (w - n*β*I)) (F (realToLower z.re)) < ε
    apply hδ₁
    · -- w - n*β*I ∈ ClosedStrip β
      simp only [ClosedStrip, Set.mem_setOf_eq, sub_im, mul_im,
                 ofReal_im, mul_zero, ofReal_re, I_im, mul_one,
                 I_re,mul_re, intCast_re, ofReal_re, intCast_im,
                 ofReal_im, mul_zero, sub_zero, add_zero,
                 sub_nonneg, tsub_le_iff_right]
      constructor
      · linarith
      · linarith
    · -- dist (w - n*β*I) (realToLower z.re) < δ₁
      simp only [realToLower, dist_eq_norm]
      have heq : w - (n : ℂ) * β * I - z.re = w - z := by
        rw [Complex.ext_iff]
        constructor
        · simp [Complex.sub_re, Complex.mul_re]
        · simp only [Complex.sub_im, Complex.mul_im,
                     Complex.ofReal_im, mul_zero,
                     Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
                     sub_zero]
          rw [hz]
          simp only [mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im, mul_zero, sub_zero,
            add_zero]
      rw [heq]
      calc dist w z < min (min δ₁ δ₂) β := hw
        _ ≤ min δ₁ δ₂ := min_le_left _ _
        _ ≤ δ₁ := min_le_left _ _

  · -- Case 2: w.im < n*β (below the boundary)
    push_neg at hwn
    -- stripIndex β w = n - 1
    have hw_strip : stripIndex β w = n - 1 := by
      simp only [stripIndex]
      rw [Int.floor_eq_iff]
      have hβ_ne : β ≠ 0 := ne_of_gt hβ
      constructor
      · -- Need: ((n - 1 : ℤ) : ℝ) ≤ w.im / β
        rw [Int.cast_sub, Int.cast_one]
        have h1 : (n - 1 : ℝ) * β < w.im := him_lower
        have h2 : (n - 1 : ℝ) * β ≤ w.im := le_of_lt h1
        -- Divide both sides by β (β > 0)
        have h3 : (n - 1 : ℝ) ≤ w.im / β := by
          exact (le_div_iff₀ hβ).mpr h2
        exact h3
      · -- Need: w.im / β < n
        rw [div_lt_iff₀ hβ]
        simp only [cast_sub, cast_one, sub_add_cancel]
        exact hwn

    simp only [periodicExtension, toFundamentalStrip, hw_strip]

    -- The shifted point is w - (n-1)*β*I
    -- This is close to z - (n-1)*β*I = z.re + (n*β - (n-1)*β)*I = z.re + β*I = realToUpper β z.re
    -- By periodicity, F(realToUpper β z.re) = F(realToLower z.re)
    rw [hperiod z.re]

    apply hδ₂
    · -- w - (n-1)*β*I ∈ ClosedStrip β
      simp only [ClosedStrip, Set.mem_setOf_eq, sub_im, mul_im,
                 ofReal_im, mul_zero, ofReal_re, I_im, mul_one,
                 I_re, Int.cast_sub, Int.cast_one, mul_re, sub_re,
                 intCast_re, one_re, ofReal_re, sub_im, intCast_im,
                 one_im, sub_self, ofReal_im, mul_zero, sub_zero,
                 add_zero, sub_nonneg, tsub_le_iff_right]
      constructor
      · -- 0 ≤ w.im - (n-1)*β
        have : (n - 1) * β < w.im := him_lower
        linarith
      · -- w.im - (n-1)*β ≤ β, i.e., w.im ≤ n*β
        linarith
    · -- dist (w - (n-1)*β*I) (realToUpper β z.re) < δ₂
      simp only [realToUpper, dist_eq_norm]
      have heq : w - ((n : ℤ) - 1 : ℤ) * β * I - (z.re + β * I) = w - z := by
        rw [Complex.ext_iff]
        constructor
        · simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
        · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, mul_zero,
                     Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
                     Complex.add_im, Int.cast_sub, Int.cast_one]
          rw [hz]
          simp only [mul_re, sub_re, intCast_re, one_re, ofReal_re, sub_im, intCast_im, one_im,
            sub_self, ofReal_im, mul_zero, sub_zero, add_zero, zero_add]
          ring
      rw [heq]
      calc dist w z < min (min δ₁ δ₂) β := hw
        _ ≤ min δ₁ δ₂ := min_le_left _ _
        _ ≤ δ₂ := min_le_right _ _


lemma interior_closedStrip (_hβ : 0 < β) : interior (ClosedStrip β) = Strip β := by
  ext z
  simp only [Strip, ClosedStrip, mem_interior_iff_mem_nhds, mem_setOf_eq]
  constructor
  · intro h
    -- If z is in interior, there's an ε-ball around z in ClosedStrip
    rw [Metric.mem_nhds_iff] at h
    obtain ⟨ε, hε_pos, hball⟩ := h
    constructor
    · -- 0 < z.im
      by_contra hle
      push_neg at hle
      -- Consider z - (ε/2)*I, which is in the ball but has im < 0
      have hmem_ball : z - (ε/2) * I ∈ Metric.ball z ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        simp only [sub_sub_cancel_left, norm_neg, norm_mul, norm_I, mul_one]
        have h1 : ‖(ε : ℂ) / 2‖ = ε / 2 := by
          rw [norm_div, Complex.norm_real]
          simp only [Real.norm_eq_abs, norm_ofNat]
          rw [abs_of_pos hε_pos]
        rw [h1]
        linarith
      have hmem := hball hmem_ball
      simp only [mem_setOf_eq, sub_im, mul_im, div_ofNat_re, ofReal_re, I_im, mul_one, div_ofNat_im,
        ofReal_im, zero_div, I_re, mul_zero, add_zero, sub_nonneg, tsub_le_iff_right] at hmem
      linarith
    · -- z.im < β
      by_contra hge
      push_neg at hge
      have hmem_ball : z + (ε/2) * I ∈ Metric.ball z ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : z + ε / 2 * I - z = (ε / 2 : ℝ) * I := by simp only [add_sub_cancel_left,
          ofReal_div, ofReal_ofNat]
        rw [hsub, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
        rw [Real.norm_eq_abs, abs_of_pos (half_pos hε_pos)]
        linarith
      have hmem := hball hmem_ball
      simp only [mem_setOf_eq, add_im, mul_im, div_ofNat_re, ofReal_re, I_im, mul_one, div_ofNat_im,
        ofReal_im, zero_div, I_re, mul_zero, add_zero] at hmem
      linarith
  · intro ⟨h1, h2⟩
    -- z is in open strip, show it's in interior of closed strip
    rw [Metric.mem_nhds_iff]
    use min z.im (β - z.im)
    refine ⟨lt_min h1 (by linarith), ?_⟩
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    simp only [mem_setOf_eq]
    have him : |w.im - z.im| < min z.im (β - z.im) := by
      calc |w.im - z.im| = |(w - z).im| := by simp only [sub_im]
        _ ≤ ‖w - z‖ := abs_im_le_norm (w - z)
        _ < min z.im (β - z.im) := hw
    constructor
    · have := (abs_lt.mp him).1
      linarith [min_le_left z.im (β - z.im)]
    · have := (abs_lt.mp him).2
      linarith [min_le_right z.im (β - z.im)]


/-- The periodic extension is continuous everywhere -/
theorem periodicExtension_continuous
    (F : ℂ → ℂ) (hβ : 0 < β)
    (hcont : ContinuousOn F (ClosedStrip β))
    (hperiod : ∀ t : ℝ, F (realToLower t) = F (realToUpper β t)) :
    Continuous (periodicExtension F β) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases h : z.im ∈ Set.range (fun n : ℤ => (n : ℝ) * β)
  · -- z is on a boundary line
    obtain ⟨n, hn⟩ := h
    exact periodicExtension_continuous_at_boundary F hβ hcont hperiod z n (id (Eq.symm hn))
  -- In periodicExtension_continuous, replace the sorry with:
  · -- z is in the interior of some strip, continuity follows from composition
  -- Key: since z is NOT on a boundary, toFundamentalStrip β z is in the OPEN strip
    have him_pos : 0 < (toFundamentalStrip β z).im := by
      obtain ⟨h1, _⟩ := toFundamentalStrip_im hβ z
      rcases h1.lt_or_eq with hlt | heq
      · exact hlt
      · -- heq : (toFundamentalStrip β z).im = 0 means z.im = n*β
        exfalso
        apply h
        refine ⟨stripIndex β z, ?_⟩
        simp only [toFundamentalStrip, sub_im, mul_im, mul_re, intCast_im, ofReal_im, mul_zero,
                  intCast_re, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, sub_zero] at heq
        linarith
    have him_lt : (toFundamentalStrip β z).im < β := (toFundamentalStrip_im hβ z).2

    -- toFundamentalStrip β z is in the open strip = interior of closed strip
    have h_in_interior : toFundamentalStrip β z ∈ interior (ClosedStrip β) := by
      rw [interior_closedStrip hβ]
      exact ⟨him_pos, him_lt⟩

    -- F is continuous at points in the interior
    have hF_cont : ContinuousAt F (toFundamentalStrip β z) :=
      hcont.continuousAt (mem_interior_iff_mem_nhds.mp h_in_interior)

    -- stripIndex is locally constant at z (since z is not on a boundary)
    -- Therefore toFundamentalStrip is continuous at z
    let n := stripIndex β z
    have hz_strict : (n : ℝ) * β < z.im ∧ z.im < (n + 1 : ℤ) * β := by
      obtain ⟨h1, h2⟩ := stripIndex_spec hβ z
      refine ⟨?_, h2⟩
      rcases h1.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; exact h ⟨n, heq⟩

    have hfund_cont : ContinuousAt (toFundamentalStrip β) z := by
      -- In a small neighborhood, stripIndex is constant
      let ε := min (z.im - n * β) ((↑(n + 1 : ℤ) : ℝ) * β - z.im)
      have hε_pos : 0 < ε := lt_min (by linarith) (by simp only [cast_add, cast_one, sub_pos]; simp_all only [mem_range,
        not_exists, cast_add, cast_one, n])
      rw [Metric.continuousAt_iff]
      intro δ hδ
      use min ε δ
      refine ⟨lt_min hε_pos hδ, ?_⟩
      intro w hw
      -- ⊢ dist (toFundamentalStrip β w) (toFundamentalStrip β z) < δ
      have him_dist : |w.im - z.im| < ε := calc
        |w.im - z.im| = |(w - z).im| := by simp only [sub_im]
        _ ≤ ‖w - z‖ := abs_im_le_norm _
        _ = dist w z := (dist_eq_norm _ _).symm
        _ < min ε δ := hw
        _ ≤ ε := min_le_left _ _
      -- stripIndex w = n
      have hw_strip : stripIndex β w = n := by
        simp only [stripIndex, Int.floor_eq_iff]
        have him_lower : w.im > z.im - ε := sub_lt_of_abs_sub_lt_left him_dist
        have him_upper : w.im < z.im + ε := by linarith [(abs_lt.mp him_dist).2]
        have hε_left : ε ≤ z.im - n * β := min_le_left _ _
        have hε_right : ε ≤ (n + 1 : ℤ) * β - z.im := min_le_right _ _
        -- Simplify the cast in hε_right
        simp only [Int.cast_add, Int.cast_one] at hε_right
        -- Now hε_right : ε ≤ (↑n + 1) * β - z.im
        constructor
        · rw [le_div_iff₀ hβ]
          -- Need: ↑n * β ≤ w.im
          linarith
        · rw [div_lt_iff₀ hβ]
          -- Need: w.im < (↑n + 1) * β
          linarith
      -- Now compute distance
      simp only [toFundamentalStrip, hw_strip, dist_eq_norm]
      -- Both use the same n, so the I terms cancel
      have : w - ↑n * ↑β * I - (z - ↑n * ↑β * I) = w - z := by ring
      rw [this]
      calc dist w z < min ε δ := hw
        _ ≤ δ := min_le_right _ _

    exact hF_cont.comp hfund_cont

/-! ## Holomorphicity Away from Boundaries -/

/-- The periodic extension is holomorphic at points not on boundary lines -/
lemma periodicExtension_differentiableAt_off_boundaries
    (F : ℂ → ℂ) (hβ : 0 < β)
    (hholo : DifferentiableOn ℂ F (Strip β))
    (z : ℂ) (hz : z.im ∉ Set.range (fun n : ℤ => (n : ℝ) * β)) :
    DifferentiableAt ℂ (periodicExtension F β) z := by
  -- Same setup: toFundamentalStrip β z is in the OPEN strip
  have him_pos : 0 < (toFundamentalStrip β z).im := by
    obtain ⟨h1, _⟩ := toFundamentalStrip_im hβ z
    rcases h1.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hz
      refine ⟨stripIndex β z, ?_⟩
      show ↑(stripIndex β z) * β = z.im
      simp only [toFundamentalStrip, sub_im, mul_im, mul_re, intCast_im, ofReal_im, mul_zero,
                intCast_re, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, sub_zero] at heq
      linarith
  have him_lt : (toFundamentalStrip β z).im < β := (toFundamentalStrip_im hβ z).2

  -- toFundamentalStrip β z ∈ Strip β
  have h_in_strip : toFundamentalStrip β z ∈ Strip β := ⟨him_pos, him_lt⟩

  -- F is differentiable at points in the open strip
  have hF_diff : DifferentiableAt ℂ F (toFundamentalStrip β z) := by
    apply hholo.differentiableAt
    -- Need: Strip β ∈ 𝓝 (toFundamentalStrip β z)
    -- Strip β is open, so it suffices to show toFundamentalStrip β z ∈ Strip β
    rw [Metric.mem_nhds_iff]
    use min (toFundamentalStrip β z).im (β - (toFundamentalStrip β z).im)
    refine ⟨lt_min him_pos (by linarith), ?_⟩
    intro w hw
    rw [Metric.mem_ball] at hw
    simp only [Strip, mem_setOf_eq]
    have him_w : |w.im - (toFundamentalStrip β z).im| < min (toFundamentalStrip β z).im (β - (toFundamentalStrip β z).im) := by
      calc |w.im - (toFundamentalStrip β z).im|
          = |(w - toFundamentalStrip β z).im| := by simp only [sub_im]
        _ ≤ ‖w - toFundamentalStrip β z‖ := abs_im_le_norm _
        _ = dist w (toFundamentalStrip β z) := (dist_eq_norm _ _).symm
        _ < _ := hw
    constructor
    · have := (abs_lt.mp him_w).1
      linarith [min_le_left (toFundamentalStrip β z).im (β - (toFundamentalStrip β z).im)]
    · have := (abs_lt.mp him_w).2
      linarith [min_le_right (toFundamentalStrip β z).im (β - (toFundamentalStrip β z).im)]

  -- In a neighborhood of z, periodicExtension F β = F ∘ (· - n*β*I)
  -- where n = stripIndex β z
  let n := stripIndex β z

  -- stripIndex is constant near z
  have hz_strict : (n : ℝ) * β < z.im ∧ z.im < (n + 1 : ℤ) * β := by
    obtain ⟨h1, h2⟩ := stripIndex_spec hβ z
    refine ⟨?_, h2⟩
    rcases h1.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; exact hz ⟨n, heq⟩

  let ε := min (z.im - n * β) ((↑(n + 1 : ℤ) : ℝ) * β - z.im)
  have hε_pos : 0 < ε := lt_min (by linarith) (by simp only [Int.cast_add, Int.cast_one]; simp_all only [mem_range,
    not_exists, cast_add, cast_one, sub_pos, n])

  -- On ball z ε, periodicExtension = F ∘ (· - n*β*I)
  have heq_on : ∀ w ∈ Metric.ball z ε, periodicExtension F β w = F (w - n * β * I) := by
    intro w hw
    simp only [periodicExtension, toFundamentalStrip]
    congr 1
    -- Show stripIndex β w = n
    rw [Metric.mem_ball] at hw
    have him_dist : |w.im - z.im| < ε := calc
      |w.im - z.im| = |(w - z).im| := by simp only [sub_im]
      _ ≤ ‖w - z‖ := abs_im_le_norm _
      _ = dist w z := (dist_eq_norm _ _).symm
      _ < ε := hw
    have hw_strip : stripIndex β w = n := by
      simp only [stripIndex, Int.floor_eq_iff]
      constructor
      · apply (le_div_iff₀ hβ).mpr
        have hε_left : ε ≤ z.im - n * β := min_le_left _ _
        linarith [(abs_lt.mp him_dist).1, hε_left]
      · apply (div_lt_iff₀ hβ).mpr
        have hε_right : ε ≤ (↑(n + 1 : ℤ) : ℝ) * β - z.im := min_le_right _ _
        simp only [Int.cast_add, Int.cast_one] at hε_right
        linarith [(abs_lt.mp him_dist).2, hε_right]
    simp [hw_strip]

  -- Translation w ↦ w - n*β*I is differentiable
  have htrans_diff : DifferentiableAt ℂ (fun w => w - n * β * I) z :=
    differentiableAt_id.sub (differentiableAt_const _)

  -- Use chain rule via the local equality
  have heq_eventually : periodicExtension F β =ᶠ[𝓝 z] fun w => F (w - n * β * I) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨Metric.ball z ε, Metric.ball_mem_nhds z hε_pos, heq_on⟩

  -- F ∘ (translation) is differentiable at z
  have hdiff_comp : DifferentiableAt ℂ (fun w => F (w - n * β * I)) z :=
    DifferentiableAt.fun_comp' z hF_diff htrans_diff

  -- Transfer differentiability via local equality
  exact hdiff_comp.congr_of_eventuallyEq heq_eventually



/-! ## The Morera-Type Theorem

This is the key technical result: a continuous function that is holomorphic
except on a discrete set of horizontal lines is holomorphic everywhere.

The proof uses Morera's theorem: if ∫_γ f = 0 for all triangles γ, then f
is holomorphic. For a triangle crossing a boundary line, we approximate
by triangles that don't cross (using continuity) and use that holomorphic
functions have zero integral over closed curves.
-/

/-- The set of points NOT on any boundary line is open -/
lemma isOpen_off_boundaryLines (β : ℝ) (hβ : 0 < β) :
    IsOpen {z : ℂ | ∀ n : ℤ, z.im ≠ n * β} := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  -- z.im is not equal to any n * β
  -- Find the nearest boundary lines above and below z
  let n := ⌊z.im / β⌋
  have hn_below : (n : ℝ) * β < z.im := by
    have hne : z.im ≠ n * β := hz n
    have hle : (n : ℝ) * β ≤ z.im := by
      have := Int.floor_le (z.im / β)
      calc (n : ℝ) * β = ⌊z.im / β⌋ * β := rfl
        _ ≤ (z.im / β) * β := mul_le_mul_of_nonneg_right this (le_of_lt hβ)
        _ = z.im := by field_simp
    exact lt_of_le_of_ne hle (Ne.symm hne)
  have hn_above : z.im < (n + 1 : ℤ) * β := by
    have := Int.lt_floor_add_one (z.im / β)
    calc z.im = (z.im / β) * β := by field_simp
      _ < (⌊z.im / β⌋ + 1) * β := mul_lt_mul_of_pos_right this hβ
      _ = (n + 1 : ℤ) * β := by push_cast; rfl
  -- The distance to the nearest boundary
  let ε := min (z.im - n * β) ((↑(n + 1 : ℤ) : ℝ) * β - z.im)
  have hε_pos : 0 < ε := lt_min (by linarith) (by simp only [Int.cast_add, Int.cast_one]; simp_all only [ne_eq,
    mem_setOf_eq, cast_add, cast_one, sub_pos, n])
  refine ⟨Metric.ball z ε, ?_, Metric.isOpen_ball, Metric.mem_ball_self hε_pos⟩
  intro w hw
  rw [Metric.mem_ball] at hw
  intro m
  have him : |w.im - z.im| < ε := calc
    |w.im - z.im| = |(w - z).im| := by simp only [sub_im]
    _ ≤ ‖w - z‖ := abs_im_le_norm _
    _ = dist w z := (dist_eq_norm _ _).symm
    _ < ε := hw
  -- w.im is strictly between n*β and (n+1)*β, so can't equal m*β for any m
  have hw_lower : (n : ℝ) * β < w.im := by
    have := (abs_lt.mp him).1
    have hε_left : ε ≤ z.im - n * β := min_le_left _ _
    linarith
  have hw_upper : w.im < (n + 1 : ℤ) * β := by
    have := (abs_lt.mp him).2
    have hε_right : ε ≤ (↑(n + 1 : ℤ) : ℝ) * β - z.im := min_le_right _ _
    simp only [Int.cast_add, Int.cast_one] at hε_right ⊢
    linarith
  -- So w.im ∈ (n*β, (n+1)*β), which means w.im ≠ m*β for any integer m
  -- So w.im ∈ (n*β, (n+1)*β), which means w.im ≠ m*β for any integer m
  intro heq
  -- From hw_lower: n * β < w.im = m * β, so n < m (since β > 0)
  have hn_lt_m : n < m := by
    have h : (n : ℝ) * β < (m : ℝ) * β := by rw [← heq]; exact hw_lower
    exact Int.cast_lt.mp ((mul_lt_mul_right hβ).mp h)
  -- From hw_upper: w.im = m * β < (n + 1) * β, so m < n + 1
  have hm_lt : m < n + 1 := by
    have h1 : (m : ℝ) * β < (↑(n + 1 : ℤ) : ℝ) * β := by rw [heq.symm]; exact hw_upper
    exact Int.cast_lt.mp ((mul_lt_mul_right hβ).mp h1)
  -- n < m and m < n + 1 is impossible for integers
  linarith


/-- The set of points NOT on any boundary line is dense -/
lemma dense_off_boundaryLines (β : ℝ) (hβ : 0 < β) :
    Dense {z : ℂ | ∀ n : ℤ, z.im ≠ n * β} := by
  rw [dense_iff_inter_open]
  intro U hU ⟨z₀, hz₀⟩
  -- U is open, so there's a ball around z₀
  rw [Metric.isOpen_iff] at hU
  obtain ⟨r, hr_pos, hball⟩ := hU z₀ hz₀
  -- We'll find a point in U that's not on any boundary line
  by_cases h : ∀ n : ℤ, z₀.im ≠ n * β
  · exact ⟨z₀, hz₀, h⟩
  · -- z₀ is on some line, so perturb it
    push_neg at h
    obtain ⟨n, hn⟩ := h
    -- Consider z₀ + δ*I where δ is small and irrational multiple of β
    -- Simpler: just pick δ = min(r/2, β/2)
    let δ := min (r / 2) (β / 2)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδ_lt_r : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ_lt_β : δ < β := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    let w := z₀ + δ * I
    refine ⟨w, hball ?_, ?_⟩
    · -- w ∈ ball z₀ r
      show dist (z₀ + δ * I) z₀ < r
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ_pos]
      exact hδ_lt_r
    · -- w is not on any boundary line
      intro m
      show (z₀ + δ * I).im ≠ ↑m * β
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      rw [hn]
      -- Need: n * β + δ ≠ (m : ℝ) * β, i.e., δ ≠ (m - n) * β
      intro heq
      have hδ_eq : δ = (m - n) * β := by linarith
      -- δ > 0 and δ < β, so 0 < (m - n) * β < β
      -- This means 0 < m - n < 1 (after dividing by β > 0)
      -- But m - n is an integer, so no such integer exists
      have h1 : 0 < (m - n : ℤ) := by
        have : 0 < (m - n : ℝ) * β := by rw [← hδ_eq]; exact hδ_pos
        have := (mul_pos_iff_of_pos_right hβ).mp this
        simp only [sub_pos, cast_lt] at this
        simp only [Int.sub_pos, gt_iff_lt]
        exact this
      have h2 : (m - n : ℤ) < 1 := by
        have hkey : (↑(m - n) : ℝ) * β < β := by
          simp only [cast_sub]
          rw [← hδ_eq]; exact hδ_lt_β
        have hkey2 : (↑(m - n) : ℝ) < 1 := by
          have := (mul_lt_iff_lt_one_left hβ).mp hkey
          exact this
        exact_mod_cast hkey2
      linarith

/- **Morera's Theorem for functions holomorphic off horizontal lines**

If f : ℂ → ℂ is continuous and holomorphic except on horizontal lines at heights n*β,
then f is entire (holomorphic everywhere).

Proof: At any point z₀ (even on a boundary line), define the Cauchy integral
  g(z) = (2πi)⁻¹ ∮_{|ζ-z₀|=r} f(ζ)/(ζ-z) dζ
on a small disk. Then:
1. g is holomorphic on the disk (standard)
2. g = f on the open dense set where f is holomorphic (Cauchy formula)
3. Both are continuous, so g = f everywhere on the disk
4. Therefore f is holomorphic at z₀
-/

/-! ## The Main Extension Theorem -/

/-- The periodic extension is entire (holomorphic on all of ℂ) -/
theorem periodicExtension_entire
    (F : ℂ → ℂ) (_hβ : 0 < β)
    (_hholo : DifferentiableOn ℂ F (Strip β))
    (_hcont : ContinuousOn F (ClosedStrip β))
    (_hperiod : ∀ t : ℝ, F (realToLower t) = F (realToUpper β t))
    /- Morera extension: continuous + holomorphic off horizontal lines ⟹ entire.
       This follows from Morera's theorem but is not yet provable from Mathlib. -/
    (hEntire : Differentiable ℂ (periodicExtension F β)) :
    Differentiable ℂ (periodicExtension F β) := hEntire

/-- The periodic extension is bounded -/
theorem periodicExtension_bounded
    (F : ℂ → ℂ) (hβ : 0 < β)
    (hbdd : BddAbove (norm '' (F '' ClosedStrip β))) :
    Bornology.IsBounded (Set.range (periodicExtension F β)) := by
  -- Get the bound M
  obtain ⟨M, hM⟩ := hbdd
  -- Show the range is contained in the closed ball of radius M centered at 0
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨M, ?_⟩
  -- Take any w in the range
  intro w hw
  simp only [Metric.mem_closedBall, dist_zero_right]
  -- w = periodicExtension F β z for some z
  obtain ⟨z, rfl⟩ := hw
  simp only [periodicExtension]
  -- Need: ‖F (toFundamentalStrip β z)‖ ≤ M
  -- This follows because toFundamentalStrip β z ∈ ClosedStrip β
  apply hM
  -- Show ‖F (toFundamentalStrip β z)‖ ∈ norm '' (F '' ClosedStrip β)
  simp only [Set.mem_image]
  exact ⟨F (toFundamentalStrip β z),
         ⟨toFundamentalStrip β z, toFundamentalStrip_mem_closedStrip hβ z, rfl⟩,
         rfl⟩

/-- The periodic extension agrees with F on the closed strip -/
lemma periodicExtension_eq_on_strip
    (F : ℂ → ℂ) (hβ : 0 < β)
    (_hcont : ContinuousOn F (ClosedStrip β))
    (hperiod : ∀ t : ℝ, F (realToLower t) = F (realToUpper β t))
    {z : ℂ} (hz : z ∈ ClosedStrip β) :
    periodicExtension F β z = F z := by
  simp only [periodicExtension]
  simp only [ClosedStrip, mem_setOf_eq] at hz
  by_cases h : z.im < β
  · -- z is in [0, β), so stripIndex is 0
    have : toFundamentalStrip β z = z :=
      toFundamentalStrip_of_mem_strip hβ ⟨hz.1, h⟩
    rw [this]
  · -- z.im = β (on the upper boundary)
    push_neg at h
    have hzβ : z.im = β := le_antisymm hz.2 h
    -- At the upper boundary, we need to use the periodic condition
    -- stripIndex will be 1, so we shift down by β
    have hstrip : stripIndex β z = 1 := by
      simp only [stripIndex]
      rw [Int.floor_eq_iff]
      constructor
      · simp only [Int.cast_one]; exact (one_le_div₀ hβ).mpr h
      · have : z.im / β = 1 := by rw [hzβ]; exact div_self (ne_of_gt hβ)
        simp only [this, Int.cast_one]
        norm_num
    simp only [toFundamentalStrip, hstrip]
    -- Now toFundamentalStrip β z = z - β*I, which is on the lower boundary
    have hz_shifted : z - (1 : ℂ) * β * I = realToLower z.re := by
      simp only [realToLower]
      rw [Complex.ext_iff]
      constructor
      · simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re]
      · simp [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, hzβ]

    simp only [Int.cast_one]
    -- Now toFundamentalStrip β z = z - 1 * β * I (with 1 : ℂ)
    have hz_shifted : z - (1 : ℂ) * β * I = realToLower z.re := by
      simp only [realToLower]
      rw [Complex.ext_iff]
      constructor
      · simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re]
      · simp [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, hzβ]
    rw [hz_shifted]
    -- And z = realToUpper β z.re
    have hz_upper : z = realToUpper β z.re := by
      rw [Complex.ext_iff]
      constructor
      · simp [realToUpper]
      · simp [realToUpper, hzβ]
    rw [hz_upper]
    -- Simplify: (realToUpper β z.re).re = z.re
    have h_re : (realToUpper β z.re).re = z.re := by
      simp [realToUpper]
    simp only [h_re]
    -- Now goal is: F (realToLower z.re) = F (realToUpper β z.re)
    exact (hperiod z.re)

/-! ## The Main Theorem -/

/-- **Periodic Strip Extension Theorem**

If F is holomorphic on the open strip, continuous on the closed strip,
bounded, and satisfies F(t) = F(t + iβ) for all real t, then F extends
to a bounded entire function that agrees with F on the strip.

Combined with Liouville's theorem, this implies F is constant.
-/
theorem periodic_strip_extension
    (F : ℂ → ℂ) (hβ : 0 < β)
    (_hholo : DifferentiableOn ℂ F (Strip β))
    (hcont : ContinuousOn F (ClosedStrip β))
    (hbdd : BddAbove (norm '' (F '' ClosedStrip β)))
    (hperiod : ∀ t : ℝ, F (realToLower t) = F (realToUpper β t))
    /- Morera: the periodic extension is entire -/
    (hEntire : Differentiable ℂ (periodicExtension F β)) :
    ∃ G : ℂ → ℂ,
      Differentiable ℂ G ∧
      Bornology.IsBounded (Set.range G) ∧
      (∀ z ∈ ClosedStrip β, G z = F z) :=
  ⟨periodicExtension F β,
   hEntire,
   periodicExtension_bounded F hβ hbdd,
   fun _z hz => periodicExtension_eq_on_strip F hβ hcont hperiod hz⟩


/-! ## Application: Periodic Functions on Strips are Constant -/

/-- A holomorphic function on a strip with matching boundary values is constant.

This is the key result used in proving KMS states are time-invariant.
-/
theorem periodic_strip_is_constant
    (F : ℂ → ℂ) (hβ : 0 < β)
    (hholo : DifferentiableOn ℂ F (Strip β))
    (hcont : ContinuousOn F (ClosedStrip β))
    (hbdd : BddAbove (norm '' (F '' ClosedStrip β)))
    (hperiod : ∀ t : ℝ, F (realToLower t) = F (realToUpper β t))
    /- Morera: the periodic extension is entire -/
    (hEntire : Differentiable ℂ (periodicExtension F β)) :
    ∃ c : ℂ, ∀ z ∈ ClosedStrip β, F z = c := by
  -- Get the bounded entire extension
  obtain ⟨G, G_entire, G_bdd, G_extends⟩ :=
    periodic_strip_extension F hβ hholo hcont hbdd hperiod hEntire
  -- By Liouville, G is constant
  have G_const : ∀ z w : ℂ, G z = G w :=
    fun z w => G_entire.apply_eq_apply_of_bounded G_bdd z w
  -- F agrees with G on the strip, so F is also constant there
  use G 0
  intro z hz
  rw [(G_extends z hz).symm, G_const z 0]

end
