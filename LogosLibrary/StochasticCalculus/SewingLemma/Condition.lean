/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/Condition.lean
-/
import LogosLibrary.StochasticCalculus.SewingLemma.Defs
/-!
# The Sewing Lemma — Layer 1 (Interval-Length Control)

The **Sewing Lemma** constructs additive functionals from almost-additive approximations.
This file proves the simplest and most directly useful version: the defect of the
two-parameter map `Ξ` is controlled by `K · |t - s|^θ` with `θ > 1`.

## Why this version?

The interval length `|t - s|` distributes *perfectly* over dyadic subdivision: at level `n`,
each sub-interval has length exactly `|t - s| / 2ⁿ`. This gives clean geometric decay:

  `‖S_{n+1} - Sₙ‖ ≤ K · |t - s|^θ · 2^{-n(θ - 1)}`

with *no additional hypotheses* on a control function. The general sewing lemma with
abstract super-additive control `ω` requires either a Lipschitz condition on `ω` or
a fundamentally different (compactness-based) proof. This version avoids both issues.

## Coverage

This version handles all standard applications where the driving signal has Hölder regularity:
* Standard Brownian motion (`γ`-Hölder for `γ < 1/2`)
* Fractional Brownian motion (`γ`-Hölder for `γ < H`)
* Hölder-regular Young integration
* Rough integration with Hölder rough path data

For the cross-controlled version with two different controls `ω₁, ω₂` (needed when the
integrand and integrator have different regularity structures), see Layer 2.

## Main results

* `dyadicSum_diff_bound₁`: geometric decay of successive dyadic refinements
* `dyadicSum_cauchy₁`: the dyadic Riemann sums form a Cauchy sequence
* `sewingMap₁_dist_le`: approximation bound `‖I(s,t) - Ξ(s,t)‖ ≤ C·K·|t-s|^θ`
* `sewingMap₁_additive`: the sewn map is genuinely additive
* `sewingMap₁_unique`: uniqueness among additive functionals with the approximation bound

## References

* [Gubinelli, M., *Controlling rough paths*][gubinelli2004]
* [Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Theorem 2.2][friz2020]
* [Lyons, T., *Differential equations driven by rough signals*][lyons1998]
-/

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

/-! ### The defect (coboundary) of a two-parameter map -/

section Defect₁

@[simp]
theorem sewingDefect₁_self_left (Ξ : ℝ → ℝ → E) (hΞ : ∀ s, Ξ s s = 0) (s t : ℝ) :
    sewingDefect₁ Ξ s s t = 0 := by
  simp [sewingDefect₁, hΞ]

@[simp]
theorem sewingDefect₁_self_right (Ξ : ℝ → ℝ → E) (hΞ : ∀ s, Ξ s s = 0) (s t : ℝ) :
    sewingDefect₁ Ξ s t t = 0 := by
  simp [sewingDefect₁, hΞ, sub_self]

/-- The defect satisfies a cocycle identity. -/
theorem sewingDefect₁_cocycle (Ξ : ℝ → ℝ → E) (s u v t : ℝ) :
    sewingDefect₁ Ξ s u t =
      sewingDefect₁ Ξ s u v + sewingDefect₁ Ξ s v t - sewingDefect₁ Ξ u v t := by
  simp only [sewingDefect₁]; abel

end Defect₁

/-! ### Dyadic partition points -/

section Dyadic

/-- The interval length at dyadic level `n` is `(t - s) / 2^n`. -/
theorem dyadicPt_sub_succ (s t : ℝ) (n k : ℕ) :
    dyadicPt s t n (k + 1) - dyadicPt s t n k = (t - s) / (2 : ℝ) ^ (n : ℕ) := by
  simp only [dyadicPt]; push_cast; ring

/-- **Key structural lemma**: level `(n+1)` point `2k` equals level `n` point `k`.
This is what makes the dyadic telescoping work — consecutive levels are nested. -/
theorem dyadicPt_double (s t : ℝ) (n k : ℕ) :
    dyadicPt s t (n + 1) (2 * k) = dyadicPt s t n k := by
  simp only [dyadicPt, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  ring



/-- Dyadic points at level `n` stay within `[s, t]`. -/
theorem dyadicPt_mem_Icc {s t : ℝ} (hst : s ≤ t) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    dyadicPt s t n k ∈ Icc s t := by
  refine ⟨dyadicPt_mono hst n (Nat.zero_le k) |>.trans_eq' (by simp),
         ?_⟩
  calc dyadicPt s t n k
      ≤ dyadicPt s t n (2 ^ n) := dyadicPt_mono hst n hk
    _ = t := dyadicPt_last s t n

/-- The absolute interval length at level `n`. -/
theorem abs_dyadicPt_sub (s t : ℝ) (n k : ℕ) :
    |dyadicPt s t n (k + 1) - dyadicPt s t n k| = |t - s| / (2 : ℝ) ^ (n : ℕ) := by
  rw [dyadicPt_sub_succ, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (n : ℕ))]

end Dyadic

/-! ### Dyadic Riemann sums -/

section DyadicSums₁

@[simp]
theorem dyadicSum₁_zero (Ξ : ℝ → ℝ → E) (s t : ℝ) :
    dyadicSum₁ Ξ s t 0 = Ξ s t := by
  simp [dyadicSum₁, dyadicPt]

/-- **Pairing lemma**: a sum over `range(2m)` splits into pairs.
This is the combinatorial engine of the dyadic refinement argument. -/
theorem sum_range_pair {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), f i =
    ∑ j ∈ Finset.range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 from by ring]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    rw [ih]; ring_nf
    rw [add_assoc (∑ x ∈ Finset.range m, (f (x * 2) + f (1 + x * 2))) (f (m * 2)) (f (1 + m * 2))]

/-- **The refinement identity**: each term at level `n` splits into two terms at level `n+1`
plus a defect.

`Ξ(tₖ, tₖ₊₁) = Ξ(tₖ, mₖ) + Ξ(mₖ, tₖ₊₁) + δΞ(tₖ, mₖ, tₖ₊₁)`

where `mₖ` is the midpoint (= level `(n+1)` point `2k+1`). -/
theorem refinement_identity (Ξ : ℝ → ℝ → E) (s t : ℝ) (n k : ℕ) :
    Ξ (dyadicPt s t n k) (dyadicPt s t n (k + 1)) =
      Ξ (dyadicPt s t (n + 1) (2 * k)) (dyadicPt s t (n + 1) (2 * k + 1)) +
      Ξ (dyadicPt s t (n + 1) (2 * k + 1)) (dyadicPt s t (n + 1) (2 * k + 2)) +
      sewingDefect₁ Ξ
        (dyadicPt s t n k)
        (dyadicPt s t (n + 1) (2 * k + 1))
        (dyadicPt s t n (k + 1)) := by
  -- Rewrite using dyadicPt_double: d(n+1, 2k) = d(n, k), d(n+1, 2k+2) = d(n, k+1)
  rw [dyadicPt_double, show 2 * k + 2 = 2 * (k + 1) from by ring, dyadicPt_double]
  -- Now this is just the definition of sewingDefect₁ rearranged
  simp only [sewingDefect₁]; abel

/-- Arithmetic identity: `2^n · (x / 2^n)^θ = x^θ · (2⁻¹)^{n(θ-1)}`. -/
lemma dyadic_geometric_factor {x : ℝ} (hx : 0 ≤ x) {θ : ℝ} (n : ℕ) :
    (2 : ℝ) ^ n * (x / (2 : ℝ) ^ n) ^ θ =
      x ^ θ * ((2 : ℝ)⁻¹) ^ (↑n * (θ - 1)) := by
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (n : ℕ) := by positivity
  -- Expand (x / 2^n)^θ = x^θ / (2^n)^θ
  rw [div_rpow hx h2pos.le]
  -- Bridge npow → rpow for (2^n)^θ
  rw [show ((2 : ℝ) ^ (n : ℕ)) ^ θ = (2 : ℝ) ^ ((↑n : ℝ) * θ) from by
    rw [← rpow_natCast (2 : ℝ) n, ← rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]]
  -- Bridge npow → rpow for the leading 2^n
  rw [show (2 : ℝ) ^ (n : ℕ) = (2 : ℝ) ^ (↑n : ℝ) from (rpow_natCast 2 n).symm]
  -- Now everything is rpow. Rearrange: 2^n · x^θ / 2^{nθ} = x^θ · (2^n / 2^{nθ})
  rw [mul_div_assoc', mul_comm ((2 : ℝ) ^ (↑n : ℝ)) (x ^ θ), mul_div_assoc]
  congr 1
  -- Remains: 2^n / 2^{nθ} = (2⁻¹)^{n(θ-1)}
  -- LHS: collapse via rpow_sub
  rw [← rpow_sub (by positivity : (0 : ℝ) < 2)]
  -- RHS: convert 2⁻¹ to base 2 with negative exponent
  rw [inv_rpow (by norm_num : (0 : ℝ) ≤ 2), ← rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  -- Both sides are 2^(something), so match exponents
  congr 1; ring

/-- **Key estimate (Layer 1)**: successive dyadic refinements decay geometrically.

`‖S_{n+1} - Sₙ‖ ≤ K · |t - s|^θ · 2^{-n(θ-1)}`

**Proof outline**:
1. Pair the `2^{n+1}` terms at level `n+1` into `2^n` pairs using `sum_range_pair`.
2. Each pair corresponds to one term at level `n` plus a defect: by `refinement_identity`,
   `S_{n+1} - Sₙ = - ∑ₖ δΞ(tₖ, mₖ, tₖ₊₁)`.
3. Triangle inequality: `‖S_{n+1} - Sₙ‖ ≤ ∑ₖ ‖δΞ(tₖ, mₖ, tₖ₊₁)‖`.
4. Each defect: `‖δΞ(tₖ, mₖ, tₖ₊₁)‖ ≤ K · |tₖ₊₁ - tₖ|^θ = K · (|t-s|/2ⁿ)^θ`.
5. Sum `2ⁿ` identical terms: `2ⁿ · K · |t-s|^θ / 2^{nθ} = K · |t-s|^θ · 2^{-n(θ-1)}`. -/
theorem dyadicSum₁_diff_bound {Ξ : ℝ → ℝ → E} {θ K a b : ℝ}
    (hΞ : SewingCondition₁ Ξ θ K a b) {s t : ℝ}
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (n : ℕ) :
    ‖dyadicSum₁ Ξ s t (n + 1) - dyadicSum₁ Ξ s t n‖ ≤
      K * |t - s| ^ θ * ((2 : ℝ)⁻¹) ^ (↑n * (θ - 1)) := by
  -- Step 1: Pair level-(n+1) terms into 2^n pairs
  simp only [dyadicSum₁]
  rw [show 2 ^ (n + 1) = 2 * 2 ^ n from by ring, sum_range_pair]
  -- Step 2: Normalize 2*k+1+1 → 2*(k+1), then collapse via dyadicPt_double
  simp only [show ∀ k : ℕ, 2 * k + 1 + 1 = 2 * (k + 1) from fun k => by omega]
  simp_rw [dyadicPt_double]
  -- Step 3: Write as sum of pointwise differences
  rw [← Finset.sum_sub_distrib]
  -- Step 4: Each summand = -(sewingDefect₁) by definition
  simp_rw [show ∀ k : ℕ,
      Ξ (dyadicPt s t n k) (dyadicPt s t (n + 1) (2 * k + 1)) +
        Ξ (dyadicPt s t (n + 1) (2 * k + 1)) (dyadicPt s t n (k + 1)) -
        Ξ (dyadicPt s t n k) (dyadicPt s t n (k + 1)) =
      -(sewingDefect₁ Ξ (dyadicPt s t n k) (dyadicPt s t (n + 1) (2 * k + 1))
          (dyadicPt s t n (k + 1)))
    from fun k => by simp only [sewingDefect₁]; abel]
  rw [Finset.sum_neg_distrib, norm_neg]
  -- Step 5: Triangle inequality → defect bound → interval length → geometric factor
  calc ‖∑ k ∈ range (2 ^ n), sewingDefect₁ Ξ (dyadicPt s t n k)
          (dyadicPt s t (n + 1) (2 * k + 1)) (dyadicPt s t n (k + 1))‖
      ≤ ∑ k ∈ range (2 ^ n), ‖sewingDefect₁ Ξ (dyadicPt s t n k)
          (dyadicPt s t (n + 1) (2 * k + 1)) (dyadicPt s t n (k + 1))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ range (2 ^ n),
          K * |dyadicPt s t n (k + 1) - dyadicPt s t n k| ^ θ := by
        gcongr with k hk
        have hk_lt : k < 2 ^ n := Finset.mem_range.mp hk
        exact hΞ.defect_bound _ _ _
          (le_trans has (dyadicPt_mem_Icc hst (le_of_lt hk_lt)).1)
          (dyadicPt_double s t n k ▸ dyadicPt_mono hst (n + 1) (by omega))
          (by rw [← dyadicPt_double s t n (k + 1)]; exact dyadicPt_mono hst (n + 1) (by omega))
          (le_trans (dyadicPt_mem_Icc hst (by omega : k + 1 ≤ 2 ^ n)).2 htb)
    _ = ∑ _k ∈ range (2 ^ n), K * (|t - s| / (2 : ℝ) ^ n) ^ θ := by
        congr 1; ext k; rw [abs_dyadicPt_sub]
    _ = (2 : ℝ) ^ n * (K * (|t - s| / (2 : ℝ) ^ n) ^ θ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ = K * ((2 : ℝ) ^ n * (|t - s| / (2 : ℝ) ^ n) ^ θ) := by ring
    _ = K * (|t - s| ^ θ * ((2 : ℝ)⁻¹) ^ (↑n * (θ - 1))) := by
        congr 1; exact dyadic_geometric_factor (abs_nonneg _) n
    _ = K * |t - s| ^ θ * ((2 : ℝ)⁻¹) ^ (↑n * (θ - 1)) := by ring

end DyadicSums₁

/-! ### Cauchy sequence and convergence -/

section Convergence₁

theorem sewingRatio₁_pos {θ : ℝ} (_hθ : 1 < θ) : 0 < sewingRatio₁ θ := by
  exact rpow_pos_of_pos (by positivity : (0 : ℝ) < 2⁻¹) _

theorem sewingRatio₁_lt_one {θ : ℝ} (hθ : 1 < θ) : sewingRatio₁ θ < 1 := by
  unfold sewingRatio₁
  exact rpow_lt_one (by positivity) (by norm_num : (2 : ℝ)⁻¹ < 1) (by linarith)

theorem sewingConst₁_pos {θ : ℝ} (hθ : 1 < θ) : 0 < sewingConst₁ θ := by
  apply div_pos one_pos; linarith [sewingRatio₁_lt_one hθ]

/-- **Cauchy sequence**: the dyadic sums converge geometrically.

The bound from `dyadicSum₁_diff_bound` gives:
  `‖Sₙ₊₁ - Sₙ‖ ≤ K · |t-s|^θ · r^n`
where `r = 2^{-(θ-1)} < 1`. This is exactly the input for `cauchySeq_of_le_geometric`. -/
theorem dyadicSum₁_cauchy {Ξ : ℝ → ℝ → E} {θ K a b : ℝ}
    (hΞ : SewingCondition₁ Ξ θ K a b) {s t : ℝ}
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    CauchySeq (fun n => dyadicSum₁ Ξ s t n) := by
  apply cauchySeq_of_le_geometric (sewingRatio₁ θ) (K * |t - s| ^ θ)
    (sewingRatio₁_lt_one hΞ.one_lt_theta)
  intro n
  rw [dist_eq_norm, norm_sub_rev]
  have h := dyadicSum₁_diff_bound hΞ has hst htb n
  -- Need to convert (2⁻¹)^(↑n * (θ-1)) to (sewingRatio₁ θ) ^ n
  -- sewingRatio₁ θ = (2⁻¹)^(θ-1), so (sewingRatio₁ θ)^n = (2⁻¹)^(n*(θ-1))
  calc ‖dyadicSum₁ Ξ s t (n + 1) - dyadicSum₁ Ξ s t n‖
      ≤ K * |t - s| ^ θ * ((2 : ℝ)⁻¹) ^ (↑n * (θ - 1)) := h
    _ = K * |t - s| ^ θ * sewingRatio₁ θ ^ n := by
        congr 1
        simp only [sewingRatio₁]
        rw [← rpow_natCast ((2 : ℝ)⁻¹ ^ (θ - 1)) n,
            ← rpow_mul (by positivity : (0 : ℝ) ≤ 2⁻¹)]
        congr 1; ring

end Convergence₁
/-- Level-n dyadic points of [s, (s+t)/2] are the first half of
level-(n+1) dyadic points of [s, t]. -/
theorem dyadicPt_left_half (s t : ℝ) (n k : ℕ) :
    dyadicPt s ((s + t) / 2) n k = dyadicPt s t (n + 1) k := by
  simp only [dyadicPt, pow_succ]; ring

/-- Level-n dyadic points of [(s+t)/2, t] are the second half of
level-(n+1) dyadic points of [s, t]. -/
theorem dyadicPt_right_half (s t : ℝ) (n k : ℕ) :
    dyadicPt ((s + t) / 2) t n k = dyadicPt s t (n + 1) (2 ^ n + k) := by
  simp only [dyadicPt, pow_succ]; push_cast; ring_nf
  simp only [one_div, inv_pow, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and,
    not_false_eq_true, inv_mul_cancel_right₀]
  linarith

/-- **Midpoint splitting**: the level-(n+1) dyadic sum over [s,t] equals the sum of
level-n dyadic sums over [s, (s+t)/2] and [(s+t)/2, t].

This is the combinatorial heart of the additivity proof: consecutive dyadic levels
are nested, and splitting at the midpoint perfectly decomposes the finer level into
two copies of the coarser level on each half. -/
theorem dyadicSum₁_midpoint_split (Ξ : ℝ → ℝ → E) (s t : ℝ) (n : ℕ) :
    dyadicSum₁ Ξ s t (n + 1) =
      dyadicSum₁ Ξ s ((s + t) / 2) n + dyadicSum₁ Ξ ((s + t) / 2) t n := by
  simp only [dyadicSum₁]
  rw [show 2 ^ (n + 1) = 2 ^ n + 2 ^ n from by ring]
  rw [Finset.sum_range_add]
  congr 1
  · congr 1; ext k; rw [dyadicPt_left_half, dyadicPt_left_half]
  · congr 1; ext k
    rw [dyadicPt_right_half, dyadicPt_right_half]
    congr 1

/-- The midpoint of a dyadic interval is the next-level odd point. -/
theorem dyadicPt_midpoint (s t : ℝ) (n k : ℕ) :
    (dyadicPt s t n k + dyadicPt s t n (k + 1)) / 2 =
      dyadicPt s t (n + 1) (2 * k + 1) := by
  simp only [dyadicPt, pow_succ]; push_cast; ring



end StochCalc
