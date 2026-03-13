/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerOne/Map.lean
-/
import LogosLibrary.StochasticCalculus.SewingLemma.Condition

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

/-! ### The sewn map -/
section SewnMap₁

/-- The sewn map vanishes on the diagonal: `I(s, s) = 0`. -/
theorem sewingMap₁_diag [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {θ K a b : ℝ}
    (hΞ : SewingCondition₁ Ξ θ K a b) {s : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    sewingMap₁ Ξ θ K a b hΞ s s = 0 := by
  unfold sewingMap₁
  rw [dif_pos ⟨has, le_refl s, hsb⟩]
  have hconst : ∀ n, dyadicSum₁ Ξ s s n = 0 := by
    intro n
    simp only [dyadicSum₁, dyadicPt, sub_self, mul_zero, zero_div, add_zero]
    simp [hΞ.vanish_diag]
  simp_rw [hconst]
  exact tendsto_const_nhds.limUnder_eq

/-- **Approximation bound**: the sewn map is close to `Ξ`.

`‖I(s,t) - Ξ(s,t)‖ ≤ K · sewingConst₁(θ) · |t - s|^θ`

**Proof**: `I(s,t) - Ξ(s,t) = lim Sₙ - S₀ = ∑_{n=0}^∞ (Sₙ₊₁ - Sₙ)`.
Each term bounded by `K · |t-s|^θ · r^n`. Sum the geometric series. -/
theorem sewingMap₁_dist_le [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {θ K a b : ℝ}
    (hΞ : SewingCondition₁ Ξ θ K a b) {s t : ℝ}
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖sewingMap₁ Ξ θ K a b hΞ s t - Ξ s t‖ ≤
      K * sewingConst₁ θ * |t - s| ^ θ := by
  set S := fun n => dyadicSum₁ Ξ s t n
  -- Unfold sewingMap₁ to limUnder, rewrite Ξ s t as S 0
  have hmap : sewingMap₁ Ξ θ K a b hΞ s t = limUnder atTop S := by
    have hcond : a ≤ s ∧ s ≤ t ∧ t ≤ b := ⟨has, hst, htb⟩
    simp only [sewingMap₁, S, dif_pos hcond]
  rw [hmap, ← dyadicSum₁_zero Ξ s t]
  -- Geometric bound setup
  set r := sewingRatio₁ θ
  have hr₀ : 0 ≤ r := le_of_lt (sewingRatio₁_pos hΞ.one_lt_theta)
  have hr₁ : r < 1 := sewingRatio₁_lt_one hΞ.one_lt_theta
  have hK₀ : 0 ≤ K := hΞ.K_nonneg
  have hts₀ : 0 ≤ |t - s| ^ θ := rpow_nonneg (abs_nonneg _) _
  -- Each successive difference bounded by (K * |t-s|^θ) * r^n
  have hd_bound : ∀ n, ‖S (n + 1) - S n‖ ≤ K * |t - s| ^ θ * r ^ n := by
    intro n
    convert dyadicSum₁_diff_bound hΞ has hst htb n using 1
    simp only [r, sewingRatio₁]
    rw [← rpow_natCast ((2 : ℝ)⁻¹ ^ (θ - 1)) n,
        ← rpow_mul (by positivity : (0 : ℝ) ≤ 2⁻¹)]
    congr 1; ring_nf
  -- Strategy: bound ‖S N - S 0‖ for all N, then pass to the limit
  suffices hbound : ∀ N, ‖S N - S 0‖ ≤ K * sewingConst₁ θ * |t - s| ^ θ from
    le_of_tendsto
      ((dyadicSum₁_cauchy hΞ has hst htb).tendsto_limUnder.sub tendsto_const_nhds).norm
      (Eventually.of_forall hbound)
  intro N
  -- Telescope: S N - S 0 = ∑_{k<N} (S(k+1) - S(k))
  have htel : S N - S 0 = ∑ k ∈ range N, (S (k + 1) - S k) := by
    induction N with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ← ih]; abel
  rw [htel]
  calc ‖∑ k ∈ range N, (S (k + 1) - S k)‖
      ≤ ∑ k ∈ range N, ‖S (k + 1) - S k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range N, K * |t - s| ^ θ * r ^ k := by
        gcongr with k _; exact hd_bound k
    _ ≤ K * |t - s| ^ θ * ∑ k ∈ range N, r ^ k := by
        rw [Finset.mul_sum]
    _ ≤ K * |t - s| ^ θ * (1 - r)⁻¹ := by
        gcongr
        have hsumm := summable_geometric_of_lt_one hr₀ hr₁
        rw [← tsum_geometric_of_lt_one hr₀ hr₁]
        exact hsumm.sum_le_tsum _ (fun k _ => pow_nonneg hr₀ k)
    _ = K * sewingConst₁ θ * |t - s| ^ θ := by
        have : (1 - r)⁻¹ = sewingConst₁ θ := by
          simp [sewingConst₁, sewingRatio₁, one_div]; rfl
        rw [this]; ring

/-- **Uniqueness**: any additive functional with the approximation bound equals the sewn map.

If `J` is additive on `[a,b]` and `‖J(s,t) - Ξ(s,t)‖ ≤ C' · |t-s|^θ`, then `J = I`.

**Proof**: For any `s ≤ t` in `[a,b]`, using additivity of both `J` and `I`, subdivide
`[s,t]` into `2^n` dyadic pieces. On each piece `[tₖ, tₖ₊₁]` of length `|t-s|/2^n`:

  `‖J(tₖ, tₖ₊₁) - I(tₖ, tₖ₊₁)‖ ≤ (C' + C) · (|t-s|/2^n)^θ`

Summing `2^n` terms by the triangle inequality:

  `‖J(s,t) - I(s,t)‖ ≤ 2^n · (C' + C) · (|t-s|/2^n)^θ = (C' + C) · |t-s|^θ · 2^{-n(θ-1)}`

Since `θ > 1`, the right side → 0 as `n → ∞`. So `J(s,t) = I(s,t)`. -/
theorem sewingMap₁_unique [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {θ K a b : ℝ}
    (hΞ : SewingCondition₁ Ξ θ K a b)
    {J : ℝ → ℝ → E} {C' : ℝ}
    (hJ_add : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      J s t = J s u + J u t)
    (hJ_bound : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖J s t - Ξ s t‖ ≤ C' * |t - s| ^ θ)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    J s t = sewingMap₁ Ξ θ K a b hΞ s t := by
  -- J(s,t) = lim S_n(s,t), since J additive telescopes over dyadic partitions
  -- and each piece's error decays geometrically.
  set S := fun n => dyadicSum₁ Ξ s t n
  have hmap : sewingMap₁ Ξ θ K a b hΞ s t = limUnder atTop S := by
    have hcond : a ≤ s ∧ s ≤ t ∧ t ≤ b := ⟨has, hst, htb⟩
    simp only [sewingMap₁, S, dif_pos hcond]
  -- J(s,t) = lim S_n(s,t) because ‖J(s,t) - S_n(s,t)‖ → 0
  rw [hmap]
  suffices h : Tendsto S atTop (nhds (J s t)) from
    tendsto_nhds_unique h (dyadicSum₁_cauchy hΞ has hst htb).tendsto_limUnder
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- J telescopes over dyadic partitions by additivity
  have hJ_tel : ∀ n, J s t = ∑ k ∈ range (2 ^ n),
      J (dyadicPt s t n k) (dyadicPt s t n (k + 1)) := by
    intro n; induction n with
    | zero => simp [dyadicPt]
    | succ n ih =>
      rw [ih, show 2 ^ (n + 1) = 2 * 2 ^ n from by ring, sum_range_pair]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_lt : k < 2 ^ n := Finset.mem_range.mp hk
      rw [dyadicPt_double, show 2 * k + 1 + 1 = 2 * (k + 1) from by omega, dyadicPt_double]
      exact hJ_add _ _ _
        (le_trans has (dyadicPt_mem_Icc hst (by omega : k ≤ 2 ^ n)).1)
        (dyadicPt_double s t n k ▸ dyadicPt_mono hst (n + 1) (by omega : 2 * k ≤ 2 * k + 1))
        (by rw [← dyadicPt_double s t n (k + 1)];
            exact dyadicPt_mono hst (n + 1) (by omega : 2 * k + 1 ≤ 2 * (k + 1)))
        (le_trans (dyadicPt_mem_Icc hst (by omega : k + 1 ≤ 2 ^ n)).2 htb)
  -- So ‖J(s,t) - S_n(s,t)‖ ≤ ∑_k C'·(|t-s|/2^n)^θ = C'·|t-s|^θ·2^{-n(θ-1)}
  set r := sewingRatio₁ θ
  have hr₀ : 0 ≤ r := le_of_lt (sewingRatio₁_pos hΞ.one_lt_theta)
  have hr₁ : r < 1 := sewingRatio₁_lt_one hΞ.one_lt_theta
  -- Choose N such that C'·|t-s|^θ·r^N < ε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C' * |t - s| ^ θ * r ^ N < ε := by
    by_cases hC : C' * |t - s| ^ θ ≤ 0
    · exact ⟨0, by linarith [pow_nonneg hr₀ (0 : ℕ)]⟩
    · push_neg at hC
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hC) hr₁
      exact ⟨N, by
        have := mul_lt_mul_of_pos_left hN hC
        rwa [mul_div_cancel₀ ε (ne_of_gt hC)] at this⟩
  use N; intro n hn
  rw [dist_comm, dist_eq_norm, hJ_tel n]
  simp only [S, dyadicSum₁]
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ k ∈ range (2 ^ n), (J (dyadicPt s t n k) (dyadicPt s t n (k + 1)) -
          Ξ (dyadicPt s t n k) (dyadicPt s t n (k + 1)))‖
      ≤ ∑ k ∈ range (2 ^ n), ‖J (dyadicPt s t n k) (dyadicPt s t n (k + 1)) -
          Ξ (dyadicPt s t n k) (dyadicPt s t n (k + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range (2 ^ n), C' * |dyadicPt s t n (k + 1) - dyadicPt s t n k| ^ θ := by
        gcongr with k hk
        exact hJ_bound _ _
          (le_trans has (dyadicPt_mem_Icc hst (le_of_lt (Finset.mem_range.mp hk))).1)
          (dyadicPt_mono hst n (by omega))
          (le_trans (dyadicPt_mem_Icc hst (by grind : k + 1 ≤ 2 ^ n)).2 htb)
    _ = ∑ _k ∈ range (2 ^ n), C' * (|t - s| / (2 : ℝ) ^ n) ^ θ := by
        congr 1; ext k; rw [abs_dyadicPt_sub]
    _ = (2 : ℝ) ^ n * (C' * (|t - s| / (2 : ℝ) ^ n) ^ θ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ = C' * (|t - s| ^ θ * ((2 : ℝ)⁻¹) ^ (↑n * (θ - 1))) := by
        rw [← dyadic_geometric_factor (abs_nonneg _) n]; ring
    _ = C' * |t - s| ^ θ * r ^ n := by
        have hrn : ((2 : ℝ)⁻¹) ^ (↑n * (θ - 1)) = r ^ n := by
          simp only [r, sewingRatio₁]
          rw [← rpow_natCast ((2 : ℝ)⁻¹ ^ (θ - 1)) n,
              ← rpow_mul (by positivity : (0 : ℝ) ≤ 2⁻¹)]
          congr 1; ring
        rw [hrn]; ring
    _ < ε := by
        by_cases h : C' * |t - s| ^ θ ≤ 0
        · linarith [mul_nonpos_of_nonpos_of_nonneg h (pow_nonneg hr₀ n)]
        · push_neg at h
          calc C' * |t - s| ^ θ * r ^ n
              ≤ C' * |t - s| ^ θ * r ^ N :=
                mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr₀ hr₁.le hn) h.le
            _ < ε := hN

/-- The dyadic sums converge to the sewing map. -/
theorem sewingMap₁_tendsto [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {θ K a b : ℝ}
    (hΞ : SewingCondition₁ Ξ θ K a b) {s t : ℝ}
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    Tendsto (fun n => dyadicSum₁ Ξ s t n) atTop
      (nhds (sewingMap₁ Ξ θ K a b hΞ s t)) := by
  have : sewingMap₁ Ξ θ K a b hΞ s t =
      limUnder atTop (fun n => dyadicSum₁ Ξ s t n) := by
    simp only [sewingMap₁]
    simp only [dite_eq_ite, ite_eq_left_iff, not_and, not_le]
    grind only
  rw [this]
  exact (dyadicSum₁_cauchy hΞ has hst htb).tendsto_limUnder


/-- **Midpoint additivity**: the sewing map splits at the midpoint.

`I(s, t) = I(s, (s+t)/2) + I((s+t)/2, t)`

Proof: the shifted sequence `n ↦ S_{n+1}(s,t)` converges to `I(s,t)`, but by
`dyadicSum₁_midpoint_split` it equals `S_n(s,m) + S_n(m,t)`, which converges
to `I(s,m) + I(m,t)`. Uniqueness of limits gives the identity. -/
theorem sewingMap₁_midpoint [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {θ K a b : ℝ}
    (hΞ : SewingCondition₁ Ξ θ K a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    sewingMap₁ Ξ θ K a b hΞ s t =
      sewingMap₁ Ξ θ K a b hΞ s ((s + t) / 2) +
      sewingMap₁ Ξ θ K a b hΞ ((s + t) / 2) t := by
  set m := (s + t) / 2
  have hsm : s ≤ m := by grind => linarith
  have hmt : m ≤ t := by grind => linarith
  -- Shifted sequence n ↦ S_{n+1}(s,t) converges to I(s,t)
  have htend_shift : Tendsto (fun n => dyadicSum₁ Ξ s t (n + 1)) atTop
      (nhds (sewingMap₁ Ξ θ K a b hΞ s t)) :=
    (sewingMap₁_tendsto hΞ has hst htb).comp
      (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega)
        (fun b => ⟨b, by omega⟩))
  -- By midpoint splitting, this equals S_n(s,m) + S_n(m,t)
  have htend_split : Tendsto
      (fun n => dyadicSum₁ Ξ s m n + dyadicSum₁ Ξ m t n) atTop
      (nhds (sewingMap₁ Ξ θ K a b hΞ s t)) := by
    have : (fun n => dyadicSum₁ Ξ s m n + dyadicSum₁ Ξ m t n) =
           (fun n => dyadicSum₁ Ξ s t (n + 1)) :=
      funext fun n => (dyadicSum₁_midpoint_split Ξ s t n).symm
    rw [this]; exact htend_shift
  -- Component sequences converge to their respective sewing maps
  have htend_sum : Tendsto
      (fun n => dyadicSum₁ Ξ s m n + dyadicSum₁ Ξ m t n) atTop
      (nhds (sewingMap₁ Ξ θ K a b hΞ s m +
             sewingMap₁ Ξ θ K a b hΞ m t)) :=
    (sewingMap₁_tendsto hΞ has hsm (hmt.trans htb)).add
      (sewingMap₁_tendsto hΞ (has.trans hsm) hmt htb)
  -- Uniqueness of limits
  exact tendsto_nhds_unique htend_split htend_sum


/-- **Dyadic additivity**: the sewing map telescopes exactly over dyadic partitions.

`I(s, t) = ∑_{k < 2^n} I(dₖ, dₖ₊₁)`

This is the iterated form of midpoint additivity. At each inductive step,
each summand `I(dₖ, dₖ₊₁)` splits at its midpoint (which is the next-level
dyadic point `d(n+1, 2k+1)`) via `sewingMap₁_midpoint`. -/
theorem sewingMap₁_dyadicSum [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {θ K a b : ℝ}
    (hΞ : SewingCondition₁ Ξ θ K a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (n : ℕ) :
    sewingMap₁ Ξ θ K a b hΞ s t =
      ∑ k ∈ Finset.range (2 ^ n),
        sewingMap₁ Ξ θ K a b hΞ (dyadicPt s t n k) (dyadicPt s t n (k + 1)) := by
  induction n with
  | zero => simp [dyadicPt]
  | succ n ih =>
    rw [ih, show 2 ^ (n + 1) = 2 * 2 ^ n from by ring, sum_range_pair]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk : k < 2 ^ n := Finset.mem_range.mp hk
    -- Rewrite level-(n+1) points to level-n points via dyadicPt_double
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) from by omega]
    rw [dyadicPt_double, dyadicPt_double]
    -- The midpoint of [d(n,k), d(n,k+1)] is d(n+1, 2k+1)
    rw [← dyadicPt_midpoint]
    -- Apply midpoint additivity
    have hdk := dyadicPt_mem_Icc hst (le_of_lt hk)
    have hdk1 := dyadicPt_mem_Icc hst (by omega : k + 1 ≤ 2 ^ n)
    exact sewingMap₁_midpoint hΞ
      (has.trans hdk.1) (dyadicPt_mono hst n (by omega)) (hdk1.2.trans htb)

end SewnMap₁

end StochCalc
