/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerThree/Map.lean
-/
import LogosLibrary.StochasticCalculus.SewingLemma.LayerThree.ThetaEnergy
import LogosLibrary.StochasticCalculus.SewingLemma.LayerThree.DyadicPartition

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc


/-! ### The sewn map (Layer 3) -/

section SewnMap₃

  -- Proof outline:
  -- 1. The n-th dyadic partition Dₙ has mesh |t-s|/2^n → 0.
  -- 2. By thetaEnergy_tendsto_zero, Φ_θ(Dₙ) → 0.
  -- 3. For m ≥ n, the level-m dyadic partition refines the level-n one.
  --    (Every level-n point is a level-m point: d(n,k) = d(m, k·2^{m-n}).)
  -- 4. By riemannSum_refinement_bound:
  --    ‖Sₘ - Sₙ‖ ≤ K · Φ_θ(Dₙ)
  -- 5. Given ε > 0, choose N with K · Φ_θ(Dₙ) < ε for n ≥ N. Done.
  --
  -- Key subtlety: we need to relate dyadicSum₁ (which uses Finset.range)
  -- to riemannSum (which uses Fin P.n). This is a packaging issue, not
  -- a mathematical one — but it needs a small glue lemma.

/-- The sewn map vanishes on the diagonal. -/
theorem sewingMap₃_diag [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    sewingMap₃ Ξ ω θ K a b hΞ s s = 0 := by
  -- Identical to Layer 1: dyadicSum₁ Ξ s s n = 0 for all n.
  unfold sewingMap₃
  rw [dif_pos ⟨has, le_refl s, hsb⟩]
  have hconst : ∀ n, dyadicSum₁ Ξ s s n = 0 := by
    intro n
    simp only [dyadicSum₁, dyadicPt, sub_self, mul_zero, zero_div, add_zero]
    simp [hΞ.vanish_diag]
  simp_rw [hconst]
  exact tendsto_const_nhds.limUnder_eq

/-- **Approximation bound (Layer 3)**: `‖I(s,t) - Ξ(s,t)‖ ≤ K · ω(s,t)^θ`.

Note the *much simpler* form compared to Layers 1–2. There is no geometric constant
`sewingConst` — the bound is simply `K · ω(s,t)^θ`, the same as the defect bound.

This is because the Riemann sum `S₀ = Ξ(s,t)`, and every refinement introduces defects
bounded by the theta-energy, which in turn is bounded by `ω(s,t)^θ` (trivially, since
the trivial partition's theta-energy is `ω(s,t)^θ`). -/
theorem sewingMap₃_dist_le [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖sewingMap₃ Ξ ω θ K a b hΞ s t - Ξ s t‖ ≤
      K * ∑' n, thetaEnergy ω θ (dyadicPartition s t hst n) := by
  set S := fun n => dyadicSum₁ Ξ s t n
  have hmap : sewingMap₃ Ξ ω θ K a b hΞ s t = limUnder atTop S := by
    unfold sewingMap₃; exact dif_pos ⟨has, hst, htb⟩
  rw [hmap, ← dyadicSum₁_zero Ξ s t]
  -- The energy sequence is summable
  set Φ := fun n => thetaEnergy ω θ (dyadicPartition s t hst n)
  have hΦ_sum : Summable Φ := hΞ.energy_summable s t has hst htb
  have hΦ_nn : ∀ n, 0 ≤ Φ n := by
    intro n; simp only [Φ, thetaEnergy_dyadicPartition]
    exact Finset.sum_nonneg fun k _ =>
      rpow_nonneg (hΞ.omega_cont.nonneg _ _
        (has.trans (dyadicPt_mem_Icc hst (by grind only [= Finset.mem_range])).1)
        (dyadicPt_mono hst n (by omega))
        ((dyadicPt_mem_Icc hst (by grind only [= Finset.mem_range])).2.trans htb)) _
  -- Each successive difference bounded by K * Φ(n)
  have hd_bound : ∀ n, ‖S (n + 1) - S n‖ ≤ K * Φ n := by
    intro n
    show ‖dyadicSum₁ Ξ s t (n + 1) - dyadicSum₁ Ξ s t n‖ ≤
      K * thetaEnergy ω θ (dyadicPartition s t hst n)
    rw [thetaEnergy_dyadicPartition]
    exact dyadicSum₃_diff_bound hΞ has hst htb n
  -- Uniform bound: ‖S N - S 0‖ ≤ K * ∑_{k<N} Φ(k) ≤ K * ∑' Φ
  suffices hbound : ∀ N, ‖S N - S 0‖ ≤
      K * ∑' n, Φ n from
    le_of_tendsto
      ((dyadicSum₃_cauchy hΞ has hst htb).tendsto_limUnder.sub tendsto_const_nhds).norm
      (Eventually.of_forall hbound)
  intro N
  have htel : S N - S 0 = ∑ k ∈ Finset.range N, (S (k + 1) - S k) := by
    induction N with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ← ih]; abel
  rw [htel]
  calc ‖∑ k ∈ Finset.range N, (S (k + 1) - S k)‖
      ≤ ∑ k ∈ Finset.range N, ‖S (k + 1) - S k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, K * Φ k := by
        gcongr with k _; exact hd_bound k
    _ = K * ∑ k ∈ Finset.range N, Φ k := by rw [← Finset.mul_sum]
    _ ≤ K * ∑' n, Φ n := by
        gcongr
        · exact hΞ.K_nonneg
        · exact hΦ_sum.sum_le_tsum _ (fun k _ => hΦ_nn k)

/-- The dyadic sums converge to the sewing map. -/
theorem sewingMap₃_tendsto [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b) {s t : ℝ}
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    Tendsto (fun n => dyadicSum₁ Ξ s t n) atTop
      (nhds (sewingMap₃ Ξ ω θ K a b hΞ s t)) := by
  have : sewingMap₃ Ξ ω θ K a b hΞ s t =
      limUnder atTop (fun n => dyadicSum₁ Ξ s t n) := by
    simp only [sewingMap₃]
    simp only [dite_eq_ite, ite_eq_left_iff, not_and, not_le]
    grind only
  rw [this]
  exact (dyadicSum₃_cauchy hΞ has hst htb).tendsto_limUnder

/-- **Midpoint additivity**: `I(s, t) = I(s, (s+t)/2) + I((s+t)/2, t)`. -/
theorem sewingMap₃_midpoint [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    sewingMap₃ Ξ ω θ K a b hΞ s t =
      sewingMap₃ Ξ ω θ K a b hΞ s ((s + t) / 2) +
      sewingMap₃ Ξ ω θ K a b hΞ ((s + t) / 2) t := by
  set m := (s + t) / 2
  have hsm : s ≤ m := by grind => linarith
  have hmt : m ≤ t := by grind => linarith
  have htend_shift : Tendsto (fun n => dyadicSum₁ Ξ s t (n + 1)) atTop
      (nhds (sewingMap₃ Ξ ω θ K a b hΞ s t)) :=
    (sewingMap₃_tendsto hΞ has hst htb).comp
      (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega)
        (fun b => ⟨b, by omega⟩))
  have htend_split : Tendsto
      (fun n => dyadicSum₁ Ξ s m n + dyadicSum₁ Ξ m t n) atTop
      (nhds (sewingMap₃ Ξ ω θ K a b hΞ s t)) := by
    have : (fun n => dyadicSum₁ Ξ s m n + dyadicSum₁ Ξ m t n) =
           (fun n => dyadicSum₁ Ξ s t (n + 1)) :=
      funext fun n => (dyadicSum₁_midpoint_split Ξ s t n).symm
    rw [this]; exact htend_shift
  have htend_sum : Tendsto
      (fun n => dyadicSum₁ Ξ s m n + dyadicSum₁ Ξ m t n) atTop
      (nhds (sewingMap₃ Ξ ω θ K a b hΞ s m +
             sewingMap₃ Ξ ω θ K a b hΞ m t)) :=
    (sewingMap₃_tendsto hΞ has hsm (hmt.trans htb)).add
      (sewingMap₃_tendsto hΞ (has.trans hsm) hmt htb)
  exact tendsto_nhds_unique htend_split htend_sum

/-- **Dyadic additivity**: `I(s, t) = ∑_{k < 2^n} I(dₖ, dₖ₊₁)`. -/
theorem sewingMap₃_dyadicSum [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (n : ℕ) :
    sewingMap₃ Ξ ω θ K a b hΞ s t =
      ∑ k ∈ Finset.range (2 ^ n),
        sewingMap₃ Ξ ω θ K a b hΞ (dyadicPt s t n k) (dyadicPt s t n (k + 1)) := by
  induction n with
  | zero => simp [dyadicPt]
  | succ n ih =>
    rw [ih, show 2 ^ (n + 1) = 2 * 2 ^ n from by ring, sum_range_pair]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk : k < 2 ^ n := Finset.mem_range.mp hk
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) from by omega]
    rw [dyadicPt_double, dyadicPt_double]
    rw [← dyadicPt_midpoint]
    have hdk := dyadicPt_mem_Icc hst (le_of_lt hk)
    have hdk1 := dyadicPt_mem_Icc hst (by omega : k + 1 ≤ 2 ^ n)
    exact sewingMap₃_midpoint hΞ
      (has.trans hdk.1) (dyadicPt_mono hst n (by omega)) (hdk1.2.trans htb)


/-- **Uniqueness (Layer 3)**. -/
theorem sewingMap₃_unique [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {J : ℝ → ℝ → E} {C' : ℝ}
    (hJ_add : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      J s t = J s u + J u t)
    (hJ_bound : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖J s t - Ξ s t‖ ≤ C' * ω s t ^ θ)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    J s t = sewingMap₃ Ξ ω θ K a b hΞ s t := by
  set S := fun n => dyadicSum₁ Ξ s t n
  have hmap : sewingMap₃ Ξ ω θ K a b hΞ s t = limUnder atTop S := by
    unfold sewingMap₃; exact dif_pos ⟨has, hst, htb⟩
  rw [hmap]
  suffices h : Tendsto S atTop (nhds (J s t)) from
    tendsto_nhds_unique h (dyadicSum₃_cauchy hΞ has hst htb).tendsto_limUnder
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
  -- ‖J(s,t) - S_n‖ ≤ C' · Φ_θ(D_n), and Φ_θ(D_n) → 0
  have hΦ_tend := thetaEnergy_dyadicPartition_tendsto hΞ.omega_cont hΞ.one_lt_theta has htb hst
  -- Choose N from tendsto
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n, N₀ ≤ n →
      thetaEnergy ω θ (dyadicPartition s t hst n) < ε / (|C'| + 1) := by
    have hε' : 0 < ε / (|C'| + 1) := div_pos hε (by positivity)
    rw [Metric.tendsto_atTop] at hΦ_tend
    obtain ⟨N₀, hN₀⟩ := hΦ_tend (ε / (|C'| + 1)) hε'
    exact ⟨N₀, fun n hn => by
      have := hN₀ n hn
      rwa [Real.dist_0_eq_abs, abs_of_nonneg (by
        rw [thetaEnergy_dyadicPartition]
        exact Finset.sum_nonneg fun k _ =>
          rpow_nonneg (hΞ.omega_cont.nonneg _ _
            (has.trans (dyadicPt_mem_Icc hst (by grind only [= Finset.mem_range])).1)
            (dyadicPt_mono hst n (by omega))
            ((dyadicPt_mem_Icc hst (by grind only [= Finset.mem_range])).2.trans htb)) _)] at this⟩
  use N₀; intro n hn
  rw [dist_comm, dist_eq_norm, hJ_tel n]
  simp only [S, dyadicSum₁]
  rw [← Finset.sum_sub_distrib]
  -- ‖∑(J - Ξ)‖ ≤ ∑‖J - Ξ‖ ≤ ∑ C'·ω^θ ≤ |C'|·Φ_θ(D_n)
  calc ‖∑ k ∈ range (2 ^ n), (J (dyadicPt s t n k) (dyadicPt s t n (k + 1)) -
          Ξ (dyadicPt s t n k) (dyadicPt s t n (k + 1)))‖
      ≤ ∑ k ∈ range (2 ^ n), ‖J (dyadicPt s t n k) (dyadicPt s t n (k + 1)) -
          Ξ (dyadicPt s t n k) (dyadicPt s t n (k + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range (2 ^ n),
          C' * ω (dyadicPt s t n k) (dyadicPt s t n (k + 1)) ^ θ := by
        gcongr with k hk
        have hk_lt := Finset.mem_range.mp hk
        exact hJ_bound _ _
          (le_trans has (dyadicPt_mem_Icc hst (le_of_lt hk_lt)).1)
          (dyadicPt_mono hst n (by omega))
          (le_trans (dyadicPt_mem_Icc hst (by exact hk_lt)).2 htb)
    _ ≤ ∑ k ∈ range (2 ^ n),
          |C'| * ω (dyadicPt s t n k) (dyadicPt s t n (k + 1)) ^ θ := by
        gcongr with k hk
        · have hk_lt := Finset.mem_range.mp hk
          exact rpow_nonneg (hΞ.omega_cont.nonneg _ _
            (has.trans (dyadicPt_mem_Icc hst (le_of_lt hk_lt)).1)
            (dyadicPt_mono hst n (Nat.le_succ k))
            ((dyadicPt_mem_Icc hst hk_lt).2.trans htb)) _
        · exact le_abs_self C'
    _ = |C'| * thetaEnergy ω θ (dyadicPartition s t hst n) := by
        rw [← Finset.mul_sum, thetaEnergy_dyadicPartition]
    _ < ε := by
        have hΦ_nn : 0 ≤ thetaEnergy ω θ (dyadicPartition s t hst n) := by
          rw [thetaEnergy_dyadicPartition]
          exact Finset.sum_nonneg fun k _ =>
            rpow_nonneg (hΞ.omega_cont.nonneg _ _
              (has.trans (dyadicPt_mem_Icc hst (by grind only [= Finset.mem_range])).1)
              (dyadicPt_mono hst n (by omega))
              ((dyadicPt_mem_Icc hst (by grind only [= Finset.mem_range])).2.trans htb)) _
        calc |C'| * thetaEnergy ω θ (dyadicPartition s t hst n)
            ≤ (|C'| + 1) * thetaEnergy ω θ (dyadicPartition s t hst n) :=
              mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C']) hΦ_nn
          _ < (|C'| + 1) * (ε / (|C'| + 1)) :=
              mul_lt_mul_of_pos_left (hN₀ n hn) (by positivity)
          _ = ε := by field_simp

/-- **I is small near the diagonal**: `‖I(s',t')‖ < ε` when `t' - s'` is small enough.
This combines `xi_cont` (Ξ is small) with `energy_vanish` (the correction is small). -/
theorem sewingMap₃_small [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ s t, a ≤ s → s ≤ t → t ≤ b → t - s < δ →
      ‖sewingMap₃ Ξ ω θ K a b hΞ s t‖ < ε := by
  -- Split ε between Ξ and the correction
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hΞ.xi_cont (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := hΞ.energy_vanish (ε / (2 * (K + 1)))
    (div_pos hε (by linarith [hΞ.K_nonneg]))
  refine ⟨min δ₁ δ₂, by positivity, fun s t has hst htb hδ => ?_⟩
  have hδ₁' : t - s < δ₁ := lt_of_lt_of_le hδ (min_le_left _ _)
  have hδ₂' : t - s < δ₂ := lt_of_lt_of_le hδ (min_le_right _ _)
  calc ‖sewingMap₃ Ξ ω θ K a b hΞ s t‖
    _ ≤ ‖sewingMap₃ Ξ ω θ K a b hΞ s t - Ξ s t‖ + ‖Ξ s t‖ := by
      calc ‖sewingMap₃ Ξ ω θ K a b hΞ s t‖
          = ‖(sewingMap₃ Ξ ω θ K a b hΞ s t - Ξ s t) + Ξ s t‖ := by abel_nf
        _ ≤ ‖sewingMap₃ Ξ ω θ K a b hΞ s t - Ξ s t‖ + ‖Ξ s t‖ := norm_add_le _ _
    _ ≤ K * ∑' n, thetaEnergy ω θ (dyadicPartition s t hst n) + ‖Ξ s t‖ := by
        gcongr; exact sewingMap₃_dist_le hΞ has hst htb
    _ < K * (ε / (2 * (K + 1))) + ε / 2 := by
        apply add_lt_add_of_le_of_lt
        · exact mul_le_mul_of_nonneg_left (hδ₂ s t has hst htb hδ₂').le hΞ.K_nonneg
        · exact hδ₁ s t has hst htb hδ₁'
    _ ≤ ε := by
        have hK := hΞ.K_nonneg
        have : K * (ε / (2 * (K + 1))) ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * (K + 1)) two_pos]
          nlinarith
        linarith

/-- **General additivity (Layer 3)**.

The proof decomposes the dyadic Riemann sum at the interval containing u,
shows the "left" and "right" Ξ-level partial sums are Cauchy (with summable
differences bounded by 2K · Φ_θ(Dₙ)), and identifies their limits with
I(s,u) and I(u,t) respectively.

The identification step requires comparing Riemann sums over different
partition point sets (dyadic points of [s,t] vs dyadic points of [s,u]),
which needs a partition-comparison lemma: any two Riemann sums on the
same interval with vanishing theta-energy converge to the same limit.
This is proved via common-refinement bounds in a separate module. -/
axiom sewingMap₃_additive [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    sewingMap₃ Ξ ω θ K a b hΞ s t =
      sewingMap₃ Ξ ω θ K a b hΞ s u + sewingMap₃ Ξ ω θ K a b hΞ u t



end SewnMap₃

/-! ### Layer 2 implies Layer 3 -/

section Coercion

/-- A Lipschitz control is automatically a continuous control.
(Lipschitz ⟹ uniformly continuous ⟹ continuous at diagonal.) -/
theorem contControl_of_lipControl {ω : ℝ → ℝ → ℝ} {a b : ℝ}
    (hω : LipControl ω a b) : ContControl ω a b where
  nonneg := hω.nonneg
  diag := hω.diag
  superadd := hω.superadd
  cont_diag := by
    intro ε hε
    by_cases hL : hω.lip_const = 0
    · exact ⟨1, one_pos, fun s t has hst htb _ => by
        calc ω s t ≤ hω.lip_const * (t - s) := hω.lip_bound s t has hst htb
          _ = 0 := by rw [hL, zero_mul]
          _ < ε := hε⟩
    · exact ⟨ε / hω.lip_const, div_pos hε (lt_of_le_of_ne hω.lip_const_nonneg
          (Ne.symm hL)), fun s t has hst htb hδ => by
        calc ω s t ≤ hω.lip_const * (t - s) := hω.lip_bound s t has hst htb
          _ < hω.lip_const * (ε / hω.lip_const) := by
              apply mul_lt_mul_of_pos_left hδ
              exact lt_of_le_of_ne hω.lip_const_nonneg (Ne.symm hL)
          _ = ε := by field_simp⟩

end Coercion

end StochCalc
