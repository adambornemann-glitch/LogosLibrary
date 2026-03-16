/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerThree/Insert.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.RefiCo
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.DyadicPartition
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.Map.Partition

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

/-- Insert point `u` into block `k` of partition `P`. -/
def Partition.insertAt {s t : ℝ} (P : Partition s t) (k : Fin P.n) (u : ℝ)
    (hleft : P.left k ≤ u) (hright : u ≤ P.right k) : Partition s t where
  n := P.n + 1
  pts := fun ⟨i, hi⟩ =>
    if h : i ≤ k.val then P.pts ⟨i, by have := k.isLt; omega⟩
    else if h' : i = k.val + 1 then u
    else P.pts ⟨i - 1, by omega⟩
  mono := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ (hij : i ≤ j)
    simp only
    split_ifs with h1 h2 h3 h4
    · -- i ≤ k, j ≤ k
      exact P.mono (by omega)
    · -- i ≤ k, j = k+1
      exact (P.mono (by omega)).trans hleft
    · -- i ≤ k, j > k+1
      exact P.mono (Fin.mk_le_mk.mpr (show i ≤ j - 1 by omega))
    · -- i = k+1, j = k+1 (impossible by split but)
      linarith
    · -- i = k+1, j > k+1
      linarith
    · -- i > k+1, j ≤ k (impossible)
      exact hright.trans (P.mono (Fin.mk_le_mk.mpr (show k.val + 1 ≤ j - 1 by omega)))
    · -- i > k+1, j = k+1 (impossible)
      omega
    ·  -- i > k+1, j > k+1
      omega
    · exact P.mono (Fin.mk_le_mk.mpr (show i - 1 ≤ j - 1 by omega))
  first := by
    simp [show (0 : ℕ) ≤ k.val from Nat.zero_le _]
    exact P.first
  last := by
    simp only [show ¬(P.n + 1 ≤ k.val) from by omega,
               show P.n + 1 ≠ k.val + 1 from by omega]
    convert P.last using 2

/-- Inserting point `u` into block `k` changes the Riemann sum by exactly
one sewing defect: `RS(P) - RS(P.insertAt k u) = δΞ(left_k, u, right_k)`. -/
theorem riemannSum_insertAt {Ξ : ℝ → ℝ → E} {s t : ℝ}
    (P : Partition s t) (k : Fin P.n) (u : ℝ)
    (hleft : P.left k ≤ u) (hright : u ≤ P.right k) :
    riemannSum Ξ P - riemannSum Ξ (P.insertAt k u hleft hright) =
      sewingDefect₁ Ξ (P.left k) u (P.right k) := by
  set P' := P.insertAt k u hleft hright
  -- Clamped P-pts
  set f : ℕ → ℝ := fun i => P.pts ⟨min i P.n, by omega⟩
  have hf_val : ∀ i (hi : i ≤ P.n), f i = P.pts ⟨i, by omega⟩ :=
    fun i hi => by simp [f, Nat.min_eq_left hi]
  -- Clamped P'-pts
  set g : ℕ → ℝ := fun i => P'.pts ⟨min i P'.n, by omega⟩
  have hg_val : ∀ i (hi : i ≤ P'.n), g i = P'.pts ⟨i, by omega⟩ :=
    fun i hi => by simp [g, Nat.min_eq_left hi]
  -- P'.n = P.n + 1
  have hP'n : P'.n = P.n + 1 := rfl
  -- Key: g values in terms of f and u
  have hg_le : ∀ i (hi : i ≤ k.val), g i = f i := by
    intro i hi
    rw [hg_val i (by omega)]
    simp only [P', Partition.insertAt, show i ≤ k.val from hi, ↓reduceDIte]
    rw [hf_val i (by omega)]
  have hg_mid : g (k.val + 1) = u := by
    rw [hg_val (k.val + 1) (by omega)]
    simp only [P', Partition.insertAt, show ¬(k.val + 1 ≤ k.val) from by omega,
              ↓reduceDIte]
  have hg_gt : ∀ i (hi : k.val + 1 < i) (hi' : i ≤ P.n + 1),
      g i = f (i - 1) := by
    intro i hi hi'
    rw [hg_val i (by omega)]
    simp only [P', Partition.insertAt, show ¬(i ≤ k.val) from by omega,
               show i ≠ k.val + 1 from by omega, ↓reduceDIte]
    rw [hf_val (i - 1) (by omega)]
  -- Express both Riemann sums as range sums
  have hRS_P : riemannSum Ξ P =
      ∑ i ∈ Finset.range P.n, Ξ (f i) (f (i + 1)) := by
    simp only [riemannSum]; rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun ⟨i, hi⟩ _ => by
      simp only [Partition.left, Partition.right]
      rw [hf_val i (by omega), hf_val (i + 1) (by omega)]
  have hRS_P' : riemannSum Ξ P' =
      ∑ i ∈ Finset.range (P.n + 1), Ξ (g i) (g (i + 1)) := by
    simp only [riemannSum]; rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun ⟨i, hi⟩ _ => by
      simp only [Partition.left, Partition.right]
      rw [hg_val i (by omega), hg_val (i + 1) (by omega)]
  rw [hRS_P, hRS_P']
  -- Split RS(P) = [0, k) + {k} + [k+1, P.n)
  rw [show P.n = k.val + 1 + (P.n - k.val - 1) from by omega,
      Finset.sum_range_add, show k.val + 1 = k.val + 1 from rfl,
      Finset.sum_range_succ]
  -- Split RS(P') = [0, k) + {k} + {k+1} + [k+2, P.n+1)
  rw [show ↑k + 1 + (P.n - ↑k - 1) + 1 = (↑k + 2) + (P.n - ↑k - 1) from by omega,
      Finset.sum_range_add, show ↑k + 2 = ↑k + 1 + 1 from by omega,
      Finset.sum_range_succ, Finset.sum_range_succ]
  -- Substitute g values
  -- First k terms match: g i = f i for i ≤ k
  have hfirst : ∑ i ∈ Finset.range k.val, Ξ (g i) (g (i + 1)) =
      ∑ i ∈ Finset.range k.val, Ξ (f i) (f (i + 1)) := by
    exact Finset.sum_congr rfl fun i hi => by
      have hi_lt := Finset.mem_range.mp hi
      rw [hg_le i (by omega), hg_le (i + 1) (by omega)]
  -- Middle two P'-terms: Ξ(f k, u) + Ξ(u, f(k+1))
  have hmid_left : Ξ (g k.val) (g (k.val + 1)) = Ξ (f k.val) u := by
    rw [hg_le k.val le_rfl, hg_mid]
  have hmid_right : Ξ (g (k.val + 1)) (g (k.val + 2)) = Ξ u (f (k.val + 1)) := by
    rw [hg_mid, hg_gt (k.val + 2) (by omega) (by omega)]
    simp [show k.val + 2 - 1 = k.val + 1 from by omega]
  -- Tail terms match with shift
  have htail : ∑ i ∈ Finset.range (P.n - k.val - 1),
      Ξ (g (k.val + 2 + i)) (g (k.val + 2 + i + 1)) =
    ∑ i ∈ Finset.range (P.n - k.val - 1),
      Ξ (f (k.val + 1 + i)) (f (k.val + 1 + i + 1)) := by
    exact Finset.sum_congr rfl fun i hi => by
      rw [hg_gt (k.val + 2 + i) (by omega) (by grind only [= Lean.Grind.toInt_fin,
        = Finset.mem_range]),
          hg_gt (k.val + 2 + i + 1) (by omega) (by grind only [= Lean.Grind.toInt_fin,
            = Finset.mem_range])]
      congr 1 <;> congr 1 <;> omega
  -- Bridge f to P.left/P.right
  have hfk : f k.val = P.left k := by
    rw [hf_val k.val (by omega)]; rfl
  have hfk1 : f (k.val + 1) = P.right k := by
    rw [hf_val (k.val + 1) (by omega)]; rfl
  -- Assemble
  rw [hfirst, hmid_left, hmid_right, htail, hfk, hfk1]
  simp [sewingDefect₁]; abel


section InsertionPoint
/-- Find the block of P containing u: the largest k with P.pts(k) ≤ u. -/
def Partition.findBlock {s t : ℝ} (P : Partition s t) (u : ℝ)
    (hsu : s ≤ u) (_hut : u ≤ t) (hPn : 0 < P.n) : Fin P.n :=
  ⟨(Finset.univ.filter (fun k : Fin P.n =>
      P.pts ⟨k.val, by omega⟩ ≤ u)).max'
    ⟨⟨0, hPn⟩, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [ P.first]; exact hsu⟩,
  by exact ((Finset.univ.filter (fun k : Fin P.n =>
      P.pts ⟨k.val, by omega⟩ ≤ u)).max'
    ⟨⟨0, hPn⟩, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [P.first]; exact hsu⟩).isLt⟩


theorem Partition.findBlock_left_le {s t : ℝ} (P : Partition s t) (u : ℝ)
    (hsu : s ≤ u) (hut : u ≤ t) (hPn : 0 < P.n) :
    P.left (P.findBlock u hsu hut hPn) ≤ u := by
  set S := Finset.univ.filter (fun k : Fin P.n => P.pts ⟨k.val, by omega⟩ ≤ u)
  have hS_ne : S.Nonempty := ⟨⟨0, hPn⟩, by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [P.first]; exact hsu⟩
  show P.pts ⟨(S.max' hS_ne).val, by omega⟩ ≤ u
  exact (Finset.mem_filter.mp (S.max'_mem hS_ne)).2


theorem Partition.findBlock_right_ge {s t : ℝ} (P : Partition s t) (u : ℝ)
    (hsu : s ≤ u) (hut : u ≤ t) (hPn : 0 < P.n) :
    u ≤ P.right (P.findBlock u hsu hut hPn) := by
  set S := Finset.univ.filter (fun k : Fin P.n => P.pts ⟨k.val, by omega⟩ ≤ u)
  have hS_ne : S.Nonempty := ⟨⟨0, hPn⟩, by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [P.first]; exact hsu⟩
  set k := S.max' hS_ne
  -- Need: u ≤ P.pts ⟨k.val + 1, _⟩
  -- If k.val + 1 < P.n, then k+1 ∉ S (by maximality), so P.pts(k+1) > u... no, ¬(≤ u)
  -- If k.val + 1 = P.n, then P.pts(P.n) = t ≥ u
  show u ≤ P.pts ⟨(S.max' hS_ne).val + 1, by omega⟩
  by_cases h : k.val + 1 < P.n
  · -- k+1 is a valid Fin P.n index, but k+1 ∉ S (k is max)
    have hk1_notin : (⟨k.val + 1, h⟩ : Fin P.n) ∉ S := by
      intro hmem
      have := S.le_max' ⟨k.val + 1, h⟩ hmem
      simp only [k] at this
      exact absurd this (by grind => instantiate only [= Lean.Grind.toInt_fin])
    -- k+1 ∉ S means ¬(P.pts(k+1) ≤ u)
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk1_notin
    exact le_of_lt hk1_notin
  · -- k.val + 1 ≥ P.n, so k.val + 1 = P.n (since k < P.n)
    have hk1 : k.val + 1 = P.n := by omega
    calc u ≤ t := hut
      _ = P.pts ⟨P.n, by omega⟩ := P.last.symm
      _ = P.pts ⟨(S.max' hS_ne).val + 1, by omega⟩ := by congr 1; ext; exact hk1.symm


theorem Partition.insertAt_contains_u {s t : ℝ} (P : Partition s t)
    (k : Fin P.n) (u : ℝ)
    (hleft : P.left k ≤ u) (hright : u ≤ P.right k) :
    ∃ i : Fin ((P.insertAt k u hleft hright).n + 1),
      (P.insertAt k u hleft hright).pts i = u := by
  refine ⟨⟨k.val + 1, by show k.val + 1 < P.n + 1 + 1; omega⟩, ?_⟩
  simp only [Partition.insertAt, show ¬(k.val + 1 ≤ k.val) from by omega, ↓reduceDIte]

theorem insertion_defect_tendsto {Ξ : ℝ → ℝ → E}
    {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    {u : ℝ} (hsu : s ≤ u) (hut : u ≤ t) :
    Tendsto (fun n =>
      let P := dyadicPartition s t hst n
      let hPn : 0 < P.n := by show 0 < 2 ^ n; positivity
      let k := P.findBlock u hsu hut hPn
      sewingDefect₁ Ξ (P.left k) u (P.right k)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get δ from maxOmega_tendsto_zero: ω(block) < (ε / (K + 1))^{1/θ}
  -- Then ‖defect‖ ≤ K · ω^θ < K · ε/(K+1) < ε
  -- Simpler: just use that ‖defect‖ ≤ K · ω(block)^θ and ω(block) → 0
  have hθ_pos : (0 : ℝ) < θ := by linarith [hΞ.one_lt_theta]
  set ε' := (ε / (K + 1)) ^ ((1 : ℝ) / θ)
  have hK1_pos : 0 < K + 1 := by linarith [hΞ.K_nonneg]
  have hε'_pos : 0 < ε' := rpow_pos_of_pos (div_pos hε hK1_pos) _
  obtain ⟨δ, hδ_pos, hδ⟩ := maxOmega_tendsto_zero hΞ.omega_cont has htb hst ε' hε'_pos
  -- mesh(Dₙ) = (t-s)/2ⁿ → 0, choose N with mesh < δ
  obtain ⟨N, hN⟩ : ∃ N, ∀ n, N ≤ n → (dyadicPartition s t hst n).mesh < δ := by
    by_cases hts : t = s
    · exact ⟨0, fun n _ => by
        rw [dyadicPartition_mesh, show t - s = 0 from by linarith, zero_div]; exact hδ_pos⟩
    · have hts_pos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hst (Ne.symm hts))
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hδ_pos hts_pos)
        (by norm_num : (2:ℝ)⁻¹ < 1)
      exact ⟨N, fun n hn => by
        rw [dyadicPartition_mesh]
        calc (t - s) / 2 ^ n
            = (t - s) * (2⁻¹ ^ n) := by rw [div_eq_mul_inv, inv_pow]
          _ ≤ (t - s) * (2⁻¹ ^ N) := by
              apply mul_le_mul_of_nonneg_left _ hts_pos.le
              exact pow_le_pow_of_le_one (by positivity : (0:ℝ) ≤ 2⁻¹)
                (by norm_num : (2:ℝ)⁻¹ ≤ 1) hn
          _ < (t - s) * (δ / (t - s)) := by gcongr
          _ = δ := by field_simp⟩
  use N; intro n hn
  rw [dist_eq_norm, sub_zero]
  set P := dyadicPartition s t hst n
  set hPn : 0 < P.n := by show 0 < 2 ^ n; positivity
  set k := P.findBlock u hsu hut hPn
  have hmesh := hN n hn
  have hω_lt := hδ P hmesh k
  -- ‖defect‖ ≤ K · ω^θ
  have hbound := hΞ.defect_bound (P.left k) u (P.right k)
    (has.trans (P.mem_Icc hst ⟨k.val, by omega⟩).1)
    (P.findBlock_left_le u hsu hut hPn)
    (P.findBlock_right_ge u hsu hut hPn)
    ((P.mem_Icc hst ⟨k.val + 1, by omega⟩).2.trans htb)
  -- ω < ε' means ω^θ < ε'^θ = ε/(K+1)
  have hε'_pow : ε' ^ θ = ε / (K + 1) := by
    show ((ε / (K + 1)) ^ ((1:ℝ) / θ)) ^ θ = _
    rw [← rpow_mul (div_nonneg hε.le hK1_pos.le), div_mul_cancel₀ 1 hθ_pos.ne', rpow_one]
  calc ‖sewingDefect₁ Ξ (P.left k) u (P.right k)‖
      ≤ K * ω (P.left k) (P.right k) ^ θ := hbound
    _ ≤ K * ε' ^ θ := by
        apply mul_le_mul_of_nonneg_left _ hΞ.K_nonneg
        exact rpow_le_rpow
          (hΞ.omega_cont.nonneg _ _
            (has.trans (P.mem_Icc hst ⟨k.val, by omega⟩).1)
            (P.left_le_right k)
            ((P.mem_Icc hst ⟨k.val + 1, by omega⟩).2.trans htb))
          hω_lt.le hθ_pos.le
    _ = K * (ε / (K + 1)) := by rw [hε'_pow]
    _ < ε := by
        have : K * (ε / (K + 1)) = K * ε / (K + 1) := mul_div_assoc' K ε (K + 1)
        rw [this]
        rw [div_lt_iff₀ hK1_pos]
        nlinarith

/-- insertAt points: indices ≤ k are original P-points. -/
theorem insertAt_pts_le {s t : ℝ} (P : Partition s t) (k : Fin P.n) (u : ℝ)
    (hleft : P.left k ≤ u) (hright : u ≤ P.right k)
    {i : ℕ} (hi : i ≤ k.val) (hi' : i < P.n + 2) :
    (P.insertAt k u hleft hright).pts ⟨i, by show i < P.n + 1 + 1; omega⟩ =
      P.pts ⟨i, by omega⟩ := by
  simp only [Partition.insertAt, show i ≤ k.val from hi, ↓reduceDIte]

/-- insertAt points: index k+1 is u. -/
theorem insertAt_pts_mid {s t : ℝ} (P : Partition s t) (k : Fin P.n) (u : ℝ)
    (hleft : P.left k ≤ u) (hright : u ≤ P.right k) :
    (P.insertAt k u hleft hright).pts ⟨k.val + 1, by show k.val + 1 < P.n + 1 + 1; omega⟩ = u := by
  simp only [Partition.insertAt, show ¬(k.val + 1 ≤ k.val) from by omega, ↓reduceDIte]

/-- insertAt points: indices > k+1 are shifted P-points. -/
theorem insertAt_pts_gt {s t : ℝ} (P : Partition s t) (k : Fin P.n) (u : ℝ)
    (hleft : P.left k ≤ u) (hright : u ≤ P.right k)
    {i : ℕ} (hi : k.val + 1 < i) (hi' : i < P.n + 2) :
    (P.insertAt k u hleft hright).pts ⟨i, by show i < P.n + 1 + 1; omega⟩ =
      P.pts ⟨i - 1, by omega⟩ := by
  simp only [Partition.insertAt, show ¬(i ≤ k.val) from by omega,
             show ¬(i = k.val + 1) from by omega, ↓reduceDIte]

/-- Structural lemma: the restrictLeft of an insertAt partition has
"good" points (from the dyadic partition, separated by (t-s)/2ⁿ)
and at most 1 "bad" point (the inserted u). -/
lemma insertAt_restrictLeft_sep_bad
    {s t : ℝ} (hst : s ≤ t) (_hst_strict : s < t) (n : ℕ)
    {u : ℝ} (hsu : s ≤ u) (hut : u ≤ t) :
    let D := dyadicPartition s t hst n
    let hDn : 0 < D.n := by show 0 < 2 ^ n; positivity
    let k := D.findBlock u hsu hut hDn
    let hl := D.findBlock_left_le u hsu hut hDn
    let hr := D.findBlock_right_ge u hsu hut hDn
    let Q := D.insertAt k u hl hr
    let hQ_u := Partition.insertAt_contains_u D k u hl hr
    let QL := Q.restrictLeft u hsu hQ_u
    let good := Finset.univ.filter (fun i : Fin (QL.n + 1) => i.val ≠ k.val + 1)
    (∀ i ∈ good, ∀ j ∈ good, QL.pts i < QL.pts j →
      (t - s) / 2 ^ n ≤ QL.pts j - QL.pts i) ∧
    (Finset.univ \ good).card ≤ 1 := by
  intro D hDn k hl hr Q hQ_u QL good
  -- Key bound: QL.n ≤ D.n + 1 (= Q.n)
  have hQL_n_le : QL.n ≤ D.n + 1 := by
    show (Q.findPoint u hQ_u).val ≤ Q.n
    exact Nat.lt_succ_iff.mp (Q.findPoint u hQ_u).isLt
  -- QL.pts i = Q.pts ⟨i.val, _⟩
  have hQn : Q.n = D.n + 1 := rfl
  have hQL_n_le_Q : QL.n ≤ Q.n := by omega
  have hQL_pts : ∀ i : Fin (QL.n + 1),
      QL.pts i = Q.pts ⟨i.val, by omega⟩ := by
    intro i; rfl
  -- Good QL points are D-points
  have hgood_is_D : ∀ i : Fin (QL.n + 1), i.val ≠ k.val + 1 →
      ∃ di : Fin (D.n + 1), QL.pts i = D.pts di := by
    intro i hi_ne
    rw [hQL_pts i]
    rcases Nat.lt_or_ge i.val (k.val + 1) with h | h
    · -- i.val ≤ k.val
      have : i.val ≤ k.val := by omega
      rw [insertAt_pts_le D k u hl hr this (by omega)]
      exact ⟨⟨i.val, by have := k.isLt; omega⟩, rfl⟩
    · -- i.val ≥ k.val + 2
      have : k.val + 1 < i.val := by omega
      rw [insertAt_pts_gt D k u hl hr this (by omega)]
      exact ⟨⟨i.val - 1, by omega⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · -- Separation
    intro i hi j hj hlt
    have hi_ne := (Finset.mem_filter.mp hi).2
    have hj_ne := (Finset.mem_filter.mp hj).2
    obtain ⟨di, hdi⟩ := hgood_is_D i hi_ne
    obtain ⟨dj, hdj⟩ := hgood_is_D j hj_ne
    rw [hdi, hdj] at hlt ⊢
    exact dyadicPartition_min_spacing hst n di dj hlt
  · -- Bad count ≤ 1
    calc (Finset.univ \ good).card
        ≤ (Finset.univ.filter
            (fun i : Fin (QL.n + 1) => i.val = k.val + 1)).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [good, Finset.mem_sdiff, Finset.mem_filter,
                      Finset.mem_univ, true_and, not_not] at hi ⊢
          exact hi
      _ ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          exact Fin.ext (by omega)

/-- insertAt refines the original partition: every P-point is a (P.insertAt)-point. -/
theorem insertAt_refines {s t : ℝ} (P : Partition s t) (k : Fin P.n) (u : ℝ)
    (hleft : P.left k ≤ u) (hright : u ≤ P.right k) :
    (P.insertAt k u hleft hright).IsRefinement P := by
  intro ⟨i, hi⟩
  rcases Nat.lt_or_ge i (k.val + 1) with h | h
  · -- i ≤ k: P.pts i = insertAt.pts i
    exact ⟨⟨i, by show i < P.n + 1 + 1; omega⟩,
      insertAt_pts_le P k u hleft hright (by omega) (by omega)⟩
  · -- i ≥ k+1: P.pts i = insertAt.pts (i+1)
    refine ⟨⟨i + 1, by show i + 1 < P.n + 1 + 1; omega⟩, ?_⟩
    rw [insertAt_pts_gt P k u hleft hright (by omega) (by omega)]
    congr 1

/-- Mesh of insertAt ≤ mesh of original (insertAt is a refinement). -/
theorem insertAt_mesh_le {s t : ℝ} (P : Partition s t) (k : Fin P.n) (u : ℝ)
    (hleft : P.left k ≤ u) (hright : u ≤ P.right k) :
    (P.insertAt k u hleft hright).mesh ≤ P.mesh :=
  Partition.mesh_refinement_le (insertAt_refines P k u hleft hright)

/-- mesh(QL) ≤ mesh(D) ≤ (t-s)/2^n. -/
theorem insertAt_restrictLeft_mesh_le {s t : ℝ} (hst : s ≤ t) (n : ℕ)
    {u : ℝ} (hsu : s ≤ u) (hut : u ≤ t) :
    let D := dyadicPartition s t hst n
    let hDn : 0 < D.n := by show 0 < 2 ^ n; positivity
    let k := D.findBlock u hsu hut hDn
    let Q := D.insertAt k u (D.findBlock_left_le u hsu hut hDn)
        (D.findBlock_right_ge u hsu hut hDn)
    let hQ_u := Partition.insertAt_contains_u D k u _ _
    (Q.restrictLeft u hsu hQ_u).mesh ≤ (t - s) / 2 ^ n := by
  intro D hDn k Q hQ_u
  calc (Q.restrictLeft u hsu hQ_u).mesh
      ≤ Q.mesh := Partition.mesh_restrictLeft_le Q u hsu hQ_u
    _ ≤ D.mesh := insertAt_mesh_le D k u _ _
    _ = (t - s) / 2 ^ n := dyadicPartition_mesh s t hst n

/-- QL.n > 0 when s < u. -/
theorem insertAt_restrictLeft_n_pos {s t : ℝ} (hst : s ≤ t) (n : ℕ)
    {u : ℝ} (hsu : s ≤ u) (hut : u ≤ t) (hsu_strict : s < u) :
    let D := dyadicPartition s t hst n
    let hDn : 0 < D.n := by show 0 < 2 ^ n; positivity
    let k := D.findBlock u hsu hut hDn
    let Q := D.insertAt k u (D.findBlock_left_le u hsu hut hDn)
        (D.findBlock_right_ge u hsu hut hDn)
    let hQ_u := Partition.insertAt_contains_u D k u _ _
    0 < (Q.restrictLeft u hsu hQ_u).n := by
  intro D hDn k Q hQ_u
  set QL := Q.restrictLeft u hsu hQ_u
  -- QL.n = (Q.findPoint u hQ_u).val
  -- If QL.n = 0, then Q.pts 0 = u, but Q.pts 0 = s, contradicting s < u
  by_contra h; push_neg at h
  have hQLn : QL.n = 0 := by omega
  have hfp_val : (Q.findPoint u hQ_u).val = 0 := hQLn
  have hfp_spec : Q.pts (Q.findPoint u hQ_u) = u := Q.findPoint_spec u hQ_u
  have hfp_zero : (Q.findPoint u hQ_u) = ⟨0, by omega⟩ := Fin.ext hfp_val
  rw [hfp_zero] at hfp_spec
  have hQ_first : Q.pts ⟨0, by omega⟩ = s := Q.first
  linarith

/-- The specific index from insertAt_contains_u. -/
def insertAt_u_index {s t : ℝ} (P : Partition s t) (k : Fin P.n) :
    Fin (P.n + 2) :=
  ⟨k.val + 1, by omega⟩

theorem insertAt_u_index_spec {s t : ℝ} (P : Partition s t) (k : Fin P.n)
    (u : ℝ) (hleft : P.left k ≤ u) (hright : u ≤ P.right k) :
    (P.insertAt k u hleft hright).pts (insertAt_u_index P k) = u :=
  insertAt_pts_mid P k u hleft hright

end InsertionPoint
end StochCalc
