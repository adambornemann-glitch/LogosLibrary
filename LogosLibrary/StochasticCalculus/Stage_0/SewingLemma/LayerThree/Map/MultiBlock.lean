/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerThree/Map/MultiBlock.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.RefiCo
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.Insert
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.Map.Unique
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.Map.Merge
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.Map
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerOne.Map

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

/-- RS(Dₙ.insertAt(kₙ, u)) → I(s,t): the inserted Riemann sums converge. -/
theorem riemannSum_insertAt_tendsto [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    {u : ℝ} (hsu : s ≤ u) (hut : u ≤ t) :
    Tendsto (fun n =>
      let P := dyadicPartition s t hst n
      let hPn : 0 < P.n := by show 0 < 2 ^ n; positivity
      let k := P.findBlock u hsu hut hPn
      riemannSum Ξ (P.insertAt k u (P.findBlock_left_le u hsu hut hPn)
        (P.findBlock_right_ge u hsu hut hPn)))
      atTop (nhds (sewingMap₃ Ξ ω θ K a b hΞ s t)) := by
  set δ := fun n =>
    let P := dyadicPartition s t hst n
    let hPn : 0 < P.n := by show 0 < 2 ^ n; positivity
    let k := P.findBlock u hsu hut hPn
    sewingDefect₁ Ξ (P.left k) u (P.right k)
  have hδ_tend : Tendsto δ atTop (nhds 0) :=
    insertion_defect_tendsto hΞ has hst htb hsu hut
  have hS_tend := sewingMap₃_tendsto hΞ has hst htb
  have hfun_eq : (fun n =>
      let P := dyadicPartition s t hst n
      let hPn : 0 < P.n := by show 0 < 2 ^ n; positivity
      let k := P.findBlock u hsu hut hPn
      riemannSum Ξ (P.insertAt k u (P.findBlock_left_le u hsu hut hPn)
        (P.findBlock_right_ge u hsu hut hPn))) =
      (fun n => dyadicSum₁ Ξ s t n - δ n) := by
    ext n
    simp only [δ]
    have h := @riemannSum_insertAt E _ Ξ s t
      (dyadicPartition s t hst n)
      ((dyadicPartition s t hst n).findBlock u hsu hut (by show 0 < 2 ^ n; positivity))
      u
      ((dyadicPartition s t hst n).findBlock_left_le u hsu hut (by show 0 < 2 ^ n; positivity))
      ((dyadicPartition s t hst n).findBlock_right_ge u hsu hut (by show 0 < 2 ^ n; positivity))
    rw [dyadicPartition_riemannSum Ξ s t hst n] at h
    rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq']
    exact h.symm
  rw [hfun_eq, show sewingMap₃ Ξ ω θ K a b hΞ s t =
      sewingMap₃ Ξ ω θ K a b hΞ s t - 0 from (sub_zero _).symm]
  exact hS_tend.sub hδ_tend


/-- In an interval of length L, an arithmetic sequence with step h > 0
contributes at most ⌊L/h⌋ + 1 points. -/
lemma count_arith_points_in_interval {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L)
    {j₁ j₂ : ℕ} (hj : j₁ ≤ j₂)
    (hfit : (j₂ - j₁ : ℝ) * h ≤ L) :
    j₂ - j₁ ≤ Nat.floor (L / h) := by
  rw [Nat.le_floor_iff (div_nonneg hL hh.le), le_div_iff₀ hh, Nat.cast_sub hj]
  linarith

/-- Monotone embedding is strictly monotone on consecutive indices when
P₁ has distinct consecutive values. -/
lemma mono_embed_strict_step {s t : ℝ} {P P' : Partition s t}
    {φ : Fin (P.n + 1) → Fin (P'.n + 1)}
    (hφ_val : ∀ i, P'.pts (φ i) = P.pts i)
    (hφ_mono : Monotone φ)
    (k : Fin P.n)
    (hk : P.pts ⟨k.val, by omega⟩ < P.pts ⟨k.val + 1, by omega⟩) :
    (φ ⟨k.val, by omega⟩).val < (φ ⟨k.val + 1, by omega⟩).val := by
  by_contra h; push_neg at h
  have heq : φ ⟨k.val, by omega⟩ = φ ⟨k.val + 1, by omega⟩ :=
    le_antisymm (hφ_mono (Fin.mk_le_mk.mpr (by omega))) h
  have h1 := hφ_val ⟨k.val, by omega⟩
  have h2 := hφ_val ⟨k.val + 1, by omega⟩
  rw [heq] at h1
  linarith


/-- Per-block multiplicity bound for merge: each block of P₁ in the merge
spans at most P₂.n + 2 sub-intervals. Uses only n_merge_le + pigeonhole.

Requires strictly monotone embedding (which holds when P₁ has distinct
consecutive values — true for all our partitions since s < u or s < t). -/
theorem merge_block_mult {s t : ℝ} (P₁ P₂ : Partition s t)
    {φ : Fin (P₁.n + 1) → Fin ((P₁.merge P₂).n + 1)}
    (hφ_step : ∀ i : Fin P₁.n,
      (φ ⟨i.val, by omega⟩).val < (φ ⟨i.val + 1, by omega⟩).val)
    (hφ_start : φ ⟨0, by omega⟩ = ⟨0, by omega⟩)
    (hφ_end : φ ⟨P₁.n, by omega⟩ = ⟨(P₁.merge P₂).n, by omega⟩)
    (k : Fin P₁.n) :
    (φ ⟨k.val + 1, by omega⟩).val - (φ ⟨k.val, by omega⟩).val ≤ P₂.n + 2 := by
  set gap : Fin P₁.n → ℕ := fun i =>
    (φ ⟨i.val + 1, by omega⟩).val - (φ ⟨i.val, by omega⟩).val
  -- Each gap ≥ 1 (strict monotonicity)
  have hgap_pos : ∀ i : Fin P₁.n, 1 ≤ gap i := by
    intro i; show 1 ≤ _; have := hφ_step i; grind only [= Lean.Grind.toInt_fin]
  -- Telescoping: sum of gaps = M.n
  have htotal : ∑ i : Fin P₁.n, gap i = (P₁.merge P₂).n := by
    set ψ : ℕ → ℕ := fun i => (φ ⟨min i P₁.n, by omega⟩).val
    have hψ_val : ∀ i (hi : i ≤ P₁.n), ψ i = (φ ⟨i, by omega⟩).val :=
      fun i hi => by simp [ψ, Nat.min_eq_left hi]
    have hψ_step : ∀ i, i < P₁.n → ψ i ≤ ψ (i + 1) := by
      intro i hi
      rw [hψ_val i (by omega), hψ_val (i + 1) (by omega)]
      exact (hφ_step ⟨i, hi⟩).le
    have hgap_eq : ∀ i (hi : i < P₁.n),
        gap ⟨i, hi⟩ = ψ (i + 1) - ψ i := by
      intro i hi
      simp only [gap]
      rw [show ψ (i + 1) = (φ ⟨i + 1, by omega⟩).val from hψ_val (i + 1) (by omega),
          show ψ i = (φ ⟨i, by omega⟩).val from hψ_val i (by omega)]
    -- Additive telescoping (avoids ℕ subtraction underflow)
    have htel : ∀ m (hm : m ≤ P₁.n),
        (∑ i ∈ Finset.range m, (ψ (i + 1) - ψ i)) + ψ 0 = ψ m := by
      intro m; induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hm
        rw [Finset.sum_range_succ]
        have := ih (by omega)
        have := hψ_step m (by omega)
        omega
    -- Specialize at m = P₁.n
    have hspec := htel P₁.n le_rfl
    rw [hψ_val 0 (Nat.zero_le _), hψ_val P₁.n le_rfl,
        congrArg Fin.val hφ_start, congrArg Fin.val hφ_end] at hspec
    simp at hspec
    -- Convert Fin sum to range sum via ψ
    rw [show ∑ i : Fin P₁.n, gap i =
        ∑ i ∈ Finset.range P₁.n, (ψ (i + 1) - ψ i) from by
      rw [← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun ⟨i, hi⟩ _ => hgap_eq i hi]
    exact hspec
  -- M.n ≤ P₁.n + P₂.n + 1
  have hMn := Partition.n_merge_le P₁ P₂
  -- Pigeonhole: gap k + other gaps = M.n, other gaps ≥ P₁.n - 1
  have hsum_eq : gap k + ∑ i ∈ Finset.univ.erase k, gap i = (P₁.merge P₂).n := by
    rw [← htotal, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have hothers : P₁.n - 1 ≤ ∑ i ∈ Finset.univ.erase k, gap i := by
    calc P₁.n - 1
        = (Finset.univ.erase k).card := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_fin]
      _ = ∑ _i ∈ Finset.univ.erase k, 1 := by simp
      _ ≤ ∑ i ∈ Finset.univ.erase k, gap i :=
          Finset.sum_le_sum fun i _ => hgap_pos i
  -- gap k ≤ M.n - (P₁.n - 1) ≤ P₂.n + 2
  show gap k ≤ P₂.n + 2
  omega

  end StochCalc
