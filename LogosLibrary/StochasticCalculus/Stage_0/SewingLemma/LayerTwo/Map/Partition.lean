/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerTwo/Map/Partition.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.ThetaEnergy
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.Map.Merge

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc
/-! ### Partition splitting at an internal point -/

section PartitionSplit

/-- Index of point `u` in partition `P`, given that `P` contains `u`. -/
def Partition.findPoint {s t : ℝ} (P : Partition s t) (u : ℝ)
    (hu : ∃ i : Fin (P.n + 1), P.pts i = u) : Fin (P.n + 1) :=
  hu.choose

theorem Partition.findPoint_spec {s t : ℝ} (P : Partition s t) (u : ℝ)
    (hu : ∃ i : Fin (P.n + 1), P.pts i = u) :
    P.pts (P.findPoint u hu) = u :=
  hu.choose_spec

/-- Left restriction: the sub-partition of `P` over `[s, u]`,
given that `u` is a point of `P`. -/
def Partition.restrictLeft {s t : ℝ} (P : Partition s t) (u : ℝ)
    (_hsu : s ≤ u) (hu : ∃ i : Fin (P.n + 1), P.pts i = u) :
    Partition s u where
  n := (P.findPoint u hu).val
  pts := fun j => P.pts ⟨j.val, by have := (P.findPoint u hu).isLt; omega⟩
  mono := fun a b hab => P.mono (show (⟨a.val, _⟩ : Fin (P.n + 1)) ≤ ⟨b.val, _⟩ from hab)
  first := P.first
  last := P.findPoint_spec u hu

/-- Right restriction: the sub-partition of `P` over `[u, t]`. -/
def Partition.restrictRight {s t : ℝ} (P : Partition s t) (u : ℝ)
    (_hut : u ≤ t) (hu : ∃ i : Fin (P.n + 1), P.pts i = u) :
    Partition u t where
  n := P.n - (P.findPoint u hu).val
  pts := fun j => P.pts ⟨j.val + (P.findPoint u hu).val,
    by have := (P.findPoint u hu).isLt; omega⟩
  mono := fun a b hab => P.mono (by show a.val + _ ≤ b.val + _; omega)
  first := by
    simp only [zero_add, Fin.eta]
    exact P.findPoint_spec u hu
  last := by
    convert P.last using 2
    have := (P.findPoint u hu).isLt
    simp only [Fin.mk.injEq]
    omega

/-- The mesh of a restriction is at most the mesh of the original. -/
theorem Partition.mesh_restrictLeft_le {s t : ℝ} (P : Partition s t) (u : ℝ)
    (hsu : s ≤ u) (hu : ∃ i : Fin (P.n + 1), P.pts i = u) :
    (P.restrictLeft u hsu hu).mesh ≤ P.mesh := by
  set PL := P.restrictLeft u hsu hu
  -- Each PL sub-interval index is a valid P sub-interval index
  have hi_bound : ∀ i : Fin PL.n, i.val < P.n := by
    intro i
    have h1 : PL.n = (P.findPoint u hu).val := rfl
    have h2 := (P.findPoint u hu).isLt
    have h3 := i.isLt
    omega
  -- Each PL sub-interval matches the corresponding P sub-interval
  have hinterval : ∀ i : Fin PL.n,
      PL.right i - PL.left i =
        P.right ⟨i.val, hi_bound i⟩ - P.left ⟨i.val, hi_bound i⟩ := by
    intro i
    simp only [Partition.right, Partition.left, PL, restrictLeft]
  simp only [Partition.mesh]
  by_cases hPLn : PL.n = 0
  · rw [dif_pos hPLn]
    split_ifs with hPn
    · exact le_refl 0
    · exact Finset.le_sup'_of_le _
        (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hPn⟩)
        (sub_nonneg.mpr (P.left_le_right _))
  · have hPn : P.n ≠ 0 := by
      have := hi_bound ⟨0, Nat.pos_of_ne_zero hPLn⟩; omega
    rw [dif_neg hPLn, dif_neg hPn]
    apply Finset.sup'_le
    intro i _
    rw [hinterval i]
    exact Finset.le_sup' (fun j : Fin P.n => P.right j - P.left j)
      (Finset.mem_univ (⟨i.val, hi_bound i⟩ : Fin P.n))

theorem Partition.mesh_restrictRight_le {s t : ℝ} (P : Partition s t) (u : ℝ)
    (hut : u ≤ t) (hu : ∃ i : Fin (P.n + 1), P.pts i = u) :
    (P.restrictRight u hut hu).mesh ≤ P.mesh := by
  set PR := P.restrictRight u hut hu
  set idx := (P.findPoint u hu).val
  have hidx := (P.findPoint u hu).isLt
  -- Each PR sub-interval index shifts to a valid P sub-interval index
  have hi_bound : ∀ i : Fin PR.n, i.val + idx < P.n := by
    intro i
    have h1 : PR.n = P.n - idx := rfl
    have h3 := i.isLt
    omega
  -- Each PR sub-interval matches the shifted P sub-interval
  have hinterval : ∀ i : Fin PR.n,
      PR.right i - PR.left i =
        P.right ⟨i.val + idx, hi_bound i⟩ - P.left ⟨i.val + idx, hi_bound i⟩ := by
    intro i
    simp only [Partition.right, Partition.left, PR, restrictRight]
    grind only
  simp only [Partition.mesh]
  by_cases hPRn : PR.n = 0
  · rw [dif_pos hPRn]
    split_ifs with hPn
    · exact le_refl 0
    · exact Finset.le_sup'_of_le _
        (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hPn⟩)
        (sub_nonneg.mpr (P.left_le_right _))
  · have hPn : P.n ≠ 0 := by
      have := hi_bound ⟨0, Nat.pos_of_ne_zero hPRn⟩; omega
    rw [dif_neg hPRn, dif_neg hPn]
    apply Finset.sup'_le
    intro i _
    rw [hinterval i]
    exact Finset.le_sup' (fun j : Fin P.n => P.right j - P.left j)
      (Finset.mem_univ (⟨i.val + idx, hi_bound i⟩ : Fin P.n))

/-- **Riemann sum splitting**: if `P` contains point `u`, then
`RS(P) = RS(P|_[s,u]) + RS(P|_[u,t])`. -/
theorem riemannSum_split {Ξ : ℝ → ℝ → E} {s t : ℝ}
    (P : Partition s t) (u : ℝ)
    (hsu : s ≤ u) (hut : u ≤ t)
    (hu : ∃ i : Fin (P.n + 1), P.pts i = u) :
    riemannSum Ξ P =
      riemannSum Ξ (P.restrictLeft u hsu hu) +
      riemannSum Ξ (P.restrictRight u hut hu) := by
  set PL := P.restrictLeft u hsu hu
  set PR := P.restrictRight u hut hu
  set idx := (P.findPoint u hu).val
  have hidx := (P.findPoint u hu).isLt
  simp only [riemannSum]
  -- Clamped helper: well-defined for all ℕ, matches P-terms for i < P.n
  set F : ℕ → E := fun i =>
    Ξ (P.pts ⟨min i P.n, by omega⟩) (P.pts ⟨min (i + 1) P.n, by omega⟩)
  -- P's Fin sum = range sum of F
  have hP_eq : ∑ i : Fin P.n, Ξ (P.left i) (P.right i) =
      ∑ i ∈ Finset.range P.n, F i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun ⟨i, hi⟩ _ => by
      simp only [F, Partition.left, Partition.right]
      congr 1 <;> grind only [= min_def]
  -- PL's Fin sum = range sum of F (first idx terms)
  have hPL_eq : ∑ i : Fin PL.n, Ξ (PL.left i) (PL.right i) =
      ∑ i ∈ Finset.range idx, F i := by
    trans ∑ i ∈ Finset.range PL.n, F i
    · rw [← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun ⟨i, hi⟩ _ => by
        simp only [F, Partition.left, Partition.right, PL, Partition.restrictLeft]
        congr 1 <;> grind only [usr Fin.isLt, = min_def]
    · rfl  -- PL.n = idx definitionally
  -- PR's Fin sum = shifted range sum of F
  have hPR_eq : ∑ i : Fin PR.n, Ξ (PR.left i) (PR.right i) =
      ∑ i ∈ Finset.range (P.n - idx), F (idx + i) := by
    trans ∑ i ∈ Finset.range PR.n, F (idx + i)
    · rw [← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun ⟨i, hi⟩ _ => by
        simp only [F, Partition.left, Partition.right, PR, Partition.restrictRight]
        congr 1 <;> grind only [= Lean.Grind.toInt_fin, = min_def]
    · rfl  -- PR.n = P.n - idx definitionally
  -- Split: range P.n = range idx ++ shifted range (P.n - idx)
  rw [hP_eq, hPL_eq, hPR_eq, show P.n = idx + (P.n - idx) from by omega]
  simp only [add_tsub_cancel_left]
  exact sum_range_add F idx (P.n - idx)

end PartitionSplit

/-! ### The 2-point partition -/

section TwoPointPartition

/-- The partition `{s, u, t}` of `[s, t]`. -/
def Partition.twoPoint (s u t : ℝ) (hsu : s ≤ u) (hut : u ≤ t) :
    Partition s t where
  n := 2
  pts := ![s, u, t]
  mono := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    interval_cases i <;> interval_cases j <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith
  first := by simp [Matrix.cons_val_zero]
  last := by simp only [Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val]


/-- Merging dyadic partition with `{s, u, t}` produces a partition containing `u`. -/
theorem merge_contains_u {s t : ℝ} (hst : s ≤ t) {u : ℝ} (hsu : s ≤ u) (hut : u ≤ t)
    (n : ℕ) :
    let M := (dyadicPartition s t hst n).merge (Partition.twoPoint s u t hsu hut)
    ∃ i : Fin (M.n + 1), M.pts i = u := by
  intro M
  -- u is the second point of twoPoint: pts ⟨1, _⟩ = u
  have hu_in_tp : (Partition.twoPoint s u t hsu hut).pts ⟨1, by simp [Partition.twoPoint]⟩ = u := by
    simp [Partition.twoPoint, Matrix.cons_val_one, Matrix.cons_val_zero]
  -- merge refines twoPoint, so every twoPoint point appears in M
  have href := Partition.merge_refines_right (dyadicPartition s t hst n)
    (Partition.twoPoint s u t hsu hut)
  obtain ⟨j, hj⟩ := href ⟨1, by simp [Partition.twoPoint]⟩
  exact ⟨j, hj.trans hu_in_tp⟩

end TwoPointPartition

section PartitionRefinement
/-- The Riemann sum of the dyadic partition equals the dyadic sum. -/
theorem dyadicPartition_riemannSum (Ξ : ℝ → ℝ → E) (s t : ℝ) (hst : s ≤ t) (n : ℕ) :
    riemannSum Ξ (dyadicPartition s t hst n) = dyadicSum₁ Ξ s t n := by
  simp only [riemannSum, dyadicSum₁, dyadicPartition, Partition.left, Partition.right]
  rw [← Fin.sum_univ_eq_sum_range]; rfl

/-- The mesh of the dyadic partition is `(t - s) / 2^n`. -/
theorem dyadicPartition_mesh (s t : ℝ) (hst : s ≤ t) (n : ℕ) :
    (dyadicPartition s t hst n).mesh = (t - s) / (2 : ℝ) ^ n := by
  set P := dyadicPartition s t hst n
  have hPn : P.n ≠ 0 := by show 2 ^ n ≠ 0; positivity
  have hPn_pos : 0 < P.n := Nat.pos_of_ne_zero hPn
  -- Every interval has the same length
  have hlen : ∀ i : Fin P.n,
      P.right i - P.left i = (t - s) / (2 : ℝ) ^ n := by
    intro ⟨i, hi⟩
    simp only [Partition.right, Partition.left, P, dyadicPartition]
    exact dyadicPt_sub_succ s t n i
  simp only [Partition.mesh, dif_neg hPn]
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun i _ => (hlen i).le
  · exact Finset.le_sup'_of_le
      (fun i : Fin P.n => P.right i - P.left i)
      (Finset.mem_univ (⟨0, hPn_pos⟩ : Fin P.n))
      (hlen ⟨0, hPn_pos⟩).ge

/-- **Mesh decreases under refinement**: if `P'` refines `P`, then `mesh(P') ≤ mesh(P)`.

Every sub-interval `[P'.left j, P'.right j]` of the refinement is *contained* in some
sub-interval `[P.left k, P.right k]` of the original partition. Hence each P'-interval
is no longer than the longest P-interval.

**Bucket-finding argument**: given `j : Fin P'.n`, use the monotone embedding
`φ : Fin(P.n+1) → Fin(P'.n+1)` from `mono_embed` to find the unique `k` with
`φ(k) ≤ j < φ(k+1)`. This `k` is constructed as `max' {k | φ(k) ≤ j}`, which exists
(0 is always in the set since `φ(0) = 0 ≤ j`) and satisfies the upper bound by
maximality: if `j ≥ φ(k+1)` then either `k+1 ∈ S` (contradicting max) or `k+1 = P.n`
(giving `j ≥ φ(P.n) = P'.n`, contradicting `j < P'.n`).

Then: `P'.right j - P'.left j ≤ P'.pts(φ(k+1)) - P'.pts(φ(k))` by monotonicity
of `P'`, and `= P.right k - P.left k ≤ mesh(P)` by the embedding property. -/
theorem Partition.mesh_refinement_le {s t : ℝ}
    {P P' : Partition s t} (hPP' : P'.IsRefinement P) :
    P'.mesh ≤ P.mesh := by
  have hst : s ≤ t :=
    calc s = P.pts ⟨0, by omega⟩ := P.first.symm
      _ ≤ P.pts ⟨P.n, by omega⟩ := P.mono (by grind only [= Lean.Grind.toInt_fin])
      _ = t := P.last
  by_cases hP'n : P'.n = 0
  · -- mesh(P') = 0
    simp only [Partition.mesh, dif_pos hP'n]
    split_ifs with h
    · exact le_refl 0
    · exact Finset.le_sup'_of_le _
        (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero h⟩)
        (sub_nonneg.mpr (P.left_le_right _))
  · by_cases hPn : P.n = 0
    · -- s = t, all points collapse
      have hst_eq : s = t := by
        have : (⟨0, by omega⟩ : Fin (P.n + 1)) = ⟨P.n, by omega⟩ :=
          Fin.ext (by omega)
        linarith [P.first, P.last, congrArg P.pts this]
      have hpts_eq : ∀ i : Fin (P'.n + 1), P'.pts i = s := by
        intro i
        have h1 : s ≤ P'.pts i :=
          calc s = P'.pts ⟨0, by omega⟩ := P'.first.symm
            _ ≤ P'.pts i := P'.mono (Fin.zero_le i)
        have h2 : P'.pts i ≤ s :=
          calc P'.pts i ≤ P'.pts ⟨P'.n, by omega⟩ := P'.mono (Fin.le_last i)
            _ = t := P'.last
            _ = s := hst_eq.symm
        linarith
      simp only [Partition.mesh, dif_neg hP'n, dif_pos hPn]
      apply Finset.sup'_le _ _
      intro i _
      simp only [Partition.right, Partition.left]
      rw [hpts_eq ⟨i.val + 1, by omega⟩, hpts_eq ⟨i.val, by omega⟩]
      simp
    · -- Main case: P.n > 0, P'.n > 0
      obtain ⟨φ, hφ_val, hφ_mono, hφ_start, hφ_end⟩ :=
        Partition.IsRefinement.mono_embed hPP' (Nat.pos_of_ne_zero hPn)
      simp only [Partition.mesh, dif_neg hP'n, dif_neg hPn]
      apply Finset.sup'_le _ _
      intro j _
      -- BUCKET FINDING: find k : Fin P.n with φ(k) ≤ j < φ(k+1)
      set S := Finset.univ.filter
        (fun k : Fin P.n => (φ ⟨k.val, by omega⟩).val ≤ j.val)
      have hS_ne : S.Nonempty := by
        refine ⟨⟨0, Nat.pos_of_ne_zero hPn⟩, ?_⟩
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        show (φ ⟨0, by omega⟩).val ≤ j.val
        rw [show (φ ⟨0, by omega⟩) = ⟨0, by omega⟩ from hφ_start]
        exact Nat.zero_le ↑j
      set k := S.max' hS_ne
      have hk_left : (φ ⟨k.val, by omega⟩).val ≤ j.val :=
        (Finset.mem_filter.mp (Finset.max'_mem S hS_ne)).2
      have hk_right : j.val + 1 ≤ (φ ⟨k.val + 1, by omega⟩).val := by
        by_contra h; push_neg at h
        have hle : (φ ⟨k.val + 1, by omega⟩).val ≤ j.val := by omega
        by_cases hk1 : k.val + 1 < P.n
        · have hmem : (⟨k.val + 1, hk1⟩ : Fin P.n) ∈ S := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hle
          have := Finset.le_max' S ⟨k.val + 1, hk1⟩ hmem
          grind only [= Lean.Grind.toInt_fin]
        · have : k.val + 1 = P.n := by omega
          have := congrArg Fin.val hφ_end
          grind => lia
      -- INTERVAL CONTAINMENT
      calc P'.right j - P'.left j
          = P'.pts ⟨j.val + 1, by omega⟩ - P'.pts ⟨j.val, by omega⟩ := rfl
        _ ≤ P'.pts (φ ⟨k.val + 1, by omega⟩) -
              P'.pts (φ ⟨k.val, by omega⟩) :=
            sub_le_sub (P'.mono hk_right) (P'.mono hk_left)
        _ = P.pts ⟨k.val + 1, by omega⟩ - P.pts ⟨k.val, by omega⟩ := by
            rw [hφ_val ⟨k.val + 1, by omega⟩, hφ_val ⟨k.val, by omega⟩]
        _ = P.right k - P.left k := rfl
        _ ≤ Finset.sup' Finset.univ _
              (fun i : Fin P.n => P.right i - P.left i) :=
            Finset.le_sup' (fun i : Fin P.n => P.right i - P.left i)
              (Finset.mem_univ k)

end PartitionRefinement

end StochCalc
