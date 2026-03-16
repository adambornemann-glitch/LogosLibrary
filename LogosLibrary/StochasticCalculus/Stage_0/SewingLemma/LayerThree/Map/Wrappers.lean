/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerThree/Map/Wrapper.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.MinSpacing
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.Map.MultiBlock
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.MergeGap


noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

section Wrappers

theorem merge_gap_of_min_spacing_mono {s t : ℝ} (P₁ P₂ : Partition s t)
    (hP₁n : 0 < P₁.n)
    (φ : Fin (P₁.n + 1) → Fin ((P₁.merge P₂).n + 1))
    (hφ_val : ∀ i, (P₁.merge P₂).pts (φ i) = P₁.pts i)
    (hφ_mono : Monotone φ)
    (_hφ_start : φ ⟨0, by omega⟩ = ⟨0, by omega⟩)
    (_hφ_end : φ ⟨P₁.n, by omega⟩ = ⟨(P₁.merge P₂).n, by omega⟩)
    {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L)
    (hP₂_sep : ∀ i j : Fin (P₂.n + 1), P₂.pts i < P₂.pts j →
      h ≤ P₂.pts j - P₂.pts i)
    (hP₁_block : ∀ k : Fin P₁.n, P₁.right k - P₁.left k ≤ L)
    (k : Fin P₁.n) :
    (φ ⟨k.val + 1, by omega⟩).val - (φ ⟨k.val, by omega⟩).val ≤
      Nat.floor (L / h) + 2 := by
  by_cases h_eq : P₁.pts ⟨k.val, by omega⟩ = P₁.pts ⟨k.val + 1, by omega⟩
  · have hφ_eq : φ ⟨k.val, by omega⟩ = φ ⟨k.val + 1, by omega⟩ := by
      by_contra hne
      have hlt : (φ ⟨k.val, by omega⟩) < (φ ⟨k.val + 1, by omega⟩) :=
        lt_of_le_of_ne
          (hφ_mono (show (⟨k.val, _⟩ : Fin (P₁.n + 1)) ≤ ⟨k.val + 1, _⟩
            from Fin.mk_le_mk.mpr (by omega)))
          hne
      have := Partition.merge_pts_strict_mono P₁ P₂ hlt
      rw [hφ_val, hφ_val] at this
      linarith
    show (φ ⟨k.val + 1, by omega⟩).val - (φ ⟨k.val, by omega⟩).val ≤ _
    rw [show (φ ⟨k.val + 1, by omega⟩).val = (φ ⟨k.val, by omega⟩).val
      from congrArg Fin.val hφ_eq.symm]
    omega
  · exact merge_gap_of_min_spacing P₁ P₂ hP₁n φ hφ_val hφ_mono
      _hφ_start _hφ_end hh hL hP₂_sep hP₁_block k
      (mono_embed_strict_step hφ_val hφ_mono ⟨k.val, by omega⟩
        (lt_of_le_of_ne (P₁.mono (Fin.mk_le_mk.mpr (by omega))) h_eq))


theorem refinement_gap_with_exceptions_mono
    {s t : ℝ} {P₁ P₂ P' : Partition s t}
    (hP₁n : 0 < P₁.n)
    (hP'_strict : ∀ {i j : Fin (P'.n + 1)}, i < j → P'.pts i < P'.pts j)
    (hP'_union : ∀ j : Fin (P'.n + 1),
      (∃ i : Fin (P₁.n + 1), P'.pts j = P₁.pts i) ∨
      (∃ i : Fin (P₂.n + 1), P'.pts j = P₂.pts i))
    (φ : Fin (P₁.n + 1) → Fin (P'.n + 1))
    (hφ_val : ∀ i, P'.pts (φ i) = P₁.pts i)
    (hφ_mono : Monotone φ)
    (hφ_start : φ ⟨0, by omega⟩ = ⟨0, by omega⟩)
    (hφ_end : φ ⟨P₁.n, by omega⟩ = ⟨P'.n, by omega⟩)
    {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L)
    (good : Finset (Fin (P₂.n + 1)))
    (hgood_sep : ∀ i ∈ good, ∀ j ∈ good, P₂.pts i < P₂.pts j →
      h ≤ P₂.pts j - P₂.pts i)
    {m : ℕ} (hbad : (Finset.univ \ good).card ≤ m)
    (hP₁_block : ∀ k : Fin P₁.n, P₁.right k - P₁.left k ≤ L)
    (k : Fin P₁.n) :
    (φ ⟨k.val + 1, by omega⟩).val - (φ ⟨k.val, by omega⟩).val ≤
      Nat.floor (L / h) + m + 2 := by
  by_cases h_eq : P₁.pts ⟨k.val, by omega⟩ = P₁.pts ⟨k.val + 1, by omega⟩
  · have hφ_eq : φ ⟨k.val, by omega⟩ = φ ⟨k.val + 1, by omega⟩ := by
      by_contra hne
      have hlt := lt_of_le_of_ne
        (hφ_mono (Fin.mk_le_mk.mpr (by omega))) hne
      have := hP'_strict hlt
      rw [hφ_val, hφ_val] at this; linarith
    rw [show (φ ⟨k.val + 1, by omega⟩).val = (φ ⟨k.val, by omega⟩).val
      from congrArg Fin.val hφ_eq.symm]; omega
  · exact refinement_gap_with_exceptions hP₁n hP'_strict hP'_union
      φ hφ_val hφ_mono hφ_start hφ_end hh hL good hgood_sep hbad hP₁_block k
      (mono_embed_strict_step hφ_val hφ_mono ⟨k.val, by omega⟩
        (lt_of_le_of_ne (P₁.mono (Fin.mk_le_mk.mpr (by omega))) h_eq))


end StochCalc.Wrappers
