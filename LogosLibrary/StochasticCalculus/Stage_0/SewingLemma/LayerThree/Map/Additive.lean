/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerThree/Map/Additive.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.Map.RightComp

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc
section Additivity

/-! ### Main theorem: General additivity (Layer 3) -/

theorem sewingMap₃_additive [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    sewingMap₃ Ξ ω θ K a b hΞ s t =
      sewingMap₃ Ξ ω θ K a b hΞ s u + sewingMap₃ Ξ ω θ K a b hΞ u t := by
  set I := sewingMap₃ Ξ ω θ K a b hΞ
  have hst : s ≤ t := hsu.trans hut
  -- Degenerate cases
  by_cases hsu_eq : s = u
  · subst hsu_eq
    have : I s s = 0 := sewingMap₃_diag hΞ has (hut.trans htb)
    rw [this, zero_add]
  by_cases hut_eq : u = t
  · subst hut_eq
    have : I u u = 0 := sewingMap₃_diag hΞ (has.trans hsu) htb
    rw [this, add_zero]
  have hsu_strict : s < u := lt_of_le_of_ne hsu hsu_eq
  have hut_strict : u < t := lt_of_le_of_ne hut hut_eq
  -- Setup: insertAt partitions
  set D := fun n => dyadicPartition s t hst n
  set hDn := fun n => (show 0 < (D n).n from by show 0 < 2 ^ n; positivity)
  set k := fun n => (D n).findBlock u hsu hut (hDn n)
  set hl := fun n => (D n).findBlock_left_le u hsu hut (hDn n)
  set hr := fun n => (D n).findBlock_right_ge u hsu hut (hDn n)
  set Q := fun n => (D n).insertAt (k n) u (hl n) (hr n)
  set idx := fun n => insertAt_u_index (D n) (k n)
  set hu_spec := fun n => insertAt_u_index_spec (D n) (k n) u (hl n) (hr n)
  set QL := fun n => (Q n).restrictLeftAt (idx n) u (hu_spec n) hsu
  set QR := fun n => (Q n).restrictRightAt (idx n) u (hu_spec n) hut
  -- Step 1: RS(Q_n) → I(s,t)
  have hRS_Q_tendsto : Tendsto (fun n => riemannSum Ξ (Q n)) atTop (nhds (I s t)) :=
    riemannSum_insertAt_tendsto hΞ has hst htb hsu hut
  -- Step 2: RS(Q_n) = RS(QL_n) + RS(QR_n)
  have hRS_split : ∀ n, riemannSum Ξ (Q n) =
      riemannSum Ξ (QL n) + riemannSum Ξ (QR n) :=
    fun n => riemannSum_splitAt (Q n) (idx n) u hsu (hu_spec n) hut
  -- Step 3: RS(QL_n) → I(s,u)
  have hRS_QL_tendsto : Tendsto (fun n => riemannSum Ξ (QL n)) atTop (nhds (I s u)) := by
    have hcomp : Tendsto (fun n => riemannSum Ξ (QL n) - dyadicSum₁ Ξ s u n)
        atTop (nhds 0) :=
      left_comparison_tendsto hΞ has hsu hut htb hsu_strict
    have hdyadic := sewingMap₃_tendsto hΞ has hsu (hut.trans htb)
    have : (fun n => riemannSum Ξ (QL n)) =
        (fun n => (riemannSum Ξ (QL n) - dyadicSum₁ Ξ s u n) + dyadicSum₁ Ξ s u n) :=
      funext fun n => by abel
    rw [this, show I s u = 0 + I s u from (zero_add _).symm]
    exact hcomp.add hdyadic
  have hRS_QR_tendsto : Tendsto (fun n => riemannSum Ξ (QR n)) atTop (nhds (I u t)) := by
    have hcomp : Tendsto (fun n => riemannSum Ξ (QR n) - dyadicSum₁ Ξ u t n)
        atTop (nhds 0) :=
      right_comparison_tendsto hΞ has hsu hut htb hut_strict
    have hdyadic := sewingMap₃_tendsto hΞ (has.trans hsu) hut htb
    have : (fun n => riemannSum Ξ (QR n)) =
        (fun n => (riemannSum Ξ (QR n) - dyadicSum₁ Ξ u t n) + dyadicSum₁ Ξ u t n) :=
      funext fun n => by abel
    rw [this, show I u t = 0 + I u t from (zero_add _).symm]
    exact hcomp.add hdyadic
  -- Step 5: RS(Q_n) = RS(QL_n) + RS(QR_n) → I(s,u) + I(u,t)
  have hRS_sum_tendsto :
      Tendsto (fun n => riemannSum Ξ (Q n)) atTop (nhds (I s u + I u t)) := by
    have : (fun n => riemannSum Ξ (Q n)) =
        (fun n => riemannSum Ξ (QL n) + riemannSum Ξ (QR n)) :=
      funext hRS_split
    rw [this]; exact hRS_QL_tendsto.add hRS_QR_tendsto
  -- Step 6: Uniqueness of limits
  exact tendsto_nhds_unique hRS_Q_tendsto hRS_sum_tendsto


end Additivity
end StochCalc
