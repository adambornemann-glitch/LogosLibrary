/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerThree/Partition.lean
-/
import LogosLibrary.StochasticCalculus.SewingLemma.Defs
import LogosLibrary.StochasticCalculus.SewingLemma.Condition

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

/-! ### Partitions -/

section Partition

/-- Each sub-interval is well-ordered. -/
theorem Partition.left_le_right {s t : ℝ} (P : Partition s t) (i : Fin P.n) :
    P.left i ≤ P.right i :=
  P.mono (by grind only [= Lean.Grind.toInt_fin] : (⟨i.val, _⟩ : Fin (P.n + 1)) ≤ ⟨i.val + 1, _⟩)

/-- Partition points lie in `[s, t]` when `s ≤ t`. -/
theorem Partition.mem_Icc {s t : ℝ} (P : Partition s t) (_hst : s ≤ t)
    (i : Fin (P.n + 1)) :
    P.pts i ∈ Icc s t := by
  refine ⟨?_, ?_⟩
  · calc s = P.pts ⟨0, _⟩ := P.first.symm
      _ ≤ P.pts i := P.mono (Fin.zero_le i)
  · calc P.pts i ≤ P.pts ⟨P.n, _⟩ := P.mono (Fin.le_last i)
      _ = t := P.last

/-- The Riemann sum of the trivial partition is just `Ξ(s, t)`. -/
theorem riemannSum_trivial (Ξ : ℝ → ℝ → E) (s t : ℝ) (hst : s ≤ t) :
    riemannSum Ξ (Partition.trivial s t hst) = Ξ s t := by
  simp [riemannSum, Partition.trivial, Partition.left, Partition.right,
        Matrix.cons_val_zero, Matrix.cons_val_one]

end Partition

end StochCalc
