/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerTwo/RightPe.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.Defs
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.Condition

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

/-! ### Right-peeling telescoping -/

section RightPeel

/-- Helper: right-peeling identity with ℕ-indexed functions and range sums. -/
lemma right_peel_range (Ξ : ℝ → ℝ → E) (hΞ : ∀ s, Ξ s s = 0)
    (f : ℕ → ℝ) : ∀ m : ℕ,
    Ξ (f 0) (f m) - ∑ j ∈ Finset.range m, Ξ (f j) (f (j + 1)) =
    ∑ j ∈ Finset.range (m - 1),
      sewingDefect₁ Ξ (f 0) (f (j + 1)) (f (j + 2)) := by
  intro m; induction m with
  | zero => simp [hΞ]
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.succ_sub_one]
    -- Rearrange: peel off last Ξ-term, expose defect + IH
    have key : Ξ (f 0) (f (m + 1)) -
        (∑ j ∈ Finset.range m, Ξ (f j) (f (j + 1)) + Ξ (f m) (f (m + 1))) =
      (Ξ (f 0) (f m) - ∑ j ∈ Finset.range m, Ξ (f j) (f (j + 1))) +
        sewingDefect₁ Ξ (f 0) (f m) (f (m + 1)) := by
      simp only [sewingDefect₁]; abel
    rw [key, ih]
    -- Remains: ∑_{<m-1} δΞ + δΞ(f0,fm,f(m+1)) = ∑_{<m} δΞ
    cases m with
    | zero => simp [sewingDefect₁, hΞ]
    | succ m' => rw [Nat.succ_sub_one, ← Finset.sum_range_succ]

/-- **Right-peeling telescoping identity**: for a monotone sequence
`q : Fin (m+1) → ℝ` with `q(0) = a`, `q(m) = c`, we have

  `Ξ(a,c) - ∑_{j<m} Ξ(qⱼ, qⱼ₊₁) = ∑_{j<m-1} δΞ(a, q(j+1), q(j+2))`

The name "right-peeling" reflects that we peel off terms from the RIGHT:
  `Ξ(a,c) = Ξ(a,qₘ₋₁) + Ξ(qₘ₋₁,c) + δΞ(a,qₘ₋₁,c)`
then recurse on `Ξ(a,qₘ₋₁)`. This keeps the LEFT endpoint `a` fixed in
every defect term, which is what makes the product bound work. -/
theorem right_peel_telescope (Ξ : ℝ → ℝ → E) (hΞ : ∀ s, Ξ s s = 0)
    {m : ℕ} (q : Fin (m + 1) → ℝ) :
    Ξ (q ⟨0, by omega⟩) (q ⟨m, by omega⟩) -
      ∑ j : Fin m, Ξ (q ⟨j, by omega⟩) (q ⟨↑j + 1, by omega⟩) =
    ∑ j : Fin (m - 1),
      sewingDefect₁ Ξ (q ⟨0, by omega⟩) (q ⟨↑j + 1, by omega⟩)
        (q ⟨↑j + 2, by omega⟩) := by
  -- Extend q to ℕ → ℝ via clamping
  set f : ℕ → ℝ := fun i => q ⟨min i m, by omega⟩
  have hv : ∀ (i : ℕ) (hi : i ≤ m), f i = q ⟨i, by omega⟩ := fun i hi => by
    simp only [f, Nat.min_eq_left hi]
  -- Apply the range-sum helper
  have h := right_peel_range Ξ hΞ f m
  -- Bridge: rewrite endpoints
  rw [hv 0 (Nat.zero_le m), hv m le_rfl] at h
  -- Bridge: match the Fin sums with the range sums
  have hsub : ∑ j : Fin m, Ξ (q ⟨↑j, by omega⟩) (q ⟨↑j + 1, by omega⟩) =
      ∑ j ∈ Finset.range m, Ξ (f j) (f (j + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => Ξ (f j) (f (j + 1)))]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hv j.val (by omega), hv (j.val + 1) (by omega)]
  have hdef : ∑ j : Fin (m - 1),
      sewingDefect₁ Ξ (q ⟨0, by omega⟩) (q ⟨↑j + 1, by omega⟩) (q ⟨↑j + 2, by omega⟩) =
      ∑ j ∈ Finset.range (m - 1),
        sewingDefect₁ Ξ (f 0) (f (j + 1)) (f (j + 2)) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => sewingDefect₁ Ξ (f 0) (f (j + 1)) (f (j + 2)))]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hv 0 (Nat.zero_le m), hv (j.val + 1) (by omega), hv (j.val + 2) (by omega)]
  rw [hsub, hdef]; exact h

end RightPeel
end StochCalc
