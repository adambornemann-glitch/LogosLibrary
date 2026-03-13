/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerThree/ContinuousCost.lean
-/
import LogosLibrary.StochasticCalculus.SewingLemma.Defs
import LogosLibrary.StochasticCalculus.SewingLemma.Condition

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

section ContinuousControl

/-- Super-additivity implies monotonicity: `ω(s, t) ≤ ω(s', t')` for `[s,t] ⊆ [s',t']`. -/
theorem ContControl.mono {ω : ℝ → ℝ → ℝ} {a b : ℝ}
    (hω : ContControl ω a b) {s s' t t' : ℝ}
    (has : a ≤ s') (hs : s' ≤ s) (hst : s ≤ t) (ht : t ≤ t') (htb : t' ≤ b) :
    ω s t ≤ ω s' t' := by
  -- ω(s,t) ≤ ω(s,t) + ω(t,t') ≤ ω(s,t') ≤ ω(s',s) + ω(s,t') ≤ ω(s',t')
  calc ω s t
      ≤ ω s t + ω t t' :=
        le_add_of_nonneg_right
          (hω.nonneg t t' (has.trans (hs.trans hst)) ht htb)
    _ ≤ ω s t' := hω.superadd s t t' (has.trans hs) hst ht htb
    _ ≤ ω s' s + ω s t' :=
        le_add_of_nonneg_left
          (hω.nonneg s' s has hs (hst.trans (ht.trans htb)))
    _ ≤ ω s' t' := hω.superadd s' s t' has hs (hst.trans ht) htb

/-- Helper: super-additivity telescopes over any monotone sequence.
    `∑_{i<n} ω(f(i), f(i+1)) ≤ ω(f(0), f(n))` -/
private lemma ContControl.range_sum_le {ω : ℝ → ℝ → ℝ} {a b : ℝ}
    (hω : ContControl ω a b) :
    ∀ (n : ℕ) {f : ℕ → ℝ}, Monotone f → a ≤ f 0 → f n ≤ b →
      ∑ i ∈ Finset.range n, ω (f i) (f (i + 1)) ≤ ω (f 0) (f n) := by
  intro n; induction n with
  | zero =>
    intro f _ _ _; simp; exact le_of_eq (hω.diag _).symm
  | succ m ih =>
    intro f hf hfa hfb
    rw [Finset.sum_range_succ]
    calc (∑ i ∈ Finset.range m, ω (f i) (f (i + 1))) + ω (f m) (f (m + 1))
        ≤ ω (f 0) (f m) + ω (f m) (f (m + 1)) := by
          gcongr; exact ih hf hfa ((hf (Nat.le_succ m)).trans hfb)
      _ ≤ ω (f 0) (f (m + 1)) :=
          hω.superadd _ _ _ hfa (hf (Nat.zero_le m)) (hf (Nat.le_succ m)) hfb

/-- Super-additivity iterates over partitions: `∑ᵢ ω(tᵢ, tᵢ₊₁) ≤ ω(s, t)`. -/
theorem ContControl.sum_le {ω : ℝ → ℝ → ℝ} {a b : ℝ}
    (hω : ContControl ω a b) {s t : ℝ} (has : a ≤ s) (htb : t ≤ b)
    (P : Partition s t) :
    ∑ i : Fin P.n, ω (P.left i) (P.right i) ≤ ω s t := by
  set f : ℕ → ℝ := fun k => P.pts ⟨min k P.n, by omega⟩ with hf_def
  have hf_mono : Monotone f := fun i j hij => P.mono (min_le_min_right P.n hij)
  have hf0 : f 0 = s := P.first
  have hfn : f P.n = t := by simp [f, P.last]
  -- For i ≤ P.n, f(i) = P.pts(i) (the min clamp is inactive)
  have hf_val : ∀ i (hi : i ≤ P.n), f i = P.pts ⟨i, Nat.lt_succ_of_le hi⟩ := by
    intro i hi
    show P.pts ⟨min i P.n, _⟩ = P.pts ⟨i, _⟩
    congr 1; ext; exact Nat.min_eq_left hi
  -- Each partition term matches the f-based term
  have hterm : ∀ i : Fin P.n,
      ω (P.left i) (P.right i) = ω (f i.val) (f (i.val + 1)) := by
    intro ⟨i, hi⟩
    simp only [Partition.left, Partition.right]
    rw [hf_val i (by omega), hf_val (i + 1) (by omega)]
  calc ∑ i : Fin P.n, ω (P.left i) (P.right i)
      = ∑ i : Fin P.n, ω (f i.val) (f (i.val + 1)) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ ≤ ω (f 0) (f P.n) := by
        rw [Fin.sum_univ_eq_sum_range (fun k => ω (f k) (f (k + 1)))]
        exact hω.range_sum_le P.n hf_mono
          (has.trans hf0.symm.le) (hfn.le.trans htb)
    _ = ω s t := by rw [hf0, hfn]


end ContinuousControl

end StochCalc
