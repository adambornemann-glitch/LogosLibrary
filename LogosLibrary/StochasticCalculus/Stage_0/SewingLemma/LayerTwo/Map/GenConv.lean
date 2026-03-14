/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: LayerTwo/Map/GenConv.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.Map.Additive

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

/-! ### Comparison and general convergence -/

section GeneralConvergence₂


/-- **General convergence**: any sequence of partitions with mesh → 0
has Riemann sums converging to `sewingMap₂`.

Proof: fix ε > 0. Choose N₁ with ‖RS(Dₙ) - I‖ < ε/3 for n ≥ N₁.
Choose δ from `crossEnergy₂_tendsto_zero` with CE < ε/(3K) when mesh < δ.
Choose N₂ with mesh(Pₙ) < δ and mesh(Dₙ) < δ for n ≥ N₂.
Compare: ‖RS(Pₙ) - RS(Dₙ)‖ ≤ K·(CE(Pₙ)+CE(Dₙ)) < 2ε/3.
So ‖RS(Pₙ) - I‖ < ε. -/
theorem riemannSum_tendsto_sewingMap₂ [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K L₁ L₂ a b : ℝ}
    (hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (P : ℕ → Partition s t)
    (hmesh : Tendsto (fun n => (P n).mesh) atTop (nhds 0)) :
    Tendsto (fun n => riemannSum Ξ (P n)) atTop
      (nhds (sewingMap₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b hΞ s t)) := by
  set I := sewingMap₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b hΞ
  set C' := K * L₁ ^ α * L₂ ^ β * sewingConst₂ α β * (2 : ℝ)⁻¹ ^ (α + β)
  have hαβ1 : 0 < α + β - 1 := by linarith [hΞ.one_lt_exp]
  have hαβ : 0 < α + β := by linarith
  have hC'_nn : 0 ≤ C' := by
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg hΞ.K_nonneg (rpow_nonneg hΞ.L₁_nonneg _)
        · exact rpow_nonneg hΞ.L₂_nonneg _
      · exact (sewingConst₂_pos hΞ.one_lt_exp).le
    · exact rpow_nonneg (by positivity) _
  have hts : 0 ≤ t - s := sub_nonneg.mpr hst
  have mesh_nn : ∀ (Q : Partition s t), 0 ≤ Q.mesh := by
    intro Q; simp only [Partition.mesh]; split_ifs with h
    · exact le_refl 0
    · exact le_trans (sub_nonneg.mpr (Q.left_le_right ⟨0, Nat.pos_of_ne_zero h⟩))
        (Finset.le_sup' (fun i : Fin Q.n => Q.right i - Q.left i)
          (Finset.mem_univ (⟨0, Nat.pos_of_ne_zero h⟩ : Fin Q.n)))
  -- I telescopes via range sum (induction on length)
  have hI_tel : ∀ (m : ℕ) (f : ℕ → ℝ), Monotone f → a ≤ f 0 → f m ≤ b →
      I (f 0) (f m) = ∑ k ∈ Finset.range m, I (f k) (f (k + 1)) := by
    intro m; induction m with
    | zero =>
      intro f _ hfa hfb
      simp only [Finset.sum_range_zero]
      exact sewingMap₂_diag hΞ hfa hfb
    | succ m ih =>
      intro f hf hfa hfb
      rw [Finset.sum_range_succ, ← ih f hf hfa ((hf (Nat.le_succ m)).trans hfb)]
      exact sewingMap₂_additive hΞ hfa (hf (Nat.zero_le m)) (hf (Nat.le_succ m)) hfb
  -- I telescopes over partitions (Fin version)
  have hI_partition : ∀ (Q : Partition s t),
      I s t = ∑ i : Fin Q.n, I (Q.left i) (Q.right i) := by
    intro Q
    set f : ℕ → ℝ := fun k => Q.pts ⟨min k Q.n, by omega⟩
    have hf_mono : Monotone f := fun i j hij => Q.mono (min_le_min_right Q.n hij)
    have hf0 : f 0 = s := Q.first
    have hfn : f Q.n = t := by simp [f, Q.last]
    have hf_val : ∀ (k : ℕ) (hk : k ≤ Q.n), f k = Q.pts ⟨k, by omega⟩ :=
      fun k hk => by show Q.pts ⟨min k Q.n, _⟩ = _; congr 1; ext; exact Nat.min_eq_left hk
    have hfa : a ≤ f 0 := by rw [hf0]; exact has
    have hfb : f Q.n ≤ b := by rw [hfn]; exact htb
    have htel := hI_tel Q.n f hf_mono hfa hfb
    rw [hf0, hfn] at htel
    rw [htel, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun ⟨k, hk⟩ _ => by
      simp only [Partition.left, Partition.right]
      rw [hf_val k (by omega), hf_val (k + 1) (by omega)]
  -- Interval lengths sum to t - s
  have hlen_sum : ∀ (Q : Partition s t),
      ∑ i : Fin Q.n, (Q.right i - Q.left i) = t - s := by
    intro Q
    set f : ℕ → ℝ := fun k => Q.pts ⟨min k Q.n, by omega⟩
    have hf_val : ∀ (k : ℕ) (hk : k ≤ Q.n), f k = Q.pts ⟨k, by omega⟩ :=
      fun k hk => by show Q.pts ⟨min k Q.n, _⟩ = _; congr 1; ext; exact Nat.min_eq_left hk
    have hfin_eq : ∑ i : Fin Q.n, (Q.right i - Q.left i) =
        ∑ k ∈ Finset.range Q.n, (f (k + 1) - f k) := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun ⟨k, hk⟩ _ => by
        simp only [Partition.right, Partition.left]
        rw [hf_val (k + 1) (by omega), hf_val k (by omega)]
    rw [hfin_eq, Finset.sum_range_sub]
    simp [f, Q.last]
    exact Q.first
  -- Main bound: ‖RS(Q) - I(s,t)‖ ≤ C' · mesh^{α+β-1} · (t-s)
  have hbound : ∀ (Q : Partition s t),
      ‖riemannSum Ξ Q - I s t‖ ≤ C' * Q.mesh ^ (α + β - 1) * (t - s) := by
    intro Q
    rw [hI_partition Q]
    simp only [riemannSum]
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ i : Fin Q.n, (Ξ (Q.left i) (Q.right i) - I (Q.left i) (Q.right i))‖
        ≤ ∑ i : Fin Q.n, ‖Ξ (Q.left i) (Q.right i) - I (Q.left i) (Q.right i)‖ :=
          norm_sum_le _ _
      _ = ∑ i : Fin Q.n, ‖I (Q.left i) (Q.right i) - Ξ (Q.left i) (Q.right i)‖ := by
          congr 1; ext i; exact norm_sub_rev _ _
      _ ≤ ∑ i : Fin Q.n, C' * |Q.right i - Q.left i| ^ (α + β) := by
          gcongr with i
          exact sewingMap₂_dist_le hΞ
            (has.trans (Q.mem_Icc hst ⟨i.val, by omega⟩).1)
            (Q.left_le_right i)
            ((Q.mem_Icc hst ⟨i.val + 1, by omega⟩).2.trans htb)
      _ = ∑ i : Fin Q.n, C' * (Q.right i - Q.left i) ^ (α + β) := by
          congr 1; ext i; rw [abs_of_nonneg (sub_nonneg.mpr (Q.left_le_right i))]
      _ ≤ ∑ i : Fin Q.n, C' * (Q.mesh ^ (α + β - 1) * (Q.right i - Q.left i)) := by
          gcongr with i
          have hlen_nn : 0 ≤ Q.right i - Q.left i := sub_nonneg.mpr (Q.left_le_right i)
          have hlen_mesh : Q.right i - Q.left i ≤ Q.mesh := by
            simp only [Partition.mesh]
            split_ifs with h
            · exact absurd i.isLt (by omega)
            · exact Finset.le_sup' (fun j : Fin Q.n => Q.right j - Q.left j)
                (Finset.mem_univ i)
          calc (Q.right i - Q.left i) ^ (α + β)
              = (Q.right i - Q.left i) ^ (α + β - 1 + 1) := by
                congr 1; ring
            _ = (Q.right i - Q.left i) ^ (α + β - 1) *
                (Q.right i - Q.left i) ^ (1 : ℝ) :=
                rpow_add' hlen_nn (by linarith : α + β - 1 + 1 ≠ 0)
            _ = (Q.right i - Q.left i) ^ (α + β - 1) *
                (Q.right i - Q.left i) := by rw [rpow_one]
            _ ≤ Q.mesh ^ (α + β - 1) * (Q.right i - Q.left i) := by
                gcongr
      _ = C' * Q.mesh ^ (α + β - 1) * ∑ i : Fin Q.n, (Q.right i - Q.left i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = C' * Q.mesh ^ (α + β - 1) * (t - s) := by rw [hlen_sum Q]
  -- Conclude: mesh → 0 implies RS → I
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_cases hCts : C' * (t - s) = 0
  · use 0; intro n _
    rw [dist_eq_norm]
    calc ‖riemannSum Ξ (P n) - I s t‖
        ≤ C' * (P n).mesh ^ (α + β - 1) * (t - s) := hbound (P n)
      _ = C' * (t - s) * (P n).mesh ^ (α + β - 1) := by ring
      _ = 0 := by rw [hCts, zero_mul]
      _ < ε := hε
  · have hCts_pos : 0 < C' * (t - s) :=
      lt_of_le_of_ne (mul_nonneg hC'_nn hts) (Ne.symm hCts)
    set δ := (ε / (C' * (t - s))) ^ (α + β - 1)⁻¹
    have hδ_pos : 0 < δ := rpow_pos_of_pos (div_pos hε hCts_pos) _
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hmesh) δ hδ_pos
    use N; intro n hn
    rw [dist_eq_norm]
    have hmesh_bound : (P n).mesh < δ := by
      have := hN n hn
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (mesh_nn _)] at this
    have hC'_pos : 0 < C' :=
      lt_of_le_of_ne hC'_nn (fun h => hCts (by rw [← h, zero_mul]))
    have hts_pos : 0 < t - s :=
      lt_of_le_of_ne hts (fun h => hCts (by rw [← h, mul_zero]))
    calc ‖riemannSum Ξ (P n) - I s t‖
        ≤ C' * (P n).mesh ^ (α + β - 1) * (t - s) := hbound (P n)
      _ < C' * δ ^ (α + β - 1) * (t - s) := by
          apply mul_lt_mul_of_pos_right _ hts_pos
          exact mul_lt_mul_of_pos_left
            (rpow_lt_rpow (mesh_nn _) hmesh_bound hαβ1) hC'_pos
      _ = ε := by
          have hδ_pow : δ ^ (α + β - 1) = ε / (C' * (t - s)) := by
            show ((ε / (C' * (t - s))) ^ (α + β - 1)⁻¹) ^ (α + β - 1) = _
            rw [← rpow_mul (div_nonneg hε.le hCts_pos.le),
                inv_mul_cancel₀ hαβ1.ne', rpow_one]
          rw [hδ_pow, show C' * (ε / (C' * (t - s))) * (t - s) =
              ε / (C' * (t - s)) * (C' * (t - s)) from by ring]
          exact div_mul_cancel₀ ε (ne_of_gt hCts_pos)

end GeneralConvergence₂

end StochCalc
