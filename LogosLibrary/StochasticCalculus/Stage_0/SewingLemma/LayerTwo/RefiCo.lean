/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerTwo/RefiCo.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.RightPe
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.ThetaEnergy
/-!
# The Sewing Lemma — Layer 2 Additivity

General additivity for the Layer 2 (cross-controlled) sewn map:
`I(s,t) = I(s,u) + I(u,t)` for arbitrary `u ∈ [s,t]`.

## Strategy

The proof requires comparing Riemann sums over different partitions, which
in turn requires the **common refinement** (merge) construction and a
**refinement cost bound**. The product structure of the Layer 2 defect bound
`‖δΞ(s,u,t)‖ ≤ K · ω₁(s,u)^α · ω₂(u,t)^β` is essential: it allows
the per-block telescoping cost to collapse via super-additivity, avoiding
the multiplicity issue that blocks the same approach for Layer 3.

## Proof outline

1. **Right-peeling telescoping**: within a sub-partition `{q₀,...,qₘ}` of `[a,c]`,
   `Ξ(a,c) - RS(sub) = ∑_{j≥1} δΞ(a, qⱼ, qⱼ₊₁)`.

2. **Per-block bound**: using the product structure,
   `‖Ξ(a,c) - RS(sub)‖ ≤ K · ω₁(a,c)^α · ω₂(a,c)^β`.
   Key: right-peeling keeps the LEFT endpoint fixed at `a`, so `ω₁(a, qⱼ)^α`
   factors out, and the remaining `∑ ω₂(qⱼ, qⱼ₊₁)^β` contracts by `rpow_add_le`.

3. **Refinement cost**: summing per-block bounds over all P-intervals,
   `‖RS(P) - RS(P')‖ ≤ K · crossEnergy₂(P)`.

4. **Cross-energy vanishes**: for Lipschitz controls, `crossEnergy₂(P) → 0`
   as `mesh(P) → 0`, since `α + β > 1`.

5. **General convergence**: any mesh→0 partition sequence has Riemann sums
   converging to `sewingMap₂`, by comparison with dyadic sums via merge.

6. **Additivity**: insert `u` into dyadic partitions, split at `u`,
   apply general convergence to each half.

## References

* [Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Theorem 2.2][friz2020]
-/

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc
/-! ### Refinement cost (Layer 2) -/

section RefinementCost₂



/-**Single-point insertion**: inserting point `u` into interval `[tₖ, tₖ₊₁]` of
partition `P` changes the Riemann sum by exactly one defect `δΞ(tₖ, u, tₖ₊₁)`.
theorem riemannSum_insert_eq_defect (Ξ : ℝ → ℝ → E) {s t : ℝ}
    (P : Partition s t) (k : Fin P.n) (u : ℝ)
    (hlu : P.left k ≤ u) (hur : u ≤ P.right k) :
    _ := sorry-/

/-- **Single defect bound (Layer 2, Lipschitz)**: each defect `δΞ(s, u, t)` is bounded by
`K · L₁^α · L₂^β · (t - s)^{α + β}`.

This replaces the per-block bound `block_riemannSum_bound₂` (which fails for α, β < 1).
The trick: bound ω₁ and ω₂ via Lipschitz BEFORE raising to powers, so the
individual exponents never matter — only their sum α + β > 1. -/
theorem insertion_defect_bound₂
    {Ξ : ℝ → ℝ → E} {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K L₁ L₂ a b : ℝ}
    (hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    ‖sewingDefect₁ Ξ s u t‖ ≤ K * L₁ ^ α * L₂ ^ β * (t - s) ^ (α + β) := by
  have hts : 0 ≤ t - s := sub_nonneg.mpr (hsu.trans hut)
  have hus : 0 ≤ u - s := sub_nonneg.mpr hsu
  have htu : 0 ≤ t - u := sub_nonneg.mpr hut
  calc ‖sewingDefect₁ Ξ s u t‖
      ≤ K * ω₁ s u ^ α * ω₂ u t ^ β :=
        hΞ.defect_bound s u t has hsu hut htb
    _ ≤ K * (L₁ * (u - s)) ^ α * (L₂ * (t - u)) ^ β := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (rpow_le_rpow
              (hΞ.ω₁_nonneg s u has hsu (hut.trans htb))
              (hΞ.ω₁_lip s u has hsu (hut.trans htb))
              hΞ.α_nonneg)
            hΞ.K_nonneg
        · exact rpow_le_rpow
            (hΞ.ω₂_nonneg u t (has.trans hsu) hut htb)
            (hΞ.ω₂_lip u t (has.trans hsu) hut htb)
            hΞ.β_nonneg
        · exact rpow_nonneg (hΞ.ω₂_nonneg u t (has.trans hsu) hut htb) _
        · exact mul_nonneg hΞ.K_nonneg (rpow_nonneg (mul_nonneg hΞ.L₁_nonneg hus) _)
    _ = K * (L₁ ^ α * (u - s) ^ α) * (L₂ ^ β * (t - u) ^ β) := by
        rw [mul_rpow hΞ.L₁_nonneg hus, mul_rpow hΞ.L₂_nonneg htu]
    _ ≤ K * (L₁ ^ α * (t - s) ^ α) * (L₂ ^ β * (t - s) ^ β) := by
        have h1 : (u - s) ^ α ≤ (t - s) ^ α :=
          rpow_le_rpow hus (by linarith) hΞ.α_nonneg
        have h2 : (t - u) ^ β ≤ (t - s) ^ β :=
          rpow_le_rpow htu (by linarith) hΞ.β_nonneg
        gcongr
        · exact mul_nonneg (rpow_nonneg hΞ.L₂_nonneg _) (rpow_nonneg htu _)
        · exact mul_nonneg hΞ.K_nonneg
            (mul_nonneg (rpow_nonneg hΞ.L₁_nonneg _) (rpow_nonneg hts _))
        · exact hΞ.K_nonneg
        · exact rpow_nonneg hΞ.L₁_nonneg _
        · exact rpow_nonneg hΞ.L₂_nonneg _
    _ = K * L₁ ^ α * L₂ ^ β * ((t - s) ^ α * (t - s) ^ β) := by ring
    _ = K * L₁ ^ α * L₂ ^ β * (t - s) ^ (α + β) := by
        congr 1
        rw [← rpow_add' hts
          (by linarith [hΞ.one_lt_exp] : (0 : ℝ) < α + β).ne']

/-! ### Per-block bound and refinement cost -/

/-- Step-monotone sequences are globally monotone. -/
lemma le_of_step_le (φ : ℕ → ℕ) {n : ℕ}
    (hφ : ∀ k, k < n → φ k ≤ φ (k + 1)) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) : φ i ≤ φ j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    grind only--exact (ih (by omega)).trans (hφ (i + d) (by omega))

/-- Decomposing a range sum into consecutive Ico blocks. -/
lemma finset_sum_Ico_blocks {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (n : ℕ) (φ : ℕ → ℕ) (hφ_step : ∀ k, k < n → φ k ≤ φ (k + 1)) :
    ∑ j ∈ Finset.Ico (φ 0) (φ n), f j =
    ∑ k ∈ Finset.range n, ∑ j ∈ Finset.Ico (φ k) (φ (k + 1)), f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Finset.sum_Ico_consecutive _
          (le_of_step_le φ (fun k hk => hφ_step k (by omega))
            (Nat.zero_le n) le_rfl)
          (hφ_step n (by omega)),
        ih (fun k hk => hφ_step k (by omega)),
        ← Finset.sum_range_succ]

/-- **Per-block bound**: within a monotone sequence of m+1 points, the error
between the single Ξ-term and the Riemann sub-sum is at most (m-1) times
the single-defect Lipschitz bound.

Uses `right_peel_range` to decompose into defects, then bounds each defect
via `insertion_defect_bound₂`. -/
lemma block_bound₂
    {Ξ : ℝ → ℝ → E} {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K L₁ L₂ a b : ℝ}
    (hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b)
    (f : ℕ → ℝ) (hf_mono : Monotone f) (hf_a : a ≤ f 0)
    (m : ℕ) (hf_b : f m ≤ b) :
    ‖Ξ (f 0) (f m) - ∑ j ∈ Finset.range m, Ξ (f j) (f (j + 1))‖ ≤
      ↑(m - 1) * (K * L₁ ^ α * L₂ ^ β *
        (f m - f 0) ^ (α + β)) := by
  rw [right_peel_range Ξ hΞ.vanish_diag f m]
  set C := K * L₁ ^ α * L₂ ^ β * (f m - f 0) ^ (α + β)
  have hC_nn : 0 ≤ C := mul_nonneg
    (mul_nonneg (mul_nonneg hΞ.K_nonneg (rpow_nonneg hΞ.L₁_nonneg _))
      (rpow_nonneg hΞ.L₂_nonneg _))
    (rpow_nonneg (sub_nonneg.mpr (hf_mono (Nat.zero_le m))) _)
  calc ‖∑ j ∈ Finset.range (m - 1),
          sewingDefect₁ Ξ (f 0) (f (j + 1)) (f (j + 2))‖
      ≤ ∑ j ∈ Finset.range (m - 1),
          ‖sewingDefect₁ Ξ (f 0) (f (j + 1)) (f (j + 2))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (m - 1), C := by
        gcongr with j hj
        have hj_lt : j < m - 1 := Finset.mem_range.mp hj
        have h_sub_nn : 0 ≤ f (j + 2) - f 0 :=
          sub_nonneg.mpr (hf_mono (Nat.zero_le _))
        have h_sub_le : f (j + 2) - f 0 ≤ f m - f 0 := by
          linarith [hf_mono (show j + 2 ≤ m by omega)]
        calc ‖sewingDefect₁ Ξ (f 0) (f (j + 1)) (f (j + 2))‖
            ≤ K * L₁ ^ α * L₂ ^ β *
                (f (j + 2) - f 0) ^ (α + β) :=
              insertion_defect_bound₂ hΞ hf_a
                (hf_mono (Nat.zero_le _))
                (hf_mono (by omega : j + 1 ≤ j + 2))
                ((hf_mono (by omega : j + 2 ≤ m)).trans hf_b)
          _ ≤ C :=
              mul_le_mul_of_nonneg_left
                (rpow_le_rpow h_sub_nn h_sub_le
                  (by linarith [hΞ.α_nonneg, hΞ.β_nonneg]))
                (mul_nonneg (mul_nonneg hΞ.K_nonneg
                  (rpow_nonneg hΞ.L₁_nonneg _))
                  (rpow_nonneg hΞ.L₂_nonneg _))
    _ = ↑(m - 1) * C := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Refinement cost (Layer 2)**: for refinement `P'` of `P`,

  `‖RS(P) - RS(P')‖ ≤ P'.n · K · L₁^α · L₂^β · mesh(P)^{α+β}`

Each of the P.n blocks of P contains some sub-intervals of P'.
Right-peeling within each block gives defects, each bounded by
the Lipschitz insertion bound. The total count of defects is ≤ P'.n. -/
theorem riemannSum_refinement_bound₂
    {Ξ : ℝ → ℝ → E} {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K L₁ L₂ a b : ℝ}
    (hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (P P' : Partition s t) (hPP' : P'.IsRefinement P) :
    ‖riemannSum Ξ P - riemannSum Ξ P'‖ ≤
      ↑P'.n * (K * L₁ ^ α * L₂ ^ β * P.mesh ^ (α + β)) := by
  set C := K * L₁ ^ α * L₂ ^ β * P.mesh ^ (α + β)
  have hmesh_nn : 0 ≤ P.mesh := by
    unfold Partition.mesh
    split_ifs with h
    · exact le_refl 0
    · exact Finset.le_sup'_of_le _
        (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero h⟩)
        (sub_nonneg.mpr (P.left_le_right ⟨0, Nat.pos_of_ne_zero h⟩))
  have hC_nn : 0 ≤ C := mul_nonneg
    (mul_nonneg (mul_nonneg hΞ.K_nonneg (rpow_nonneg hΞ.L₁_nonneg _))
      (rpow_nonneg hΞ.L₂_nonneg _))
    (rpow_nonneg hmesh_nn _)
  by_cases hPn : P.n = 0
  · -- Degenerate: P.n = 0 means s = t, all points collapse
    have hst_eq : s = t := le_antisymm hst (by
      have h1 := P.first; have h2 := P.last
      have : (⟨0, by omega⟩ : Fin (P.n + 1)) = ⟨P.n, by omega⟩ := by
        ext; omega
      linarith [congrArg P.pts this])
    subst hst_eq
    -- RS(P) = 0 (empty sum over Fin 0)
    have hRS_P : riemannSum Ξ P = 0 := by
      simp only [riemannSum]
      exact Finset.sum_eq_zero fun i _ => absurd i.isLt (by omega)
    -- All P'-points equal s, so RS(P') = ∑ Ξ(s,s) = 0
    have hP'_pts_eq : ∀ j : Fin (P'.n + 1), P'.pts j = s := by
      intro j
      have h1 : s ≤ P'.pts j :=
        calc s = P'.pts ⟨0, by omega⟩ := P'.first.symm
          _ ≤ P'.pts j := P'.mono (Fin.zero_le j)
      have h2 : P'.pts j ≤ s :=
        calc P'.pts j ≤ P'.pts ⟨P'.n, by omega⟩ := P'.mono (Fin.le_last j)
          _ = s := P'.last
      linarith
    have hRS_P' : riemannSum Ξ P' = 0 := by
      apply Finset.sum_eq_zero; intro i _
      simp only [Partition.left, Partition.right]
      rw [hP'_pts_eq ⟨i.val, by omega⟩,
          hP'_pts_eq ⟨i.val + 1, by omega⟩]
      exact hΞ.vanish_diag s
    rw [hRS_P, hRS_P', sub_self, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hC_nn
  · -- Main case: P.n > 0
    obtain ⟨φ, hφ_val, hφ_mono, hφ_start, hφ_end⟩ :=
      Partition.IsRefinement.mono_embed hPP' (Nat.pos_of_ne_zero hPn)
    -- Clamped extension of P'.pts to ℕ → ℝ
    set g : ℕ → ℝ := fun j => P'.pts ⟨min j P'.n, by omega⟩
    have hg_mono : Monotone g :=
      fun i j hij => P'.mono (min_le_min_right P'.n hij)
    have hg_val : ∀ (j : ℕ) (hj : j ≤ P'.n),
        g j = P'.pts ⟨j, by omega⟩ := by
      intro j hj; show P'.pts ⟨min j P'.n, _⟩ = _
      congr 1; ext; exact Nat.min_eq_left hj
    -- φ as ℕ → ℕ function
    set ψ : ℕ → ℕ := fun k => (φ ⟨min k P.n, by omega⟩).val
    have hψ_step : ∀ k, k < P.n → ψ k ≤ ψ (k + 1) := by
      intro k hk; exact hφ_mono (by grind)
    have hψ_val : ∀ (k : ℕ) (hk : k ≤ P.n),
        ψ k = (φ ⟨k, by omega⟩).val := by
      intro k hk; simp [ψ, Nat.min_eq_left hk]
    have hψ_start : ψ 0 = 0 := by
      rw [hψ_val 0 (Nat.zero_le _)]; exact congrArg Fin.val hφ_start
    have hψ_end : ψ P.n = P'.n := by
      rw [hψ_val P.n le_rfl]; exact congrArg Fin.val hφ_end
    -- g(ψ(k)) = P.pts(k) for k ≤ P.n
    have hg_ψ : ∀ (k : ℕ) (hk : k ≤ P.n),
        g (ψ k) = P.pts ⟨k, by omega⟩ := by
      intro k hk
      have hψk_le : ψ k ≤ P'.n := by
        have := (φ ⟨k, by omega⟩).isLt; rw [hψ_val k hk]; omega
      have : g (ψ k) = P'.pts (φ ⟨k, by omega⟩) := by
        rw [hg_val (ψ k) hψk_le]
        congr 1; ext; exact hψ_val k hk
      rw [this]
      exact hφ_val ⟨k, by omega⟩
    -- Express RS(P') as range sum of g-terms
    set F : ℕ → E := fun j => Ξ (g j) (g (j + 1))
    have hRS_P'_eq : riemannSum Ξ P' = ∑ j ∈ Finset.range P'.n, F j := by
      simp only [riemannSum, F]
      rw [← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun ⟨j, hj⟩ _ => by
        simp only [Partition.left, Partition.right]
        rw [hg_val j (by omega), hg_val (j + 1) (by omega)]
    -- Express RS(P) via g and ψ
    have hRS_P_eq : riemannSum Ξ P =
        ∑ k ∈ Finset.range P.n,
          Ξ (g (ψ k)) (g (ψ (k + 1))) := by
      simp only [riemannSum]
      rw [← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun ⟨k, hk⟩ _ => by
        simp only [Partition.left, Partition.right]
        rw [hg_ψ k (by omega), hg_ψ (k + 1) (by omega)]
    -- Block decomposition: RS(P') splits into Ico blocks aligned with ψ
    have hblock_decomp :
        ∑ j ∈ Finset.range P'.n, F j =
        ∑ k ∈ Finset.range P.n,
          ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), F j := by
      have hrng : Finset.range P'.n = Finset.Ico (ψ 0) (ψ P.n) := by
        rw [hψ_start, hψ_end, Finset.range_eq_Ico]
      rw [hrng]
      exact finset_sum_Ico_blocks F P.n ψ hψ_step
    -- Write RS(P) - RS(P') as sum of block differences
    rw [hRS_P_eq, hRS_P'_eq, hblock_decomp, ← Finset.sum_sub_distrib]
    -- Each block difference: Ξ(g(ψ k), g(ψ(k+1))) - ∑_{Ico} Ξ(g j, g(j+1))
    -- equals Ξ(f_k 0, f_k m_k) - ∑_{range m_k} Ξ(f_k j, f_k(j+1))
    -- where f_k(j) = g(ψ(k) + j) and m_k = ψ(k+1) - ψ(k)
    -- Triangle inequality on blocks, then block_bound₂ + mesh bound
    calc ‖∑ k ∈ Finset.range P.n,
            (Ξ (g (ψ k)) (g (ψ (k + 1))) -
              ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), F j)‖
        ≤ ∑ k ∈ Finset.range P.n,
            ‖Ξ (g (ψ k)) (g (ψ (k + 1))) -
              ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), F j‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range P.n,
            ↑(ψ (k + 1) - ψ k - 1) * C := by
          gcongr with k hk
          have hk_lt := Finset.mem_range.mp hk
          -- Reindex Ico sum to range sum via shift
          set m_k := ψ (k + 1) - ψ k
          set f_k : ℕ → ℝ := fun j => g (ψ k + j)
          have hf_k_mono : Monotone f_k :=
            fun i j hij => hg_mono (by omega)
          have hf_k_0 : f_k 0 = g (ψ k) := by simp [f_k]
          have hf_k_m : f_k m_k = g (ψ (k + 1)) := by
            simp [f_k, m_k, Nat.add_sub_cancel' (hψ_step k hk_lt)]
          have hIco_eq : ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), F j =
              ∑ j ∈ Finset.range m_k, Ξ (f_k j) (f_k (j + 1)) := by
            rw [Finset.sum_Ico_eq_sum_range]
            exact Finset.sum_congr rfl fun j _ => by simp [F, f_k]; rfl
          rw [← hf_k_0, ← hf_k_m, hIco_eq]
          -- Apply block_bound₂
          have hfk_a : a ≤ f_k 0 := by
            rw [hf_k_0, hg_ψ k (by omega)]
            exact has.trans (P.mem_Icc hst ⟨k, by omega⟩).1
          have hfk_b : f_k m_k ≤ b := by
            rw [hf_k_m, hg_ψ (k + 1) (by omega)]
            exact (P.mem_Icc hst ⟨k + 1, by omega⟩).2.trans htb
          calc ‖Ξ (f_k 0) (f_k m_k) -
                  ∑ j ∈ Finset.range m_k, Ξ (f_k j) (f_k (j + 1))‖
              ≤ ↑(m_k - 1) * (K * L₁ ^ α * L₂ ^ β *
                  (f_k m_k - f_k 0) ^ (α + β)) :=
                block_bound₂ hΞ f_k hf_k_mono hfk_a m_k hfk_b
            _ ≤ ↑(m_k - 1) * C := by
                apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
                rw [hf_k_m, hf_k_0, hg_ψ (k + 1) (by omega), hg_ψ k (by omega)]
                apply mul_le_mul_of_nonneg_left
                · apply rpow_le_rpow
                    (sub_nonneg.mpr (P.mono (by grind only [= Lean.Grind.toInt_fin])))
                  · simp only [Partition.mesh, dif_neg hPn, Partition.right, Partition.left]
                    exact Finset.le_sup'
                      (fun i : Fin P.n => P.pts ⟨i.val + 1, by omega⟩ - P.pts ⟨i.val, by omega⟩)
                      (Finset.mem_univ ⟨k, hk_lt⟩)
                  · linarith [hΞ.α_nonneg, hΞ.β_nonneg]
                · exact mul_nonneg (mul_nonneg hΞ.K_nonneg (rpow_nonneg hΞ.L₁_nonneg _))
                    (rpow_nonneg hΞ.L₂_nonneg _)
      _ ≤ ↑P'.n * C := by
          calc ∑ k ∈ Finset.range P.n, ↑(ψ (k + 1) - ψ k - 1) * C
              ≤ ∑ k ∈ Finset.range P.n, ↑(ψ (k + 1) - ψ k) * C := by
                apply Finset.sum_le_sum; intro k _
                exact mul_le_mul_of_nonneg_right
                  (Nat.cast_le.mpr (Nat.sub_le _ _)) hC_nn
            _ = (∑ k ∈ Finset.range P.n, ↑(ψ (k + 1) - ψ k)) * C := by
                rw [Finset.sum_mul]
            _ = ↑P'.n * C := by
                congr 1
                have htel : ∑ k ∈ Finset.range P.n,
                    (ψ (k + 1) - ψ k : ℕ) = P'.n := by
                  suffices h : ∀ m, m ≤ P.n →
                      (∑ k ∈ Finset.range m, (ψ (k + 1) - ψ k)) +
                        ψ 0 = ψ m from by
                    have := h P.n le_rfl
                    rw [hψ_start, hψ_end] at this; omega
                  intro m; induction m with
                  | zero => simp
                  | succ m ih =>
                    intro hm
                    rw [Finset.sum_range_succ]
                    set S := ∑ k ∈ Finset.range m, (ψ (k + 1) - ψ k)
                    have ihm := ih (by omega)
                    have hstep := hψ_step m (by omega)
                    omega
                exact_mod_cast htel

end RefinementCost₂

end StochCalc
