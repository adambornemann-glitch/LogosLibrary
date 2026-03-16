/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerThree/RefiCo.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.RefiCo

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

section BlockBounds


/-- Inserting a single point `u` into one block of a partition changes the
Riemann sum by exactly one defect, bounded by `K · ω(block)^θ`. -/
theorem riemannSum_insert_point_bound₃
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (P : Partition s t) (k : Fin P.n) (u : ℝ)
    (hleft : P.left k ≤ u) (hright : u ≤ P.right k) :
    ‖Ξ (P.left k) (P.right k) -
      (Ξ (P.left k) u + Ξ u (P.right k))‖ ≤
      K * ω (P.left k) (P.right k) ^ θ := by
  -- This is exactly ‖sewingDefect₁ Ξ (P.left k) u (P.right k)‖
  have : Ξ (P.left k) (P.right k) - (Ξ (P.left k) u + Ξ u (P.right k)) =
      sewingDefect₁ Ξ (P.left k) u (P.right k) := by
    simp [sewingDefect₁]; abel
  rw [this]
  exact hΞ.defect_bound _ _ _
    (has.trans (P.mem_Icc hst ⟨k.val, by omega⟩).1)
    hleft hright
    ((P.mem_Icc hst ⟨k.val + 1, by omega⟩).2.trans htb)

/-- **Per-block bound (Layer 3)**: within a monotone sequence of m+1 points,
the Riemann sum error is controlled by ω on the whole block.

Each of the (m-1) defects from right-peeling satisfies
  ‖δΞ(f 0, f(j+1), f(j+2))‖ ≤ K · ω(f 0, f(j+2))^θ ≤ K · ω(f 0, f m)^θ
using the SewingCondition₃ bound + ContControl.mono. -/
lemma block_bound₃
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    (f : ℕ → ℝ) (hf_mono : Monotone f) (hf_a : a ≤ f 0)
    (m : ℕ) (hf_b : f m ≤ b) :
    ‖Ξ (f 0) (f m) - ∑ j ∈ Finset.range m, Ξ (f j) (f (j + 1))‖ ≤
      ↑(m - 1) * (K * ω (f 0) (f m) ^ θ) := by
  rw [right_peel_range Ξ hΞ.vanish_diag f m]
  set C := K * ω (f 0) (f m) ^ θ
  have hC_nn : 0 ≤ C := mul_nonneg hΞ.K_nonneg
    (rpow_nonneg (hΞ.omega_cont.nonneg _ _ hf_a (hf_mono (Nat.zero_le m)) hf_b) _)
  calc ‖∑ j ∈ Finset.range (m - 1),
          sewingDefect₁ Ξ (f 0) (f (j + 1)) (f (j + 2))‖
      ≤ ∑ j ∈ Finset.range (m - 1),
          ‖sewingDefect₁ Ξ (f 0) (f (j + 1)) (f (j + 2))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (m - 1), C := by
        gcongr with j hj
        have hj_lt : j < m - 1 := Finset.mem_range.mp hj
        -- δΞ(f 0, f(j+1), f(j+2)) ≤ K · ω(f 0, f(j+2))^θ
        have hdefect : ‖sewingDefect₁ Ξ (f 0) (f (j + 1)) (f (j + 2))‖ ≤
            K * ω (f 0) (f (j + 2)) ^ θ :=
          hΞ.defect_bound _ _ _ hf_a
            (hf_mono (Nat.zero_le _))
            (hf_mono (by omega))
            (hf_mono (show j + 2 ≤ m by omega) |>.trans hf_b)
        -- ω(f 0, f(j+2)) ≤ ω(f 0, f m) by ContControl.mono
        have hω_mono : ω (f 0) (f (j + 2)) ≤ ω (f 0) (f m) :=
          hΞ.omega_cont.mono hf_a le_rfl
            (hf_mono (Nat.zero_le _))
            (hf_mono (show j + 2 ≤ m by omega))
            hf_b
        calc ‖sewingDefect₁ Ξ (f 0) (f (j + 1)) (f (j + 2))‖
            ≤ K * ω (f 0) (f (j + 2)) ^ θ := hdefect
          _ ≤ K * ω (f 0) (f m) ^ θ := by
              apply mul_le_mul_of_nonneg_left _ hΞ.K_nonneg
              exact rpow_le_rpow
                (hΞ.omega_cont.nonneg _ _ hf_a (hf_mono (Nat.zero_le _))
                  (hf_mono (show j + 2 ≤ m by omega) |>.trans hf_b))
                hω_mono (by linarith [hΞ.one_lt_theta])
    _ = ↑(m - 1) * C := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


/-- **Refinement cost (Layer 3)**: if P' refines P, and each block of P
contains at most M sub-intervals of P', then

  ‖RS(P) - RS(P')‖ ≤ (M - 1) · K · Φ_θ(P)

The proof decomposes RS(P') into blocks aligned with P (via mono_embed),
applies block_bound₃ to each block, bounds (m_k - 1) ≤ M - 1, and sums. -/
theorem riemannSum_refinement_bound₃
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    {P P' : Partition s t} (hPn : 0 < P.n)
    (φ : Fin (P.n + 1) → Fin (P'.n + 1))
    (hφ_val : ∀ i, P'.pts (φ i) = P.pts i)
    (hφ_mono : Monotone φ)
    (hφ_start : φ ⟨0, by omega⟩ = ⟨0, by omega⟩)
    (hφ_end : φ ⟨P.n, by omega⟩ = ⟨P'.n, by omega⟩)
    {M : ℕ}
    (hM : ∀ k : Fin P.n,
      (φ ⟨k.val + 1, by omega⟩).val - (φ ⟨k.val, by omega⟩).val ≤ M) :
    ‖riemannSum Ξ P - riemannSum Ξ P'‖ ≤
      ↑(M - 1) * (K * thetaEnergy ω θ P) := by
  -- Clamped extension of P'.pts
  set g : ℕ → ℝ := fun j => P'.pts ⟨min j P'.n, by omega⟩
  have hg_mono : Monotone g :=
    fun i j hij => P'.mono (min_le_min_right P'.n hij)
  have hg_val : ∀ j (hj : j ≤ P'.n), g j = P'.pts ⟨j, by omega⟩ := by
    intro j hj; show P'.pts ⟨min j P'.n, _⟩ = _; congr 1; ext; exact Nat.min_eq_left hj
  -- φ as ℕ → ℕ (clamped)
  set ψ : ℕ → ℕ := fun k => (φ ⟨min k P.n, by omega⟩).val
  have hψ_val : ∀ k (hk : k ≤ P.n), ψ k = (φ ⟨k, by omega⟩).val := by
    intro k hk; simp [ψ, Nat.min_eq_left hk]
  have hψ_step : ∀ k, k < P.n → ψ k ≤ ψ (k + 1) := by
    intro k hk
    rw [hψ_val k (by omega), hψ_val (k + 1) (by omega)]
    exact hφ_mono (Fin.mk_le_mk.mpr (by omega))
  have hψ_start : ψ 0 = 0 := by
    rw [hψ_val 0 (Nat.zero_le _)]; exact congrArg Fin.val hφ_start
  have hψ_end : ψ P.n = P'.n := by
    rw [hψ_val P.n le_rfl]; exact congrArg Fin.val hφ_end
  -- g(ψ(k)) = P.pts(k)
  have hg_ψ : ∀ k (hk : k ≤ P.n), g (ψ k) = P.pts ⟨k, by omega⟩ := by
    intro k hk
    have hψk_le : ψ k ≤ P'.n := by
      have := (φ ⟨k, by omega⟩).isLt; rw [hψ_val k hk]; omega
    have : g (ψ k) = P'.pts (φ ⟨k, by omega⟩) := by
      rw [hg_val (ψ k) hψk_le]; congr 1; ext; exact hψ_val k hk
    rw [this]; exact hφ_val ⟨k, by omega⟩
  -- Express Riemann sums via g, ψ
  set F : ℕ → E := fun j => Ξ (g j) (g (j + 1))
  have hRS_P'_eq : riemannSum Ξ P' = ∑ j ∈ Finset.range P'.n, F j := by
    simp only [riemannSum, F]
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun ⟨j, hj⟩ _ => by
      simp only [Partition.left, Partition.right]
      rw [hg_val j (by omega), hg_val (j + 1) (by omega)]
  have hRS_P_eq : riemannSum Ξ P =
      ∑ k ∈ Finset.range P.n, Ξ (g (ψ k)) (g (ψ (k + 1))) := by
    simp only [riemannSum]
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun ⟨k, hk⟩ _ => by
      simp only [Partition.left, Partition.right]
      rw [hg_ψ k (by omega), hg_ψ (k + 1) (by omega)]
  -- Block decomposition
  have hblock_decomp :
      ∑ j ∈ Finset.range P'.n, F j =
      ∑ k ∈ Finset.range P.n,
        ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), F j := by
    rw [show Finset.range P'.n = Finset.Ico (ψ 0) (ψ P.n) from by
      rw [hψ_start, hψ_end, Finset.range_eq_Ico]]
    exact finset_sum_Ico_blocks F P.n ψ hψ_step
  -- ω-nonnegativity helper
  have hω_gψ : ∀ k (hk : k < P.n),
      0 ≤ ω (g (ψ k)) (g (ψ (k + 1))) := by
    intro k hk
    rw [hg_ψ k (by omega), hg_ψ (k + 1) (by omega)]
    exact hΞ.omega_cont.nonneg _ _
      (has.trans (P.mem_Icc hst ⟨k, by omega⟩).1)
      (P.mono (Fin.mk_le_mk.mpr (by omega)))
      ((P.mem_Icc hst ⟨k + 1, by omega⟩).2.trans htb)
  -- Rewrite thetaEnergy into g ∘ ψ coordinates
  have hΦ_eq : thetaEnergy ω θ P =
      ∑ k ∈ Finset.range P.n, ω (g (ψ k)) (g (ψ (k + 1))) ^ θ := by
    simp only [thetaEnergy]
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun ⟨k, hk⟩ _ => by
      simp only [Partition.left, Partition.right]
      rw [hg_ψ k (by omega), hg_ψ (k + 1) (by omega)]
  -- Main bound
  rw [hRS_P_eq, hRS_P'_eq, hblock_decomp, ← Finset.sum_sub_distrib, hΦ_eq]
  calc ‖∑ k ∈ Finset.range P.n,
          (Ξ (g (ψ k)) (g (ψ (k + 1))) -
            ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), F j)‖
      ≤ ∑ k ∈ Finset.range P.n,
          ‖Ξ (g (ψ k)) (g (ψ (k + 1))) -
            ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), F j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range P.n,
          ↑(M - 1) * (K * ω (g (ψ k)) (g (ψ (k + 1))) ^ θ) := by
        apply Finset.sum_le_sum; intro k hk
        have hk_lt := Finset.mem_range.mp hk
        -- Set up block
        let m_k := ψ (k + 1) - ψ k
        let f_k : ℕ → ℝ := fun j => g (ψ k + j)
        have hf_k_mono : Monotone f_k := fun i j hij => hg_mono (by omega)
        have hf_k_0 : f_k 0 = g (ψ k) := by simp [f_k]
        have hf_k_m : f_k m_k = g (ψ (k + 1)) := by
          simp [f_k, m_k, Nat.add_sub_cancel' (hψ_step k hk_lt)]
        have hIco_eq : ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), F j =
            ∑ j ∈ Finset.range m_k, Ξ (f_k j) (f_k (j + 1)) := by
          rw [Finset.sum_Ico_eq_sum_range]
          exact Finset.sum_congr rfl fun j _ => by simp [F, f_k]; rfl
        rw [← hf_k_0, ← hf_k_m, hIco_eq]
        -- Interval membership
        have hfk_a : a ≤ f_k 0 := by
          rw [hf_k_0, hg_ψ k (by omega)]
          exact has.trans (P.mem_Icc hst ⟨k, by omega⟩).1
        have hfk_b : f_k m_k ≤ b := by
          rw [hf_k_m, hg_ψ (k + 1) (by omega)]
          exact (P.mem_Icc hst ⟨k + 1, by omega⟩).2.trans htb
        -- Multiplicity bound
        have hm_k_le : m_k ≤ M := by
          show ψ (k + 1) - ψ k ≤ M
          rw [hψ_val (k + 1) (by omega), hψ_val k (by omega)]
          exact hM ⟨k, hk_lt⟩
        -- Apply block_bound₃ then bound multiplicity
        calc ‖Ξ (f_k 0) (f_k m_k) -
                ∑ j ∈ Finset.range m_k, Ξ (f_k j) (f_k (j + 1))‖
            ≤ ↑(m_k - 1) * (K * ω (f_k 0) (f_k m_k) ^ θ) :=
              block_bound₃ hΞ f_k hf_k_mono hfk_a m_k hfk_b
          _ = ↑(m_k - 1) * (K * ω (g (ψ k)) (g (ψ (k + 1))) ^ θ) := by
              rw [hf_k_0, hf_k_m]
          _ ≤ ↑(M - 1) * (K * ω (g (ψ k)) (g (ψ (k + 1))) ^ θ) := by
              apply mul_le_mul_of_nonneg_right _
                (mul_nonneg hΞ.K_nonneg (rpow_nonneg (hω_gψ k hk_lt) _))
              exact Nat.cast_le.mpr (Nat.sub_le_sub_right hm_k_le 1)
        rw [hf_k_0, hf_k_m]
    _ = ↑(M - 1) * (K * ∑ k ∈ Finset.range P.n,
          ω (g (ψ k)) (g (ψ (k + 1))) ^ θ) := by
        rw [← Finset.mul_sum]; congr 1; rw [← Finset.mul_sum]


/-! ### Helper lemma 2: Max-ω on a partition vanishes as mesh → 0

If `ω` is a continuous control and `P` has mesh < δ, then every
`ω(P.left i, P.right i) < ε` (by `cont_diag`). -/
theorem maxOmega_tendsto_zero {ω : ℝ → ℝ → ℝ} {a b : ℝ}
    (hω : ContControl ω a b) {s t : ℝ} (has : a ≤ s) (htb : t ≤ b)
    (hst : s ≤ t) :
    ∀ ε > 0, ∃ δ > 0, ∀ (P : Partition s t), P.mesh < δ →
      ∀ i : Fin P.n, ω (P.left i) (P.right i) < ε := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := hω.cont_diag ε hε
  exact ⟨δ, hδ_pos, fun P hmesh i => by
    have hPn : P.n ≠ 0 := by rw [@Nat.ne_zero_iff_zero_lt]; exact Fin.pos i
    have hlen_le_mesh : P.right i - P.left i ≤ P.mesh := by
      simp only [Partition.mesh, dif_neg hPn]
      simp only [le_sup'_iff, Finset.mem_univ, tsub_le_iff_right, true_and]
      exact ⟨i, by linarith⟩
    exact hδ _ _
      (has.trans (P.mem_Icc hst ⟨i.val, by omega⟩).1)
      (P.left_le_right i)
      ((P.mem_Icc hst ⟨i.val + 1, by omega⟩).2.trans htb)
      (lt_of_le_of_lt hlen_le_mesh hmesh)⟩


end BlockBounds
end StochCalc
