/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerTwo/ThetaEnergy.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.ContinuousControl

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

/-! ### Partitions -/

section Partition

end Partition

/-! ### The theta-energy of a partition -/

section ThetaEnergy

/-- **The key estimate**: `Φ_θ(P)` is controlled by the maximum individual term
raised to `θ - 1`, times the total control `ω(s, t)`.

`Φ_θ(P) = ∑ᵢ ωᵢ^θ = ∑ᵢ ωᵢ^{θ-1} · ωᵢ ≤ (max ωᵢ)^{θ-1} · ∑ᵢ ωᵢ ≤ (max ωᵢ)^{θ-1} · ω(s,t)`

This is where `θ > 1` earns its keep: as the mesh refines, `max ωᵢ → 0` (by continuity
of `ω`), so `Φ_θ → 0` — even though `∑ ωᵢ` stays bounded by `ω(s,t)`.

For `θ = 1`, `Φ₁ = ∑ ωᵢ ≤ ω(s,t)`, which is bounded but does NOT vanish.
For `θ < 1`, `Φ_θ` can actually *grow* under refinement. This is the analytical
reason that `θ > 1` is necessary: it is a *quantitative convexity* condition. -/
theorem thetaEnergy_le {ω : ℝ → ℝ → ℝ} {a b : ℝ} {θ : ℝ}
    (hω : ContControl ω a b) (hθ : 1 ≤ θ)
    {s t : ℝ} (has : a ≤ s) (htb : t ≤ b) (hst : s ≤ t)
    (P : Partition s t) (hP : 0 < P.n) :
    thetaEnergy ω θ P ≤
      (Finset.sup' Finset.univ
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hP⟩⟩)
        (fun i : Fin P.n => ω (P.left i) (P.right i))) ^ (θ - 1) *
      ω s t := by
  set M := Finset.sup' Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hP⟩⟩)
    (fun i : Fin P.n => ω (P.left i) (P.right i)) with hM_def
  -- Nonnegativity of ω on partition intervals
  have hω_nn : ∀ i : Fin P.n, 0 ≤ ω (P.left i) (P.right i) := by
    intro i
    exact hω.nonneg _ _
      (has.trans (P.mem_Icc hst ⟨i.val, by omega⟩).1)
      (P.left_le_right i)
      ((P.mem_Icc hst ⟨i.val + 1, by omega⟩).2.trans htb)
  have hM_nn : 0 ≤ M :=
    (hω_nn ⟨0, hP⟩).trans
      (Finset.le_sup' (fun i : Fin P.n => ω (P.left i) (P.right i))
        (Finset.mem_univ (⟨0, hP⟩ : Fin P.n)))
  -- Pointwise bound: ωᵢ^θ ≤ M^{θ-1} · ωᵢ
  have hpt : ∀ i : Fin P.n, ω (P.left i) (P.right i) ^ θ ≤
      M ^ (θ - 1) * ω (P.left i) (P.right i) := by
    intro i
    set ωi := ω (P.left i) (P.right i)
    have h_nn : 0 ≤ ωi := hω_nn i
    have h_le : ωi ≤ M := by
      simp only [le_sup'_iff, Finset.mem_univ, true_and, M, ωi]
      apply Exists.intro; rfl
    have hsplit : ωi ^ θ = ωi ^ (θ - 1) * ωi := by
      rw [show θ = (θ - 1) + 1 from by ring,
          rpow_add' h_nn (show (0 : ℝ) < (θ - 1) + 1 from by linarith).ne',
          rpow_one]; simp only [sub_add_cancel, ωi]
    rw [hsplit]
    -- ωᵢ^{θ-1} ≤ M^{θ-1} by rpow_le_rpow, multiply by ωᵢ ≥ 0
    apply mul_le_mul_of_nonneg_right _ h_nn
    exact rpow_le_rpow h_nn h_le (by linarith : 0 ≤ θ - 1)
  -- Sum the pointwise bounds, then collapse via super-additivity
  calc thetaEnergy ω θ P
      = ∑ i : Fin P.n, ω (P.left i) (P.right i) ^ θ := rfl
    _ ≤ ∑ i : Fin P.n, M ^ (θ - 1) * ω (P.left i) (P.right i) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = M ^ (θ - 1) * ∑ i : Fin P.n, ω (P.left i) (P.right i) := by
        rw [← Finset.mul_sum]
    _ ≤ M ^ (θ - 1) * ω s t := by
        gcongr
        exact hω.sum_le has htb P

/-- **Theta-energy vanishes as mesh refines**: for a continuous control, `Φ_θ(P) → 0`
as the partition mesh → 0, provided `θ > 1`.

This is the fundamental convergence mechanism of the general sewing lemma. -/
theorem thetaEnergy_tendsto_zero {ω : ℝ → ℝ → ℝ} {a b : ℝ} {θ : ℝ}
    (hω : ContControl ω a b) (hθ : 1 < θ)
    {s t : ℝ} (has : a ≤ s) (htb : t ≤ b) (hst : s ≤ t) :
    ∀ ε > 0, ∃ δ > 0, ∀ (P : Partition s t),
      P.mesh < δ → thetaEnergy ω θ P < ε := by
  intro ε hε
  have hθ₀ : (0 : ℝ) < θ := by linarith
  have hθ₁ : (0 : ℝ) < θ - 1 := by linarith
  by_cases hωst : ω s t = 0
  · -- All sub-ω's are 0 by nonnegativity + monotonicity → Φ_θ = 0
    refine ⟨1, one_pos, fun P _ => ?_⟩
    have hωi_zero : ∀ i : Fin P.n, ω (P.left i) (P.right i) = 0 := by
      intro i
      have h_nn : 0 ≤ ω (P.left i) (P.right i) :=
        hω.nonneg _ _
          (has.trans (P.mem_Icc hst ⟨i.val, by omega⟩).1)
          (P.left_le_right i)
          ((P.mem_Icc hst ⟨i.val + 1, by omega⟩).2.trans htb)
      have h_le : ω (P.left i) (P.right i) ≤ 0 :=
        hωst ▸ hω.mono has
          (P.mem_Icc hst ⟨i.val, by omega⟩).1
          (P.left_le_right i)
          (P.mem_Icc hst ⟨i.val + 1, by omega⟩).2
          htb
      linarith
    suffices thetaEnergy ω θ P = 0 by linarith
    exact Finset.sum_eq_zero fun i _ => by rw [hωi_zero i, zero_rpow hθ₀.ne']
  · -- ω(s,t) > 0: choose ε₁ with ε₁^{θ-1} · ω(s,t) < ε
    have hωst_pos : 0 < ω s t :=
      lt_of_le_of_ne (hω.nonneg s t has hst htb) (Ne.symm hωst)
    set c := ε / (2 * ω s t) with hc_def
    have hc_pos : 0 < c := div_pos hε (mul_pos two_pos hωst_pos)
    set ε₁ := c ^ (θ - 1)⁻¹ with hε₁_def
    have hε₁_pos : 0 < ε₁ := rpow_pos_of_pos hc_pos _
    -- Key identity: ε₁^{θ-1} = c (by rpow inverse)
    have hε₁_pow : ε₁ ^ (θ - 1) = c := by
      show (c ^ (θ - 1)⁻¹) ^ (θ - 1) = c
      rw [← rpow_mul hc_pos.le, inv_mul_cancel₀ hθ₁.ne', rpow_one]
    -- So ε₁^{θ-1} · ω(s,t) = ε/2 < ε
    have hε₁_ωst : ε₁ ^ (θ - 1) * ω s t < ε := by
      rw [hε₁_pow]
      have : c * ω s t = ε / 2 := by
        simp only [c]; field_simp
      linarith
    -- Get δ from continuity of ω at the diagonal
    obtain ⟨δ, hδ_pos, hδ⟩ := hω.cont_diag ε₁ hε₁_pos
    refine ⟨δ, hδ_pos, fun P hmesh => ?_⟩
    by_cases hPn : P.n = 0
    · -- Empty partition: sum over Fin 0 is 0
      suffices thetaEnergy ω θ P = 0 by linarith
      exact Finset.sum_eq_zero fun i _ => absurd i.isLt (by omega)
    · -- Each sub-interval length < δ, so each ωᵢ < ε₁
      have hmesh_bound : ∀ i : Fin P.n, P.right i - P.left i < δ := by
        intro i
        calc P.right i - P.left i
            ≤ P.mesh := by
              simp only [Partition.mesh, dif_neg hPn]
              exact Finset.le_sup'
                (fun j : Fin P.n => P.right j - P.left j)
                (Finset.mem_univ i)
          _ < δ := hmesh
      have hωi_lt : ∀ i : Fin P.n, ω (P.left i) (P.right i) < ε₁ := by
        intro i
        exact hδ _ _
          (has.trans (P.mem_Icc hst ⟨i.val, by omega⟩).1)
          (P.left_le_right i)
          ((P.mem_Icc hst ⟨i.val + 1, by omega⟩).2.trans htb)
          (hmesh_bound i)
      -- Pointwise: ωᵢ^θ = ωᵢ^{θ-1} · ωᵢ ≤ ε₁^{θ-1} · ωᵢ
      have hpt : ∀ i : Fin P.n, ω (P.left i) (P.right i) ^ θ ≤
          ε₁ ^ (θ - 1) * ω (P.left i) (P.right i) := by
        intro i
        have h_nn : 0 ≤ ω (P.left i) (P.right i) :=
          hω.nonneg _ _
            (has.trans (P.mem_Icc hst ⟨i.val, by omega⟩).1)
            (P.left_le_right i)
            ((P.mem_Icc hst ⟨i.val + 1, by omega⟩).2.trans htb)
        by_cases hωi : ω (P.left i) (P.right i) = 0
        · simp [hωi, zero_rpow hθ₀.ne']
        · have hωi_pos : 0 < ω (P.left i) (P.right i) :=
            lt_of_le_of_ne h_nn (Ne.symm hωi)
          rw [show θ = (θ - 1) + 1 from by ring, rpow_add hωi_pos, rpow_one]
          simp only [sub_add_cancel, ge_iff_le]
          exact mul_le_mul_of_nonneg_right
            (rpow_le_rpow h_nn (hωi_lt i).le hθ₁.le) h_nn
      -- Sum the pointwise bounds, collapse via super-additivity
      calc thetaEnergy ω θ P
          = ∑ i : Fin P.n, ω (P.left i) (P.right i) ^ θ := rfl
        _ ≤ ∑ i : Fin P.n, ε₁ ^ (θ - 1) * ω (P.left i) (P.right i) :=
            Finset.sum_le_sum fun i _ => hpt i
        _ = ε₁ ^ (θ - 1) * ∑ i : Fin P.n, ω (P.left i) (P.right i) := by
            rw [← Finset.mul_sum]
        _ ≤ ε₁ ^ (θ - 1) * ω s t :=
            mul_le_mul_of_nonneg_left (hω.sum_le has htb P)
              (rpow_nonneg hε₁_pos.le _)
        _ < ε := hε₁_ωst

/-- Key inequality: `a^θ + b^θ ≤ (a+b)^θ` for `a, b ≥ 0` and `θ ≥ 1`. -/
private lemma rpow_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {θ : ℝ} (hθ : 1 ≤ θ) :
    a ^ θ + b ^ θ ≤ (a + b) ^ θ := by
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have hθ₁ : 0 ≤ θ - 1 := by linarith
  -- Factor: x^θ = x · x^{θ-1}
  have factor : ∀ x : ℝ, 0 ≤ x → x ^ θ = x * x ^ (θ - 1) := by
    intro x hx
    rcases eq_or_lt_of_le hx with rfl | hx_pos
    · rw [zero_rpow (by linarith : θ ≠ 0), zero_mul]
    · rw [show θ = 1 + (θ - 1) from by ring, rpow_add hx_pos, rpow_one]
      simp only [add_sub_cancel]
  calc a ^ θ + b ^ θ
      = a * a ^ (θ - 1) + b * b ^ (θ - 1) := by
        rw [factor a ha, factor b hb]
    _ ≤ a * (a + b) ^ (θ - 1) + b * (a + b) ^ (θ - 1) :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (rpow_le_rpow ha (le_add_of_nonneg_right hb) hθ₁) ha)
          (mul_le_mul_of_nonneg_left
            (rpow_le_rpow hb (le_add_of_nonneg_left ha) hθ₁) hb)
    _ = (a + b) * (a + b) ^ (θ - 1) := by ring
    _ = (a + b) ^ θ := (factor (a + b) hab).symm

/-- Super-additivity + concavity: `∑ ω(fᵢ, fᵢ₊₁)^θ ≤ ω(f₀, fₙ)^θ`
for monotone `f` with values in `[a, b]`. -/
private lemma ContControl.range_sum_rpow_le {ω : ℝ → ℝ → ℝ} {a b : ℝ} {θ : ℝ}
    (hω : ContControl ω a b) (hθ : 1 ≤ θ) :
    ∀ (n : ℕ) {f : ℕ → ℝ}, Monotone f → a ≤ f 0 → f n ≤ b →
      ∑ i ∈ Finset.range n, ω (f i) (f (i + 1)) ^ θ ≤ ω (f 0) (f n) ^ θ := by
  intro n; induction n with
  | zero =>
    intro f _ _ _
    simp only [Finset.sum_range_zero]
    rw [hω.diag (f 0), zero_rpow (by linarith : θ ≠ 0)]
  | succ m ih =>
    intro f hf hfa hfb
    have hfm_b : f m ≤ b := (hf (Nat.le_succ m)).trans hfb
    have hfa_m : a ≤ f m := hfa.trans (hf (Nat.zero_le m))
    have hω₁ : 0 ≤ ω (f 0) (f m) :=
      hω.nonneg _ _ hfa (hf (Nat.zero_le m)) hfm_b
    have hω₂ : 0 ≤ ω (f m) (f (m + 1)) :=
      hω.nonneg _ _ hfa_m (hf (Nat.le_succ m)) hfb
    rw [Finset.sum_range_succ]
    calc (∑ i ∈ Finset.range m, ω (f i) (f (i + 1)) ^ θ) +
            ω (f m) (f (m + 1)) ^ θ
        ≤ ω (f 0) (f m) ^ θ + ω (f m) (f (m + 1)) ^ θ := by
          gcongr; exact ih hf hfa hfm_b
      _ ≤ (ω (f 0) (f m) + ω (f m) (f (m + 1))) ^ θ :=
          rpow_add_le hω₁ hω₂ hθ
      _ ≤ ω (f 0) (f (m + 1)) ^ θ :=
          rpow_le_rpow (add_nonneg hω₁ hω₂)
            (hω.superadd _ _ _ hfa (hf (Nat.zero_le m))
              (hf (Nat.le_succ m)) hfb)
            (by linarith)
/-
/-- **Refinement with witness**: partition `P'` refines `P` via a monotone injection. -/
structure Partition.IsRefinementWith {s t : ℝ} (P' P : Partition s t)
    (φ : Fin (P.n + 1) → Fin (P'.n + 1)) : Prop where
  val_match : ∀ i, P'.pts (φ i) = P.pts i
  mono : Monotone φ
  start : φ ⟨0, by omega⟩ = ⟨0, by omega⟩
  last : φ ⟨P.n, by omega⟩ = ⟨P'.n, by omega⟩
-/

/-- Monotone injection extracted from refinement. This is the combinatorial
heart: given that every P-point appears in P', construct a monotone map
between index sets. -/
lemma Partition.IsRefinement.mono_embed {s t : ℝ}
    {P P' : Partition s t} (hPP' : P'.IsRefinement P) (hPn : 0 < P.n) :
    ∃ φ : Fin (P.n + 1) → Fin (P'.n + 1),
      (∀ i, P'.pts (φ i) = P.pts i) ∧
      Monotone φ ∧
      φ ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧
      φ ⟨P.n, by omega⟩ = ⟨P'.n, by omega⟩ := by
  -- Witnesses exist for each P-point
  have hex : ∀ i : Fin (P.n + 1),
      ∃ (j : ℕ) (hj : j < P'.n + 1), P'.pts ⟨j, hj⟩ = P.pts i := by
    intro i; obtain ⟨⟨j, hj⟩, heq⟩ := hPP' i; exact ⟨j, hj, heq⟩
  -- Minimum-witness construction, with last index pinned to P'.n
  set ψ : Fin (P.n + 1) → ℕ := fun i =>
    if i.val = P.n then P'.n
    else Nat.find (hex i)
  -- ψ values are ≤ P'.n
  have hψ_le : ∀ i, ψ i ≤ P'.n := by
    intro i; simp only [ψ]
    split_ifs <;> [exact le_rfl; exact Nat.lt_succ_iff.mp (Nat.find_spec (hex i)).choose]
  -- Value matching
  have hψ_val : ∀ i, P'.pts ⟨ψ i, by grind⟩ = P.pts i := by
    intro i; simp only [ψ]
    split_ifs with h
    · have : i = ⟨P.n, by omega⟩ := Fin.ext h
      rw [P'.last,this, P.last]
    · have spec := Nat.find_spec (hex i)
      exact spec.choose_spec
  -- Start: ψ(0) = 0
  have hψ_start : ψ ⟨0, by omega⟩ = 0 := by
    simp only [ψ]
    split_ifs with h
    · -- 0 = P.n is impossible since P.n > 0
      omega
    · exact le_antisymm
        (Nat.find_min' _ ⟨by omega, by rw [P'.first, P.first]⟩)
        (Nat.zero_le _)
  -- End: ψ(P.n) = P'.n
  have hψ_end : ψ ⟨P.n, by omega⟩ = P'.n := by
    simp only [ψ]; exact ite_true _ _
  -- Step monotonicity: ψ(i) ≤ ψ(i+1)
  have hψ_step : ∀ i : Fin P.n,
      ψ ⟨i.val, by omega⟩ ≤ ψ ⟨i.val + 1, by omega⟩ := by
    intro i
    -- Since i < P.n, ψ(i) = Nat.find(hex i)
    have h_not_last : (⟨i, by omega⟩ : Fin (P.n + 1)).val ≠ P.n := by grind
    simp only [ψ, h_not_last, ite_false]
    split_ifs with h_next
    · -- i + 1 = P.n: need Nat.find(hex i) ≤ P'.n, which is hψ_le
      exact Nat.lt_succ_iff.mp (Nat.find_spec (hex ⟨i, by omega⟩)).choose
    · -- Both are Nat.find. Monotonicity by minimality argument.
      by_contra hlt
      push_neg at hlt
      -- fi > fi₊₁ where fi = Nat.find(hex i), fi₊₁ = Nat.find(hex (i+1))
      set fi := Nat.find (hex ⟨i, by omega⟩)
      set fi₁ := Nat.find (hex ⟨i + 1, by omega⟩)
      have hfi := Nat.find_spec (hex ⟨i, by omega⟩)
      have hfi₁ := Nat.find_spec (hex ⟨i + 1, by omega⟩)
      -- P'.pts(fi₁) ≤ P'.pts(fi) since fi₁ < fi and P' monotone
      have hmono_P' : P'.pts ⟨fi₁, by grind⟩ ≤ P'.pts ⟨fi, by grind⟩ :=
        P'.mono (Fin.mk_le_mk.mpr (by omega))
      -- P.pts(i) ≤ P.pts(i+1) since P monotone
      have hmono_P : P.pts ⟨i, by omega⟩ ≤ P.pts (⟨i + 1, by omega⟩) :=
        P.mono (Fin.mk_le_mk.mpr (by omega))
      -- Combining: P.pts(i) = P'.pts(fi) ≥ P'.pts(fi₁) = P.pts(i+1) ≥ P.pts(i)
      -- So P'.pts(fi₁) = P.pts(i), making fi₁ a valid witness for index i
      have heq : P'.pts ⟨fi₁, by grind⟩ = P.pts ⟨i, by omega⟩ := by
        linarith [hfi.2, hfi₁.2]
      -- fi₁ < fi = Nat.find(hex i) contradicts minimality
      exact Nat.find_min (hex ⟨i, by omega⟩) hlt ⟨hfi₁.1, heq⟩
  -- Assemble: wrap ψ in Fin, derive full monotonicity from step monotonicity
  refine ⟨fun i => ⟨ψ i, by grind⟩, fun i => hψ_val i, ?_, ?_, ?_⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    show ψ ⟨i, hi⟩ ≤ ψ ⟨j, hj⟩
    have hij' : i ≤ j := hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij'
    induction d with
    | zero => simp
    | succ d ih =>
      have hid_bound : i + d < P.n + 1 := by omega
      calc ψ ⟨i, hi⟩
          ≤ ψ ⟨i + d, hid_bound⟩ :=
            ih hid_bound (by show i ≤ i + d; omega) (by omega)
        _ ≤ ψ ⟨i + (d + 1), hj⟩ := hψ_step ⟨i + d, by omega⟩
  · ext; exact hψ_start
  · ext; exact hψ_end


theorem thetaEnergy_le_of_refinement {ω : ℝ → ℝ → ℝ} {a b : ℝ} {θ : ℝ}
    (hω : ContControl ω a b) (hθ : 1 ≤ θ)
    {s t : ℝ} (has : a ≤ s) (htb : t ≤ b)
    {P P' : Partition s t} (hPP' : P'.IsRefinement P) :
    thetaEnergy ω θ P' ≤ thetaEnergy ω θ P := by
  by_cases hPn : P.n = 0
  · -- P.n = 0: s = t, all partition points collapse, both energies = 0
    have hP_zero : thetaEnergy ω θ P = 0 :=
      Finset.sum_eq_zero (fun i _ => absurd i.isLt (by omega))
    rw [hP_zero]
    -- s ≤ t and t ≤ s (from P having one point)
    have hsle : s ≤ t := by
      calc s = P.pts ⟨0, by omega⟩ := P.first.symm
        _ ≤ P.pts ⟨P.n, by omega⟩ := P.mono (by omega)
        _ = t := P.last
    have htle : t ≤ s := by
      calc t = P.pts ⟨P.n, by omega⟩ := P.last.symm
        _ ≤ P.pts ⟨0, by omega⟩ := P.mono (by show P.n ≤ 0; omega)
        _ = s := P.first
    -- Every P'-point equals s (squeezed between s and t = s)
    have hpt_eq : ∀ j : Fin (P'.n + 1), P'.pts j = s := by
      intro j
      have h1 : s ≤ P'.pts j := by
        calc s = P'.pts ⟨0, by omega⟩ := P'.first.symm
          _ ≤ P'.pts j := P'.mono (Fin.zero_le j)
      have h2 : P'.pts j ≤ s := by
        calc P'.pts j ≤ P'.pts ⟨P'.n, by omega⟩ := P'.mono (Fin.le_last j)
          _ = t := P'.last
          _ ≤ s := htle
      linarith
    apply Finset.sum_nonpos; intro ⟨i, hi⟩ _
    simp only [Partition.left, Partition.right]
    rw [hpt_eq ⟨i, by omega⟩, hpt_eq ⟨i + 1, by omega⟩, hω.diag,
        zero_rpow (by linarith : θ ≠ 0)]
  · obtain ⟨φ, hφ_val, hφ_mono, hφ_start, hφ_end⟩ :=
      hPP'.mono_embed (Nat.pos_of_ne_zero hPn)
    have hst : s ≤ t := by
      calc s = P.pts ⟨0, by omega⟩ := P.first.symm
        _ ≤ P.pts ⟨P.n, by omega⟩ := P.mono (Fin.zero_le _)
        _ = t := P.last
    -- Extend P'.pts to ℕ → ℝ
    set g : ℕ → ℝ := fun j => P'.pts ⟨min j P'.n, by omega⟩
    have hg_mono : Monotone g := fun i j hij => P'.mono (min_le_min_right P'.n hij)
    have hg_val : ∀ j (hj : j ≤ P'.n), g j = P'.pts ⟨j, Nat.lt_succ_of_le hj⟩ := by
      intro j hj; show P'.pts ⟨min j P'.n, _⟩ = _; congr 1; ext; exact Nat.min_eq_left hj
    -- ω-nonnegativity for P'-intervals
    have hω_nn_P' : ∀ j : Fin P'.n, 0 ≤ ω (P'.left j) (P'.right j) :=
      fun j => hω.nonneg _ _
        (has.trans (P'.mem_Icc hst ⟨j.val, by omega⟩).1)
        (P'.left_le_right j)
        ((P'.mem_Icc hst ⟨j.val + 1, by omega⟩).2.trans htb)
    -- Group bound: within each P-interval, P'-theta-energy ≤ P-theta-energy
    have hgroup_bound : ∀ k : Fin P.n,
        ∑ j ∈ Finset.Ico (φ ⟨k.val, by omega⟩).val (φ ⟨k.val + 1, by omega⟩).val,
          ω (P'.pts ⟨min j P'.n, by omega⟩) (P'.pts ⟨min (j + 1) P'.n, by omega⟩) ^ θ ≤
        ω (P.left ⟨k.val, k.isLt⟩) (P.right ⟨k.val, k.isLt⟩) ^ θ := by
      intro ⟨k, hk⟩
      set lo := (φ ⟨k, by omega⟩).val
      set hi := (φ ⟨k + 1, by omega⟩).val
      have hlo_le : lo ≤ P'.n := by have := (φ ⟨k, by omega⟩).isLt; omega
      have hhi_le : hi ≤ P'.n := by have := (φ ⟨k + 1, by omega⟩).isLt; omega
      have hg_lo : P'.pts ⟨lo, by omega⟩ = P.left ⟨k, hk⟩ := by
        show P'.pts (φ ⟨k, by omega⟩) = P.pts ⟨k, by omega⟩
        exact hφ_val ⟨k, by omega⟩
      have hg_hi : P'.pts ⟨hi, by omega⟩ = P.right ⟨k, hk⟩ := by
        show P'.pts (φ ⟨k + 1, by omega⟩) = P.pts ⟨k + 1, by omega⟩
        exact hφ_val ⟨k + 1, by omega⟩
      set h : ℕ → ℝ := fun j => g (lo + j)
      have hh_mono : Monotone h := fun i j hij => hg_mono (by omega)
      have hlo_hi : lo ≤ hi := by
        have h : (⟨k, by omega⟩ : Fin (P.n + 1)) ≤ ⟨k + 1, by omega⟩ := by
          show k ≤ k + 1; omega
        exact hφ_mono h
      calc ∑ j ∈ Finset.Ico lo hi,
              ω (P'.pts ⟨min j P'.n, _⟩) (P'.pts ⟨min (j + 1) P'.n, _⟩) ^ θ
          = ∑ j ∈ Finset.range (hi - lo),
              ω (g (lo + j)) (g (lo + j + 1)) ^ θ := by
            rw [Finset.sum_Ico_eq_sum_range]
        _ ≤ ω (g lo) (g hi) ^ θ := by
            have ha_h0 : a ≤ h 0 := by
              show a ≤ g lo
              rw [hg_val lo hlo_le, hg_lo]
              exact has.trans (P.mem_Icc hst ⟨k, by omega⟩).1
            have hh_end : h (hi - lo) ≤ b := by
              show g (lo + (hi - lo)) ≤ b
              rw [Nat.add_sub_cancel' hlo_hi, hg_val hi hhi_le, hg_hi]
              exact (P.mem_Icc hst ⟨k + 1, by omega⟩).2.trans htb
            have key := hω.range_sum_rpow_le hθ (hi - lo) hh_mono ha_h0 hh_end
            simp only [h] at key
            rwa [Nat.add_sub_cancel' hlo_hi] at key
        _ = ω (P.left ⟨k, hk⟩) (P.right ⟨k, hk⟩) ^ θ := by
            congr 1
            rw [hg_val lo hlo_le, hg_lo]
            rw [hg_val hi hhi_le, hg_hi]
    -- Clamped P-pts function
    set pf : ℕ → ℝ := fun k => P.pts ⟨min k P.n, by omega⟩
    have hpf_left : ∀ k (hk : k < P.n), pf k = P.left ⟨k, hk⟩ := by
      intro k hk; simp only [pf, Partition.left]; congr 1; ext; exact Nat.min_eq_left (by omega)
    have hpf_right : ∀ k (hk : k < P.n), pf (k + 1) = P.right ⟨k, hk⟩ := by
      intro k hk; simp only [pf, Partition.right]; congr 1; ext; exact Nat.min_eq_left (by omega)
    -- Main inequality by induction on K
    suffices hkey : ∀ K (hK : K ≤ P.n),
        ∑ j ∈ Finset.Ico 0 (φ ⟨K, by omega⟩).val,
          ω (g j) (g (j + 1)) ^ θ ≤
        ∑ k ∈ Finset.range K,
          ω (pf k) (pf (k + 1)) ^ θ by
      -- Specialize at K = P.n
      specialize hkey P.n le_rfl
      rw [show (φ ⟨P.n, by omega⟩).val = P'.n from congrArg Fin.val hφ_end,
          ← Finset.range_eq_Ico] at hkey
      -- Connect to thetaEnergy
      calc thetaEnergy ω θ P'
          = ∑ j ∈ Finset.range P'.n, ω (g j) (g (j + 1)) ^ θ := by
            unfold thetaEnergy
            rw [← Fin.sum_univ_eq_sum_range]
            congr 1; ext ⟨j, hj⟩
            simp only [Partition.left, Partition.right]
            show ω (P'.pts ⟨j, _⟩) (P'.pts ⟨j + 1, _⟩) ^ θ =
                 ω (g j) (g (j + 1)) ^ θ
            have h1 : g j = P'.pts ⟨j, by omega⟩ := hg_val j (by omega)
            have h2 : g (j + 1) = P'.pts ⟨j + 1, by omega⟩ := hg_val (j + 1) (by omega)
            rw [h1, h2]
        _ ≤ ∑ k ∈ Finset.range P.n, ω (pf k) (pf (k + 1)) ^ θ := hkey
        _ = thetaEnergy ω θ P := by
            unfold thetaEnergy; rw [← Fin.sum_univ_eq_sum_range]
            congr 1; ext ⟨k, hk⟩
            rw [hpf_left k hk, hpf_right k hk]
    -- Induction
    intro K; induction K with
    | zero =>
      intro _
      rw [show (φ ⟨0, by omega⟩).val = 0 from congrArg Fin.val hφ_start]
      simp
    | succ K ih =>
      intro hK
      have hφ_le : (φ ⟨K, by omega⟩).val ≤ (φ ⟨K + 1, by omega⟩).val :=
        hφ_mono (show (⟨K, by omega⟩ : Fin (P.n + 1)) ≤ ⟨K + 1, by omega⟩ from by
          show K ≤ K + 1; omega)
      have hsplit : ∑ j ∈ Finset.Ico 0 (φ ⟨K + 1, by omega⟩).val,
          ω (g j) (g (j + 1)) ^ θ =
        ∑ j ∈ Finset.Ico 0 (φ ⟨K, by omega⟩).val, ω (g j) (g (j + 1)) ^ θ +
        ∑ j ∈ Finset.Ico (φ ⟨K, by omega⟩).val (φ ⟨K + 1, by omega⟩).val,
          ω (g j) (g (j + 1)) ^ θ :=
        (Finset.sum_Ico_consecutive _ (Nat.zero_le _) hφ_le).symm
      rw [hsplit, Finset.sum_range_succ]
      apply add_le_add (ih (by omega))
      rw [hpf_left K (by omega), hpf_right K (by omega)]
      exact hgroup_bound ⟨K, by omega⟩



end ThetaEnergy

end StochCalc
