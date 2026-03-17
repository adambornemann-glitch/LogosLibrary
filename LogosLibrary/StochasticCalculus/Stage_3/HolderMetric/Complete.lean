/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_3/HolderMetric/Complete.lean
-/
import LogosLibrary.StochasticCalculus.Stage_3.HolderMetric.Metric
/-!
# Completeness of the Hölder rough path space

## Overview

We prove that `RoughPathOn V γ a b` is a complete metric space
(when `V` and `T₂ V` are complete). This is the key input for
Stage 4's Banach fixed-point / Picard iteration argument.

## Structure of the proof

Given a Cauchy sequence `Xⁿ` in `roughPathDist`:

### Step 1: Pointwise Cauchy
The distance controls pointwise differences:
```
  ‖xⁿ(s,t) − xᵐ(s,t)‖ ≤ d(Xⁿ, Xᵐ) · |t−s|^γ
```
So for each fixed `(s, t)`, the sequence `xⁿ(s,t)` is Cauchy in `V`,
and `areaⁿ(s,t)` is Cauchy in `T₂ V`.

### Step 2: Pointwise limits
By completeness of `V` and `T₂ V`, the pointwise limits exist:
```
  x(s,t) := lim_n xⁿ(s,t)
  area(s,t) := lim_n areaⁿ(s,t)
```

### Step 3: Chen's identities pass to the limit
Both Chen identities are closed conditions — continuous algebraic
relations. If `xⁿ(s,t) = xⁿ(s,u) + xⁿ(u,t)` for all n, then
`x(s,t) = x(s,u) + x(u,t)` by continuity of addition.

For Chen₂, the key is the cross-norm: the tensor product
`xⁿ(s,u) ⊗ xⁿ(u,t) → x(s,u) ⊗ x(u,t)` by the estimate
```
  ‖v₁ ⊗ w₁ − v₂ ⊗ w₂‖ ≤ ‖v₁‖·‖w₁ − w₂‖ + ‖v₁ − v₂‖·‖w₂‖
```
and the boundedness of the Hölder constants.

### Step 4: Hölder bounds pass to the limit
This is the step that is **trivial** in the Hölder formulation but
hard in p-variation. If `‖xⁿ(s,t)‖ ≤ Cₙ · |t−s|^γ` and the
constants `Cₙ` are bounded (which follows from Cauchy + triangle),
then taking n → ∞:
```
  ‖x(s,t)‖ = lim ‖xⁿ(s,t)‖ ≤ lim sup Cₙ · |t−s|^γ ≤ C · |t−s|^γ
```
No lower-semicontinuity argument needed.

### Step 5: Convergence in d
For any ε > 0, take N such that `d(Xⁿ, Xᵐ) < ε` for n, m ≥ N.
Then for each (s,t):
```
  ‖xⁿ(s,t) − x(s,t)‖ = lim_m ‖xⁿ(s,t) − xᵐ(s,t)‖ ≤ ε · |t−s|^γ
```
Taking sup over (s,t): `d₁(Xⁿ, X) ≤ ε`. Similarly for d₂.
Hence `d(Xⁿ, X) → 0`.

## Key advantage over p-variation

In the p-variation formulation, Step 4 requires **lower semicontinuity**
of the p-variation functional:
```
  ‖f‖_{p-var} ≤ lim inf_n ‖fⁿ‖_{p-var}
```
This is true but requires a non-trivial argument (pass partition sums
to the limit, then take sup). In the Hölder formulation, the bound is
pointwise and passes to the limit trivially.

## References

* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., §8.1
* Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as
  Rough Paths*, Cambridge (2010), Chapter 8
-/

open NormedTensorSquare Real Set Filter Topology

noncomputable section

namespace StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]
variable {γ a b : ℝ}

/-! ### Step 1: Cauchy sequence ⟹ pointwise Cauchy

The distance controls pointwise differences, so a Cauchy sequence
in `d` gives Cauchy sequences at each point `(s, t)`. -/

/-- A Cauchy sequence in rough path distance has Cauchy level-1
increments at each point.

The key estimate: `‖xⁿ(s,t) − xᵐ(s,t)‖ ≤ d(Xⁿ, Xᵐ) · |t−s|^γ`.
Since `d(Xⁿ, Xᵐ) → 0`, the RHS → 0, so the LHS → 0. -/
lemma cauchySeq_x_of_cauchySeq
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    CauchySeq (fun n => (X n).x s t) := by
  rcases hst.eq_or_lt with rfl | hst'
  · simp_rw [(X _).x_diag s has htb]
    exact cauchySeq_const 0
  · rw [Metric.cauchySeq_iff]
    intro ε hε
    have hts_pos : 0 < |t - s| ^ γ := by
      apply rpow_pos_of_pos; rw [abs_pos]
      exact sub_ne_zero.mpr (ne_of_lt hst').symm
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hC (ε / |t - s| ^ γ) (div_pos hε hts_pos)
    exact ⟨N, fun n hn m hm => by
      rw [dist_eq_norm]
      calc ‖(X n).x s t - (X m).x s t‖
          ≤ dist (X n) (X m) * |t - s| ^ γ :=
            roughPathDist_controls₁ (X n) (X m) has hst' htb
        _ < ε / |t - s| ^ γ * |t - s| ^ γ :=
            mul_lt_mul_of_pos_right (hN n hn m hm) hts_pos
        _ = ε := div_mul_cancel₀ ε (ne_of_gt hts_pos)⟩

lemma cauchySeq_area_of_cauchySeq
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    CauchySeq (fun n => (X n).area s t) := by
  rcases hst.eq_or_lt with rfl | hst'
  · simp_rw [(X _).area_diag s has htb]
    exact cauchySeq_const 0
  · rw [Metric.cauchySeq_iff]
    intro ε hε
    have hts_pos : 0 < |t - s| ^ (2 * γ) := by
      apply rpow_pos_of_pos; rw [abs_pos]
      exact sub_ne_zero.mpr (ne_of_lt hst').symm
    set δ := Real.sqrt (ε / |t - s| ^ (2 * γ))
    have hδ_pos : 0 < δ := Real.sqrt_pos_of_pos (div_pos hε hts_pos)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hC δ hδ_pos
    exact ⟨N, fun n hn m hm => by
      rw [dist_eq_norm]
      calc ‖(X n).area s t - (X m).area s t‖
          ≤ dist (X n) (X m) ^ 2 * |t - s| ^ (2 * γ) :=
            roughPathDist_controls₂ (X n) (X m) has hst' htb
        _ < δ ^ 2 * |t - s| ^ (2 * γ) := by
            apply mul_lt_mul_of_pos_right _ hts_pos
            exact pow_lt_pow_left₀ (hN n hn m hm) dist_nonneg two_ne_zero
        _ = ε := by
            rw [Real.sq_sqrt (div_nonneg hε.le hts_pos.le),
                div_mul_cancel₀ ε (ne_of_gt hts_pos)]⟩

/-- More useful form: the level-1 sequence is Cauchy, stated via
`Metric.cauchySeq_iff` for explicit ε-N extraction. -/
lemma cauchySeq_x_of_cauchySeq' [CompleteSpace V]
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X)
    {s t : ℝ} (has : a ≤ s) (hst : s < t) (htb : t ≤ b) :
    ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m →
      ‖(X n).x s t - (X m).x s t‖ < ε := by
  intro ε hε
  have hts_pos : 0 < |t - s| ^ γ :=
    rpow_pos_of_pos (by simp only [abs_pos, ne_eq]; linarith) _
  rw [Metric.cauchySeq_iff] at hC
  obtain ⟨N, hN⟩ := hC (ε / |t - s| ^ γ) (div_pos hε hts_pos)
  refine ⟨N, fun n m hn hm => ?_⟩
  calc ‖(X n).x s t - (X m).x s t‖
      ≤ dist (X n) (X m) * |t - s| ^ γ :=
        roughPathDist_controls₁ (X n) (X m) has hst htb
    _ < ε / |t - s| ^ γ * |t - s| ^ γ := by
        gcongr; exact hN n hn m hm
    _ = ε := div_mul_cancel₀ ε (ne_of_gt hts_pos)

/-- Level-2: Cauchy sequence of areas at each point. -/
lemma cauchySeq_area_of_cauchySeq' [CompleteSpace (T₂ V)]
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X)
    {s t : ℝ} (has : a ≤ s) (hst : s < t) (htb : t ≤ b) :
    ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m →
      ‖(X n).area s t - (X m).area s t‖ < ε := by
  intro ε hε
  have hts_pos : 0 < |t - s| ^ (2 * γ) :=
    rpow_pos_of_pos (by simp only [abs_pos, ne_eq]; linarith) _
  -- d₂ ≤ d², so ‖area diff‖ ≤ d² · |t-s|^{2γ}
  -- For d < √(ε / |t-s|^{2γ}), we get ‖area diff‖ < ε
  rw [Metric.cauchySeq_iff] at hC
  set δ := Real.sqrt (ε / |t - s| ^ (2 * γ)) with hδ_def
  have hδ_pos : 0 < δ := Real.sqrt_pos.mpr (div_pos hε hts_pos)
  obtain ⟨N, hN⟩ := hC δ hδ_pos
  refine ⟨N, fun n m hn hm => ?_⟩
  have hdist := hN n hn m hm
  calc ‖(X n).area s t - (X m).area s t‖
      ≤ dist (X n) (X m) ^ 2 * |t - s| ^ (2 * γ) :=
        roughPathDist_controls₂ (X n) (X m) has hst htb
    _ < δ ^ 2 * |t - s| ^ (2 * γ) := by
        gcongr
    _ = ε := by
        rw [hδ_def, Real.sq_sqrt (div_nonneg hε.le hts_pos.le),
            div_mul_cancel₀ ε (ne_of_gt hts_pos)]

/-! ### Step 2: Pointwise limits

By completeness of V and T₂ V, we extract pointwise limits.
We define the limit functions using `limUnder` (the Mathlib limit). -/

section PointwiseLimits

variable [CompleteSpace V]

/-- The pointwise limit of the level-1 increments. -/
noncomputable def cauchySeqLim_x
    (X : ℕ → RoughPathOn V γ a b) (s t : ℝ) : V :=
  if _h : a ≤ s ∧ s ≤ t ∧ t ≤ b then
    limUnder atTop (fun n => (X n).x s t)
  else 0

/-- The pointwise limit of the level-2 areas. -/
noncomputable def cauchySeqLim_area
    (X : ℕ → RoughPathOn V γ a b) (s t : ℝ) : T₂ V :=
  if _h : a ≤ s ∧ s ≤ t ∧ t ≤ b then
    limUnder atTop (fun n => (X n).area s t)
  else 0


/-- The level-1 sequence converges to the limit at each point in the domain. -/
lemma tendsto_x_of_cauchySeq
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    Tendsto (fun n => (X n).x s t) atTop (𝓝 (cauchySeqLim_x X s t)) := by
  have h_dom : a ≤ s ∧ s ≤ t ∧ t ≤ b := ⟨has, hst, htb⟩
  simp only [cauchySeqLim_x, dif_pos h_dom]
  exact (cauchySeq_x_of_cauchySeq X hC has hst htb).tendsto_limUnder



omit [CompleteSpace V] in
/-- The level-2 sequence converges to the limit at each point in the domain. -/
lemma tendsto_area_of_cauchySeq
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    Tendsto (fun n => (X n).area s t) atTop (𝓝 (cauchySeqLim_area X s t)) := by
  have h_dom : a ≤ s ∧ s ≤ t ∧ t ≤ b := ⟨has, hst, htb⟩
  simp only [cauchySeqLim_area, dif_pos h_dom]
  exact (cauchySeq_area_of_cauchySeq X hC has hst htb).tendsto_limUnder

end PointwiseLimits

/-! ### Step 3: Algebraic identities pass to the limit

Chen₁ and Chen₂ are continuous algebraic relations. -/

section ChenLimit

variable [CompleteSpace V]

/-- Chen₁ passes to the limit: `x(s,t) = x(s,u) + x(u,t)`.

Proof: `xⁿ(s,t) = xⁿ(s,u) + xⁿ(u,t)` for all n, and both sides
converge (by Step 2), so the identity holds in the limit by
continuity of addition. -/
lemma chen₁_limit
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    cauchySeqLim_x X s t =
      cauchySeqLim_x X s u + cauchySeqLim_x X u t := by
  -- xⁿ(s,t) → x(s,t), xⁿ(s,u) → x(s,u), xⁿ(u,t) → x(u,t)
  have h_st := tendsto_x_of_cauchySeq X hC has (hsu.trans hut) htb
  have h_su := tendsto_x_of_cauchySeq X hC has hsu (hut.trans htb)
  have h_ut := tendsto_x_of_cauchySeq X hC (has.trans hsu) hut htb
  -- xⁿ(s,t) = xⁿ(s,u) + xⁿ(u,t) for all n
  have h_chen : ∀ n, (X n).x s t = (X n).x s u + (X n).x u t :=
    fun n => (X n).chen₁ s u t has hsu hut htb
  -- Pass to limit: lim(LHS) = lim(RHS)
  exact tendsto_nhds_unique h_st
    (by rw [show (fun n => (X n).x s t) = (fun n => (X n).x s u + (X n).x u t)
          from funext h_chen]
        exact h_su.add h_ut)


/-- Chen₂ passes to the limit:
`area(s,t) = area(s,u) + area(u,t) + x(s,u) ⊗ x(u,t)`.

The tensor product term converges because:
- `xⁿ(s,u) → x(s,u)` and `xⁿ(u,t) → x(u,t)` (Step 2)
- `tprod` is a continuous bilinear map
- So `xⁿ(s,u) ⊗ xⁿ(u,t) → x(s,u) ⊗ x(u,t)` -/
lemma chen₂_limit
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    cauchySeqLim_area X s t =
      cauchySeqLim_area X s u + cauchySeqLim_area X u t +
      cauchySeqLim_x X s u ⊗ₜ cauchySeqLim_x X u t := by
  have h_area_st := tendsto_area_of_cauchySeq X hC has (hsu.trans hut) htb
  have h_area_su := tendsto_area_of_cauchySeq X hC has hsu (hut.trans htb)
  have h_area_ut := tendsto_area_of_cauchySeq X hC (has.trans hsu) hut htb
  have h_x_su := tendsto_x_of_cauchySeq X hC has hsu (hut.trans htb)
  have h_x_ut := tendsto_x_of_cauchySeq X hC (has.trans hsu) hut htb
  -- tprod is continuous bilinear, so the tensor product converges
  have h_tprod : Tendsto
      (fun n => (tprod ((X n).x s u)) ((X n).x u t)) atTop
      (𝓝 ((tprod (cauchySeqLim_x X s u)) (cauchySeqLim_x X u t))) := by
    have hcont : Continuous (fun p : V × V => (tprod (V := V) p.1) p.2) :=
      (tprod (V := V)).isBoundedBilinearMap.continuous
    have h_prod : Tendsto (fun n => ((X n).x s u, (X n).x u t)) atTop
        (𝓝 (cauchySeqLim_x X s u, cauchySeqLim_x X u t)) := by
      rw [nhds_prod_eq]
      exact Tendsto.prodMk h_x_su h_x_ut
    exact hcont.continuousAt.tendsto.comp h_prod
  -- Chen₂ for each n
  have h_chen : ∀ n, (X n).area s t =
      (X n).area s u + (X n).area u t +
      (tprod ((X n).x s u)) ((X n).x u t) :=
    fun n => (X n).chen₂ s u t has hsu hut htb
  -- Pass to limit
  exact tendsto_nhds_unique h_area_st
    (by rw [show (fun n => (X n).area s t) = (fun n =>
          (X n).area s u + (X n).area u t +
          (tprod ((X n).x s u)) ((X n).x u t))
        from funext h_chen]
        exact (h_area_su.add h_area_ut).add h_tprod)

end ChenLimit

/-! ### Step 4: Hölder bounds pass to the limit

This is the **easy** step in the Hölder formulation.
If `‖xⁿ(s,t)‖ ≤ C · |t−s|^γ` for all n (with uniform C),
then `‖x(s,t)‖ ≤ C · |t−s|^γ` by continuity of the norm. -/

section HolderLimit


/-- Uniform bound on the Hölder constants of a Cauchy sequence.

A Cauchy sequence is bounded, hence the Hölder constants are bounded. -/
lemma cauchySeq_holder_bound
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X) :
    ∃ C_unif ≥ 0, ∀ n s t, a ≤ s → s ≤ t → t ≤ b →
      ‖(X n).x s t‖ ≤ C_unif * |t - s| ^ γ := by
  -- Cauchy ⟹ bounded range
  have hbdd := hC.isBounded_range
  rw [Metric.isBounded_range_iff] at hbdd
  obtain ⟨R, hR⟩ := hbdd
  -- Use C_unif = max 0 (R + C₁(X 0)) to guarantee nonnegativity
  refine ⟨max 0 (R + (X 0).C₁), le_max_left _ _, fun n s t has hst htb => ?_⟩
  rcases hst.eq_or_lt with rfl | hst'
  · rw [(X n).x_diag s has htb, norm_zero]
    exact mul_nonneg (le_max_left _ _) (rpow_nonneg (abs_nonneg _) _)
  · calc ‖(X n).x s t‖
        ≤ ‖(X n).x s t - (X 0).x s t‖ + ‖(X 0).x s t‖ :=
          norm_le_norm_sub_add ((X n).x s t) ((X 0).x s t)
      _ ≤ dist (X n) (X 0) * |t - s| ^ γ + (X 0).C₁ * |t - s| ^ γ := by
          gcongr
          · exact roughPathDist_controls₁ (X n) (X 0) has hst' htb
          · exact (X 0).x_holder s t has hst'.le htb
      _ ≤ R * |t - s| ^ γ + (X 0).C₁ * |t - s| ^ γ := by
          gcongr; exact hR n 0
      _ = (R + (X 0).C₁) * |t - s| ^ γ := by ring
      _ ≤ max 0 (R + (X 0).C₁) * |t - s| ^ γ := by
          apply mul_le_mul_of_nonneg_right (le_max_right _ _)
            (rpow_nonneg (abs_nonneg _) _)



lemma cauchySeq_area_holder_bound
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X) :
    ∃ C_unif ≥ 0, ∀ n s t, a ≤ s → s ≤ t → t ≤ b →
      ‖(X n).area s t‖ ≤ C_unif * |t - s| ^ (2 * γ) := by
  have hbdd := hC.isBounded_range
  rw [Metric.isBounded_range_iff] at hbdd
  obtain ⟨R, hR⟩ := hbdd
  refine ⟨max 0 (R ^ 2 + (X 0).C₂), le_max_left _ _, fun n s t has hst htb => ?_⟩
  rcases hst.eq_or_lt with rfl | hst'
  · rw [(X n).area_diag s has htb, norm_zero]
    exact mul_nonneg (le_max_left _ _) (rpow_nonneg (abs_nonneg _) _)
  · calc ‖(X n).area s t‖
        ≤ ‖(X n).area s t - (X 0).area s t‖ + ‖(X 0).area s t‖ :=
          norm_le_norm_sub_add ((X n).area s t) ((X 0).area s t)
      _ ≤ dist (X n) (X 0) ^ 2 * |t - s| ^ (2 * γ) +
            (X 0).C₂ * |t - s| ^ (2 * γ) := by
          gcongr
          · exact roughPathDist_controls₂ (X n) (X 0) has hst' htb
          · exact (X 0).area_holder s t has hst'.le htb
      _ ≤ R ^ 2 * |t - s| ^ (2 * γ) + (X 0).C₂ * |t - s| ^ (2 * γ) := by
          gcongr
          exact Metric.mem_closedBall.mp (hR n 0)
      _ = (R ^ 2 + (X 0).C₂) * |t - s| ^ (2 * γ) := by ring
      _ ≤ max 0 (R ^ 2 + (X 0).C₂) * |t - s| ^ (2 * γ) := by
          apply mul_le_mul_of_nonneg_right (le_max_right _ _)
            (rpow_nonneg (abs_nonneg _) _)


lemma cauchySeqLim_area_holder
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X) :
    ∃ C ≥ 0, ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖cauchySeqLim_area X s t‖ ≤ C * |t - s| ^ (2 * γ) := by
  obtain ⟨C_unif, hC_nn, hC_bound⟩ := cauchySeq_area_holder_bound X hC
  refine ⟨C_unif, hC_nn, fun s t has hst htb => ?_⟩
  have h_tendsto := tendsto_area_of_cauchySeq X hC has hst htb
  have h_norm : Tendsto (fun n => ‖(X n).area s t‖) atTop
      (𝓝 ‖cauchySeqLim_area X s t‖) :=
    continuous_norm.continuousAt.tendsto.comp h_tendsto
  exact le_of_tendsto h_norm
    (Eventually.of_forall fun n => hC_bound n s t has hst htb)


variable [CompleteSpace V]
/-- The level-1 limit satisfies a Hölder bound. -/
lemma cauchySeqLim_x_holder
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X) :
    ∃ C ≥ 0, ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖cauchySeqLim_x X s t‖ ≤ C * |t - s| ^ γ := by
  obtain ⟨C_unif, hC_nn, hC_bound⟩ := cauchySeq_holder_bound X hC
  refine ⟨C_unif, hC_nn, fun s t has hst htb => ?_⟩
  have h_tendsto := tendsto_x_of_cauchySeq X hC has hst htb
  have h_norm : Tendsto (fun n => ‖(X n).x s t‖) atTop
      (𝓝 ‖cauchySeqLim_x X s t‖) :=
    continuous_norm.continuousAt.tendsto.comp h_tendsto
  exact le_of_tendsto h_norm
    (Eventually.of_forall fun n => hC_bound n s t has hst htb)


end HolderLimit

/-! ### Step 5: Assemble the limit rough path -/

section Assembly

variable [CompleteSpace V] [CompleteSpace (T₂ V)]

/-- The limit of a Cauchy sequence of rough paths is itself a rough path. -/
noncomputable def cauchySeqLim
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X) :
    RoughPathOn V γ a b where
  x := cauchySeqLim_x X
  area := cauchySeqLim_area X
  chen₁ := fun s u t has hsu hut htb =>
    chen₁_limit X hC has hsu hut htb
  chen₂ := fun s u t has hsu hut htb =>
    chen₂_limit X hC has hsu hut htb
  x_diag := fun s has hsb => by
    have h_lim := tendsto_x_of_cauchySeq X hC has le_rfl hsb
    have h_zero : Tendsto (fun n => (X n).x s s) atTop (𝓝 0) := by
      simp_rw [(X _).x_diag s has hsb]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h_lim h_zero
  area_diag := fun s has hsb => by
    have h_lim := tendsto_area_of_cauchySeq X hC has le_rfl hsb
    have h_zero : Tendsto (fun n => (X n).area s s) atTop (𝓝 0) := by
      simp_rw [(X _).area_diag s has hsb]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h_lim h_zero
  x_bound := cauchySeqLim_x_holder X hC
  area_bound := cauchySeqLim_area_holder X hC
  x_default := fun s t h => by
    simp only [cauchySeqLim_x, dif_neg h]
  area_default := fun s t h => by
    simp only [cauchySeqLim_area, dif_neg h]

end Assembly

/-! ### Step 6: Convergence in d -/

section Convergence

variable [CompleteSpace V]

/-- The level-1 Hölder distance `d₁(Xⁿ, X)` converges to 0.

For any ε > 0, take N such that `d(Xⁿ, Xᵐ) < ε` for n, m ≥ N.
Then for each (s,t) with s < t:
```
  ‖xⁿ(s,t) − x(s,t)‖ = lim_m ‖xⁿ(s,t) − xᵐ(s,t)‖
                       ≤ lim_m d(Xⁿ, Xᵐ) · |t−s|^γ
                       ≤ ε · |t−s|^γ
```
Taking `sSup`: `d₁(Xⁿ, X) ≤ ε`.
-/
lemma holderDist₁_tendsto_zero
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X) :
    Tendsto (fun n => holderDist₁ (X n) (cauchySeqLim X hC)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hC (ε / 2) hε2
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_0_eq_abs, abs_of_nonneg (holderDist₁_nonneg _ _)]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply holderDist₁_le_of_bound _ _ hε2.le
  intro s t has hst htb
  -- Pass m → ∞ in ‖xⁿ(s,t) − xᵐ(s,t)‖ ≤ (ε/2) · |t-s|^γ
  have h_tendsto := tendsto_x_of_cauchySeq X hC has hst.le htb
  have h_diff_tendsto : Tendsto (fun m => ‖(X n).x s t - (X m).x s t‖) atTop
      (𝓝 ‖(X n).x s t - cauchySeqLim_x X s t‖) :=
    continuous_norm.continuousAt.tendsto.comp (tendsto_const_nhds.sub h_tendsto)
  apply le_of_tendsto h_diff_tendsto
  filter_upwards [Filter.Ici_mem_atTop N] with m hm
  calc ‖(X n).x s t - (X m).x s t‖
      ≤ dist (X n) (X m) * |t - s| ^ γ :=
        roughPathDist_controls₁ _ _ has hst htb
    _ ≤ (ε / 2) * |t - s| ^ γ := by
        gcongr
        exact Std.le_of_lt (hN n hn m hm)


/-- The level-2 Hölder distance `d₂(Xⁿ, X)` converges to 0. -/
lemma holderDist₂_tendsto_zero
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X) :
    Tendsto (fun n => holderDist₂ (X n) (cauchySeqLim X hC)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  -- Choose δ = √(ε/2) so that d < δ ⟹ d² < ε/2
  set δ := Real.sqrt (ε / 2) with hδ_def
  have hδ_pos : 0 < δ := Real.sqrt_pos_of_pos hε2
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hC δ hδ_pos
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_0_eq_abs, abs_of_nonneg (holderDist₂_nonneg _ _)]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply holderDist₂_le_of_bound _ _ hε2.le
  intro s t has hst htb
  -- Pass m → ∞ in ‖areaⁿ(s,t) − areaᵐ(s,t)‖ ≤ d(Xⁿ,Xᵐ)² · |t-s|^{2γ}
  have h_tendsto := tendsto_area_of_cauchySeq X hC has hst.le htb
  have h_diff_tendsto : Tendsto (fun m => ‖(X n).area s t - (X m).area s t‖) atTop
      (𝓝 ‖(X n).area s t - cauchySeqLim_area X s t‖) :=
    continuous_norm.continuousAt.tendsto.comp (tendsto_const_nhds.sub h_tendsto)
  apply le_of_tendsto h_diff_tendsto
  filter_upwards [Filter.Ici_mem_atTop N] with m hm
  calc ‖(X n).area s t - (X m).area s t‖
      ≤ dist (X n) (X m) ^ 2 * |t - s| ^ (2 * γ) :=
        roughPathDist_controls₂ _ _ has hst htb
    _ ≤ δ ^ 2 * |t - s| ^ (2 * γ) := by
        gcongr
        exact Std.le_of_lt (hN n hn m hm)
    _ = (ε / 2) * |t - s| ^ (2 * γ) := by
        rw [hδ_def, Real.sq_sqrt hε2.le]



/-- **Convergence**: `d(Xⁿ, X) → 0` where `X` is the limit rough path. -/
theorem roughPathDist_tendsto_zero
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X) :
    Tendsto (fun n => roughPathDist (X n) (cauchySeqLim X hC)) atTop (𝓝 0) := by
  have h₁ := holderDist₁_tendsto_zero X hC
  have h₂ := holderDist₂_tendsto_zero X hC
  have h₂' : Tendsto (fun n => (holderDist₂ (X n) (cauchySeqLim X hC)) ^ (1/2 : ℝ))
      atTop (𝓝 0) := by
    rw [show (0 : ℝ) = (0 : ℝ) ^ (1/2 : ℝ) from by simp]
    exact h₂.rpow_const (Or.inr (by norm_num : (0:ℝ) ≤ 1/2))
  show Tendsto (fun n => holderDist₁ (X n) (cauchySeqLim X hC) +
      (holderDist₂ (X n) (cauchySeqLim X hC)) ^ (1/2 : ℝ)) atTop (𝓝 0)
  simpa using h₁.add h₂'

end Convergence


/-! ### The CompleteSpace instance -/

/-- **Completeness**: `RoughPathOn V γ a b` is a complete metric space
(when `V` and `T₂ V` are complete and `γ > 0`).

This is the main result of Phase 3.1, together with `Metric.lean`.
Stage 4's Banach fixed-point theorem applies in this space. -/
instance roughPathOn_completeSpace
    [CompleteSpace V] [CompleteSpace (T₂ V)]
    {γ a b : ℝ} (hγ : 0 < γ) :
    @CompleteSpace (RoughPathOn V γ a b)
      (roughPathOn_metricSpace hγ).toUniformSpace := by
  letI : MetricSpace (RoughPathOn V γ a b) := roughPathOn_metricSpace hγ
  exact Metric.complete_of_cauchySeq_tendsto fun X hC =>
    ⟨cauchySeqLim X hC,
     tendsto_iff_dist_tendsto_zero.mpr (roughPathDist_tendsto_zero X hC)⟩

/-- Sequential completeness (the form most useful for direct application). -/
theorem roughPathOn_cauchySeq_tendsto
    [CompleteSpace V] [CompleteSpace (T₂ V)]
    {γ a b : ℝ} (_hγ : 0 < γ)
    (X : ℕ → RoughPathOn V γ a b) (hC : CauchySeq X) :
    ∃ X_lim, Tendsto X atTop (𝓝 X_lim) := by
  letI : MetricSpace (RoughPathOn V γ a b) := roughPathOn_metricSpace _hγ
  exact ⟨cauchySeqLim X hC,
    tendsto_iff_dist_tendsto_zero.mpr (roughPathDist_tendsto_zero X hC)⟩

end StochCalc
