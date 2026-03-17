/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_3/Geometric/Closed.lean
-/
import LogosLibrary.StochasticCalculus.Stage_3.Geometric.Defs
/-!
# The geometric condition is closed under limits

## Overview

We prove that `IsGeometric` is a closed condition: if `Xⁿ → X` in
the rough path metric and each `Xⁿ` is geometric, then `X` is geometric.

This is the key structural result for Phase 3.3. Combined with the
completeness of `RoughPathOn` (Phase 3.1), it gives:
- `GeometricRoughPathOn` is a closed subset of a complete metric space
- Therefore `GeometricRoughPathOn` is itself complete

## Proof strategy

The geometric condition is `Sym(𝕏(s,t)) = ½ X(s,t) ⊗ X(s,t)`.

Both sides are continuous in the rough path metric:
- **LHS**: `Sym` is a continuous linear map, and `𝕏ⁿ(s,t) → 𝕏(s,t)`
  pointwise (from `d(Xⁿ, X) → 0`).
- **RHS**: `tprod` is a continuous bilinear map, and `Xⁿ(s,t) → X(s,t)`
  pointwise.

Since both sides converge and agree for all n, they agree in the limit.

## What this gives Stage 4

```lean
-- The Picard fixed-point for geometric RDEs:
-- if X is geometric and f is smooth enough, then
-- the solution Y to dY = f(Y) dX is controlled by a geometric rough path.
-- Completeness of GeometricRoughPathOn ensures the iteration converges.
```

## References

* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., §2.3
-/

open NormedTensorSquare Real Set Filter Topology StochCalc.RoughPathOn StochCalc.GeometricRoughPathOn

noncomputable section

namespace StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]
variable {γ a b : ℝ}

/-! ### Continuity of the geometric condition

The two sides of `Sym(𝕏) = ½ X ⊗ X` are each continuous in the
rough path metric. We establish this via pointwise convergence. -/

/-- If `Xⁿ → X` in the rough path metric, then `Sym(𝕏ⁿ(s,t)) → Sym(𝕏(s,t))`.

This follows from `𝕏ⁿ(s,t) → 𝕏(s,t)` (pointwise, from the metric)
and continuity of `Sym`. -/
lemma tendsto_sym_area
    (X : ℕ → RoughPathOn V γ a b) (X_lim : RoughPathOn V γ a b)
    (h : Tendsto X atTop (𝓝 X_lim))
    {s t : ℝ} (has : a ≤ s) (hst : s < t) (htb : t ≤ b) :
    Tendsto (fun n => sym ((X n).area s t)) atTop
      (𝓝 (sym (X_lim.area s t))) := by
  have h_area : Tendsto (fun n => (X n).area s t) atTop (𝓝 (X_lim.area s t)) := by
    rw [Metric.tendsto_atTop] at h ⊢
    intro ε hε
    have hts_pos : 0 < |t - s| ^ (2 * γ) :=
      rpow_pos_of_pos (by rw [abs_pos]; linarith) _
    set δ := Real.sqrt (ε / |t - s| ^ (2 * γ))
    have hδ_pos : 0 < δ := Real.sqrt_pos_of_pos (div_pos hε hts_pos)
    obtain ⟨N, hN⟩ := h δ hδ_pos
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    calc ‖(X n).area s t - X_lim.area s t‖
        ≤ dist (X n) X_lim ^ 2 * |t - s| ^ (2 * γ) :=
          roughPathDist_controls₂ _ _ has hst htb
      _ < δ ^ 2 * |t - s| ^ (2 * γ) := by
          apply mul_lt_mul_of_pos_right _ hts_pos
          exact pow_lt_pow_left₀ (hN n hn) dist_nonneg two_ne_zero
      _ = ε := by
          rw [Real.sq_sqrt (div_nonneg hε.le hts_pos.le),
              div_mul_cancel₀ ε (ne_of_gt hts_pos)]
  have h_sym_cont : Continuous (sym (V := V)) := by
    unfold sym
    exact continuous_const.smul (continuous_id.add (swap (V := V)).continuous)
  exact h_sym_cont.continuousAt.tendsto.comp h_area

/-- If `Xⁿ → X` in the rough path metric, then
`½ Xⁿ(s,t) ⊗ Xⁿ(s,t) → ½ X(s,t) ⊗ X(s,t)`.

This follows from `Xⁿ(s,t) → X(s,t)` and continuity of `tprod`. -/
lemma tendsto_half_tprod_self
    (X : ℕ → RoughPathOn V γ a b) (X_lim : RoughPathOn V γ a b)
    (h : Tendsto X atTop (𝓝 X_lim))
    {s t : ℝ} (has : a ≤ s) (hst : s < t) (htb : t ≤ b) :
    Tendsto (fun n => (2⁻¹ : ℝ) • ((X n).x s t ⊗ₜ (X n).x s t)) atTop
      (𝓝 ((2⁻¹ : ℝ) • (X_lim.x s t ⊗ₜ X_lim.x s t))) := by
  -- Xⁿ(s,t) → X(s,t) pointwise
  have h_x : Tendsto (fun n => (X n).x s t) atTop (𝓝 (X_lim.x s t)) := by
    rw [Metric.tendsto_atTop] at h ⊢
    intro ε hε
    have hts_pos : 0 < |t - s| ^ γ :=
      rpow_pos_of_pos (by rw [abs_pos]; linarith) _
    obtain ⟨N, hN⟩ := h (ε / |t - s| ^ γ) (div_pos hε hts_pos)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    calc ‖(X n).x s t - X_lim.x s t‖
        ≤ dist (X n) X_lim * |t - s| ^ γ :=
          roughPathDist_controls₁ _ _ has hst htb
      _ < ε / |t - s| ^ γ * |t - s| ^ γ := by
          gcongr; exact hN n hn
      _ = ε := div_mul_cancel₀ ε (ne_of_gt hts_pos)
  -- tprod is continuous bilinear ⟹ v ↦ v ⊗ v is continuous
  have h_tprod : Tendsto
      (fun n => (tprod ((X n).x s t)) ((X n).x s t)) atTop
      (𝓝 ((tprod (X_lim.x s t)) (X_lim.x s t))) := by
    have hcont : Continuous (fun p : V × V => (tprod (V := V) p.1) p.2) :=
      (tprod (V := V)).isBoundedBilinearMap.continuous
    have h_prod : Tendsto (fun n => ((X n).x s t, (X n).x s t)) atTop
        (𝓝 (X_lim.x s t, X_lim.x s t)) := by
      rw [nhds_prod_eq]
      exact Tendsto.prodMk h_x h_x
    exact hcont.continuousAt.tendsto.comp h_prod
  -- smul by constant is continuous
  exact h_tprod.const_smul _

/-! ### The main closedness result -/

/-- **Closedness of the geometric condition**: if `Xⁿ → X` in the
rough path metric and each `Xⁿ` is geometric, then `X` is geometric.

Proof: for each `(s, t)` with `s < t`,
```
  Sym(𝕏(s,t)) = lim Sym(𝕏ⁿ(s,t))     (continuity of Sym)
              = lim ½ Xⁿ(s,t) ⊗ Xⁿ(s,t)  (geometric condition for Xⁿ)
              = ½ X(s,t) ⊗ X(s,t)       (continuity of tprod)
```
For `s = t`, both sides are zero. -/
theorem isGeometric_of_tendsto
    (X : ℕ → RoughPathOn V γ a b) (X_lim : RoughPathOn V γ a b)
    (h_tendsto : Tendsto X atTop (𝓝 X_lim))
    (hg : ∀ n, IsGeometric (X n)) :
    IsGeometric X_lim := by
  intro s t has hst htb
  rcases hst.eq_or_lt with rfl | hst'
  · exact isGeometric_diag X_lim s has htb
  · have h_lhs := tendsto_sym_area X X_lim h_tendsto has hst' htb
    have h_rhs := tendsto_half_tprod_self X X_lim h_tendsto has hst' htb
    have h_eq : ∀ n, sym ((X n).area s t) =
        (2⁻¹ : ℝ) • ((tprod ((X n).x s t)) ((X n).x s t)) :=
      fun n => hg n s t has hst'.le htb
    have h_lhs' : Tendsto
        (fun n => (2⁻¹ : ℝ) • ((tprod ((X n).x s t)) ((X n).x s t))) atTop
        (𝓝 (sym (X_lim.area s t))) := by
      rw [show (fun n => (2⁻¹ : ℝ) • ((tprod ((X n).x s t)) ((X n).x s t))) =
            (fun n => sym ((X n).area s t)) from (funext h_eq).symm]
      exact h_lhs
    exact tendsto_nhds_unique h_lhs' h_rhs

/-- The set of geometric rough paths is closed in `RoughPathOn`. -/
theorem isClosed_isGeometric :
    IsClosed {X : RoughPathOn V γ a b | IsGeometric X} := by
  apply isSeqClosed_iff_isClosed.mp
  intro X X_lim hX hconv
  exact isGeometric_of_tendsto X X_lim hconv hX

/-! ### Completeness of geometric rough paths -/

/-- `MetricSpace` on `GeometricRoughPathOn`, induced from `RoughPathOn`. -/
noncomputable def geometricRoughPathOn_metricSpace
    {γ a b : ℝ} (hγ : 0 < γ) :
    MetricSpace (GeometricRoughPathOn V γ a b) :=
  MetricSpace.induced
    GeometricRoughPathOn.toRoughPathOn
    (fun X Y h => ext X Y h)
    (roughPathOn_metricSpace hγ)

instance geometricRoughPathOn_completeSpace
    [CompleteSpace V] [CompleteSpace (T₂ V)]
    {γ a b : ℝ} (hγ : 0 < γ) :
    @CompleteSpace (GeometricRoughPathOn V γ a b)
      (geometricRoughPathOn_metricSpace hγ).toUniformSpace := by
  letI : MetricSpace (RoughPathOn V γ a b) := roughPathOn_metricSpace hγ
  letI : MetricSpace (GeometricRoughPathOn V γ a b) :=
    geometricRoughPathOn_metricSpace hγ
  haveI : CompleteSpace (RoughPathOn V γ a b) := roughPathOn_completeSpace hγ
  apply Metric.complete_of_cauchySeq_tendsto
  intro X hC
  have hC_rp : CauchySeq (fun n => (X n).toRoughPathOn) := by
    rw [Metric.cauchySeq_iff] at hC ⊢
    exact fun ε hε => hC ε hε
  -- RoughPathOn is complete, so extract a limit
  obtain ⟨X_lim, hconv⟩ := cauchySeq_tendsto_of_complete hC_rp
  -- The limit is geometric (closed condition)
  have hg : IsGeometric X_lim :=
    isGeometric_of_tendsto _ X_lim hconv (fun n => (X n).geometric)
  -- Lift back and transfer convergence
  refine ⟨⟨X_lim, hg⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv ε hε
  exact ⟨N, fun n hn => hN n hn⟩

/-- Sequential completeness for geometric rough paths. -/
theorem geometricRoughPathOn_cauchySeq_tendsto
    [CompleteSpace V] [CompleteSpace (T₂ V)]
    {γ a b : ℝ} (hγ : 0 < γ)
    (X : ℕ → GeometricRoughPathOn V γ a b) (hC : CauchySeq (fun n => (X n).toRoughPathOn)) :
    ∃ X_lim : GeometricRoughPathOn V γ a b,
      Tendsto (fun n => (X n).toRoughPathOn) atTop (𝓝 X_lim.toRoughPathOn) := by
  -- The underlying sequence in RoughPathOn is Cauchy, hence converges
  obtain ⟨L, hL⟩ := roughPathOn_cauchySeq_tendsto hγ _ hC
  -- The limit is geometric by closedness
  have hg : IsGeometric L :=
    isGeometric_of_tendsto _ L hL (fun n => (X n).geometric)
  exact ⟨⟨L, hg⟩, hL⟩

end StochCalc
