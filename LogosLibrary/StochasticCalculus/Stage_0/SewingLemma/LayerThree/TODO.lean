/-
section LayerThreeFail

/-- The refinement cost bound `‖RS(P) - RS(P')‖ ≤ K · Φ_θ(P)` is false
for general continuous controls. Counterexample: Ξ(s,t) = s·(t-s) with
θ = 2 and K = 1/4. Inserting two points into a single interval produces
two non-cancelling defects, each bounded by K·ω^θ, exceeding the budget. -/
theorem riemannSum_refinement_bound_false :
    ∃ (Ξ : ℝ → ℝ → ℝ) (ω : ℝ → ℝ → ℝ) (θ K : ℝ)
      (P P' : Partition (0 : ℝ) 1),
      P'.IsRefinement P ∧
      (∀ s u t, 0 ≤ s → s ≤ u → u ≤ t → t ≤ 1 →
        |Ξ s t - Ξ s u - Ξ u t| ≤ K * |t - s| ^ θ) ∧
      1 < θ ∧ 0 ≤ K ∧
      |riemannSum Ξ P - riemannSum Ξ P'| >
        K * thetaEnergy ω θ P := by
  sorry


end LayerThreeFail
-/
