/-
/-- The p-variation on small intervals tends to zero for continuous functions
with finite p-variation. This is the key analytical engine. -/
private theorem ePVariationOn_Icc_tendsto_zero {p : ℝ} {f : ℝ → E} {a b : ℝ}
    (hp : 1 ≤ p) (hf : ContinuousOn f (Icc a b))
    (hfv : HasFinitePVariationOn p f (Icc a b)) :
    ∀ ε > 0, ∃ δ > 0, ∀ s t, s ∈ Icc a b → t ∈ Icc a b → |t - s| < δ →
      ePVariationOn p f (Icc s t) < ε := by
  -- By contradiction: suppose ∃ δ > 0 and intervals [sₙ, tₙ] with
  -- |tₙ - sₙ| → 0 but ePVariationOn p f (Icc sₙ tₙ) ≥ δ.
  -- By compactness of [a,b], pass to subsequence with sₙ → s₀.
  -- Greedily extract infinitely many DISJOINT intervals from the sequence.
  -- By iterated super-additivity (ePVariationOn_add_le):
  --   ∑ₖ ePVariationOn p f (Icc s_{nₖ} t_{nₖ}) ≤ ePVariationOn p f (Icc a b) < ⊤
  -- But each summand ≥ δ > 0 and there are infinitely many. Contradiction.
  sorry



/-- A continuous path with finite `p`-variation (for `p ≥ 1`) has continuous
`p`-variation. This is a standard result; see Friz–Victoir Proposition 5.3. -/
theorem hasContinuousPVariationOn_of_continuous {p : ℝ} {f : ℝ → E} {a b : ℝ}
    (hp : 1 ≤ p) (hf : ContinuousOn f (Icc a b))
    (hfv : HasFinitePVariationOn p f (Icc a b)) :
    HasContinuousPVariationOn p f a b := by
  rw [HasContinuousPVariationOn]
  set ω : ℝ → ℝ≥0∞ := fun t => ePVariationOn p f (Icc a t)
  -- ω is monotone
  have hω_mono : MonotoneOn ω (Icc a b) := by
    intro s hs t ht hst
    exact ePVariationOn_mono_set (Icc_subset_Icc_right hst)
  -- Left-continuity: ω is lower semicontinuous (sup of continuous functions)
  -- + monotone ⟹ left-continuous.
  -- For any c < ω(t₀), a partition achieving sum > c can be clamped to [a, t]
  -- for t < t₀ near t₀, with the sum remaining > c by continuity of f.
  -- Right-continuity: for t₀ ∈ [a, b) and ε > 0,
  --   ω(t₀) ≤ ω(t₀+ε)                           [monotone]
  --   ω(t₀+ε) ≤ ω(t₀) + Δ(ε) + ePVariationOn p f (Icc t₀ (t₀+ε))  [clamping]
  -- where Δ(ε) → 0 (uniform continuity of f on compact [a,b])
  -- and ePVariationOn p f (Icc t₀ (t₀+ε)) → 0 (key lemma above).
  sorry
-/
