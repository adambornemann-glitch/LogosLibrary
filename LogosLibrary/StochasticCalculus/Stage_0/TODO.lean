/-
/-! ### Convenience API -/


section API₃

variable [CompleteSpace E]

/-- **The Sewing Lemma (general form)**: given a continuous super-additive control `ω`,
an exponent `θ > 1`, and a two-parameter map `Ξ` whose defect is bounded by
`K · ω(s,t)^θ`, there exists a unique additive functional `I` satisfying:

1. `I(s, s) = 0`
2. `I(s, t) = I(s, u) + I(u, t)` for `s ≤ u ≤ t`
3. `‖I(s, t) - Ξ(s, t)‖ ≤ K · ∑ₙ Φ_θ(Dₙ(s,t))`

For Lipschitz controls (Layers 1–2), the tsum bound reduces to
`K · C · |t-s|^θ` for an explicit geometric constant `C = (1 - 2^{-(θ-1)})⁻¹`.
For general continuous controls, the tsum is finite by `energy_summable`
and vanishes as `t - s → 0` by `energy_vanish`. -/
theorem sewing_lemma₃ {Ξ : ℝ → ℝ → E}
    {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b) :
    ∃ I : ℝ → ℝ → E,
      (∀ s, a ≤ s → s ≤ b → I s s = 0) ∧
      (∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → I s t = I s u + I u t) ∧
      (∀ s t, a ≤ s → (hst : s ≤ t) → t ≤ b →
        ‖I s t - Ξ s t‖ ≤ K * ∑' n, thetaEnergy ω θ (dyadicPartition s t hst n)) := by
  exact ⟨sewingMap₃ Ξ ω θ K a b hΞ,
    fun s has hsb => sewingMap₃_diag hΞ has hsb,
    fun s u t has hsu hut htb => sewingMap₃_additive hΞ has hsu hut htb,
    fun s t has hst htb => sewingMap₃_dist_le hΞ has hst htb⟩


end API₃
-/
