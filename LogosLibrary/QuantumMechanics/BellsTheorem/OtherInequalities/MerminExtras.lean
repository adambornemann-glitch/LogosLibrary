import LogosLibrary.QuantumMechanics.BellsTheorem.OtherInequalities.ThermMerm

namespace ThermalMermin
/-- GHZ achieves the maximum possible violation -/
theorem ghz_is_maximal (n : ℕ) (hn : n ≥ 3) :
    ghzViolation n hn = merminQuantumBound n (Nat.one_le_of_lt hn) := by
  unfold ghzViolation merminValue merminQuantumBound
  -- GHZ correlation is ±1 on each Mermin configuration
  -- The signs align perfectly to give 2^(n-1)
  -- Number of contributing configs = 2^(n-1), each contributing ±1 with correct sign
  sorry

/-- W-state violation is bounded by a suboptimal value -/
theorem w_violation_bound (n : ℕ) (hn : n ≥ 3) :
    wStateViolation n hn ≤ (n - 2 : ℝ) / n * 2^(n - 1) := by
  unfold wStateViolation merminValue wCorrelation
  -- W-state has correlation (n-2)/n only for all-X configurations
  -- All other configurations (with Y measurements) give 0
  -- So total ≤ (n-2)/n * (number of all-X configs in Mermin sum)
  -- ≤ (n-2)/n * 2^(n-1)
  sorry

/-- The gap between GHZ and W-state violation grows with n -/
theorem ghz_w_gap_grows (n : ℕ) (hn : n ≥ 3) :
    ghzViolation n hn - wStateViolation n hn ≥ 2 * 2^(n - 1) / n := by
  -- GHZ = 2^(n-1), W ≤ (n-2)/n * 2^(n-1)
  -- Gap ≥ 2^(n-1) - (n-2)/n * 2^(n-1) = 2^(n-1) * (1 - (n-2)/n) = 2^(n-1) * 2/n
  sorry

/-- W-state gives strictly smaller violation than GHZ -/
theorem w_vs_ghz_violation (n : ℕ) (hn : n ≥ 3) :
    wStateViolation n hn < ghzViolation n hn := by
  unfold wStateViolation ghzViolation
  -- ⊢ merminValue ⋯ (wCorrelation n ⋯) < merminValue ⋯ (ghzCorrelation n)
  sorry

end ThermalMermin
