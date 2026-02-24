import LogosLibrary.QuantumMechanics.BellsTheorem.OtherInequalities.CGLMP
/-!
# CGLMP Inequality: Bell Tests for Qudits

The CGLMP inequality generalizes CHSH to d-dimensional systems (qudits).
Instead of ±1 outcomes, we have d outcomes: 0, 1, ..., d-1.

## Key Features
- Two parties, two settings each (like CHSH)
- d outcomes per measurement (not just 2)
- Classical bound: 2 for all d
- Quantum bound: increases with d, approaches 4 as d → ∞

## The Inequality (d = 3 case for concreteness)
For outcomes a, b ∈ {0, 1, 2} and settings x, y ∈ {0, 1}:

I₃ = P(a = b | 00) + P(b = a+1 | 01) + P(a = b | 10) + P(a = b+1 | 11)
   - P(a = b+1 | 00) - P(b = a | 01) - P(a = b+1 | 10) - P(a = b | 11)

Classical: I₃ ≤ 2
Quantum: I₃ ≤ (something involving d)

## Thermal Connection
- d outcomes = d-fold phase space
- Angular resolution = 2π/d
- As d → ∞, approaches continuous phase space
-/

namespace ThermalCGLMP

open ThermalMermin Real Finset BigOperators
/-- Specific case: d=4 to d=5 -/
theorem violation_ratio_4_to_5 : quantumCglmpBound 4 ≤ quantumCglmpBound 5 := by
  unfold quantumCglmpBound
  simp only [Nat.reduceDiv]
  -- d=4: Fin 2, sum = cos(π/8) + cos(3π/8), denom = cos(π/8)
  -- d=5: Fin 2, sum = cos(π/10) + cos(3π/10), denom = cos(π/10)
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, CharP.cast_eq_zero, mul_zero,
    zero_add, one_mul, Nat.cast_ofNat, Nat.mod_succ, Nat.cast_one, mul_one]
  ring_nf
  -- Need: 2 * (cos(π/8) + cos(3π/8)) * cos(π/10) ≤ 2 * (cos(π/10) + cos(3π/10)) * cos(π/8)
  sorry

/-- Specific case: d=5 to d=6 -/
theorem violation_ratio_5_to_6 : quantumCglmpBound 5 ≤ quantumCglmpBound 6 := by
  unfold quantumCglmpBound
  simp only [Nat.reduceDiv]
  rw [Fin.sum_univ_two, Fin.sum_univ_three]
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, CharP.cast_eq_zero, mul_zero,
    zero_add, one_mul, Nat.cast_ofNat, Nat.mod_succ, Nat.cast_one, mul_one, Nat.one_mod]
  ring_nf
  sorry

/-- The quantum/classical violation ratio increases with d (specific cases) -/
theorem violation_ratio_increases_cases :
    quantumCglmpBound 2 ≤ quantumCglmpBound 3 ∧
    quantumCglmpBound 3 ≤ quantumCglmpBound 4 ∧
    quantumCglmpBound 4 ≤ quantumCglmpBound 5 ∧
    quantumCglmpBound 5 ≤ quantumCglmpBound 6 := by
  exact ⟨violation_ratio_2_to_3, violation_ratio_3_to_4, violation_ratio_4_to_5, violation_ratio_5_to_6⟩

/-- The quantum/classical violation ratio increases with d (general, admitted) -/
theorem violation_ratio_increases (d₁ d₂ : ℕ) (hd₁ : d₁ ≥ 2) (hd₂ : d₂ > d₁) :
    quantumCglmpBound d₁ / 2 ≤ quantumCglmpBound d₂ / 2 := by
  -- The general proof requires showing that the ratio
  -- (∑ₖ cos((2k+1)π/(2d))) / cos(π/(2d))
  -- is monotonically increasing in d.
  --
  -- This follows from:
  -- 1. As d increases, each angle decreases, so each cosine in numerator increases
  -- 2. The number of terms in the sum increases (or stays same)
  -- 3. The denominator cos(π/(2d)) also increases, but slower than the numerator
  --
  -- A complete proof would use the closed form for the sum of cosines:
  -- ∑ₖ₌₀^{n-1} cos(a + kd) = sin(nd/2) * cos(a + (n-1)d/2) / sin(d/2)
  sorry

/-- The sum of cosines in the numerator grows with d -/
theorem numerator_grows (d₁ d₂ : ℕ) (hd₁ : d₁ ≥ 2) (hd₂ : d₂ > d₁) :
    ∑ k : Fin (d₁ / 2), Real.cos ((2 * k.val + 1) * Real.pi / (2 * d₁)) ≤
    ∑ k : Fin (d₂ / 2), Real.cos ((2 * k.val + 1) * Real.pi / (2 * d₂)) := by
  -- More terms AND each term potentially larger due to smaller angles
  sorry

/-- As d → ∞, the quantum bound approaches 4 -/
theorem quantum_bound_limit :
    Filter.Tendsto (fun d => quantumCglmpBound (d + 2)) Filter.atTop (nhds 4) := by

  unfold quantumCglmpBound
  simp only [Nat.cast_add, Nat.cast_ofNat]
  sorry
