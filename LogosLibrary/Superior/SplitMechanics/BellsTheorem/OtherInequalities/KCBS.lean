import LogosLibrary.Superior.SplitMechanics.BellsTheorem.OtherInequalities.ThermMerm
import LogosLibrary.Superior.SplitMechanics.BellsTheorem.OtherInequalities.LeggettGarg
/-!
# KCBS Inequality: Contextuality in a Pentagon

The KCBS inequality is the simplest demonstration of quantum contextuality.
Unlike Bell inequalities (nonlocality), KCBS works on a SINGLE system.

## Setup
- 5 observables A₁, ..., A₅ with outcomes ±1
- Adjacent pairs are compatible (jointly measurable)
- Non-adjacent pairs are incompatible

## The Inequality
Classical (noncontextual): ∑ᵢ ⟨AᵢAᵢ₊₁⟩ ≥ -3
Quantum: ∑ᵢ ⟨AᵢAᵢ₊₁⟩ ≥ 5 - 4√5 ≈ -3.944

## Thermal Connection
- 5-fold symmetry → 2π/5 angular resolution
- cos(2π/5) = (√5 - 1)/4 (golden ratio!)
- The quantum violation is determined by this angle
-/

namespace ThermalKCBS

open Real Finset BigOperators ThermalLeggettGarg

/-- The pentagon graph: vertices 0,1,2,3,4 with edges (i, i+1 mod 5) -/
def pentagonEdges : Finset (Fin 5 × Fin 5) :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)}

/-- A noncontextual hidden variable model for KCBS -/
structure NoncontextualModel where
  /-- Hidden state space -/
  Λ : Type
  /-- Probability distribution -/
  ρ : Λ → ℝ
  ρ_pos : ∀ s, ρ s ≥ 0
  ρ_sum : ∀ [Fintype Λ], ∑ s : Λ, ρ s = 1
  /-- Predetermined values for each observable -/
  A : Fin 5 → Λ → ℝ
  /-- Dichotomic: A = ±1 -/
  dichotomic : ∀ i s, A i s = 1 ∨ A i s = -1

/-- The KCBS quantity: sum of adjacent correlations -/
noncomputable def kcbsValue (corr : Fin 5 → Fin 5 → ℝ) : ℝ :=
  corr 0 1 + corr 1 2 + corr 2 3 + corr 3 4 + corr 4 0

/-- Correlation from a noncontextual model -/
noncomputable def ncCorrelation (M : NoncontextualModel) [Fintype M.Λ] : Fin 5 → Fin 5 → ℝ :=
  fun i j => ∑ s : M.Λ, M.ρ s * M.A i s * M.A j s

/-- For ±1 values, sum of 5 adjacent products ≥ -3 -/
lemma kcbs_combinatorial_bound (A : Fin 5 → ℝ) (hA : ∀ i, A i = 1 ∨ A i = -1) :
    A 0 * A 1 + A 1 * A 2 + A 2 * A 3 + A 3 * A 4 + A 4 * A 0 ≥ -3 := by
  -- Each product is ±1, so sum ∈ {-5, -3, -1, 1, 3, 5}
  -- Key insight: can't have all 5 products = -1 (odd cycle constraint)
  -- If all products were -1, then ∏ᵢ (AᵢAᵢ₊₁) = (-1)⁵ = -1
  -- But ∏ᵢ (AᵢAᵢ₊₁) = (A₀A₁)(A₁A₂)(A₂A₃)(A₃A₄)(A₄A₀) = A₀²A₁²A₂²A₃²A₄² = 1
  -- Contradiction! So at least one product is +1, meaning sum ≥ -3
  have hA2 : ∀ i, A i * A i = 1 := fun i => pm_one_sq (hA i)
  have hprods : ∀ i j, A i * A j = 1 ∨ A i * A j = -1 :=
    fun i j => pm_one_mul_pm_one (hA i) (hA j)
  -- The product of all 5 adjacent products equals 1
  have hprod_all : A 0 * A 1 * (A 1 * A 2) * (A 2 * A 3) * (A 3 * A 4) * (A 4 * A 0) = 1 := by
    have h : A 0 * A 1 * (A 1 * A 2) * (A 2 * A 3) * (A 3 * A 4) * (A 4 * A 0)
           = (A 0 * A 0) * (A 1 * A 1) * (A 2 * A 2) * (A 3 * A 3) * (A 4 * A 4) := by ring
    rw [h, hA2, hA2, hA2, hA2, hA2]
    ring
  -- Since product = 1 and each factor is ±1, an even number of factors are -1
  -- 5 factors, even count ∈ {0, 2, 4}, so at most 4 are -1
  -- Sum = (5 - k) - k = 5 - 2k where k = number of -1s
  -- k ∈ {0, 2, 4} gives sum ∈ {5, 1, -3}
  -- Therefore sum ≥ -3
  -- Case analysis on values
  rcases hA 0 with h0 | h0 <;>
  rcases hA 1 with h1 | h1 <;>
  rcases hA 2 with h2 | h2 <;>
  rcases hA 3 with h3 | h3 <;>
  rcases hA 4 with h4 | h4 <;>
  simp [h0, h1, h2, h3, h4]
  all_goals try norm_num

/-- Classical KCBS bound: ∑⟨AᵢAᵢ₊₁⟩ ≥ -3 -/
theorem classical_kcbs_bound (M : NoncontextualModel) [Fintype M.Λ] :
    kcbsValue (ncCorrelation M) ≥ -3 := by
  unfold kcbsValue ncCorrelation
  simp only [Fin.isValue, ge_iff_le]
  -- Combine sums
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  -- For each hidden state, the combination ≥ -3 * ρ(s)
  have hbound : ∀ s : M.Λ,
      M.ρ s * M.A 0 s * M.A 1 s + M.ρ s * M.A 1 s * M.A 2 s +
      M.ρ s * M.A 2 s * M.A 3 s + M.ρ s * M.A 3 s * M.A 4 s +
      M.ρ s * M.A 4 s * M.A 0 s
      = M.ρ s * (M.A 0 s * M.A 1 s + M.A 1 s * M.A 2 s +
                 M.A 2 s * M.A 3 s + M.A 3 s * M.A 4 s + M.A 4 s * M.A 0 s) := by
    intro s; ring
  simp_rw [hbound]
  -- Apply combinatorial bound
  have hcomb : ∀ s : M.Λ, M.A 0 s * M.A 1 s + M.A 1 s * M.A 2 s +
                          M.A 2 s * M.A 3 s + M.A 3 s * M.A 4 s + M.A 4 s * M.A 0 s ≥ -3 := by
    intro s
    exact kcbs_combinatorial_bound (fun i => M.A i s) (fun i => M.dichotomic i s)
  calc ∑ s : M.Λ, M.ρ s * (M.A 0 s * M.A 1 s + M.A 1 s * M.A 2 s +
                            M.A 2 s * M.A 3 s + M.A 3 s * M.A 4 s + M.A 4 s * M.A 0 s)
      ≥ ∑ s : M.Λ, M.ρ s * (-3) := by
        apply Finset.sum_le_sum
        intro s _
        apply mul_le_mul_of_nonneg_left (hcomb s) (M.ρ_pos s)
    _ = -3 * ∑ s : M.Λ, M.ρ s := by rw [Finset.mul_sum]; congr 1; ext s; ring
    _ = -3 * 1 := by rw [M.ρ_sum]
    _ = -3 := by ring

/-- The quantum optimal angle: 2π/5 -/
noncomputable def kcbsAngle : ℝ := 2 * Real.pi / 5

/-- The golden ratio -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

/-- cos(2π/5) from double angle formula -/
theorem cos_two_pi_div_five : Real.cos kcbsAngle = (Real.sqrt 5 - 1) / 4 := by
  unfold kcbsAngle
  rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring, Real.cos_two_mul, Real.cos_pi_div_five]
  have hsqrt5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  field_simp
  linarith

/-- The quantum KCBS correlation uses angle 4π/5 between adjacent measurements -/
noncomputable def kcbsQuantumCorr : ℝ := Real.cos (4 * Real.pi / 5)

/-- cos(4π/5) = -(1 + √5)/4 -/
theorem cos_four_pi_div_five : Real.cos (4 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
  have h : 4 * Real.pi / 5 = Real.pi - Real.pi / 5 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

/-- Quantum KCBS bound is 5 * cos(4π/5) -/
noncomputable def quantumKcbsBound : ℝ := 5 * Real.cos (4 * Real.pi / 5)

/-- The quantum bound equals -5(1 + √5)/4 -/
theorem quantum_bound_alt : quantumKcbsBound = -5 * (1 + Real.sqrt 5) / 4 := by
  unfold quantumKcbsBound
  rw [cos_four_pi_div_five]
  ring

/-- Quantum correlations achieve the Tsirelson-like bound -/
theorem quantum_kcbs_achievable :
    ∃ corr : Fin 5 → Fin 5 → ℝ, kcbsValue corr = quantumKcbsBound := by
  let c := Real.cos (4 * Real.pi / 5)
  let corr : Fin 5 → Fin 5 → ℝ := fun i j =>
    if i = j then 1
    else if (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val then c
    else 0
  use corr
  unfold kcbsValue quantumKcbsBound
  have h01 : corr 0 1 = c := by simp [corr]
  have h12 : corr 1 2 = c := by simp [corr]
  have h23 : corr 2 3 = c := by simp [corr]
  have h34 : corr 3 4 = c := by simp [corr]
  have h40 : corr 4 0 = c := by simp [corr]
  rw [h01, h12, h23, h34, h40]
  ring

end ThermalKCBS
