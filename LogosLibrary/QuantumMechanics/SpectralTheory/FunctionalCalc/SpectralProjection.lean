/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute
import LogosLibrary.QuantumMechanics.SpectralTheory.ResolventRoute
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform
/-!
# Spectral Projection Properties

This file establishes the fundamental properties of spectral projections `E(B)` for
Borel sets `B ⊆ ℝ`. These projections are orthogonal (self-adjoint and idempotent),
commute with each other, and satisfy the multiplicative property `E(B)E(C) = E(B ∩ C)`.

## Main results

* `spectral_projection_orthogonal`: `E(B)² = E(B)` (idempotent)
* `spectral_projection_adjoint`: `E(B)* = E(B)` (self-adjoint)
* `spectral_projection_mul`: `E(B)E(C) = E(B ∩ C)`
* `spectral_projection_comm`: `E(B)E(C) = E(C)E(B)`
* `spectral_projection_disjoint`: `E(B)E(C) = 0` when `B ∩ C = ∅`
* `spectral_projection_norm_le`: `‖E(B)ψ‖ ≤ ‖ψ‖` (contractive)
* `spectral_projection_opNorm_le_one`: `‖E(B)‖ ≤ 1`
* `spectral_projection_compl`: `E(Bᶜ) = I - E(B)`

## Tags

spectral measure, orthogonal projection, spectral projection
-/

namespace FunctionalCalculus

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory InnerProductSpace Complex QuantumMechanics.Cayley SpectralBridge.Resolvent SpectralBridge.Bochner QuantumMechanics.Generators ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## Basic Projection Properties
-/

/-- Spectral projections are idempotent: `E(B) * E(B) = E(B)`. This follows
    immediately from `E(B) * E(C) = E(B ∩ C)` with `C = B`. -/
lemma spectral_projection_orthogonal (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) : E B * E B = E B := by
  have := hE.mul B B hB hB
  simp [Set.inter_self] at this
  exact this

/-- Disjoint sets give orthogonal projections -/
lemma spectral_disjoint_mul_zero (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : Disjoint B C) : E B * E C = 0 := by
  have h := hE.mul B C hB hC
  rwa [Set.disjoint_iff_inter_eq_empty.mp hBC, hE.empty] at h

/-- Complementary sets give complementary projections -/
lemma spectral_compl (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) : E B + E Bᶜ = 1 := by
  have h_disj : Disjoint B Bᶜ := by exact Set.disjoint_compl_right_iff_subset.mpr fun ⦃a⦄ a => a
  have h_union : B ∪ Bᶜ = Set.univ := Set.union_compl_self B
  calc E B + E Bᶜ = E (B ∪ Bᶜ) := (hE.add B Bᶜ hB hB.compl h_disj).symm
    _ = E Set.univ := by rw [h_union]
    _ = 1 := hE.univ

/-- E(B) is an orthogonal projection -/
lemma spectral_projection (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) : E B * E B = E B := by
  have := hE.mul B B hB hB
  simp only [Set.inter_self] at this
  exact this

/-- Disjoint Borel sets give orthogonal spectral projections: if `B ∩ C = ∅`,
    then `E(B) * E(C) = 0`. -/
lemma spectral_disjoint_orthogonal (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : Disjoint B C) :
    E B * E C = 0 := by
  have := hE.mul B C hB hC
  simp [Set.disjoint_iff_inter_eq_empty.mp hBC] at this
  rw [this]
  exact hE.empty

/-- Spectral projections multiply: E(B)E(C) = E(B ∩ C) -/
lemma spectral_projection_mul (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    E B * E C = E (B ∩ C) := hE.mul B C hB hC

/-- E(B) is idempotent: E(B)² = E(B) -/
lemma spectral_projection_idempotent (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) :
    E B * E B = E B := by
  rw [spectral_projection_mul E hE B B hB hB, Set.inter_self]

/-- E(B) applied twice equals E(B) applied once -/
lemma spectral_projection_apply_twice (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    E B (E B ψ) = E B ψ := by
  have h := spectral_projection_idempotent E hE B hB
  exact congrFun (congrArg DFunLike.coe h) ψ

/-- Key identity: ⟪E(B)x, y⟫ = ⟪E(B)x, E(B)y⟫
    Uses: E self-adjoint and E² = E -/
lemma spectral_projection_inner_factorization (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    ⟪E B x, y⟫_ℂ = ⟪E B x, E B y⟫_ℂ := by
  calc ⟪E B x, y⟫_ℂ
      = ⟪E B (E B x), y⟫_ℂ := by rw [spectral_projection_apply_twice E hE B hB x]
    _ = ⟪E B x, E B y⟫_ℂ := by exact hE.sa B ((E B) x) y

/-- Variant: ⟪E(B)x, E(B)y⟫ = ⟪x, E(B)y⟫ -/
lemma spectral_projection_inner_factorization' (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    ⟪E B x, E B y⟫_ℂ = ⟪x, E B y⟫_ℂ := by
  rw [← spectral_projection_inner_factorization E hE B hB x y]
  exact hE.sa B x y

/-- ‖E(B)ψ‖² = ⟪E(B)ψ, ψ⟫.re -/
lemma spectral_projection_norm_sq (E : Set ℝ → H →L[ℂ] H) (B : Set ℝ) (hE : IsSpectralMeasure E)
    (hB : MeasurableSet B) (ψ : H) : ‖E B ψ‖^2 = (⟪E B ψ, ψ⟫_ℂ).re := by
  have h1 : ‖E B ψ‖^2 = (⟪E B ψ, E B ψ⟫_ℂ).re := by
    conv_rhs => rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    simp only [coe_algebraMap]
    rw [← ofReal_pow]
    exact rfl
  rw [h1, ← spectral_projection_inner_factorization E hE B hB ψ ψ]

/-!
## Empty, Disjoint, Union Properties
-/

/-- E(∅) = 0 -/
lemma spectral_projection_empty (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) :
    E ∅ = 0 := hE.empty

/-- Disjoint sets give orthogonal projections: E(B) * E(C) = 0 when B ∩ C = ∅ -/
lemma spectral_projection_disjoint (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : Disjoint B C) :
    E B * E C = 0 := by
  rw [spectral_projection_mul E hE B C hB hC]
  rw [Set.disjoint_iff_inter_eq_empty.mp hBC]
  exact spectral_projection_empty E hE

/-- E(B ∪ C) = E(B) + E(C) for disjoint B, C -/
lemma spectral_projection_union_disjoint (E : Set ℝ → H →L[ℂ] H)
    (hE_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
              E (B ∪ C) = E B + E C)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : Disjoint B C) :
    E (B ∪ C) = E B + E C := hE_add B C hB hC hBC

/-- E(B) and E(C) commute -/
lemma spectral_projection_comm (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    E B * E C = E C * E B := by
  rw [spectral_projection_mul E hE B C hB hC, spectral_projection_mul E hE C B hC hB, Set.inter_comm]

/-!
## Self-Adjoint and Norm Properties
-/

/-- E(B) is self-adjoint as an operator -/
lemma spectral_projection_adjoint (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (E B).adjoint = E B := by
  ext ψ
  apply ext_inner_left ℂ
  intro φ
  rw [@ContinuousLinearMap.adjoint_inner_right]
  exact hE.sa B φ ψ

/-- ‖E(B)ψ‖ ≤ ‖ψ‖ (projections are contractions) -/
lemma spectral_projection_norm_le (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    ‖E B ψ‖ ≤ ‖ψ‖ := by
  have h := spectral_projection_norm_sq E B hE hB ψ
  -- ‖E(B)ψ‖² = ⟪E(B)ψ, ψ⟫.re ≤ ‖E(B)ψ‖ * ‖ψ‖ by Cauchy-Schwarz
  by_cases hEψ : E B ψ = 0
  · simp [hEψ]
  · have h_cs : |(⟪E B ψ, ψ⟫_ℂ).re| ≤ ‖E B ψ‖ * ‖ψ‖ := by
      calc |(⟪E B ψ, ψ⟫_ℂ).re|
          ≤ ‖⟪E B ψ, ψ⟫_ℂ‖ := Complex.abs_re_le_norm _
        _ ≤ ‖E B ψ‖ * ‖ψ‖ := norm_inner_le_norm _ _
    have h_nonneg : (⟪E B ψ, ψ⟫_ℂ).re ≥ 0 := by
      rw [← h]
      exact sq_nonneg _
    rw [abs_of_nonneg h_nonneg] at h_cs
    have h_pos : ‖E B ψ‖ > 0 := norm_pos_iff.mpr hEψ
    calc ‖E B ψ‖ = ‖E B ψ‖^2 / ‖E B ψ‖ := by field_simp
      _ = (⟪E B ψ, ψ⟫_ℂ).re / ‖E B ψ‖ := by rw [h]
      _ ≤ (‖E B ψ‖ * ‖ψ‖) / ‖E B ψ‖ := by exact
        (div_le_div_iff_of_pos_right h_pos).mpr h_cs
      _ = ‖ψ‖ := by field_simp

/-- ‖E(B)‖ ≤ 1 (operator norm bound) -/
lemma spectral_projection_opNorm_le_one (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ‖E B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  simp only [one_mul]
  exact spectral_projection_norm_le E hE B hB ψ

/-!
## Range and Kernel Characterizations
-/

/-- Range of E(B) is the set of fixed points -/
lemma spectral_projection_range_eq_fixed (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    ψ ∈ LinearMap.range (E B) ↔ E B ψ = ψ := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact spectral_projection_apply_twice E hE B hB φ
  · intro h
    exact ⟨ψ, h⟩

/-- E(Bᶜ) = I - E(B) when E(ℝ) = I -/
lemma spectral_projection_compl (E : Set ℝ → H →L[ℂ] H)
    (hE_univ : E Set.univ = 1)
    (hE_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
              E (B ∪ C) = E B + E C)
    (B : Set ℝ) (hB : MeasurableSet B) :
    E Bᶜ = 1 - E B := by
  have h : B ∪ Bᶜ = Set.univ := Set.union_compl_self B
  have hBc : MeasurableSet Bᶜ := hB.compl
  have hdisj : Disjoint B Bᶜ := by exact Set.disjoint_compl_right_iff_subset.mpr fun ⦃a⦄ a => a
  calc E Bᶜ = E (B ∪ Bᶜ) - E B := by rw [hE_add B Bᶜ hB hBc hdisj]; exact Eq.symm (add_sub_cancel_left (E B) (E Bᶜ))
    _ = E Set.univ - E B := by rw [h]
    _ = 1 - E B := by rw [hE_univ]

/-!
## Additional Lemmas for Other Files
-/

/-- Spectral measure is idempotent: E(B)² = E(B) -/
lemma spectral_measure_sq (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) : E B * E B = E B := by
  rw [hE.mul B B hB hB, Set.inter_self]

/-- Inner product with spectral measure is nonneg -/
theorem spectral_measure_inner_nonneg (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) : 0 ≤ (⟪(E B) ψ, ψ⟫_ℂ).re := by
  have h1 : ⟪(E B) ψ, ψ⟫_ℂ = ⟪(E B) ψ, (E B) ψ⟫_ℂ := by
    conv_rhs => rw [← spectral_measure_sq E hE B hB]
    simp only [ContinuousLinearMap.mul_apply]
    rw [spectral_projection_range E hE B hB ψ]
    exact spectral_projection_inner_factorization E hE B hB ψ ψ
  rw [h1]
  exact @inner_self_nonneg ℂ H _ _ _ ((E B) ψ)

/-- Spectral measure is a contraction: ‖E(B)ψ‖ ≤ ‖ψ‖ -/
lemma spectral_measure_norm_le (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) : ‖(E B) ψ‖ ≤ ‖ψ‖ := by
  -- ‖E(B)ψ‖² = ⟪E(B)ψ, E(B)ψ⟫ = ⟪E(B)ψ, ψ⟫ ≤ ‖E(B)ψ‖‖ψ‖
  by_cases hEψ : ‖(E B) ψ‖ = 0
  · simp [hEψ]
  have h1 : ‖(E B) ψ‖^2 = (⟪(E B) ψ, (E B) ψ⟫_ℂ).re := by
    rw [spectral_projection_norm_sq E B hE hB ψ]
    rw [spectral_projection_inner_factorization E hE B hB ψ ψ]
  have h2 : ⟪(E B) ψ, (E B) ψ⟫_ℂ = ⟪(E B) ψ, ψ⟫_ℂ := by
    conv_lhs => rw [← spectral_measure_sq E hE B hB]
    simp only [ContinuousLinearMap.mul_apply]
    rw [spectral_projection_range E hE B hB ψ]
    rw [← spectral_projection_inner_factorization E hE B hB ψ ψ]
  have h3 : (⟪(E B) ψ, ψ⟫_ℂ).re ≤ ‖(E B) ψ‖ * ‖ψ‖ := by
    calc (⟪(E B) ψ, ψ⟫_ℂ).re ≤ |(⟪(E B) ψ, ψ⟫_ℂ).re| := le_abs_self _
         _ ≤ ‖⟪(E B) ψ, ψ⟫_ℂ‖ := abs_re_le_norm ⟪(E B) ψ, ψ⟫_ℂ
         _ ≤ ‖(E B) ψ‖ * ‖ψ‖ := norm_inner_le_norm _ _
  exact spectral_projection_norm_le E hE B hB ψ

end FunctionalCalculus
