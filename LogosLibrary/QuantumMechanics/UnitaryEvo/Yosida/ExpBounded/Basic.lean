/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.Convergence
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent
/-!
# Exponential of Bounded Operators

This file defines the exponential of a bounded linear operator via power series
and establishes its basic properties including the group law and norm bounds.

## Main definitions

* `expBounded`: The exponential `exp(tB) = Σₖ (tB)^k / k!`

## Main results

* `expBounded_group_law`: `exp((s+t)B) = exp(sB) ∘ exp(tB)`
* `expBounded_norm_bound`: `‖exp(tB)‖ ≤ exp(|t| * ‖B‖)`
* `expBounded_summable`: The defining series is summable
* `expBounded_at_zero`: `exp(0·B) = id`
* `expBounded_eq_exp`: Equivalence with `NormedSpace.exp`

-/

namespace QuantumMechanics.Yosida

open Complex Filter Topology Generators Resolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Definition -/

/-- The exponential of a bounded operator `B` at time `t`, defined via power series. -/
noncomputable def expBounded (B : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  ∑' (k : ℕ), (1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k

/-! ### Group law -/

theorem expBounded_group_law (B : H →L[ℂ] H) (s t : ℝ) :
    expBounded B (s + t) = (expBounded B s).comp (expBounded B t) := by
  unfold expBounded
  have h_eq_exp : ∀ c : ℂ, (∑' k : ℕ, (1 / k.factorial : ℂ) • (c • B) ^ k) =
      NormedSpace.exp ℂ (c • B) := by
    intro c
    rw [NormedSpace.exp_eq_tsum]
    congr 1
    ext k
    rw [one_div]
  have h_comm : Commute ((s : ℂ) • B) ((t : ℂ) • B) := by
    show ((s : ℂ) • B) * ((t : ℂ) • B) = ((t : ℂ) • B) * ((s : ℂ) • B)
    rw [smul_mul_smul, smul_mul_smul, mul_comm (s : ℂ) (t : ℂ)]
  simp only [h_eq_exp]
  simp only [ofReal_add, add_smul]
  rw [NormedSpace.exp_add_of_commute h_comm]
  rfl

/-! ### Summability -/

lemma expBounded_summable (B : H →L[ℂ] H) (t : ℝ) :
    Summable (fun k : ℕ => (1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k) := by
  apply Summable.of_norm
  have h_bound : ∀ k, ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖ ≤
      ‖(t : ℂ) • B‖ ^ k / k.factorial := by
    intro k
    rw [norm_smul]
    calc ‖(1 / k.factorial : ℂ)‖ * ‖((t : ℂ) • B) ^ k‖
        ≤ ‖(1 / k.factorial : ℂ)‖ * ‖(t : ℂ) • B‖ ^ k := by
            apply mul_le_mul_of_nonneg_left (opNorm_pow_le _ _)
            exact norm_nonneg _
      _ = (1 / k.factorial) * ‖(t : ℂ) • B‖ ^ k := by
            congr 1
            simp only [norm_div]
            simp_all only [one_mem, CStarRing.norm_of_mem_unitary, RCLike.norm_natCast, one_div]
      _ = ‖(t : ℂ) • B‖ ^ k / k.factorial := by ring
  apply Summable.of_nonneg_of_le
  · intro k; exact norm_nonneg _
  · exact h_bound
  · exact Real.summable_pow_div_factorial ‖(t : ℂ) • B‖

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma expBounded_norm_summable (B : H →L[ℂ] H) (t : ℝ) :
    Summable (fun k : ℕ => ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖) := by
  have h_bound : ∀ k, ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖ ≤
      ‖(t : ℂ) • B‖ ^ k / k.factorial := by
    intro k
    rw [norm_smul]
    calc ‖(1 / k.factorial : ℂ)‖ * ‖((t : ℂ) • B) ^ k‖
        ≤ ‖(1 / k.factorial : ℂ)‖ * ‖(t : ℂ) • B‖ ^ k := by
            apply mul_le_mul_of_nonneg_left (opNorm_pow_le _ _)
            exact norm_nonneg _
      _ = ‖(t : ℂ) • B‖ ^ k / k.factorial := by
            have h1 : ‖(1 / k.factorial : ℂ)‖ = 1 / k.factorial := by
              simp_all only [one_div, norm_inv, RCLike.norm_natCast]
            rw [h1]
            field_simp
  apply Summable.of_nonneg_of_le
  · intro k; exact norm_nonneg _
  · exact h_bound
  · exact Real.summable_pow_div_factorial ‖(t : ℂ) • B‖

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-! ### Norm bounds -/

theorem expBounded_norm_bound (B : H →L[ℂ] H) (t : ℝ) :
    ‖expBounded B t‖ ≤ Real.exp (|t| * ‖B‖) := by
  unfold expBounded
  set X := (t : ℂ) • B with hX
  set f := (fun n : ℕ => (n.factorial : ℂ)⁻¹ • X ^ n) with hf
  set g := (fun n : ℕ => ‖X‖ ^ n / n.factorial) with hg
  have h_norm_summable : Summable g := Real.summable_pow_div_factorial ‖X‖
  have h_term_le : ∀ n, ‖f n‖ ≤ g n := fun n => by
    simp only [hf, hg]
    rw [norm_smul, norm_inv, norm_natCast, div_eq_inv_mul]
    gcongr
    exact opNorm_pow_le X n
  have h_summable : Summable f :=
    Summable.of_norm_bounded (g := g) h_norm_summable h_term_le
  have h_eq_exp : (∑' k : ℕ, (1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k) =
      ∑' n, f n := by
    congr 1; ext k
    simp only [hf, one_div]
    abel
  have h_exp_eq : NormedSpace.exp ℂ X = ∑' n, f n := by
    rw [NormedSpace.exp_eq_tsum]
  have h_norm_f_summable : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) h_term_le h_norm_summable
  have h1 : ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := by
    apply norm_tsum_le_tsum_norm
    exact h_norm_f_summable
  have h2 : ∑' n, ‖f n‖ ≤ ∑' n, g n := by
    apply Summable.tsum_le_tsum h_term_le h_norm_f_summable h_norm_summable
  have h3 : ∑' n, g n = Real.exp ‖X‖ := by
    simp only [hg]
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have h4 : ‖X‖ = |t| * ‖B‖ := by
    simp only [hX]
    rw [norm_smul, norm_real, Real.norm_eq_abs]
  rw [h_eq_exp]
  calc ‖∑' n, f n‖
      ≤ ∑' n, ‖f n‖ := h1
    _ ≤ ∑' n, g n := h2
    _ = Real.exp ‖X‖ := h3
    _ = Real.exp (|t| * ‖B‖) := by rw [h4]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-! ### Special values -/

lemma expBounded_at_zero (B : H →L[ℂ] H) (ψ : H) :
    expBounded B 0 ψ = ψ := by
  unfold expBounded
  simp only [one_div, ofReal_zero, zero_smul]
  have h_zero_pow : ∀ k : ℕ, (0 : H →L[ℂ] H) ^ k = if k = 0 then 1 else 0 := by
    intro k
    cases k with
    | zero => simp [pow_zero]
    | succ k => simp [pow_succ, mul_zero]
  simp_rw [h_zero_pow]
  have h_sum : (∑' k : ℕ, (1 / k.factorial : ℂ) • (if k = 0 then (1 : H →L[ℂ] H) else 0)) = 1 := by
    rw [tsum_eq_single 0]
    · simp [Nat.factorial_zero]
    · intro k hk
      simp [hk]
  simp only [smul_ite, smul_zero]
  simp_all only [one_div, smul_ite, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    smul_zero, tsum_ite_eq, ContinuousLinearMap.one_apply]

lemma expBounded_at_zero' (B : H →L[ℂ] H) : expBounded B 0 = 1 := by
  unfold expBounded
  simp only [ofReal_zero, zero_smul, one_div]
  have h_single : ∀ k ≠ 0, (k.factorial : ℂ)⁻¹ • (0 : H →L[ℂ] H) ^ k = 0 := by
    intro k hk
    rw [zero_pow hk, smul_zero]
  rw [tsum_eq_single 0 h_single]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul]

lemma expBounded_zero_op (t : ℝ) : expBounded (0 : H →L[ℂ] H) t = 1 := by
  unfold expBounded
  simp only [smul_zero]
  conv_lhs =>
    arg 1
    ext k
    rw [zero_pow_eq]
  simp only [one_div, smul_ite, smul_zero]
  rw [tsum_eq_single 0]
  · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, ↓reduceIte]
    exact MulAction.one_smul 1
  · intro k hk
    simp only [hk, ↓reduceIte]

lemma expBounded_eq_exp (B : H →L[ℂ] H) (t : ℝ) :
    expBounded B t = NormedSpace.exp ℂ ((t : ℂ) • B) := by
  unfold expBounded
  rw [NormedSpace.exp_eq_tsum]
  congr 1
  ext k
  congr 1
  · field_simp

/-! ### Commutativity helpers -/

/-- Scalar multiples of B commute. -/
lemma smul_commute (B : H →L[ℂ] H) (s t : ℂ) : Commute (s • B) (t • B) := by
  unfold Commute SemiconjBy
  rw [smul_mul_smul, smul_mul_smul, mul_comm s t]

/-- B commutes with exp(τB). -/
lemma B_commute_expBounded (B : H →L[ℂ] H) (τ : ℝ) :
    Commute B (expBounded B τ) := by
  unfold expBounded
  have h_eq : (∑' k : ℕ, (1 / k.factorial : ℂ) • ((τ : ℂ) • B) ^ k) =
              NormedSpace.exp ℂ ((τ : ℂ) • B) := by
    rw [NormedSpace.exp_eq_tsum]
    congr 1; ext k; simp only [one_div]
  rw [h_eq]
  have h_comm : Commute B ((τ : ℂ) • B) := by
    unfold Commute SemiconjBy
    rw [mul_smul_comm, smul_mul_assoc]
  exact h_comm.exp_right ℂ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exponential group law for scalar multiples. -/
lemma expBounded_add_smul (B : H →L[ℂ] H) (s t : ℝ) :
    expBounded B (s + t) = (expBounded B s).comp (expBounded B t) := by
  unfold expBounded
  have h_eq : ∀ τ : ℝ, (∑' k : ℕ, (1 / k.factorial : ℂ) • ((τ : ℂ) • B) ^ k) =
              NormedSpace.exp ℂ ((τ : ℂ) • B) := by
    intro τ
    rw [NormedSpace.exp_eq_tsum]
    congr 1; ext k; simp only [one_div]
  simp_rw [h_eq]
  have h_comm : Commute ((s : ℂ) • B) ((t : ℂ) • B) := smul_commute B s t
  rw [show ((s + t : ℝ) : ℂ) • B = (s : ℂ) • B + (t : ℂ) • B by
      rw [ofReal_add, add_smul]]
  rw [NormedSpace.exp_add_of_commute h_comm]
  rfl

end QuantumMechanics.Yosida
