import LogosLibrary.QuantumMechanics.BellsTheorem.QuantumCHSH.Q_CHSH_Basic

open Matrix Complex MatrixGroups
namespace QuantumCHSH

/-! ## Alice's and Bob's Observables -/

/-- Alice's first observable: A₀ = σ_z ⊗ I -/
def A₀ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  kroneckerMap (· * ·) σ_z I₂

/-- Alice's second observable: A₁ = σₓ ⊗ I -/
def A₁ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  kroneckerMap (· * ·) σₓ I₂

/-- Bob's first observable: B₀ = I ⊗ (σ_z - σₓ)/√2 -/
noncomputable def B₀ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  kroneckerMap (· * ·) I₂ ((1/Real.sqrt 2 : ℂ) • (σ_z - σₓ))

/-- Bob's second observable: B₁ = I ⊗ -(σ_z + σₓ)/√2 -/
noncomputable def B₁ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  kroneckerMap (· * ·) I₂ ((-1/Real.sqrt 2 : ℂ) • (σ_z + σₓ))

/-! ## Expectation Values -/

/-- Expectation value ⟨O⟩ = Tr(O · ρ) -/
noncomputable def expectation (O ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℂ :=
  (O * ρ).trace

/-- The correlation E(A, B) for observables A, B on state ρ -/
noncomputable def correlation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B ρ : Matrix ι ι ℂ) : ℂ :=
  (A * B * ρ).trace

/-! ## Computing the Correlations -/

-- These are the four correlations needed for CHSH

/-- E(A₀, B₀) = -1/√2 for the Bell state -/
lemma E_A₀_B₀ : correlation A₀ B₀ ρ_Ψ_minus = -1 / Real.sqrt 2 := by
  unfold correlation A₀ B₀ ρ_Ψ_minus
  simp only [one_div]
  simp only [σ_z, σₓ, I₂]
  -- Expand the trace over (Fin 2 × Fin 2)
  rw [Matrix.trace]
  rw [← @mul_kronecker_mul]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  -- Expand matrix multiplication
  simp only [mul_one, of_sub_of, sub_cons, head_cons, sub_zero, tail_cons, zero_sub, sub_self,
    zero_empty, smul_of, smul_cons, smul_eq_mul, mul_neg, smul_empty, one_mul, Fin.isValue,
    diag_apply]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.of_apply]
  -- Normalize the expression
  simp only [mul_zero, add_zero, zero_add, mul_neg]
  -- Simplify with √2 arithmetic
  have sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp [Real.sqrt_ne_zero'.mpr (by norm_num : (2:ℝ) > 0)]
  field_simp
  rw [← @adjugate_fin_two_of]
  simp only [one_div, adjugate_fin_two_of, Fin.isValue, kroneckerMap_apply, of_apply, cons_val',
    cons_val_zero, cons_val_fin_one, cons_val_one, mul_neg, one_mul, zero_mul, neg_zero, add_zero,
    neg_mul, zero_add]
  ring_nf
  simp only [ne_eq, ofReal_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero,
    not_false_eq_true, mul_inv_cancel₀, one_mul]

/-- E(A₀, B₁) = 1/√2 for the Bell state -/
lemma E_A₀_B₁ : correlation A₀ B₁ ρ_Ψ_minus = 1 / Real.sqrt 2 := by
  unfold correlation A₀ B₁ ρ_Ψ_minus
  simp only [one_div]
  simp only [σ_z, σₓ, I₂]
  rw [Matrix.trace]
  rw [← @mul_kronecker_mul]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  simp only [mul_one, of_add_of, add_cons, head_cons, add_zero, tail_cons, zero_add,
    empty_add_empty, smul_of, smul_cons, smul_eq_mul, smul_empty, mul_neg, one_mul, Fin.isValue,
    diag_apply]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.of_apply]
  simp only [mul_zero, add_zero, zero_add, mul_neg]
  have sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp [Real.sqrt_ne_zero'.mpr (by norm_num : (2:ℝ) > 0)]
  field_simp
  rw [← @adjugate_fin_two_of]
  simp only [one_div, adjugate_fin_two_of, Fin.isValue, kroneckerMap_apply, of_apply, cons_val',
    cons_val_zero, cons_val_fin_one, cons_val_one, mul_neg, one_mul, zero_mul, neg_zero, add_zero,
    neg_mul, zero_add, neg_neg]
  ring_nf
  simp only [ne_eq, ofReal_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero,
    not_false_eq_true, mul_inv_cancel₀, one_mul]

/-- E(A₁, B₀) = 1/√2 for the Bell state -/
lemma E_A₁_B₀ : correlation A₁ B₀ ρ_Ψ_minus = 1 / Real.sqrt 2 := by
  unfold correlation A₁ B₀ ρ_Ψ_minus
  simp only [one_div]
  simp only [σ_z, σₓ, I₂]
  rw [Matrix.trace]
  rw [← @mul_kronecker_mul]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  simp only [mul_one, of_sub_of, sub_cons, head_cons, sub_zero, tail_cons, zero_sub, sub_self,
    zero_empty, smul_of, smul_cons, smul_eq_mul, mul_neg, smul_empty, one_mul, Fin.isValue,
    diag_apply]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.of_apply]
  simp only [mul_zero, add_zero, zero_add, mul_neg]
  have sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp [Real.sqrt_ne_zero'.mpr (by norm_num : (2:ℝ) > 0)]
  field_simp
  rw [← @adjugate_fin_two_of]
  simp only [one_div, adjugate_fin_two_of, Fin.isValue, kroneckerMap_apply, of_apply, cons_val',
    cons_val_zero, cons_val_fin_one, cons_val_one, mul_neg, one_mul, zero_mul, neg_zero, add_zero,
    zero_add]
  ring_nf
  simp only [ne_eq, ofReal_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero,
    not_false_eq_true, mul_inv_cancel₀, one_mul]

/-- E(A₁, B₁) = 1/√2 for the Bell state -/
lemma E_A₁_B₁ : correlation A₁ B₁ ρ_Ψ_minus = 1 / Real.sqrt 2 := by
  unfold correlation A₁ B₁ ρ_Ψ_minus
  simp only [one_div]
  simp only [σ_z, σₓ, I₂]
  rw [Matrix.trace]
  rw [← @mul_kronecker_mul]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  simp only [mul_one, of_add_of, add_cons, head_cons, add_zero, tail_cons, zero_add,
    empty_add_empty, smul_of, smul_cons, smul_eq_mul, smul_empty, mul_neg, one_mul, Fin.isValue,
    diag_apply]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.of_apply]
  simp only [mul_zero, add_zero, zero_add, mul_neg]
  have sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp [Real.sqrt_ne_zero'.mpr (by norm_num : (2:ℝ) > 0)]
  field_simp
  rw [← @adjugate_fin_two_of]
  simp only [one_div, adjugate_fin_two_of, Fin.isValue, kroneckerMap_apply, of_apply, cons_val',
    cons_val_zero, cons_val_fin_one, cons_val_one, mul_neg, one_mul, zero_mul, neg_zero, add_zero,
    zero_add, neg_neg]
  ring_nf
  simp only [ne_eq, ofReal_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero,
    not_false_eq_true, mul_inv_cancel₀, one_mul]


end QuantumCHSH
