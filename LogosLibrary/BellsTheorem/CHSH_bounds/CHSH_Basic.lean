/-
Copyright (c) 2025 Bell Theorem Formalization Project
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla
Ported by: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.BellsTheorem.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.LinearAlgebra.Matrix.Hermitian
-- Imports that might be needed
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Basic

open scoped Matrix ComplexConjugate BigOperators TensorProduct Order
open MeasureTheory ProbabilityTheory Matrix Complex

/-! ## Quantum State Foundations -/


namespace QuantumInfo

/-! ## Helper Lemmas for Separable Bound -/

/-- The expectation of a Hermitian observable in a state with Hermitian density matrix is real -/
lemma hermitian_expectation_real {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian)
    (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian) :
    ((A * ρ).trace).im = 0 := by
  have h : conj (A * ρ).trace = (A * ρ).trace := by
    have eq1 : conj (A * ρ).trace = (A * ρ)ᴴ.trace := by
      simp only [Matrix.trace, Matrix.diag_apply, map_sum, Matrix.conjTranspose_apply]
      rfl
    rw [eq1, Matrix.conjTranspose_mul, hA.eq, hρ.eq, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_im.mp h


-- 1. Self dot product is norm squared (as a real cast to ℂ)
lemma star_dotProduct_self_eq_sum_normSq (x : Fin n → ℂ) :
    star x ⬝ᵥ x = ↑(∑ i, ‖x i‖^2) := by
  simp only [dotProduct, Pi.star_apply]
  simp only [RCLike.star_def, ofReal_sum, ofReal_pow]
  apply Finset.sum_congr rfl
  intro i _
  exact conj_mul' (x i)

-- 2. Self dot product is non-negative real
lemma star_dotProduct_self_re_nonneg (x : Fin n → ℂ) :
    0 ≤ (star x ⬝ᵥ x).re := by
  rw [star_dotProduct_self_eq_sum_normSq]
  simp only [ofReal_re]
  apply Finset.sum_nonneg
  intro i _
  exact sq_nonneg ‖x i‖

-- 3. For Hermitian A: ⟨Ax, Ax⟩ = ⟨x, A²x⟩
lemma star_mulVec_dotProduct_mulVec_hermitian (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (x : Fin n → ℂ) :
    star (A.mulVec x) ⬝ᵥ (A.mulVec x) = star x ⬝ᵥ (A * A).mulVec x := by
  rw [Matrix.star_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_vecMul]
  rw [hA.eq]
  exact Eq.symm (dotProduct_mulVec (star x) (A * A) x)

lemma norm_star_dotProduct_self (x : Fin n → ℂ) :
    ‖star x ⬝ᵥ x‖ = ∑ i, ‖x i‖^2 := by
  rw [star_dotProduct_self_eq_sum_normSq, Complex.norm_real, Real.norm_of_nonneg]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

lemma sum_normSq_mulVec_eq_of_hermitian_sq_one (A : Matrix (Fin n) (Fin n) ℂ)
    (hA_herm : A.IsHermitian) (hA_sq : A * A = 1) (x : Fin n → ℂ) :
    ∑ i, ‖(A.mulVec x) i‖^2 = ∑ i, ‖x i‖^2 := by
  have h1 : star (A.mulVec x) ⬝ᵥ (A.mulVec x) = star x ⬝ᵥ (A * A).mulVec x :=
    star_mulVec_dotProduct_mulVec_hermitian A hA_herm x
  rw [hA_sq, Matrix.one_mulVec] at h1
  rw [star_dotProduct_self_eq_sum_normSq, star_dotProduct_self_eq_sum_normSq] at h1
  exact_mod_cast h1


/-- For Hermitian A with A² = I, we have |⟨x, Ax⟩| ≤ ‖x‖² -/
lemma inner_mul_self_bound {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hA_herm : A.IsHermitian)
    (hA_sq : A * A = 1)
    (x : Fin n → ℂ) :
    ‖star x ⬝ᵥ A.mulVec x‖ ≤ ‖star x ⬝ᵥ x‖ := by
  let x' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  let y' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (A.mulVec x)
  have h_inner : star x ⬝ᵥ A.mulVec x = inner (𝕜 := ℂ) x' y' := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct]
    rw [dotProduct_comm]
  rw [h_inner]
  have h_cs : ‖inner (𝕜 := ℂ) x' y'‖ ≤ ‖x'‖ * ‖y'‖ := norm_inner_le_norm x' y'
  have h_norm_y : ‖y'‖ = ‖x'‖ := by
    simp only [EuclideanSpace.norm_eq]
    congr 1
    exact sum_normSq_mulVec_eq_of_hermitian_sq_one A hA_herm hA_sq x
  rw [h_norm_y] at h_cs
  rw [norm_star_dotProduct_self]
  convert h_cs using 1
  ring_nf
  exact Eq.symm (EuclideanSpace.norm_sq_eq x')

lemma hermitian_dotProduct_self_im_eq_zero (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ A.mulVec x).im = 0 := by
  rw [Complex.conj_eq_iff_im.mp]
  calc star (star x ⬝ᵥ A.mulVec x)
      = star (A.mulVec x) ⬝ᵥ star (star x) :=
        Eq.symm (star_dotProduct_star (A *ᵥ x) (star x))
    _ = star (A.mulVec x) ⬝ᵥ x := by rw [star_star]
    _ = Matrix.vecMul (star x) Aᴴ ⬝ᵥ x := by rw [Matrix.star_mulVec]
    _ = Matrix.vecMul (star x) A ⬝ᵥ x := by rw [hA.eq]
    _ = star x ⬝ᵥ A.mulVec x := by rw [← Matrix.dotProduct_mulVec]

/-- (I + A)/2 is positive semidefinite when A is Hermitian with A² = I -/
lemma spectral_proj_plus_posSemidef {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hA_herm : A.IsHermitian)
    (hA_sq : A * A = 1) :
    IsPosSemidefComplex ((1/2 : ℂ) • (1 + A)) := by
  intro x
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
  simp only [dotProduct_add, dotProduct_smul]
  simp only [one_div, smul_eq_mul, mul_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self',
    add_re, inv_im, im_ofNat]
  ring_nf
  have h_self_nonneg := star_dotProduct_self_re_nonneg x
  have h_bound := inner_mul_self_bound A hA_herm hA_sq x
  have h_im := hermitian_dotProduct_self_im_eq_zero A hA_herm x
  have h_norm_re : ‖star x ⬝ᵥ A.mulVec x‖ = |(star x ⬝ᵥ A.mulVec x).re| := by
    exact Eq.symm ((fun {z} => abs_re_eq_norm.mpr) h_im)
  rw [h_norm_re, norm_star_dotProduct_self] at h_bound
  have h_re_le : -(star x ⬝ᵥ A.mulVec x).re ≤ ∑ i, ‖x i‖^2 := by
    have := abs_le.mp h_bound
    linarith [this.1]
  have h_self_eq : (star x ⬝ᵥ x).re = ∑ i, ‖x i‖^2 := by
    have := star_dotProduct_self_eq_sum_normSq x
    simp only at this ⊢
    exact congrArg Complex.re this
  rw [h_self_eq]
  linarith

/-- (I - A)/2 is positive semidefinite when A is Hermitian with A² = I -/
lemma spectral_proj_minus_posSemidef {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hA_herm : A.IsHermitian)
    (hA_sq : A * A = 1) :
    IsPosSemidefComplex ((1/2 : ℂ) • (1 - A)) := by
  intro x
  simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [dotProduct_sub, dotProduct_smul]
  simp only [one_div, smul_eq_mul, mul_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self',
    sub_re, inv_im, im_ofNat]
  ring_nf
  have h_self_nonneg := star_dotProduct_self_re_nonneg x
  have h_bound := inner_mul_self_bound A hA_herm hA_sq x
  have h_im := hermitian_dotProduct_self_im_eq_zero A hA_herm x
  have h_norm_re : ‖star x ⬝ᵥ A.mulVec x‖ = |(star x ⬝ᵥ A.mulVec x).re| := by
    exact Eq.symm ((fun {z} => abs_re_eq_norm.mpr) h_im)
  rw [h_norm_re, norm_star_dotProduct_self] at h_bound
  have h_re_le : (star x ⬝ᵥ A.mulVec x).re ≤ ∑ i, ‖x i‖^2 := by
    have := abs_le.mp h_bound
    linarith [this.2]
  have h_self_eq : (star x ⬝ᵥ x).re = ∑ i, ‖x i‖^2 := by
    have := star_dotProduct_self_eq_sum_normSq x
    simp only at this ⊢
    exact congrArg Complex.re this
  rw [h_self_eq]
  linarith

private lemma finsupp_sum_eq_dotProduct_mulVec {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n →₀ ℂ) :
    (x.sum fun i xi => x.sum fun j xj =>
      xj * (M i j * star xi)) = star ⇑x ⬝ᵥ M *ᵥ ⇑x := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  -- Convert outer Finsupp.sum → Finset.sum
  rw [Finsupp.sum_fintype _ _ (fun i => by
    -- Need: x.sum (fun j xj => xj * (M i j * star 0)) = 0
    simp only [star_zero, mul_zero, mul_zero]
    exact Finsupp.sum_fun_zero x)]
  -- Convert inner Finsupp.sum → Finset.sum
  congr 1; ext i
  rw [Finsupp.sum_fintype _ _ (fun j => by simp [zero_mul])]
  -- Now both sides are Finset.sum; factor and ring
  rw [Finset.mul_sum]
  congr 1; ext j; ring

-- Match the exact ordering in Matrix.PosSemidef
private lemma finsupp_quadform_eq_dotProduct_mulVec {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n →₀ ℂ) :
    (x.sum fun i xi => x.sum fun j xj =>
      star xi * M i j * xj) = star ⇑x ⬝ᵥ M *ᵥ ⇑x := by
  rw [← finsupp_sum_eq_dotProduct_mulVec M x]
  simp only [Finsupp.sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma isPosSemidefComplex_iff_posSemidef {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) :
    letI := Complex.partialOrder
    IsPosSemidefComplex M ↔ M.PosSemidef := by
  letI := Complex.partialOrder
  constructor
  · intro h
    exact ⟨hM, fun x => by
      rw [finsupp_quadform_eq_dotProduct_mulVec, RCLike.nonneg_iff]
      exact ⟨h ⇑x, hermitian_dotProduct_self_im_eq_zero M hM ⇑x⟩⟩
  · intro ⟨_, h⟩ x
    let x' : Fin n →₀ ℂ := Finsupp.equivFunOnFinite.symm x
    have hx' : ⇑x' = x := by ext; simp [x', Finsupp.equivFunOnFinite]
    have h' := h x'
    rw [finsupp_quadform_eq_dotProduct_mulVec, hx', RCLike.nonneg_iff] at h'
    exact h'.1

lemma trace_posSemidef_mul_re_nonneg {n : ℕ} [NeZero n]
    (P ρ : Matrix (Fin n) (Fin n) ℂ)
    (hP_herm : P.IsHermitian)
    (hρ_herm : ρ.IsHermitian)
    (hP_pos : IsPosSemidefComplex P)
    (hρ_pos : IsPosSemidefComplex ρ) :
    0 ≤ (P * ρ).trace.re := by
  letI := Complex.partialOrder
  haveI : AddLeftMono ℂ := ⟨fun a _ _ h => by
    rw [Complex.le_def] at h ⊢
    simp only [Complex.add_re, Complex.add_im]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩⟩
  have hP_psd := (isPosSemidefComplex_iff_posSemidef P hP_herm).mp hP_pos
  have hρ_psd := (isPosSemidefComplex_iff_posSemidef ρ hρ_herm).mp hρ_pos
  -- Spectral decomposition of ρ
  let Uu := Matrix.IsHermitian.eigenvectorUnitary hρ_herm
  let U : Matrix (Fin n) (Fin n) ℂ := ↑Uu
  let d := Matrix.IsHermitian.eigenvalues hρ_herm
  let d' : Fin n → ℂ := RCLike.ofReal ∘ d
  let D := Matrix.diagonal d'
  -- ρ = U * D * star U (unfolding conjStarAlgAut)
  have hρ_spec : ρ = U * D * star U := by
    have := Matrix.IsHermitian.spectral_theorem hρ_herm
    -- THIS IS THE STEP THAT NEEDS THE PROBE RESULT
    simp only [Unitary.conjStarAlgAut] at this  -- adjust based on probe
    exact this
  -- B := star U * P * U is PSD by sandwich
  let B := star U * P * U
  have hB_psd : B.PosSemidef := hP_psd.conjTranspose_mul_mul_same U
  -- Tr(Pρ) = Tr(B * D)
  have h_trace_eq : (P * ρ).trace = (B * D).trace :=
    calc (P * ρ).trace
        = (P * (U * D * star U)).trace := by rw [hρ_spec]
      _ = ((P * U * D) * star U).trace := by simp only [Matrix.mul_assoc]
      _ = (star U * (P * U * D)).trace := by rw [Matrix.trace_mul_comm]
      _ = (B * D).trace := by simp only [B, Matrix.mul_assoc]
  -- Tr(B * D) = Σᵢ Bᵢᵢ * d'ᵢ
  have h_trace_sum : (B * D).trace = ∑ i, B i i * d' i := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, D,
               Matrix.diagonal_apply, mul_ite, mul_zero,
               Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  -- Push .re through sum, each term nonneg
  rw [h_trace_eq, h_trace_sum]
  -- Goal: 0 ≤ (∑ i, B i i * d' i).re
  -- Bridge .re to a map_sum compatible form
  have h_re_dist : (∑ i, B i i * d' i).re = ∑ i, (B i i * d' i).re := by
    change Complex.reCLM (∑ i, B i i * d' i) = ∑ i, Complex.reCLM (B i i * d' i)
    exact map_sum Complex.reCLM _ _
  rw [h_re_dist]
  apply Finset.sum_nonneg
  intro i _
  have hB_diag : 0 ≤ (B i i).re := by
    have h := Matrix.PosSemidef.diag_nonneg hB_psd (i := i)
    exact (Complex.le_def.mp h).1
  have hd_nonneg : 0 ≤ d i := Matrix.PosSemidef.eigenvalues_nonneg hρ_psd i
  simp only [d', Function.comp, Complex.mul_re, coe_algebraMap, ofReal_re,
                                  ofReal_im, mul_zero, sub_zero, ge_iff_le]
  exact mul_nonneg hB_diag hd_nonneg



/-- For a dichotomic observable (A² = I, A Hermitian) and density matrix ρ,
    the expectation value satisfies |Tr(Aρ)| ≤ 1.

    Proof idea: A has eigenvalues ±1, ρ is a probability distribution over
    eigenstates, so Tr(Aρ) is a convex combination of ±1. -/
lemma dichotomic_expectation_bound {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hA_herm : A.IsHermitian)
    (hA_sq : A * A = 1)
    (ρ : DensityMatrix n) :
    ‖(A * ρ.toMatrix).trace‖ ≤ 1 := by
  -- Step 1: The expectation is real
  have h_real := hermitian_expectation_real A hA_herm ρ.toMatrix ρ.hermitian

  -- Step 2: For real complex numbers, ‖z‖ = |z.re|
  have h_norm : ‖(A * ρ.toMatrix).trace‖ = |(A * ρ.toMatrix).trace.re| := by
    exact Eq.symm ((fun {z} => abs_re_eq_norm.mpr) h_real)

  rw [h_norm]

  -- Step 3: Define spectral projections P_plus = (I + A)/2, P_minus = (I - A)/2
  let P_plus : Matrix (Fin n) (Fin n) ℂ := (1/2 : ℂ) • (1 + A)
  let P_minus : Matrix (Fin n) (Fin n) ℂ := (1/2 : ℂ) • (1 - A)

  -- Step 4: Show A = P_plus - P_minus
  have hA_decomp : A = P_plus - P_minus := by
    simp only [P_plus, P_minus, ← smul_sub, add_sub_sub_cancel, ← two_smul ℂ A, smul_smul]
    norm_num
    exact Eq.symm (MulAction.one_smul A)

  -- Step 5: Rewrite trace using decomposition
  have h_trace : (A * ρ.toMatrix).trace = (P_plus * ρ.toMatrix).trace - (P_minus * ρ.toMatrix).trace := by
    rw [hA_decomp, sub_mul, Matrix.trace_sub]

  -- Step 6: Show Tr(P_plusρ) + Tr(P_minusρ) = 1
  have h_sum : (P_plus * ρ.toMatrix).trace + (P_minus * ρ.toMatrix).trace = 1 := by
    rw [← Matrix.trace_add, ← add_mul]
    simp only [P_plus, P_minus]
    have : (1 / 2 : ℂ) • (1 + A) + (1 / 2 : ℂ) • (1 - A) = 1 := by
      ext i j
      simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sub_apply]
      ring
    rw [this, Matrix.one_mul]
    exact ρ.trace_one

  -- Step 7: Show P_plus, P_minus are Hermitian (for real traces)
  have h_P_plus_proj : P_plus * P_plus = P_plus := by
    show (1/2 : ℂ) • (1 + A) * ((1/2 : ℂ) • (1 + A)) = (1/2 : ℂ) • (1 + A)
    rw [mul_smul_comm, smul_mul_assoc, smul_smul]
    have h_sq : (1 + A) * (1 + A) = (2 : ℂ) • (1 + A) := by
      rw [mul_add, add_mul, add_mul, Matrix.mul_one, Matrix.one_mul, hA_sq]
      ext i j; simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]; ring
    rw [h_sq, smul_smul]
    norm_num

  have h_P_minus_proj : P_minus * P_minus = P_minus := by
    show (1/2 : ℂ) • (1 - A) * ((1/2 : ℂ) • (1 - A)) = (1/2 : ℂ) • (1 - A)
    rw [mul_smul_comm, smul_mul_assoc, smul_smul]
    have h_sq : (1 - A) * (1 - A) = (2 : ℂ) • (1 - A) := by
      rw [mul_sub, sub_mul, sub_mul, Matrix.mul_one, Matrix.one_mul, hA_sq]
      ext i j; simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]; ring
    rw [h_sq, smul_smul]
    norm_num

  have h_P_plus_herm : P_plus.IsHermitian := by
    simp only [P_plus, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
               Matrix.conjTranspose_one, hA_herm.eq, one_div, star_inv₀, star_ofNat]
  have h_P_minus_herm : P_minus.IsHermitian := by
    simp only [P_minus, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
               Matrix.conjTranspose_one, hA_herm.eq, one_div, star_inv₀, star_ofNat]

  -- Step 8: Show traces are non-negative
  have h_tr_plus_nonneg : 0 ≤ (P_plus * ρ.toMatrix).trace.re := by
    apply trace_posSemidef_mul_re_nonneg
    · exact h_P_plus_herm
    · exact ρ.hermitian
    · exact spectral_proj_plus_posSemidef A hA_herm hA_sq
    · exact ρ.posSemidef
  have h_tr_minus_nonneg : 0 ≤ (P_minus * ρ.toMatrix).trace.re := by
    apply trace_posSemidef_mul_re_nonneg
    · exact h_P_minus_herm
    · exact ρ.hermitian
    · exact spectral_proj_minus_posSemidef A hA_herm hA_sq
    · exact ρ.posSemidef

  -- Step 9: Final bound: |a - b| ≤ 1 when a,b ≥ 0 and a + b = 1
  have h_sum_re : (P_plus * ρ.toMatrix).trace.re + (P_minus * ρ.toMatrix).trace.re = 1 := by
    have := congrArg Complex.re h_sum
    simp only [Complex.add_re, Complex.one_re] at this
    exact this

  rw [h_trace, Complex.sub_re]
  have h1 : (P_plus * ρ.toMatrix).trace.re ≤ 1 := by linarith
  have h2 : (P_minus * ρ.toMatrix).trace.re ≤ 1 := by linarith
  rw [abs_sub_le_iff]
  constructor <;> linarith


/-- Algebraic lemma: when |a|, |a'|, |b|, |b'| ≤ 1,
    |a*b' - a*b + a'*b + a'*b'| ≤ 2

    Key insight: rewrite as a*(b'-b) + a'*(b+b')
    Since b, b' ∈ [-1,1], we have |b'-b| + |b+b'| ≤ 2 -/
lemma chsh_expectation_algebraic_bound (a a' b b' : ℝ)
    (ha : |a| ≤ 1) (ha' : |a'| ≤ 1)
    (hb : |b| ≤ 1) (hb' : |b'| ≤ 1) :
    |a * b' - a * b + a' * b + a' * b'| ≤ 2 := by
  -- Rewrite: a*b' - a*b + a'*b + a'*b' = a*(b'-b) + a'*(b+b')
  have h1 : a * b' - a * b + a' * b + a' * b' = a * (b' - b) + a' * (b + b') := by ring
  rw [h1]
  -- Triangle inequality
  calc |a * (b' - b) + a' * (b + b')|
      ≤ |a * (b' - b)| + |a' * (b + b')| := abs_add_le _ _ -- Unknown identifier `abs_add`
    _ = |a| * |b' - b| + |a'| * |b + b'| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * |b' - b| + 1 * |b + b'| := by
        apply add_le_add
        · exact mul_le_mul ha (le_refl _) (abs_nonneg _) zero_le_one
        · exact mul_le_mul ha' (le_refl _) (abs_nonneg _) zero_le_one
    _ = |b' - b| + |b + b'| := by ring
    _ ≤ 2 := by
        -- Split on signs of (b' - b) and (b + b')
        rcases le_or_gt 0 (b' - b) with hbd_nn | hbd_neg
        <;> rcases le_or_gt 0 (b + b') with hbs_nn | hbs_neg
        · -- b' - b ≥ 0, b + b' ≥ 0
          calc |b' - b| + |b + b'| = (b' - b) + (b + b') := by
                  rw [abs_of_nonneg hbd_nn, abs_of_nonneg hbs_nn]
            _ = 2 * b' := by ring
            _ ≤ 2 * 1 := by nlinarith [abs_le.mp hb']
            _ = 2 := by ring
        · -- b' - b ≥ 0, b + b' < 0
          calc |b' - b| + |b + b'| = (b' - b) + -(b + b') := by
                  rw [abs_of_nonneg hbd_nn, abs_of_neg hbs_neg]
            _ = -2 * b := by ring
            _ ≤ 2 * 1 := by nlinarith [abs_le.mp hb]
            _ = 2 := by ring
        · -- b' - b < 0, b + b' ≥ 0
          calc |b' - b| + |b + b'| = -(b' - b) + (b + b') := by
                  rw [abs_of_neg hbd_neg, abs_of_nonneg hbs_nn]
            _ = 2 * b := by ring
            _ ≤ 2 * 1 := by nlinarith [abs_le.mp hb]
            _ = 2 := by ring
        · -- b' - b < 0, b + b' < 0
          calc |b' - b| + |b + b'| = -(b' - b) + -(b + b') := by
                  rw [abs_of_neg hbd_neg, abs_of_neg hbs_neg]
            _ = -2 * b' := by ring
            _ ≤ 2 * 1 := by nlinarith [abs_le.mp hb']
            _ = 2 := by ring

/-- Mixed product property for kroneckerMap with multiplication -/
lemma kronecker_mul_mul {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A C : Matrix m m ℂ) (B D : Matrix n n ℂ) :
    kroneckerMap (· * ·) A B * kroneckerMap (· * ·) C D =
    kroneckerMap (· * ·) (A * C) (B * D) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.mul_apply, kroneckerMap_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  -- Goal: ∑ y, ∑ x, A i₁ x * B i₂ y * (C x j₁ * D y j₂) = (∑ j, A i₁ j * C j j₁) * ∑ j, B i₂ j * D j j₂
  -- Step 1: Rewrite each summand to group A*C and B*D terms
  have h : ∀ y x, A i₁ x * B i₂ y * (C x j₁ * D y j₂) = (A i₁ x * C x j₁) * (B i₂ y * D y j₂) :=
    fun y x => by ring
  simp_rw [h]
  -- Step 2: Factor (B i₂ y * D y j₂) out of inner sum
  simp_rw [← Finset.sum_mul]
  -- Step 3: Factor (∑ x, A i₁ x * C x j₁) out of outer sum
  rw [← Finset.mul_sum]

/-- Trace of Kronecker product factors -/
lemma trace_kronecker_mul {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    (kroneckerMap (· * ·) A B).trace = A.trace * B.trace :=
  Matrix.trace_kronecker A B

end QuantumInfo
