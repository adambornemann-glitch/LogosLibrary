/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent
/-!
# Yosida Approximation and Stone's Theorem (Converse)

This file proves the converse of Stone's theorem: every self-adjoint operator
generates a strongly continuous one-parameter unitary group via the formula
`U(t) = exp(itA)`, constructed as the limit of Yosida approximants.

## Main definitions

* `yosidaApprox`: The Yosida approximant `Aₙ = n²R(in) - in·I`
* `yosidaApproxSym`: The symmetric Yosida approximant `(n²/2)(R(in) + R(-in))`
* `yosidaJ`, `yosidaJNeg`: The contractive operators `Jₙ = -in·R(in)`, `Jₙ⁻ = in·R(-in)`
* `expBounded`: Exponential of bounded operators via power series
* `exponential`: The unitary group `exp(itA)` as limit of `exp(it·Aₙˢʸᵐ)`

## Main statements

* `yosidaApproxSym_selfAdjoint`: Aₙˢʸᵐ is self-adjoint
* `I_smul_yosidaApproxSym_skewAdjoint`: i·Aₙˢʸᵐ is skew-adjoint
* `expBounded_yosidaApproxSym_unitary`: exp(i·Aₙˢʸᵐ·t) preserves inner products
* `yosidaApprox_tendsto_on_domain`: Aₙφ → Aφ for φ ∈ D(A)
* `duhamel_identity`: U(t)φ - exp(Bₙt)φ = ∫₀ᵗ exp(Bₙ(t-s))·(iA - Bₙ)(U(s)φ) ds
* `exponential_unitary`: exp(itA) is unitary
* `exponential_group_law`: exp(i(s+t)A) = exp(isA)·exp(itA)
* `exponential_strong_continuous`: t ↦ exp(itA)ψ is continuous
* `exponential_generator_eq`: The generator of exp(itA) is iA

## Strategy

1. Approximate the unbounded A by bounded Aₙ using resolvents at z = ±in
2. exp(i·Aₙ·t) is unitary because i·Aₙ is skew-adjoint
3. Duhamel's formula relates U(t) - exp(i·Aₙ·t) to an integral of (A - Aₙ)
4. The integrand norm is constant in s (A commutes with U(t) on domain)
5. Aₙ → A pointwise on domain, so the integral → 0
6. Completeness gives the limit; properties follow by continuity

## Implementation notes

* We use `yosidaApproxSym` rather than `yosidaApprox` for the exponential to
  ensure self-adjointness without assuming the original group exists.
* The `expBounded` function is defined via tsum and shown equal to `NormedSpace.exp`.
* Duhamel's formula requires differentiating products of operator-valued functions,
  handled via `IsBoundedBilinearMap.hasFDerivAt`.

## References

* [Kato, *Perturbation Theory*][kato1995], Section IX.1
* [Reed-Simon, *Methods of Modern Mathematical Physics I*][reed1980], Theorem VIII.7
-/
namespace QuantumMechanics.Yosida
open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Resolvent QuantumMechanics.Bochner QuantumMechanics.Generators


set_option linter.unusedSectionVars false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


lemma I_mul_pnat_im_ne_zero (n : ℕ+) : (I * (n : ℂ)).im ≠ 0 := by
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
             zero_mul, one_mul, zero_add]
  exact Nat.cast_ne_zero.mpr n.ne_zero


lemma neg_I_mul_pnat_im_ne_zero (n : ℕ+) : (-I * (n : ℂ)).im ≠ 0 := by
  simp only [neg_mul, Complex.neg_im]
  exact neg_ne_zero.mpr (I_mul_pnat_im_ne_zero n)


lemma I_mul_pnat_im (n : ℕ+) : (I * (n : ℂ)).im = (n : ℝ) := by
  simp [Complex.mul_im]


lemma abs_I_mul_pnat_im (n : ℕ+) : |(I * (n : ℂ)).im| = (n : ℝ) := by
  rw [I_mul_pnat_im]
  exact abs_of_pos (Nat.cast_pos.mpr n.pos)


lemma norm_pnat_sq (n : ℕ+) : ‖((n : ℂ)^2)‖ = (n : ℝ)^2 := by
  rw [norm_pow]
  simp


lemma norm_I_mul_pnat (n : ℕ+) : ‖I * (n : ℂ)‖ = (n : ℝ) := by
  calc ‖I * (n : ℂ)‖
      = ‖I‖ * ‖(n : ℂ)‖ := norm_mul I (n : ℂ)
    _ = 1 * ‖(n : ℂ)‖ := by rw [Complex.norm_I]
    _ = ‖(n : ℂ)‖ := one_mul _
    _ = (n : ℝ) := by simp only [Complex.norm_natCast]


lemma resolvent_spec
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : ℂ) (hz : z.im ≠ 0) (φ : H) :
    (Resolvent.resolvent gen z hz hsa φ) ∈ gen.domain ∧
    gen.op ⟨Resolvent.resolvent gen z hz hsa φ,
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists).property⟩ -
    z • (Resolvent.resolvent gen z hz hsa φ) = φ := by
  let ψ_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists
  have h_mem : (ψ_sub : H) ∈ gen.domain := ψ_sub.property
  have h_eq := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists
  constructor
  · exact h_mem
  · convert h_eq using 2


lemma resolvent_spec'
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : ℂ) (hz : z.im ≠ 0) (φ : H) :
    ∃ (h : Resolvent.resolvent gen z hz hsa φ ∈ gen.domain),
      gen.op ⟨Resolvent.resolvent gen z hz hsa φ, h⟩ -
      z • (Resolvent.resolvent gen z hz hsa φ) = φ := by
  let ψ_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists
  have h_eq := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists
  exact ⟨ψ_sub.property, h_eq⟩



noncomputable def resolventAtIn
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa


noncomputable def resolventAtNegIn
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa


noncomputable def yosidaApprox
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  (n : ℂ)^2 • resolventAtIn gen hsa n - (I * (n : ℂ)) • ContinuousLinearMap.id ℂ H


noncomputable def yosidaApproxSym
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  ((n : ℂ)^2 / 2) • (resolventAtIn gen hsa n + resolventAtNegIn gen hsa n)


noncomputable def yosidaJ
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  (-I * (n : ℂ)) • resolventAtIn gen hsa n


noncomputable def yosidaJNeg
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  (I * (n : ℂ)) • resolventAtNegIn gen hsa n


noncomputable def yosidaApproxNeg
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  ((n : ℂ)^2) • resolventAtNegIn gen hsa n + (I * (n : ℂ)) • ContinuousLinearMap.id ℂ H


lemma resolventAtIn_bound
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    ‖resolventAtIn gen hsa n‖ ≤ 1 / (n : ℝ) := by
  unfold resolventAtIn
  calc ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖
      ≤ 1 / |(I * (n : ℂ)).im| := resolvent_bound gen hsa (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n)
    _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]


/-!
============================================================================================================================
## Section 2: Norm Bounds on Yosida Operators
============================================================================================================================
-/
theorem yosidaApprox_norm_bound
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    ‖yosidaApprox gen hsa n‖ ≤ 2 * (n : ℝ) := by
  unfold yosidaApprox

  have h_first : ‖(n : ℂ)^2 • resolventAtIn gen hsa n‖ ≤ (n : ℝ) := by
    calc ‖(n : ℂ)^2 • resolventAtIn gen hsa n‖
        = ‖(n : ℂ)^2‖ * ‖resolventAtIn gen hsa n‖ := norm_smul ((n : ℂ)^2) _
      _ ≤ ‖(n : ℂ)^2‖ * (1 / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left (resolventAtIn_bound gen hsa n)
          exact norm_nonneg _
      _ = (n : ℝ)^2 * (1 / (n : ℝ)) := by rw [norm_pnat_sq]
      _ = (n : ℝ) := by field_simp

  have h_second : ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖ ≤ (n : ℝ) := by
    calc ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖
        = ‖I * (n : ℂ)‖ * ‖ContinuousLinearMap.id ℂ H‖ := norm_smul (I * (n : ℂ)) _
      _ ≤ ‖I * (n : ℂ)‖ * 1 := by
          apply mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
          exact norm_nonneg _
      _ = ‖I * (n : ℂ)‖ := mul_one _
      _ = (n : ℝ) := norm_I_mul_pnat n

  calc ‖(n : ℂ)^2 • resolventAtIn gen hsa n - (I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖
      ≤ ‖(n : ℂ)^2 • resolventAtIn gen hsa n‖ + ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖ :=
          norm_sub_le _ _
    _ ≤ (n : ℝ) + (n : ℝ) := add_le_add h_first h_second
    _ = 2 * (n : ℝ) := by ring



lemma yosidaJ_norm_bound
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    ‖(-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ ≤ 1 := by
  have h_neg : (-I : ℂ) * (n : ℂ) = -(I * (n : ℂ)) := by ring

  have h_coeff : ‖(-I * (n : ℂ))‖ = (n : ℝ) := by
    calc ‖(-I * (n : ℂ))‖
        = ‖-(I * (n : ℂ))‖ := by rw [h_neg]
      _ = ‖I * (n : ℂ)‖ := norm_neg _
      _ = (n : ℝ) := norm_I_mul_pnat n

  have h_res : ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ ≤ 1 / (n : ℝ) := by
    calc ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖
        ≤ 1 / |(I * (n : ℂ)).im| := resolvent_bound gen hsa _ _
      _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]

  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos

  calc ‖(-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖
      = ‖(-I * (n : ℂ))‖ * ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ :=
          norm_smul _ _
    _ = (n : ℝ) * ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ := by
          rw [h_coeff]
    _ ≤ (n : ℝ) * (1 / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h_res
          exact le_of_lt hn_pos
    _ = 1 := by field_simp


lemma yosidaJNeg_norm_bound
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    ‖yosidaJNeg gen hsa n‖ ≤ 1 := by
  unfold yosidaJNeg resolventAtNegIn
  have h_coeff : ‖I * (n : ℂ)‖ = (n : ℝ) := norm_I_mul_pnat n
  have h_res : ‖resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖ ≤ 1 / (n : ℝ) := by
    calc ‖resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖
        ≤ 1 / |(-I * (n : ℂ)).im| := resolvent_bound gen hsa _ _
      _ = 1 / (n : ℝ) := by
          simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re,
                     Complex.I_im, zero_mul, one_mul, zero_add]
          rw [← h_coeff]
          rw [h_coeff]
          rw [@abs_neg]
          rw [natCast_re]
          rw [abs_of_pos (Nat.cast_pos.mpr n.pos)]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos
  calc ‖(I * (n : ℂ)) • resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖
      = ‖I * (n : ℂ)‖ * ‖resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖ :=
          norm_smul _ _
    _ = (n : ℝ) * ‖resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖ := by
          rw [h_coeff]
    _ ≤ (n : ℝ) * (1 / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h_res (le_of_lt hn_pos)
    _ = 1 := by field_simp

/-!
============================================================================================================================
## Section 3: Self-Adjointness and Skew-Adjointness
============================================================================================================================
-/
theorem yosidaApproxSym_selfAdjoint
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    (yosidaApproxSym gen hsa n).adjoint = yosidaApproxSym gen hsa n := by
  unfold yosidaApproxSym resolventAtIn resolventAtNegIn
  ext φ
  apply ext_inner_right ℂ
  intro ψ

  -- Use ⟨T*φ, ψ⟩ = ⟨φ, Tψ⟩
  rw [ContinuousLinearMap.adjoint_inner_left]

  -- Expand the smul and add on both sides
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]

  -- LHS: ⟨φ, (n²/2) • (R(in) + R(-in)) ψ⟩
  -- RHS: ⟨(n²/2) • (R(in) + R(-in)) φ, ψ⟩

  -- The scalar n²/2 is real
  have h_scalar_real : (starRingEnd ℂ) ((n : ℂ)^2 / 2) = (n : ℂ)^2 / 2 := by
    simp only [map_div₀, map_pow]
    congr 1
    simp
    exact conj_eq_iff_re.mpr rfl

  -- Pull scalars through inner products
  rw [inner_smul_right, inner_smul_left, h_scalar_real]
  congr 1

  -- Now show ⟨φ, (R(in) + R(-in)) ψ⟩ = ⟨(R(in) + R(-in)) φ, ψ⟩
  rw [inner_add_right, inner_add_left]

  -- Use resolvent_adjoint: ⟨φ, R(z)ψ⟩ = ⟨R(z̄)φ, ψ⟩
  have h1 : ⟪φ, resolvent gen (I * ↑↑n) (I_mul_pnat_im_ne_zero n) hsa ψ⟫_ℂ =
            ⟪resolvent gen (-I * ↑↑n) (neg_I_mul_pnat_im_ne_zero n) hsa φ, ψ⟫_ℂ := by
    have hadj := resolvent_adjoint gen hsa (I * ↑↑n) (I_mul_pnat_im_ne_zero n)
    have h_conj : (starRingEnd ℂ) (I * ↑↑n) = -I * ↑↑n := by simp []
    rw [← ContinuousLinearMap.adjoint_inner_left]
    congr 1
    rw [hadj]
    congr 1
    rw [← hadj]
    simp_all only [map_div₀, map_pow, map_natCast, neg_mul, map_mul, conj_I]


  have h2 : ⟪φ, resolvent gen (-I * ↑↑n) (neg_I_mul_pnat_im_ne_zero n) hsa ψ⟫_ℂ =
            ⟪resolvent gen (I * ↑↑n) (I_mul_pnat_im_ne_zero n) hsa φ, ψ⟫_ℂ := by
    have hadj := resolvent_adjoint gen hsa (-I * ↑↑n) (neg_I_mul_pnat_im_ne_zero n)
    have h_conj : (starRingEnd ℂ) (-I * ↑↑n) = I * ↑↑n := by simp []
    rw [← ContinuousLinearMap.adjoint_inner_left]
    congr 1
    rw [hadj]
    congr 1
    rw [← hadj]
    simp_all only [map_div₀, map_pow, map_natCast, neg_mul, map_neg, map_mul, conj_I, neg_neg]

  rw [h1, h2]
  ring

theorem I_smul_yosidaApproxSym_skewAdjoint
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    (I • yosidaApproxSym gen hsa n).adjoint = -(I • yosidaApproxSym gen hsa n) := by
  ext φ
  apply ext_inner_right ℂ
  intro ψ

  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply]

  -- LHS: ⟨φ, i • Aₙˢʸᵐ ψ⟩ = i • ⟨φ, Aₙˢʸᵐ ψ⟩
  -- RHS: ⟨-(i • Aₙˢʸᵐ φ), ψ⟩ = -⟨i • Aₙˢʸᵐ φ, ψ⟩ = -ī • ⟨Aₙˢʸᵐ φ, ψ⟩ = i • ⟨Aₙˢʸᵐ φ, ψ⟩

  rw [inner_smul_right, inner_neg_left, inner_smul_left]

  -- conj(I) = -I, so -conj(I) = I
  simp only [Complex.conj_I]

  -- Now need: I • ⟨φ, Aₙˢʸᵐ ψ⟩ = I • ⟨Aₙˢʸᵐ φ, ψ⟩
  -- This follows from self-adjointness of Aₙˢʸᵐ

  -- ⟨φ, Aₙˢʸᵐ ψ⟩ = ⟨(Aₙˢʸᵐ)* φ, ψ⟩ = ⟨Aₙˢʸᵐ φ, ψ⟩
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rw [yosidaApproxSym_selfAdjoint gen hsa n]
  -- ⊢ I * ⟪(yosidaApproxSym gen hsa n) φ, ψ⟫_ℂ = -(-I * ⟪(yosidaApproxSym gen hsa n) φ, ψ⟫_ℂ)
  rw [neg_mul]
  -- ⊢ I * ⟪(yosidaApproxSym gen hsa n) φ, ψ⟫_ℂ = - -(I * ⟪(yosidaApproxSym gen hsa n) φ, ψ⟫_ℂ)
  rw [eq_neg_iff_add_eq_zero, add_eq_zero_iff_neg_eq']
  -- ⊢ - -(I * ⟪(yosidaApproxSym gen hsa n) φ, ψ⟫_ℂ) = I * ⟪(yosidaApproxSym gen hsa n) φ, ψ⟫_ℂ
  rw [neg_eq_iff_eq_neg]


/-!
============================================================================================================================
## Section 4: J Operator Identities and Convergence
============================================================================================================================
-/

lemma yosidaJ_eq_sub_resolvent_A
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (φ : H) (hφ : φ ∈ gen.domain) :
    (-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ =
      φ - Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩) := by
  -- Let R = R(in) and z = in for clarity
  set z := I * (n : ℂ) with hz_def
  set R := Resolvent.resolvent gen z (I_mul_pnat_im_ne_zero n) hsa with hR_def

  -- R(φ) is in domain and satisfies (A - zI)(Rφ) = φ
  obtain ⟨hRφ_domain, hRφ_eq⟩ := resolvent_spec gen hsa z (I_mul_pnat_im_ne_zero n) φ

  -- From (A - zI)(Rφ) = φ, we get A(Rφ) = φ + z·Rφ
  have h_ARφ : gen.op ⟨R φ, hRφ_domain⟩ = φ + z • (R φ) := by
    calc gen.op ⟨R φ, hRφ_domain⟩
        = (gen.op ⟨R φ, hRφ_domain⟩ - z • R φ) + z • R φ := by abel
      _ = φ + z • R φ := by rw [hRφ_eq]

  -- R(Aφ) is in domain and satisfies (A - zI)(R(Aφ)) = Aφ
  obtain ⟨hRAφ_domain, hRAφ_eq⟩ := resolvent_spec gen hsa z (I_mul_pnat_im_ne_zero n) (gen.op ⟨φ, hφ⟩)

  -- Key: R((A-zI)φ) = φ for φ ∈ D(A)
  have h_R_AzI : R (gen.op ⟨φ, hφ⟩ - z • φ) = φ := by
    let ψ_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z
                               (I_mul_pnat_im_ne_zero n) (gen.op ⟨φ, hφ⟩ - z • φ)).exists
    have h_ψ_eq := Classical.choose_spec (self_adjoint_range_all_z gen hsa z
                    (I_mul_pnat_im_ne_zero n) (gen.op ⟨φ, hφ⟩ - z • φ)).exists
    have h_φ_solves : gen.op ⟨φ, hφ⟩ - z • φ = gen.op ⟨φ, hφ⟩ - z • φ := rfl
    have h_subtype : (⟨φ, hφ⟩ : gen.domain) = ψ_sub :=
      (self_adjoint_range_all_z gen hsa z (I_mul_pnat_im_ne_zero n)
        (gen.op ⟨φ, hφ⟩ - z • φ)).unique h_φ_solves h_ψ_eq
    calc R (gen.op ⟨φ, hφ⟩ - z • φ)
        = ψ_sub.val := rfl
      _ = (⟨φ, hφ⟩ : gen.domain).val := by rw [← h_subtype]
      _ = φ := rfl

  -- By linearity: R(Aφ - zφ) = R(Aφ) - z·Rφ
  have h_R_linear : R (gen.op ⟨φ, hφ⟩ - z • φ) = R (gen.op ⟨φ, hφ⟩) - z • R φ := by
    calc R (gen.op ⟨φ, hφ⟩ - z • φ)
        = R (gen.op ⟨φ, hφ⟩) - R (z • φ) := by rw [R.map_sub]
      _ = R (gen.op ⟨φ, hφ⟩) - z • R φ := by rw [R.map_smul]

  -- So R(Aφ) = φ + z·Rφ
  have h_RAφ_explicit : R (gen.op ⟨φ, hφ⟩) = φ + z • R φ := by
    calc R (gen.op ⟨φ, hφ⟩)
        = R (gen.op ⟨φ, hφ⟩) - z • R φ + z • R φ := by abel
      _ = R (gen.op ⟨φ, hφ⟩ - z • φ) + z • R φ := by rw [h_R_linear]
      _ = φ + z • R φ := by rw [h_R_AzI]

  -- Conclude: (-z)·Rφ = φ - R(Aφ)
  calc (-I * (n : ℂ)) • R φ
      = (-z) • R φ := by rw [neg_mul]
    _ = -(z • R φ) := by rw [neg_smul]
    _ = φ - (φ + z • R φ) := by abel
    _ = φ - R (gen.op ⟨φ, hφ⟩) := by rw [← h_RAφ_explicit]


lemma yosidaJ_tendsto_on_domain
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => (-I * (n : ℂ)) •
              Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ)
            atTop (𝓝 φ) := by
  rw [Metric.tendsto_atTop]
  intro ε hε

  by_cases h_Aφ_zero : ‖gen.op ⟨φ, hφ⟩‖ = 0
  · -- Case: Aφ = 0, so Jₙφ = φ for all n
    use 1
    intro n _
    rw [yosidaJ_eq_sub_resolvent_A gen hsa n φ hφ]
    have h_Aφ_eq_zero : gen.op ⟨φ, hφ⟩ = 0 := norm_eq_zero.mp h_Aφ_zero
    simp only [h_Aφ_eq_zero, map_zero, sub_zero]
    rw [dist_self]
    exact hε

  · -- Case: ‖Aφ‖ > 0
    have h_Aφ_pos : 0 < ‖gen.op ⟨φ, hφ⟩‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_Aφ_zero)

    -- Choose N > ‖Aφ‖/ε
    use ⟨Nat.ceil (‖gen.op ⟨φ, hφ⟩‖ / ε) + 1, Nat.add_one_pos _⟩
    intro n hn

    calc dist ((-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ) φ
        = ‖(-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ - φ‖ :=
            dist_eq_norm _ _
      _ = ‖(φ - Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)) - φ‖ := by
            rw [yosidaJ_eq_sub_resolvent_A gen hsa n φ hφ]
      _ = ‖-Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)‖ := by
            congr 1; abel
      _ = ‖Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)‖ :=
            norm_neg _
      _ ≤ ‖Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ * ‖gen.op ⟨φ, hφ⟩‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 / (n : ℝ)) * ‖gen.op ⟨φ, hφ⟩‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            calc ‖Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖
                ≤ 1 / |(I * (n : ℂ)).im| := resolvent_bound gen hsa _ _
              _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]
      _ < ε := by
            have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos
            have h_n_bound : ‖gen.op ⟨φ, hφ⟩‖ / ε + 1 ≤ (n : ℝ) := by
              have h1 : (Nat.ceil (‖gen.op ⟨φ, hφ⟩‖ / ε) + 1 : ℕ) ≤ n := hn
              calc ‖gen.op ⟨φ, hφ⟩‖ / ε + 1
                  ≤ ↑(Nat.ceil (‖gen.op ⟨φ, hφ⟩‖ / ε)) + 1 :=
                      add_le_add_right (Nat.le_ceil _) _
                _ = ↑(Nat.ceil (‖gen.op ⟨φ, hφ⟩‖ / ε) + 1) := by norm_cast
                _ ≤ (n : ℝ) := Nat.cast_le.mpr h1
            have h_ratio_lt : ‖gen.op ⟨φ, hφ⟩‖ / ε < (n : ℝ) := by linarith
            have h_prod_lt : ‖gen.op ⟨φ, hφ⟩‖ < (n : ℝ) * ε := by
              calc ‖gen.op ⟨φ, hφ⟩‖
                  = (‖gen.op ⟨φ, hφ⟩‖ / ε) * ε := by field_simp
                _ < (n : ℝ) * ε := mul_lt_mul_of_pos_right h_ratio_lt hε
            calc (1 / (n : ℝ)) * ‖gen.op ⟨φ, hφ⟩‖
                = ‖gen.op ⟨φ, hφ⟩‖ / (n : ℝ) := by ring
              _ = ‖gen.op ⟨φ, hφ⟩‖ * (1 / (n : ℝ)) := by ring
              _ < ((n : ℝ) * ε) * (1 / (n : ℝ)) := by
                  apply mul_lt_mul_of_pos_right h_prod_lt
                  exact one_div_pos.mpr hn_pos
              _ = ε := by field_simp


theorem yosida_J_tendsto_id
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (ψ : H) :
    Tendsto (fun n : ℕ+ => (-I * (n : ℂ)) •
              resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa ψ)
            atTop (𝓝 ψ) := by
  let J : ℕ+ → H →L[ℂ] H := fun n =>
    (-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa

  rw [Metric.tendsto_atTop]
  intro ε hε

  -- Step 1: Approximate ψ by domain element φ
  have h_dense := gen.dense_domain
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp (h_dense.closure_eq ▸ Set.mem_univ ψ)
                                    (ε / 3) (by linarith)

  -- Step 2: Get N such that Jₙφ is close to φ for n ≥ N
  have h_domain_conv := yosidaJ_tendsto_on_domain gen hsa φ hφ_mem
  rw [Metric.tendsto_atTop] at h_domain_conv
  obtain ⟨N, hN⟩ := h_domain_conv (ε / 3) (by linarith)

  -- Step 3: For n ≥ N, Jₙψ is close to ψ
  use N
  intro n hn

  calc dist (J n ψ) ψ
      ≤ dist (J n ψ) (J n φ) + dist (J n φ) φ + dist φ ψ := dist_triangle4 _ _ _ _
    _ = ‖J n ψ - J n φ‖ + dist (J n φ) φ + dist φ ψ := by rw [dist_eq_norm]
    _ = ‖J n (ψ - φ)‖ + dist (J n φ) φ + dist φ ψ := by
        congr 1
        rw [ContinuousLinearMap.map_sub]
    _ ≤ ‖J n‖ * ‖ψ - φ‖ + dist (J n φ) φ + dist φ ψ := by
        apply add_le_add_right (add_le_add_right (ContinuousLinearMap.le_opNorm _ _) _)
    _ ≤ 1 * ‖ψ - φ‖ + dist (J n φ) φ + dist φ ψ := by
        apply add_le_add_right (add_le_add_right _ _)
        apply mul_le_mul_of_nonneg_right (yosidaJ_norm_bound gen hsa n) (norm_nonneg _)
    _ = ‖ψ - φ‖ + dist (J n φ) φ + dist φ ψ := by rw [one_mul]
    _ = dist ψ φ + dist (J n φ) φ + dist φ ψ := by rw [← dist_eq_norm]
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h1 : dist ψ φ < ε / 3 := hφ_close
        have h2 : dist (J n φ) φ < ε / 3 := hN n hn
        have h3 : dist φ ψ < ε / 3 := by rw [dist_comm]; exact hφ_close
        exact add_lt_add (add_lt_add h1 h2) h3
    _ = ε := by ring


lemma yosidaJNeg_eq_sub_resolvent_A
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (φ : H) (hφ : φ ∈ gen.domain) :
    (I * (n : ℂ)) • Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa φ =
      φ - Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩) := by
  set z := -I * (n : ℂ) with hz_def
  set R := Resolvent.resolvent gen z (neg_I_mul_pnat_im_ne_zero n) hsa with hR_def

  -- R((A-zI)φ) = φ for φ ∈ D(A)
  have h_R_AzI : R (gen.op ⟨φ, hφ⟩ - z • φ) = φ := by
    let ψ_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z
                               (neg_I_mul_pnat_im_ne_zero n) (gen.op ⟨φ, hφ⟩ - z • φ)).exists
    have h_ψ_eq := Classical.choose_spec (self_adjoint_range_all_z gen hsa z
                    (neg_I_mul_pnat_im_ne_zero n) (gen.op ⟨φ, hφ⟩ - z • φ)).exists
    have h_φ_solves : gen.op ⟨φ, hφ⟩ - z • φ = gen.op ⟨φ, hφ⟩ - z • φ := rfl
    have h_subtype : (⟨φ, hφ⟩ : gen.domain) = ψ_sub :=
      (self_adjoint_range_all_z gen hsa z (neg_I_mul_pnat_im_ne_zero n)
        (gen.op ⟨φ, hφ⟩ - z • φ)).unique h_φ_solves h_ψ_eq
    calc R (gen.op ⟨φ, hφ⟩ - z • φ)
        = ψ_sub.val := rfl
      _ = (⟨φ, hφ⟩ : gen.domain).val := by rw [← h_subtype]
      _ = φ := rfl

  -- By linearity: R(Aφ - zφ) = R(Aφ) - z·Rφ
  have h_R_linear : R (gen.op ⟨φ, hφ⟩ - z • φ) = R (gen.op ⟨φ, hφ⟩) - z • R φ := by
    calc R (gen.op ⟨φ, hφ⟩ - z • φ)
        = R (gen.op ⟨φ, hφ⟩) - R (z • φ) := by rw [R.map_sub]
      _ = R (gen.op ⟨φ, hφ⟩) - z • R φ := by rw [R.map_smul]

  -- So R(Aφ) = φ + z·Rφ
  have h_RAφ_explicit : R (gen.op ⟨φ, hφ⟩) = φ + z • R φ := by
    calc R (gen.op ⟨φ, hφ⟩)
        = R (gen.op ⟨φ, hφ⟩) - z • R φ + z • R φ := by abel
      _ = R (gen.op ⟨φ, hφ⟩ - z • φ) + z • R φ := by rw [h_R_linear]
      _ = φ + z • R φ := by rw [h_R_AzI]

  -- Conclude: (in)·Rφ = φ - R(Aφ) since z = -in
  calc (I * (n : ℂ)) • R φ
      = -((-I * (n : ℂ)) • R φ) := by simp only [neg_mul, neg_smul, neg_neg]
    _ = -(z • R φ) := by rw [hz_def]
    _ = φ - (φ + z • R φ) := by abel
    _ = φ - R (gen.op ⟨φ, hφ⟩) := by rw [← h_RAφ_explicit]


lemma yosidaJNeg_tendsto_on_domain
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaJNeg gen hsa n φ) atTop (𝓝 φ) := by
  unfold yosidaJNeg resolventAtNegIn

  have h_identity : ∀ n : ℕ+,
      (I * (n : ℂ)) • Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa φ =
      φ - Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩) :=
    fun n => yosidaJNeg_eq_sub_resolvent_A gen hsa n φ hφ

  have h_tendsto : Tendsto (fun n : ℕ+ => φ - Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)) atTop (𝓝 φ) := by
    -- First show R(-in)(Aφ) → 0
    have h_to_zero : Tendsto (fun n : ℕ+ => Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)) atTop (𝓝 0) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε

      obtain ⟨N, hN⟩ := exists_nat_gt (‖gen.op ⟨φ, hφ⟩‖ / ε)
      use ⟨N + 1, Nat.succ_pos N⟩
      intro n hn

      rw [dist_eq_norm, sub_zero]

      have h_res_bound : ‖Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖ ≤ 1 / (n : ℝ) := by
        calc ‖Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖
            ≤ 1 / |(-I * (n : ℂ)).im| := resolvent_bound gen hsa _ _
          _ = 1 / (n : ℝ) := by
              simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re,
                         Complex.I_im, zero_mul, one_mul, zero_add]
              rw [div_eq_div_iff_comm, natCast_re]
              rw [abs_neg, Nat.abs_cast]

      have hn_ge : (n : ℕ) ≥ N + 1 := hn
      have hn_gt : (n : ℝ) > N := by
        have h : (N + 1 : ℕ) ≤ (n : ℕ) := hn
        calc (n : ℝ) ≥ (N + 1 : ℕ) := Nat.cast_le.mpr h
          _ = N + 1 := by simp
          _ > N := by linarith

      calc ‖Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)‖
          ≤ ‖Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖ * ‖gen.op ⟨φ, hφ⟩‖ :=
              ContinuousLinearMap.le_opNorm _ _
        _ ≤ (1 / (n : ℝ)) * ‖gen.op ⟨φ, hφ⟩‖ := by
              apply mul_le_mul_of_nonneg_right h_res_bound (norm_nonneg _)
        _ = ‖gen.op ⟨φ, hφ⟩‖ / (n : ℝ) := by ring
        _ < ε := by
              by_cases hAφ : ‖gen.op ⟨φ, hφ⟩‖ = 0
              · simp [hAφ, hε]
              · have hAφ_pos : 0 < ‖gen.op ⟨φ, hφ⟩‖ := (norm_nonneg _).lt_of_ne' hAφ
                calc ‖gen.op ⟨φ, hφ⟩‖ / (n : ℝ)
                  < ‖gen.op ⟨φ, hφ⟩‖ / N := by
                      have hN_pos : (0 : ℝ) < N := by
                        have : 0 < ‖gen.op ⟨φ, hφ⟩‖ / ε := div_pos hAφ_pos hε
                        linarith
                      apply div_lt_div_of_pos_left hAφ_pos hN_pos hn_gt
                _ ≤ ε := by
                      have hN_pos : (0 : ℝ) < N := by
                        have : 0 < ‖gen.op ⟨φ, hφ⟩‖ / ε := div_pos hAφ_pos hε
                        linarith
                      rw [propext (div_le_iff₀ hN_pos)]
                      calc ‖gen.op ⟨φ, hφ⟩‖ = (‖gen.op ⟨φ, hφ⟩‖ / ε) * ε := by field_simp
                        _ ≤ N * ε := by
                            apply mul_le_mul_of_nonneg_right (le_of_lt hN) (le_of_lt hε)
                      linarith

    have h_sub : Tendsto (fun n : ℕ+ => φ - Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)) atTop (𝓝 (φ - 0)) := by
      exact Filter.Tendsto.sub tendsto_const_nhds h_to_zero
    simp only [sub_zero] at h_sub
    exact h_sub

  exact h_tendsto.congr (fun n => (h_identity n).symm)


lemma yosidaJNeg_tendsto_id
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) :
    Tendsto (fun n : ℕ+ => yosidaJNeg gen hsa n ψ) atTop (𝓝 ψ) := by

  apply Metric.tendsto_atTop.mpr
  intro ε hε

  -- Step 1: Approximate ψ by φ ∈ D(A) with ‖ψ - φ‖ < ε/3
  have hε3 : ε / 3 > 0 := by linarith
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp
    (h_dense.closure_eq ▸ Set.mem_univ ψ) (ε / 3) hε3
  rw [dist_eq_norm] at hφ_close

  -- Step 2: For φ ∈ D(A), Jₙ⁻φ → φ
  have h_conv_φ := yosidaJNeg_tendsto_on_domain gen hsa φ hφ_mem
  rw [Metric.tendsto_atTop] at h_conv_φ
  obtain ⟨N, hN⟩ := h_conv_φ (ε / 3) hε3

  use N
  intro n hn
  rw [dist_eq_norm]

  calc ‖yosidaJNeg gen hsa n ψ - ψ‖
      = ‖(yosidaJNeg gen hsa n ψ - yosidaJNeg gen hsa n φ) +
         (yosidaJNeg gen hsa n φ - φ) + (φ - ψ)‖ := by abel_nf
    _ ≤ ‖yosidaJNeg gen hsa n ψ - yosidaJNeg gen hsa n φ‖ +
        ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by
          apply le_trans (norm_add_le _ _)
          apply add_le_add_right
          exact norm_add_le _ _
    _ = ‖yosidaJNeg gen hsa n (ψ - φ)‖ +
        ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by
          congr 2
          simp only [map_sub]
    _ ≤ ‖yosidaJNeg gen hsa n‖ * ‖ψ - φ‖ +
        ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by
          apply add_le_add_right
          apply add_le_add_right
          exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖ψ - φ‖ + ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by
          apply add_le_add_right
          apply add_le_add_right
          apply mul_le_mul_of_nonneg_right (yosidaJNeg_norm_bound gen hsa n) (norm_nonneg _)
    _ = ‖ψ - φ‖ + ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by ring
    _ < ε / 3 + ε / 3 + ε / 3 := by
          apply add_lt_add
          apply add_lt_add
          · exact hφ_close
          · rw [← dist_eq_norm]; exact hN n hn
          · rw [norm_sub_rev]; exact hφ_close
    _ = ε := by ring

/-!
============================================================================================================================
## Section 5: Yosida Approximant Convergence
============================================================================================================================
-/

theorem yosidaApprox_eq_J_comp_A (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (φ : H) (hφ : φ ∈ gen.domain) :
    yosidaApprox gen hsa n φ = yosidaJ gen hsa n (gen.op ⟨φ, hφ⟩) := by
  -- Get the key identity: Jₙφ = φ - R(in)(Aφ)
  have hJ_eq := yosidaJ_eq_sub_resolvent_A gen hsa n φ hφ
  -- Rearrange to get R(in)(Aφ) = φ + (in) • R(in)φ
  have hR_Aφ : Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)
             = φ + (I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
    unfold yosidaJ at hJ_eq
    have h_rearrange : Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩) =
             φ - (-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
      calc Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)
          = φ - (φ - Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)) := by
              rw [sub_sub_cancel]
        _ = φ - (-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
              rw [← hJ_eq]
    calc Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)
        = φ - (-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := h_rearrange
      _ = φ + -(-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
          rw [sub_eq_add_neg, neg_smul]
      _ = φ + (I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
          congr 2
          ring
  -- Key scalar identity: (-I * n) * (I * n) = n²
  have h_scalar : (-I * (n : ℂ)) * (I * (n : ℂ)) = (n : ℂ)^2 := by
    calc (-I * (n : ℂ)) * (I * (n : ℂ))
        = -I * I * (n : ℂ) * (n : ℂ) := by ring
      _ = -(I * I) * (n : ℂ)^2 := by ring
      _ = -(I^2) * (n : ℂ)^2 := by rw [sq I]
      _ = -(-1) * (n : ℂ)^2 := by rw [Complex.I_sq]
      _ = (n : ℂ)^2 := by ring
  -- Now prove main equality by computing RHS to LHS
  symm
  unfold yosidaApprox yosidaJ
  simp only [resolventAtIn]
  calc (-I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op ⟨φ, hφ⟩)
      = (-I * (n : ℂ)) • (φ + (I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) _ hsa φ) := by
          rw [hR_Aφ]
    _ = (-I * (n : ℂ)) • φ + (-I * (n : ℂ)) • ((I * (n : ℂ)) • Resolvent.resolvent gen (I * (n : ℂ)) _ hsa φ) := by
          rw [smul_add]
    _ = (-I * (n : ℂ)) • φ + ((-I * (n : ℂ)) * (I * (n : ℂ))) • Resolvent.resolvent gen (I * (n : ℂ)) _ hsa φ := by
          rw [smul_smul]
    _ = (-I * (n : ℂ)) • φ + ((n : ℂ)^2) • Resolvent.resolvent gen (I * (n : ℂ)) _ hsa φ := by
          rw [h_scalar]
    _ = ((n : ℂ)^2) • Resolvent.resolvent gen (I * (n : ℂ)) _ hsa φ + (-I * (n : ℂ)) • φ := by
          rw [add_comm]
    _ = ((n : ℂ)^2) • Resolvent.resolvent gen (I * (n : ℂ)) _ hsa φ - (I * (n : ℂ)) • φ := by
          have h_neg : -I * (n : ℂ) = -(I * (n : ℂ)) := by ring
          have h : (-I * (n : ℂ)) • φ = -((I * (n : ℂ)) • φ) := by
            rw [h_neg, neg_smul]
          rw [h, ← sub_eq_add_neg]


theorem yosidaApprox_tendsto_on_domain
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaApprox gen hsa n ψ) atTop (𝓝 (gen.op ⟨ψ, hψ⟩)) := by
  -- Aₙψ = Jₙ(Aψ) by yosidaApprox_eq_J_comp_A
  -- Jₙ(Aψ) → Aψ by yosida_J_tendsto_id applied to (gen.op ⟨ψ, hψ⟩)
  simp only [fun n => yosidaApprox_eq_J_comp_A gen hsa n ψ hψ]
  exact yosida_J_tendsto_id gen hsa (gen.op ⟨ψ, hψ⟩)


lemma yosidaApproxNeg_eq_JNeg_A
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (φ : H) (hφ : φ ∈ gen.domain) :
    yosidaApproxNeg gen hsa n φ = yosidaJNeg gen hsa n (gen.op ⟨φ, hφ⟩) := by
  unfold yosidaApproxNeg yosidaJNeg resolventAtNegIn
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.id_apply]

  set R := Resolvent.resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa

  have h := yosidaJNeg_eq_sub_resolvent_A gen hsa n φ hφ
  have h_RAφ : R (gen.op ⟨φ, hφ⟩) = φ - (I * (n : ℂ)) • R φ := by
    abel_nf ; rw [h, ← h];
    simp_all only [neg_mul, Int.reduceNeg, neg_smul, one_smul, neg_sub, add_sub_cancel, R]

  -- Compute (in)² = -n²
  have h_in_sq : (I * (n : ℂ)) * (I * (n : ℂ)) = -((n : ℂ)^2) := by
    calc (I * (n : ℂ)) * (I * (n : ℂ))
        = I * I * (n : ℂ) * (n : ℂ) := by ring
      _ = (-1) * (n : ℂ) * (n : ℂ) := by rw [I_mul_I]
      _ = -((n : ℂ)^2) := by ring

  symm
  calc (I * (n : ℂ)) • R (gen.op ⟨φ, hφ⟩)
      = (I * (n : ℂ)) • (φ - (I * (n : ℂ)) • R φ) := by rw [h_RAφ]
    _ = (I * (n : ℂ)) • φ - (I * (n : ℂ)) • ((I * (n : ℂ)) • R φ) := smul_sub _ _ _
    _ = (I * (n : ℂ)) • φ - ((I * (n : ℂ)) * (I * (n : ℂ))) • R φ := by rw [smul_smul]
    _ = (I * (n : ℂ)) • φ - (-((n : ℂ)^2)) • R φ := by rw [h_in_sq]
    _ = (I * (n : ℂ)) • φ + (n : ℂ)^2 • R φ := by rw [neg_smul, sub_neg_eq_add]
    _ = (n : ℂ)^2 • R φ + (I * (n : ℂ)) • φ := by abel



lemma yosidaApproxNeg_tendsto_on_domain
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaApproxNeg gen hsa n φ) atTop (𝓝 (gen.op ⟨φ, hφ⟩)) := by
  have h_eq : ∀ n : ℕ+, yosidaApproxNeg gen hsa n φ = yosidaJNeg gen hsa n (gen.op ⟨φ, hφ⟩) :=
    fun n => yosidaApproxNeg_eq_JNeg_A gen hsa n φ hφ

  simp_rw [h_eq]
  exact yosidaJNeg_tendsto_id gen hsa h_dense (gen.op ⟨φ, hφ⟩)


lemma yosidaApproxSym_eq_avg
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    yosidaApproxSym gen hsa n = (1/2 : ℂ) • (yosidaApprox gen hsa n + yosidaApproxNeg gen hsa n) := by
  unfold yosidaApproxSym yosidaApprox yosidaApproxNeg resolventAtIn resolventAtNegIn
  ext ψ
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
             ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  set R_pos := resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa
  set R_neg := resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa

  have h : (1 / 2 : ℂ) * (n : ℂ)^2 = (n : ℂ)^2 / 2 := by ring

  calc ((n : ℂ)^2 / 2) • (R_pos ψ + R_neg ψ)
      = ((n : ℂ)^2 / 2) • R_pos ψ + ((n : ℂ)^2 / 2) • R_neg ψ := smul_add _ _ _
    _ = (1 / 2 : ℂ) • ((n : ℂ)^2 • R_pos ψ) + (1 / 2 : ℂ) • ((n : ℂ)^2 • R_neg ψ) := by
        simp only [smul_smul]; ring_nf
    _ = (1 / 2 : ℂ) • ((n : ℂ)^2 • R_pos ψ + (n : ℂ)^2 • R_neg ψ) := by rw [← smul_add]
    _ = (1 / 2 : ℂ) • ((n : ℂ)^2 • R_pos ψ - (I * (n : ℂ)) • ψ + ((n : ℂ)^2 • R_neg ψ + (I * (n : ℂ)) • ψ)) := by
        congr 1; abel
    _ = (1 / 2 : ℂ) • (((n : ℂ)^2 • R_pos ψ - (I * (n : ℂ)) • ψ) + ((n : ℂ)^2 • R_neg ψ + (I * (n : ℂ)) • ψ)) := by
        congr 1;


theorem yosidaApproxSym_tendsto_on_domain
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaApproxSym gen hsa n φ) atTop (𝓝 (gen.op ⟨φ, hφ⟩)) := by
  have h_eq : ∀ n : ℕ+, yosidaApproxSym gen hsa n φ =
      (1/2 : ℂ) • (yosidaApprox gen hsa n φ + yosidaApproxNeg gen hsa n φ) := by
    intro n
    calc yosidaApproxSym gen hsa n φ
        = ((1/2 : ℂ) • (yosidaApprox gen hsa n + yosidaApproxNeg gen hsa n)) φ := by
            rw [yosidaApproxSym_eq_avg]
      _ = (1/2 : ℂ) • (yosidaApprox gen hsa n φ + yosidaApproxNeg gen hsa n φ) := by
            simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]

  simp_rw [h_eq]

  have h_pos := yosidaApprox_tendsto_on_domain gen hsa φ hφ
  have h_neg := yosidaApproxNeg_tendsto_on_domain gen hsa h_dense φ hφ

  have h_sum : Tendsto (fun n : ℕ+ => yosidaApprox gen hsa n φ + yosidaApproxNeg gen hsa n φ)
      atTop (𝓝 (gen.op ⟨φ, hφ⟩ + gen.op ⟨φ, hφ⟩)) := h_pos.add h_neg

  have h_half : Tendsto (fun n : ℕ+ => (1/2 : ℂ) • (yosidaApprox gen hsa n φ + yosidaApproxNeg gen hsa n φ))
      atTop (𝓝 ((1/2 : ℂ) • (gen.op ⟨φ, hφ⟩ + gen.op ⟨φ, hφ⟩))) := h_sum.const_smul (1/2 : ℂ)

  have h_simp : (1/2 : ℂ) • (gen.op ⟨φ, hφ⟩ + gen.op ⟨φ, hφ⟩) = gen.op ⟨φ, hφ⟩ := by
    rw [← two_smul ℂ (gen.op ⟨φ, hφ⟩), smul_smul]
    norm_num

  rw [h_simp] at h_half
  exact h_half


theorem yosidaApprox_commutes_resolvent
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (z : ℂ) (hz : z.im ≠ 0) :
    (yosidaApprox gen hsa n).comp (resolvent gen z hz hsa)
      = (resolvent gen z hz hsa).comp (yosidaApprox gen hsa n) := by
  -- First establish that resolvents commute
  have h_resolvent_comm : (resolventAtIn gen hsa n).comp (resolvent gen z hz hsa) =
                          (resolvent gen z hz hsa).comp (resolventAtIn gen hsa n) := by
    unfold resolventAtIn
    by_cases h_eq : I * (n : ℂ) = z
    · have hz' : (I * (n : ℂ)).im ≠ 0 := I_mul_pnat_im_ne_zero n
      have h_res_eq : resolvent gen (I * (n : ℂ)) hz' hsa = resolvent gen z hz hsa := by
        subst h_eq
        congr
      rw [h_res_eq]
    · have h_diff_ne : I * (n : ℂ) - z ≠ 0 := sub_ne_zero.mpr h_eq
      have h_diff_ne' : z - I * (n : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h_eq)
      have h_id1 := resolvent_identity gen hsa (I * (n : ℂ)) z (I_mul_pnat_im_ne_zero n) hz
      have h_id2 := resolvent_identity gen hsa z (I * (n : ℂ)) hz (I_mul_pnat_im_ne_zero n)
      have h1 : (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa).comp (resolvent gen z hz hsa) =
                (I * (n : ℂ) - z)⁻¹ • (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa - resolvent gen z hz hsa) := by
        symm
        calc (I * (n : ℂ) - z)⁻¹ • (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa - resolvent gen z hz hsa)
            = (I * (n : ℂ) - z)⁻¹ • ((I * (n : ℂ) - z) • (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa).comp (resolvent gen z hz hsa)) := by
                rw [h_id1]
          _ = (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa).comp (resolvent gen z hz hsa) := by
                rw [smul_smul, inv_mul_cancel₀ h_diff_ne, one_smul]
      have h2 : (resolvent gen z hz hsa).comp (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa) =
                (z - I * (n : ℂ))⁻¹ • (resolvent gen z hz hsa - resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa) := by
        symm
        calc (z - I * (n : ℂ))⁻¹ • (resolvent gen z hz hsa - resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa)
            = (z - I * (n : ℂ))⁻¹ • ((z - I * (n : ℂ)) • (resolvent gen z hz hsa).comp (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa)) := by
                rw [h_id2]
          _ = (resolvent gen z hz hsa).comp (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa) := by
                rw [smul_smul, inv_mul_cancel₀ h_diff_ne', one_smul]
      rw [h1, h2]
      have h_inv_neg : (z - I * (n : ℂ))⁻¹ = -(I * (n : ℂ) - z)⁻¹ := by
        rw [← neg_sub, neg_inv]
      have h_sub_neg : resolvent gen z hz hsa - resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa =
                      -(resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa - resolvent gen z hz hsa) := by
        rw [neg_sub]
      rw [h_inv_neg, h_sub_neg, smul_neg, neg_smul, neg_neg]
  -- Now expand yosidaApprox and use resolvent commutativity
  unfold yosidaApprox
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  congr 1
  unfold resolventAtIn
  simp only [resolventAtIn] at h_resolvent_comm
  rw [h_resolvent_comm]

/-!
============================================================================================================================
## Section 6: Exponential of Bounded Operators
============================================================================================================================
-/
noncomputable def expBounded (B : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  ∑' (k : ℕ), (1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k


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
  simp only [Complex.ofReal_add, add_smul]
  rw [NormedSpace.exp_add_of_commute h_comm]
  rfl


theorem expBounded_norm_bound (B : H →L[ℂ] H) (t : ℝ) :
    ‖expBounded B t‖ ≤ Real.exp (|t| * ‖B‖) := by
  unfold expBounded
  set X := (t : ℂ) • B with hX
  set f := (fun n : ℕ => (n.factorial : ℂ)⁻¹ • X ^ n) with hf
  set g := (fun n : ℕ => ‖X‖ ^ n / n.factorial) with hg

  have h_norm_summable : Summable g := Real.summable_pow_div_factorial ‖X‖

  have h_term_le : ∀ n, ‖f n‖ ≤ g n := fun n => by
    simp only [hf, hg]
    rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
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
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

  rw [h_eq_exp]
  calc ‖∑' n, f n‖
      ≤ ∑' n, ‖f n‖ := h1
    _ ≤ ∑' n, g n := h2
    _ = Real.exp ‖X‖ := h3
    _ = Real.exp (|t| * ‖B‖) := by rw [h4]


theorem expBounded_yosida_norm_le
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) :
    ‖expBounded (I • yosidaApprox gen hsa n) t‖ ≤ Real.exp (|t| * ‖I • yosidaApprox gen hsa n‖) :=
  expBounded_norm_bound _ _



lemma expBounded_summable (B : H →L[ℂ] H) (t : ℝ) :
    Summable (fun k : ℕ => (1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k) := by
  apply Summable.of_norm
  have h_bound : ∀ k, ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖ ≤ ‖(t : ℂ) • B‖ ^ k / k.factorial := by
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



theorem adjoint_pow (B : H →L[ℂ] H) (k : ℕ) :
    (B ^ k).adjoint = B.adjoint ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    ext φ
    apply ext_inner_right ℂ
    intro ψ
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [ContinuousLinearMap.one_apply]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    ext φ
    apply ext_inner_right ℂ
    intro ψ
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [ContinuousLinearMap.mul_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left (B ^ k)]
    rw [ih]
    rw [← ContinuousLinearMap.adjoint_inner_left B]
    congr 1
    have h_comm : B.adjoint * B.adjoint ^ k = B.adjoint ^ k * B.adjoint := by
      rw [← pow_succ, ← pow_succ', add_comm]
    calc B.adjoint ((B.adjoint ^ k) φ)
        = (B.adjoint * B.adjoint ^ k) φ := rfl
      _ = (B.adjoint ^ k * B.adjoint) φ := by rw [h_comm]
      _ = (B.adjoint ^ k) (B.adjoint φ) := rfl


lemma tsum_apply_of_summable (f : ℕ → H →L[ℂ] H) (hf : Summable f) (x : H) :
    (∑' n, f n) x = ∑' n, f n x := by
  let evalx : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H x
  calc (∑' n, f n) x
      = evalx (∑' n, f n) := rfl
    _ = ∑' n, evalx (f n) := evalx.map_tsum hf
    _ = ∑' n, f n x := rfl



lemma expBounded_norm_summable (B : H →L[ℂ] H) (t : ℝ) :
    Summable (fun k : ℕ => ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖) := by
  have h_bound : ∀ k, ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖ ≤ ‖(t : ℂ) • B‖ ^ k / k.factorial := by
    intro k
    rw [norm_smul]
    calc ‖(1 / k.factorial : ℂ)‖ * ‖((t : ℂ) • B) ^ k‖
        ≤ ‖(1 / k.factorial : ℂ)‖ * ‖(t : ℂ) • B‖ ^ k := by
            apply mul_le_mul_of_nonneg_left (opNorm_pow_le _ _) (norm_nonneg _)
      _ = ‖(t : ℂ) • B‖ ^ k / k.factorial := by
            have h1 : ‖(1 / k.factorial : ℂ)‖ = 1 / k.factorial := by
              simp_all only [one_div, norm_inv, RCLike.norm_natCast]
            rw [h1]
            field_simp
  apply Summable.of_nonneg_of_le
  · intro k; exact norm_nonneg _
  · exact h_bound
  · exact Real.summable_pow_div_factorial ‖(t : ℂ) • B‖



lemma inner_tsum_right' (x : H) (f : ℕ → H) (hf : Summable f) :
    ⟪x, ∑' n, f n⟫_ℂ = ∑' n, ⟪x, f n⟫_ℂ := by
  let L : H →L[ℂ] ℂ := innerSL ℂ x
  have hL : ∀ y, L y = ⟪x, y⟫_ℂ := fun y => rfl
  calc ⟪x, ∑' n, f n⟫_ℂ
      = L (∑' n, f n) := (hL _).symm
    _ = ∑' n, L (f n) := L.map_tsum hf
    _ = ∑' n, ⟪x, f n⟫_ℂ := by simp only [hL]


lemma tsum_inner_left' (f : ℕ → H) (y : H) (hf : Summable f) :
    ⟪∑' n, f n, y⟫_ℂ = ∑' n, ⟪f n, y⟫_ℂ := by
  have h_conj : ⟪∑' n, f n, y⟫_ℂ = (starRingEnd ℂ) ⟪y, ∑' n, f n⟫_ℂ :=
    (inner_conj_symm (∑' n, f n) y).symm
  rw [h_conj, inner_tsum_right' y f hf]
  rw [conj_tsum]
  · congr 1
    ext n
    exact (inner_conj_symm (f n) y)


theorem adjoint_expBounded (B : H →L[ℂ] H) (t : ℝ) :
    (expBounded B t).adjoint = expBounded B.adjoint t := by
  unfold expBounded

  have h_summable : Summable (fun k : ℕ => (1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k) :=
    expBounded_summable B t

  have h_summable_adj : Summable (fun k : ℕ => (1 / k.factorial : ℂ) • ((t : ℂ) • B.adjoint) ^ k) :=
    expBounded_summable B.adjoint t

  ext φ
  apply ext_inner_right ℂ
  intro ψ

  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [tsum_apply_of_summable _ h_summable ψ]
  rw [tsum_apply_of_summable _ h_summable_adj φ]

  have h_inner_summable : Summable (fun k => ((1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k) ψ) := by
    apply Summable.of_norm
    have h_norm_sum := expBounded_norm_summable B t
    have h_scaled : Summable (fun k => ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖ * ‖ψ‖) :=
      h_norm_sum.mul_right ‖ψ‖
    apply Summable.of_nonneg_of_le
    · intro k; exact norm_nonneg _
    · intro k
      exact ContinuousLinearMap.le_opNorm _ _
    · exact h_scaled

  have h_inner_summable_adj : Summable (fun k => ((1 / k.factorial : ℂ) • ((t : ℂ) • B.adjoint) ^ k) φ) := by
    apply Summable.of_norm
    have h_norm_sum := expBounded_norm_summable B.adjoint t
    have h_scaled : Summable (fun k => ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B.adjoint) ^ k‖ * ‖φ‖) :=
      h_norm_sum.mul_right ‖φ‖
    apply Summable.of_nonneg_of_le
    · intro k; exact norm_nonneg _
    · intro k
      exact ContinuousLinearMap.le_opNorm _ _
    · exact h_scaled

  rw [inner_tsum_right' φ _ h_inner_summable]
  rw [tsum_inner_left' _ ψ h_inner_summable_adj]

  congr 1
  ext k

  simp only [ContinuousLinearMap.smul_apply]
  rw [inner_smul_right, inner_smul_left]

  have h_real : (starRingEnd ℂ) (1 / k.factorial : ℂ) = (1 / k.factorial : ℂ) := by
    simp only [map_div₀, map_one, map_natCast]
  rw [h_real]

  congr 1

  have h_smul_pow : ∀ (c : ℂ) (T : H →L[ℂ] H) (n : ℕ), (c • T) ^ n = c ^ n • T ^ n := by
    intro c T n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, pow_succ, ih]
      ext x
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply]
      rw [ContinuousLinearMap.map_smul]
      rw [smul_smul]

  rw [h_smul_pow, h_smul_pow]
  simp only [ContinuousLinearMap.smul_apply]
  rw [inner_smul_right, inner_smul_left]

  have h_t_real : (starRingEnd ℂ) ((t : ℂ) ^ k) = (t : ℂ) ^ k := by
    simp only [map_pow, Complex.conj_ofReal]
  rw [h_t_real]

  congr 1

  rw [← ContinuousLinearMap.adjoint_inner_left (B ^ k)]
  rw [adjoint_pow]



theorem expBounded_skewAdjoint_unitary (B : H →L[ℂ] H) (hB : B.adjoint = -B) (t : ℝ) :
    (expBounded B t).adjoint.comp (expBounded B t) = ContinuousLinearMap.id ℂ H ∧
    (expBounded B t).comp (expBounded B t).adjoint = ContinuousLinearMap.id ℂ H := by
  -- exp(tB)* = exp(tB*) = exp(t(-B)) = exp(-tB)
  have h_adj : (expBounded B t).adjoint = expBounded B (-t) := by
    rw [adjoint_expBounded]
    rw [hB]
    unfold expBounded
    congr 1
    ext k
    congr 2
    ext x
    simp only [Complex.ofReal_neg, neg_smul, smul_neg]

  constructor
  · -- exp(tB)* ∘ exp(tB) = exp(-tB) ∘ exp(tB) = exp(0) = I
    rw [h_adj]
    rw [← expBounded_group_law B (-t) t]
    simp only [neg_add_cancel]
    unfold expBounded
    simp only [Complex.ofReal_zero, zero_smul]
    have h_eq : (fun k : ℕ => (1 / k.factorial : ℂ) • (0 : H →L[ℂ] H) ^ k) =
                (fun k : ℕ => if k = 0 then 1 else 0) := by
      ext k
      cases k with
      | zero => simp
      | succ k => simp [pow_succ]
    rw [h_eq]
    rw [tsum_eq_single 0]
    · abel
    · intro k hk
      simp [hk]

  · -- exp(tB) ∘ exp(tB)* = exp(tB) ∘ exp(-tB) = exp(0) = I
    rw [h_adj]
    rw [← expBounded_group_law B t (-t)]
    simp only [add_neg_cancel]
    unfold expBounded
    simp only [Complex.ofReal_zero, zero_smul]
    have h_eq : (fun k : ℕ => (1 / k.factorial : ℂ) • (0 : H →L[ℂ] H) ^ k) =
                (fun k : ℕ => if k = 0 then 1 else 0) := by
      ext k
      cases k with
      | zero => simp
      | succ k => simp [pow_succ]
    rw [h_eq]
    rw [tsum_eq_single 0]
    · abel
    · intro k hk
      simp [hk]

/-!
============================================================================================================================
## Section 7: Unitarity of Yosida Exponentials
============================================================================================================================
-/
theorem expBounded_yosidaApproxSym_unitary
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (ψ φ : H) :
    ⟪expBounded (I • yosidaApproxSym gen hsa n) t ψ,
     expBounded (I • yosidaApproxSym gen hsa n) t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
  have h_skew := I_smul_yosidaApproxSym_skewAdjoint gen hsa n
  have h_unitary := expBounded_skewAdjoint_unitary (I • yosidaApproxSym gen hsa n) h_skew t
  let U := expBounded (I • yosidaApproxSym gen hsa n) t

  calc ⟪U ψ, U φ⟫_ℂ
      = ⟪ψ, U.adjoint (U φ)⟫_ℂ := (ContinuousLinearMap.adjoint_inner_right U ψ (U φ)).symm
    _ = ⟪ψ, (U.adjoint.comp U) φ⟫_ℂ := rfl
    _ = ⟪ψ, (ContinuousLinearMap.id ℂ H) φ⟫_ℂ := by rw [h_unitary.1]
    _ = ⟪ψ, φ⟫_ℂ := by simp



theorem expBounded_yosidaApproxSym_isometry
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (ψ : H) :
    ‖expBounded (I • yosidaApproxSym gen hsa n) t ψ‖ = ‖ψ‖ := by
  set U := expBounded (I • yosidaApproxSym gen hsa n) t with hU
  have h_inner := expBounded_yosidaApproxSym_unitary gen hsa n t ψ ψ
  have h1 : ‖U ψ‖^2 = re ⟪U ψ, U ψ⟫_ℂ := (inner_self_eq_norm_sq (𝕜 := ℂ) (U ψ)).symm
  have h2 : ‖ψ‖^2 = re ⟪ψ, ψ⟫_ℂ := (inner_self_eq_norm_sq (𝕜 := ℂ) ψ).symm
  have h_sq : ‖U ψ‖^2 = ‖ψ‖^2 := by
    rw [h1, h2, h_inner]
  have h_nonneg1 : 0 ≤ ‖U ψ‖ := norm_nonneg _
  have h_nonneg2 : 0 ≤ ‖ψ‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖U ψ‖ - ‖ψ‖), sq_nonneg (‖U ψ‖ + ‖ψ‖), h_sq, h_nonneg1, h_nonneg2]





/-!
============================================================================================================================
## Section 8: UNIFORM CONVERGENCE ON COMPACT ORBITS
============================================================================================================================
-/

section UniformConvergence

open QuantumMechanics.Resolvent QuantumMechanics.Yosida

variable (U_grp : OneParameterUnitaryGroup (H := H))
variable (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
variable (h_dense : Dense (gen.domain : Set H))

/-- The orbit {U(s)φ : s ∈ [0, |t|]} is compact. -/
lemma orbit_compact (t : ℝ) (φ : H) :
    IsCompact {ψ : H | ∃ s ∈ Set.Icc 0 |t|, ψ = U_grp.U s φ} := by
  have h_eq : {ψ : H | ∃ s ∈ Set.Icc 0 |t|, ψ = U_grp.U s φ} =
              (fun s => U_grp.U s φ) '' (Set.Icc 0 |t|) := by
    ext ψ
    simp only [Set.mem_setOf_eq, Set.mem_image]
    simp_all only [Set.mem_Icc]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨left, right_1⟩ := left
      subst right
      apply Exists.intro
      · apply And.intro
        on_goal 2 => { rfl
        }
        · simp_all only [and_self]
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨left, right_1⟩ := left
      subst right
      apply Exists.intro
      · apply And.intro
        on_goal 2 => { rfl
        }
        · simp_all only [and_self]
  rw [h_eq]
  exact IsCompact.image isCompact_Icc (U_grp.strong_continuous φ)

/-- The Yosida approximants are equicontinuous (uniformly bounded). -/
lemma yosidaApproxSym_equicontinuous :
    ∀ n : ℕ+, ‖yosidaApproxSym gen hsa n‖ ≤ 2 * n := by
  intro n
  unfold yosidaApproxSym

  -- Bound: ‖(n²/2) • (R(in) + R(-in))‖ ≤ |n²/2| * (‖R(in)‖ + ‖R(-in)‖)
  calc ‖((n : ℂ)^2 / 2) • (resolventAtIn gen hsa n + resolventAtNegIn gen hsa n)‖
      ≤ ‖((n : ℂ)^2 / 2)‖ * ‖resolventAtIn gen hsa n + resolventAtNegIn gen hsa n‖ :=
          norm_smul_le _ _
    _ ≤ ‖((n : ℂ)^2 / 2)‖ * (‖resolventAtIn gen hsa n‖ + ‖resolventAtNegIn gen hsa n‖) := by
          apply mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ((n : ℝ)^2 / 2) * (1 / n + 1 / n) := by
          apply mul_le_mul
          · -- ‖(n : ℂ)^2 / 2‖ = n^2 / 2
            simp only [norm_div, Complex.norm_pow, Complex.norm_natCast]
            simp_all only [norm_ofNat, le_refl]
          · -- ‖R(in)‖ + ‖R(-in)‖ ≤ 1/n + 1/n
            apply add_le_add
            · unfold resolventAtIn
              calc ‖Resolvent.resolvent gen (I * n) (I_mul_pnat_im_ne_zero n) hsa‖
                  ≤ 1 / |(I * (n : ℂ)).im| := resolvent_bound gen hsa _ _
                _ = 1 / n := by simp [Complex.mul_im, Complex.I_re, Complex.I_im]
            · unfold resolventAtNegIn
              calc ‖Resolvent.resolvent gen (-I * n) (neg_I_mul_pnat_im_ne_zero n) hsa‖
                  ≤ 1 / |(-I * (n : ℂ)).im| := resolvent_bound gen hsa _ _
                _ = 1 / n := by simp [Complex.mul_im, Complex.I_re, Complex.I_im, abs_neg]
          · apply add_nonneg <;> positivity
          · positivity
    _ = n := by
          have hn : (n : ℝ) > 0 := Nat.cast_pos.mpr n.pos
          field_simp
          ring
    _ ≤ 2 * n := by simp_all only [Nat.cast_pos, PNat.pos, le_mul_iff_one_le_left, Nat.one_le_ofNat]

/-- Pointwise convergence of Yosida approximants on the domain. -/
lemma yosidaApproxSym_pointwise
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaApproxSym gen hsa n ψ) atTop (𝓝 (gen.op ⟨ψ, hψ⟩)) := by
  exact yosidaApproxSym_tendsto_on_domain gen hsa h_dense ψ hψ



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
  simp_all only [one_div, smul_ite, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, smul_zero, tsum_ite_eq,
    ContinuousLinearMap.one_apply]


lemma unitary_group_at_zero
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (ψ : H) :
    U_grp.U 0 ψ = ψ := by
  rw [U_grp.identity]
  simp only [ContinuousLinearMap.id_apply]


lemma unitary_group_domain_invariant
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    U_grp.U t φ ∈ gen.domain :=
  gen.domain_invariant t φ hφ


lemma generator_commutes_unitary
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    gen.op ⟨U_grp.U t φ, gen.domain_invariant t φ hφ⟩ = U_grp.U t (gen.op ⟨φ, hφ⟩) := by
  have hUtφ : U_grp.U t φ ∈ gen.domain := gen.domain_invariant t φ hφ
  have h_gen_Utφ := gen.generator_formula ⟨U_grp.U t φ, hUtφ⟩
  have h_gen_φ := gen.generator_formula ⟨φ, hφ⟩

  have h_key : ∀ s : ℝ, U_grp.U s (U_grp.U t φ) - U_grp.U t φ = U_grp.U t (U_grp.U s φ - φ) := by
    intro s
    have h1 : U_grp.U s (U_grp.U t φ) = U_grp.U (s + t) φ := by
      rw [U_grp.group_law]
      rfl
    have h2 : U_grp.U (s + t) φ = U_grp.U (t + s) φ := by
      rw [add_comm]
    have h3 : U_grp.U (t + s) φ = U_grp.U t (U_grp.U s φ) := by
      rw [U_grp.group_law]
      rfl
    calc U_grp.U s (U_grp.U t φ) - U_grp.U t φ
        = U_grp.U t (U_grp.U s φ) - U_grp.U t φ := by rw [h1, h2, h3]
      _ = U_grp.U t (U_grp.U s φ) - U_grp.U t φ := rfl
      _ = U_grp.U t (U_grp.U s φ - φ) := by rw [ContinuousLinearMap.map_sub]

  have h_eq_seq : ∀ s : ℝ, (I * s)⁻¹ • (U_grp.U s (U_grp.U t φ) - U_grp.U t φ) =
                          U_grp.U t ((I * s)⁻¹ • (U_grp.U s φ - φ)) := by
    intro s
    rw [h_key s, ContinuousLinearMap.map_smul]

  have h_rhs_tendsto : Tendsto (fun s : ℝ => U_grp.U t ((I * (s : ℂ))⁻¹ • (U_grp.U s φ - φ)))
                               (𝓝[≠] 0) (𝓝 (U_grp.U t (gen.op ⟨φ, hφ⟩))) := by
    apply Filter.Tendsto.comp (U_grp.U t).continuous.continuousAt h_gen_φ

  have h_limits_eq := tendsto_nhds_unique h_gen_Utφ (h_rhs_tendsto.congr (fun s => (h_eq_seq s).symm))
  exact h_limits_eq


/-!
================================================================================
SECTION 8X: DUHAMEL FORMULA
================================================================================
-/

section DuhamelFormula

open QuantumMechanics.Resolvent

variable (U_grp : OneParameterUnitaryGroup (H := H))
variable (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
variable (h_dense : Dense (gen.domain : Set H))


noncomputable def duhamelIntegrand
    (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) (s : ℝ) : H :=
  expBounded (I • yosidaApproxSym gen hsa n) (t - s)
    (I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ - I • yosidaApproxSym gen hsa n (U_grp.U s φ))


/-- The integrand is continuous in s. -/
lemma duhamelIntegrand_continuous (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    Continuous (duhamelIntegrand U_grp gen hsa n t φ hφ) := by
  unfold duhamelIntegrand

  have h_comm : ∀ s, gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ =
                     U_grp.U s (gen.op ⟨φ, hφ⟩) :=
    fun s => generator_commutes_unitary gen s φ hφ

  have h_Uφ_cont : Continuous (fun s => U_grp.U s φ) := U_grp.strong_continuous φ
  have h_UAφ_cont : Continuous (fun s => U_grp.U s (gen.op ⟨φ, hφ⟩)) :=
    U_grp.strong_continuous (gen.op ⟨φ, hφ⟩)

  have h_Aorbit_cont : Continuous (fun s => gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩) := by
    simp_rw [h_comm]; exact h_UAφ_cont

  have h_yosida_cont : Continuous (fun s => yosidaApproxSym gen hsa n (U_grp.U s φ)) :=
    (yosidaApproxSym gen hsa n).continuous.comp h_Uφ_cont

  have h_diff_cont : Continuous (fun s =>
      I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ -
      I • yosidaApproxSym gen hsa n (U_grp.U s φ)) :=
    (continuous_const.smul h_Aorbit_cont).sub (continuous_const.smul h_yosida_cont)

  set B := I • yosidaApproxSym gen hsa n

  -- Show τ ↦ expBounded B τ is continuous (in operator norm)
  have h_exp_cont_τ : Continuous (fun τ : ℝ => expBounded B τ) := by
    unfold expBounded
    have h_eq : ∀ τ : ℝ, (∑' k : ℕ, (1 / k.factorial : ℂ) • ((τ : ℂ) • B) ^ k) =
                NormedSpace.exp ℂ ((τ : ℂ) • B) := by
      intro τ
      rw [NormedSpace.exp_eq_tsum]
      congr 1
      ext k
      simp only [one_div]
    simp_rw [h_eq]
    have h_smul_cont : Continuous (fun τ : ℝ => (τ : ℂ) • B) :=
      continuous_ofReal.smul continuous_const
    -- exp on a Banach algebra is continuous via power series
    have h_exp_cont : Continuous (fun T : H →L[ℂ] H => NormedSpace.exp ℂ T) :=
      NormedSpace.exp_continuous
    exact h_exp_cont.comp h_smul_cont

  -- s ↦ expBounded B (t - s) is continuous
  have h_exp_cont_s : Continuous (fun s : ℝ => expBounded B (t - s)) :=
    h_exp_cont_τ.comp (continuous_const.sub continuous_id)

  -- Joint continuity: (T, v) ↦ T v is continuous for CLMs
  exact h_exp_cont_s.clm_apply h_diff_cont

/-- The integrand is bounded. -/
lemma duhamelIntegrand_bound (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) (s : ℝ)
    ( _ /-hs-/ : s ∈ Set.Icc 0 |t|) :
    ‖duhamelIntegrand U_grp gen hsa n t φ hφ s‖ ≤
    ‖I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ - I • yosidaApproxSym gen hsa n (U_grp.U s φ)‖ := by
  unfold duhamelIntegrand
  rw [expBounded_yosidaApproxSym_isometry gen hsa n (t - s)]


/- HELPER LEMMAS FOR duhamel_identity -/

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


/-- expBounded B 0 = 1 -/
lemma expBounded_at_zero' (B : H →L[ℂ] H) : expBounded B 0 = 1 := by
  unfold expBounded
  simp only [ofReal_zero, zero_smul, one_div]
  have h_single : ∀ k ≠ 0, (k.factorial : ℂ)⁻¹ • (0 : H →L[ℂ] H) ^ k = 0 := by
    intro k hk
    rw [zero_pow hk, smul_zero]
  rw [tsum_eq_single 0 h_single]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul]

/-- Key lemma: derivative of exp at 0 along the direction B. -/
lemma expBounded_hasDerivAt_zero (B : H →L[ℂ] H) :
    HasDerivAt (fun τ : ℝ => expBounded B τ) B 0 := by
  rw [hasDerivAt_iff_tendsto_slope]

  have h_exp_zero : expBounded B 0 = 1 := expBounded_at_zero' B

  have h_eq_exp : ∀ h : ℝ, expBounded B h = NormedSpace.exp ℂ ((h : ℂ) • B) := by
    intro h
    unfold expBounded
    rw [NormedSpace.exp_eq_tsum]
    congr 1; ext k; simp only [one_div]

  have h_deriv_smul : HasDerivAt (fun t : ℝ => (t : ℂ) • B) B 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
      have := ContinuousLinearMap.hasDerivAt ofRealCLM (x := 0)
      simp only [ofRealCLM_apply] at this
      exact this
    convert h1.smul_const B using 1
    simp only [one_smul]

  have h_exp_deriv : HasDerivAt (fun t : ℝ => NormedSpace.exp ℂ ((t : ℂ) • B)) B 0 := by
    have h1 : HasFDerivAt (fun T : H →L[ℂ] H => NormedSpace.exp ℂ T)
                          (1 : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (0 : H →L[ℂ] H) := hasFDerivAt_exp_zero
    have h1' : HasFDerivAt (fun T : H →L[ℂ] H => NormedSpace.exp ℂ T)
                           ((1 : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)).restrictScalars ℝ) (0 : H →L[ℂ] H) :=
      h1.restrictScalars ℝ
    have h2 := h_deriv_smul
    -- f(0) = 0 • B = 0
    have h_f0 : (0 : ℂ) • B = 0 := zero_smul ℂ B
    simp only at h_f0
    have h1'' : HasFDerivAt (fun T : H →L[ℂ] H => NormedSpace.exp ℂ T)
                            ((1 : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)).restrictScalars ℝ)
                            ((fun t : ℝ => (t : ℂ) • B) 0) := by
      simp only [ofReal_zero, zero_smul]
      exact h1'
    have h_comp := h1''.comp_hasDerivAt (0 : ℝ) h2
    -- h_comp : HasDerivAt (exp ∘ (t ↦ t • B)) (1.restrictScalars ℝ B) 0
    -- 1.restrictScalars ℝ B = B since 1 is identity
    convert h_comp using 1

  rw [hasDerivAt_iff_tendsto_slope] at h_exp_deriv

  apply h_exp_deriv.congr
  intro h
  simp_all only [ofReal_zero, zero_smul, NormedSpace.exp_zero, coe_smul]


/-- Derivative of the bounded exponential at any point. -/
lemma expBounded_hasDerivAt (B : H →L[ℂ] H) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => expBounded B t) (B.comp (expBounded B τ)) τ := by
  -- Use the group law: expBounded B t = (expBounded B τ).comp (expBounded B (t - τ))
  have h_eq : ∀ t, expBounded B t = (expBounded B τ).comp (expBounded B (t - τ)) := by
    intro t
    rw [← expBounded_add_smul]
    congr 1; ring

  -- Derivative of t ↦ expBounded B (t - τ) at t = τ is B
  have h_shift : HasDerivAt (fun t => expBounded B (t - τ)) B τ := by
    have h0 : HasDerivAt (fun t => expBounded B t) B (τ - τ) := by
      simp only [sub_self]
      exact expBounded_hasDerivAt_zero B
    exact h0.comp_sub_const τ τ

  -- At t = τ, expBounded B (t - τ) = expBounded B 0 = 1
  have h_val : expBounded B (τ - τ) = 1 := by simp only [sub_self, expBounded_at_zero']

  -- Post-composition with a fixed continuous linear map
  have h_post : HasDerivAt (fun t => (expBounded B τ).comp (expBounded B (t - τ)))
                           ((expBounded B τ).comp B) τ := by
    have h_clm : HasFDerivAt (fun T : H →L[ℂ] H => (expBounded B τ).comp T)
                             ((ContinuousLinearMap.compL ℂ H H H) (expBounded B τ))
                             (expBounded B (τ - τ)) :=
      ((ContinuousLinearMap.compL ℂ H H H) (expBounded B τ)).hasFDerivAt
    have h_clm' := h_clm.restrictScalars ℝ
    have h_comp := h_clm'.comp_hasDerivAt τ h_shift
    convert h_comp using 1

  -- Use commutativity: (expBounded B τ).comp B = B.comp (expBounded B τ)
  have h_comm : (expBounded B τ).comp B = B.comp (expBounded B τ) := by
    ext ψ
    simp only [ContinuousLinearMap.comp_apply]
    have := B_commute_expBounded B τ
    unfold Commute SemiconjBy at this
    exact congrFun (congrArg DFunLike.coe this.symm) ψ

  rw [h_comm] at h_post
  exact h_post.congr_of_eventuallyEq (Eventually.of_forall (fun t => (h_eq t)))


/-- The unitary group has derivative i·A at t=0 for domain elements. -/
lemma unitary_hasDerivAt_zero {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (φ : H) (hφ : φ ∈ gen.domain) :
    HasDerivAt (fun t => U_grp.U t φ) (I • gen.op ⟨φ, hφ⟩) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]

  have h_U0 : U_grp.U 0 φ = φ := by
    have := U_grp.identity
    simp only [this, ContinuousLinearMap.id_apply]

  have h_gen := gen.generator_formula ⟨φ, hφ⟩
  -- h_gen : Tendsto (fun t => (I * t)⁻¹ • (U(t)φ - φ)) (𝓝[≠] 0) (𝓝 (gen.op ⟨φ, hφ⟩))

  -- slope uses real smul: t⁻¹ • x, but h_gen uses complex smul: (I * t)⁻¹ • x
  -- Real smul equals complex smul via IsScalarTower: r • x = (r : ℂ) • x

  have h_slope_eq : ∀ t : ℝ, t ≠ 0 →
    slope (fun t => U_grp.U t φ) 0 t = (t : ℂ)⁻¹ • (U_grp.U t φ - φ) := by
    intro t ht
    simp only [slope, vsub_eq_sub, h_U0, sub_zero]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp only [map_inv₀, coe_algebraMap]

  -- From generator formula: (I * t)⁻¹ • (U(t)φ - φ) → A(φ)
  -- We want: t⁻¹ • (U(t)φ - φ) → I • A(φ)
  -- Since (I * t)⁻¹ = t⁻¹ * I⁻¹ = t⁻¹ * (-I), we have
  -- (I * t)⁻¹ • x = (-I) • (t⁻¹ • x)
  -- So t⁻¹ • x = (-I)⁻¹ • ((I * t)⁻¹ • x) = I • ((I * t)⁻¹ • x)

  have h_convert : ∀ t : ℝ, t ≠ 0 →
    (t : ℂ)⁻¹ • (U_grp.U t φ - φ) = I • (((I : ℂ) * (t : ℂ))⁻¹ • (U_grp.U t φ - φ)) := by
    intro t ht
    have h_inv : ((I : ℂ) * (t : ℂ))⁻¹ = (t : ℂ)⁻¹ * (-I) := by
      rw [mul_inv, inv_I]
      ring
    rw [h_inv, smul_smul]
    congr 1
    -- Goal: (t : ℂ)⁻¹ = I * ((t : ℂ)⁻¹ * -I)
    have : I * ((t : ℂ)⁻¹ * -I) = (t : ℂ)⁻¹ * (I * -I) := by ring
    rw [this]
    simp only [mul_neg, Complex.I_mul_I, neg_neg, mul_one]

  have h_scale : Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (U_grp.U t φ - φ))
                         (𝓝[≠] 0) (𝓝 (I • gen.op ⟨φ, hφ⟩)) := by
    have h_smul_tendsto := Tendsto.const_smul h_gen I
    apply Tendsto.congr' _ h_smul_tendsto
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (h_convert t ht).symm

  apply h_scale.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (h_slope_eq t ht).symm



/-- The unitary group has derivative i·A·U(s) at any point s for domain elements. -/
lemma unitary_hasDerivAt {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) ( _ /-hsa-/ : gen.IsSelfAdjoint)
    (s : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    HasDerivAt (fun t => U_grp.U t φ)
               (I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩) s := by
  -- U(s + h)φ = U(s)(U(h)φ)
  -- So d/dh[U(s+h)φ]|_{h=0} = U(s) · d/dh[U(h)φ]|_{h=0} = U(s)(i·Aφ) = i·U(s)(Aφ)
  -- By generator_commutes_unitary: U(s)(Aφ) = A(U(s)φ)

  have h_eq : ∀ t, U_grp.U t φ = U_grp.U s (U_grp.U (t - s) φ) := by
    intro t
    have := U_grp.group_law s (t - s)
    simp only [add_sub_cancel] at this
    calc U_grp.U t φ
        = (U_grp.U s).comp (U_grp.U (t - s)) φ := by rw [← this]
      _ = U_grp.U s (U_grp.U (t - s) φ) := rfl

  -- Derivative of t ↦ U(t-s)φ at t = s is i·Aφ
  have h_shift : HasDerivAt (fun t => U_grp.U (t - s) φ) (I • gen.op ⟨φ, hφ⟩) s := by
    have h0 : HasDerivAt (fun t => U_grp.U t φ) (I • gen.op ⟨φ, hφ⟩) (s - s) := by
      simp only [sub_self]
      exact unitary_hasDerivAt_zero gen φ hφ
    exact h0.comp_sub_const s s

  -- U(s) is a continuous linear map, so d/dt[U(s)(f(t))] = U(s)(f'(t))
  have h_comp : HasDerivAt (fun t => U_grp.U s (U_grp.U (t - s) φ))
                         (U_grp.U s (I • gen.op ⟨φ, hφ⟩)) s := by
    -- Restrict U_grp.U s to ℝ-linear map
    let L := (U_grp.U s).restrictScalars ℝ
    -- L and U_grp.U s have the same underlying function
    have h_eq : ∀ v, L v = U_grp.U s v := fun v => rfl
    -- L is a continuous ℝ-linear map, so it preserves HasDerivAt
    have h_L := L.hasFDerivAt.comp_hasDerivAt s h_shift
    -- h_L : HasDerivAt (L ∘ (fun t => U_grp.U (t - s) φ)) (L (I • gen.op ⟨φ, hφ⟩)) s
    convert h_L using 1

  -- Use generator_commutes_unitary: U(s)(Aφ) = A(U(s)φ)
  have h_comm := generator_commutes_unitary gen s φ hφ
  -- h_comm : gen.op ⟨U(s)φ, ...⟩ = U(s)(gen.op ⟨φ, hφ⟩)

  have h_val : U_grp.U s (I • gen.op ⟨φ, hφ⟩) = I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ := by
    rw [ContinuousLinearMap.map_smul, h_comm]

  rw [h_val] at h_comp
  exact h_comp.congr_of_eventuallyEq (Eventually.of_forall (fun t => (h_eq t)))



theorem duhamel_identity (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    U_grp.U t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ =
    ∫ s in (0)..t, duhamelIntegrand U_grp gen hsa n t φ hφ s := by
  set B := I • yosidaApproxSym gen hsa n

  -- Define the auxiliary function f(s) = exp((t-s)B)(U(s)φ)
  let f : ℝ → H := fun s => expBounded B (t - s) (U_grp.U s φ)

  -- f(t) = U(t)φ (since exp(0) = 1)
  have hf_t : f t = U_grp.U t φ := by
    simp_all only [sub_self, f, B]
    simp only [expBounded_at_zero', ContinuousLinearMap.one_apply]

  -- f(0) = exp(tB)φ (since U(0) = 1)
  have hf_0 : f 0 = expBounded B t φ := by
    simp_all only [sub_self, sub_zero, f, B]
    have h := U_grp.identity
    simp only [h, ContinuousLinearMap.id_apply]

  -- Derivative of exp((t-s)B) with respect to s
  have h_exp_deriv : ∀ s, HasDerivAt (fun s => expBounded B (t - s))
                                    (-(B.comp (expBounded B (t - s)))) s := by
    intro s
    have h := expBounded_hasDerivAt B (t - s)
    -- h : HasDerivAt (fun τ => expBounded B τ) (B.comp (expBounded B (t - s))) (t - s)
    have h1 : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
      convert (hasDerivAt_const s t).sub (hasDerivAt_id' s) using 1; ring
    have h_comp := h.scomp s h1
    -- h_comp : HasDerivAt (fun s => expBounded B (t - s)) ((-1) • B.comp (expBounded B (t - s))) s
    convert h_comp using 1
    simp only [neg_one_smul]

  -- Derivative of U(s)φ
  have h_U_deriv : ∀ s, HasDerivAt (fun s => U_grp.U s φ)
                         (I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩) s :=
    fun s => unitary_hasDerivAt gen hsa s φ hφ

  -- f has derivative = duhamelIntegrand at each s
  have h_deriv : ∀ s, HasDerivAt f (duhamelIntegrand U_grp gen hsa n t φ hφ s) s := by
    intro s
    -- Application of CLM to vector is bounded bilinear over ℝ
    have h_bil : IsBoundedBilinearMap ℝ (fun p : (H →L[ℂ] H) × H => p.1 p.2) := {
      add_left := fun T₁ T₂ v => by simp only [ContinuousLinearMap.add_apply]
      smul_left := fun c T v => by
        simp only [ContinuousLinearMap.smul_apply]
      add_right := fun T v₁ v₂ => T.map_add v₁ v₂
      smul_right := fun c T v => by
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), T.map_smul]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      bound := by
        use 1
        constructor
        · norm_num
        · intro T v
          simp only [one_mul]
          exact T.le_opNorm v
    }

    -- Derivative of the pair (expBounded B (t-s), U(s)φ)
    have h_pair : HasDerivAt (fun s => (expBounded B (t - s), U_grp.U s φ))
                            (-(B.comp (expBounded B (t - s))),
                              I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩) s :=
      (h_exp_deriv s).prodMk (h_U_deriv s)

    -- Compose bilinear with the pair
    have h_fderiv := h_bil.hasFDerivAt (expBounded B (t - s), U_grp.U s φ)
    have h_comp := h_fderiv.comp_hasDerivAt s h_pair

    -- The derivative formula for bilinear: b(x,y)' = b(x',y) + b(x,y')
    have h_deriv_val : h_bil.deriv (expBounded B (t - s), U_grp.U s φ)
                    (-(B.comp (expBounded B (t - s))),
                     I • gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩) =
                   duhamelIntegrand U_grp gen hsa n t φ hφ s := by
      simp only [IsBoundedBilinearMap.deriv_apply]

      unfold duhamelIntegrand

      set ψ := U_grp.U s φ
      set expB := expBounded B (t - s)
      set Aψ := gen.op ⟨ψ, gen.domain_invariant s φ hφ⟩
      set Aₙψ := yosidaApproxSym gen hsa n ψ

      -- Use commutativity: B ∘ exp(B) = exp(B) ∘ B
      have h_comm : B.comp expB = expB.comp B := by
        ext v
        simp only [ContinuousLinearMap.comp_apply]
        have := B_commute_expBounded B (t - s)
        unfold Commute SemiconjBy at this
        exact congrFun (congrArg DFunLike.coe this) v

      -- Simplify LHS
      calc expB (I • Aψ) + (-(B.comp expB)) ψ
          = expB (I • Aψ) - (B.comp expB) ψ := by simp only [ContinuousLinearMap.neg_apply]; exact Eq.symm (sub_eq_add_neg (expB (I • Aψ)) ((B.comp expB) ψ))
        _ = expB (I • Aψ) - (expB.comp B) ψ := by rw [h_comm]
        _ = expB (I • Aψ) - expB (B ψ) := by rfl
        _ = expB (I • Aψ - B ψ) := by rw [ContinuousLinearMap.map_sub]
        _ = expB (I • Aψ - I • Aₙψ) := by
            congr 1

    convert h_comp using 1
    exact id (Eq.symm h_deriv_val) -- exact h_deriv_val

  -- f is continuous (follows from continuity of components)
  have h_cont : Continuous f := by
    unfold f
    have h1 : Continuous (fun s => expBounded B (t - s)) := by
      have h_smul : Continuous (fun s : ℝ => ((t - s) : ℂ) • B) := by
        apply Continuous.smul
        · have : (fun s : ℝ => ((t - s) : ℂ)) = (fun s : ℝ => (t : ℂ) - (s : ℂ)) := by
            ext s; exact rfl
          rw [this]
          exact continuous_const.sub continuous_ofReal
        · exact continuous_const
      have h_exp : Continuous (NormedSpace.exp ℂ : (H →L[ℂ] H) → (H →L[ℂ] H)) :=
        NormedSpace.exp_continuous
      have h_comp := h_exp.comp h_smul
      convert h_comp using 1
      ext s v
      simp only [Function.comp_apply, expBounded, NormedSpace.exp_eq_tsum]
      congr 1
      ext k
      congr 1
      field_simp
      rw [ofReal_sub]
    have h2 : Continuous (fun s => U_grp.U s φ) := U_grp.strong_continuous φ
    exact h1.clm_apply h2

  -- The integrand is interval integrable
  have h_int : IntervalIntegrable (duhamelIntegrand U_grp gen hsa n t φ hφ) MeasureTheory.volume 0 t :=
    (duhamelIntegrand_continuous U_grp gen hsa n t φ hφ).intervalIntegrable 0 t

  -- Apply FTC
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
                  (fun s _ => h_deriv s) h_int

  -- h_ftc : ∫ = f t - f 0
  -- Substitute using hf_t and hf_0
  rw [hf_t, hf_0] at h_ftc
  -- Now h_ftc : ∫ = U(t)φ - exp(tB)φ

  exact h_ftc.symm



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


lemma expBounded_adjoint (B : H →L[ℂ] H) (t : ℝ) :
    ContinuousLinearMap.adjoint (expBounded B t) = expBounded (ContinuousLinearMap.adjoint B) t := by
  exact adjoint_expBounded B t


lemma expBounded_mem_unitary (B : H →L[ℂ] H) (hB : ContinuousLinearMap.adjoint B = -B) (t : ℝ) :
    expBounded B t ∈ unitary (H →L[ℂ] H) := by
  rw [unitary.mem_iff]
  constructor
  · -- star (exp B t) * exp B t = 1
    have h1 : star (expBounded B t) = expBounded (-B) t := by
      rw [ContinuousLinearMap.star_eq_adjoint, adjoint_expBounded, hB]
    rw [h1]
    -- Use expBounded_eq_exp to convert to NormedSpace.exp
    rw [expBounded_eq_exp, expBounded_eq_exp]
    -- exp((-t) • B) * exp(t • B) = exp(((-t) + t) • B) = exp(0) = 1
    have h_comm : Commute ((t : ℂ) • (-B)) ((t : ℂ) • B) := by
      unfold Commute SemiconjBy
      simp_all only [smul_neg, coe_smul, Algebra.mul_smul_comm, neg_mul, Algebra.smul_mul_assoc, mul_neg]
    have h2 := (@NormedSpace.exp_add_of_commute ℂ (H →L[ℂ] H) _ _ _ _ _ _ h_comm).symm
    simp only [smul_neg, neg_add_cancel, NormedSpace.exp_zero] at h2
    simp_all only [smul_neg, coe_smul, Commute.neg_left_iff, Commute.refl]
  · -- exp B t * star (exp B t) = 1
    have h1 : star (expBounded B t) = expBounded (-B) t := by
      rw [ContinuousLinearMap.star_eq_adjoint, adjoint_expBounded, hB]
    rw [h1]
    rw [expBounded_eq_exp, expBounded_eq_exp]
    have h_comm : Commute ((t : ℂ) • B) ((t : ℂ) • (-B)) := by
      unfold Commute SemiconjBy
      simp_all only [coe_smul, smul_neg, mul_neg, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, neg_mul]
    have h2 := (@NormedSpace.exp_add_of_commute ℂ (H →L[ℂ] H) _ _ _ _ _ _ h_comm).symm
    simp only [smul_neg, add_neg_cancel, NormedSpace.exp_zero] at h2
    simp_all only [smul_neg, coe_smul]


lemma smul_I_skewSelfAdjoint (A : H →L[ℂ] H) (hA : ContinuousLinearMap.adjoint A = A) :
    ContinuousLinearMap.adjoint (I • A) = -(I • A) := by
  have h := ContinuousLinearMap.adjoint.map_smulₛₗ I A
  rw [h, hA, starRingEnd_apply, star_def, conj_I]
  simp only [neg_smul]


lemma U_neg_eq_adjoint (U_grp : OneParameterUnitaryGroup (H := H)) (t : ℝ) :
    U_grp.U (-t) = ContinuousLinearMap.adjoint (U_grp.U t) := by
  ext φ
  apply ext_inner_left ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_right]
  -- Need: ⟪ψ, U(-t)φ⟫ = ⟪U(t)ψ, φ⟫
  have h_inv : U_grp.U (-t) (U_grp.U t ψ) = ψ := by
    have := U_grp.group_law (-t) t
    simp only [neg_add_cancel] at this
    rw [U_grp.identity] at this
    rw [← ContinuousLinearMap.comp_apply, ← this, ContinuousLinearMap.id_apply]
  -- Use unitary property with U(t)ψ instead of ψ
  have h := U_grp.unitary (-t) (U_grp.U t ψ) φ
  -- h : ⟪U(-t)(U(t)ψ), U(-t)φ⟫ = ⟪U(t)ψ, φ⟫
  rw [h_inv] at h
  -- h : ⟪ψ, U(-t)φ⟫ = ⟪U(t)ψ, φ⟫
  exact h


lemma U_norm_preserving (U_grp : OneParameterUnitaryGroup (H := H)) (t : ℝ) (φ : H) :
    ‖U_grp.U t φ‖ = ‖φ‖ := by
  have h := U_grp.unitary t φ φ
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), h]


lemma resolvent_unique {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (z : ℂ) (hz : z.im ≠ 0)
    (ψ : H) (hψ : ψ ∈ gen.domain)
    (h : gen.op ⟨ψ, hψ⟩ - z • ψ = 0) : ψ = 0 := by
  -- If Aψ = zψ with z.im ≠ 0, then ψ = 0
  have h_eq : gen.op ⟨ψ, hψ⟩ = z • ψ := by
    rw [sub_eq_zero] at h; exact h
  -- ⟪ψ, Aψ⟫ = z * ⟪ψ, ψ⟫
  have h1 : ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ = z * ⟪ψ, ψ⟫_ℂ := by
    rw [h_eq, inner_smul_right]
  -- By symmetry: ⟪Aψ, ψ⟫ = ⟪ψ, Aψ⟫
  have h2 : ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ = ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ :=
    gen.symmetric ⟨ψ, hψ⟩ ⟨ψ, hψ⟩
  -- Also ⟪Aψ, ψ⟫ = conj ⟪ψ, Aψ⟫ (inner product conjugate symmetry)
  have h3 : ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ = starRingEnd ℂ ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ :=
    (inner_conj_symm (gen.op ⟨ψ, hψ⟩) ψ).symm
  -- So ⟪ψ, Aψ⟫ = conj ⟪ψ, Aψ⟫, meaning ⟪ψ, Aψ⟫ is real
  have h4 : ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ = starRingEnd ℂ ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ := by
    rw [← h3, h2]
  -- z * ⟪ψ, ψ⟫ is real
  rw [h1] at h4
  -- ⟪ψ, ψ⟫ = ‖ψ‖² which is real and non-negative
  have h5 : ⟪ψ, ψ⟫_ℂ = (‖ψ‖ : ℂ)^2 := inner_self_eq_norm_sq_to_K ψ
  rw [h5] at h4
  -- z * ‖ψ‖² = conj(z * ‖ψ‖²) = conj(z) * ‖ψ‖²
  simp only [map_mul] at h4
  -- (z - conj z) * ‖ψ‖² = 0
  have h6 : (z - starRingEnd ℂ z) * (‖ψ‖ : ℂ)^2 = 0 := by
    rw [sub_mul, h4]
    simp_all only [ne_eq, sub_self, map_pow, conj_ofReal, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply,
      mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, ofReal_eq_zero, norm_eq_zero]
  -- z - conj z = 2i * im(z) ≠ 0
  have h7 : z - starRingEnd ℂ z ≠ 0 := by
    rw [sub_conj]
    intro h
    simp only [mul_eq_zero, ofReal_eq_zero, I_ne_zero, or_false] at h
    simp_all only [ne_eq, sub_self, map_pow, conj_ofReal, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply,
      mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, ofReal_eq_zero, norm_eq_zero,
      mul_eq_zero, or_self]
  -- So ‖ψ‖² = 0, hence ψ = 0
  have h8 : (‖ψ‖ : ℂ)^2 = 0 := by
    cases mul_eq_zero.mp h6 with
    | inl h => exact absurd h h7
    | inr h => exact h
  have h9 : ‖ψ‖ = 0 := by
    have : (‖ψ‖ : ℂ) = 0 := pow_eq_zero h8
    exact_mod_cast this
  exact norm_eq_zero.mp h9


-- HELPER 7
lemma resolvent_commutes_unitary {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) (φ : H) :
    Resolvent.resolvent gen z hz hsa (U_grp.U t φ) =
    U_grp.U t (Resolvent.resolvent gen z hz hsa φ) := by
  -- Let ψ = R(z)φ
  set ψ := Resolvent.resolvent gen z hz hsa φ
  -- ψ ∈ domain and Aψ - zψ = φ
  have hψ_spec := resolvent_spec gen hsa z hz φ
  have hψ_dom : ψ ∈ gen.domain := hψ_spec.1
  have hψ_eq : gen.op ⟨ψ, hψ_dom⟩ - z • ψ = φ := hψ_spec.2

  -- U(t)ψ ∈ domain
  have hUψ_dom : U_grp.U t ψ ∈ gen.domain := gen.domain_invariant t ψ hψ_dom

  -- A(U(t)ψ) - z(U(t)ψ) = U(t)φ
  have hUψ_eq : gen.op ⟨U_grp.U t ψ, hUψ_dom⟩ - z • (U_grp.U t ψ) = U_grp.U t φ := by
    rw [generator_commutes_unitary gen t ψ hψ_dom]
    rw [← ContinuousLinearMap.map_smul]
    rw [← ContinuousLinearMap.map_sub]
    congr 1

  -- R(z)(U(t)φ) also satisfies this equation
  set ψ' := Resolvent.resolvent gen z hz hsa (U_grp.U t φ)
  have hψ'_spec := resolvent_spec gen hsa z hz (U_grp.U t φ)
  have hψ'_dom : ψ' ∈ gen.domain := hψ'_spec.1
  have hψ'_eq : gen.op ⟨ψ', hψ'_dom⟩ - z • ψ' = U_grp.U t φ := hψ'_spec.2

  -- ψ' - U(t)ψ ∈ domain
  have h_diff_dom : ψ' - U_grp.U t ψ ∈ gen.domain := gen.domain.sub_mem hψ'_dom hUψ_dom

  -- By uniqueness: ψ' - U(t)ψ = 0
  have h_diff : ψ' - U_grp.U t ψ = 0 := by
    apply resolvent_unique gen z hz (ψ' - U_grp.U t ψ) h_diff_dom
    -- Need: A(ψ' - U(t)ψ) - z(ψ' - U(t)ψ) = 0
    have h1 : gen.op ⟨ψ' - U_grp.U t ψ, h_diff_dom⟩ =
              gen.op ⟨ψ', hψ'_dom⟩ - gen.op ⟨U_grp.U t ψ, hUψ_dom⟩ := by
      have := gen.op.map_sub ⟨ψ', hψ'_dom⟩ ⟨U_grp.U t ψ, hUψ_dom⟩
      convert this using 2
    rw [h1, smul_sub, sub_sub_sub_comm, hψ'_eq, hUψ_eq, sub_self]

  exact sub_eq_zero.mp h_diff

-- HELPER 8
lemma yosidaApproxSym_commutes_unitary {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (φ : H) :
    yosidaApproxSym gen hsa n (U_grp.U t φ) = U_grp.U t (yosidaApproxSym gen hsa n φ) := by
  unfold yosidaApproxSym
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]

  -- Need to show resolventAtIn and resolventAtNegIn commute with U(t)
  unfold resolventAtIn resolventAtNegIn
  rw [resolvent_commutes_unitary gen hsa _ _ t φ]
  rw [resolvent_commutes_unitary gen hsa _ _ t φ]
  simp only [neg_mul, smul_add, map_add, map_smul]

-- HELPER 9
lemma norm_gen_diff_constant {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (s : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    ‖gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s φ)‖ =
    ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖ := by
  rw [generator_commutes_unitary gen s φ hφ]
  rw [yosidaApproxSym_commutes_unitary gen hsa n s φ]
  rw [← ContinuousLinearMap.map_sub]
  exact U_norm_preserving U_grp s _


lemma duhamel_estimate
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    ‖U_grp.U t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ ≤
    |t| * ⨆ (s : Set.Icc 0 |t|), ‖gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s φ)‖ := by
  rw [duhamel_identity U_grp gen hsa n t φ hφ]

  set B := I • yosidaApproxSym gen hsa n
  set C := ⨆ (s : Set.Icc 0 |t|), ‖gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ -
                                   yosidaApproxSym gen hsa n (U_grp.U s φ)‖

  -- B is skew-self-adjoint
  have hB : ContinuousLinearMap.adjoint B = -B :=
    smul_I_skewSelfAdjoint (yosidaApproxSym gen hsa n) (yosidaApproxSym_selfAdjoint gen hsa n)

  -- expBounded B is unitary, hence isometric
  have h_isometric : ∀ τ v, ‖expBounded B τ v‖ = ‖v‖ := by
    intro τ v
    have h_unitary := expBounded_mem_unitary B hB τ
    exact unitary.norm_map ⟨expBounded B τ, h_unitary⟩ v

  -- Apply integral bound
  have h_bound := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := C)
                    (f := duhamelIntegrand U_grp gen hsa n t φ hφ)

  calc ‖∫ s in (0)..t, duhamelIntegrand U_grp gen hsa n t φ hφ s‖
      ≤ C * |t - 0| := h_bound ?_
    _ = C * |t| := by simp only [sub_zero]
    _ = |t| * C := mul_comm C |t|

  -- Need to prove: ∀ s ∈ uIoc 0 t, ‖duhamelIntegrand s‖ ≤ C
  intro s hs
  unfold duhamelIntegrand

  -- ‖exp(B)(t-s)(I • (A - Aₙ)(U(s)φ))‖ = ‖I • (A - Aₙ)(U(s)φ)‖ = ‖(A - Aₙ)(U(s)φ)‖
  rw [h_isometric]

  -- ‖I • w‖ = ‖w‖
  rw [← smul_sub, norm_smul, Complex.norm_I, one_mul]

  -- Need: ‖A(U(s)φ) - Aₙ(U(s)φ)‖ ≤ C where C is sup over [0, |t|]
  -- s ∈ uIoc 0 t means s is between 0 and t

  -- We have s ∈ uIoc 0 t
  -- Need to produce an element of Set.Icc 0 |t| to use le_ciSup_of_le

  -- First check if the range is bounded
  have h_bdd : BddAbove (Set.range (fun (s : Set.Icc 0 |t|) =>
    ‖gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s φ)‖)) := by
    -- The function is constant by norm_gen_diff_constant
    have h_const : ∀ s : Set.Icc 0 |t|,
        ‖gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s φ)‖ =
        ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖ := by
      intro s
      exact norm_gen_diff_constant gen hsa n s φ hφ
    use ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖
    intro x hx
    simp only [Set.mem_range] at hx
    obtain ⟨s, hs⟩ := hx
    rw [← hs, h_const]

  -- From s ∈ uIoc 0 t, extract bounds
  rw [Set.mem_uIoc] at hs
  cases hs with
  | inl h =>
    -- 0 < s ∧ s ≤ t, so t ≥ 0 and |t| = t
    have hs_pos : 0 ≤ s := le_of_lt h.1
    have hs_le : s ≤ |t| := by
      have h1 : 0 < s := h.1
      have h2 : s ≤ t := h.2
      have h3 : 0 ≤ t := le_trans (le_of_lt h1) h2
      rw [abs_of_nonneg h3]
      exact h2
    apply le_ciSup_of_le h_bdd ⟨s, hs_pos, hs_le⟩
    rfl
  | inr h =>
    -- t < s ≤ 0
    -- The norm is constant in s, so equals the value at s = 0
    rw [norm_gen_diff_constant gen hsa n s φ hφ]
    -- Now need ‖A(φ) - Aₙ(φ)‖ ≤ C where C is sup over [0, |t|]
    -- Use s = 0 ∈ [0, |t|]
    have h0_mem : (0 : ℝ) ∈ Set.Icc 0 |t| := by
      constructor
      · exact le_refl 0
      · exact abs_nonneg t
    have h_at_0 : ‖gen.op ⟨U_grp.U 0 φ, gen.domain_invariant 0 φ hφ⟩ -
                  yosidaApproxSym gen hsa n (U_grp.U 0 φ)‖ ≤ C := by
      apply le_ciSup_of_le h_bdd ⟨0, h0_mem⟩
      rfl
    -- U(0) = id
    simp only [U_grp.identity, ContinuousLinearMap.id_apply] at h_at_0
    exact h_at_0


end DuhamelFormula


theorem yosidaApproxSym_uniform_on_orbit
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => ⨆ s ∈ Set.Icc 0 |t|,
              ‖gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s φ)‖)
            atTop (𝓝 0) := by
  -- The norm is constant in s by norm_gen_diff_constant
  have h_const : ∀ n : ℕ+, ∀ s ∈ Set.Icc 0 |t|,
      ‖gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s φ)‖ =
      ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖ :=
    fun n s _ => norm_gen_diff_constant gen hsa n s φ hφ

  have h_nonempty : Nonempty (Set.Icc (0 : ℝ) |t|) := ⟨⟨0, le_refl 0, abs_nonneg t⟩⟩
  have h_set_nonempty : (Set.Icc (0 : ℝ) |t|).Nonempty := ⟨0, le_refl 0, abs_nonneg t⟩

  -- The biSup of a constant equals the constant
  have h_sup_eq : ∀ n : ℕ+,
      (⨆ s ∈ Set.Icc 0 |t|, ‖gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ -
                            yosidaApproxSym gen hsa n (U_grp.U s φ)‖) =
      ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖ := by
    intro n
    apply le_antisymm
    · -- Upper bound: sup ≤ constant
      apply ciSup_le; intro s
      by_cases hs : s ∈ Set.Icc 0 |t|
      · rw [ciSup_pos hs, h_const n s hs]
      · simp only [Set.mem_Icc, not_and_or, not_le] at hs
        cases hs with
        | inl h =>
          simp_all only [Set.mem_Icc, and_imp, nonempty_subtype, Set.nonempty_Icc, abs_nonneg, isEmpty_Prop, not_and,
            not_le, IsEmpty.forall_iff, Real.iSup_of_isEmpty, norm_nonneg]
        | inr h =>
          simp_all only [Set.mem_Icc, and_imp, nonempty_subtype, Set.nonempty_Icc, abs_nonneg, isEmpty_Prop, not_and,
            not_le, implies_true, Real.iSup_of_isEmpty, norm_nonneg]
    · -- Lower bound: constant ≤ sup
      have h0 : (0 : ℝ) ∈ Set.Icc 0 |t| := ⟨le_refl 0, abs_nonneg t⟩
      calc ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖
          = ‖gen.op ⟨U_grp.U 0 φ, gen.domain_invariant 0 φ hφ⟩ -
             yosidaApproxSym gen hsa n (U_grp.U 0 φ)‖ := by
              simp only [U_grp.identity, ContinuousLinearMap.id_apply]
        _ ≤ ⨆ s ∈ Set.Icc 0 |t|, ‖gen.op ⟨U_grp.U s φ, gen.domain_invariant s φ hφ⟩ -
             yosidaApproxSym gen hsa n (U_grp.U s φ)‖ := by
              apply le_ciSup_of_le _ 0
              · rw [ciSup_pos h0]
              · use ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖
                intro x hx
                simp only [Set.mem_range] at hx
                obtain ⟨s, hs⟩ := hx
                rw [← hs]
                by_cases h : s ∈ Set.Icc 0 |t|
                · rw [ciSup_pos h, h_const n s h]
                · simp only [Set.mem_Icc, not_and_or, not_le] at h
                  cases h with
                  | inl h =>
                    subst hs
                    simp_all only [Set.mem_Icc, and_imp, nonempty_subtype, Set.nonempty_Icc, abs_nonneg, le_refl,
                      and_self, isEmpty_Prop, not_and, not_le, IsEmpty.forall_iff, Real.iSup_of_isEmpty, norm_nonneg]
                  | inr h =>
                    subst hs
                    simp_all only [Set.mem_Icc, and_imp, nonempty_subtype, Set.nonempty_Icc, abs_nonneg, le_refl,
                      and_self, isEmpty_Prop, not_and, not_le, implies_true, Real.iSup_of_isEmpty, norm_nonneg]

  simp_rw [h_sup_eq]

  -- yosidaApproxSym gen hsa n φ → gen.op ⟨φ, hφ⟩
  have h_tendsto := yosidaApproxSym_tendsto_on_domain gen hsa h_dense φ hφ

  -- ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖ → 0
  have h_norm : Tendsto (fun n : ℕ+ => ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖) atTop (𝓝 0) := by
    have h : Tendsto (fun n => gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := gen.op ⟨φ, hφ⟩)).sub h_tendsto
      simp only [sub_self] at this
      convert this using 1
    exact tendsto_norm_zero.comp h

  exact h_norm

end UniformConvergence


lemma yosidaApproxSym_uniform_convergence_on_orbit
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => ⨆ (s : Set.Icc 0 |t|),
             ‖gen.op ⟨U_grp.U s.val φ, gen.domain_invariant s.val φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s.val φ)‖)
            atTop (𝓝 0) := by
  -- The norm is constant in s by norm_gen_diff_constant
  have h_const : ∀ n : ℕ+, ∀ s : Set.Icc 0 |t|,
      ‖gen.op ⟨U_grp.U s.val φ, gen.domain_invariant s.val φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s.val φ)‖ =
      ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖ :=
    fun n s => norm_gen_diff_constant gen hsa n s.val φ hφ

  have h_nonempty : Nonempty (Set.Icc (0 : ℝ) |t|) := ⟨⟨0, le_refl 0, abs_nonneg t⟩⟩

  -- The sup of a constant is the constant
  have h_sup_eq : ∀ n : ℕ+,
      (⨆ (s : Set.Icc 0 |t|), ‖gen.op ⟨U_grp.U s.val φ, gen.domain_invariant s.val φ hφ⟩ -
                              yosidaApproxSym gen hsa n (U_grp.U s.val φ)‖) =
      ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖ := by
    intro n
    simp_rw [h_const n]
    exact ciSup_const

  simp_rw [h_sup_eq]

  have h_tendsto := yosidaApproxSym_tendsto_on_domain gen hsa h_dense φ hφ

  have h_norm : Tendsto (fun n : ℕ+ => ‖gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ‖) atTop (𝓝 0) := by
    have h : Tendsto (fun n => gen.op ⟨φ, hφ⟩ - yosidaApproxSym gen hsa n φ) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := gen.op ⟨φ, hφ⟩)).sub h_tendsto
      simp only [sub_self] at this
      convert this using 1
    exact tendsto_norm_zero.comp h

  exact h_norm


lemma expBounded_yosidaApproxSym_tendsto_unitary
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ)
            atTop (𝓝 (U_grp.U t φ)) := by

  by_cases ht : t = 0
  · simp only [ht]
    have h_exp_zero : ∀ n : ℕ+, expBounded (I • yosidaApproxSym gen hsa n) 0 φ = φ :=
      fun n => expBounded_at_zero _ φ
    have h_U_zero : U_grp.U 0 φ = φ := unitary_group_at_zero φ
    simp_rw [h_exp_zero, h_U_zero]
    exact tendsto_const_nhds

  · apply Metric.tendsto_atTop.mpr
    intro ε hε

    have h_unif := yosidaApproxSym_uniform_convergence_on_orbit gen hsa h_dense t φ hφ
    rw [Metric.tendsto_atTop] at h_unif

    have ht_pos : 0 < |t| + 1 := by linarith [abs_nonneg t]
    have hεt : ε / (|t| + 1) > 0 := div_pos hε ht_pos
    obtain ⟨N, hN⟩ := h_unif (ε / (|t| + 1)) hεt

    use N
    intro n hn
    rw [dist_eq_norm]

    calc ‖expBounded (I • yosidaApproxSym gen hsa n) t φ - U_grp.U t φ‖
        = ‖U_grp.U t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ := norm_sub_rev _ _
      _ ≤ |t| * ⨆ (s : Set.Icc 0 |t|), ‖gen.op ⟨U_grp.U s.val φ, gen.domain_invariant s.val φ hφ⟩ - yosidaApproxSym gen hsa n (U_grp.U s.val φ)‖ :=
          duhamel_estimate gen hsa n t φ hφ
      _ < |t| * (ε / (|t| + 1)) := by
          apply mul_lt_mul_of_pos_left _ (abs_pos.mpr ht)
          specialize hN n hn
          simp only [dist_zero_right, Real.norm_eq_abs] at hN
          rw [abs_of_nonneg] at hN
          · exact hN
          · apply Real.iSup_nonneg
            intro s
            exact norm_nonneg _
      _ < (|t| + 1) * (ε / (|t| + 1)) := by
          apply mul_lt_mul_of_pos_right _ hεt
          linarith
      _ = ε := mul_div_cancel₀ ε (ne_of_gt ht_pos)



theorem expBounded_yosidaApproxSym_cauchy
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ : H) :
    CauchySeq (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t ψ) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε

  have hε3 : ε / 3 > 0 := by linarith

  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp
    (h_dense.closure_eq ▸ Set.mem_univ ψ) (ε / 3) hε3
  rw [dist_eq_norm] at hφ_close

  have h_cauchy_φ : CauchySeq (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ) := by
    apply Filter.Tendsto.cauchySeq
    exact expBounded_yosidaApproxSym_tendsto_unitary gen hsa h_dense t φ hφ_mem

  rw [Metric.cauchySeq_iff] at h_cauchy_φ
  obtain ⟨N, hN⟩ := h_cauchy_φ (ε / 3) hε3

  use N
  intro m hm n hn
  rw [dist_eq_norm]

  calc ‖expBounded (I • yosidaApproxSym gen hsa m) t ψ -
        expBounded (I • yosidaApproxSym gen hsa n) t ψ‖
      = ‖(expBounded (I • yosidaApproxSym gen hsa m) t ψ - expBounded (I • yosidaApproxSym gen hsa m) t φ) +
         (expBounded (I • yosidaApproxSym gen hsa m) t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ) +
         (expBounded (I • yosidaApproxSym gen hsa n) t φ - expBounded (I • yosidaApproxSym gen hsa n) t ψ)‖ := by
          congr 1; abel
    _ ≤ ‖expBounded (I • yosidaApproxSym gen hsa m) t ψ - expBounded (I • yosidaApproxSym gen hsa m) t φ‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa m) t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa n) t φ - expBounded (I • yosidaApproxSym gen hsa n) t ψ‖ := by
          apply le_trans (norm_add_le _ _)
          apply add_le_add_right
          exact norm_add_le _ _
    _ = ‖expBounded (I • yosidaApproxSym gen hsa m) t (ψ - φ)‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa m) t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa n) t (φ - ψ)‖ := by
          congr 1
          · congr 1
            · rw [← ContinuousLinearMap.map_sub]
          · rw [← ContinuousLinearMap.map_sub]
    _ = ‖ψ - φ‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa m) t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ +
        ‖φ - ψ‖ := by
          congr 1
          · congr 1
            · exact expBounded_yosidaApproxSym_isometry gen hsa m t (ψ - φ)
          · exact expBounded_yosidaApproxSym_isometry gen hsa n t (φ - ψ)
    _ < ε / 3 + ε / 3 + ε / 3 := by
          apply add_lt_add
          apply add_lt_add
          · exact hφ_close
          · rw [← dist_eq_norm]; exact hN m hm n hn
          · rw [norm_sub_rev]; exact hφ_close
    _ = ε := by ring



noncomputable def exponential
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H)) (t : ℝ) : H →L[ℂ] H where
  toFun ψ := limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ)
  map_add' := fun ψ₁ ψ₂ => by
    -- Each T_n is linear
    have h_add : ∀ n : ℕ+, expBounded (I • yosidaApproxSym gen hsa n) t (ψ₁ + ψ₂) =
        expBounded (I • yosidaApproxSym gen hsa n) t ψ₁ + expBounded (I • yosidaApproxSym gen hsa n) t ψ₂ :=
      fun n => map_add _ _ _
    -- Get convergence for each
    have h1 := cauchySeq_tendsto_of_complete (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ₁)
    have h2 := cauchySeq_tendsto_of_complete (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ₂)
    have h12 := cauchySeq_tendsto_of_complete (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t (ψ₁ + ψ₂))
    obtain ⟨L1, hL1⟩ := h1
    obtain ⟨L2, hL2⟩ := h2
    obtain ⟨L12, hL12⟩ := h12
    -- limUnder equals the limit
    have hLim1 : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ₁) = L1 :=
      tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L1, hL1⟩) hL1
    have hLim2 : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ₂) = L2 :=
      tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L2, hL2⟩) hL2
    have hLim12 : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t (ψ₁ + ψ₂)) = L12 :=
      tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L12, hL12⟩) hL12
    -- The sum of limits equals the limit of sums
    have hSum : Tendsto (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ₁ +
                                  expBounded (I • yosidaApproxSym gen hsa n) t ψ₂) atTop (𝓝 (L1 + L2)) :=
      hL1.add hL2
    -- But that's the same as T_n (ψ₁ + ψ₂)
    simp_rw [← h_add] at hSum
    have : L12 = L1 + L2 := tendsto_nhds_unique hL12 hSum
    rw [hLim12, hLim1, hLim2, this]
  map_smul' := fun c ψ => by
    have h_smul : ∀ n : ℕ+, expBounded (I • yosidaApproxSym gen hsa n) t (c • ψ) =
        c • expBounded (I • yosidaApproxSym gen hsa n) t ψ :=
      fun n => map_smul _ _ _
    have h1 := cauchySeq_tendsto_of_complete (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ)
    have hc := cauchySeq_tendsto_of_complete (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t (c • ψ))
    obtain ⟨L, hL⟩ := h1
    obtain ⟨Lc, hLc⟩ := hc
    have hLim : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ) = L :=
      tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L, hL⟩) hL
    have hLimC : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t (c • ψ)) = Lc :=
      tendsto_nhds_unique (tendsto_nhds_limUnder ⟨Lc, hLc⟩) hLc
    have hSmul : Tendsto (fun n => c • expBounded (I • yosidaApproxSym gen hsa n) t ψ) atTop (𝓝 (c • L)) :=
      tendsto_const_nhds.smul hL
    simp_rw [← h_smul] at hSmul
    have : Lc = c • L := tendsto_nhds_unique hLc hSmul
    rw [hLimC, hLim, this, RingHom.id_apply]
  cont := by
    apply continuous_of_linear_of_bound (𝕜 := ℂ)
    -- Additivity
    · intro ψ₁ ψ₂
      have h_add : ∀ n : ℕ+, expBounded (I • yosidaApproxSym gen hsa n) t (ψ₁ + ψ₂) =
          expBounded (I • yosidaApproxSym gen hsa n) t ψ₁ + expBounded (I • yosidaApproxSym gen hsa n) t ψ₂ :=
        fun n => map_add _ _ _
      have h1 := cauchySeq_tendsto_of_complete (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ₁)
      have h2 := cauchySeq_tendsto_of_complete (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ₂)
      have h12 := cauchySeq_tendsto_of_complete (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t (ψ₁ + ψ₂))
      obtain ⟨L1, hL1⟩ := h1
      obtain ⟨L2, hL2⟩ := h2
      obtain ⟨L12, hL12⟩ := h12
      have hLim1 : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ₁) = L1 :=
        tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L1, hL1⟩) hL1
      have hLim2 : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ₂) = L2 :=
        tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L2, hL2⟩) hL2
      have hLim12 : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t (ψ₁ + ψ₂)) = L12 :=
        tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L12, hL12⟩) hL12
      have hSum : Tendsto (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ₁ +
                                    expBounded (I • yosidaApproxSym gen hsa n) t ψ₂) atTop (𝓝 (L1 + L2)) :=
        hL1.add hL2
      simp_rw [← h_add] at hSum
      have : L12 = L1 + L2 := tendsto_nhds_unique hL12 hSum
      rw [hLim12, hLim1, hLim2, this]
    -- Scalar multiplication
    · intro c ψ
      have h_smul : ∀ n : ℕ+, expBounded (I • yosidaApproxSym gen hsa n) t (c • ψ) =
          c • expBounded (I • yosidaApproxSym gen hsa n) t ψ :=
        fun n => map_smul _ _ _
      have h1 := cauchySeq_tendsto_of_complete (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ)
      have hc := cauchySeq_tendsto_of_complete (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t (c • ψ))
      obtain ⟨L, hL⟩ := h1
      obtain ⟨Lc, hLc⟩ := hc
      have hLim : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ) = L :=
        tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L, hL⟩) hL
      have hLimC : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t (c • ψ)) = Lc :=
        tendsto_nhds_unique (tendsto_nhds_limUnder ⟨Lc, hLc⟩) hLc
      have hSmul : Tendsto (fun n => c • expBounded (I • yosidaApproxSym gen hsa n) t ψ) atTop (𝓝 (c • L)) :=
        tendsto_const_nhds.smul hL
      simp_rw [← h_smul] at hSmul
      have : Lc = c • L := tendsto_nhds_unique hLc hSmul
      rw [hLimC, hLim, this]
    -- Bound: ‖f ψ‖ ≤ 1 * ‖ψ‖
    · intro ψ
      have h := cauchySeq_tendsto_of_complete (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ)
      obtain ⟨L, hL⟩ := h
      have hLim : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ) = L :=
        tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L, hL⟩) hL
      rw [hLim, one_mul]
      -- Each T_n is unitary hence isometric
      have h_norm : ∀ n : ℕ+, ‖expBounded (I • yosidaApproxSym gen hsa n) t ψ‖ = ‖ψ‖ := fun n => by
        have h_sa : ContinuousLinearMap.adjoint (yosidaApproxSym gen hsa n) = yosidaApproxSym gen hsa n :=
          yosidaApproxSym_selfAdjoint gen hsa n
        have h_skew : ContinuousLinearMap.adjoint (I • yosidaApproxSym gen hsa n) = -(I • yosidaApproxSym gen hsa n) :=
          smul_I_skewSelfAdjoint (A := yosidaApproxSym gen hsa n) h_sa
        have h_unitary := expBounded_mem_unitary (I • yosidaApproxSym gen hsa n) h_skew t
        exact unitary.norm_map ⟨_, h_unitary⟩ ψ
      -- Norm is continuous, so ‖L‖ = lim ‖T_n ψ‖ = ‖ψ‖
      have h_tendsto_norm : Tendsto (fun n => ‖expBounded (I • yosidaApproxSym gen hsa n) t ψ‖) atTop (𝓝 ‖L‖) :=
        tendsto_norm.comp hL
      simp_rw [h_norm] at h_tendsto_norm
      subst hLim
      simp_all only [tendsto_const_nhds_iff, le_refl]





lemma exponential_tendsto
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ : H) :
    Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t ψ)
            atTop (𝓝 (exponential gen hsa h_dense t ψ)) := by
  -- The pointwise sequence is Cauchy
  have h_cauchy := expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ
  -- In a complete space, Cauchy implies convergent
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete h_cauchy
  -- exponential is defined as limUnder, which equals L
  have h_eq : exponential gen hsa h_dense t ψ = L :=
    tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L, hL⟩) hL
  rw [h_eq]
  exact hL


theorem exponential_unitary
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ φ : H) :
    ⟪exponential gen hsa h_dense t ψ, exponential gen hsa h_dense t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
  have h_conv_ψ : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t ψ)
                          atTop (𝓝 (exponential gen hsa h_dense t ψ)) :=
    exponential_tendsto gen hsa h_dense t ψ

  have h_conv_φ : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ)
                          atTop (𝓝 (exponential gen hsa h_dense t φ)) :=
    exponential_tendsto gen hsa h_dense t φ

  have h_approx_unitary : ∀ n : ℕ+,
      ⟪expBounded (I • yosidaApproxSym gen hsa n) t ψ,
       expBounded (I • yosidaApproxSym gen hsa n) t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ :=
    fun n => expBounded_yosidaApproxSym_unitary gen hsa n t ψ φ

  have h_inner_cont : Tendsto (fun n : ℕ+ =>
      ⟪expBounded (I • yosidaApproxSym gen hsa n) t ψ,
       expBounded (I • yosidaApproxSym gen hsa n) t φ⟫_ℂ)
      atTop (𝓝 ⟪exponential gen hsa h_dense t ψ, exponential gen hsa h_dense t φ⟫_ℂ) :=
    Filter.Tendsto.inner h_conv_ψ h_conv_φ

  have h_const : Tendsto (fun n : ℕ+ => ⟪ψ, φ⟫_ℂ) atTop (𝓝 ⟪ψ, φ⟫_ℂ) := tendsto_const_nhds

  exact tendsto_nhds_unique h_inner_cont (h_const.congr (fun n => (h_approx_unitary n).symm))



theorem exponential_group_law
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (s t : ℝ) (ψ : H) :
    exponential gen hsa h_dense (s + t) ψ = exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ) := by
  have h_approx_group : ∀ n : ℕ+,
      expBounded (I • yosidaApproxSym gen hsa n) (s + t) ψ =
      expBounded (I • yosidaApproxSym gen hsa n) s (expBounded (I • yosidaApproxSym gen hsa n) t ψ) := by
    intro n
    rw [expBounded_group_law]
    exact rfl

  have h_conv_lhs : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) (s + t) ψ)
                            atTop (𝓝 (exponential gen hsa h_dense (s + t) ψ)) :=
    exponential_tendsto gen hsa h_dense (s + t) ψ

  have h_conv_t : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t ψ)
                          atTop (𝓝 (exponential gen hsa h_dense t ψ)) :=
    exponential_tendsto gen hsa h_dense t ψ

  have h_conv_rhs : Tendsto (fun n : ℕ+ =>
      expBounded (I • yosidaApproxSym gen hsa n) s (expBounded (I • yosidaApproxSym gen hsa n) t ψ))
      atTop (𝓝 (exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ))) := by
    have h_inner := exponential_tendsto gen hsa h_dense t ψ
    have h_outer : ∀ χ : H, Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) s χ)
                                    atTop (𝓝 (exponential gen hsa h_dense s χ)) :=
      fun χ => exponential_tendsto gen hsa h_dense s χ

    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hε2 : ε / 2 > 0 := by linarith

    rw [Metric.tendsto_atTop] at h_inner
    obtain ⟨N₁, hN₁⟩ := h_inner (ε / 2) hε2

    have h_outer_limit := h_outer (exponential gen hsa h_dense t ψ)
    rw [Metric.tendsto_atTop] at h_outer_limit
    obtain ⟨N₂, hN₂⟩ := h_outer_limit (ε / 2) hε2

    use max N₁ N₂
    intro n hn
    rw [dist_eq_norm]

    calc ‖expBounded (I • yosidaApproxSym gen hsa n) s (expBounded (I • yosidaApproxSym gen hsa n) t ψ) -
          exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ)‖
        = ‖(expBounded (I • yosidaApproxSym gen hsa n) s (expBounded (I • yosidaApproxSym gen hsa n) t ψ) -
           expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa h_dense t ψ)) +
          (expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa h_dense t ψ) -
           exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ))‖ := by congr 1; abel
      _ ≤ ‖expBounded (I • yosidaApproxSym gen hsa n) s (expBounded (I • yosidaApproxSym gen hsa n) t ψ) -
           expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa h_dense t ψ)‖ +
          ‖expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa h_dense t ψ) -
           exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ)‖ := norm_add_le _ _
      _ = ‖expBounded (I • yosidaApproxSym gen hsa n) s (expBounded (I • yosidaApproxSym gen hsa n) t ψ - exponential gen hsa h_dense t ψ)‖ +
          ‖expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa h_dense t ψ) -
           exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ)‖ := by rw [← map_sub]
      _ = ‖expBounded (I • yosidaApproxSym gen hsa n) t ψ - exponential gen hsa h_dense t ψ‖ +
          ‖expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa h_dense t ψ) -
           exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ)‖ := by
            rw [expBounded_yosidaApproxSym_isometry gen hsa n s _]
      _ < ε / 2 + ε / 2 := by
            apply add_lt_add
            · rw [← dist_eq_norm]; exact hN₁ n (le_of_max_le_left hn)
            · rw [← dist_eq_norm]; exact hN₂ n (le_of_max_le_right hn)
      _ = ε := by ring

  exact tendsto_nhds_unique h_conv_lhs (h_conv_rhs.congr (fun n => (h_approx_group n).symm))



theorem exponential_identity
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) :
    exponential gen hsa h_dense 0 ψ = ψ := by
  have h_approx_zero : ∀ n : ℕ+, expBounded (I • yosidaApproxSym gen hsa n) 0 ψ = ψ :=
    fun n => expBounded_at_zero _ ψ

  have h_const : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) 0 ψ)
                         atTop (𝓝 ψ) := by
    simp_rw [h_approx_zero]
    exact tendsto_const_nhds

  have h_conv : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) 0 ψ)
                        atTop (𝓝 (exponential gen hsa h_dense 0 ψ)) :=
    exponential_tendsto gen hsa h_dense 0 ψ

  exact tendsto_nhds_unique h_conv h_const


theorem exponential_strong_continuous
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) :
    Continuous (fun t : ℝ => exponential gen hsa h_dense t ψ) := by
  have h_exp_eq_U : ∀ (φ : H), φ ∈ gen.domain → ∀ t : ℝ, exponential gen hsa h_dense t φ = U_grp.U t φ := by
    intro φ hφ t
    have h_tendsto := expBounded_yosidaApproxSym_tendsto_unitary gen hsa h_dense t φ hφ
    have h_conv : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ)
                          atTop (𝓝 (exponential gen hsa h_dense t φ)) :=
      exponential_tendsto gen hsa h_dense t φ
    exact tendsto_nhds_unique h_conv h_tendsto

  have h_cont_domain : ∀ (φ : H), φ ∈ gen.domain →
      Continuous (fun t : ℝ => exponential gen hsa h_dense t φ) := by
    intro φ hφ
    have h_eq : (fun t => exponential gen hsa h_dense t φ) = (fun t => U_grp.U t φ) := by
      ext t
      exact h_exp_eq_U φ hφ t
    rw [h_eq]
    exact U_grp.strong_continuous φ

  have h_isometry : ∀ t : ℝ, ∀ (χ : H), ‖exponential gen hsa h_dense t χ‖ = ‖χ‖ := by
    intro t χ
    have h_inner := exponential_unitary gen hsa h_dense t χ χ
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h_inner
    have h_sq : ‖exponential gen hsa h_dense t χ‖^2 = ‖χ‖^2 := by
      have h_eq : (‖exponential gen hsa h_dense t χ‖ : ℂ)^2 = (‖χ‖ : ℂ)^2 := by
        exact h_inner
      exact_mod_cast h_eq
    rw [← Real.sqrt_sq (norm_nonneg (exponential gen hsa h_dense t χ)),
        ← Real.sqrt_sq (norm_nonneg χ), h_sq]

  rw [Metric.continuous_iff]
  intro t ε hε

  have hε3 : ε / 3 > 0 := by linarith

  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp
    (h_dense.closure_eq ▸ Set.mem_univ ψ) (ε / 3) hε3
  rw [dist_eq_norm] at hφ_close

  have h_cont_φ := h_cont_domain φ hφ_mem
  rw [Metric.continuous_iff] at h_cont_φ
  obtain ⟨δ, hδ_pos, hδ⟩ := h_cont_φ t (ε / 3) hε3

  use δ, hδ_pos
  intro s hs
  rw [dist_eq_norm]

  calc ‖exponential gen hsa h_dense s ψ - exponential gen hsa h_dense t ψ‖
      = ‖(exponential gen hsa h_dense s ψ - exponential gen hsa h_dense s φ) +
         (exponential gen hsa h_dense s φ - exponential gen hsa h_dense t φ) +
         (exponential gen hsa h_dense t φ - exponential gen hsa h_dense t ψ)‖ := by abel_nf
    _ ≤ ‖exponential gen hsa h_dense s ψ - exponential gen hsa h_dense s φ‖ +
        ‖exponential gen hsa h_dense s φ - exponential gen hsa h_dense t φ‖ +
        ‖exponential gen hsa h_dense t φ - exponential gen hsa h_dense t ψ‖ := by
          apply le_trans (norm_add_le _ _)
          apply add_le_add_right
          exact norm_add_le _ _
    _ = ‖exponential gen hsa h_dense s (ψ - φ)‖ +
        ‖exponential gen hsa h_dense s φ - exponential gen hsa h_dense t φ‖ +
        ‖exponential gen hsa h_dense t (φ - ψ)‖ := by
          rw [← map_sub (exponential gen hsa h_dense s), ← map_sub (exponential gen hsa h_dense t)]
    _ = ‖ψ - φ‖ + ‖exponential gen hsa h_dense s φ - exponential gen hsa h_dense t φ‖ + ‖φ - ψ‖ := by
          rw [h_isometry s (ψ - φ), h_isometry t (φ - ψ)]
    _ < ε / 3 + ε / 3 + ε / 3 := by
          apply add_lt_add
          apply add_lt_add
          · exact hφ_close
          · rw [← dist_eq_norm]; exact hδ s hs
          · rw [norm_sub_rev]; exact hφ_close
    _ = ε := by ring



theorem exponential_generator_eq
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • (exponential gen hsa h_dense t φ - φ))
            (𝓝[≠] 0) (𝓝 (I • gen.op ⟨φ, hφ⟩)) := by
  have h_exp_eq_U : ∀ t : ℝ, exponential gen hsa h_dense t φ = U_grp.U t φ := by
    intro t
    have h_tendsto := expBounded_yosidaApproxSym_tendsto_unitary gen hsa h_dense t φ hφ
    have h_conv : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ)
                          atTop (𝓝 (exponential gen hsa h_dense t φ)) :=
      exponential_tendsto gen hsa h_dense t φ
    exact tendsto_nhds_unique h_conv h_tendsto

  have h_eq_seq : ∀ t : ℝ, (t⁻¹ : ℂ) • (exponential gen hsa h_dense t φ - φ) =
                          (t⁻¹ : ℂ) • (U_grp.U t φ - φ) := by
    intro t
    rw [h_exp_eq_U t]

  have h_gen_formula := gen.generator_formula ⟨φ, hφ⟩

  have h_scalar : ∀ t : ℝ, t ≠ 0 → (t⁻¹ : ℂ) = I * (I * (t : ℂ))⁻¹ := by
    intro t ht
    field_simp

  have h_transform : ∀ t : ℝ, t ≠ 0 →
      (t⁻¹ : ℂ) • (U_grp.U t φ - φ) = I • ((I * (t : ℂ))⁻¹ • (U_grp.U t φ - φ)) := by
    intro t ht
    rw [← smul_assoc, h_scalar t ht]
    exact rfl

  refine Tendsto.congr' ?_ (Filter.Tendsto.const_smul h_gen_formula I)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [h_eq_seq t, h_transform t ht]



theorem exponential_derivative_on_domain
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ : H) (hψ : ψ ∈ gen.domain) :
    HasDerivAt (fun s : ℝ => exponential gen hsa h_dense s ψ)
               (I • gen.op ⟨U_grp.U t ψ, gen.domain_invariant t ψ hψ⟩)
               t := by
  have h_exp_eq_U : ∀ s : ℝ, exponential gen hsa h_dense s ψ = U_grp.U s ψ := by
    intro s
    have h_tendsto := expBounded_yosidaApproxSym_tendsto_unitary gen hsa h_dense s ψ hψ
    have h_conv : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) s ψ)
                          atTop (𝓝 (exponential gen hsa h_dense s ψ)) :=
      exponential_tendsto gen hsa h_dense s ψ
    exact tendsto_nhds_unique h_conv h_tendsto

  have h_fun_eq : (fun s : ℝ => exponential gen hsa h_dense s ψ) = (fun s : ℝ => U_grp.U s ψ) := by
    ext s
    exact h_exp_eq_U s

  rw [h_fun_eq]

  have hUtψ : U_grp.U t ψ ∈ gen.domain := gen.domain_invariant t ψ hψ

  rw [hasDerivAt_iff_tendsto_slope]

  have h_diff : ∀ s : ℝ, U_grp.U s ψ - U_grp.U t ψ = U_grp.U t (U_grp.U (s - t) ψ - ψ) := by
    intro s
    have h1 : U_grp.U s ψ = U_grp.U (t + (s - t)) ψ := by ring_nf
    have h2 : U_grp.U (t + (s - t)) ψ = U_grp.U t (U_grp.U (s - t) ψ) := by
      rw [U_grp.group_law]; rfl
    calc U_grp.U s ψ - U_grp.U t ψ
        = U_grp.U t (U_grp.U (s - t) ψ) - U_grp.U t ψ := by rw [h1, h2]
      _ = U_grp.U t (U_grp.U (s - t) ψ - ψ) := by rw [ContinuousLinearMap.map_sub]

  have h_slope : ∀ s : ℝ, s ≠ t → slope (fun s => U_grp.U s ψ) t s =
      U_grp.U t ((s - t)⁻¹ • (U_grp.U (s - t) ψ - ψ)) := by
    intro s hs
    simp only [slope, vsub_eq_sub, h_diff s]
    exact
      Eq.symm
        (ContinuousLinearMap.map_smul_of_tower (U_grp.U t) (s - t)⁻¹ ((U_grp.U (s - t)) ψ - ψ))

  have h_gen := gen.generator_formula ⟨ψ, hψ⟩

  have h_convert : ∀ h : ℝ, h ≠ 0 → (h⁻¹ : ℂ) • (U_grp.U h ψ - ψ) =
      I • ((I * (h : ℂ))⁻¹ • (U_grp.U h ψ - ψ)) := by
    intro h hh
    rw [← smul_assoc]
    congr 1
    rw [smul_eq_mul, mul_inv_rev, Complex.inv_I, mul_neg, mul_comm ((↑h)⁻¹) I,
        ← neg_mul, ← mul_assoc]
    simp

  have h_lim : Tendsto (fun s : ℝ => ((s - t)⁻¹ : ℂ) • (U_grp.U (s - t) ψ - ψ))
                       (𝓝[≠] t) (𝓝 (I • gen.op ⟨ψ, hψ⟩)) := by
    have h_comp : Tendsto (fun s : ℝ => s - t) (𝓝[≠] t) (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 (t - t)) :=
          tendsto_id.sub tendsto_const_nhds
        simp only [sub_self] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero]
        exact hs
    have h_inner := h_gen.comp h_comp
    have h_smul := h_inner.const_smul I
    refine h_smul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [← ofReal_sub]
    exact (h_convert (s - t) (sub_ne_zero.mpr hs)).symm

  have h_final : Tendsto (slope (fun s => U_grp.U s ψ) t) (𝓝[≠] t) (𝓝 (I • gen.op ⟨U_grp.U t ψ, hUtψ⟩)) := by
    have h_Ut_cont : Continuous (U_grp.U t) := (U_grp.U t).continuous
    have h_composed := h_Ut_cont.continuousAt.tendsto.comp h_lim
    have h_comm : U_grp.U t (I • gen.op ⟨ψ, hψ⟩) = I • gen.op ⟨U_grp.U t ψ, hUtψ⟩ := by
      rw [ContinuousLinearMap.map_smul, generator_commutes_unitary gen t ψ hψ]
    rw [h_comm] at h_composed
    refine h_composed.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Function.comp_apply]
    convert (h_slope s hs).symm using 2
    rw [← Complex.ofReal_sub]
    rw [← h_exp_eq_U]
    norm_cast

  exact h_final


end QuantumMechanics.Yosida
