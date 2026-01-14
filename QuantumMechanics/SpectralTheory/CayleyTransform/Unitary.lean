/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
/-!
# Unitary Operators on Hilbert Spaces

This file develops basic theory of unitary operators, including their characterization
as inner product preserving bijections and their spectral properties.

## Main definitions

* `Unitary`: Predicate for an operator satisfying `U* U = U U* = 1`
* `ContinuousLinearMap.IsNormal`: Predicate for a normal operator (`T* T = T T*`)

## Main statements

* `Unitary.inner_map_map`: Unitary operators preserve inner products
* `Unitary.norm_map`: Unitary operators preserve norms
* `unitary_not_isUnit_approx_eigenvalue`: Non-invertibility implies approximate eigenvalues
-/

namespace QuantumMechanics.Cayley

open InnerProductSpace Complex Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded operator is unitary if it satisfies `U* U = U U* = 1`. -/
def Unitary (U : H →L[ℂ] H) : Prop :=
  U.adjoint * U = 1 ∧ U * U.adjoint = 1

/-- Unitary operators preserve inner products. -/
lemma Unitary.inner_map_map {U : H →L[ℂ] H} (hU : Unitary U) (x y : H) :
    ⟪U x, U y⟫_ℂ = ⟪x, y⟫_ℂ := by
  calc ⟪U x, U y⟫_ℂ
      = ⟪U.adjoint (U x), y⟫_ℂ := by rw [ContinuousLinearMap.adjoint_inner_left]
    _ = ⟪(U.adjoint * U) x, y⟫_ℂ := rfl
    _ = ⟪x, y⟫_ℂ := by rw [hU.1]; simp

/-- Unitary operators preserve norms. -/
lemma Unitary.norm_map {U : H →L[ℂ] H} (hU : Unitary U) (x : H) : ‖U x‖ = ‖x‖ := by
  have h := hU.inner_map_map x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h_sq : ‖U x‖^2 = ‖x‖^2 := by exact_mod_cast h
  nlinarith [norm_nonneg (U x), norm_nonneg x, sq_nonneg (‖U x‖ - ‖x‖)]

/-- Unitary operators are injective. -/
lemma Unitary.injective {U : H →L[ℂ] H} (hU : Unitary U) : Function.Injective U := by
  intro x y hxy
  have : ‖U x - U y‖ = 0 := by simp [hxy]
  rw [← map_sub, hU.norm_map] at this
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Unitary operators are surjective. -/
lemma Unitary.surjective {U : H →L[ℂ] H} (hU : Unitary U) : Function.Surjective U := by
  intro y
  use U.adjoint y
  have := congr_arg (· y) hU.2
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
  exact this

/-- Unitary operators are invertible. -/
lemma Unitary.isUnit {U : H →L[ℂ] H} (hU : Unitary U) : IsUnit U :=
  ⟨⟨U, U.adjoint, hU.2, hU.1⟩, rfl⟩

/-- A bounded operator is normal if it commutes with its adjoint. -/
def ContinuousLinearMap.IsNormal (T : H →L[ℂ] H) : Prop :=
  T.adjoint.comp T = T.comp T.adjoint

/-- `U - w` is normal when `U` is unitary. -/
lemma unitary_sub_scalar_isNormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] E) (hU : U.adjoint * U = 1 ∧ U * U.adjoint = 1) (w : ℂ) :
    (U - w • 1).adjoint * (U - w • 1) = (U - w • 1) * (U - w • 1).adjoint := by
  have h_adj : (U - w • 1).adjoint = U.adjoint - (starRingEnd ℂ w) • 1 := by
    ext x
    apply ext_inner_right ℂ
    intro y
    simp only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.sub_apply,
               ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
               inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    simp_all only [RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [h_adj]
  ext x
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
             ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  have h1 : U.adjoint (U x) = x := by
    have := congr_arg (· x) hU.1
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    exact this
  have h2 : U (U.adjoint x) = x := by
    have := congr_arg (· x) hU.2
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    exact this
  simp only [map_sub, map_smul, h1, h2]
  module

/-- Variant of `unitary_sub_scalar_isNormal` using the `Unitary` predicate. -/
lemma unitary_sub_scalar_isNormal' {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ) :
    (U - w • 1).adjoint * (U - w • 1) = (U - w • 1) * (U - w • 1).adjoint :=
  unitary_sub_scalar_isNormal U hU w

/-! ### General operator lemmas -/

/-- A subspace with trivial orthogonal complement is dense. -/
lemma dense_range_of_orthogonal_trivial {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : F →L[ℂ] F)
    (h : ∀ y, (∀ x, ⟪T x, y⟫_ℂ = 0) → y = 0) :
    Dense (Set.range T) := by
  have h_orth : (LinearMap.range T.toLinearMap)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    apply h y
    intro x
    rw [Submodule.mem_orthogonal'] at hy
    simp_all only [LinearMap.mem_range, ContinuousLinearMap.coe_coe,
                   forall_exists_index, forall_apply_eq_imp_iff]
    exact inner_eq_zero_symm.mp (hy x)
  have h_double_orth : (LinearMap.range T.toLinearMap)ᗮᗮ = ⊤ := by
    rw [h_orth]
    exact Submodule.bot_orthogonal_eq_top
  have h_closure_top : (LinearMap.range T.toLinearMap).topologicalClosure = ⊤ := by
    rw [h_double_orth.symm]
    rw [@Submodule.orthogonal_orthogonal_eq_closure]
  rw [dense_iff_closure_eq]
  have : closure (Set.range T) = ↑(LinearMap.range T.toLinearMap).topologicalClosure := by
    rw [Submodule.topologicalClosure_coe]
    rfl
  rw [this, h_closure_top]
  rfl

/-- A continuous linear map with closed dense range is surjective. -/
lemma surjective_of_isClosed_range_of_dense {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F)
    (hClosed : IsClosed (Set.range T))
    (hDense : Dense (Set.range T)) :
    Function.Surjective T := by
  intro y
  have h_closure : closure (Set.range T) = Set.range T := hClosed.closure_eq
  have h_univ : closure (Set.range T) = Set.univ := hDense.closure_eq
  rw [h_closure] at h_univ
  have hy : y ∈ Set.range T := by rw [h_univ]; trivial
  exact hy


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- An invertible operator is bounded below. -/
lemma isUnit_bounded_below [Nontrivial H] {T : H →L[ℂ] H} (hT : IsUnit T) :
    ∃ c > 0, ∀ φ, ‖T φ‖ ≥ c * ‖φ‖ := by
  obtain ⟨⟨T, T_inv, hT_left, hT_right⟩, rfl⟩ := hT
  have hT_inv_ne : T_inv ≠ 0 := by
    intro h
    have h_one_eq : (1 : H →L[ℂ] H) = 0 := by
      calc (1 : H →L[ℂ] H) = T_inv * T := hT_right.symm
        _ = 0 * T := by rw [h]
        _ = 0 := zero_mul T
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have : x = 0 := by simpa using congr_arg (· x) h_one_eq
    exact hx this
  have hT_inv_norm_pos : ‖T_inv‖ > 0 := norm_pos_iff.mpr hT_inv_ne
  use ‖T_inv‖⁻¹, inv_pos.mpr hT_inv_norm_pos
  intro φ
  have h_eq : T_inv (T φ) = φ := by
    have := congr_arg (· φ) hT_right
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    exact this
  have h_bound : ‖φ‖ ≤ ‖T_inv‖ * ‖T φ‖ := by
    calc ‖φ‖ = ‖T_inv (T φ)‖ := by rw [h_eq]
      _ ≤ ‖T_inv‖ * ‖T φ‖ := ContinuousLinearMap.le_opNorm T_inv (T φ)
  exact (inv_mul_le_iff₀ hT_inv_norm_pos).mpr h_bound

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A normal operator bounded below is surjective. -/
lemma normal_bounded_below_surjective {T : H →L[ℂ] H}
    (hT : T.adjoint.comp T = T.comp T.adjoint)
    (c : ℝ) (hc_pos : c > 0) (hc_bound : ∀ φ, ‖T φ‖ ≥ c * ‖φ‖) :
    Function.Surjective T := by
  have h_range_dense : Dense (Set.range T) := by
    apply dense_range_of_orthogonal_trivial
    intro y hy
    have hT_adj_y : T.adjoint y = 0 := by
      apply ext_inner_left ℂ
      intro x
      rw [inner_zero_right, ContinuousLinearMap.adjoint_inner_right]
      exact hy x
    have h_norm_eq : ‖T.adjoint y‖ = ‖T y‖ := by
      have h1 : ⟪T.adjoint (T y), y⟫_ℂ = ⟪T (T.adjoint y), y⟫_ℂ := by
        calc ⟪T.adjoint (T y), y⟫_ℂ
            = ⟪(T.adjoint.comp T) y, y⟫_ℂ := rfl
          _ = ⟪(T.comp T.adjoint) y, y⟫_ℂ := by rw [hT]
          _ = ⟪T (T.adjoint y), y⟫_ℂ := rfl
      have h2 : ‖T.adjoint y‖^2 = (⟪T (T.adjoint y), y⟫_ℂ).re := by
        have h := ContinuousLinearMap.adjoint_inner_right T (T.adjoint y) y
        have h_inner : (⟪T.adjoint y, T.adjoint y⟫_ℂ).re = ‖T.adjoint y‖^2 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
          simp only [coe_algebraMap]
          rw [← ofReal_pow]
          exact Complex.ofReal_re _
        linarith [h_inner, congrArg Complex.re h]
      have h3 : ‖T y‖^2 = (⟪T.adjoint (T y), y⟫_ℂ).re := by
        have h := ContinuousLinearMap.adjoint_inner_left T (T y) y
        have h_inner : (⟪T y, T y⟫_ℂ).re = ‖T y‖^2 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
          simp only [coe_algebraMap]
          rw [← ofReal_pow]
          exact Complex.ofReal_re _
        have h_adj : ⟪T.adjoint (T y), y⟫_ℂ = ⟪T y, T y⟫_ℂ := by
          rw [ContinuousLinearMap.adjoint_inner_left]
        rw [h_adj]
        exact h_inner.symm
      have h_sq : ‖T.adjoint y‖^2 = ‖T y‖^2 := by rw [h2, h3, h1]
      nlinarith [norm_nonneg (T.adjoint y), norm_nonneg (T y),
                 sq_nonneg (‖T.adjoint y‖ - ‖T y‖)]
    rw [hT_adj_y, norm_zero] at h_norm_eq
    have h_Ty_zero : ‖T y‖ = 0 := by rw [← h_norm_eq]
    have h := hc_bound y
    rw [h_Ty_zero] at h
    have hy_norm_zero : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
    exact norm_eq_zero.mp hy_norm_zero
  have h_range_closed : IsClosed (Set.range T) := by
    rw [← isSeqClosed_iff_isClosed]
    intro xseq x hxseq hx_lim
    choose yseq hyseq using hxseq
    have h_cauchy : CauchySeq yseq := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      have hx_cauchy := hx_lim.cauchySeq
      rw [Metric.cauchySeq_iff'] at hx_cauchy
      obtain ⟨N, hN⟩ := hx_cauchy (c * ε) (by positivity)
      use N
      intro n hn
      have h_bound := hc_bound (yseq n - yseq N)
      rw [map_sub] at h_bound
      have h_xdist : ‖xseq n - xseq N‖ < c * ε := by
        rw [← dist_eq_norm]
        exact hN n hn
      have h_ydist : c * ‖yseq n - yseq N‖ ≤ ‖T (yseq n) - T (yseq N)‖ := h_bound
      rw [hyseq n, hyseq N] at h_ydist
      calc dist (yseq n) (yseq N)
          = ‖yseq n - yseq N‖ := dist_eq_norm _ _
        _ ≤ ‖xseq n - xseq N‖ / c := by
            have : c * ‖yseq n - yseq N‖ ≤ ‖xseq n - xseq N‖ := h_ydist
            exact (le_div_iff₀' hc_pos).mpr h_ydist
        _ < (c * ε) / c := by apply div_lt_div_of_pos_right h_xdist hc_pos
        _ = ε := by field_simp
    obtain ⟨y', hy'_lim⟩ := cauchySeq_tendsto_of_complete h_cauchy
    have hTy' : T y' = x := by
      have hT_cont := T.continuous.tendsto y'
      have hTyseq_lim : Tendsto (fun n => T (yseq n)) atTop (𝓝 (T y')) := hT_cont.comp hy'_lim
      have hTyseq_eq : ∀ n, T (yseq n) = xseq n := hyseq
      simp_rw [hTyseq_eq] at hTyseq_lim
      exact tendsto_nhds_unique hTyseq_lim hx_lim
    exact ⟨y', hTy'⟩
  exact surjective_of_isClosed_range_of_dense T h_range_closed h_range_dense

/-- A normal operator bounded below is invertible. -/
lemma normal_bounded_below_isUnit [Nontrivial H] {T : H →L[ℂ] H}
    (hT : T.adjoint * T = T * T.adjoint)
    (c : ℝ) (hc_pos : c > 0) (hc_bound : ∀ φ, ‖T φ‖ ≥ c * ‖φ‖) :
    IsUnit T := by
  have h_inj : Function.Injective T := by
    intro x y hxy
    have : ‖T (x - y)‖ = 0 := by simp [hxy]
    have h := hc_bound (x - y)
    rw [this] at h
    have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  have h_surj := normal_bounded_below_surjective hT c hc_pos hc_bound
  have h_ker : LinearMap.ker T = ⊥ := LinearMap.ker_eq_bot.mpr h_inj
  have h_range : LinearMap.range T = ⊤ := LinearMap.range_eq_top.mpr h_surj
  let e := ContinuousLinearEquiv.ofBijective T h_ker h_range
  exact ⟨⟨T, e.symm.toContinuousLinearMap,
         by ext x;
            simp only [ContinuousLinearMap.coe_mul, ContinuousLinearEquiv.coe_coe,
              Function.comp_apply, ContinuousLinearMap.one_apply]
            exact ContinuousLinearEquiv.ofBijective_apply_symm_apply T h_ker h_range x,
         by ext x;
            simp only [ContinuousLinearMap.coe_mul, ContinuousLinearEquiv.coe_coe,
              Function.comp_apply, ContinuousLinearMap.one_apply]
            exact ContinuousLinearEquiv.ofBijective_symm_apply_apply T h_ker h_range x⟩,
            rfl⟩

/-- If `U - w` is not invertible for unitary `U`, then `w` is an approximate eigenvalue. -/
lemma unitary_not_isUnit_approx_eigenvalue [Nontrivial H] {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ)
    (h_not : ¬IsUnit (U - w • ContinuousLinearMap.id ℂ H)) :
    ∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧ ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ < ε := by
  by_contra h_neg
  push_neg at h_neg
  obtain ⟨ε, hε_pos, hε_bound⟩ := h_neg
  have h_bounded_below : ∀ φ, ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ ≥ ε * ‖φ‖ := by
    intro φ
    by_cases hφ : φ = 0
    · simp [hφ]
    · have hφ_norm_pos : ‖φ‖ > 0 := norm_pos_iff.mpr hφ
      have h_unit := hε_bound (‖φ‖⁻¹ • φ) (by rw [norm_smul, norm_inv, norm_norm]; field_simp)
      calc ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖
          = ‖φ‖ * (‖φ‖⁻¹ * ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖) := by field_simp
        _ = ‖φ‖ * ‖‖φ‖⁻¹ • (U - w • ContinuousLinearMap.id ℂ H) φ‖ := by
            congr 1; rw [norm_smul, norm_inv, norm_norm]
        _ = ‖φ‖ * ‖(U - w • ContinuousLinearMap.id ℂ H) (‖φ‖⁻¹ • φ)‖ := by
            congr 1; simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_smul',
              ContinuousLinearMap.coe_id', Pi.sub_apply, Pi.smul_apply, id_eq,
              ContinuousLinearMap.map_smul_of_tower]
        _ ≥ ‖φ‖ * ε := mul_le_mul_of_nonneg_left h_unit (norm_nonneg φ)
        _ = ε * ‖φ‖ := mul_comm _ _
  have h_normal := unitary_sub_scalar_isNormal' hU w
  have h_isUnit := normal_bounded_below_isUnit h_normal ε hε_pos h_bounded_below
  exact h_not h_isUnit

/-- Converse: if `w` is not an approximate eigenvalue, then `U - w` is invertible. -/
lemma unitary_not_approx_eigenvalue_isUnit [Nontrivial H] {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ)
    (h_not : ¬∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧ ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ < ε) :
    IsUnit (U - w • ContinuousLinearMap.id ℂ H) := by
  push_neg at h_not
  obtain ⟨ε, hε_pos, hε_bound⟩ := h_not
  have h_bounded_below : ∀ φ, ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ ≥ ε * ‖φ‖ := by
    intro φ
    by_cases hφ : φ = 0
    · simp [hφ]
    · have hφ_norm_pos : ‖φ‖ > 0 := norm_pos_iff.mpr hφ
      have h_unit := hε_bound (‖φ‖⁻¹ • φ) (by rw [norm_smul, norm_inv, norm_norm]; field_simp)
      calc ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖
          = ‖φ‖ * (‖φ‖⁻¹ * ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖) := by field_simp
        _ = ‖φ‖ * ‖‖φ‖⁻¹ • (U - w • ContinuousLinearMap.id ℂ H) φ‖ := by
            congr 1; rw [norm_smul, norm_inv, norm_norm]
        _ = ‖φ‖ * ‖(U - w • ContinuousLinearMap.id ℂ H) (‖φ‖⁻¹ • φ)‖ := by
            congr 1; simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_smul',
              ContinuousLinearMap.coe_id', Pi.sub_apply, Pi.smul_apply, id_eq,
              ContinuousLinearMap.map_smul_of_tower]
        _ ≥ ‖φ‖ * ε := mul_le_mul_of_nonneg_left h_unit (norm_nonneg φ)
        _ = ε * ‖φ‖ := mul_comm _ _
  have h_normal := unitary_sub_scalar_isNormal' hU w
  exact normal_bounded_below_isUnit h_normal ε hε_pos h_bounded_below

end QuantumMechanics.Cayley
