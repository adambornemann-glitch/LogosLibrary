/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner.Limits
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Generator Domain and Self-Adjointness

This file constructs the generator of a strongly continuous one-parameter unitary
group and proves it is self-adjoint.

## Main definitions

* `generatorDomain`: the submodule of vectors where the generator limit exists
* `generatorOp`: the generator as a linear map on its domain
* `generatorOfUnitaryGroup`: the complete `Generator` structure
* `averagedVector`: time-averaged vectors used to prove domain density

## Main results

* `generatorDomain_dense`: the generator domain is dense in `H`
* `range_plus_i_eq_top`: `ran(A + iI) = H`
* `range_minus_i_eq_top`: `ran(A - iI) = H`
* `generatorOfUnitaryGroup_isSelfAdjoint`: the generator is self-adjoint

## Implementation notes

Self-adjointness is proved using the criterion: `A` is self-adjoint iff `A` is
symmetric and `ran(A ± iI) = H`. This avoids dealing with the adjoint of an
unbounded operator directly.

Domain density uses averaged vectors: `h⁻¹ ∫₀ʰ U(t)φ dt → φ` as `h → 0`,
and these averaged vectors lie in the domain.

## Tags

generator, self-adjoint, domain, Stone's theorem
-/

namespace QuantumMechanics.Bochner

open MeasureTheory Measure Filter Topology Complex QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option linter.unusedSectionVars false

section GeneratorConstruction

open Classical
open InnerProductSpace
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The domain of the generator: vectors where the limit `lim_{h→0} (U(h)ψ - ψ)/(ih)` exists. -/
noncomputable def generatorDomain : Submodule ℂ H where
  carrier := {ψ : H | ∃ (η : H), Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ - ψ))
                                         (𝓝[≠] 0) (𝓝 η)}
  add_mem' := by
    intro ψ₁ ψ₂ ⟨η₁, hη₁⟩ ⟨η₂, hη₂⟩
    refine ⟨η₁ + η₂, ?_⟩
    have h_add : ∀ h : ℝ, ((I * h)⁻¹ : ℂ) • (U_grp.U h (ψ₁ + ψ₂) - (ψ₁ + ψ₂)) =
                         ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₁ - ψ₁) +
                         ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₂ - ψ₂) := by
      intro h
      rw [map_add]
      ring_nf
      rw [← smul_add]
      congr 1
      abel
    simp_rw [h_add]
    exact hη₁.add hη₂
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp only [map_zero, sub_zero, smul_zero]
    exact tendsto_const_nhds
  smul_mem' := by
    intro c ψ ⟨η, hη⟩
    refine ⟨c • η, ?_⟩
    have h_smul : ∀ h : ℝ, ((I * h)⁻¹ : ℂ) • (U_grp.U h (c • ψ) - c • ψ) =
                          c • (((I * h)⁻¹ : ℂ) • (U_grp.U h ψ - ψ)) := by
      intro h
      rw [ContinuousLinearMap.map_smul, smul_sub, smul_comm]
      rw [smul_comm ((I * (h : ℂ))⁻¹) c ψ, ← smul_sub, ← smul_sub]
    simp_rw [h_smul]
    exact hη.const_smul c

noncomputable def generatorLimitValue (ψ : H)
    (hψ : ψ ∈ generatorDomain U_grp) : H :=
  Classical.choose hψ

lemma generatorLimitValue_spec (ψ : H) (hψ : ψ ∈ generatorDomain U_grp) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ - ψ))
            (𝓝[≠] 0) (𝓝 (generatorLimitValue U_grp ψ hψ)) :=
  Classical.choose_spec hψ

/-- The generator of a unitary group as a linear map on its domain. -/
noncomputable def generatorOp : (generatorDomain U_grp) →ₗ[ℂ] H where
  toFun := fun ⟨ψ, hψ⟩ => generatorLimitValue U_grp ψ hψ
  map_add' := by
    intro ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩
    have hψ_sum : ψ₁ + ψ₂ ∈ generatorDomain U_grp := (generatorDomain U_grp).add_mem hψ₁ hψ₂
    simp
    have h₁ := generatorLimitValue_spec U_grp ψ₁ hψ₁
    have h₂ := generatorLimitValue_spec U_grp ψ₂ hψ₂
    have h_sum := generatorLimitValue_spec U_grp (ψ₁ + ψ₂) hψ_sum
    have h_add_lim : Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (ψ₁ + ψ₂) - (ψ₁ + ψ₂)))
                             (𝓝[≠] 0)
                             (𝓝 (generatorLimitValue U_grp ψ₁ hψ₁ + generatorLimitValue U_grp ψ₂ hψ₂)) := by
      have h_eq : ∀ h : ℝ, ((I * h)⁻¹ : ℂ) • (U_grp.U h (ψ₁ + ψ₂) - (ψ₁ + ψ₂)) =
                          ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₁ - ψ₁) +
                          ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₂ - ψ₂) := by
        intro h
        rw [map_add, ← smul_add]
        congr 1
        abel
      simp_rw [h_eq]
      exact h₁.add h₂
    exact tendsto_nhds_unique h_sum h_add_lim
  map_smul' := by
    intro c ⟨ψ, hψ⟩
    have hcψ : c • ψ ∈ generatorDomain U_grp := (generatorDomain U_grp).smul_mem c hψ
    simp only [RingHom.id_apply]
    have h := generatorLimitValue_spec U_grp ψ hψ
    have hc := generatorLimitValue_spec U_grp (c • ψ) hcψ
    have h_smul_lim : Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (c • ψ) - c • ψ))
                              (𝓝[≠] 0)
                              (𝓝 (c • generatorLimitValue U_grp ψ hψ)) := by
      have h_eq : ∀ h : ℝ, ((I * h)⁻¹ : ℂ) • (U_grp.U h (c • ψ) - c • ψ) =
                          c • (((I * h)⁻¹ : ℂ) • (U_grp.U h ψ - ψ)) := by
        intro h
        rw [ContinuousLinearMap.map_smul, smul_sub, smul_comm]
        rw [smul_comm ((I * (h : ℂ))⁻¹) c ψ, ← smul_sub]
        congr 1
        rw [← smul_sub]
      simp_rw [h_eq]
      exact h.const_smul c
    exact tendsto_nhds_unique hc h_smul_lim

theorem generator_formula_holds (ψ : generatorDomain U_grp) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (ψ : H) - (ψ : H)))
            (𝓝[≠] 0)
            (𝓝 (generatorOp U_grp ψ)) := by
  exact generatorLimitValue_spec U_grp ψ.val ψ.property

theorem generatorDomain_invariant (t : ℝ) (ψ : H) (hψ : ψ ∈ generatorDomain U_grp) :
    U_grp.U t ψ ∈ generatorDomain U_grp := by
  obtain ⟨η, hη⟩ := hψ
  refine ⟨U_grp.U t η, ?_⟩
  have h_eq : ∀ h : ℝ, ((I * h)⁻¹ : ℂ) • (U_grp.U h (U_grp.U t ψ) - U_grp.U t ψ) =
                       U_grp.U t (((I * h)⁻¹ : ℂ) • (U_grp.U h ψ - ψ)) := by
    intro h
    have h_comm : U_grp.U h (U_grp.U t ψ) = U_grp.U t (U_grp.U h ψ) := by
      calc U_grp.U h (U_grp.U t ψ)
          = (U_grp.U h).comp (U_grp.U t) ψ := rfl
        _ = U_grp.U (h + t) ψ := by rw [← U_grp.group_law]
        _ = U_grp.U (t + h) ψ := by rw [add_comm]
        _ = (U_grp.U t).comp (U_grp.U h) ψ := by rw [U_grp.group_law]
        _ = U_grp.U t (U_grp.U h ψ) := rfl
    rw [h_comm, ← ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul]
  simp_rw [h_eq]
  exact (U_grp.U t).continuous.tendsto _ |>.comp hη

theorem generator_symmetric (ψ₁ ψ₂ : generatorDomain U_grp) :
    ⟪generatorOp U_grp ψ₁, (ψ₂ : H)⟫_ℂ = ⟪(ψ₁ : H), generatorOp U_grp ψ₂⟫_ℂ := by
  have h₁ := generatorLimitValue_spec U_grp ψ₁.val ψ₁.property
  have h₂ := generatorLimitValue_spec U_grp ψ₂.val ψ₂.property
  have h_lhs : Tendsto (fun h : ℝ => ⟪((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₁ - ψ₁), (ψ₂ : H)⟫_ℂ)
                       (𝓝[≠] 0) (𝓝 ⟪generatorOp U_grp ψ₁, (ψ₂ : H)⟫_ℂ) :=
    Tendsto.inner h₁ tendsto_const_nhds
  have h_rhs : Tendsto (fun h : ℝ => ⟪(ψ₁ : H), ((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₂ - ψ₂)⟫_ℂ)
                       (𝓝[≠] 0) (𝓝 ⟪(ψ₁ : H), generatorOp U_grp ψ₂⟫_ℂ) :=
    Tendsto.inner tendsto_const_nhds h₂
  have h_eq : ∀ h : ℝ, h ≠ 0 →
      ⟪((I * h)⁻¹ : ℂ) • (U_grp.U h ψ₁ - ψ₁), (ψ₂ : H)⟫_ℂ =
      ⟪(ψ₁ : H), ((I * (-h))⁻¹ : ℂ) • (U_grp.U (-h) ψ₂ - ψ₂)⟫_ℂ := by
    intro h hh
    rw [inner_smul_left]
    have h_unitary : ⟪U_grp.U h ψ₁, (ψ₂ : H)⟫_ℂ = ⟪(ψ₁ : H), U_grp.U (-h) ψ₂⟫_ℂ := by
      calc ⟪U_grp.U h ψ₁, (ψ₂ : H)⟫_ℂ
          = ⟪U_grp.U (-h) (U_grp.U h ψ₁), U_grp.U (-h) ψ₂⟫_ℂ := by rw [U_grp.unitary (-h)]
        _ = ⟪(U_grp.U (-h)).comp (U_grp.U h) ψ₁, U_grp.U (-h) ψ₂⟫_ℂ := rfl
        _ = ⟪U_grp.U ((-h) + h) ψ₁, U_grp.U (-h) ψ₂⟫_ℂ := by rw [← U_grp.group_law]
        _ = ⟪U_grp.U 0 ψ₁, U_grp.U (-h) ψ₂⟫_ℂ := by ring_nf
        _ = ⟪(ψ₁ : H), U_grp.U (-h) ψ₂⟫_ℂ := by rw [U_grp.identity]; rfl
    rw [inner_sub_left, h_unitary, ← inner_sub_right]
    rw [inner_smul_right]
    congr 1
    simp only [map_inv₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have h_rhs' : Tendsto (fun h : ℝ => ⟪(ψ₁ : H), ((I * (-h))⁻¹ : ℂ) • (U_grp.U (-h) ψ₂ - ψ₂)⟫_ℂ)
                        (𝓝[≠] 0) (𝓝 ⟪(ψ₁ : H), generatorOp U_grp ψ₂⟫_ℂ) := by
    have h_neg : Tendsto (fun h : ℝ => -h) (𝓝[≠] 0) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
          convert (continuous_neg (G := ℝ)).tendsto 0 using 1
          simp
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, neg_eq_zero]
        exact hh
    have h_comp := h_rhs.comp h_neg
    apply Tendsto.congr _ h_comp
    intro h
    simp only [Function.comp_apply, ofReal_neg]
  refine tendsto_nhds_unique ?_ h_rhs'
  apply Tendsto.congr' _ h_lhs
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact h_eq h hh

theorem resolventIntegralPlus_in_domain (φ : H) :
    resolventIntegralPlus U_grp φ ∈ generatorDomain U_grp := by
  exact ⟨φ - I • resolventIntegralPlus U_grp φ, generator_limit_resolventIntegralPlus U_grp φ⟩

theorem resolventIntegralMinus_in_domain (φ : H) :
    resolventIntegralMinus U_grp φ ∈ generatorDomain U_grp := by
  exact ⟨φ + I • resolventIntegralMinus U_grp φ, generator_limit_resolventIntegralMinus U_grp φ⟩

theorem resolventIntegralPlus_solves (φ : H) :
    generatorOp U_grp ⟨resolventIntegralPlus U_grp φ, resolventIntegralPlus_in_domain U_grp φ⟩ +
    I • resolventIntegralPlus U_grp φ = φ := by
      classical
  have hψ := resolventIntegralPlus_in_domain U_grp φ
  simp only [generatorOp]
  have h_lim := generatorLimitValue_spec U_grp (resolventIntegralPlus U_grp φ) hψ
  have h_target := generator_limit_resolventIntegralPlus U_grp φ
  have h_eq := tendsto_nhds_unique h_lim h_target
  abel_nf
  rw [@LinearMap.coe_mk]
  simp_all only [mul_inv_rev, inv_I, mul_neg, neg_smul, AddHom.coe_mk, sub_add_cancel]

theorem resolventIntegralMinus_solves (φ : H) :
    generatorOp U_grp ⟨resolventIntegralMinus U_grp φ, resolventIntegralMinus_in_domain U_grp φ⟩ -
    I • resolventIntegralMinus U_grp φ = φ := by
  classical
  have hψ := resolventIntegralMinus_in_domain U_grp φ
  simp only [generatorOp]
  have h_lim := generatorLimitValue_spec U_grp (resolventIntegralMinus U_grp φ) hψ
  have h_target := generator_limit_resolventIntegralMinus U_grp φ
  have h_eq := tendsto_nhds_unique h_lim h_target
  abel_nf
  simp_all only [mul_inv_rev, inv_I, mul_neg, neg_smul, LinearMap.coe_mk, AddHom.coe_mk, Int.reduceNeg,
    one_smul, add_neg_cancel_right]

theorem range_plus_i_eq_top :
    ∀ φ : H, ∃ ψ : generatorDomain U_grp,
      generatorOp U_grp ψ + I • (ψ : H) = φ := by
  intro φ
  exact ⟨⟨resolventIntegralPlus U_grp φ, resolventIntegralPlus_in_domain U_grp φ⟩,
         resolventIntegralPlus_solves U_grp φ⟩

theorem range_minus_i_eq_top :
    ∀ φ : H, ∃ ψ : generatorDomain U_grp,
      generatorOp U_grp ψ - I • (ψ : H) = φ := by
  intro φ
  exact ⟨⟨resolventIntegralMinus U_grp φ, resolventIntegralMinus_in_domain U_grp φ⟩,
         resolventIntegralMinus_solves U_grp φ⟩

end GeneratorConstruction

section AveragedVectors

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- Time-averaged vector: `h⁻¹ ∫₀ʰ U(t)φ dt`. These lie in the generator domain
    and converge to `φ` as `h → 0`, proving domain density. -/
noncomputable def averagedVector (h : ℝ) (_ : h ≠ 0) (φ : H) : H :=
  (h⁻¹ : ℂ) • ∫ t in Set.Ioc 0 h, U_grp.U t φ

lemma averagedVector_tendsto (φ : H) :
    Tendsto (fun h : ℝ => if hh : h ≠ 0 then averagedVector U_grp h hh φ else φ)
            (𝓝[>] 0) (𝓝 φ) := by
  unfold averagedVector
  have h_cont : Continuous (fun t => U_grp.U t φ) := U_grp.strong_continuous φ
  have h_f0 : U_grp.U 0 φ = φ := by rw [U_grp.identity]; rfl
  have h_deriv : HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, U_grp.U t φ) (U_grp.U 0 φ) 0 := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact h_cont.intervalIntegrable 0 0
    · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
    · exact h_cont.continuousAt
  rw [h_f0] at h_deriv
  have h_F0 : ∫ t in (0 : ℝ)..0, U_grp.U t φ = 0 := intervalIntegral.integral_same
  have h_tendsto_real : Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, U_grp.U t φ)
                                (𝓝[≠] 0) (𝓝 φ) := by
    have := h_deriv.hasDerivWithinAt (s := Set.univ \ {0})
    rw [hasDerivWithinAt_iff_tendsto_slope] at this
    simp only [Set.diff_diff, Set.union_self] at this
    convert this using 1
    · ext h
      unfold slope
      simp only [sub_zero, h_F0, vsub_eq_sub]
    · congr 1
      exact Set.compl_eq_univ_diff {(0 : ℝ)}
  have h_restrict := h_tendsto_real.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
  apply Tendsto.congr' _ h_restrict
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [dif_pos (ne_of_gt hh)]
  rw [intervalIntegral.integral_of_le (le_of_lt hh)]
  rw [(Complex.coe_smul h⁻¹ _).symm, ofReal_inv]

lemma averagedVector_in_domain (h : ℝ) (hh : h ≠ 0) (φ : H) :
    averagedVector U_grp h hh φ ∈ generatorDomain U_grp := by
  by_cases hpos : h > 0
  · refine ⟨((I * h)⁻¹ : ℂ) • (U_grp.U h φ - φ), ?_⟩
    have h_cont : Continuous (fun t => U_grp.U t φ) := U_grp.strong_continuous φ
    set ψ := averagedVector U_grp h hh φ with hψ_def
    have h_FTC1 : Tendsto (fun s : ℝ => (s⁻¹ : ℂ) • ∫ t in (0 : ℝ)..s, U_grp.U t φ) (𝓝[≠] 0) (𝓝 φ) := by
      have h_deriv : HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, U_grp.U t φ) φ 0 := by
        have := intervalIntegral.integral_hasDerivAt_right (h_cont.intervalIntegrable 0 0)
                  (h_cont.stronglyMeasurableAtFilter volume (𝓝 0)) h_cont.continuousAt
        simp only [U_grp.identity, ContinuousLinearMap.id_apply] at this
        exact this
      have h_F0 : ∫ t in (0 : ℝ)..0, U_grp.U t φ = 0 := intervalIntegral.integral_same
      rw [hasDerivAt_iff_tendsto_slope] at h_deriv
      apply h_deriv.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      unfold slope
      simp only [vsub_eq_sub, sub_zero, h_F0, sub_zero]
      rw [(Complex.coe_smul s⁻¹ _).symm, ofReal_inv]
    have h_FTC2 : Tendsto (fun s : ℝ => (s⁻¹ : ℂ) • ∫ t in (h : ℝ)..(h + s), U_grp.U t φ) (𝓝[≠] 0) (𝓝 (U_grp.U h φ)) := by
      have h_deriv : HasDerivAt (fun x => ∫ t in (h : ℝ)..x, U_grp.U t φ) (U_grp.U h φ) h := by
        exact intervalIntegral.integral_hasDerivAt_right (h_cont.intervalIntegrable h h)
                (h_cont.stronglyMeasurableAtFilter volume (𝓝 h)) h_cont.continuousAt
      have h_Fh : ∫ t in (h : ℝ)..h, U_grp.U t φ = 0 := intervalIntegral.integral_same
      rw [hasDerivAt_iff_tendsto_slope] at h_deriv
      have h_shift : Tendsto (fun s : ℝ => h + s) (𝓝[≠] 0) (𝓝[≠] h) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · have : Tendsto (fun s : ℝ => h + s) (𝓝 0) (𝓝 h) := by
            have h1 : Tendsto (fun _ : ℝ => h) (𝓝 0) (𝓝 h) := tendsto_const_nhds
            have h2 : Tendsto (fun s : ℝ => s) (𝓝 0) (𝓝 0) := tendsto_id
            convert h1.add h2 using 1
            simp only [add_zero]
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left]
          exact hs
      have := h_deriv.comp h_shift
      simp only at this
      apply this.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      unfold slope
      simp only [vsub_eq_sub, h_Fh, sub_zero, Function.comp_apply, add_sub_cancel_left]
      rw [(Complex.coe_smul s⁻¹ _).symm, ofReal_inv]
    have h_key : ∀ s : ℝ, s ≠ 0 →
        ((I * s)⁻¹ : ℂ) • (U_grp.U s ψ - ψ) =
        ((I * h)⁻¹ : ℂ) • (((s⁻¹ : ℂ) • ∫ t in (h : ℝ)..(h + s), U_grp.U t φ) -
                           ((s⁻¹ : ℂ) • ∫ t in (0 : ℝ)..s, U_grp.U t φ)) := by
      intro s hs
      rw [hψ_def]
      unfold averagedVector
      rw [ContinuousLinearMap.map_smul]
      have h_shift_int : U_grp.U s (∫ t in Set.Ioc 0 h, U_grp.U t φ) =
                         ∫ t in Set.Ioc s (s + h), U_grp.U t φ := by
        rw [← (U_grp.U s).integral_comp_comm h_cont.integrableOn_Ioc]
        have h_subst : ∫ t in Set.Ioc 0 h, U_grp.U s (U_grp.U t φ) =
                       ∫ t in Set.Ioc 0 h, U_grp.U (s + t) φ := by
          congr 1; ext t
          rw [@OneParameterUnitaryGroup.group_law]
          rfl
        rw [h_subst]
        have h_preimage : (fun t => t - s) ⁻¹' (Set.Ioc 0 h) = Set.Ioc s (s + h) := by
          ext t; simp only [Set.mem_preimage, Set.mem_Ioc]; constructor <;> intro ⟨a, b⟩ <;> constructor <;> linarith
        have h_meas : Measure.map (fun t => t - s) volume = volume :=
          (measurePreserving_sub_right volume s).map_eq
        rw [← h_meas, MeasureTheory.setIntegral_map measurableSet_Ioc]
        · simp only [h_preimage]; congr 1
          exact congrFun (congrArg restrict (id (Eq.symm h_meas))) (Set.Ioc s (s + h))
          simp only [add_sub_cancel]
        · exact h_cont.aestronglyMeasurable.comp_measurable (measurable_const_add s)
        · exact (measurable_sub_const s).aemeasurable
      rw [h_shift_int]
      rw [← smul_sub, smul_smul]
      have h_Ioc_eq_interval : ∀ a b : ℝ, a ≤ b → ∫ t in Set.Ioc a b, U_grp.U t φ =
                                                    ∫ t in a..b, U_grp.U t φ := by
        intro a b hab
        rw [intervalIntegral.integral_of_le hab]
      rw [h_Ioc_eq_interval s (s + h) (by linarith), h_Ioc_eq_interval 0 h (le_of_lt hpos)]
      have h_arith : (∫ t in s..(s + h), U_grp.U t φ) - ∫ t in (0 : ℝ)..h, U_grp.U t φ =
               (∫ t in (h : ℝ)..(h + s), U_grp.U t φ) - ∫ t in (0 : ℝ)..s, U_grp.U t φ := by
        have hint : ∀ a b : ℝ, IntervalIntegrable (fun t => U_grp.U t φ) volume a b :=
          fun a b => h_cont.intervalIntegrable a b
        have h3 : s + h = h + s := add_comm s h
        have key : (∫ t in s..(s + h), U_grp.U t φ) + ∫ t in (0 : ℝ)..s, U_grp.U t φ =
                  (∫ t in h..(h + s), U_grp.U t φ) + ∫ t in (0 : ℝ)..h, U_grp.U t φ := by
          have eq1 := intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s (s + h))
          have eq2 := intervalIntegral.integral_add_adjacent_intervals (hint 0 h) (hint h (h + s))
          calc (∫ t in s..(s + h), U_grp.U t φ) + ∫ t in (0 : ℝ)..s, U_grp.U t φ
              = (∫ t in (0 : ℝ)..s, U_grp.U t φ) + ∫ t in s..(s + h), U_grp.U t φ := by abel
            _ = ∫ t in (0 : ℝ)..(s + h), U_grp.U t φ := eq1
            _ = ∫ t in (0 : ℝ)..(h + s), U_grp.U t φ := by rw [h3]
            _ = (∫ t in (0 : ℝ)..h, U_grp.U t φ) + ∫ t in h..(h + s), U_grp.U t φ := eq2.symm
            _ = (∫ t in h..(h + s), U_grp.U t φ) + ∫ t in (0 : ℝ)..h, U_grp.U t φ := by abel
        have h_sub : ∀ a b c d : H, a + b = c + d → a - d = c - b := by
          intros a b c d heq
          have h1 : a = c + d - b := by rw [← heq]; abel
          rw [h1]; abel
        exact h_sub _ _ _ _ key
      rw [h_arith]
      have h_scalar : ((I * s)⁻¹ : ℂ) * (h⁻¹ : ℂ) = ((I * h)⁻¹ : ℂ) * (s⁻¹ : ℂ) := by
        field_simp
      rw [h_scalar, ← smul_smul, smul_sub]
    apply Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact (h_key s hs).symm
    · exact Tendsto.smul tendsto_const_nhds (h_FTC2.sub h_FTC1)
  · push_neg at hpos
    have hneg : h < 0 := lt_of_le_of_ne hpos (Ne.symm hh.symm)
    have h_empty : Set.Ioc 0 h = ∅ := Set.Ioc_eq_empty (not_lt.mpr (le_of_lt hneg))
    unfold averagedVector
    rw [h_empty, setIntegral_empty, smul_zero]
    exact (generatorDomain U_grp).zero_mem

theorem generatorDomain_dense_via_average :
    Dense (generatorDomain U_grp : Set H) := by
  rw [Metric.dense_iff]
  intro φ ε hε
  have h_tendsto := averagedVector_tendsto U_grp φ
  rw [Metric.tendsto_nhds] at h_tendsto
  specialize h_tendsto ε hε
  rw [Filter.eventually_iff_exists_mem] at h_tendsto
  obtain ⟨S, hS_mem, hS_ball⟩ := h_tendsto
  rw [mem_nhdsWithin] at hS_mem
  obtain ⟨U, hU_open, hU_zero, hU_sub⟩ := hS_mem
  rw [Metric.isOpen_iff] at hU_open
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := hU_open 0 hU_zero
  have hh : δ / 2 ≠ 0 := by linarith
  have hh_pos : δ / 2 > 0 := by linarith
  refine ⟨averagedVector U_grp (δ / 2) hh φ, ?_, ?_⟩
  · have h_in_ball : δ / 2 ∈ Metric.ball 0 δ := by
      rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_of_pos hh_pos]
      linarith
    have h_in_U : δ / 2 ∈ U := hδ_ball h_in_ball
    have h_in_S : δ / 2 ∈ S := hU_sub ⟨h_in_U, hh_pos⟩
    have := hS_ball (δ / 2) h_in_S
    rw [dif_pos hh] at this
    exact this
  · exact averagedVector_in_domain U_grp (δ / 2) hh φ

theorem generatorDomain_dense : Dense (generatorDomain U_grp : Set H) :=
  generatorDomain_dense_via_average U_grp

lemma generatorDomain_maximal (ψ : H)
    (h : ∃ η : H, Tendsto (fun t : ℝ => ((I : ℂ) * t)⁻¹ • (U_grp.U t ψ - ψ)) (𝓝[≠] 0) (𝓝 η)) :
    ψ ∈ generatorDomain U_grp := h

/-- The complete generator structure for a strongly continuous one-parameter unitary group. -/
noncomputable def generatorOfUnitaryGroup : Generator U_grp where
  op := generatorOp U_grp
  domain := generatorDomain U_grp
  dense_domain := generatorDomain_dense U_grp
  generator_formula := generator_formula_holds U_grp
  domain_invariant := generatorDomain_invariant U_grp
  symmetric := generator_symmetric U_grp
  domain_maximal := generatorDomain_maximal U_grp

theorem generatorOfUnitaryGroup_isSelfAdjoint :
    (generatorOfUnitaryGroup U_grp).IsSelfAdjoint := by
  constructor
  · intro φ
    obtain ⟨ψ, hψ_eq⟩ := range_plus_i_eq_top U_grp φ
    exact ⟨ψ.val, ψ.property, hψ_eq⟩
  · intro φ
    obtain ⟨ψ, hψ_eq⟩ := range_minus_i_eq_top U_grp φ
    exact ⟨ψ.val, ψ.property, hψ_eq⟩

end AveragedVectors



variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- Constructs the unique self-adjoint generator of a strongly continuous
    one-parameter unitary group. This is the forward direction of Stone's theorem. -/
noncomputable def Generator.ofUnitaryGroup
    (U_grp : OneParameterUnitaryGroup (H := H)) :
    Generator U_grp :=
  generatorOfUnitaryGroup U_grp

theorem Generator.ofUnitaryGroup_isSelfAdjoint
    (U_grp : OneParameterUnitaryGroup (H := H)) :
    (Generator.ofUnitaryGroup U_grp).IsSelfAdjoint :=
  generatorOfUnitaryGroup_isSelfAdjoint U_grp

theorem generatorOfUnitaryGroup_eq_ofUnitaryGroup :
    generatorOfUnitaryGroup U_grp = Generator.ofUnitaryGroup U_grp := by
  unfold generatorOfUnitaryGroup Generator.ofUnitaryGroup
  rfl

theorem isSelfAdjoint_transfer :
    (Generator.ofUnitaryGroup U_grp).IsSelfAdjoint := by
  rw [← generatorOfUnitaryGroup_eq_ofUnitaryGroup]
  exact generatorOfUnitaryGroup_isSelfAdjoint U_grp



end QuantumMechanics.Bochner
