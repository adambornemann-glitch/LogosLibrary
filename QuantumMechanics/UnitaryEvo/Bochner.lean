/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Generator
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Stone's Theorem: Existence of Self-Adjoint Generators

This file proves that every strongly continuous one-parameter unitary group on a
complex Hilbert space has a unique self-adjoint infinitesimal generator. This is
the "forward direction" of Stone's theorem.

The construction uses Laplace transform techniques: given a unitary group `U(t)`,
we define resolvent-type integrals `R±(φ) = ∓i ∫₀^∞ e^{-t} U(±t)φ dt` and show these
solve `(A ± iI)ψ = φ`, establishing surjectivity of `A ± iI` and hence self-adjointness.

## Main definitions

* `resolventIntegralPlus`: The integral `(-i) ∫₀^∞ e^{-t} U(t)φ dt`, solving `(A + iI)ψ = φ`.
* `resolventIntegralMinus`: The integral `i ∫₀^∞ e^{-t} U(-t)φ dt`, solving `(A - iI)ψ = φ`.
* `generatorDomain`: The submodule of vectors where the generator limit exists.
* `generatorOp`: The generator as a linear map on its domain.
* `generatorOfUnitaryGroup`: The complete `Generator` structure for a unitary group.
* `averagedVector`: Time-averaged vectors `h⁻¹ ∫₀ʰ U(t)φ dt` used to prove domain density.

## Main statements

* `generator_limit_resolventIntegralPlus`: The resolvent integral is in the generator
  domain and `A(R₊φ) = φ - iR₊φ`.
* `generator_limit_resolventIntegralMinus`: Similarly, `A(R₋φ) = φ + iR₋φ`.
* `resolventIntegralPlus_solves`: We have `Aψ + iψ = φ` for `ψ = R₊φ`.
* `resolventIntegralMinus_solves`: We have `Aψ - iψ = φ` for `ψ = R₋φ`.
* `range_plus_i_eq_top`: The operator `A + iI` is surjective.
* `range_minus_i_eq_top`: The operator `A - iI` is surjective.
* `generatorDomain_dense`: The domain of the generator is dense in `H`.
* `generatorOfUnitaryGroup_isSelfAdjoint`: The generator is self-adjoint.

## Implementation notes

* The exponential weight `e^{-t}` ensures integrability; the parameter `λ = 1` is
  arbitrary (any `λ > 0` works). This corresponds to evaluating the resolvent at `z = ±i`.
* The generator limit uses `𝓝[≠] 0` (punctured neighborhood) to define `Aψ = lim_{t→0} (U(t)ψ - ψ)/(it)`.
* Domain density is proved via averaged vectors: `h⁻¹ ∫₀ʰ U(t)φ dt → φ` as `h → 0`,
  and these averaged vectors lie in the domain.
* The self-adjointness criterion used is: `A` is self-adjoint iff `A` is symmetric
  and `ran(A ± iI) = H`. This avoids dealing with the adjoint of an unbounded operator directly.

## Physics interpretation

This file establishes that quantum time evolution `U(t) = e^{-itH}` uniquely determines
the Hamiltonian `H` (up to the scaling by `ℏ`). The resolvent integrals are related to
the Laplace transform of the propagator, which in physics connects time-domain evolution
to energy-domain (spectral) properties.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Theorem VIII.8
* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Section X.1
* [Hall, *Quantum Theory for Mathematicians*][hall2013], Chapter 10

## TODO

* Prove the converse: every self-adjoint operator generates a unique unitary group
  (requires spectral theorem and functional calculus).
* Prove uniqueness of the generator.
* Connect to the spectral measure via `U(t) = ∫ e^{itλ} dE(λ)`.
-/

namespace QuantumMechanics.Bochner

open MeasureTheory Measure Filter Topology Complex QuantumMechanics.Generators


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
set_option linter.unusedSectionVars false

section BasicBochner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]


lemma integral_exp_neg_Ioc (n : ℕ) : ∫ x in (0 : ℝ)..n, Real.exp (-x) = 1 - Real.exp (-n) := by
  by_cases hn : (n : ℝ) ≤ 0
  · have hn' : n = 0 := Nat.cast_eq_zero.mp (le_antisymm hn (Nat.cast_nonneg n))
    simp [hn', intervalIntegral.integral_same]
  · push_neg at hn
    have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) n, HasDerivAt (fun t => -Real.exp (-t)) (Real.exp (-x)) x := by
      intro x _
      have h1 : HasDerivAt (fun t => -t) (-1) x := hasDerivAt_neg x
      have h2 : HasDerivAt Real.exp (Real.exp (-x)) (-x) := Real.hasDerivAt_exp (-x)
      convert (h2.comp x h1).neg using 1
      ring
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hn)
            ((Real.continuous_exp.comp continuous_neg).continuousOn.neg)
            (fun x hx => hderiv x hx)
            ((Real.continuous_exp.comp continuous_neg).intervalIntegrable 0 n) using 1
    simp [Real.exp_zero]; ring


lemma integrableOn_exp_neg : IntegrableOn (fun t => Real.exp (-t)) (Set.Ici 0) volume := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (ι := ℕ) (l := atTop)
        (b := fun n => (n : ℝ)) 1 0 ?_ ?_ ?_
  · intro i
    exact (Real.continuous_exp.comp continuous_neg).integrableOn_Ioc
  · exact tendsto_natCast_atTop_atTop
  · filter_upwards with n
    simp_rw [fun x => Real.norm_of_nonneg (le_of_lt (Real.exp_pos (-x)))]
    calc ∫ x in (0 : ℝ)..n, Real.exp (-x)
        = 1 - Real.exp (-n) := integral_exp_neg_Ioc n
      _ ≤ 1 := by linarith [Real.exp_pos (-n : ℝ)]


lemma integral_exp_neg_eq_one : ∫ t in Set.Ici (0 : ℝ), Real.exp (-t) = 1 := by
  rw [integral_Ici_eq_integral_Ioi]
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
      (f := fun t => -Real.exp (-t)) (m := 0)]
  · simp [Real.exp_zero]
  · intro x _
    have h1 : HasDerivAt (fun t => -t) (-1) x := hasDerivAt_neg x
    have h2 : HasDerivAt Real.exp (Real.exp (-x)) (-x) := Real.hasDerivAt_exp (-x)
    convert (h2.comp x h1).neg using 1; ring
  · exact integrableOn_exp_neg.mono_set Set.Ioi_subset_Ici_self
  · convert (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).neg using 1; simp


lemma integrableOn_exp_neg_Ioi : IntegrableOn (fun t => Real.exp (-t)) (Set.Ioi 0) volume :=
  integrableOn_exp_neg.mono_set Set.Ioi_subset_Ici_self

lemma integrable_exp_decay_continuous
    (f : ℝ → E) (hf_cont : Continuous f)
    (C : ℝ) (hC : ∀ t ≥ 0, ‖f t‖ ≤ C) :
    IntegrableOn (fun t => Real.exp (-t) • f t) (Set.Ici 0) volume := by
  set M := max |C| 1 with hM_def
  have hM_pos : 0 < M := lt_max_of_lt_right one_pos
  have hM_ge : |C| ≤ M := le_max_left _ _
  have h_exp_int : IntegrableOn (fun t => Real.exp (-t)) (Set.Ici 0) volume :=
  integrableOn_exp_neg

  have h_bound_int : IntegrableOn (fun t => M * Real.exp (-t)) (Set.Ici 0) volume :=
    h_exp_int.const_mul M
  have h_meas : AEStronglyMeasurable (fun t => Real.exp (-t) • f t)
                                      (volume.restrict (Set.Ici 0)) := by
    apply AEStronglyMeasurable.smul
    · exact (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable.restrict
    · exact hf_cont.aestronglyMeasurable.restrict
  have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ici 0)),
                  ‖Real.exp (-t) • f t‖ ≤ M * Real.exp (-t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
    calc Real.exp (-t) * ‖f t‖
        ≤ Real.exp (-t) * |C| := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            calc ‖f t‖ ≤ C := hC t ht
              _ ≤ |C| := le_abs_self C
      _ ≤ Real.exp (-t) * M := mul_le_mul_of_nonneg_left hM_ge (Real.exp_pos _).le
      _ = M * Real.exp (-t) := mul_comm _ _
  exact Integrable.mono' h_bound_int h_meas h_bound


lemma norm_integral_exp_decay_le
    (f : ℝ → E) (hf_cont : Continuous f)
    (C : ℝ) (hC : ∀ t ≥ 0, ‖f t‖ ≤ C) (_ : 0 ≤ C) :
    ‖∫ t in Set.Ici 0, Real.exp (-t) • f t‖ ≤ C := by
  have h_integrand_int : IntegrableOn (fun t => Real.exp (-t) • f t) (Set.Ici 0) volume :=
    integrable_exp_decay_continuous f hf_cont C hC
  have h_exp_int : IntegrableOn (fun t => Real.exp (-t)) (Set.Ici 0) volume :=
    integrableOn_exp_neg
  calc ‖∫ t in Set.Ici 0, Real.exp (-t) • f t‖
      ≤ ∫ t in Set.Ici 0, ‖Real.exp (-t) • f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ici 0, C * Real.exp (-t) := by
        apply setIntegral_mono_on h_integrand_int.norm (h_exp_int.const_mul C) measurableSet_Ici
        intro t ht
        rw [norm_smul, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
        calc Real.exp (-t) * ‖f t‖
            ≤ Real.exp (-t) * C := mul_le_mul_of_nonneg_left (hC t ht) (Real.exp_pos _).le
          _ = C * Real.exp (-t) := mul_comm _ _
    _ = C * ∫ t in Set.Ici 0, Real.exp (-t) := by exact MeasureTheory.integral_const_mul C fun a => Real.exp (-a)
    _ = C * 1 := by rw [integral_exp_neg_eq_one]
    _ = C := mul_one C

lemma tendsto_integral_Ioc_exp_decay
    (f : ℝ → E) (hf_cont : Continuous f)
    (C : ℝ) (hC : ∀ t ≥ 0, ‖f t‖ ≤ C) :
    Tendsto (fun T => ∫ t in Set.Ioc 0 T, Real.exp (-t) • f t)
            atTop
            (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • f t)) := by
  rw [integral_Ici_eq_integral_Ioi]
  have h_int : IntegrableOn (fun t => Real.exp (-t) • f t) (Set.Ioi 0) volume :=
    (integrable_exp_decay_continuous f hf_cont C hC).mono_set Set.Ioi_subset_Ici_self
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M := max C 0 with hM_def
  have hM_nonneg : 0 ≤ M := le_max_right _ _
  have h_norm_int : IntegrableOn (fun t => M * Real.exp (-t)) (Set.Ioi 0) volume := by
    have h_exp : IntegrableOn (fun t => Real.exp (-t)) (Set.Ioi 0) volume :=
      integrableOn_exp_neg_Ioi
    exact h_exp.const_mul M
  have h_tail_bound : ∀ T ≥ 0, ∫ t in Set.Ioi T, M * Real.exp (-t) = M * Real.exp (-T) := by
    intro T hT
    have h_deriv : ∀ x ∈ Set.Ici T, HasDerivAt (fun t => -M * Real.exp (-t)) (M * Real.exp (-x)) x := by
      intro x _
      have h1 : HasDerivAt (fun t => -t) (-1) x := hasDerivAt_neg x
      have h2 : HasDerivAt Real.exp (Real.exp (-x)) (-x) := Real.hasDerivAt_exp (-x)
      have h3 := h2.comp x h1
      have h4 : HasDerivAt (fun t => M * Real.exp (-t)) (M * (Real.exp (-x) * -1)) x :=
        h3.const_mul M
      have h5 := h4.neg
      convert h5 using 1 <;> ring_nf ; exact rfl
    have h_int : IntegrableOn (fun t => M * Real.exp (-t)) (Set.Ioi T) volume :=
      h_norm_int.mono_set (Set.Ioi_subset_Ioi hT)
    have h_tend : Tendsto (fun t => -M * Real.exp (-t)) atTop (𝓝 0) := by
      have : Tendsto (fun t => -M * Real.exp (-t)) atTop (𝓝 (-M * 0)) := by
        apply Tendsto.const_mul
        exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
      simp only [mul_zero] at this
      exact this
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (a := T) (f := fun t => -M * Real.exp (-t)) (m := 0)
        h_deriv h_int h_tend]
    ring
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M * Real.exp (-(N : ℝ)) < ε := by
    by_cases hM_zero : M = 0
    · exact ⟨0, by simp [hM_zero, hε]⟩
    · have hM_pos : 0 < M := lt_of_le_of_ne hM_nonneg (Ne.symm hM_zero)
      have : Tendsto (fun n : ℕ => M * Real.exp (-(n : ℝ))) atTop (𝓝 (M * 0)) := by
        apply Tendsto.const_mul
        exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      simp at this
      exact (this.eventually (gt_mem_nhds hε)).exists
  use max 1 N
  intro T hT
  have hT_pos : 0 < T := by
    have : (1 : ℝ) ≤ max 1 (N : ℝ) := le_max_left 1 (N : ℝ)
    linarith
  have h_split : ∫ t in Set.Ioi 0, Real.exp (-t) • f t ∂volume =
                 (∫ t in Set.Ioc 0 T, Real.exp (-t) • f t ∂volume) +
                 (∫ t in Set.Ioi T, Real.exp (-t) • f t ∂volume) := by
    have h_union : Set.Ioc 0 T ∪ Set.Ioi T = Set.Ioi 0 := by
      ext x
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · intro h; cases h with
        | inl h => exact h.1
        | inr h => exact lt_trans hT_pos h
      · intro hx
        by_cases hxT : x ≤ T
        · left; exact ⟨hx, hxT⟩
        · right; exact lt_of_not_ge hxT
    rw [← h_union, setIntegral_union (Set.Ioc_disjoint_Ioi (le_refl T)) measurableSet_Ioi
          (h_int.mono_set Set.Ioc_subset_Ioi_self) (h_int.mono_set (Set.Ioi_subset_Ioi hT_pos.le))]
  rw [h_split, dist_eq_norm]
  have h_simp : (∫ t in Set.Ioc 0 T, Real.exp (-t) • f t) -
                ((∫ t in Set.Ioc 0 T, Real.exp (-t) • f t) + ∫ t in Set.Ioi T, Real.exp (-t) • f t) =
                -(∫ t in Set.Ioi T, Real.exp (-t) • f t) := by abel
  rw [h_simp, norm_neg]
  calc ‖∫ t in Set.Ioi T, Real.exp (-t) • f t‖
      ≤ ∫ t in Set.Ioi T, ‖Real.exp (-t) • f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi T, M * Real.exp (-t) := by
        apply setIntegral_mono_on (h_int.mono_set (Set.Ioi_subset_Ioi hT_pos.le)).norm
              (h_norm_int.mono_set (Set.Ioi_subset_Ioi hT_pos.le)) measurableSet_Ioi
        intro t ht
        rw [norm_smul, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        calc ‖f t‖ ≤ C := hC t (le_of_lt (lt_trans hT_pos ht))
          _ ≤ M := le_max_left _ _
    _ = M * Real.exp (-T) := h_tail_bound T hT_pos.le
    _ ≤ M * Real.exp (-(N : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hM_nonneg
        apply Real.exp_le_exp.mpr
        have h1 : (N : ℝ) ≤ max 1 N := Nat.cast_le.mpr (le_max_right 1 N)
        simp_all only [ge_iff_le, gt_iff_lt, le_sup_right, sup_le_iff, sub_add_cancel_left, Nat.cast_max, Nat.cast_one,
          neg_le_neg_iff, M]
    _ < ε := hN

lemma hasDerivAt_integral_of_exp_decay
    (f : ℝ → ℝ → E)
    (hf_cont : Continuous (Function.uncurry f))
    (hf_deriv : ∀ t s, HasDerivAt (f · s) (deriv (f · s) t) t)
    (hf'_cont : ∀ t, Continuous (fun s => deriv (f · s) t))
    (C : ℝ) (hC : ∀ t s, s ≥ 0 → ‖f t s‖ ≤ C)
    (hC' : ∀ t s, s ≥ 0 → ‖deriv (f · s) t‖ ≤ C)
    (t : ℝ) :
    HasDerivAt (fun τ => ∫ s in Set.Ici 0, Real.exp (-s) • f τ s)
               (∫ s in Set.Ici 0, Real.exp (-s) • deriv (f · s) t)
               t := by
  let μ := volume.restrict (Set.Ici (0 : ℝ))
  let M := max |C| 1
  have hM_pos : 0 < M := lt_max_of_lt_right one_pos
  have hC_le_M : |C| ≤ M := le_max_left _ _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (ε := 1) (x₀ := t)
    (F := fun τ s => Real.exp (-s) • f τ s)
    (F' := fun τ s => Real.exp (-s) • deriv (f · s) τ)
    (bound := fun s => M * Real.exp (-s))
    one_pos ?hF_meas ?hF_int ?hF'_meas ?hF'_bound ?hbound_int ?hF_deriv
  exact h.2
  case hF_meas =>
    filter_upwards with τ
    apply AEStronglyMeasurable.smul
    · exact (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable
    · exact (hf_cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  case hF_int =>
    have hf_t_cont : Continuous (fun s => f t s) :=
      hf_cont.comp (continuous_const.prodMk continuous_id)
    have hf_t_bound : ∀ s ≥ 0, ‖f t s‖ ≤ |C| := fun s hs => (hC t s hs).trans (le_abs_self C)
    exact integrable_exp_decay_continuous (fun s => f t s) hf_t_cont |C| hf_t_bound
  case hF'_meas =>
    apply AEStronglyMeasurable.smul
    · exact (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable
    · exact (hf'_cont t).aestronglyMeasurable
  case hF'_bound =>
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs τ _
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
    have h1 : ‖deriv (f · s) τ‖ ≤ C := hC' τ s hs
    calc Real.exp (-s) * ‖deriv (f · s) τ‖
        ≤ Real.exp (-s) * M := by
          apply mul_le_mul_of_nonneg_left
          exact h1.trans ((le_abs_self C).trans hC_le_M)
          exact le_of_lt (Real.exp_pos _)
      _ = M * Real.exp (-s) := mul_comm _ _
  case hbound_int =>
    exact integrableOn_exp_neg.const_mul M
  case hF_deriv =>
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s _ τ _
    exact (hf_deriv τ s).const_smul (Real.exp (-s))

end BasicBochner

section UnitaryGroupIntegration

variable (U_grp : OneParameterUnitaryGroup (H := H))

lemma continuous_unitary_apply (φ : H) :
    Continuous (fun t => U_grp.U t φ) :=
  U_grp.strong_continuous φ

lemma integrable_exp_neg_unitary (φ : H) :
    IntegrableOn (fun t => Real.exp (-t) • U_grp.U t φ) (Set.Ici 0) volume := by
  apply integrable_exp_decay_continuous
    (fun t => U_grp.U t φ)
    (U_grp.strong_continuous φ)
    ‖φ‖
  intro t _ht
  exact le_of_eq (norm_preserving U_grp t φ)

lemma integrable_exp_neg_unitary_neg (φ : H) :
    IntegrableOn (fun t => Real.exp (-t) • U_grp.U (-t) φ) (Set.Ici 0) volume := by
  apply integrable_exp_decay_continuous
    (fun t => U_grp.U (-t) φ)
    ((U_grp.strong_continuous φ).comp continuous_neg)
    ‖φ‖
  intro t _ht
  exact le_of_eq (norm_preserving U_grp (-t) φ)

lemma norm_integral_exp_neg_unitary_le (φ : H) :
    ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ ≤ ‖φ‖ := by
  apply norm_integral_exp_decay_le
    (fun t => U_grp.U t φ)
    (U_grp.strong_continuous φ)
    ‖φ‖
  · intro t _ht
    exact le_of_eq (norm_preserving U_grp t φ)
  · exact norm_nonneg φ

lemma integrable_unitary_Ioc (φ : H) (h : ℝ) (_ : 0 < h) :
    IntegrableOn (fun t => U_grp.U t φ) (Set.Ioc 0 h) volume := by
  exact (U_grp.strong_continuous φ).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

end UnitaryGroupIntegration

section ResolventIntegrals

variable (U_grp : OneParameterUnitaryGroup (H := H))

noncomputable def resolventIntegralPlus (φ : H) : H :=
  (-I) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ

noncomputable def resolventIntegralMinus (φ : H) : H :=
  I • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ

lemma resolventIntegralPlus_add (φ₁ φ₂ : H) :
    resolventIntegralPlus U_grp (φ₁ + φ₂) =
    resolventIntegralPlus U_grp φ₁ + resolventIntegralPlus U_grp φ₂ := by
  unfold resolventIntegralPlus
  have h_int₁ := integrable_exp_neg_unitary U_grp φ₁
  have h_int₂ := integrable_exp_neg_unitary U_grp φ₂
  have h_eq : (fun t => Real.exp (-t) • U_grp.U t (φ₁ + φ₂)) =
              (fun t => Real.exp (-t) • U_grp.U t φ₁ + Real.exp (-t) • U_grp.U t φ₂) := by
    ext t
    rw [map_add, smul_add]
  rw [h_eq, integral_add h_int₁ h_int₂, DistribMulAction.smul_add]

lemma norm_resolventIntegralPlus_le (φ : H) :
    ‖resolventIntegralPlus U_grp φ‖ ≤ ‖φ‖ := by
  unfold resolventIntegralPlus
  calc ‖(-I) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖
      = ‖-I‖ * ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ := norm_smul (-I) _
    _ = 1 * ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ := by simp only [norm_neg, norm_I]
    _ = ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ‖ := one_mul _
    _ ≤ ‖φ‖ := norm_integral_exp_neg_unitary_le U_grp φ

lemma norm_resolventIntegralMinus_le (φ : H) :
    ‖resolventIntegralMinus U_grp φ‖ ≤ ‖φ‖ := by
  unfold resolventIntegralMinus
  have h_bound : ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖ ≤ ‖φ‖ := by
    apply norm_integral_exp_decay_le
      (fun t => U_grp.U (-t) φ)
      ((U_grp.strong_continuous φ).comp continuous_neg)
      ‖φ‖
    · intro t _ht
      exact le_of_eq (norm_preserving U_grp (-t) φ)
    · exact norm_nonneg φ
  calc ‖I • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖
      = ‖I‖ * ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖ := norm_smul I _
    _ = 1 * ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖ := by simp only [norm_I, one_mul]
    _ = ‖∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ‖ := one_mul _
    _ ≤ ‖φ‖ := h_bound

end ResolventIntegrals

section GeneratorLimit

variable (U_grp : OneParameterUnitaryGroup (H := H))

lemma unitary_shift_resolventIntegralPlus (φ : H) (h : ℝ) (hh : h > 0) :
    U_grp.U h (resolventIntegralPlus U_grp φ) - resolventIntegralPlus U_grp φ =
    (-I) • ((Real.exp h - 1) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) -
    (-I) • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ := by
  unfold resolventIntegralPlus
  rw [ContinuousLinearMap.map_smul]
  have h_int := integrable_exp_neg_unitary U_grp φ
  have h_comm : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) =
              ∫ t in Set.Ici 0, U_grp.U h (Real.exp (-t) • U_grp.U t φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  rw [h_comm]
  have h_shift : ∀ t, U_grp.U h (Real.exp (-t) • U_grp.U t φ) =
                      Real.exp (-t) • U_grp.U (t + h) φ := by
    intro t
    have := U_grp.group_law h t
    rw [add_comm] at this
    rw [this]
    exact ContinuousLinearMap.map_smul_of_tower (U_grp.U h) (Real.exp (-t)) ((U_grp.U t) φ)
  simp_rw [h_shift]
  have h_exp : ∀ t, Real.exp (-t) • U_grp.U (t + h) φ =
                  Real.exp h • (Real.exp (-(t + h)) • U_grp.U (t + h) φ) := by
    intro t
    rw [← smul_assoc]
    congr 1
    rw [smul_eq_mul, ← Real.exp_add]
    congr 1
    ring
  simp_rw [h_exp]
  rw [integral_smul]
  have h_subst : ∫ t in Set.Ici 0, Real.exp (-(t + h)) • U_grp.U (t + h) φ =
               ∫ s in Set.Ici h, Real.exp (-s) • U_grp.U s φ := by
    have h_preimage : (· + h) ⁻¹' (Set.Ici h) = Set.Ici 0 := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ici]
      constructor
      · intro ht; linarith
      · intro ht; linarith
    have h_map : Measure.map (· + h) volume = (volume : Measure ℝ) :=
      (measurePreserving_add_right volume h).map_eq
    have h_meas_set : MeasurableSet (Set.Ici h) := measurableSet_Ici
    have h_f_meas : AEStronglyMeasurable (fun s => Real.exp (-s) • U_grp.U s φ)
                      (Measure.map (· + h) volume) := by
      rw [h_map]
      exact ((Real.continuous_exp.comp continuous_neg).smul
         (U_grp.strong_continuous φ)).aestronglyMeasurable
    have h_g_meas : AEMeasurable (· + h) volume := measurable_add_const h |>.aemeasurable
    rw [← h_map, MeasureTheory.setIntegral_map h_meas_set h_f_meas h_g_meas, h_preimage]
    congr 1
    ext t
    exact congrFun (congrArg DFunLike.coe (congrFun (congrArg restrict h_map) (Set.Ici 0))) t
  rw [h_subst]
  have h_split : ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ =
               (∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ) +
               (∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) := by
    rw [integral_Ici_eq_integral_Ioi]
    have h_union : Set.Ioi (0 : ℝ) = Set.Ioc 0 h ∪ Set.Ioi h := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro hx
        by_cases hxh : x ≤ h
        · left; exact ⟨hx, hxh⟩
        · right; exact lt_of_not_ge hxh
      · intro hx
        cases hx with
        | inl hx => exact hx.1
        | inr hx => exact lt_trans hh hx
    rw [h_union, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (h_int.mono_set (Set.Ioc_subset_Icc_self.trans Set.Icc_subset_Ici_self))
      (h_int.mono_set (Set.Ioi_subset_Ici hh.le))]
    congr 1
    exact Eq.symm integral_Ici_eq_integral_Ioi
  rw [h_split]
  set X := ∫ s in Set.Ici h, Real.exp (-s) • U_grp.U s φ with hX_def
  set Y := ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ with hY_def
  rw [smul_add]
  calc -I • Real.exp h • X - (-I • Y + -I • X)
      = -I • Real.exp h • X - -I • X - -I • Y := by abel
    _ = -I • (Real.exp h • X - X) - -I • Y := by rw [← smul_sub]
    _ = -I • ((Real.exp h - 1) • X) - -I • Y := by rw [sub_smul, one_smul]
    _ = -I • (Real.exp h - 1) • X - -I • Y := by rw [← h_subst]

lemma tendsto_exp_sub_one_div :
    Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[≠] 0) (𝓝 1) := by
  have h : HasDerivAt Real.exp 1 0 := by
    convert Real.hasDerivAt_exp 0 using 1
    exact Real.exp_zero.symm
  rw [hasDerivAt_iff_tendsto_slope] at h
  convert h using 1
  ext y
  simp only [slope, Real.exp_zero, sub_zero, vsub_eq_sub, smul_eq_mul]
  exact div_eq_inv_mul (Real.exp y - 1) y

lemma tendsto_integral_Ici_exp_unitary (φ : H) :
    Tendsto (fun h : ℝ => ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ)
            (𝓝 0)
            (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) := by
  have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U t φ) :=
    (Real.continuous_exp.comp continuous_neg).smul (U_grp.strong_continuous φ)
  have h_int := integrable_exp_neg_unitary U_grp φ
  have h_prim_cont : Continuous (fun h => ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ) :=
    intervalIntegral.continuous_primitive (fun a b => h_cont.intervalIntegrable a b) 0
  have h_prim_zero : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U t φ = 0 :=
    intervalIntegral.integral_same
  have h_prim_tendsto : Tendsto (fun h => ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
                                (𝓝 0) (𝓝 0) := by
    rw [← h_prim_zero]
    exact h_prim_cont.tendsto 0
  convert tendsto_const_nhds.sub h_prim_tendsto using 1
  · ext h
    by_cases hh : h ≥ 0
    · have h_ae_eq : ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ =
                     ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U t φ :=
        setIntegral_congr_set Ioi_ae_eq_Ici.symm
      have h_union : Set.Ioi (0 : ℝ) = Set.Ioc 0 h ∪ Set.Ioi h := by
        ext x
        simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
        constructor
        · intro hx
          by_cases hxh : x ≤ h
          · left; exact ⟨hx, hxh⟩
          · right; exact lt_of_not_ge hxh
        · intro hx
          cases hx with
          | inl hx => exact hx.1
          | inr hx => linarith [hh, hx]
      have h_disj : Disjoint (Set.Ioc 0 h) (Set.Ioi h) := Set.Ioc_disjoint_Ioi le_rfl
      have h_ae_eq2 : ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ =
                      ∫ t in Set.Ioi h, Real.exp (-t) • U_grp.U t φ :=
        setIntegral_congr_set Ioi_ae_eq_Ici.symm
      have h_eq1 : ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U t φ =
                   (∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ) +
                   ∫ t in Set.Ioi h, Real.exp (-t) • U_grp.U t φ := by
        rw [h_union, setIntegral_union h_disj measurableSet_Ioi
            (h_int.mono_set (Set.Ioc_subset_Icc_self.trans Set.Icc_subset_Ici_self))
            (h_int.mono_set (Set.Ioi_subset_Ici hh))]
      have h_eq2 : ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ =
                   ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ := by
        rw [intervalIntegral.integral_of_le hh]
      have h_eq3 : ∫ t in Set.Ioi h, Real.exp (-t) • U_grp.U t φ =
                   (∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U t φ) -
                   ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ := by
        exact Eq.symm (sub_eq_of_eq_add' h_eq1)
      rw [h_ae_eq2, h_eq3, h_ae_eq.symm, h_eq2]
    · push_neg at hh
      have h_union : Set.Ici h = Set.Ico h 0 ∪ Set.Ici 0 := by
        ext x
        simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ico]
        constructor
        · intro hx
          by_cases hx0 : x < 0
          · left; exact ⟨hx, hx0⟩
          · right; linarith
        · intro hx
          cases hx with
          | inl hx => exact hx.1
          | inr hx => linarith [hh, hx]
      have h_disj : Disjoint (Set.Ico h 0) (Set.Ici 0) := by
        rw [Set.disjoint_iff]
        intro x ⟨hx1, hx2⟩
        simp only [Set.mem_Ico] at hx1
        simp only [Set.mem_Ici] at hx2
        linarith [hx1.2, hx2]
      have h_eq1 : ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ =
                   (∫ t in Set.Ico h 0, Real.exp (-t) • U_grp.U t φ) +
                   ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ := by
        rw [h_union, setIntegral_union h_disj measurableSet_Ici
            (h_cont.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)
            h_int]
      have h_eq2 : ∫ t in Set.Ico h 0, Real.exp (-t) • U_grp.U t φ =
                   -(∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ) := by
        rw [← intervalIntegral.integral_symm]
        rw [intervalIntegral.integral_of_le (le_of_lt hh)]
        rw [@restrict_Ico_eq_restrict_Ioc]
      rw [h_eq1, h_eq2]
      ring_nf
      exact
        neg_add_eq_sub (∫ (t : ℝ) in 0..h, Real.exp (-t) • (U_grp.U t) φ)
          (∫ (t : ℝ) in Set.Ici 0, Real.exp (-t) • (U_grp.U t) φ)
  · simp only [sub_zero]

lemma tendsto_average_integral_unitary (φ : H) :
    Tendsto (fun h : ℝ => (h⁻¹ : ℂ) • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ)
            (𝓝[>] 0)
            (𝓝 φ) := by
  have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U t φ) :=
    (Real.continuous_exp.comp continuous_neg).smul (U_grp.strong_continuous φ)
  have h_f0 : Real.exp (-(0 : ℝ)) • U_grp.U 0 φ = φ := by
    simp only [neg_zero, Real.exp_zero, one_smul]
    rw [U_grp.identity]
    simp only [ContinuousLinearMap.id_apply]
  have h_eq : ∀ h > 0, ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ =
                       ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ := by
    intro h hh
    rw [intervalIntegral.integral_of_le (le_of_lt hh)]
  have h_deriv : HasDerivAt (fun h => ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
                            (Real.exp (-(0 : ℝ)) • U_grp.U 0 φ) 0 := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact h_cont.intervalIntegrable 0 0
    · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
    · exact h_cont.continuousAt
  rw [h_f0] at h_deriv
  have h_F0 : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U t φ = 0 :=
    intervalIntegral.integral_same
  have h_tendsto_real : Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
                                (𝓝[≠] 0) (𝓝 φ) := by
    have := h_deriv.hasDerivWithinAt (s := Set.univ \ {0})
    rw [hasDerivWithinAt_iff_tendsto_slope] at this
    simp only [Set.diff_diff, Set.union_self] at this
    convert this using 1
    ext h
    unfold slope
    simp only [sub_zero, h_F0, vsub_eq_sub]
    · congr 1
      exact Set.compl_eq_univ_diff {(0 : ℝ)}
  have h_restrict := h_tendsto_real.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
  apply Tendsto.congr' _ h_restrict
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [h_eq h hh, ← ofReal_inv, @Complex.coe_smul]

lemma unitary_shift_resolventIntegralPlus_neg (φ : H) (h : ℝ) (hh : h < 0) :
    U_grp.U h (resolventIntegralPlus U_grp φ) - resolventIntegralPlus U_grp φ =
    (-I) • (Real.exp h • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ) +
    (-I) • ((Real.exp h - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) := by
  unfold resolventIntegralPlus
  have h_int := integrable_exp_neg_unitary U_grp φ
  rw [ContinuousLinearMap.map_smul]
  have h_comm : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) =
                ∫ t in Set.Ici 0, U_grp.U h (Real.exp (-t) • U_grp.U t φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  rw [h_comm]
  have h_shift : ∀ t, U_grp.U h (Real.exp (-t) • U_grp.U t φ) =
                      Real.exp (-t) • U_grp.U (t + h) φ := by
    intro t
    rw [ContinuousLinearMap.map_smul_of_tower]
    congr 1
    have := U_grp.group_law h t
    rw [add_comm] at this
    exact congrFun (congrArg DFunLike.coe this).symm φ
  simp_rw [h_shift]
  have h_exp : ∀ t, Real.exp (-t) • U_grp.U (t + h) φ =
                    Real.exp h • (Real.exp (-(t + h)) • U_grp.U (t + h) φ) := by
    intro t
    rw [← smul_assoc, smul_eq_mul, ← Real.exp_add]
    congr 1
    ring_nf
  simp_rw [h_exp]
  have h_smul_comm : ∫ t in Set.Ici 0, Real.exp h • (Real.exp (-(t + h)) • U_grp.U (t + h) φ) =
                     Real.exp h • ∫ t in Set.Ici 0, Real.exp (-(t + h)) • U_grp.U (t + h) φ := by
    rw [@integral_smul]
  rw [h_smul_comm]
  have h_subst : ∫ t in Set.Ici 0, Real.exp (-(t + h)) • U_grp.U (t + h) φ =
                 ∫ s in Set.Ici h, Real.exp (-s) • U_grp.U s φ := by
    have h_preimage : (· + h) ⁻¹' (Set.Ici h) = Set.Ici 0 := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ici]
      constructor
      · intro ht; linarith
      · intro ht; linarith
    have h_map : Measure.map (· + h) volume = (volume : Measure ℝ) :=
      (measurePreserving_add_right volume h).map_eq
    have h_meas_set : MeasurableSet (Set.Ici h) := measurableSet_Ici
    have h_f_meas : AEStronglyMeasurable (fun s => Real.exp (-s) • U_grp.U s φ)
                      (Measure.map (· + h) volume) := by
      rw [h_map]
      exact ((Real.continuous_exp.comp continuous_neg).smul
             (U_grp.strong_continuous φ)).aestronglyMeasurable
    have h_g_meas : AEMeasurable (· + h) volume := measurable_add_const h |>.aemeasurable
    rw [← h_map, MeasureTheory.setIntegral_map h_meas_set h_f_meas h_g_meas, h_preimage]
    congr 1
    ext t
    exact congrFun (congrArg DFunLike.coe (congrFun (congrArg restrict h_map) (Set.Ici 0))) t
  rw [h_subst]
  set X := ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ with hX_def
  set Y := ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ with hY_def
  have h_split : ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ = X + Y := by
    have h_ae_eq1 : ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ =
                    ∫ t in Set.Ioi h, Real.exp (-t) • U_grp.U t φ :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_ae_eq2 : Y = ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U t φ :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_union : Set.Ioi h = Set.Ioc h 0 ∪ Set.Ioi 0 := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro hx
        by_cases hx0 : x ≤ 0
        · left; exact ⟨hx, hx0⟩
        · right; linarith
      · intro hx
        cases hx with
        | inl hx => exact hx.1
        | inr hx => linarith [hh, hx]
    have h_disj : Disjoint (Set.Ioc h 0) (Set.Ioi 0) := Set.Ioc_disjoint_Ioi le_rfl
    have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U t φ) :=
      (Real.continuous_exp.comp continuous_neg).smul (U_grp.strong_continuous φ)
    rw [h_ae_eq1, h_union, setIntegral_union h_disj measurableSet_Ioi
        (h_cont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (h_int.mono_set Set.Ioi_subset_Ici_self), h_ae_eq2.symm]
  rw [h_split, smul_add]
  calc -I • (Real.exp h • X + Real.exp h • Y) - -I • Y
      = -I • Real.exp h • X + -I • Real.exp h • Y - -I • Y := by rw [smul_add]
    _ = -I • Real.exp h • X + (-I • Real.exp h • Y - -I • Y) := by abel
    _ = -I • Real.exp h • X + -I • (Real.exp h • Y - Y) := by rw [← smul_sub]
    _ = -I • Real.exp h • X + -I • ((Real.exp h - 1) • Y) := by rw [sub_smul, one_smul]
    _ = -I • (Real.exp h • X) + -I • ((Real.exp h - 1) • Y) := by rw [hX_def]

lemma tendsto_average_integral_unitary_neg (φ : H) :
    Tendsto (fun h : ℝ => ((-h)⁻¹ : ℂ) • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ)
            (𝓝[<] 0)
            (𝓝 φ) := by
  have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U t φ) :=
    (Real.continuous_exp.comp continuous_neg).smul (U_grp.strong_continuous φ)
  have h_f0 : Real.exp (-(0 : ℝ)) • U_grp.U 0 φ = φ := by
    simp only [neg_zero, Real.exp_zero, one_smul]
    rw [U_grp.identity]
    simp only [ContinuousLinearMap.id_apply]
  have h_eq : ∀ h < 0, ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ =
                       ∫ t in h..0, Real.exp (-t) • U_grp.U t φ := by
    intro h hh
    rw [intervalIntegral.integral_of_le (le_of_lt hh)]
  have h_eq' : ∀ h < 0, ∫ t in h..0, Real.exp (-t) • U_grp.U t φ =
                        -∫ t in 0..h, Real.exp (-t) • U_grp.U t φ := by
    intro h _
    rw [intervalIntegral.integral_symm]
  have h_deriv : HasDerivAt (fun h => ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
                            (Real.exp (-(0 : ℝ)) • U_grp.U 0 φ) 0 := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact h_cont.intervalIntegrable 0 0
    · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
    · exact h_cont.continuousAt
  rw [h_f0] at h_deriv
  have h_F0 : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U t φ = 0 :=
    intervalIntegral.integral_same
  have h_tendsto_real : Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
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
  have h_restrict := h_tendsto_real.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))
  apply Tendsto.congr' _ h_restrict
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [h_eq h hh, h_eq' h hh]
  rw [smul_neg]
  rw [← neg_smul]
  rw [(Complex.coe_smul h⁻¹ _).symm, ofReal_inv]
  congr 1
  rw [@neg_inv]
  simp_all only [neg_zero, Real.exp_zero, one_smul, intervalIntegral.integral_same, neg_neg]

lemma generator_limit_resolventIntegralPlus (φ : H) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
                                              resolventIntegralPlus U_grp φ))
            (𝓝[≠] 0)
            (𝓝 (φ - I • resolventIntegralPlus U_grp φ)) := by
  have h_target : φ - I • resolventIntegralPlus U_grp φ =
                  φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ := by
    unfold resolventIntegralPlus
    rw [smul_smul, mul_neg, I_mul_I, neg_neg, one_smul]
  rw [h_target]
  have h_scalar : ∀ h : ℝ, h ≠ 0 → ((I * (h : ℂ))⁻¹ * (-I) : ℂ) = -(h : ℂ)⁻¹ := by
    intro h _
    calc ((I * (h : ℂ))⁻¹ * (-I) : ℂ)
        = (h : ℂ)⁻¹ * I⁻¹ * (-I) := by rw [mul_inv_rev]
      _ = (h : ℂ)⁻¹ * (I⁻¹ * (-I)) := by rw [mul_assoc]
      _ = (h : ℂ)⁻¹ * (-(I⁻¹ * I)) := by rw [mul_neg]
      _ = (h : ℂ)⁻¹ * (-1) := by rw [inv_mul_cancel₀ I_ne_zero]
      _ = -(h : ℂ)⁻¹ := by rw [mul_neg_one]
  have h_compl : ({0} : Set ℝ)ᶜ = Set.Ioi 0 ∪ Set.Iio 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · intro hx
      by_cases h : x > 0
      · left; exact h
      · right; push_neg at h; exact lt_of_le_of_ne h hx
    · intro hx
      cases hx with
      | inl h => linarith
      | inr h => linarith
  rw [show (𝓝[≠] (0 : ℝ)) = 𝓝[Set.Ioi 0 ∪ Set.Iio 0] 0 from by rw [← h_compl]]
  rw [nhdsWithin_union]
  apply Tendsto.sup
  · have h_eq : ∀ h : ℝ, h > 0 → ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
                                                   resolventIntegralPlus U_grp φ) =
                         (-(h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) -
                         (-(h : ℂ)⁻¹ • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ) := by
      intro h hh
      rw [unitary_shift_resolventIntegralPlus U_grp φ h hh]
      rw [smul_sub, smul_smul, smul_smul, h_scalar h (ne_of_gt hh)]
    have h_eq' : ∀ h : ℝ, h > 0 → ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
                                                   resolventIntegralPlus U_grp φ) =
                         -((h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) +
                         ((h : ℂ)⁻¹ • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ) := by
      intro h hh
      rw [h_eq h hh]
      rw [neg_smul, neg_smul, sub_neg_eq_add]
    apply Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact (h_eq' h hh).symm
    rw [show φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ =
            -(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) + φ by abel]
    apply Tendsto.add
    · apply Tendsto.neg
      have he : Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[>] 0) (𝓝 1) :=
        tendsto_exp_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
      have hi : Tendsto (fun h : ℝ => ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ)
                        (𝓝[>] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) :=
        (tendsto_integral_Ici_exp_unitary U_grp φ).mono_left nhdsWithin_le_nhds
      have he_cplx : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ)) (𝓝[>] 0) (𝓝 1) := by
        convert Tendsto.comp (continuous_ofReal.tendsto 1) he using 1
        ext h
        simp only [Function.comp_apply, ofReal_div, ofReal_sub, ofReal_one]
      have h_prod : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ)
                            (𝓝[>] 0) (𝓝 ((1 : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) :=
        Tendsto.smul he_cplx hi
      simp only [one_smul] at h_prod
      apply Tendsto.congr' _ h_prod
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [div_eq_inv_mul]
      conv_lhs =>
        rw [show (↑(Real.exp h) : ℂ) - 1 = ↑(Real.exp h - 1) from by rw [ofReal_sub, ofReal_one]]
        rw [← smul_smul]
      exact rfl
    · exact tendsto_average_integral_unitary U_grp φ
  · have h_eq : ∀ h : ℝ, h < 0 → ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
                                                   resolventIntegralPlus U_grp φ) =
                         (-(h : ℂ)⁻¹ • Real.exp h • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ) +
                         (-(h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) := by
      intro h hh
      rw [unitary_shift_resolventIntegralPlus_neg U_grp φ h hh]
      rw [smul_add, smul_smul, smul_smul, h_scalar h (ne_of_lt hh)]
    apply Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact (h_eq h hh).symm
    rw [show φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ =
            φ + (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) by abel]
    apply Tendsto.add
    · have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U t φ) :=
        (Real.continuous_exp.comp continuous_neg).smul (U_grp.strong_continuous φ)
      have h_f0 : Real.exp (-(0 : ℝ)) • U_grp.U 0 φ = φ := by
        simp only [neg_zero, Real.exp_zero, one_smul]
        rw [U_grp.identity]
        simp only [ContinuousLinearMap.id_apply]
      have he : Tendsto (fun h : ℝ => Real.exp h) (𝓝[<] 0) (𝓝 1) := by
        rw [← Real.exp_zero]
        exact Real.continuous_exp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h_flip : ∀ h : ℝ, h < 0 → -(h : ℂ)⁻¹ • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ =
                             ((-h) : ℂ)⁻¹ • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ := by
        intro h hh
        congr 1
        exact neg_inv
      have he : Tendsto (fun h : ℝ => Real.exp h) (𝓝[<] 0) (𝓝 1) := by
        rw [← Real.exp_zero]
        exact Real.continuous_exp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h_avg := tendsto_average_integral_unitary_neg U_grp φ
      have h_comb : Tendsto (fun h : ℝ => Real.exp h • (((-h)⁻¹ : ℂ) • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ))
                            (𝓝[<] 0) (𝓝 ((1 : ℝ) • φ)) := by
        have he' : Tendsto (fun h : ℝ => Real.exp h) (𝓝[<] 0) (𝓝 (1 : ℝ)) := by
          rw [← Real.exp_zero]
          exact Real.continuous_exp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        exact Tendsto.smul he' h_avg
      simp only [one_smul] at h_comb
      apply Tendsto.congr' _ h_comb
      filter_upwards [self_mem_nhdsWithin] with h hh
      rw [smul_comm, @inv_neg]
    · have he : Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[<] 0) (𝓝 1) :=
        tendsto_exp_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))
      have he_cplx : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ)) (𝓝[<] 0) (𝓝 1) := by
        convert Tendsto.comp (continuous_ofReal.tendsto 1) he using 1
        ext h
        simp only [Function.comp_apply, ofReal_div, ofReal_sub, ofReal_one]
      have h_prod : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)
                            (𝓝[<] 0) (𝓝 ((1 : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) :=
        Tendsto.smul he_cplx tendsto_const_nhds
      simp only [one_smul] at h_prod
      have h_inner : Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)
                             (𝓝[<] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) := by
        apply Tendsto.congr' _ h_prod
        filter_upwards [self_mem_nhdsWithin] with h hh
        simp only [div_eq_inv_mul]
        conv_lhs =>
          rw [show (↑(Real.exp h) : ℂ) - 1 = ↑(Real.exp h - 1) from by rw [ofReal_sub, ofReal_one]]
          rw [← smul_smul]
        rw [@Complex.coe_smul]
      apply Tendsto.congr' _ h_inner.neg
      filter_upwards with h
      rw [neg_smul]

lemma unitary_shift_resolventIntegralMinus (φ : H) (h : ℝ) (hh : h > 0) :
    U_grp.U h (resolventIntegralMinus U_grp φ) - resolventIntegralMinus U_grp φ =
    I • (Real.exp (-h) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) +
    I • ((Real.exp (-h) - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) := by
  unfold resolventIntegralMinus
  have h_int := integrable_exp_neg_unitary_neg U_grp φ
  rw [ContinuousLinearMap.map_smul]
  have h_comm : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) =
                ∫ t in Set.Ici 0, U_grp.U h (Real.exp (-t) • U_grp.U (-t) φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  rw [h_comm]
  have h_shift : ∀ t, U_grp.U h (Real.exp (-t) • U_grp.U (-t) φ) =
                      Real.exp (-t) • U_grp.U (h - t) φ := by
    intro t
    rw [ContinuousLinearMap.map_smul_of_tower]
    congr 1
    have := U_grp.group_law h (-t)
    simp only at this
    exact congrFun (congrArg DFunLike.coe this).symm φ
  simp_rw [h_shift]
  have h_exp : ∀ t, Real.exp (-t) • U_grp.U (h - t) φ =
                    Real.exp (-h) • (Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ) := by
    intro t
    rw [← smul_assoc, smul_eq_mul, ← Real.exp_add]
    congr 1
    · ring_nf
    · ring_nf
  simp_rw [h_exp]
  have h_smul_comm : ∫ t in Set.Ici 0, Real.exp (-h) • (Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ) =
                     Real.exp (-h) • ∫ t in Set.Ici 0, Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ := by
    exact integral_smul (Real.exp (-h)) fun a => Real.exp (-(a - h)) • (U_grp.U (-(a - h))) φ
  rw [h_smul_comm]
  have h_subst : ∫ t in Set.Ici 0, Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ =
                 ∫ s in Set.Ici (-h), Real.exp (-s) • U_grp.U (-s) φ := by
    have h_preimage : (· - h) ⁻¹' (Set.Ici (-h)) = Set.Ici 0 := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ici]
      constructor
      · intro ht; linarith
      · intro ht; linarith
    have h_map : Measure.map (· - h) volume = (volume : Measure ℝ) :=
      (measurePreserving_sub_right volume h).map_eq
    have h_meas_set : MeasurableSet (Set.Ici (-h)) := measurableSet_Ici
    have h_cont : Continuous (fun s => Real.exp (-s) • U_grp.U (-s) φ) :=
      ((Real.continuous_exp.comp continuous_neg).smul
       ((U_grp.strong_continuous φ).comp continuous_neg))
    have h_f_meas : AEStronglyMeasurable (fun s => Real.exp (-s) • U_grp.U (-s) φ)
                      (Measure.map (· - h) volume) := by
      rw [h_map]
      exact h_cont.aestronglyMeasurable
    have h_g_meas : AEMeasurable (· - h) volume := (measurable_sub_const h).aemeasurable
    rw [← h_map, MeasureTheory.setIntegral_map h_meas_set h_f_meas h_g_meas, h_preimage]
    congr 1
    ext t
    exact congrFun (congrArg DFunLike.coe (congrFun (congrArg restrict h_map) (Set.Ici 0))) t
  rw [h_subst]
  have h_split : ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ =
                 (∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) +
                 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) := by
    have h_ae_eq1 : ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ =
                    ∫ t in Set.Ioi (-h), Real.exp (-t) • U_grp.U (-t) φ :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_ae_eq2 : ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ =
                    ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U (-t) φ :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_union : Set.Ioi (-h) = Set.Ioc (-h) 0 ∪ Set.Ioi 0 := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro hx
        by_cases hx0 : x ≤ 0
        · left; exact ⟨hx, hx0⟩
        · right; linarith
      · intro hx
        cases hx with
        | inl hx => exact hx.1
        | inr hx => linarith [hh, hx]
    have h_disj : Disjoint (Set.Ioc (-h) 0) (Set.Ioi 0) := Set.Ioc_disjoint_Ioi le_rfl
    have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U (-t) φ) :=
      ((Real.continuous_exp.comp continuous_neg).smul
       ((U_grp.strong_continuous φ).comp continuous_neg))
    rw [h_ae_eq1, h_union, setIntegral_union h_disj measurableSet_Ioi
        (h_cont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (h_int.mono_set Set.Ioi_subset_Ici_self), h_ae_eq2.symm]
  rw [h_split, smul_add]
  set X := ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ with hX_def
  set Y := ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ with hY_def
  calc I • (Real.exp (-h) • X + Real.exp (-h) • Y) - I • Y
      = I • Real.exp (-h) • X + I • Real.exp (-h) • Y - I • Y := by rw [smul_add]
    _ = I • Real.exp (-h) • X + (I • Real.exp (-h) • Y - I • Y) := by abel
    _ = I • Real.exp (-h) • X + I • (Real.exp (-h) • Y - Y) := by rw [← smul_sub]
    _ = I • Real.exp (-h) • X + I • ((Real.exp (-h) - 1) • Y) := by rw [sub_smul, one_smul]
    _ = I • (Real.exp (-h) • X) + I • ((Real.exp (-h) - 1) • Y) := by rw [hX_def]

lemma unitary_shift_resolventIntegralMinus_neg (φ : H) (h : ℝ) (hh : h < 0) :
    U_grp.U h (resolventIntegralMinus U_grp φ) - resolventIntegralMinus U_grp φ =
    I • ((Real.exp (-h) - 1) • ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ) -
    I • ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ := by
  unfold resolventIntegralMinus
  have h_int := integrable_exp_neg_unitary_neg U_grp φ
  rw [ContinuousLinearMap.map_smul]
  have h_comm : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) =
                ∫ t in Set.Ici 0, U_grp.U h (Real.exp (-t) • U_grp.U (-t) φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  rw [h_comm]
  have h_shift : ∀ t, U_grp.U h (Real.exp (-t) • U_grp.U (-t) φ) =
                      Real.exp (-t) • U_grp.U (h - t) φ := by
    intro t
    rw [ContinuousLinearMap.map_smul_of_tower]
    congr 1
    have := U_grp.group_law h (-t)
    simp only at this
    exact congrFun (congrArg DFunLike.coe (id (Eq.symm this))) φ
  simp_rw [h_shift]
  have h_exp : ∀ t, Real.exp (-t) • U_grp.U (h - t) φ =
                    Real.exp (-h) • (Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ) := by
    intro t
    rw [← smul_assoc, smul_eq_mul, ← Real.exp_add]
    congr 1
    · ring_nf
    · ring_nf
  simp_rw [h_exp]
  have h_smul_comm : ∫ t in Set.Ici 0, Real.exp (-h) • (Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ) =
                     Real.exp (-h) • ∫ t in Set.Ici 0, Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ := by
    exact integral_smul (Real.exp (-h)) fun a => Real.exp (-(a - h)) • (U_grp.U (-(a - h))) φ
  rw [h_smul_comm]
  have h_subst : ∫ t in Set.Ici 0, Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ =
                 ∫ s in Set.Ici (-h), Real.exp (-s) • U_grp.U (-s) φ := by
    have h_preimage : (· - h) ⁻¹' (Set.Ici (-h)) = Set.Ici 0 := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ici]
      constructor
      · intro ht; linarith
      · intro ht; linarith
    have h_map : Measure.map (· - h) volume = (volume : Measure ℝ) :=
      (measurePreserving_sub_right volume h).map_eq
    have h_meas_set : MeasurableSet (Set.Ici (-h)) := measurableSet_Ici
    have h_cont : Continuous (fun s => Real.exp (-s) • U_grp.U (-s) φ) :=
      ((Real.continuous_exp.comp continuous_neg).smul
       ((U_grp.strong_continuous φ).comp continuous_neg))
    have h_f_meas : AEStronglyMeasurable (fun s => Real.exp (-s) • U_grp.U (-s) φ)
                      (Measure.map (· - h) volume) := by
      rw [h_map]
      exact h_cont.aestronglyMeasurable
    have h_g_meas : AEMeasurable (· - h) volume := (measurable_sub_const h).aemeasurable
    rw [← h_map, MeasureTheory.setIntegral_map h_meas_set h_f_meas h_g_meas, h_preimage]
    congr 1
    ext t
    exact congrFun (congrArg DFunLike.coe (congrFun (congrArg restrict h_map) (Set.Ici 0))) t
  rw [h_subst]
  have h_neg_pos : -h > 0 := neg_pos.mpr hh
  have h_split : ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ =
                 (∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ) +
                 (∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ) := by
    have h_ae_eq1 : ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ =
                    ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U (-t) φ :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_ae_eq2 : ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ =
                    ∫ t in Set.Ioi (-h), Real.exp (-t) • U_grp.U (-t) φ :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_union : Set.Ioi 0 = Set.Ioc 0 (-h) ∪ Set.Ioi (-h) := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro hx
        by_cases hxh : x ≤ -h
        · left; exact ⟨hx, hxh⟩
        · right; linarith
      · intro hx
        cases hx with
        | inl hx => exact hx.1
        | inr hx => linarith [h_neg_pos, hx]
    have h_disj : Disjoint (Set.Ioc 0 (-h)) (Set.Ioi (-h)) := Set.Ioc_disjoint_Ioi le_rfl
    have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U (-t) φ) :=
      ((Real.continuous_exp.comp continuous_neg).smul
       ((U_grp.strong_continuous φ).comp continuous_neg))
    rw [h_ae_eq1, h_union, setIntegral_union h_disj measurableSet_Ioi
        (h_cont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (h_int.mono_set (Set.Ioi_subset_Ici h_neg_pos.le)), h_ae_eq2.symm]
  rw [h_split]
  set X := ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ with hX_def
  set Y := ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ with hY_def
  rw [smul_add]
  calc  I • Real.exp (-h) • Y - (I • X + I • Y)
      = I • Real.exp (-h) • Y - I • X - I • Y := by exact sub_add_eq_sub_sub (I • Real.exp (-h) • Y) (I • X) (I • Y)
    _ = I • Real.exp (-h) • Y - I • Y - I • X := by abel
    _ = I • (Real.exp (-h) • Y - Y) - I • X := by rw [← smul_sub]
    _ = I • ((Real.exp (-h) - 1) • Y) - I • X := by rw [sub_smul, one_smul]
    _ = I • (Real.exp (-h) - 1) • Y - I • X := by exact rfl

lemma generator_limit_resolventIntegralMinus (φ : H) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) -
                                              resolventIntegralMinus U_grp φ))
            (𝓝[≠] 0)
            (𝓝 (φ + I • resolventIntegralMinus U_grp φ)) := by
  have h_target : φ + I • resolventIntegralMinus U_grp φ =
                  φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ := by
    unfold resolventIntegralMinus
    rw [smul_smul, I_mul_I, neg_one_smul, sub_eq_add_neg]
  rw [h_target]
  have h_scalar : ∀ h : ℝ, h ≠ 0 → ((I * (h : ℂ))⁻¹ * I : ℂ) = (h : ℂ)⁻¹ := by
    intro h _
    calc ((I * (h : ℂ))⁻¹ * I : ℂ)
        = (h : ℂ)⁻¹ * I⁻¹ * I := by rw [mul_inv_rev]
      _ = (h : ℂ)⁻¹ * (I⁻¹ * I) := by rw [mul_assoc]
      _ = (h : ℂ)⁻¹ * 1 := by rw [inv_mul_cancel₀ I_ne_zero]
      _ = (h : ℂ)⁻¹ := by rw [mul_one]
  have h_compl : ({0} : Set ℝ)ᶜ = Set.Ioi 0 ∪ Set.Iio 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · intro hx
      by_cases h : x > 0
      · left; exact h
      · right; push_neg at h; exact lt_of_le_of_ne h hx
    · intro hx
      cases hx with
      | inl h => linarith
      | inr h => linarith
  rw [show (𝓝[≠] (0 : ℝ)) = 𝓝[Set.Ioi 0 ∪ Set.Iio 0] 0 from by rw [← h_compl]]
  rw [nhdsWithin_union]
  apply Tendsto.sup
  · have h_eq : ∀ h : ℝ, h > 0 → ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) -
                                                   resolventIntegralMinus U_grp φ) =
                         ((h : ℂ)⁻¹ • Real.exp (-h) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) +
                         ((h : ℂ)⁻¹ • (Real.exp (-h) - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) := by
      intro h hh
      rw [unitary_shift_resolventIntegralMinus U_grp φ h hh]
      rw [smul_add, smul_smul, smul_smul, h_scalar h (ne_of_gt hh)]
    apply Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact (h_eq h hh).symm
    rw [show φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ =
            φ + (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) by abel]
    apply Tendsto.add
    · have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U (-t) φ) :=
        ((Real.continuous_exp.comp continuous_neg).smul
         ((U_grp.strong_continuous φ).comp continuous_neg))
      have h_f0 : Real.exp (-(0 : ℝ)) • U_grp.U (-(0 : ℝ)) φ = φ := by
        simp only [neg_zero, Real.exp_zero, one_smul]
        rw [U_grp.identity]
        simp only [ContinuousLinearMap.id_apply]
      have he : Tendsto (fun h : ℝ => Real.exp (-h)) (𝓝[>] 0) (𝓝 1) := by
        have h1 : Tendsto (fun h : ℝ => -h) (𝓝 (0 : ℝ)) (𝓝 0) := by
          convert (continuous_neg (G := ℝ)).tendsto 0 using 1
          simp
        have h2 : Tendsto Real.exp (𝓝 0) (𝓝 1) := by
          rw [← Real.exp_zero]
          exact Real.continuous_exp.tendsto 0
        exact (h2.comp h1).mono_left nhdsWithin_le_nhds
      have h_avg : Tendsto (fun h : ℝ => (h⁻¹ : ℂ) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ)
                           (𝓝[>] 0) (𝓝 φ) := by
        have h_eq_int : ∀ h > 0, ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ =
                                 ∫ t in (-h)..0, Real.exp (-t) • U_grp.U (-t) φ := by
          intro h hh
          rw [intervalIntegral.integral_of_le (by linarith : -h ≤ 0)]
        have h_deriv : HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, Real.exp (-t) • U_grp.U (-t) φ)
                                  (Real.exp (-(0 : ℝ)) • U_grp.U (-(0 : ℝ)) φ) 0 := by
          apply intervalIntegral.integral_hasDerivAt_right
          · exact h_cont.intervalIntegrable 0 0
          · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
          · exact h_cont.continuousAt
        rw [h_f0] at h_deriv
        have h_F0 : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U (-t) φ = 0 :=
          intervalIntegral.integral_same
        have h_tendsto_real : Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U (-t) φ)
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
        have tendsto_neg_Ioi : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
          rw [tendsto_nhdsWithin_iff]
          constructor
          · have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
              convert (continuous_neg (G := ℝ)).tendsto 0 using 1
              simp
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with h hh
            simp only [Set.mem_Iio, Left.neg_neg_iff]
            exact hh
        have h_neg_tendsto := h_tendsto_real.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx)) |>.comp tendsto_neg_Ioi
        apply Tendsto.congr' _ h_neg_tendsto
        filter_upwards [self_mem_nhdsWithin] with h hh
        rw [h_eq_int h hh]
        simp only [Function.comp_apply]
        rw [intervalIntegral.integral_symm (-h) 0]
        rw [smul_neg]
        rw [neg_eq_iff_eq_neg, ← neg_smul]
        rw [(Complex.coe_smul (-h)⁻¹ _).symm]
        congr 1
        simp only [ofReal_inv, ofReal_neg, neg_inv]
      have h_comb : Tendsto (fun h : ℝ => Real.exp (-h) • ((h⁻¹ : ℂ) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ))
                            (𝓝[>] 0) (𝓝 ((1 : ℝ) • φ)) := by
        exact Tendsto.smul he h_avg
      simp only [one_smul] at h_comb
      apply Tendsto.congr' _ h_comb
      filter_upwards [self_mem_nhdsWithin] with h hh
      rw [smul_comm]
    · have he : Tendsto (fun h : ℝ => (Real.exp (-h) - 1) / h) (𝓝[>] 0) (𝓝 (-1)) := by
        have tendsto_neg_Ioi : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
          rw [tendsto_nhdsWithin_iff]
          constructor
          · have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
              convert (continuous_neg (G := ℝ)).tendsto 0 using 1
              simp
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with h hh
            simp only [Set.mem_Iio, Left.neg_neg_iff]
            exact hh
        have h1 : Tendsto (fun h : ℝ => (Real.exp (-h) - 1) / (-h) * (-1)) (𝓝[>] 0) (𝓝 (1 * (-1))) := by
          apply Tendsto.mul
          · have := (tendsto_exp_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))).comp tendsto_neg_Ioi
            simp only at this
            convert this using 1
          · exact tendsto_const_nhds
        simp only [mul_neg_one] at h1
        convert h1 using 1
        ext h
        by_cases hh : h = 0
        · simp [hh]
        · field_simp
      have he_cplx : Tendsto (fun h : ℝ => ((Real.exp (-h) - 1) / h : ℂ)) (𝓝[>] 0) (𝓝 (-1)) := by
        convert Tendsto.comp (continuous_ofReal.tendsto (-1)) he using 1
        ext h
        simp only [Function.comp_apply, ofReal_div, ofReal_sub, ofReal_one]
        simp_all only [ne_eq, mul_inv_rev, inv_I, mul_neg, neg_mul, gt_iff_lt, neg_smul, ofReal_neg, ofReal_one]
      have h_prod : Tendsto (fun h : ℝ => ((Real.exp (-h) - 1) / h : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)
                            (𝓝[>] 0) (𝓝 ((-1 : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) :=
        Tendsto.smul he_cplx tendsto_const_nhds
      simp only [neg_one_smul] at h_prod
      apply Tendsto.congr' _ h_prod
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [div_eq_inv_mul]
      conv_lhs =>
        rw [show (↑(Real.exp (-h)) : ℂ) - 1 = ↑(Real.exp (-h) - 1) from by rw [ofReal_sub, ofReal_one]]
        rw [← smul_smul]
      rw [@Complex.coe_smul]
  · have h_eq : ∀ h : ℝ, h < 0 → ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) -
                                                   resolventIntegralMinus U_grp φ) =
                         ((h : ℂ)⁻¹ • (Real.exp (-h) - 1) • ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ) +
                         (-(h : ℂ)⁻¹ • ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ) := by
      intro h hh
      rw [unitary_shift_resolventIntegralMinus_neg U_grp φ h hh]
      rw [smul_sub, smul_smul, smul_smul, h_scalar h (ne_of_lt hh)]
      rw [sub_eq_add_neg, neg_smul]
    apply Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact (h_eq h hh).symm
    rw [show φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ =
            (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) + φ by abel]
    apply Tendsto.add
    · have he : Tendsto (fun h : ℝ => (Real.exp (-h) - 1) / h) (𝓝[<] 0) (𝓝 (-1)) := by
        have tendsto_neg_Iio : Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝[>] 0) := by
          rw [tendsto_nhdsWithin_iff]
          constructor
          · have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
              convert (continuous_neg (G := ℝ)).tendsto 0 using 1
              simp
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with h hh
            simp only [Set.mem_Ioi, Left.neg_pos_iff]
            exact hh
        have h1 : Tendsto (fun h : ℝ => (Real.exp (-h) - 1) / (-h) * (-1)) (𝓝[<] 0) (𝓝 (1 * (-1))) := by
          apply Tendsto.mul
          · have := (tendsto_exp_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))).comp tendsto_neg_Iio
            simp only at this
            convert this using 1
          · exact tendsto_const_nhds
        simp only [mul_neg_one] at h1
        convert h1 using 1
        ext h
        by_cases hh : h = 0
        · simp [hh]
        · field_simp
      have he_cplx : Tendsto (fun h : ℝ => ((Real.exp (-h) - 1) / h : ℂ)) (𝓝[<] 0) (𝓝 (-1)) := by
        convert Tendsto.comp (continuous_ofReal.tendsto (-1)) he using 1
        ext h
        simp only [Function.comp_apply, ofReal_div, ofReal_sub, ofReal_one]
        rw [ofReal_neg]
        exact rfl
      have hi : Tendsto (fun h : ℝ => ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ)
                        (𝓝[<] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) := by
        have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U (-t) φ) :=
          ((Real.continuous_exp.comp continuous_neg).smul
           ((U_grp.strong_continuous φ).comp continuous_neg))
        have h_int := integrable_exp_neg_unitary_neg U_grp φ
        have h_prim_cont : Continuous (fun a => ∫ t in (0 : ℝ)..a, Real.exp (-t) • U_grp.U (-t) φ) :=
          intervalIntegral.continuous_primitive (fun a b => h_cont.intervalIntegrable a b) 0
        have h_prim_zero : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U (-t) φ = 0 :=
          intervalIntegral.integral_same
        have h_prim_tendsto : Tendsto (fun a => ∫ t in (0 : ℝ)..a, Real.exp (-t) • U_grp.U (-t) φ)
                                      (𝓝 0) (𝓝 0) := by
          rw [← h_prim_zero]
          exact h_prim_cont.tendsto 0
        have h_split : ∀ h < 0, ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ =
                                (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) -
                                ∫ t in (0 : ℝ)..(-h), Real.exp (-t) • U_grp.U (-t) φ := by
          intro h hh
          have h_neg_pos : -h > 0 := neg_pos.mpr hh
          have h_ae_eq1 : ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ =
                          ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U (-t) φ :=
            setIntegral_congr_set Ioi_ae_eq_Ici.symm
          have h_ae_eq2 : ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ =
                          ∫ t in Set.Ioi (-h), Real.exp (-t) • U_grp.U (-t) φ :=
            setIntegral_congr_set Ioi_ae_eq_Ici.symm
          have h_union : Set.Ioi 0 = Set.Ioc 0 (-h) ∪ Set.Ioi (-h) := by
            ext x
            simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
            constructor
            · intro hx
              by_cases hxh : x ≤ -h
              · left; exact ⟨hx, hxh⟩
              · right; linarith
            · intro hx
              cases hx with
              | inl hx => exact hx.1
              | inr hx => linarith [h_neg_pos, hx]
          have h_disj : Disjoint (Set.Ioc 0 (-h)) (Set.Ioi (-h)) := Set.Ioc_disjoint_Ioi le_rfl
          have h_eq1 : ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U (-t) φ =
                       (∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ) +
                       ∫ t in Set.Ioi (-h), Real.exp (-t) • U_grp.U (-t) φ := by
            rw [h_union, setIntegral_union h_disj measurableSet_Ioi
                (h_cont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
                (h_int.mono_set (Set.Ioi_subset_Ici h_neg_pos.le))]
          have h_eq2 : ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ =
                       ∫ t in (0 : ℝ)..(-h), Real.exp (-t) • U_grp.U (-t) φ := by
            rw [intervalIntegral.integral_of_le h_neg_pos.le]
          rw [h_ae_eq1, h_eq1, h_ae_eq2.symm, h_eq2]
          ring_nf
          exact
            Eq.symm
              (add_sub_cancel_left (∫ (t : ℝ) in 0..-h, Real.exp (-t) • (U_grp.U (-t)) φ)
                (∫ (t : ℝ) in Set.Ici (-h), Real.exp (-t) • (U_grp.U (-t)) φ))
        have h_int_tendsto : Tendsto (fun h : ℝ => ∫ t in (0 : ℝ)..(-h), Real.exp (-t) • U_grp.U (-t) φ)
                                     (𝓝[<] 0) (𝓝 0) := by
          have h_neg_tendsto : Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝 0) := by
            have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
              convert (continuous_neg (G := ℝ)).tendsto 0 using 1
              simp
            exact this.mono_left nhdsWithin_le_nhds
          have := h_prim_tendsto.comp h_neg_tendsto
          simp only at this
          convert this using 1
        have h_combined : Tendsto (fun h : ℝ => (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) -
                                                 ∫ t in (0 : ℝ)..(-h), Real.exp (-t) • U_grp.U (-t) φ)
                                  (𝓝[<] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) := by
          convert tendsto_const_nhds.sub h_int_tendsto using 1
          simp only [sub_zero]
        apply Tendsto.congr' _ h_combined
        filter_upwards [self_mem_nhdsWithin] with h hh
        exact (h_split h hh).symm
      have h_prod : Tendsto (fun h : ℝ => ((Real.exp (-h) - 1) / h : ℂ) • ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ)
                            (𝓝[<] 0) (𝓝 ((-1 : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) :=
        Tendsto.smul he_cplx hi
      simp only [neg_one_smul] at h_prod
      apply Tendsto.congr' _ h_prod
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [div_eq_inv_mul]
      conv_lhs =>
        rw [show (↑(Real.exp (-h)) : ℂ) - 1 = ↑(Real.exp (-h) - 1) from by rw [ofReal_sub, ofReal_one]]
        rw [← smul_smul]
      rw [@Complex.coe_smul]
    · have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U (-t) φ) :=
        ((Real.continuous_exp.comp continuous_neg).smul
         ((U_grp.strong_continuous φ).comp continuous_neg))
      have h_f0 : Real.exp (-(0 : ℝ)) • U_grp.U (-(0 : ℝ)) φ = φ := by
        simp only [neg_zero, Real.exp_zero, one_smul]
        rw [U_grp.identity]
        simp only [ContinuousLinearMap.id_apply]
      have h_avg : Tendsto (fun h : ℝ => (h⁻¹ : ℂ) • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U (-t) φ)
                           (𝓝[>] 0) (𝓝 φ) := by
        have h_eq_int : ∀ h > 0, ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U (-t) φ =
                                 ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U (-t) φ := by
          intro h hh
          rw [intervalIntegral.integral_of_le (le_of_lt hh)]
        have h_deriv : HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, Real.exp (-t) • U_grp.U (-t) φ)
                                  (Real.exp (-(0 : ℝ)) • U_grp.U (-(0 : ℝ)) φ) 0 := by
          apply intervalIntegral.integral_hasDerivAt_right
          · exact h_cont.intervalIntegrable 0 0
          · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
          · exact h_cont.continuousAt
        rw [h_f0] at h_deriv
        have h_F0 : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U (-t) φ = 0 :=
          intervalIntegral.integral_same
        have h_tendsto_real : Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U (-t) φ)
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
        rw [h_eq_int h hh, (Complex.coe_smul h⁻¹ _).symm, ofReal_inv]
      have tendsto_neg_Iio : Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝[>] 0) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
            convert (continuous_neg (G := ℝ)).tendsto 0 using 1
            simp
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with h hh
          simp only [Set.mem_Ioi, Left.neg_pos_iff]
          exact hh
      have h_comp := h_avg.comp tendsto_neg_Iio
      apply Tendsto.congr' _ h_comp
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [Function.comp_apply]
      rw [show -(h : ℂ)⁻¹ = ((-h) : ℂ)⁻¹ from by rw [@neg_inv]]
      simp only [ofReal_neg, inv_neg, neg_smul]

end GeneratorLimit

section GeneratorConstruction

open Classical
open InnerProductSpace
variable (U_grp : OneParameterUnitaryGroup (H := H))

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
          exact rfl
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

section Bridge

variable (U_grp : OneParameterUnitaryGroup (H := H))

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

end Bridge

section Appendix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma fubini_Ioc (f : ℝ → ℝ → E) (a b c d : ℝ)
    (hf : Integrable (Function.uncurry f) ((volume.restrict (Set.Ioc a b)).prod
                                           (volume.restrict (Set.Ioc c d)))) :
    ∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d, f x y =
    ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, f x y := by
  exact MeasureTheory.integral_integral_swap hf

lemma tendsto_integral_of_dominated_convergence
    (f : ℕ → ℝ → E) (g : ℝ → E) (bound : ℝ → ℝ)
    (S : Set ℝ)
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict S))
    (hbound : ∀ n, ∀ᵐ x ∂(volume.restrict S), ‖f n x‖ ≤ bound x)
    (hbound_int : Integrable bound (volume.restrict S))
    (hf_tendsto : ∀ᵐ x ∂(volume.restrict S), Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x in S, f n x) atTop (𝓝 (∫ x in S, g x)) := by
  exact MeasureTheory.tendsto_integral_of_dominated_convergence bound hf_meas hbound_int hbound hf_tendsto

end Appendix

end QuantumMechanics.Bochner
