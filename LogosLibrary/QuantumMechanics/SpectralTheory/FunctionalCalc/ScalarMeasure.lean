/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.SpectralProjection
/-!
# Spectral Scalar Measure Properties

This file develops properties of the spectral scalar measure `μ_ψ(B) = ‖E(B)ψ‖²`,
which encodes how the "spectral weight" of a vector `ψ` is distributed across the
spectrum.

## Main definitions

* `finite_measure_countable_atoms`: Finite measures have at most countably many atoms
* `measurable_of_countable_support`: Functions with countable support are measurable

## Main results

* `spectral_inner_measurable`: `s ↦ ⟪E{s}ψ, ψ⟫` is measurable
* `spectral_scalar_measure_zero`: `μ_0(B) = 0`
* `spectral_scalar_measure_smul`: `μ_{cψ}(B) = |c|² μ_ψ(B)`
* `spectral_scalar_measure_add`: Expansion formula for `μ_{x+y}(B)`
* `spectral_scalar_measure_sub`: Expansion formula for `μ_{x-y}(B)`
* `spectral_scalar_measure_eq_norm_sq`: `μ_ψ(B) = ‖E(B)ψ‖²`
* `spectral_scalar_measure_univ`: `μ_ψ(ℝ) = ‖ψ‖²`
* `spectral_scalar_measure_mono`: Monotonicity under set inclusion
* `spectral_scalar_measure_compl`: Complement formula

## Tags

spectral measure, scalar measure, spectral weight
-/

namespace FunctionalCalculus

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory InnerProductSpace Complex QuantumMechanics.Cayley SpectralBridge.Resolvent SpectralBridge.Bochner QuantumMechanics.Generators ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## Countable Atoms and Measurability
-/

/-- A finite measure on `ℝ` has at most countably many atoms. That is, the set
    `{s : ℝ | μ({s}) ≠ 0}` is countable. This is a key ingredient for proving
    measurability of `s ↦ ⟪E{s}ψ, ψ⟫`. -/
lemma finite_measure_countable_atoms (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Set.Countable {s | μ {s} ≠ 0} := by
  have h_finite : ∀ n : ℕ, Set.Finite {s : ℝ | μ {s} ≥ (1 : ENNReal) / (n + 1)} := by
    intro n
    by_contra h_inf
    have h_infinite : Set.Infinite {s : ℝ | μ {s} ≥ (1 : ENNReal) / (n + 1)} := h_inf
    haveI : Infinite {s : ℝ | μ {s} ≥ (1 : ENNReal) / (n + 1)} := h_infinite.to_subtype
    have h_sum_top : ∑' (_ : {s : ℝ | μ {s} ≥ (1 : ENNReal) / (n + 1)}), (1 : ENNReal) / (n + 1) = ⊤ := by
      apply ENNReal.tsum_const_eq_top_of_ne_zero
      simp only [one_div, ne_eq, ENNReal.inv_eq_zero]
      exact not_eq_of_beq_eq_false rfl
    have h_le : ∑' (_ : {s : ℝ | μ {s} ≥ (1 : ENNReal) / (n + 1)}), (1 : ENNReal) / (n + 1) ≤
                ∑' (x : {s : ℝ | μ {s} ≥ (1 : ENNReal) / (n + 1)}), μ {(x : ℝ)} := by
      apply ENNReal.tsum_le_tsum
      intro ⟨x, hx⟩
      exact hx
    have h_le_univ : ∑' (x : {s : ℝ | μ {s} ≥ (1 : ENNReal) / (n + 1)}), μ {(x : ℝ)} ≤ μ Set.univ := by
      have h_disj : Pairwise (Function.onFun Disjoint (fun (x : {s : ℝ | μ {s} ≥ (1 : ENNReal) / (n + 1)}) => ({(x : ℝ)} : Set ℝ))) := by
        intro i j hij
        simp only [Function.onFun, Set.disjoint_singleton]
        exact fun h => hij (Subtype.ext h)
      have h_meas : ∀ (i : {s : ℝ | μ {s} ≥ (1 : ENNReal) / (n + 1)}), MeasurableSet {(i : ℝ)} :=
        fun i => MeasurableSet.singleton _
      calc ∑' (x : {s : ℝ | μ {s} ≥ (1 : ENNReal) / (n + 1)}), μ {(x : ℝ)}
          ≤ μ (⋃ (x : {s : ℝ | μ {s} ≥ (1 : ENNReal) / (n + 1)}), {(x : ℝ)}) :=
            tsum_meas_le_meas_iUnion_of_disjoint μ h_meas h_disj
        _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    have h_top : μ Set.univ = ⊤ := by
      rw [h_sum_top] at h_le
      exact top_unique (le_trans h_le h_le_univ)
    exact measure_ne_top μ Set.univ h_top
  have h_subset : {s | μ {s} ≠ 0} ⊆ ⋃ n : ℕ, {s | μ {s} ≥ (1 : ENNReal) / (n + 1)} := by
    intro s hs
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    have hpos : 0 < μ {s} := pos_iff_ne_zero.mpr hs
    by_contra h_neg
    push_neg at h_neg
    have h_zero : μ {s} = 0 := by
      apply le_antisymm _ (zero_le _)
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      have hε_ne : (ε : ENNReal) ≠ 0 := by simp [hε.ne']
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε_ne
      rw [zero_add]
      apply le_of_lt
      calc μ {s} ≤ (1 : ENNReal) / (n + 1) := le_of_lt (h_neg n)
        _ ≤ (n : ENNReal)⁻¹ := by
            rw [one_div]
            apply ENNReal.inv_le_inv.mpr
            exact le_self_add
        _ < ε := hn
    exact (hpos.ne' h_zero).elim
  apply Set.Countable.mono h_subset
  apply Set.countable_iUnion
  intro n
  exact (h_finite n).countable

/-- A function `f : ℝ → ℂ` with countable support is measurable. On the support,
    countability gives measurability; on the complement, constancy (= 0) gives
    measurability. -/
lemma measurable_of_countable_support (f : ℝ → ℂ)
    (hf : Set.Countable {s | f s ≠ 0}) : Measurable f := by
  let S := {s | f s ≠ 0}
  have hS_meas : MeasurableSet S := hf.measurableSet
  apply measurable_of_restrict_of_restrict_compl hS_meas
  · haveI : Countable S := hf.to_subtype
    exact measurable_of_countable _
  · have h_eq : Sᶜ.restrict f = fun _ => (0 : ℂ) := by
      ext ⟨x, hx⟩
      simp only [Set.restrict_apply, Set.mem_compl_iff] at hx ⊢
      exact Function.notMem_support.mp hx
    rw [h_eq]
    exact measurable_const

/-- The function `s ↦ ⟪E({s})ψ, ψ⟫` is measurable. This follows from the fact
    that finite spectral measures have countably many atoms, so the inner product
    is nonzero on at most countably many points. -/
theorem spectral_inner_measurable (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (ψ : H) :
    Measurable (fun s => ⟪E {s} ψ, ψ⟫_ℂ) := by
  haveI : IsFiniteMeasure (spectral_scalar_measure E ψ hE) :=
    spectral_scalar_measure_finite E hE hE_univ ψ
  apply measurable_of_countable_support
  have h_atoms := finite_measure_countable_atoms (spectral_scalar_measure E ψ hE)
  apply Set.Countable.mono _ h_atoms
  intro s hs
  simp only [Set.mem_setOf_eq] at hs ⊢
  intro h_mu_zero
  apply hs
  have h_re : (⟪E {s} ψ, ψ⟫_ℂ).re = (spectral_scalar_measure E ψ hE {s}).toReal := by
    exact (spectral_scalar_measure_apply' E hE ψ {s} (MeasurableSet.singleton s)).symm
  have h_im : (⟪E {s} ψ, ψ⟫_ℂ).im = 0 := spectral_diagonal_real hE {s} ψ
  rw [h_mu_zero] at h_re
  simp only [ENNReal.toReal_zero] at h_re
  exact Eq.symm (Complex.ext (_root_.id (Eq.symm h_re)) (_root_.id (Eq.symm h_im)))

/-!
## Basic Scalar Measure Properties
-/

/-- The spectral scalar measure of the zero vector is the zero measure:
    `μ_0(B) = 0` for all Borel sets `B`. -/
lemma spectral_scalar_measure_zero (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) :
    spectral_scalar_measure E (0 : H) hE B = 0 := by
  rw [spectral_scalar_measure_apply E hE (0 : H) B hB]
  simp only [map_zero, inner_zero_left, Complex.zero_re, ENNReal.ofReal_zero]

/-- Helper for functionalDomain_zero_mem -/
lemma spectral_scalar_measure_zero_eq (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) :
    spectral_scalar_measure E (0 : H) hE = 0 := by
  ext B hB
  exact spectral_scalar_measure_zero E hE B hB

/-- Spectral measure scales quadratically: μ(c•ψ)(B) = |c|² μ(ψ)(B) -/
lemma spectral_scalar_measure_smul (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (c : ℂ) (ψ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    (spectral_scalar_measure E (c • ψ) hE B).toReal = ‖c‖^2 * (spectral_scalar_measure E ψ hE B).toReal := by
  rw [spectral_scalar_measure_apply' E hE (c • ψ) B hB]
  rw [spectral_scalar_measure_apply' E hE ψ B hB]
  simp only [map_smul, inner_smul_left, inner_smul_right]
  have h : starRingEnd ℂ c * c = (‖c‖^2 : ℂ) := conj_mul' c
  calc (c * (starRingEnd ℂ c * ⟪(E B) ψ, ψ⟫_ℂ)).re
      = (starRingEnd ℂ c * c * ⟪(E B) ψ, ψ⟫_ℂ).re := by ring_nf
    _ = ((‖c‖^2 : ℂ) * ⟪(E B) ψ, ψ⟫_ℂ).re := by rw [h]
    _ = ‖c‖^2 * (⟪(E B) ψ, ψ⟫_ℂ).re := by
        rw [Complex.mul_re]
        simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Helper for functionalDomain_smul_mem -/
lemma spectral_scalar_measure_smul_eq (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (c : ℂ) (ψ : H) :
    spectral_scalar_measure E (c • ψ) hE = ENNReal.ofReal (‖c‖^2) • spectral_scalar_measure E ψ hE := by
  haveI : IsFiniteMeasure (spectral_scalar_measure E (c • ψ) hE) :=
    spectral_scalar_measure_finite E hE hE_univ (c • ψ)
  haveI : IsFiniteMeasure (spectral_scalar_measure E ψ hE) :=
    spectral_scalar_measure_finite E hE hE_univ ψ
  ext B hB
  rw [Measure.smul_apply, ← ENNReal.toReal_eq_toReal]
  · rw [spectral_scalar_measure_smul E hE c ψ B hB]
    simp only [norm_nonneg, ENNReal.ofReal_pow, ofReal_norm, smul_eq_mul, ENNReal.toReal_mul,
               ENNReal.toReal_pow, toReal_enorm]
  · exact (measure_lt_top _ _).ne
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_lt_top _ _).ne

/-!
## Addition and Subtraction Formulas
-/

/-- The spectral measure of a sum expands with cross terms -/
lemma spectral_scalar_measure_add (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (x y : H) (B : Set ℝ) (hB : MeasurableSet B) :
    (spectral_scalar_measure E (x + y) hE B).toReal =
    (spectral_scalar_measure E x hE B).toReal +
    (spectral_scalar_measure E y hE B).toReal +
    2 * Complex.re ⟪E B x, y⟫_ℂ := by
  rw [spectral_scalar_measure_apply' E hE (x + y) B hB]
  rw [spectral_scalar_measure_apply' E hE x B hB]
  rw [spectral_scalar_measure_apply' E hE y B hB]
  simp only [map_add, inner_add_left, inner_add_right]
  have h_conj : Complex.re ⟪E B y, x⟫_ℂ = Complex.re ⟪E B x, y⟫_ℂ := by
    rw [hE.sa B y x]
    have h : ⟪y, (E B) x⟫_ℂ = starRingEnd ℂ ⟪(E B) x, y⟫_ℂ := by
      exact Eq.symm (conj_inner_symm y ((E B) x))
    rw [h, Complex.conj_re]
  calc (⟪(E B) x, x⟫_ℂ + ⟪(E B) y, x⟫_ℂ + (⟪(E B) x, y⟫_ℂ + ⟪(E B) y, y⟫_ℂ)).re
      = (⟪(E B) x, x⟫_ℂ).re + (⟪(E B) y, x⟫_ℂ).re + (⟪(E B) x, y⟫_ℂ).re + (⟪(E B) y, y⟫_ℂ).re := by
          simp only [Complex.add_re]
          exact
            Eq.symm
              (add_assoc ((⟪(E B) x, x⟫_ℂ).re + (⟪(E B) y, x⟫_ℂ).re) (⟪(E B) x, y⟫_ℂ).re
                (⟪(E B) y, y⟫_ℂ).re)
    _ = (⟪(E B) x, x⟫_ℂ).re + (⟪(E B) y, y⟫_ℂ).re + 2 * (⟪(E B) x, y⟫_ℂ).re := by
          rw [h_conj]; ring

/-- The spectral measure of a difference expands as:
    `μ_{x-y}(B) = μ_x(B) + μ_y(B) - 2·Re⟪E(B)x, y⟫`. -/
lemma spectral_scalar_measure_sub (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (x y : H) (B : Set ℝ) (hB : MeasurableSet B) :
    (spectral_scalar_measure E (x - y) hE B).toReal =
    (spectral_scalar_measure E x hE B).toReal +
    (spectral_scalar_measure E y hE B).toReal -
    2 * Complex.re ⟪E B x, y⟫_ℂ := by
  have h : x - y = x + (-1 : ℂ) • y := by simp only [neg_smul, one_smul]; exact sub_eq_add_neg x y
  rw [h, spectral_scalar_measure_add E hE x ((-1 : ℂ) • y) B hB]
  rw [spectral_scalar_measure_smul E hE (-1) y B hB]
  simp only [norm_neg, NormOneClass.norm_one, one_pow, one_mul, inner_smul_right, neg_one_mul,
             Complex.neg_re]
  ring

/-!
## Norm and Monotonicity Properties
-/

/-- μ_ψ(B) = ‖E(B)ψ‖² -/
lemma spectral_scalar_measure_eq_norm_sq (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    (spectral_scalar_measure E ψ hE B).toReal = ‖E B ψ‖^2 := by
  rw [spectral_scalar_measure_apply' E hE ψ B hB, ← spectral_projection_norm_sq E B hE hB ψ]

/-- Monotonicity: B ⊆ C → μ_ψ(B) ≤ μ_ψ(C) -/
lemma spectral_scalar_measure_mono (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : B ⊆ C) (ψ : H) :
    spectral_scalar_measure E ψ hE B ≤ spectral_scalar_measure E ψ hE C := by
  haveI := spectral_scalar_measure_finite E hE hE_univ ψ
  exact MeasureTheory.measure_mono hBC

/-- μ_ψ(ℝ) = ‖ψ‖² -/
lemma spectral_scalar_measure_univ (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (ψ : H) :
    (spectral_scalar_measure E ψ hE Set.univ).toReal = ‖ψ‖^2 := by
  rw [spectral_scalar_measure_apply' E hE ψ Set.univ MeasurableSet.univ]
  rw [hE_univ]
  simp only [ContinuousLinearMap.one_apply]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  simp only [coe_algebraMap]
  rw [← ofReal_pow]
  exact rfl

/-- μ_ψ(Bᶜ) = ‖ψ‖² - μ_ψ(B) -/
lemma spectral_scalar_measure_compl (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (hE_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
              E (B ∪ C) = E B + E C)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    (spectral_scalar_measure E ψ hE Bᶜ).toReal = ‖ψ‖^2 - (spectral_scalar_measure E ψ hE B).toReal := by
  rw [spectral_scalar_measure_eq_norm_sq E hE Bᶜ hB.compl ψ]
  rw [spectral_scalar_measure_eq_norm_sq E hE B hB ψ]
  rw [spectral_projection_compl E hE_univ hE_add B hB]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]

  have h1 : ⟪E B ψ, ψ⟫_ℂ = ‖E B ψ‖^2 := by
    rw [spectral_projection_inner_factorization E hE B hB ψ ψ]
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    exact rfl

  have h2 : ⟪ψ, E B ψ⟫_ℂ = ‖E B ψ‖^2 := by
    rw [← inner_conj_symm, h1]
    simp only [map_pow, Complex.conj_ofReal]

  have h_expand : ‖ψ - E B ψ‖^2 = (⟪ψ - E B ψ, ψ - E B ψ⟫_ℂ).re := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    simp only [coe_algebraMap]
    rw [← ofReal_pow]
    exact rfl

  rw [h_expand]
  simp only [inner_sub_left, inner_sub_right]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (E B ψ)]
  rw [h1, h2]
  simp only [Complex.sub_re]
  have hre1 : ((‖ψ‖ : ℂ) ^ 2).re = ‖ψ‖ ^ 2 := by rw [← ofReal_pow] ; exact rfl
  have hre2 : ((‖E B ψ‖ : ℂ) ^ 2).re = ‖E B ψ‖ ^ 2 := by rw [← ofReal_pow] ; exact rfl
  simp_all only [coe_algebraMap, sub_self, sub_zero]

/-!
## Kernel Characterization
-/

/-- Kernel characterization: E(B)ψ = 0 iff μ_ψ(B) = 0 -/
lemma spectral_projection_ker_iff (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    E B ψ = 0 ↔ spectral_scalar_measure E ψ hE B = 0 := by
  haveI := spectral_scalar_measure_finite E hE hE_univ ψ
  constructor
  · intro h
    have h1 : ‖E B ψ‖^2 = 0 := by simp [h]
    rw [spectral_projection_norm_sq E B hE hB ψ] at h1
    rw [← spectral_scalar_measure_apply' E hE ψ B hB] at h1
    have h2 : (spectral_scalar_measure E ψ hE B).toReal = 0 := by linarith
    rw [ENNReal.toReal_eq_zero_iff] at h2
    cases h2 with
    | inl h => exact h
    | inr h => exact absurd h (measure_lt_top _ B).ne
  · intro h
    have h1 : (spectral_scalar_measure E ψ hE B).toReal = 0 := by simp [h]
    rw [spectral_scalar_measure_apply' E hE ψ B hB] at h1
    have h2 : ‖E B ψ‖^2 = 0 := by
      rw [spectral_projection_norm_sq E B hE hB ψ]
      linarith
    exact norm_eq_zero.mp (pow_eq_zero h2)

end FunctionalCalculus
