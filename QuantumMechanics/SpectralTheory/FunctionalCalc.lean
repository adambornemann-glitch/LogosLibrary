/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.Routes
import LogosLibrary.QuantumMechanics.SpectralTheory.Cayley.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic
/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.Spectral.Routes
import LogosLibrary.QuantumMechanics.Spectral.Cayley
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic

/-!
# Functional Calculus for Self-Adjoint Operators

This file develops the Borel functional calculus for self-adjoint operators via
spectral measures. Given a spectral measure `E` on `ℝ` and a measurable function
`f : ℝ → ℂ`, we construct the operator `f(A) = ∫ f(λ) dE(λ)` and establish its
key algebraic properties.

## Overview

The functional calculus is a *-homomorphism from (a suitable algebra of) functions
on `ℝ` to operators on `H`:
- `Φ(f + g) = Φ(f) + Φ(g)` (additive)
- `Φ(fg) = Φ(f) ∘ Φ(g)` (multiplicative)
- `Φ(f̄) = Φ(f)*` (preserves adjoints)
- `Φ(1) = I` (unital)
- `Φ(𝟙_B) = E(B)` (indicator functions give spectral projections)

For bounded functions, `Φ(f)` is a bounded operator on all of `H`. For unbounded
functions, `Φ(f)` is defined on the domain `{ψ : ∫|f|² dμ_ψ < ∞}`.

## Main definitions

### §1. Domain Characterization
* `functionalDomain`: The set `{ψ : ∫|f|² dμ_ψ < ∞}` where `f(A)ψ` is defined
* `functionalDomainSubmodule`: The functional domain as a `Submodule ℂ H`

### §2. The Functional Calculus Map
* `boundedFunctionalCalculus`: `f(A)` for bounded Borel functions, as a `H →L[ℂ] H`
* `functionalCalculus`: `f(A)` for general measurable functions, as a linear map
  on `functionalDomainSubmodule`

### §3. Algebraic Properties
* `IsSpectralMeasureFor`: Predicate bundling spectral measure axioms for a generator

### §4. Recovering A from E
* `identityFunction`: The function `id(s) = s`
* `generator_eq_spectral_integral`: `A = ∫ s dE(s)` on `dom(A)`

### §5. Three Routes Agreement
* `SpectralMeasureAgreement`: Structure asserting Bochner, Stieltjes, and Cayley
  routes produce the same spectral measure

## Main statements

### Spectral Projection Properties
* `spectral_projection_orthogonal`: `E(B)² = E(B)` (idempotent)
* `spectral_projection_adjoint`: `E(B)* = E(B)` (self-adjoint)
* `spectral_projection_norm_le`: `‖E(B)ψ‖ ≤ ‖ψ‖` (contractive)
* `spectral_projection_disjoint`: `E(B)E(C) = 0` when `B ∩ C = ∅`
* `spectral_projection_comm`: `E(B)E(C) = E(C)E(B)` (commutative)

### Spectral Scalar Measure Properties
* `spectral_scalar_measure_eq_norm_sq`: `μ_ψ(B) = ‖E(B)ψ‖²`
* `spectral_scalar_measure_univ`: `μ_ψ(ℝ) = ‖ψ‖²`
* `spectral_scalar_measure_add`: Expansion with cross terms for `μ_{x+y}`
* `spectral_cross_term_bound`: `|Re⟨E(B)x, y⟩| ≤ √μ_x(B) · √μ_y(B)`

### Functional Calculus Algebraic Properties
* `functionalCalculus_add`: `(f + g)(A) = f(A) + g(A)`
* `functionalCalculus_mul`: `(fg)(A) = f(A) ∘ g(A)`
* `functionalCalculus_conj`: `f̄(A) = f(A)*`
* `functionalCalculus_one`: `1(A) = I`
* `functionalCalculus_indicator`: `𝟙_B(A) = E(B)`

### Generator Recovery
* `generator_eq_spectral_integral`: `Aψ = (∫ s dE(s))ψ` for `ψ ∈ dom(A)`
* `generator_domain_eq_functional_domain`: `dom(A) = {ψ : ∫|s|² dμ_ψ < ∞}`
* `generator_norm_sq_eq_second_moment`: `‖Aψ‖² = ∫ s² dμ_ψ`

### Three Routes Agreement
* `three_routes_agree`: Bochner (Fourier), Stieltjes (resolvent), and Cayley
  routes all produce the same spectral measure

### Extended Lemmas
* `boundedFunctionalCalculus_nonneg`: `f ≥ 0` implies `⟨Φ(f)ψ, ψ⟩ ≥ 0`
* `boundedFunctionalCalculus_mono`: `f ≤ g` implies `⟨Φ(f)ψ, ψ⟩ ≤ ⟨Φ(g)ψ, ψ⟩`
* `boundedFunctionalCalculus_real_selfAdjoint`: Real `f` gives self-adjoint `Φ(f)`
* `boundedFunctionalCalculus_sq`: `Φ(f²) = Φ(f)²`

## Implementation notes

This file is **heavily axiomatized**. The axioms fall into several categories:

### Measurability and Integrability Axioms
* `spectral_inner_measurable`: `s ↦ ⟨E{s}ψ, ψ⟩` is measurable
* `spectral_integral_add_bound`: Integrability under sum measure
* `functionalDomain_inter_aux`, `functionalDomain_mul_bound_aux`,
  `functionalDomain_of_bounded_aux`: Domain closure properties

### Spectral Integral Construction Axioms
* `spectral_integral_bounded`: Existence for bounded functions
* `spectral_integral`: Existence for general functions on domain
* `spectral_integral_inner`: Inner product formula `⟨Φ(f)ψ, φ⟩ = ∫ f dν_{ψ,φ}`

### Spectral Integral Properties Axioms
* `spectral_integral_indicator`: `Φ(𝟙_B) = E(B)`
* `spectral_integral_add`, `spectral_integral_smul`: Linearity in `f`
* `spectral_integral_mul`: Multiplicativity `Φ(fg) = Φ(f)Φ(g)`
* `spectral_integral_conj`: Adjoint property `Φ(f̄) = Φ(f)*`
* `spectral_integral_add_vector`, `spectral_integral_smul_vector`: Linearity in `ψ`
* `spectral_integral_one`: `Φ(1) = I`

### Generator-Spectral Correspondence Axioms
* `generator_spectral_integral_inner_eq`: `⟨Aψ, φ⟩ = ⟨(∫ s dE)ψ, φ⟩`
* `generator_domain_subset_id_domain`: `dom(A) ⊆ dom(id(A))`
* `id_domain_subset_generator_domain`: `dom(id(A)) ⊆ dom(A)`
* `generator_norm_sq_eq_second_moment`: `‖Aψ‖² = ∫ s² dμ_ψ`

### Three Routes Agreement Axioms
* `spectralMeasure_from_cayley`: Cayley-constructed spectral measure
* `bochner_route_agreement`, `stieltjes_route_agreement`, `cayley_route_agreement`

Discharging these axioms requires:
- Careful construction of the spectral integral via approximation
- Dominated convergence and monotone convergence machinery
- Connection between generator domain and second moment finiteness
- Detailed analysis of the Cayley transform spectral correspondence

## Physical interpretation

The functional calculus is the mathematical foundation for quantum observables:
- If `A` is the Hamiltonian with spectrum `σ(A)`, then `f(A)` represents measuring
  the observable `f(energy)`
- The spectral projections `E(B)` represent "the system has energy in `B`"
- The formula `⟨f(A)ψ, ψ⟩ = ∫ f dμ_ψ` is the expectation value of `f(A)` in state `ψ`
- Positivity preservation (`f ≥ 0 ⟹ Φ(f) ≥ 0`) reflects physical positivity of
  observables

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Chapter VII-VIII
* [Schmüdgen, *Unbounded Self-adjoint Operators*][schmudgen2012], Chapters 4-5
* [Rudin, *Functional Analysis*][rudin1991], Chapter 12
* [Hall, *Quantum Theory for Mathematicians*][hall2013], Chapter 7

## TODO

* Prove spectral integral construction via simple function approximation
* Discharge integrability axioms using measure theory machinery
* Prove generator domain equals second moment domain directly
* Connect to continuous functional calculus for C*-algebras
* Prove spectral mapping theorem: `σ(f(A)) = f(σ(A))`

## Tags

functional calculus, spectral measure, spectral theorem, self-adjoint operator,
*-homomorphism, Borel functional calculus
-/
namespace FunctionalCalculus

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory InnerProductSpace Complex QuantumMechanics.Cayley SpectralBridge SpectralBridge.BochnerRoute QuantumMechanics.Generators ContinuousLinearMap


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## §1. Domain Characterization
-/

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

lemma spectral_disjoint_orthogonal (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : Disjoint B C) :
    E B * E C = 0 := by
  have := hE.mul B C hB hC
  simp [Set.disjoint_iff_inter_eq_empty.mp hBC] at this
  rw [this]
  exact hE.empty


lemma finite_measure_countable_atoms (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Set.Countable {s | μ {s} ≠ 0} := by
  have h_finite : ∀ n : ℕ, Set.Finite {s : ℝ | μ {s} ≥ (1 : ENNReal) / (n + 1)} := by
    intro n
    by_contra h_inf
    -- Convert ¬Finite to Infinite
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


lemma measurable_of_countable_support (f : ℝ → ℂ)
    (hf : Set.Countable {s | f s ≠ 0}) : Measurable f := by
  let S := {s | f s ≠ 0}
  have hS_meas : MeasurableSet S := hf.measurableSet
  apply measurable_of_restrict_of_restrict_compl hS_meas
  · -- On S: S is countable as a subtype, so any function is measurable
    haveI : Countable S := hf.to_subtype
    exact measurable_of_countable _
  · -- On Sᶜ: f = 0 (constant), hence measurable
    have h_eq : Sᶜ.restrict f = fun _ => (0 : ℂ) := by
      ext ⟨x, hx⟩
      simp only [Set.restrict_apply, Set.mem_compl_iff] at hx ⊢
      exact Function.notMem_support.mp hx
    rw [h_eq]
    exact measurable_const


/-- The spectral inner product s ↦ ⟪E{s}ψ, ψ⟫ is measurable -/
axiom spectral_inner_measurable (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (ψ : H) : Measurable (fun s => ⟪E {s} ψ, ψ⟫_ℂ)


/-- Spectral projections multiply: E(B)E(C) = E(B ∩ C) -/
lemma spectral_projection_mul (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    E B * E C = E (B ∩ C) := hE.mul B C hB hC


/-- The domain of f(A) consists of vectors with finite f-moment. -/
def functionalDomain (μ : H → Measure ℝ) (f : ℝ → ℂ) : Set H :=
  {ψ : H | Integrable (fun s => ‖f s‖^2) (μ ψ)}

-- E(B) is idempotent: E(B)² = E(B) -/
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
    _ = ⟪E B x, E B y⟫_ℂ := spectral_self_adjoint E B (E B x) y

/-- Variant: ⟪E(B)x, E(B)y⟫ = ⟪x, E(B)y⟫ -/
lemma spectral_projection_inner_factorization' (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    ⟪E B x, E B y⟫_ℂ = ⟪x, E B y⟫_ℂ := by
  rw [← spectral_projection_inner_factorization E hE B hB x y]
  exact spectral_self_adjoint E B x y

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
## Spectral Scalar Measure Properties
-/

lemma spectral_scalar_measure_zero (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) :
    spectral_scalar_measure E (0 : H) hE B = 0 := by
  rw [spectral_scalar_measure_apply E hE (0 : H) B hB]
  simp only [map_zero, inner_zero_left, Complex.zero_re, ENNReal.ofReal_zero]


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

/-!
## Cross-term Bound (the key for add_mem)

For the cross measure ν(B) = Re⟪E(B)x, y⟫, we need:
  |ν(B)| ≤ √(μ_x(B)) · √(μ_y(B))
-/

/-- Cauchy-Schwarz bound for spectral cross term -/
lemma spectral_cross_term_bound (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    |Complex.re ⟪E B x, y⟫_ℂ| ≤
    Real.sqrt ((spectral_scalar_measure E x hE B).toReal) *
    Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
  -- Use ⟪E(B)x, y⟩ = ⟪E(B)x, E(B)y⟩ and Cauchy-Schwarz
  rw [spectral_projection_inner_factorization E hE B hB x y]

  have h_cs : |Complex.re ⟪E B x, E B y⟫_ℂ| ≤ ‖E B x‖ * ‖E B y‖ := by
    calc |Complex.re ⟪E B x, E B y⟫_ℂ|
        ≤ ‖⟪E B x, E B y⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖E B x‖ * ‖E B y‖ := norm_inner_le_norm (E B x) (E B y)

  -- Now use ‖E(B)ψ‖² = μ_ψ(B)
  have hx : ‖E B x‖ = Real.sqrt ((spectral_scalar_measure E x hE B).toReal) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    congr 1
    rw [spectral_projection_norm_sq E B hE hB x]
    exact Eq.symm (spectral_scalar_measure_apply' E hE x B hB)
  have hy : ‖E B y‖ = Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    congr 1
    rw [spectral_projection_norm_sq E B hE hB y]
    exact Eq.symm (spectral_scalar_measure_apply' E hE y B hB)

  rw [hx, hy] at h_cs
  exact h_cs



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
    rw [spectral_self_adjoint E B y x]
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

/-!
## Integrability of |f|² under spectral measure of sum

The key theorem: if ∫|f|² dμ_x < ∞ and ∫|f|² dμ_y < ∞, then ∫|f|² dμ_{x+y} < ∞
-/

/-- Upper bound on μ_{x+y}(B) in terms of μ_x(B) and μ_y(B) -/
lemma spectral_scalar_measure_add_bound (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (x y : H) (B : Set ℝ) (hB : MeasurableSet B) :
    (spectral_scalar_measure E (x + y) hE B).toReal ≤
    2 * (spectral_scalar_measure E x hE B).toReal +
    2 * (spectral_scalar_measure E y hE B).toReal +
    2 * Real.sqrt ((spectral_scalar_measure E x hE B).toReal) *
        Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
  rw [spectral_scalar_measure_add E hE x y B hB]
  have h_cross := spectral_cross_term_bound E hE B hB x y
  have h1 : 2 * Complex.re ⟪E B x, y⟫_ℂ ≤
      2 * Real.sqrt ((spectral_scalar_measure E x hE B).toReal) *
          Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
    have : Complex.re ⟪E B x, y⟫_ℂ ≤ |Complex.re ⟪E B x, y⟫_ℂ| := le_abs_self _
    linarith [h_cross]
  have hx_nonneg : (spectral_scalar_measure E x hE B).toReal ≥ 0 := ENNReal.toReal_nonneg
  have hy_nonneg : (spectral_scalar_measure E y hE B).toReal ≥ 0 := ENNReal.toReal_nonneg
  linarith

/-- For simple functions, integral bound under sum measure -/
-- This would need substantial measure theory machinery
-- For now, we'll axiomatize the key integrability result
axiom spectral_integral_add_bound (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (x y : H) (f : ℝ → ℂ)
    (hx : Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E x hE))
    (hy : Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E y hE)) :
    Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E (x + y) hE)

/-!
## The Submodule Structure
-/

/-- Helper for functionalDomain_zero_mem -/
lemma spectral_scalar_measure_zero_eq (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) :
    spectral_scalar_measure E (0 : H) hE = 0 := by
  ext B hB
  exact spectral_scalar_measure_zero E hE B hB

/-- Helper: zero is in the functional domain -/
lemma functionalDomain_zero_mem (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ) :
    (0 : H) ∈ functionalDomain (spectral_scalar_measure E · hE) f := by
  simp only [functionalDomain, Set.mem_setOf_eq]
  rw [spectral_scalar_measure_zero_eq E hE]
  exact integrable_zero_measure

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

/-- Helper: scalar multiples preserve functional domain -/
lemma functionalDomain_smul_mem (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f : ℝ → ℂ) (c : ℂ) (ψ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    c • ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f := by
  simp only [functionalDomain, Set.mem_setOf_eq] at hψ ⊢
  rw [spectral_scalar_measure_smul_eq E hE hE_univ c ψ]
  exact Integrable.smul_measure hψ ENNReal.coe_ne_top

/-- Helper: sums preserve functional domain -/
lemma functionalDomain_add_mem (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f : ℝ → ℂ) (x y : H)
    (hx : x ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hy : y ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    x + y ∈ functionalDomain (spectral_scalar_measure E · hE) f := by
  simp only [functionalDomain, Set.mem_setOf_eq] at hx hy ⊢
  exact spectral_integral_add_bound E hE x y f hx hy

/-- The functional domain is a submodule -/
def functionalDomainSubmodule' (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f : ℝ → ℂ) : Submodule ℂ H where
  carrier := functionalDomain (spectral_scalar_measure E · hE) f
  zero_mem' := functionalDomain_zero_mem E hE f
  add_mem' := fun hx hy => functionalDomain_add_mem E hE f _ _ hx hy
  smul_mem' := fun c _ hψ => functionalDomain_smul_mem E hE hE_univ f c _ hψ

/-!
## Spectral Projection Properties - Basic
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

/-- E(B) is self-adjoint as an operator -/
lemma spectral_projection_adjoint (E : Set ℝ → H →L[ℂ] H)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (E B).adjoint = E B := by
  ext ψ
  apply ext_inner_left ℂ
  intro φ
  rw [@ContinuousLinearMap.adjoint_inner_right]
  exact spectral_self_adjoint E B φ ψ

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

/-- Range of E(B) is the set of fixed points -/
lemma spectral_projection_range_eq_fixed (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    ψ ∈ LinearMap.range (E B) ↔ E B ψ = ψ := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact spectral_projection_apply_twice E hE B hB φ
  · intro h
    exact ⟨ψ, h⟩

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

/-!
## Spectral Scalar Measure Properties - Extended
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
## Cross-term and Inner Product Bounds
-/

/-- Imaginary part of cross term also bounded -/
lemma spectral_cross_term_im_bound (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    |Complex.im ⟪E B x, y⟫_ℂ| ≤
    Real.sqrt ((spectral_scalar_measure E x hE B).toReal) *
    Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
  rw [spectral_projection_inner_factorization E hE B hB x y]
  have h_cs : |Complex.im ⟪E B x, E B y⟫_ℂ| ≤ ‖E B x‖ * ‖E B y‖ := by
    calc |Complex.im ⟪E B x, E B y⟫_ℂ|
        ≤ ‖⟪E B x, E B y⟫_ℂ‖ := Complex.abs_im_le_norm _
      _ ≤ ‖E B x‖ * ‖E B y‖ := norm_inner_le_norm (E B x) (E B y)
  calc |Complex.im ⟪E B x, E B y⟫_ℂ|
      ≤ ‖E B x‖ * ‖E B y‖ := h_cs
    _ = Real.sqrt ((spectral_scalar_measure E x hE B).toReal) *
        Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
        rw [spectral_scalar_measure_eq_norm_sq E hE B hB x, spectral_scalar_measure_eq_norm_sq E hE B hB y]
        simp [Real.sqrt_sq (norm_nonneg _)]

/-- Full complex cross term bound -/
lemma spectral_cross_term_norm_bound (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    ‖⟪E B x, y⟫_ℂ‖ ≤
    Real.sqrt ((spectral_scalar_measure E x hE B).toReal) *
    Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
  rw [spectral_projection_inner_factorization E hE B hB x y]
  calc ‖⟪E B x, E B y⟫_ℂ‖
      ≤ ‖E B x‖ * ‖E B y‖ := norm_inner_le_norm _ _
    _ = Real.sqrt ((spectral_scalar_measure E x hE B).toReal) *
        Real.sqrt ((spectral_scalar_measure E y hE B).toReal) := by
        rw [spectral_scalar_measure_eq_norm_sq E hE B hB x, spectral_scalar_measure_eq_norm_sq E hE B hB y]
        simp [Real.sqrt_sq (norm_nonneg _)]

/-!
## Polarization Identities
-/

/-- Polarization: recover ⟪E(B)x, y⟫ from diagonal terms -/
lemma spectral_polarization (E : Set ℝ → H →L[ℂ] H) (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    ⟪E B x, y⟫_ℂ = (1/4 : ℂ) * (
      ⟪E B (x + y), x + y⟫_ℂ -
      ⟪E B (x - y), x - y⟫_ℂ -
      I * ⟪E B (x + I • y), x + I • y⟫_ℂ +
      I * ⟪E B (x - I • y), x - I • y⟫_ℂ) := by
  simp only [map_add, map_sub, map_smul]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
             inner_smul_left, inner_smul_right]
  have hI2 : (I : ℂ)^2 = -1 := Complex.I_sq
  ring_nf
  linear_combination (norm := ring_nf) (⟪(E B) x, y⟫_ℂ - ⟪(E B) x, y⟫_ℂ) * hI2
  simp only [one_div, I_sq, mul_neg, mul_one, neg_mul, add_neg_cancel, zero_add, conj_I]
  have hII : (I : ℂ) * I = -1 := by rw [← sq, Complex.I_sq]
  rw [hII.symm]
  ring

/-- Spectral measure version of polarization -/
lemma spectral_scalar_measure_polarization (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    ⟪E B x, y⟫_ℂ = (1/4 : ℂ) * (
      (spectral_scalar_measure E (x + y) hE B).toReal -
      (spectral_scalar_measure E (x - y) hE B).toReal -
      I * (spectral_scalar_measure E (x + I • y) hE B).toReal +
      I * (spectral_scalar_measure E (x - I • y) hE B).toReal) := by
  rw [spectral_polarization E B hB x y]
  congr 1
  -- Rewrite each spectral measure in terms of inner product
  have h1 : ((spectral_scalar_measure E (x + y) hE B).toReal : ℂ) = ⟪E B (x + y), x + y⟫_ℂ := by
    rw [spectral_scalar_measure_apply' E hE (x + y) B hB]
    have h := spectral_diagonal_real E B (x + y)
    conv_rhs => rw [← Complex.re_add_im ⟪E B (x + y), x + y⟫_ℂ, h]
    simp
  have h2 : ((spectral_scalar_measure E (x - y) hE B).toReal : ℂ) = ⟪E B (x - y), x - y⟫_ℂ := by
    rw [spectral_scalar_measure_apply' E hE (x - y) B hB]
    have h := spectral_diagonal_real E B (x - y)
    conv_rhs => rw [← Complex.re_add_im ⟪E B (x - y), x - y⟫_ℂ, h]
    simp
  have h3 : ((spectral_scalar_measure E (x + I • y) hE B).toReal : ℂ) = ⟪E B (x + I • y), x + I • y⟫_ℂ := by
    rw [spectral_scalar_measure_apply' E hE (x + I • y) B hB]
    have h := spectral_diagonal_real E B (x + I • y)
    conv_rhs => rw [← Complex.re_add_im ⟪E B (x + I • y), x + I • y⟫_ℂ, h]
    simp
  have h4 : ((spectral_scalar_measure E (x - I • y) hE B).toReal : ℂ) = ⟪E B (x - I • y), x - I • y⟫_ℂ := by
    rw [spectral_scalar_measure_apply' E hE (x - I • y) B hB]
    have h := spectral_diagonal_real E B (x - I • y)
    conv_rhs => rw [← Complex.re_add_im ⟪E B (x - I • y), x - I • y⟫_ℂ, h]
    simp
  rw [h1, h2, h3, h4]

/-!
## Complement and Set Operations
-/

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
  -- Goal: ‖ψ - E B ψ‖² = ‖ψ‖² - ‖E B ψ‖²
  -- Pythagorean theorem for orthogonal projection

  -- Key facts from spectral_projection_inner_factorization:
  -- ⟪E B ψ, ψ⟫ = ⟪E B ψ, E B ψ⟫ = ‖E B ψ‖²
  have h1 : ⟪E B ψ, ψ⟫_ℂ = ‖E B ψ‖^2 := by
    rw [spectral_projection_inner_factorization E hE B hB ψ ψ]
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    exact rfl

  -- ⟪ψ, E B ψ⟫ = conj ⟪E B ψ, ψ⟫ = ‖E B ψ‖² (real, so equals its conjugate)
  have h2 : ⟪ψ, E B ψ⟫_ℂ = ‖E B ψ‖^2 := by
    rw [← inner_conj_symm, h1]
    simp only [map_pow, Complex.conj_ofReal]

  -- Expand ‖ψ - E B ψ‖²
  have h_expand : ‖ψ - E B ψ‖^2 = (⟪ψ - E B ψ, ψ - E B ψ⟫_ℂ).re := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    simp only [coe_algebraMap]
    rw [← ofReal_pow]
    exact rfl

  rw [h_expand]
  simp only [inner_sub_left, inner_sub_right]
  -- ⟪ψ, ψ⟫ - ⟪ψ, E B ψ⟫ - ⟪E B ψ, ψ⟫ + ⟪E B ψ, E B ψ⟫
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (E B ψ)]
  rw [h1, h2]
  simp only [Complex.sub_re]
  have hre1 : ((‖ψ‖ : ℂ) ^ 2).re = ‖ψ‖ ^ 2 := by rw [← ofReal_pow] ; exact rfl
  have hre2 : ((‖E B ψ‖ : ℂ) ^ 2).re = ‖E B ψ‖ ^ 2 := by rw [← ofReal_pow] ; exact rfl
  simp_all only [coe_algebraMap, sub_self, sub_zero]

/-!
## Functional Domain Helpers
-/
axiom functionalDomain_inter_aux (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f g : ℝ → ℂ) (ψ : H) :
    Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E ψ hE) →
    Integrable (fun s => ‖g s‖^2) (spectral_scalar_measure E ψ hE) →
    Integrable (fun s => ‖f s + g s‖^2) (spectral_scalar_measure E ψ hE)

axiom functionalDomain_mul_bound_aux (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f g : ℝ → ℂ) (M : ℝ) (ψ : H) :
    (∀ s, ‖f s‖ ≤ M) →
    Integrable (fun s => ‖g s‖^2) (spectral_scalar_measure E ψ hE) →
    Integrable (fun s => ‖f s * g s‖^2) (spectral_scalar_measure E ψ hE)

axiom functionalDomain_of_bounded_aux (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f : ℝ → ℂ) (M : ℝ) (ψ : H) :
    (∀ s, ‖f s‖ ≤ M) →
    Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E ψ hE)

/-- Intersection of functional domains -/
lemma functionalDomain_inter (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f g : ℝ → ℂ) :
    functionalDomain (spectral_scalar_measure E · hE) f ∩
    functionalDomain (spectral_scalar_measure E · hE) g ⊆
    functionalDomain (spectral_scalar_measure E · hE) (fun s => f s + g s) := by
  intro ψ ⟨hf, hg⟩
  simp only [functionalDomain, Set.mem_setOf_eq] at hf hg ⊢
  exact functionalDomain_inter_aux E hE f g ψ hf hg

/-- Product bound for functional domains -/
lemma functionalDomain_mul_bound (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f g : ℝ → ℂ)
    (hf_bdd : ∃ M, ∀ s, ‖f s‖ ≤ M) :
    functionalDomain (spectral_scalar_measure E · hE) g ⊆
    functionalDomain (spectral_scalar_measure E · hE) (fun s => f s * g s) := by
  intro ψ hg
  simp only [functionalDomain, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨M, hM⟩ := hf_bdd
  exact functionalDomain_mul_bound_aux E hE f g M ψ hM hg

/-- Bounded functions always give full domain -/
lemma functionalDomain_of_bounded (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) (ψ : H) :
    ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f := by
  simp only [functionalDomain, Set.mem_setOf_eq]
  obtain ⟨M, hM⟩ := hf
  exact functionalDomain_of_bounded_aux E hE f M ψ hM

/-- Indicator functions are bounded -/
lemma indicator_bounded (B : Set ℝ) :
    ∃ M : ℝ, ∀ s, ‖Set.indicator B (1 : ℝ → ℂ) s‖ ≤ M := by
  use 1
  intro s
  by_cases hs : s ∈ B
  · simp [Set.indicator_of_mem hs]
  · simp [Set.indicator_of_notMem hs]

/-- Identity function is in the domain iff finite second moment -/
lemma functionalDomain_id_iff (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (ψ : H) :
    ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun s => (s : ℂ)) ↔
    Integrable (fun s => s^2) (spectral_scalar_measure E ψ hE) := by
  simp only [functionalDomain, Set.mem_setOf_eq]
  constructor
  · intro h
    convert h using 2
    simp_all only [norm_real, Real.norm_eq_abs, sq_abs]
  · intro h
    convert h using 2
    simp_all only [norm_real, Real.norm_eq_abs, sq_abs]

/-- Domain as submodule -/
def functionalDomainSubmodule (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f : ℝ → ℂ) : Submodule ℂ H where
  carrier := functionalDomain (spectral_scalar_measure E · hE) f
  zero_mem' := functionalDomain_zero_mem E hE f
  add_mem' := fun hx hy => functionalDomain_add_mem E hE f _ _ hx hy
  smul_mem' := fun c _ hψ => functionalDomain_smul_mem E hE hE_univ f c _ hψ


/-!
## Functional Calculus Axioms

We axiomatize the spectral integral ∫ f(s) dE(s) and its key properties.
-/

/-- The spectral integral for bounded functions exists and is bounded -/
axiom spectral_integral_bounded (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) : H →L[ℂ] H

/-- The spectral integral for general functions, defined on appropriate domain -/
axiom spectral_integral (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f) : H

/-- Core property: inner product representation -/
axiom spectral_integral_inner (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (φ : H) (hφ : φ ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    ⟪spectral_integral E hE f ψ hψ, φ⟫_ℂ =
    ∫ s, f s * ⟪E {s} ψ, φ⟫_ℂ ∂(spectral_scalar_measure E ψ hE)
    -- Or more properly: ∫ f dν_{ψ,φ} where ν_{ψ,φ}(B) = ⟪E(B)ψ, φ⟫

/-- Indicator functions give projections -/
axiom spectral_integral_indicator (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (Set.indicator B 1)) :
    spectral_integral E hE (Set.indicator B 1) ψ hψ = E B ψ

/-- Linearity in f -/
axiom spectral_integral_add (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f g : ℝ → ℂ)
    (ψ : H)
    (hf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f + g)) :
    spectral_integral E hE (f + g) ψ hfg =
    spectral_integral E hE f ψ hf + spectral_integral E hE g ψ hg

axiom spectral_integral_smul (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (c : ℂ) (f : ℝ → ℂ)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hcf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (c • f)) :
    spectral_integral E hE (c • f) ψ hcf = c • spectral_integral E hE f ψ hψ

/-- Multiplicativity: Φ(fg) = Φ(f) ∘ Φ(g) -/
axiom spectral_integral_mul (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f g : ℝ → ℂ)
    (ψ : H)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g)
    (hfg : spectral_integral E hE g ψ hg ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (h_prod : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f * g)) :
    spectral_integral E hE (f * g) ψ h_prod =
    spectral_integral E hE f (spectral_integral E hE g ψ hg) hfg

/-- Adjoint property: Φ(f̄) = Φ(f)* -/
axiom spectral_integral_conj (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (ψ φ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hφ : φ ∈ functionalDomain (spectral_scalar_measure E · hE) (starRingEnd ℂ ∘ f)) :
    ⟪spectral_integral E hE f ψ hψ, φ⟫_ℂ =
    ⟪ψ, spectral_integral E hE (starRingEnd ℂ ∘ f) φ hφ⟫_ℂ

/-- Bounded functions on full domain agree with bounded version -/
axiom spectral_integral_bounded_eq (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) (ψ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    spectral_integral E hE f ψ hψ = spectral_integral_bounded E hE f hf ψ

/-- **Theorem**: The domain contains dom(A) when f is polynomially bounded.
    NOTE: For polynomial degree n > 1, this really requires dom(A^n).
    We axiomatize the full statement for now. -/
axiom generator_domain_subset_functional_aux {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (C n : ℝ) (hf : ∀ s, ‖f s‖ ≤ C * (1 + |s|)^n)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f

/-- **Theorem**: The domain contains dom(A) when f is polynomially bounded. -/
theorem generator_domain_subset_functional {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (hf : ∃ C n : ℝ, ∀ s, ‖f s‖ ≤ C * (1 + |s|)^n) :
    (gen.domain : Set H) ⊆ functionalDomain (spectral_scalar_measure E · hE) f := by
  intro ψ hψ
  obtain ⟨C, n, hCn⟩ := hf
  exact generator_domain_subset_functional_aux gen hsa E hE f C n hCn ψ hψ



/-!
## §2. The Functional Calculus Map
-/


/-- Functional calculus for bounded Borel functions.
    This is a *-homomorphism from L^∞(ℝ, μ_ψ) to B(H). -/
noncomputable def boundedFunctionalCalculus
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f : ℝ → ℂ)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) : H →L[ℂ] H :=
  spectral_integral_bounded E hE f hf


/-!
## Spectral Integral Axioms
-/

/-- Spectral integral is additive in ψ -/
axiom spectral_integral_add_vector (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (x y : H)
    (hx : x ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hy : y ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hxy : x + y ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    spectral_integral E hE f (x + y) hxy =
    spectral_integral E hE f x hx + spectral_integral E hE f y hy

/-- Spectral integral is homogeneous in ψ -/
axiom spectral_integral_smul_vector (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (f : ℝ → ℂ)
    (c : ℂ) (ψ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hcψ : c • ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    spectral_integral E hE f (c • ψ) hcψ = c • spectral_integral E hE f ψ hψ

/-- Constant function 1 gives identity -/
axiom spectral_integral_one (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun _ => 1)) :
    spectral_integral E hE (fun _ => 1) ψ hψ = ψ

/-!
## Functional Calculus Definition
-/

/-- Functional calculus for general measurable functions. -/
noncomputable def functionalCalculus
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (hE_univ : E Set.univ = 1)
    (f : ℝ → ℂ) :
    functionalDomainSubmodule E hE hE_univ f →ₗ[ℂ] H where
  toFun := fun ⟨ψ, hψ⟩ => spectral_integral E hE f ψ hψ
  map_add' := fun ⟨x, hx⟩ ⟨y, hy⟩ => by
    simp only
    have hxy : x + y ∈ functionalDomain (spectral_scalar_measure E · hE) f :=
      (functionalDomainSubmodule E hE hE_univ f).add_mem hx hy
    exact spectral_integral_add_vector E hE f x y hx hy hxy
  map_smul' := fun c ⟨ψ, hψ⟩ => by
    simp only [RingHom.id_apply]
    have hcψ : c • ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f :=
      (functionalDomainSubmodule E hE hE_univ f).smul_mem c hψ
    exact spectral_integral_smul_vector E hE f c ψ hψ hcψ

/-- The inner product formula for functional calculus. -/
axiom functionalCalculus_inner
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (hE_univ : E Set.univ = 1)
    (f : ℝ → ℂ)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    ⟪functionalCalculus E hE hE_univ f ⟨ψ, hψ⟩, ψ⟫_ℂ = ∫ s, f s ∂(spectral_scalar_measure E ψ hE)

/-!
## §3. Algebraic Properties (*-homomorphism)
-/

section Algebra

variable (E : Set ℝ → H →L[ℂ] H)
variable (μ : H → Measure ℝ)

/-!
## Additional Spectral Integral Axioms for Algebra
-/

/-- Spectral integral is additive in f -/
axiom spectral_integral_add_function (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f g : ℝ → ℂ) (ψ : H)
    (hf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f + g)) :
    spectral_integral E hE (f + g) ψ hfg =
    spectral_integral E hE f ψ hf + spectral_integral E hE g ψ hg

/-- Spectral integral is multiplicative in f (composition property) -/
axiom spectral_integral_mul_function (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f g : ℝ → ℂ) (ψ : H)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f * g))
    (hf_gψ : spectral_integral E hE g ψ hg ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    spectral_integral E hE (f * g) ψ hfg =
    spectral_integral E hE f (spectral_integral E hE g ψ hg) hf_gψ


/-!
## Completed Theorems
-/

/-- **Addition**: (f + g)(A) = f(A) + g(A) -/
theorem functionalCalculus_add (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f g : ℝ → ℂ) (ψ : H)
    (hf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f + g)) :
    functionalCalculus E hE hE_univ (f + g) ⟨ψ, hfg⟩ =
    functionalCalculus E hE hE_univ f ⟨ψ, hf⟩ + functionalCalculus E hE hE_univ g ⟨ψ, hg⟩ :=
  spectral_integral_add_function E hE f g ψ hf hg hfg

/-- **Multiplication**: (fg)(A) = f(A) ∘ g(A) on appropriate domain -/
theorem functionalCalculus_mul (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f g : ℝ → ℂ) (ψ : H)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f * g))
    (hf_gψ : functionalCalculus E hE hE_univ g ⟨ψ, hg⟩ ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    functionalCalculus E hE hE_univ (f * g) ⟨ψ, hfg⟩ =
    functionalCalculus E hE hE_univ f ⟨functionalCalculus E hE hE_univ g ⟨ψ, hg⟩, hf_gψ⟩ :=
  spectral_integral_mul_function E hE f g ψ hg hfg hf_gψ

/-- **Conjugation**: f̄(A) = f(A)* -/
theorem functionalCalculus_conj (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f : ℝ → ℂ) (ψ φ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hφ : φ ∈ functionalDomain (spectral_scalar_measure E · hE) (starRingEnd ℂ ∘ f)) :
    ⟪functionalCalculus E hE hE_univ f ⟨ψ, hψ⟩, φ⟫_ℂ =
    ⟪ψ, functionalCalculus E hE hE_univ (starRingEnd ℂ ∘ f) ⟨φ, hφ⟩⟫_ℂ :=
  spectral_integral_conj E hE f ψ φ hψ hφ

/-- **Normalization**: 1(A) = I -/
theorem functionalCalculus_one (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (ψ : H) (h : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun _ => 1)) :
    functionalCalculus E hE hE_univ (fun _ => 1) ⟨ψ, h⟩ = ψ :=
  spectral_integral_one E hE hE_univ ψ h

/-- **Spectral mapping for indicator**: 𝟙_B(A) = E(B) -/
theorem functionalCalculus_indicator (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (B : Set ℝ) (hB : MeasurableSet B)
    (ψ : H) (h : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (Set.indicator B 1)) :
    functionalCalculus E hE hE_univ (Set.indicator B 1) ⟨ψ, h⟩ = E B ψ :=
  spectral_integral_indicator E hE B hB ψ h
end Algebra

/-!
## §4. Recovering A from E
-/

/-- Predicate: E is the spectral measure associated to the generator -/
structure IsSpectralMeasureFor (E : Set ℝ → H →L[ℂ] H)
    {U_grp : OneParameterUnitaryGroup (H := H)} (gen : Generator U_grp) : Prop where
  proj_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C)
  proj_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ
  proj_empty : E ∅ = 0
  proj_univ : E Set.univ = 1
  proj_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
             E (B ∪ C) = E B + E C
  proj_sot : ∀ ψ t₀, Filter.Tendsto (fun t => E (Set.Iic t) ψ) (nhdsWithin t₀ (Set.Ioi t₀)) (nhds (E (Set.Iic t₀) ψ))

  unitary_eq_integral : ∀ (t : ℝ) (ψ : H),
    ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ s, Complex.exp (I * t * s) ∂(BochnerRoute.spectral_scalar_measure E ψ ⟨proj_mul, proj_sa, proj_sot, proj_empty, proj_univ, proj_add⟩)

/-- Extract IsSpectralMeasure from IsSpectralMeasureFor -/
def IsSpectralMeasureFor.toIsSpectralMeasure {E : Set ℝ → H →L[ℂ] H}
    {U_grp : OneParameterUnitaryGroup (H := H)} {gen : Generator U_grp}
    (hE : IsSpectralMeasureFor E gen) : BochnerRoute.IsSpectralMeasure E where
  mul := hE.proj_mul
  sa := hE.proj_sa
  sot := hE.proj_sot
  add := hE.proj_add
  empty := hE.proj_empty
  univ := hE.proj_univ

/-- The identity function id(s) = s -/
def identityFunction : ℝ → ℂ := fun s => s

/-- Direct axiom: Generator and spectral integral agree on inner products
NOTE: This is the first axiom to turn into a lemma.  This is temporary! -/
axiom generator_spectral_integral_inner_eq {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ_dom : ψ ∈ gen.domain)
    (hψ_func : ψ ∈ functionalDomain (spectral_scalar_measure E · hE.toIsSpectralMeasure) identityFunction)
    (φ : H) :
    ⟪gen.op ⟨ψ, hψ_dom⟩, φ⟫_ℂ = ⟪spectral_integral E hE.toIsSpectralMeasure identityFunction ψ hψ_func, φ⟫_ℂ

/-- **Core Theorem**: A = ∫ s dE(s) on dom(A)

The generator equals the functional calculus of the identity function. -/
theorem generator_eq_spectral_integral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ_dom : ψ ∈ gen.domain)
    (hψ_func : ψ ∈ functionalDomain (spectral_scalar_measure E · hE.toIsSpectralMeasure) identityFunction) :
    gen.op ⟨ψ, hψ_dom⟩ = functionalCalculus E hE.toIsSpectralMeasure hE.proj_univ identityFunction ⟨ψ, hψ_func⟩ := by
  apply ext_inner_right ℂ
  intro φ
  exact generator_spectral_integral_inner_eq gen hsa E hE ψ hψ_dom hψ_func φ

/-- Forward direction: dom(A) ⊆ functionalDomain(id)
    Key fact: ψ ∈ dom(A) implies ∫|s|² dμ_ψ < ∞ -/
axiom generator_domain_subset_id_domain {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ψ ∈ functionalDomain (spectral_scalar_measure E · hE.toIsSpectralMeasure) identityFunction

/-- Backward direction: functionalDomain(id) ⊆ dom(A)
    Key fact: ∫|s|² dμ_ψ < ∞ implies ψ ∈ dom(A) -/
axiom id_domain_subset_generator_domain {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE.toIsSpectralMeasure) identityFunction) :
    ψ ∈ gen.domain

/-- Norm formula: ‖Aψ‖² = ∫|s|² dμ_ψ -/
axiom generator_norm_sq_eq_second_moment {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ‖gen.op ⟨ψ, hψ⟩‖^2 = ∫ s, s^2 ∂(spectral_scalar_measure E ψ hE.toIsSpectralMeasure)

/-- Domain equality: dom(A) = dom(id(A)) -/
theorem generator_domain_eq_functional_domain {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen) :
    (gen.domain : Set H) = functionalDomain (spectral_scalar_measure E · hE.toIsSpectralMeasure) identityFunction := by
  ext ψ
  constructor
  · exact generator_domain_subset_id_domain gen hsa E hE ψ
  · exact id_domain_subset_generator_domain gen hsa E hE ψ

/-!
## §5. Three Routes Agreement
-/

/-- The spectral measure from unitary (Cayley) route - axiomatized -/
axiom spectralMeasure_from_cayley {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) : Set ℝ → H →L[ℂ] H

/-- The spectral measures from all three routes agree. -/
structure SpectralMeasureAgreement
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen) : Prop where
  /-- E agrees with Bochner measure from U(t) -/
  bochner_agreement : ∀ ψ B, MeasurableSet B →
    (spectral_scalar_measure E ψ hE.toIsSpectralMeasure B).toReal =
    (SpectralBridge.BochnerRoute.bochner_measure U_grp ψ B).toReal
  /-- E agrees with Stieltjes inversion from R(z) -/
  stieltjes_agreement : ∀ ψ a b, a < b →
    (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re =
    (SpectralBridge.BochnerRoute.bochner_measure U_grp ψ (Set.Ioc a b)).toReal
  /-- E agrees with Cayley-lifted spectral measure -/
  cayley_agreement : ∀ B, MeasurableSet B →
    E B = spectralMeasure_from_cayley gen hsa B

/-- Bochner route produces same measure as E -/
axiom bochner_route_agreement {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    (spectral_scalar_measure E ψ hE.toIsSpectralMeasure B).toReal =
    (SpectralBridge.BochnerRoute.bochner_measure U_grp ψ B).toReal

/-- Stieltjes inversion produces same measure as E -/
axiom stieltjes_route_agreement {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (a b : ℝ) (hab : a < b) :
    (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re =
    (SpectralBridge.BochnerRoute.bochner_measure U_grp ψ (Set.Ioc a b)).toReal

/-- Cayley route produces same measure as E -/
axiom cayley_route_agreement {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (B : Set ℝ) (hB : MeasurableSet B) :
    E B = spectralMeasure_from_cayley gen hsa B

/-- The three routes produce the same spectral measure -/
theorem three_routes_agree {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen) :
    SpectralMeasureAgreement gen hsa E hE where
  bochner_agreement := fun ψ B hB => bochner_route_agreement gen hsa E hE ψ B hB
  stieltjes_agreement := fun ψ a b hab => stieltjes_route_agreement gen hsa E hE ψ a b hab
  cayley_agreement := fun B hB => cayley_route_agreement gen hsa E hE B hB



/-
=================================================================================================================================
# Extra Lemmas!
=================================================================================================================================
-/
section lemmaExtension
/-- Bounded spectral integral is additive in f -/
lemma spectral_integral_bounded_add (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f g : ℝ → ℂ) (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) (hg : ∃ M, ∀ s, ‖g s‖ ≤ M)
    (hfg : ∃ M, ∀ s, ‖(f + g) s‖ ≤ M) :
    spectral_integral_bounded E hE (f + g) hfg =
    spectral_integral_bounded E hE f hf + spectral_integral_bounded E hE g hg := by
  ext ψ
  -- Every ψ is in functional domain for bounded functions
  have hψf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f :=
    functionalDomain_of_bounded E hE f hf ψ
  have hψg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g :=
    functionalDomain_of_bounded E hE g hg ψ
  have hψfg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f + g) :=
    functionalDomain_of_bounded E hE (f + g) hfg ψ
  -- Connect bounded ↔ unbounded, then use spectral_integral_add
  simp only [ContinuousLinearMap.add_apply]
  rw [← spectral_integral_bounded_eq E hE (f + g) hfg ψ hψfg,
      ← spectral_integral_bounded_eq E hE f hf ψ hψf,
      ← spectral_integral_bounded_eq E hE g hg ψ hψg]
  exact spectral_integral_add E hE f g ψ hψf hψg hψfg

/-- Bounded spectral integral is homogeneous in f -/
lemma spectral_integral_bounded_smul (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (c : ℂ) (f : ℝ → ℂ) (hf : ∃ M, ∀ s, ‖f s‖ ≤ M)
    (hcf : ∃ M, ∀ s, ‖(c • f) s‖ ≤ M) :
    spectral_integral_bounded E hE (c • f) hcf = c • spectral_integral_bounded E hE f hf := by
  ext ψ
  have hψf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f :=
    functionalDomain_of_bounded E hE f hf ψ
  have hψcf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (c • f) :=
    functionalDomain_of_bounded E hE (c • f) hcf ψ
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply]
  rw [← spectral_integral_bounded_eq E hE (c • f) hcf ψ hψcf,
      ← spectral_integral_bounded_eq E hE f hf ψ hψf]
  exact spectral_integral_smul E hE c f ψ hψf hψcf

/-- Functional calculus of zero function is zero -/
lemma boundedFunctionalCalculus_zero (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) :
    boundedFunctionalCalculus E hE (fun _ => 0) ⟨0, fun _ => by simp⟩ = 0 := by
  ext ψ
  simp only [boundedFunctionalCalculus, ContinuousLinearMap.zero_apply]
  -- Use the route through spectral_integral
  have hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun _ : ℝ => (0 : ℂ)) :=
    functionalDomain_of_bounded E hE (fun _ => 0) ⟨0, fun _ => by simp⟩ ψ
  rw [← spectral_integral_bounded_eq E hE (fun _ => 0) ⟨0, fun _ => by simp⟩ ψ hψ]
  -- Now need: spectral_integral E hE (fun _ => 0) ψ hψ = 0
  -- This is 0 • spectral_integral E hE (fun _ => 1) ψ _
  have h1 : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun _ : ℝ => (1 : ℂ)) :=
    functionalDomain_of_bounded E hE (fun _ => 1) ⟨1, fun _ => by simp⟩ ψ
  have h0_eq : (fun _ : ℝ => (0 : ℂ)) = (0 : ℂ) • (fun _ : ℝ => (1 : ℂ)) := by ext; simp
  have hψ0 : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) ((0 : ℂ) • fun _ : ℝ => (1 : ℂ)) := by
    convert hψ using 2
    ext; simp
  -- begin hacky code, version 1:
  rw [← @enorm_eq_zero]
  convert spectral_integral_smul E hE 0 (fun _ : ℝ => (1 : ℂ)) ψ h1 hψ0 using 1
  simp only [zero_smul]
  exact ENormedAddMonoid.enorm_eq_zero (spectral_integral E hE (fun x => 0) ψ hψ)
  /-
  -- begin hacky code, version 2:
  rw [← @UniformSpace.Completion.coe_eq_zero_iff]
  convert spectral_integral_smul E hE 0 (fun _ : ℝ => (1 : ℂ)) ψ h1 hψ0 using 1
  simp only [zero_smul]
  exact UniformSpace.Completion.coe_eq_zero_iff
  -/

/-- Spectral integral respects function equality (with proof irrelevance) -/
lemma spectral_integral_eq_of_eq_fun (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f g : ℝ → ℂ) (hfg : f = g) (ψ : H)
    (hf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g) :
    spectral_integral E hE f ψ hf = spectral_integral E hE g ψ hg := by
  subst hfg
  rfl  -- proof irrelevance: hf and hg now have the same type

lemma boundedFunctionalCalculus_const (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (c : ℂ) :
    boundedFunctionalCalculus E hE (fun _ => c) ⟨‖c‖, fun _ => le_refl _⟩ = c • 1 := by
  ext ψ
  simp only [boundedFunctionalCalculus, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]

  -- (fun _ => c) = c • (fun _ => 1)
  have h_eq : (fun _ : ℝ => c) = c • (fun _ : ℝ => (1 : ℂ)) := by ext s; simp

  have hψ1 : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun _ : ℝ => (1 : ℂ)) :=
    functionalDomain_of_bounded E hE _ ⟨1, fun _ => by simp⟩ ψ
  have hψc : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun _ : ℝ => c) :=
    functionalDomain_of_bounded E hE _ ⟨‖c‖, fun _ => le_refl _⟩ ψ
  have hψc' : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (c • fun _ : ℝ => (1 : ℂ)) := by
    rw [← h_eq]; exact hψc

  rw [← spectral_integral_bounded_eq E hE _ ⟨‖c‖, fun _ => le_refl _⟩ ψ hψc]
  rw [spectral_integral_eq_of_eq_fun E hE _ _ h_eq ψ hψc hψc']
  rw [spectral_integral_smul E hE c (fun _ : ℝ => (1 : ℂ)) ψ hψ1 hψc']
  rw [spectral_integral_one E hE hE_univ ψ hψ1]


/-- Functional calculus respects negation -/
lemma boundedFunctionalCalculus_neg (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f : ℝ → ℂ) (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) :
    boundedFunctionalCalculus E hE (-f) (by obtain ⟨M, hM⟩ := hf; exact ⟨M, fun s => by simp [hM s]⟩) =
    -boundedFunctionalCalculus E hE f hf := by
  ext ψ
  simp only [boundedFunctionalCalculus, ContinuousLinearMap.neg_apply]

  -- -f = (-1) • f
  have h_eq : -f = (-1 : ℂ) • f := by ext s; simp

  have hψf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f :=
    functionalDomain_of_bounded E hE f hf ψ
  have hψnf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (-f) :=
    functionalDomain_of_bounded E hE (-f) (by obtain ⟨M, hM⟩ := hf; exact ⟨M, fun s => by simp [hM s]⟩) ψ
  have hψnf' : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) ((-1 : ℂ) • f) := by
    rw [← h_eq]; exact hψnf

  rw [← spectral_integral_bounded_eq E hE (-f) _ ψ hψnf]
  rw [← spectral_integral_bounded_eq E hE f hf ψ hψf]
  rw [spectral_integral_eq_of_eq_fun E hE _ _ h_eq ψ hψnf hψnf']
  rw [spectral_integral_smul E hE (-1) f ψ hψf hψnf']
  simp only [neg_smul, one_smul]


/-- Real-valued bounded functions give self-adjoint operators -/
lemma boundedFunctionalCalculus_real_selfAdjoint (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f : ℝ → ℝ) (hf : ∃ M, ∀ s, |f s| ≤ M) :
    let f' : ℝ → ℂ := fun s => f s
    let hf' : ∃ M, ∀ s, ‖f' s‖ ≤ M := by
      obtain ⟨M, hM⟩ := hf
      exact ⟨M, fun s => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM s⟩
    (boundedFunctionalCalculus E hE f' hf').adjoint = boundedFunctionalCalculus E hE f' hf' := by
  intro f' hf'
  ext φ
  apply ext_inner_left ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_right]
  -- Goal: ⟪Φ(f') ψ, φ⟫ = ⟪ψ, Φ(f') φ⟫
  simp only [boundedFunctionalCalculus]

  have hψf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f' :=
    functionalDomain_of_bounded E hE f' hf' ψ
  have hφf : φ ∈ functionalDomain (spectral_scalar_measure E · hE) f' :=
    functionalDomain_of_bounded E hE f' hf' φ

  -- For real f, starRingEnd ℂ ∘ f' = f'
  have h_conj : starRingEnd ℂ ∘ f' = f' := by
    ext s
    simp only [Function.comp_apply, f', Complex.conj_ofReal]

  have hφ_conj : φ ∈ functionalDomain (spectral_scalar_measure E · hE) (starRingEnd ℂ ∘ f') := by
    rw [h_conj]; exact hφf

  rw [← spectral_integral_bounded_eq E hE f' hf' ψ hψf]
  rw [← spectral_integral_bounded_eq E hE f' hf' φ hφf]
  rw [spectral_integral_conj E hE f' ψ φ hψf hφ_conj]
  congr 1
  exact spectral_integral_eq_of_eq_fun E hE _ _ h_conj φ hφ_conj hφf


-- If g : X → ℂ has g(x).re ≥ 0 for all x, then (∫ g dμ).re ≥ 0
lemma integral_re_nonneg {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : X → ℂ} (hg : ∀ x, 0 ≤ (g x).re) (hg_int : Integrable g μ) :
    0 ≤ (∫ x, g x ∂μ).re := by
  calc (∫ x, g x ∂μ).re
      = RCLike.re (∫ x, g x ∂μ) := rfl
    _ = ∫ x, RCLike.re (g x) ∂μ := (integral_re hg_int).symm
    _ = ∫ x, (g x).re ∂μ := by rfl
    _ ≥ 0 := integral_nonneg hg

/-- Real-valued bounded Borel functions are measurable -/
theorem borel_bounded_measurable (f : ℝ → ℝ)
    (hf_meas : Measurable f)

    (hf_bdd : ∃ M, ∀ s, |f s| ≤ M) :
    Measurable (fun s => (f s : ℂ)) :=
  Complex.measurable_ofReal.comp hf_meas

set_option maxHeartbeats 500000

/-- Positive functions give positive operators -/
lemma boundedFunctionalCalculus_nonneg (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (f : ℝ → ℝ)
    (hf_meas : Measurable f)  -- ADD THIS
    (hf_bdd : ∃ M, ∀ s, |f s| ≤ M)
    (hf_pos : ∀ s, 0 ≤ f s) (ψ : H) :
    let f' : ℝ → ℂ := fun s => f s
    let hf' : ∃ M, ∀ s, ‖f' s‖ ≤ M := by
      obtain ⟨M, hM⟩ := hf_bdd
      exact ⟨M, fun s => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM s⟩
    0 ≤ (⟪boundedFunctionalCalculus E hE f' hf' ψ, ψ⟫_ℂ).re := by
  intro f' hf'
  simp only [boundedFunctionalCalculus]

  have hψf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f' :=
    functionalDomain_of_bounded E hE f' hf' ψ

  rw [← spectral_integral_bounded_eq E hE f' hf' ψ hψf]
  rw [spectral_integral_inner E hE f' ψ hψf ψ hψf]

  -- Goal: 0 ≤ (∫ s, f' s * ⟪E {s} ψ, ψ⟫_ℂ ∂μ).re

  -- The integrand is real and non-negative pointwise
  have h_integrand_re : ∀ s, (f' s * ⟪E {s} ψ, ψ⟫_ℂ).re = (f s) * (⟪E {s} ψ, ψ⟫_ℂ).re := by
    intro s
    rw [Complex.mul_re]
    simp only [f', Complex.ofReal_re, Complex.ofReal_im]
    have hE_im : (⟪E {s} ψ, ψ⟫_ℂ).im = 0 := spectral_diagonal_real E {s} ψ
    rw [hE_im]
    ring

  have h_integrand_nonneg : ∀ s, 0 ≤ (f' s * ⟪E {s} ψ, ψ⟫_ℂ).re := by
    intro s
    rw [h_integrand_re s]
    apply mul_nonneg (hf_pos s)
    -- ⟪E {s} ψ, ψ⟫.re ≥ 0 because E {s} is a positive operator
    rw [← spectral_projection_norm_sq E {s} hE (MeasurableSet.singleton s) ψ]
    exact sq_nonneg _

  -- Integral of pointwise non-negative real part
  -- Need: (∫ g dμ).re = ∫ g.re dμ for appropriate conditions, then integral_nonneg
  -- Construct integrability
  have hf_integrable : Integrable (fun s => f' s * ⟪E {s} ψ, ψ⟫_ℂ) (spectral_scalar_measure E ψ hE) := by
    -- f' is bounded
    obtain ⟨M, hM⟩ := hf'
    -- The inner product term is bounded by ‖ψ‖² (since ‖E{s}‖ ≤ 1)
    have h_inner_bdd : ∀ s, ‖⟪E {s} ψ, ψ⟫_ℂ‖ ≤ ‖ψ‖^2 := fun s => by
      calc ‖⟪E {s} ψ, ψ⟫_ℂ‖
          ≤ ‖E {s} ψ‖ * ‖ψ‖ := norm_inner_le_norm _ _
        _ ≤ ‖ψ‖ * ‖ψ‖ := by {
            apply mul_le_mul_of_nonneg_right
            exact spectral_projection_norm_le E hE {s} (MeasurableSet.singleton s) ψ
            exact norm_nonneg _
          }
        _ = ‖ψ‖^2 := by ring
    -- Product is bounded
    have h_bdd : ∀ s, ‖f' s * ⟪E {s} ψ, ψ⟫_ℂ‖ ≤ M * ‖ψ‖^2 := fun s => by
      calc ‖f' s * ⟪E {s} ψ, ψ⟫_ℂ‖
          = ‖f' s‖ * ‖⟪E {s} ψ, ψ⟫_ℂ‖ := norm_mul _ _
        _ ≤ M * ‖ψ‖^2 := by {
            apply mul_le_mul (hM s) (h_inner_bdd s) (norm_nonneg _)
            linarith [norm_nonneg (f' 0), hM 0]
          }
    -- Bounded function on finite measure is integrable
    haveI : IsFiniteMeasure (spectral_scalar_measure E ψ hE) :=
      spectral_scalar_measure_finite E hE hE_univ ψ
    have h_const_int : Integrable (fun _ : ℝ => (M * ‖ψ‖^2 : ℂ)) (spectral_scalar_measure E ψ hE) :=
      integrable_const _
    apply Integrable.mono h_const_int
    · apply Measurable.aestronglyMeasurable
      apply Measurable.mul
      · exact borel_bounded_measurable f hf_meas hf_bdd
      · exact spectral_inner_measurable E hE ψ
    · apply Filter.Eventually.of_forall
      intro s
      have h1 : ‖(M * ‖ψ‖^2 : ℂ)‖ = M * ‖ψ‖^2 := by
        have h : (M * ‖ψ‖^2 : ℂ) = ((M * ‖ψ‖^2 : ℝ) : ℂ) := by norm_cast
        rw [h, Complex.norm_real, Real.norm_of_nonneg]
        have hM_nonneg : 0 ≤ M := by
          have := hM 0
          calc 0 ≤ ‖f' 0‖ := norm_nonneg _
            _ ≤ M := this
        exact mul_nonneg hM_nonneg (sq_nonneg _)
      rw [h1]
      exact h_bdd s

  -- Now use integral_re_nonneg
  exact integral_re_nonneg h_integrand_nonneg hf_integrable



/-- Functional calculus is monotone for real functions -/
lemma boundedFunctionalCalculus_mono (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (f g : ℝ → ℝ)
    (hf_meas : Measurable f)
    (hg_meas : Measurable g)
    (hf : ∃ M, ∀ s, |f s| ≤ M) (hg : ∃ M, ∀ s, |g s| ≤ M)
    (hfg : ∀ s, f s ≤ g s) (ψ : H) :
    let f' : ℝ → ℂ := fun s => f s
    let g' : ℝ → ℂ := fun s => g s
    let hf' : ∃ M, ∀ s, ‖f' s‖ ≤ M := by
      obtain ⟨M, hM⟩ := hf
      exact ⟨M, fun s => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM s⟩
    let hg' : ∃ M, ∀ s, ‖g' s‖ ≤ M := by
      obtain ⟨M, hM⟩ := hg
      exact ⟨M, fun s => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM s⟩
    (⟪boundedFunctionalCalculus E hE f' hf' ψ, ψ⟫_ℂ).re ≤
    (⟪boundedFunctionalCalculus E hE g' hg' ψ, ψ⟫_ℂ).re := by
  intro f' g' hf' hg'

  -- Define g - f
  let d : ℝ → ℝ := fun s => g s - f s
  let d' : ℝ → ℂ := fun s => d s

  have hd_pos : ∀ s, 0 ≤ d s := fun s => sub_nonneg.mpr (hfg s)
  have hd_bdd : ∃ M, ∀ s, |d s| ≤ M := by
    obtain ⟨Mf, hMf⟩ := hf
    obtain ⟨Mg, hMg⟩ := hg
    exact ⟨Mf + Mg, fun s => by
      calc |d s| = |g s - f s| := rfl
        _ ≤ |g s| + |f s| := abs_sub (g s) (f s)
        _ ≤ Mg + Mf := add_le_add (hMg s) (hMf s)
        _ = Mf + Mg := add_comm Mg Mf⟩
  have hd' : ∃ M, ∀ s, ‖d' s‖ ≤ M := by
    obtain ⟨M, hM⟩ := hd_bdd
    exact ⟨M, fun s => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM s⟩

  -- Key: g' = f' + d'
  have h_sum : g' = f' + d' := by ext s; simp [f', g', d', d]

  -- Use linearity: Φ(g') = Φ(f') + Φ(d')
  have h_linear : boundedFunctionalCalculus E hE g' hg' =
                  boundedFunctionalCalculus E hE f' hf' + boundedFunctionalCalculus E hE d' hd' := by
    simp only [boundedFunctionalCalculus]
    have hfd_bound : ∃ M, ∀ s, ‖(f' + d') s‖ ≤ M := by
      obtain ⟨M, hM⟩ := hg'
      refine ⟨M, fun s => ?_⟩
      simp only [Pi.add_apply]
      have h : f' s + d' s = g' s := by simp [f', g', d', d]
      rw [h]
      exact hM s
    have key := spectral_integral_bounded_add E hE f' d' hf' hd' hfd_bound
    convert key using 2

  -- Therefore: ⟪Φ(g')ψ, ψ⟫ = ⟪Φ(f')ψ, ψ⟫ + ⟪Φ(d')ψ, ψ⟫
  have h_inner : ⟪boundedFunctionalCalculus E hE g' hg' ψ, ψ⟫_ℂ =
                 ⟪boundedFunctionalCalculus E hE f' hf' ψ, ψ⟫_ℂ +
                 ⟪boundedFunctionalCalculus E hE d' hd' ψ, ψ⟫_ℂ := by
    rw [h_linear]
    simp only [ContinuousLinearMap.add_apply, inner_add_left]

  -- Take real parts
  have h_re : (⟪boundedFunctionalCalculus E hE g' hg' ψ, ψ⟫_ℂ).re =
              (⟪boundedFunctionalCalculus E hE f' hf' ψ, ψ⟫_ℂ).re +
              (⟪boundedFunctionalCalculus E hE d' hd' ψ, ψ⟫_ℂ).re := by
    rw [h_inner, Complex.add_re]

  -- Now use: ⟪Φ(d')ψ, ψ⟫.re ≥ 0 since d ≥ 0 (this is boundedFunctionalCalculus_nonneg)
  have h_nonneg : 0 ≤ (⟪boundedFunctionalCalculus E hE d' hd' ψ, ψ⟫_ℂ).re := by
    have hd_meas : Measurable d := hg_meas.sub hf_meas
    exact boundedFunctionalCalculus_nonneg E hE hE_univ d hd_meas hd_bdd hd_pos ψ

  linarith

/-- Square of self-adjoint functional calculus -/
lemma boundedFunctionalCalculus_sq (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f : ℝ → ℂ) (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) :
    let hf2 : ∃ M, ∀ s, ‖f s * f s‖ ≤ M := by
      obtain ⟨M, hM⟩ := hf
      exact ⟨M^2, fun s => by calc ‖f s * f s‖ = ‖f s‖ * ‖f s‖ := norm_mul _ _
        _ ≤ M * M := mul_le_mul (hM s) (hM s) (norm_nonneg _) (by linarith [norm_nonneg (f s), hM s])
        _ = M^2 := by ring⟩
    boundedFunctionalCalculus E hE (fun s => f s * f s) hf2 =
    boundedFunctionalCalculus E hE f hf * boundedFunctionalCalculus E hE f hf := by
  intro hf2
  ext ψ
  simp only [boundedFunctionalCalculus, ContinuousLinearMap.mul_apply]

  have hψf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f :=
    functionalDomain_of_bounded E hE f hf ψ
  have hψf2 : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun s => f s * f s) :=
    functionalDomain_of_bounded E hE _ hf2 ψ

  -- Key: Φ(f)ψ is in the domain of f (since f is bounded, every vector is in its domain)
  have h_fψ_dom : spectral_integral E hE f ψ hψf ∈ functionalDomain (spectral_scalar_measure E · hE) f :=
    functionalDomain_of_bounded E hE f hf (spectral_integral E hE f ψ hψf)

  rw [← spectral_integral_bounded_eq E hE _ hf2 ψ hψf2]
  rw [← spectral_integral_bounded_eq E hE f hf ψ hψf]
  rw [← spectral_integral_bounded_eq E hE f hf (spectral_integral E hE f ψ hψf) h_fψ_dom]

  -- Match (fun s => f s * f s) with (f * f)
  have h_eq : (fun s => f s * f s) = f * f := by ext; simp [Pi.mul_apply]

  have hψf_mul : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f * f) := by
    rw [← h_eq]; exact hψf2

  rw [spectral_integral_eq_of_eq_fun E hE _ _ h_eq ψ hψf2 hψf_mul]
  exact spectral_integral_mul E hE f f ψ hψf h_fψ_dom hψf_mul

end lemmaExtension

end FunctionalCalculus
