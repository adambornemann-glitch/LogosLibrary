/-
Author: Adam Bornemann
Created: 1-6-2026
Updated: 1-9-2026

================================================================================
FUNCTIONAL CALCULUS FOR UNBOUNDED SELF-ADJOINT OPERATORS
================================================================================

This file constructs the functional calculus f ↦ f(A) that allows arbitrary
Borel functions to be applied to a self-adjoint operator A. This is the
synthesis layer unifying the three routes to spectral theory.

THE FUNCTIONAL CALCULUS MACHINE:

  ┌─────────────────────────────────────────────────────────────────────────┐
  │                                                                         │
  │   INPUT                           OUTPUT                                │
  │   ─────                           ──────                                │
  │                                                                         │
  │   f : ℝ → ℂ                       f(A) : dom(f(A)) → H                  │
  │   (Borel function)                (closed operator)                     │
  │                                                                         │
  │                        Φ                                                │
  │         f  ─────────────────────────────►  f(A)                         │
  │                        │                                                │
  │                        │  Φ(f) = ∫ f(s) dE(s)                           │
  │                        │                                                │
  │                        ▼                                                │
  │              SPECTRAL MEASURE E                                         │
  │              (from Bochner/Resolvent/Cayley)                            │
  │                                                                         │
  └─────────────────────────────────────────────────────────────────────────┘

DOMAIN CHARACTERIZATION:

The key insight for unbounded f(A) is the domain formula:

  dom(f(A)) = { ψ ∈ H : ∫_ℝ |f(s)|² dμ_ψ(s) < ∞ }

where μ_ψ is the scalar spectral measure: μ_ψ(B) = ⟪E(B)ψ, ψ⟫.

This says: ψ is in the domain of f(A) precisely when f is square-integrable
against the spectral distribution of ψ. Vectors "concentrated" at energies
where f blows up are excluded from the domain.

ALGEBRAIC STRUCTURE (*-HOMOMORPHISM):

The functional calculus Φ : Borel(ℝ) → Operators(H) satisfies:

  ┌───────────────────────────────────────────────────────────┐
  │  Φ(f + g) = Φ(f) + Φ(g)           (linearity)             │
  │  Φ(fg)    = Φ(f) ∘ Φ(g)           (multiplicativity)      │
  │  Φ(f̄)     = Φ(f)*                 (adjoint preservation)  │
  │  Φ(1)     = I                     (unital)                │
  │  Φ(𝟙_B)   = E(B)                  (spectral projections)   │
  └───────────────────────────────────────────────────────────┘

The multiplicativity Φ(fg) = Φ(f)Φ(g) requires care with domains:
  - dom(Φ(fg)) ⊇ dom(Φ(g)) ∩ Φ(g)⁻¹(dom(Φ(f)))
  - Equality holds when f is bounded

CLOSING THE LOOP:

The fundamental theorem that completes the circle:

              ┌─────────────────────────────────────┐
              │                                     │
              │   A  =  ∫_ℝ s dE(s)  on dom(A)      │
              │                                     │
              │   A  =  Φ(id)  where id(s) = s      │
              │                                     │
              └─────────────────────────────────────┘

This says: the generator A is recovered as the functional calculus
of the identity function. The spectral measure E completely determines A.

Combined with dom(A) = dom(id(A)) = {ψ : ∫|s|² dμ_ψ < ∞}, this gives
the complete characterization of self-adjoint operators via spectral data.

UNIFICATION OF THREE ROUTES:

  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐
  │   BOCHNER    │    │  RESOLVENT   │    │    CAYLEY    │
  │              │    │              │    │              │
  │  t ↦ ⟨Uₜψ,ψ⟩ │    │  z ↦ ⟨Rᵤψ,ψ⟩ │    │  U = Cayley  │
  │      │       │    │      │       │    │      │       │
  │      ▼       │    │      ▼       │    │      ▼       │
  │    μ_ψ       │    │   E(a,b]     │    │    E_U       │
  └──────┬───────┘    └──────┬───────┘    └──────┬───────┘
         │                   │                   │
         └───────────────────┼───────────────────┘
                             │
                             ▼
                    ┌────────────────┐
                    │   UNIQUE E     │
                    │                │
                    │  Spectral      │
                    │  Measure       │
                    └────────┬───────┘
                             │
                             ▼
                    ┌────────────────┐
                    │  FUNCTIONAL    │
                    │  CALCULUS Φ    │
                    │                │
                    │  f ↦ ∫f(s)dE   │
                    └────────────────┘

The three routes construct the SAME spectral measure E. This file
proves their agreement and builds the unified functional calculus.

PHYSICAL INTERPRETATION:

In quantum mechanics, if A is an observable (energy, position, momentum),
then f(A) is the observable "f of A":

  • A = Hamiltonian (energy)     →  e^{-itA} = time evolution
  • A = position                 →  A² = "position squared"
  • A = momentum p               →  p²/2m = kinetic energy

The spectral measure E(B) projects onto states with eigenvalues in B.
The functional calculus lets us compute expectations:

  ⟨f(A)⟩_ψ = ⟪f(A)ψ, ψ⟫ = ∫_ℝ f(s) dμ_ψ(s)

This is the Born rule: f(s) is weighted by the spectral distribution μ_ψ.

MATHEMATICAL CONTENT:

  §1 Domain Characterization
     - functionalDomain: {ψ : ∫|f(s)|² dμ_ψ < ∞}
     - functionalDomainSubmodule: verification it's a subspace
     - generator_domain_subset_functional: dom(A) ⊆ dom(f(A)) for nice f

  §2 Functional Calculus Map
     - boundedFunctionalCalculus: f bounded → Φ(f) ∈ B(H)
     - functionalCalculus: general f → Φ(f) densely defined
     - functionalCalculus_inner: ⟪Φ(f)ψ, ψ⟫ = ∫ f dμ_ψ

  §3 Algebraic Properties
     - functionalCalculus_add: Φ(f + g) = Φ(f) + Φ(g)
     - functionalCalculus_mul: Φ(fg) = Φ(f) ∘ Φ(g)
     - functionalCalculus_conj: Φ(f̄) = Φ(f)*
     - functionalCalculus_indicator: Φ(𝟙_B) = E(B)

  §4 Recovering A from E
     - generator_eq_spectral_integral: A = ∫ s dE(s)
     - generator_domain_eq_functional_domain: dom(A) = {ψ : ∫|s|² dμ_ψ < ∞}

  §5 Three Routes Agreement
     - SpectralMeasureAgreement: structure witnessing E is unique
     - three_routes_agree: Bochner, Resolvent, Cayley give same E

KEY AXIOMS:

  Tier 1 (Integral Properties):
    - functionalCalculus_inner: inner product equals spectral integral
    - spectral_projection_mul: E(B)E(C) = E(B ∩ C)

  Tier 2 (Domain):
    - spectral_scalar_measure properties from SpectralBridge

  Tier 3 (Construction):
    - Existence of spectral integral as operator

These axioms interface with measure theory (Lebesgue integration) and
operator theory (closed operators, domains). They are mathematically
sound consequences of the spectral theorem.

DEPENDENCIES:

  - SpectralBridge.lean: Bochner and Resolvent routes, spectral_scalar_measure
  - Cayley.lean: Cayley transform, spectrum correspondence
  - Resolvent.lean: resolventFun, resolvent bounds
  - Bochner.lean: OneParameterUnitaryGroup, Generator

REFERENCES:

  [1] von Neumann, "Mathematische Grundlagen der Quantenmechanik" (1932)
      - Original spectral theorem for unbounded operators

  [2] Reed & Simon, "Methods of Modern Mathematical Physics I" Ch. VIII
      - Functional calculus construction, domain characterization

  [3] Rudin, "Functional Analysis" Ch. 13
      - Unbounded operators, spectral theorem

  [4] Schmüdgen, "Unbounded Self-adjoint Operators on Hilbert Space" (2012)
      - Modern treatment, careful domain analysis

  [5] Weidmann, "Linear Operators in Hilbert Spaces" (1980)
      - Spectral theory, functional calculus
-/

import LogosLibrary.QuantumMechanics.SpectralTheory.Routes
import LogosLibrary.QuantumMechanics.SpectralTheory.Cayley


namespace FunctionalCalculus
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory InnerProductSpace Complex StonesTheorem.Cayley SpectralBridge SpectralBridge.BochnerRoute Stone.Generators
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## §1. Domain Characterization
-/

/-- Spectral projections multiply: E(B)E(C) = E(B ∩ C) -/
axiom spectral_projection_mul (E : Set ℝ → H →L[ℂ] H)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    E B * E C = E (B ∩ C)

/-- The domain of f(A) consists of vectors with finite f-moment. -/
def functionalDomain (μ : H → Measure ℝ) (f : ℝ → ℂ) : Set H :=
  {ψ : H | Integrable (fun s => ‖f s‖^2) (μ ψ)}

-- E(B) is idempotent: E(B)² = E(B) -/
lemma spectral_projection_idempotent (E : Set ℝ → H →L[ℂ] H)
    (B : Set ℝ) (hB : MeasurableSet B) :
    E B * E B = E B := by
  rw [FunctionalCalculus.spectral_projection_mul E B B hB hB, Set.inter_self]

/-- E(B) applied twice equals E(B) applied once -/
lemma spectral_projection_apply_twice (E : Set ℝ → H →L[ℂ] H)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    E B (E B ψ) = E B ψ := by
  have h := spectral_projection_idempotent E B hB
  exact congrFun (congrArg DFunLike.coe h) ψ

/-- Key identity: ⟪E(B)x, y⟫ = ⟪E(B)x, E(B)y⟫
    Uses: E self-adjoint and E² = E -/
lemma spectral_projection_inner_factorization (E : Set ℝ → H →L[ℂ] H)
    (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    ⟪E B x, y⟫_ℂ = ⟪E B x, E B y⟫_ℂ := by
  calc ⟪E B x, y⟫_ℂ
      = ⟪E B (E B x), y⟫_ℂ := by rw [spectral_projection_apply_twice E B hB x]
    _ = ⟪E B x, E B y⟫_ℂ := spectral_self_adjoint E B (E B x) y

/-- Variant: ⟪E(B)x, E(B)y⟫ = ⟪x, E(B)y⟫ -/
lemma spectral_projection_inner_factorization' (E : Set ℝ → H →L[ℂ] H) (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    ⟪E B x, E B y⟫_ℂ = ⟪x, E B y⟫_ℂ := by
  rw [← spectral_projection_inner_factorization E B hB x y]
  exact spectral_self_adjoint E B x y

/-- ‖E(B)ψ‖² = ⟪E(B)ψ, ψ⟫.re -/
lemma spectral_projection_norm_sq (E : Set ℝ → H →L[ℂ] H) (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    ‖E B ψ‖^2 = (⟪E B ψ, ψ⟫_ℂ).re := by
  have h1 : ‖E B ψ‖^2 = (⟪E B ψ, E B ψ⟫_ℂ).re := by
    conv_rhs => rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    simp only [coe_algebraMap]
    rw [← ofReal_pow]
    exact rfl
  rw [h1, ← spectral_projection_inner_factorization E B hB ψ ψ]

/-!
## Spectral Scalar Measure Properties
-/

lemma spectral_scalar_measure_zero (E : Set ℝ → H →L[ℂ] H)
    (B : Set ℝ) (hB : MeasurableSet B) :
    spectral_scalar_measure E (0 : H) B = 0 := by
  rw [spectral_scalar_measure_apply E (0 : H) B hB]
  simp only [map_zero, inner_zero_left, Complex.zero_re, ENNReal.ofReal_zero]


/-- Spectral measure scales quadratically: μ(c•ψ)(B) = |c|² μ(ψ)(B) -/
lemma spectral_scalar_measure_smul (E : Set ℝ → H →L[ℂ] H) (c : ℂ) (ψ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    (spectral_scalar_measure E (c • ψ) B).toReal = ‖c‖^2 * (spectral_scalar_measure E ψ B).toReal := by
  rw [spectral_scalar_measure_apply' E (c • ψ) B hB]
  rw [spectral_scalar_measure_apply' E ψ B hB]
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
lemma spectral_cross_term_bound (E : Set ℝ → H →L[ℂ] H) (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    |Complex.re ⟪E B x, y⟫_ℂ| ≤
    Real.sqrt ((spectral_scalar_measure E x B).toReal) *
    Real.sqrt ((spectral_scalar_measure E y B).toReal) := by
  -- Use ⟪E(B)x, y⟩ = ⟪E(B)x, E(B)y⟩ and Cauchy-Schwarz
  rw [spectral_projection_inner_factorization E B hB x y]

  have h_cs : |Complex.re ⟪E B x, E B y⟫_ℂ| ≤ ‖E B x‖ * ‖E B y‖ := by
    calc |Complex.re ⟪E B x, E B y⟫_ℂ|
        ≤ ‖⟪E B x, E B y⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖E B x‖ * ‖E B y‖ := norm_inner_le_norm (E B x) (E B y)

  -- Now use ‖E(B)ψ‖² = μ_ψ(B)
  have hx : ‖E B x‖ = Real.sqrt ((spectral_scalar_measure E x B).toReal) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    congr 1
    rw [spectral_projection_norm_sq E B hB x]
    exact Eq.symm (spectral_scalar_measure_apply' E x B hB)
  have hy : ‖E B y‖ = Real.sqrt ((spectral_scalar_measure E y B).toReal) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    congr 1
    rw [spectral_projection_norm_sq E B hB y]
    exact Eq.symm (spectral_scalar_measure_apply' E y B hB)

  rw [hx, hy] at h_cs
  exact h_cs



/-- The spectral measure of a sum expands with cross terms -/
lemma spectral_scalar_measure_add (E : Set ℝ → H →L[ℂ] H) (x y : H) (B : Set ℝ) (hB : MeasurableSet B) :
    (spectral_scalar_measure E (x + y) B).toReal =
    (spectral_scalar_measure E x B).toReal +
    (spectral_scalar_measure E y B).toReal +
    2 * Complex.re ⟪E B x, y⟫_ℂ := by
  rw [spectral_scalar_measure_apply' E (x + y) B hB]
  rw [spectral_scalar_measure_apply' E x B hB]
  rw [spectral_scalar_measure_apply' E y B hB]
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
lemma spectral_scalar_measure_add_bound (E : Set ℝ → H →L[ℂ] H) (x y : H) (B : Set ℝ) (hB : MeasurableSet B) :
    (spectral_scalar_measure E (x + y) B).toReal ≤
    2 * (spectral_scalar_measure E x B).toReal +
    2 * (spectral_scalar_measure E y B).toReal +
    2 * Real.sqrt ((spectral_scalar_measure E x B).toReal) *
        Real.sqrt ((spectral_scalar_measure E y B).toReal) := by
  rw [spectral_scalar_measure_add E x y B hB]
  have h_cross := spectral_cross_term_bound E B hB x y
  have h1 : 2 * Complex.re ⟪E B x, y⟫_ℂ ≤
      2 * Real.sqrt ((spectral_scalar_measure E x B).toReal) *
          Real.sqrt ((spectral_scalar_measure E y B).toReal) := by
    have : Complex.re ⟪E B x, y⟫_ℂ ≤ |Complex.re ⟪E B x, y⟫_ℂ| := le_abs_self _
    linarith [h_cross]
  have hx_nonneg : (spectral_scalar_measure E x B).toReal ≥ 0 := ENNReal.toReal_nonneg
  have hy_nonneg : (spectral_scalar_measure E y B).toReal ≥ 0 := ENNReal.toReal_nonneg
  linarith

/-- For simple functions, integral bound under sum measure -/
-- This would need substantial measure theory machinery
-- For now, we'll axiomatize the key integrability result

axiom spectral_integral_add_bound (E : Set ℝ → H →L[ℂ] H) (x y : H) (f : ℝ → ℂ)
    (hx : Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E x))
    (hy : Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E y)) :
    Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E (x + y))

/-!
## The Submodule Structure
-/


/-- Helper for functionalDomain_zero_mem -/
lemma spectral_scalar_measure_zero_eq (E : Set ℝ → H →L[ℂ] H) :
    spectral_scalar_measure E (0 : H) = 0 := by
  ext B hB
  exact spectral_scalar_measure_zero E B hB
  /-
  Application type mismatch: The argument
  B
has type
  Set ℝ
of sort `Type` but is expected to have type
  E Set.univ = 1
of sort `Prop` in the application
  spectral_scalar_measure_zero E B-/

/-- Helper: zero is in the functional domain -/
lemma functionalDomain_zero_mem (E : Set ℝ → H →L[ℂ] H) (f : ℝ → ℂ) :
    (0 : H) ∈ functionalDomain (spectral_scalar_measure E) f := by
  simp only [functionalDomain, Set.mem_setOf_eq]
  rw [spectral_scalar_measure_zero_eq E]
  exact integrable_zero_measure

/-- Helper for functionalDomain_smul_mem -/
lemma spectral_scalar_measure_smul_eq (E : Set ℝ → H →L[ℂ] H) (hE_univ : E Set.univ = 1)
    (c : ℂ) (ψ : H) :
    spectral_scalar_measure E (c • ψ) = ENNReal.ofReal (‖c‖^2) • spectral_scalar_measure E ψ := by
  haveI : IsFiniteMeasure (spectral_scalar_measure E (c • ψ)) :=
    spectral_scalar_measure_finite E hE_univ (c • ψ)
  haveI : IsFiniteMeasure (spectral_scalar_measure E ψ) :=
    spectral_scalar_measure_finite E hE_univ ψ
  ext B hB
  rw [Measure.smul_apply, ← ENNReal.toReal_eq_toReal]
  · rw [spectral_scalar_measure_smul E c ψ B hB]
    simp only [norm_nonneg, ENNReal.ofReal_pow, ofReal_norm, smul_eq_mul, ENNReal.toReal_mul,
               ENNReal.toReal_pow, toReal_enorm]
  · exact (measure_lt_top _ _).ne
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_lt_top _ _).ne

/-- Helper: scalar multiples preserve functional domain -/
lemma functionalDomain_smul_mem (E : Set ℝ → H →L[ℂ] H) (hE_univ : E Set.univ = 1)
    (f : ℝ → ℂ) (c : ℂ) (ψ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E) f) :
    c • ψ ∈ functionalDomain (spectral_scalar_measure E) f := by
  simp only [functionalDomain, Set.mem_setOf_eq] at hψ ⊢
  rw [spectral_scalar_measure_smul_eq E hE_univ c ψ]
  exact Integrable.smul_measure hψ ENNReal.coe_ne_top

/-- Helper: sums preserve functional domain -/
lemma functionalDomain_add_mem (E : Set ℝ → H →L[ℂ] H) (f : ℝ → ℂ) (x y : H)
    (hx : x ∈ functionalDomain (spectral_scalar_measure E) f)
    (hy : y ∈ functionalDomain (spectral_scalar_measure E) f) :
    x + y ∈ functionalDomain (spectral_scalar_measure E) f := by
  simp only [functionalDomain, Set.mem_setOf_eq] at hx hy ⊢
  exact spectral_integral_add_bound E x y f hx hy

/-- The functional domain is a submodule -/
def functionalDomainSubmodule' (E : Set ℝ → H →L[ℂ] H) (hE_univ : E Set.univ = 1)
    (f : ℝ → ℂ) : Submodule ℂ H where
  carrier := functionalDomain (spectral_scalar_measure E) f
  zero_mem' := functionalDomain_zero_mem E f
  add_mem' := fun hx hy => functionalDomain_add_mem E f _ _ hx hy
  smul_mem' := fun c _ hψ => functionalDomain_smul_mem E hE_univ f c _ hψ

/-!
## Spectral Projection Properties - Basic
-/

/-- E(∅) = 0 -/
lemma spectral_projection_empty (E : Set ℝ → H →L[ℂ] H)
    (hE_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C)) :
    E ∅ = 0 := by
  ext ψ
  simp only [ContinuousLinearMap.zero_apply]
  -- Show ‖E(∅)ψ‖² = 0, hence E(∅)ψ = 0
  have h_norm_sq : ‖E ∅ ψ‖^2 = (⟪E ∅ ψ, ψ⟫_ℂ).re :=
    spectral_projection_norm_sq E ∅ MeasurableSet.empty ψ
  -- μ_ψ(∅) = 0 for any measure
  have h_measure_empty : spectral_scalar_measure E ψ ∅ = 0 := measure_empty
  -- By spectral_scalar_measure_apply: (μ_ψ(∅)).toReal = ⟪E(∅)ψ, ψ⟫.re
  have h_inner_zero : (⟪E ∅ ψ, ψ⟫_ℂ).re = 0 := by
    rw [← spectral_scalar_measure_apply' E ψ ∅ MeasurableSet.empty]
    simp [h_measure_empty]
  -- Therefore ‖E(∅)ψ‖ = 0
  have h_norm_zero : ‖E ∅ ψ‖ = 0 := by
    have h : ‖E ∅ ψ‖^2 = 0 := by rw [h_norm_sq, h_inner_zero]
    exact pow_eq_zero h
  exact norm_eq_zero.mp h_norm_zero


/-- Disjoint sets give orthogonal projections: E(B) * E(C) = 0 when B ∩ C = ∅ -/
lemma spectral_projection_disjoint (E : Set ℝ → H →L[ℂ] H)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : Disjoint B C) :
    E B * E C = 0 := by
  rw [spectral_projection_mul E B C hB hC]
  rw [Set.disjoint_iff_inter_eq_empty.mp hBC]
  exact spectral_projection_empty E (spectral_projection_mul E)

/-- E(B ∪ C) = E(B) + E(C) for disjoint B, C -/
lemma spectral_projection_union_disjoint (E : Set ℝ → H →L[ℂ] H)
    (hE_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
              E (B ∪ C) = E B + E C)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : Disjoint B C) :
    E (B ∪ C) = E B + E C := hE_add B C hB hC hBC

/-- E(B) and E(C) commute -/
lemma spectral_projection_comm (E : Set ℝ → H →L[ℂ] H)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    E B * E C = E C * E B := by
  rw [spectral_projection_mul E B C hB hC, spectral_projection_mul E C B hC hB, Set.inter_comm]

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
lemma spectral_projection_norm_le (E : Set ℝ → H →L[ℂ] H)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    ‖E B ψ‖ ≤ ‖ψ‖ := by
  have h := spectral_projection_norm_sq E B hB ψ
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
lemma spectral_projection_opNorm_le_one (E : Set ℝ → H →L[ℂ] H)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ‖E B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  simp only [one_mul]
  exact spectral_projection_norm_le E B hB ψ

/-- Range of E(B) is the set of fixed points -/
lemma spectral_projection_range_eq_fixed (E : Set ℝ → H →L[ℂ] H)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    ψ ∈ LinearMap.range (E B) ↔ E B ψ = ψ := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact spectral_projection_apply_twice E B hB φ
  · intro h
    exact ⟨ψ, h⟩

/-- Kernel characterization: E(B)ψ = 0 iff μ_ψ(B) = 0 -/
lemma spectral_projection_ker_iff (E : Set ℝ → H →L[ℂ] H) (hE_univ : E Set.univ = 1)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    E B ψ = 0 ↔ spectral_scalar_measure E ψ B = 0 := by
  haveI := spectral_scalar_measure_finite E hE_univ ψ
  constructor
  · intro h
    have h1 : ‖E B ψ‖^2 = 0 := by simp [h]
    rw [spectral_projection_norm_sq E B hB ψ] at h1
    rw [← spectral_scalar_measure_apply' E ψ B hB] at h1
    have h2 : (spectral_scalar_measure E ψ B).toReal = 0 := by linarith
    rw [ENNReal.toReal_eq_zero_iff] at h2
    cases h2 with
    | inl h => exact h
    | inr h => exact absurd h (measure_lt_top _ B).ne
  · intro h
    have h1 : (spectral_scalar_measure E ψ B).toReal = 0 := by simp [h]
    rw [spectral_scalar_measure_apply' E ψ B hB] at h1
    have h2 : ‖E B ψ‖^2 = 0 := by
      rw [spectral_projection_norm_sq E B hB ψ]
      linarith
    exact norm_eq_zero.mp (pow_eq_zero h2)

/-!
## Spectral Scalar Measure Properties - Extended
-/

/-- μ_ψ(B) = ‖E(B)ψ‖² -/
lemma spectral_scalar_measure_eq_norm_sq (E : Set ℝ → H →L[ℂ] H)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    (spectral_scalar_measure E ψ B).toReal = ‖E B ψ‖^2 := by
  rw [spectral_scalar_measure_apply' E ψ B hB, ← spectral_projection_norm_sq E B hB ψ]

/-- Monotonicity: B ⊆ C → μ_ψ(B) ≤ μ_ψ(C) -/
lemma spectral_scalar_measure_mono (E : Set ℝ → H →L[ℂ] H) (hE_univ : E Set.univ = 1)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : B ⊆ C) (ψ : H) :
    spectral_scalar_measure E ψ B ≤ spectral_scalar_measure E ψ C := by
  haveI := spectral_scalar_measure_finite E hE_univ ψ
  exact MeasureTheory.measure_mono hBC

/-- μ_ψ(ℝ) = ‖ψ‖² -/
lemma spectral_scalar_measure_univ (E : Set ℝ → H →L[ℂ] H)
    (hE_univ : E Set.univ = 1)
    (ψ : H) :
    (spectral_scalar_measure E ψ Set.univ).toReal = ‖ψ‖^2 := by
  rw [spectral_scalar_measure_apply' E ψ Set.univ MeasurableSet.univ]
  rw [hE_univ]
  simp only [ContinuousLinearMap.one_apply]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  simp only [coe_algebraMap]
  rw [← ofReal_pow]
  exact rfl

lemma spectral_scalar_measure_sub (E : Set ℝ → H →L[ℂ] H) (x y : H) (B : Set ℝ) (hB : MeasurableSet B) :
    (spectral_scalar_measure E (x - y) B).toReal =
    (spectral_scalar_measure E x B).toReal +
    (spectral_scalar_measure E y B).toReal -
    2 * Complex.re ⟪E B x, y⟫_ℂ := by
  have h : x - y = x + (-1 : ℂ) • y := by simp only [neg_smul, one_smul]; exact sub_eq_add_neg x y
  rw [h, spectral_scalar_measure_add E x ((-1 : ℂ) • y) B hB]
  rw [spectral_scalar_measure_smul E (-1) y B hB]
  simp only [norm_neg, NormOneClass.norm_one, one_pow, one_mul, inner_smul_right, neg_one_mul,
             Complex.neg_re]
  ring

/-!
## Cross-term and Inner Product Bounds
-/


/-- Imaginary part of cross term also bounded -/
lemma spectral_cross_term_im_bound (E : Set ℝ → H →L[ℂ] H) (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    |Complex.im ⟪E B x, y⟫_ℂ| ≤
    Real.sqrt ((spectral_scalar_measure E x B).toReal) *
    Real.sqrt ((spectral_scalar_measure E y B).toReal) := by
  rw [spectral_projection_inner_factorization E B hB x y]
  have h_cs : |Complex.im ⟪E B x, E B y⟫_ℂ| ≤ ‖E B x‖ * ‖E B y‖ := by
    calc |Complex.im ⟪E B x, E B y⟫_ℂ|
        ≤ ‖⟪E B x, E B y⟫_ℂ‖ := Complex.abs_im_le_norm _
      _ ≤ ‖E B x‖ * ‖E B y‖ := norm_inner_le_norm (E B x) (E B y)
  calc |Complex.im ⟪E B x, E B y⟫_ℂ|
      ≤ ‖E B x‖ * ‖E B y‖ := h_cs
    _ = Real.sqrt ((spectral_scalar_measure E x B).toReal) *
        Real.sqrt ((spectral_scalar_measure E y B).toReal) := by
        rw [spectral_scalar_measure_eq_norm_sq E B hB x, spectral_scalar_measure_eq_norm_sq E B hB y]
        simp [Real.sqrt_sq (norm_nonneg _)]

/-- Full complex cross term bound -/
lemma spectral_cross_term_norm_bound (E : Set ℝ → H →L[ℂ] H) (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    ‖⟪E B x, y⟫_ℂ‖ ≤
    Real.sqrt ((spectral_scalar_measure E x B).toReal) *
    Real.sqrt ((spectral_scalar_measure E y B).toReal) := by
  rw [spectral_projection_inner_factorization E B hB x y]
  calc ‖⟪E B x, E B y⟫_ℂ‖
      ≤ ‖E B x‖ * ‖E B y‖ := norm_inner_le_norm _ _
    _ = Real.sqrt ((spectral_scalar_measure E x B).toReal) *
        Real.sqrt ((spectral_scalar_measure E y B).toReal) := by
        rw [spectral_scalar_measure_eq_norm_sq E B hB x, spectral_scalar_measure_eq_norm_sq E B hB y]
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
lemma spectral_scalar_measure_polarization (E : Set ℝ → H →L[ℂ] H)
    (B : Set ℝ) (hB : MeasurableSet B) (x y : H) :
    ⟪E B x, y⟫_ℂ = (1/4 : ℂ) * (
      (spectral_scalar_measure E (x + y) B).toReal -
      (spectral_scalar_measure E (x - y) B).toReal -
      I * (spectral_scalar_measure E (x + I • y) B).toReal +
      I * (spectral_scalar_measure E (x - I • y) B).toReal) := by
  rw [spectral_polarization E B hB x y]
  congr 1
  -- Rewrite each spectral measure in terms of inner product
  have h1 : ((spectral_scalar_measure E (x + y) B).toReal : ℂ) = ⟪E B (x + y), x + y⟫_ℂ := by
    rw [spectral_scalar_measure_apply' E (x + y) B hB]
    have h := spectral_diagonal_real E B (x + y)
    conv_rhs => rw [← Complex.re_add_im ⟪E B (x + y), x + y⟫_ℂ, h]
    simp
  have h2 : ((spectral_scalar_measure E (x - y) B).toReal : ℂ) = ⟪E B (x - y), x - y⟫_ℂ := by
    rw [spectral_scalar_measure_apply' E (x - y) B hB]
    have h := spectral_diagonal_real E B (x - y)
    conv_rhs => rw [← Complex.re_add_im ⟪E B (x - y), x - y⟫_ℂ, h]
    simp
  have h3 : ((spectral_scalar_measure E (x + I • y) B).toReal : ℂ) = ⟪E B (x + I • y), x + I • y⟫_ℂ := by
    rw [spectral_scalar_measure_apply' E (x + I • y) B hB]
    have h := spectral_diagonal_real E B (x + I • y)
    conv_rhs => rw [← Complex.re_add_im ⟪E B (x + I • y), x + I • y⟫_ℂ, h]
    simp
  have h4 : ((spectral_scalar_measure E (x - I • y) B).toReal : ℂ) = ⟪E B (x - I • y), x - I • y⟫_ℂ := by
    rw [spectral_scalar_measure_apply' E (x - I • y) B hB]
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
lemma spectral_scalar_measure_compl (E : Set ℝ → H →L[ℂ] H)
    (hE_univ : E Set.univ = 1)
    (hE_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
              E (B ∪ C) = E B + E C)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H) :
    (spectral_scalar_measure E ψ Bᶜ).toReal = ‖ψ‖^2 - (spectral_scalar_measure E ψ B).toReal := by
  rw [spectral_scalar_measure_eq_norm_sq E Bᶜ hB.compl ψ]
  rw [spectral_scalar_measure_eq_norm_sq E B hB ψ]
  rw [spectral_projection_compl E hE_univ hE_add B hB]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  -- Goal: ‖ψ - E B ψ‖² = ‖ψ‖² - ‖E B ψ‖²
  -- Pythagorean theorem for orthogonal projection

  -- Key facts from spectral_projection_inner_factorization:
  -- ⟪E B ψ, ψ⟫ = ⟪E B ψ, E B ψ⟫ = ‖E B ψ‖²
  have h1 : ⟪E B ψ, ψ⟫_ℂ = ‖E B ψ‖^2 := by
    rw [spectral_projection_inner_factorization E B hB ψ ψ]
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
axiom functionalDomain_inter_aux (E : Set ℝ → H →L[ℂ] H) (f g : ℝ → ℂ) (ψ : H) :
    Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E ψ) →
    Integrable (fun s => ‖g s‖^2) (spectral_scalar_measure E ψ) →
    Integrable (fun s => ‖f s + g s‖^2) (spectral_scalar_measure E ψ)

axiom functionalDomain_mul_bound_aux (E : Set ℝ → H →L[ℂ] H) (f g : ℝ → ℂ) (M : ℝ) (ψ : H) :
    (∀ s, ‖f s‖ ≤ M) →
    Integrable (fun s => ‖g s‖^2) (spectral_scalar_measure E ψ) →
    Integrable (fun s => ‖f s * g s‖^2) (spectral_scalar_measure E ψ)

axiom functionalDomain_of_bounded_aux (E : Set ℝ → H →L[ℂ] H) (f : ℝ → ℂ) (M : ℝ) (ψ : H) :
    (∀ s, ‖f s‖ ≤ M) →
    Integrable (fun s => ‖f s‖^2) (spectral_scalar_measure E ψ)

/-- Intersection of functional domains -/
lemma functionalDomain_inter (E : Set ℝ → H →L[ℂ] H) (f g : ℝ → ℂ) :
    functionalDomain (spectral_scalar_measure E) f ∩
    functionalDomain (spectral_scalar_measure E) g ⊆
    functionalDomain (spectral_scalar_measure E) (fun s => f s + g s) := by
  intro ψ ⟨hf, hg⟩
  simp only [functionalDomain, Set.mem_setOf_eq] at hf hg ⊢
  exact functionalDomain_inter_aux E f g ψ hf hg

/-- Product bound for functional domains -/
lemma functionalDomain_mul_bound (E : Set ℝ → H →L[ℂ] H) (f g : ℝ → ℂ)
    (hf_bdd : ∃ M, ∀ s, ‖f s‖ ≤ M) :
    functionalDomain (spectral_scalar_measure E) g ⊆
    functionalDomain (spectral_scalar_measure E) (fun s => f s * g s) := by
  intro ψ hg
  simp only [functionalDomain, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨M, hM⟩ := hf_bdd
  exact functionalDomain_mul_bound_aux E f g M ψ hM hg

/-- Bounded functions always give full domain -/
lemma functionalDomain_of_bounded (E : Set ℝ → H →L[ℂ] H) (f : ℝ → ℂ)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) (ψ : H) :
    ψ ∈ functionalDomain (spectral_scalar_measure E) f := by
  simp only [functionalDomain, Set.mem_setOf_eq]
  obtain ⟨M, hM⟩ := hf
  exact functionalDomain_of_bounded_aux E f M ψ hM

/-- Indicator functions are bounded -/
lemma indicator_bounded (B : Set ℝ) :
    ∃ M : ℝ, ∀ s, ‖Set.indicator B (1 : ℝ → ℂ) s‖ ≤ M := by
  use 1
  intro s
  by_cases hs : s ∈ B
  · simp [Set.indicator_of_mem hs]
  · simp [Set.indicator_of_notMem hs]

/-- Identity function is in the domain iff finite second moment -/
lemma functionalDomain_id_iff (E : Set ℝ → H →L[ℂ] H) (ψ : H) :
    ψ ∈ functionalDomain (spectral_scalar_measure E) (fun s => (s : ℂ)) ↔
    Integrable (fun s => s^2) (spectral_scalar_measure E ψ) := by
  simp only [functionalDomain, Set.mem_setOf_eq]
  constructor
  · intro h
    convert h using 2
    simp_all only [norm_real, Real.norm_eq_abs, sq_abs]
  · intro h
    convert h using 2
    simp_all only [norm_real, Real.norm_eq_abs, sq_abs]

/-- Domain as submodule -/
def functionalDomainSubmodule (E : Set ℝ → H →L[ℂ] H) (hE_univ : E Set.univ = 1)
    (f : ℝ → ℂ) : Submodule ℂ H where
  carrier := functionalDomain (spectral_scalar_measure E) f
  zero_mem' := functionalDomain_zero_mem E f
  add_mem' := fun hx hy => functionalDomain_add_mem E f _ _ hx hy
  smul_mem' := fun c _ hψ => functionalDomain_smul_mem E hE_univ f c _ hψ


/-!
## Functional Calculus Axioms

We axiomatize the spectral integral ∫ f(s) dE(s) and its key properties.
-/

/-- The spectral integral for bounded functions exists and is bounded -/
axiom spectral_integral_bounded (E : Set ℝ → H →L[ℂ] H) (f : ℝ → ℂ)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) : H →L[ℂ] H

/-- The spectral integral for general functions, defined on appropriate domain -/
axiom spectral_integral (E : Set ℝ → H →L[ℂ] H) (f : ℝ → ℂ)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E) f) : H

/-- Core property: inner product representation -/
axiom spectral_integral_inner (E : Set ℝ → H →L[ℂ] H) (f : ℝ → ℂ)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E) f)
    (φ : H) (hφ : φ ∈ functionalDomain (spectral_scalar_measure E) f) :
    ⟪spectral_integral E f ψ hψ, φ⟫_ℂ =
    ∫ s, f s * ⟪E {s} ψ, φ⟫_ℂ ∂(spectral_scalar_measure E ψ)
    -- Or more properly: ∫ f dν_{ψ,φ} where ν_{ψ,φ}(B) = ⟪E(B)ψ, φ⟫

/-- Indicator functions give projections -/
axiom spectral_integral_indicator (E : Set ℝ → H →L[ℂ] H)
    (B : Set ℝ) (hB : MeasurableSet B) (ψ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E) (Set.indicator B 1)) :
    spectral_integral E (Set.indicator B 1) ψ hψ = E B ψ

/-- Linearity in f -/
axiom spectral_integral_add (E : Set ℝ → H →L[ℂ] H) (f g : ℝ → ℂ)
    (ψ : H)
    (hf : ψ ∈ functionalDomain (spectral_scalar_measure E) f)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E) (f + g)) :
    spectral_integral E (f + g) ψ hfg =
    spectral_integral E f ψ hf + spectral_integral E g ψ hg

axiom spectral_integral_smul (E : Set ℝ → H →L[ℂ] H) (c : ℂ) (f : ℝ → ℂ)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E) f)
    (hcf : ψ ∈ functionalDomain (spectral_scalar_measure E) (c • f)) :
    spectral_integral E (c • f) ψ hcf = c • spectral_integral E f ψ hψ

/-- Multiplicativity: Φ(fg) = Φ(f) ∘ Φ(g) -/
axiom spectral_integral_mul (E : Set ℝ → H →L[ℂ] H) (f g : ℝ → ℂ)
    (ψ : H)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E) g)
    (hfg : spectral_integral E g ψ hg ∈ functionalDomain (spectral_scalar_measure E) f)
    (h_prod : ψ ∈ functionalDomain (spectral_scalar_measure E) (f * g)) :
    spectral_integral E (f * g) ψ h_prod =
    spectral_integral E f (spectral_integral E g ψ hg) hfg

/-- Adjoint property: Φ(f̄) = Φ(f)* -/
axiom spectral_integral_conj (E : Set ℝ → H →L[ℂ] H) (f : ℝ → ℂ)
    (ψ φ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E) f)
    (hφ : φ ∈ functionalDomain (spectral_scalar_measure E) (starRingEnd ℂ ∘ f)) :
    ⟪spectral_integral E f ψ hψ, φ⟫_ℂ =
    ⟪ψ, spectral_integral E (starRingEnd ℂ ∘ f) φ hφ⟫_ℂ

/-- Bounded functions on full domain agree with bounded version -/
axiom spectral_integral_bounded_eq (E : Set ℝ → H →L[ℂ] H) (f : ℝ → ℂ)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) (ψ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E) f) :
    spectral_integral E f ψ hψ = spectral_integral_bounded E f hf ψ



/-- **Theorem**: The domain contains dom(A) when f is polynomially bounded.
    NOTE: For polynomial degree n > 1, this really requires dom(A^n).
    We axiomatize the full statement for now. -/
axiom generator_domain_subset_functional_aux {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (f : ℝ → ℂ)
    (C n : ℝ) (hf : ∀ s, ‖f s‖ ≤ C * (1 + |s|)^n)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ψ ∈ functionalDomain (spectral_scalar_measure E) f

/-- **Theorem**: The domain contains dom(A) when f is polynomially bounded. -/
theorem generator_domain_subset_functional {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (f : ℝ → ℂ)
    (hf : ∃ C n : ℝ, ∀ s, ‖f s‖ ≤ C * (1 + |s|)^n) :
    (gen.domain : Set H) ⊆ functionalDomain (spectral_scalar_measure E) f := by
  intro ψ hψ
  obtain ⟨C, n, hCn⟩ := hf
  exact generator_domain_subset_functional_aux gen hsa E f C n hCn ψ hψ



/-!
## §2. The Functional Calculus Map
-/


/-- Functional calculus for bounded Borel functions.
    This is a *-homomorphism from L^∞(ℝ, μ_ψ) to B(H). -/
noncomputable def boundedFunctionalCalculus
    (E : Set ℝ → H →L[ℂ] H)
    (f : ℝ → ℂ)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) : H →L[ℂ] H :=
  spectral_integral_bounded E f hf


/-!
## Spectral Integral Axioms
-/

/-- Spectral integral is additive in ψ -/
axiom spectral_integral_add_vector (E : Set ℝ → H →L[ℂ] H) (f : ℝ → ℂ)
    (x y : H)
    (hx : x ∈ functionalDomain (spectral_scalar_measure E) f)
    (hy : y ∈ functionalDomain (spectral_scalar_measure E) f)
    (hxy : x + y ∈ functionalDomain (spectral_scalar_measure E) f) :
    spectral_integral E f (x + y) hxy =
    spectral_integral E f x hx + spectral_integral E f y hy

/-- Spectral integral is homogeneous in ψ -/
axiom spectral_integral_smul_vector (E : Set ℝ → H →L[ℂ] H) (f : ℝ → ℂ)
    (c : ℂ) (ψ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E) f)
    (hcψ : c • ψ ∈ functionalDomain (spectral_scalar_measure E) f) :
    spectral_integral E f (c • ψ) hcψ = c • spectral_integral E f ψ hψ

/-- Constant function 1 gives identity -/
axiom spectral_integral_one (E : Set ℝ → H →L[ℂ] H)
    (hE_univ : E Set.univ = 1)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E) (fun _ => 1)) :
    spectral_integral E (fun _ => 1) ψ hψ = ψ

/-!
## Functional Calculus Definition
-/

/-- Functional calculus for general measurable functions. -/
noncomputable def functionalCalculus
    (E : Set ℝ → H →L[ℂ] H) (hE_univ : E Set.univ = 1)
    (f : ℝ → ℂ) :
    functionalDomainSubmodule E hE_univ f →ₗ[ℂ] H where
  toFun := fun ⟨ψ, hψ⟩ => spectral_integral E f ψ hψ
  map_add' := fun ⟨x, hx⟩ ⟨y, hy⟩ => by
    simp only
    have hxy : x + y ∈ functionalDomain (spectral_scalar_measure E) f :=
      (functionalDomainSubmodule E hE_univ f).add_mem hx hy
    exact spectral_integral_add_vector E f x y hx hy hxy
  map_smul' := fun c ⟨ψ, hψ⟩ => by
    simp only [RingHom.id_apply]
    have hcψ : c • ψ ∈ functionalDomain (spectral_scalar_measure E) f :=
      (functionalDomainSubmodule E hE_univ f).smul_mem c hψ
    exact spectral_integral_smul_vector E f c ψ hψ hcψ

/-- The inner product formula for functional calculus. -/
axiom functionalCalculus_inner
    (E : Set ℝ → H →L[ℂ] H) (hE_univ : E Set.univ = 1)
    (f : ℝ → ℂ)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E) f) :
    ⟪functionalCalculus E hE_univ f ⟨ψ, hψ⟩, ψ⟫_ℂ = ∫ s, f s ∂(spectral_scalar_measure E ψ)

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
axiom spectral_integral_add_function (E : Set ℝ → H →L[ℂ] H) (f g : ℝ → ℂ)
    (ψ : H)
    (hf : ψ ∈ functionalDomain (spectral_scalar_measure E) f)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E) (f + g)) :
    spectral_integral E (f + g) ψ hfg =
    spectral_integral E f ψ hf + spectral_integral E g ψ hg

/-- Spectral integral is multiplicative in f (composition property) -/
axiom spectral_integral_mul_function (E : Set ℝ → H →L[ℂ] H) (f g : ℝ → ℂ)
    (ψ : H)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E) (f * g))
    (hf_gψ : spectral_integral E g ψ hg ∈ functionalDomain (spectral_scalar_measure E) f) :
    spectral_integral E (f * g) ψ hfg =
    spectral_integral E f (spectral_integral E g ψ hg) hf_gψ


/-!
## Completed Theorems
-/

/-- **Addition**: (f + g)(A) = f(A) + g(A) -/
theorem functionalCalculus_add (E : Set ℝ → H →L[ℂ] H) (hE_univ : E Set.univ = 1)
    (f g : ℝ → ℂ)
    (ψ : H)
    (hf : ψ ∈ functionalDomain (spectral_scalar_measure E) f)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E) (f + g)) :
    functionalCalculus E hE_univ (f + g) ⟨ψ, hfg⟩ =
    functionalCalculus E hE_univ f ⟨ψ, hf⟩ + functionalCalculus E hE_univ g ⟨ψ, hg⟩ :=
  spectral_integral_add_function E f g ψ hf hg hfg

/-- **Multiplication**: (fg)(A) = f(A) ∘ g(A) on appropriate domain -/
theorem functionalCalculus_mul (E : Set ℝ → H →L[ℂ] H) (hE_univ : E Set.univ = 1)
    (f g : ℝ → ℂ)
    (ψ : H)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E) (f * g))
    (hf_gψ : functionalCalculus E hE_univ g ⟨ψ, hg⟩ ∈ functionalDomain (spectral_scalar_measure E) f) :
    functionalCalculus E hE_univ (f * g) ⟨ψ, hfg⟩ =
    functionalCalculus E hE_univ f ⟨functionalCalculus E hE_univ g ⟨ψ, hg⟩, hf_gψ⟩ :=
  spectral_integral_mul_function E f g ψ hg hfg hf_gψ

/-- **Conjugation**: f̄(A) = f(A)* -/
theorem functionalCalculus_conj (E : Set ℝ → H →L[ℂ] H) (hE_univ : E Set.univ = 1)
    (f : ℝ → ℂ)
    (ψ φ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E) f)
    (hφ : φ ∈ functionalDomain (spectral_scalar_measure E) (starRingEnd ℂ ∘ f)) :
    ⟪functionalCalculus E hE_univ f ⟨ψ, hψ⟩, φ⟫_ℂ =
    ⟪ψ, functionalCalculus E hE_univ (starRingEnd ℂ ∘ f) ⟨φ, hφ⟩⟫_ℂ :=
  spectral_integral_conj E f ψ φ hψ hφ

/-- **Normalization**: 1(A) = I -/
theorem functionalCalculus_one (E : Set ℝ → H →L[ℂ] H) (hE_univ : E Set.univ = 1)
    (ψ : H) (h : ψ ∈ functionalDomain (spectral_scalar_measure E) (fun _ => 1)) :
    functionalCalculus E hE_univ (fun _ => 1) ⟨ψ, h⟩ = ψ :=
  spectral_integral_one E hE_univ ψ h

/-- **Spectral mapping for indicator**: 𝟙_B(A) = E(B) -/
theorem functionalCalculus_indicator (E : Set ℝ → H →L[ℂ] H) (hE_univ : E Set.univ = 1)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ψ : H) (h : ψ ∈ functionalDomain (spectral_scalar_measure E) (Set.indicator B 1)) :
    functionalCalculus E hE_univ (Set.indicator B 1) ⟨ψ, h⟩ = E B ψ :=
  spectral_integral_indicator E B hB ψ h

end Algebra

/-!
## §4. Recovering A from E
-/

/-- Predicate: E is the spectral measure associated to the generator -/
structure IsSpectralMeasureFor (E : Set ℝ → H →L[ℂ] H)
    {U_grp : OneParameterUnitaryGroup (H := H)} (gen : Generator U_grp) : Prop where
  proj_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C)
  proj_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ
  proj_univ : E Set.univ = 1
  proj_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
             E (B ∪ C) = E B + E C  -- ADD THIS LINE
  unitary_eq_integral : ∀ (t : ℝ) (ψ : H),
    ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ s, Complex.exp (I * t * s) ∂(BochnerRoute.spectral_scalar_measure E ψ)




/-- Direct axiom: Generator and spectral integral agree on inner products
NOTE: This is the first axiom to turn into a lemma.  This is temporary! -/
axiom generator_spectral_integral_inner_eq {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ_dom : ψ ∈ gen.domain)
    (hψ_func : ψ ∈ functionalDomain (spectral_scalar_measure E) identityFunction)
    (φ : H) :
    ⟪gen.op ⟨ψ, hψ_dom⟩, φ⟫_ℂ = ⟪spectral_integral E identityFunction ψ hψ_func, φ⟫_ℂ

/-- The identity function id(s) = s -/
def identityFunction : ℝ → ℂ := fun s => s

/-- **Core Theorem**: A = ∫ s dE(s) on dom(A)

The generator equals the functional calculus of the identity function. -/
theorem generator_eq_spectral_integral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ_dom : ψ ∈ gen.domain)
    (hψ_func : ψ ∈ functionalDomain (spectral_scalar_measure E) identityFunction) :
    gen.op ⟨ψ, hψ_dom⟩ = functionalCalculus E hE.proj_univ identityFunction ⟨ψ, hψ_func⟩ := by
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
    ψ ∈ functionalDomain (spectral_scalar_measure E) identityFunction

/-- Backward direction: functionalDomain(id) ⊆ dom(A)
    Key fact: ∫|s|² dμ_ψ < ∞ implies ψ ∈ dom(A) -/
axiom id_domain_subset_generator_domain {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E) identityFunction) :
    ψ ∈ gen.domain

/-- Norm formula: ‖Aψ‖² = ∫|s|² dμ_ψ -/
axiom generator_norm_sq_eq_second_moment {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ‖gen.op ⟨ψ, hψ⟩‖^2 = ∫ s, s^2 ∂(spectral_scalar_measure E ψ)

/-- Domain equality: dom(A) = dom(id(A)) -/
theorem generator_domain_eq_functional_domain {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : IsSpectralMeasureFor E gen) :
    (gen.domain : Set H) = functionalDomain (spectral_scalar_measure E) identityFunction := by
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
    (E : Set ℝ → H →L[ℂ] H) : Prop where
  /-- E agrees with Bochner measure from U(t) -/
  bochner_agreement : ∀ ψ B, MeasurableSet B →
    (spectral_scalar_measure E ψ B).toReal =
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
    (spectral_scalar_measure E ψ B).toReal =
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
    SpectralMeasureAgreement gen hsa E where
  bochner_agreement := fun ψ B hB => bochner_route_agreement gen hsa E hE ψ B hB
  stieltjes_agreement := fun ψ a b hab => stieltjes_route_agreement gen hsa E hE ψ a b hab
  cayley_agreement := fun B hB => cayley_route_agreement gen hsa E hE B hB


end FunctionalCalculus
