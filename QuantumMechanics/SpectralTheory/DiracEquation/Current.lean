/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.GammaTraces
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The Dirac Current and Probability Density

This file defines the Dirac probability current jᵘ = ψ̄γᵘψ and proves the
fundamental result that the zeroth component j⁰ = ψ†ψ is non-negative,
making it a valid probability density.

## Main definitions

* `SpinorField`: A spinor field assigns a 4-component spinor to each spacetime point
* `SpinorField'`: A spinor field with integrability conditions
* `diracAdjoint`: The Dirac adjoint ψ̄ = ψ†γ⁰
* `diracCurrent`: The 4-current jᵘ = ψ̄γᵘψ
* `probabilityDensity`: ρ = j⁰ = ψ†ψ (as a real number)
* `probabilityCurrent`: The spatial current jⁱ = ψ̄γⁱψ

## Main results

* `gamma0_sq`: (γ⁰)² = I (needed for current calculation)
* `current_zero_eq_norm_sq`: j⁰ = Σₐ|ψₐ|² (fundamental identity)
* `current_zero_nonneg`: j⁰ ≥ 0 (probability is non-negative)
* `current_zero_eq_zero_iff`: j⁰ = 0 ↔ ψ = 0 (only zero spinor has zero density)

## Physical interpretation

### The Probability Current
The Dirac current jᵘ = (ρ, j) has components:
- j⁰ = ρ = ψ†ψ: probability density (probability per unit volume)
- jⁱ = ψ†αⁱψ: probability current (probability flux)

The continuity equation ∂ᵤjᵘ = 0 (proved in Conservation.lean) ensures that
probability is conserved: particles are neither created nor destroyed.

### Why j⁰ ≥ 0 Matters
The Klein-Gordon equation (relativistic scalar equation) has j⁰ that can be
negative, making it unsuitable as a probability density. This was the main
motivation for Dirac's construction: find a relativistic equation with a
positive-definite probability density.

The key is that j⁰ = ψ†ψ = Σₐ|ψₐ|² is a sum of squared magnitudes, which
is manifestly non-negative. This relies on the specific form of the Dirac
equation and the Clifford algebra relations.

### The Dirac Adjoint
The Dirac adjoint ψ̄ = ψ†γ⁰ (not just ψ†) is needed for Lorentz covariance.
Under a Lorentz transformation Λ, spinors transform as ψ → S(Λ)ψ, and the
adjoint transforms as ψ̄ → ψ̄S(Λ)⁻¹, ensuring that ψ̄ψ is a Lorentz scalar.

## References

* [Dirac, *The Principles of Quantum Mechanics*][dirac1930], Chapter XI
* [Peskin, Schroeder, *An Introduction to Quantum Field Theory*][peskin1995], §3.2
* [Thaller, *The Dirac Equation*][thaller1992], Chapter 1

## Tags

Dirac current, probability density, probability current, spinor field,
Dirac adjoint, positive definiteness
-/

namespace Dirac.Current

open Dirac.Matrices Complex MeasureTheory

/-! ## Gamma Matrix Structures -/

/-- Abstract specification of gamma matrices satisfying the Minkowski-Clifford algebra.

This allows working with any representation of the gamma matrices, not just
the standard (Dirac-Pauli) representation. -/
structure GammaMatrices where
  /-- The four gamma matrices γ⁰, γ¹, γ², γ³. -/
  gamma : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ
  /-- The Minkowski-Clifford relation: {γᵘ, γᵛ} = 2ηᵘᵛI.
      Written as γᵘγᵛ + γᵛγᵘ = 2ηᵘᵛI where η = diag(1,-1,-1,-1). -/
  clifford_minkowski : ∀ μ ν, gamma μ * gamma ν + gamma ν * gamma μ =
    2 • (if μ = ν then (if μ = 0 then 1 else -1) • (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0)
  /-- γ⁰ is Hermitian: (γ⁰)† = γ⁰. Required for j⁰ to be real. -/
  gamma0_hermitian : (gamma 0).conjTranspose = gamma 0
  /-- Spatial gammas are anti-Hermitian: (γⁱ)† = -γⁱ. -/
  gammaI_antihermitian : ∀ i : Fin 3, (gamma i.succ).conjTranspose = -gamma i.succ

set_option maxHeartbeats 78703

/-- The standard (Dirac-Pauli) representation of the gamma matrices.

This is the representation where:
- γ⁰ = β = diag(1,1,-1,-1)
- γⁱ = βαⁱ

Other representations (Weyl, Majorana) are related by unitary transformations. -/
def standardGammaMatrices : GammaMatrices where
  gamma := fun μ => match μ with
    | 0 => gamma0
    | 1 => gamma1
    | 2 => gamma2
    | 3 => gamma3
  clifford_minkowski := by
    intro μ ν
    fin_cases μ <;> fin_cases ν
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, one_smul]; exact clifford_00
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, zero_ne_one, ↓reduceIte, nsmul_zero]; exact clifford_01
    · simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_02
    · simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_03
    · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, one_ne_zero, ↓reduceIte, nsmul_zero]; exact clifford_10
    · simp only [Fin.mk_one, Fin.isValue, ↓reduceIte, one_ne_zero, Int.reduceNeg, neg_smul,
        one_smul, smul_neg, nsmul_eq_mul, Nat.cast_ofNat, mul_one]; rw [neg_two_eq_smul]; exact clifford_11
    · simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_12
    · simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_13
    · simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.isValue, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_20
    · simp only [Fin.reduceFinMk, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_21
    · simp only [Fin.reduceFinMk, ↓reduceIte, Fin.isValue, Fin.reduceEq, Int.reduceNeg, neg_smul,
        one_smul, smul_neg, nsmul_eq_mul, Nat.cast_ofNat, mul_one]; rw [neg_two_eq_smul]; exact clifford_22
    · simp only [Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_23
    · simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.isValue, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_30
    · simp only [Fin.reduceFinMk, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_31
    · simp only [Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_32
    · simp only [Fin.reduceFinMk, ↓reduceIte, Fin.isValue, Fin.reduceEq, Int.reduceNeg, neg_smul,
        one_smul, smul_neg, nsmul_eq_mul, Nat.cast_ofNat, mul_one]; rw [neg_two_eq_smul]; exact clifford_33
  gamma0_hermitian := gamma0_hermitian_proof
  gammaI_antihermitian := by
    intro i
    fin_cases i
    · exact gamma1_antihermitian
    · exact gamma2_antihermitian
    · exact gamma3_antihermitian


/-! ## Spinor Fields -/

/-- A point in 4-dimensional spacetime: x^μ = (t, x, y, z). -/
abbrev Spacetime := Fin 4 → ℝ

/-- A spinor field assigns a 4-component spinor to each spacetime point.

This is the basic object in relativistic quantum mechanics: ψ(x) ∈ ℂ⁴
for each x ∈ ℝ⁴. The four components encode spin-up/down and particle/antiparticle. -/
structure SpinorField where
  /-- The spinor value at each spacetime point. -/
  ψ : Spacetime → (Fin 4 → ℂ)

/-- A spinor field with integrability condition.

For probability to be well-defined, we need ∫|ψ|²d³x < ∞ on each time slice. -/
structure SpinorField' where
  /-- The four-component spinor at each spacetime point: x^μ ↦ ψ_a(x). -/
  ψ : (Fin 4 → ℝ) → (Fin 4 → ℂ)
  /-- Square-integrable on each spatial slice: ∫|ψ(t,x)|² d³x < ∞ for all t. -/
  integrable : ∀ t : ℝ, Integrable (fun x : Fin 3 → ℝ =>
    ‖ψ (Fin.cons t (fun i => x i))‖^2) volume


/-! ## The Dirac Adjoint and Current -/

/-- The Dirac adjoint: ψ̄ = ψ†γ⁰.

This is NOT the same as the Hermitian conjugate ψ†. The extra γ⁰ factor
ensures Lorentz covariance: ψ̄ψ is a Lorentz scalar, while ψ†ψ is only
the time component of a 4-vector.

For the standard representation where γ⁰ = diag(1,1,-1,-1):
  ψ̄ = (ψ₁*, ψ₂*, -ψ₃*, -ψ₄*) -/
noncomputable def diracAdjoint (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun a => ∑ b, star (ψ b) * (Γ.gamma 0) b a

/-- The Dirac current 4-vector: jᵘ = ψ̄γᵘψ.

Components:
- j⁰ = ψ̄γ⁰ψ = ψ†γ⁰γ⁰ψ = ψ†ψ (probability density)
- jⁱ = ψ̄γⁱψ = ψ†γ⁰γⁱψ = ψ†αⁱψ (probability current)

The current satisfies the continuity equation ∂ᵤjᵘ = 0 when ψ solves
the Dirac equation. -/
noncomputable def diracCurrent (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun μ => ∑ a : Fin 4, ∑ b : Fin 4, star (ψ a) * (Γ.gamma 0 * Γ.gamma μ) a b * ψ b


/-! ## Key Lemma: γ⁰ is an Involution -/

/-- γ⁰ is an involution: (γ⁰)² = I.

This is derived from the Clifford relation {γ⁰, γ⁰} = 2η⁰⁰I = 2I,
which gives 2(γ⁰)² = 2I, hence (γ⁰)² = I.

This lemma is crucial for proving j⁰ = ψ†ψ. -/
lemma gamma0_sq (Γ : GammaMatrices) : Γ.gamma 0 * Γ.gamma 0 = 1 := by
  have hcliff := Γ.clifford_minkowski 0 0
  simp only [↓reduceIte, one_smul, two_nsmul] at hcliff
  have : (2 : ℂ) • (Γ.gamma 0 * Γ.gamma 0) = (2 : ℂ) • 1 := by
    calc (2 : ℂ) • (Γ.gamma 0 * Γ.gamma 0)
        = Γ.gamma 0 * Γ.gamma 0 + Γ.gamma 0 * Γ.gamma 0 := by rw [two_smul]
      _ = 1 + 1 := hcliff
      _ = (2 : ℂ) • 1 := by rw [two_smul]
  exact smul_right_injective (Matrix (Fin 4) (Fin 4) ℂ) (two_ne_zero) this


/-! ## Fundamental Theorems -/

/-- **FUNDAMENTAL THEOREM**: The zeroth component of the current equals ψ†ψ.

  j⁰ = ψ̄γ⁰ψ = ψ†(γ⁰)²ψ = ψ†ψ = Σₐ|ψₐ|²

This is the key identity that makes the Dirac equation physically sensible:
the probability density is the sum of squared amplitudes, exactly as in
non-relativistic quantum mechanics.

**Proof**: Use (γ⁰)² = I to simplify γ⁰γ⁰ to the identity matrix, then
the double sum collapses to Σₐ(ψₐ)*ψₐ = Σₐ|ψₐ|². -/
theorem current_zero_eq_norm_sq (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) :
    diracCurrent Γ ψ 0 = ∑ a, ‖ψ a‖^2 := by
  unfold diracCurrent
  simp only [gamma0_sq Γ, Matrix.one_apply, RCLike.star_def, mul_ite, mul_one, mul_zero,
             ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
             ofReal_sum, ofReal_pow]
  congr 1
  funext a
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  exact ofReal_pow ‖ψ a‖ 2

/-- **FUNDAMENTAL THEOREM**: The probability density j⁰ is non-negative.

  j⁰ = Σₐ|ψₐ|² ≥ 0

This is why the Dirac equation succeeds where Klein-Gordon fails: the
probability density is a sum of non-negative terms, hence non-negative.

**Physical significance**: Probability cannot be negative. This seems obvious,
but it's a non-trivial constraint on relativistic wave equations. -/
theorem current_zero_nonneg (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) :
    0 ≤ (diracCurrent Γ ψ 0).re := by
  rw [current_zero_eq_norm_sq]
  simp only [ofReal_sum, ofReal_pow, re_sum]
  apply Finset.sum_nonneg
  intro a _
  simp only [← ofReal_pow, Complex.ofReal_re]
  exact sq_nonneg ‖ψ a‖

/-- The probability density vanishes if and only if the spinor is zero.

  j⁰ = 0 ↔ ψ = 0

**Physical meaning**: The only state with zero probability everywhere is
the zero state (no particle). Every non-zero state has positive probability
somewhere. -/
theorem current_zero_eq_zero_iff (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) :
    diracCurrent Γ ψ 0 = 0 ↔ ψ = 0 := by
  rw [current_zero_eq_norm_sq]
  constructor
  · intro h
    ext a
    have h_nonneg : ∀ i : Fin 4, 0 ≤ ‖ψ i‖^2 := fun i => sq_nonneg _
    have h_sum_eq : ∑ i : Fin 4, ‖ψ i‖^2 = 0 := by
      exact Eq.symm ((fun {z w} => ofReal_inj.mp) (id (Eq.symm h)))
    have h_each_zero := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h_nonneg i) |>.mp h_sum_eq
    have : ‖ψ a‖^2 = 0 := h_each_zero a (Finset.mem_univ a)
    exact norm_eq_zero.mp (pow_eq_zero this)
  · intro h
    simp [h]


/-! ## Probability Density and Current -/

/-- The probability density ρ = j⁰ = ψ†ψ as a real number.

This extracts the real part of j⁰, which is already real (j⁰ = Σ|ψₐ|² ∈ ℝ).
The probability of finding the particle in a region R is ∫_R ρ d³x. -/
noncomputable def probabilityDensity (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : ℝ :=
  (diracCurrent Γ ψ 0).re

/-- The probability current (spatial components): jⁱ = ψ̄γⁱψ.

This gives the probability flux through surfaces. The continuity equation
∂ρ/∂t + ∇·j = 0 ensures that probability flows continuously (no teleportation). -/
noncomputable def probabilityCurrent (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 3 → ℂ :=
  fun i => diracCurrent Γ ψ i.succ


/-! ## Spacetime Utilities -/

/-- Construct a spacetime point from time t and spatial position x = (x¹, x², x³).

This packages (t, x, y, z) into a single function Fin 4 → ℝ. -/
def spacetimePoint (t : ℝ) (x : Fin 3 → ℝ) : Spacetime :=
  ![t, x 0, x 1, x 2]

/-- Total probability at time t: P(t) = ∫ρ(t,x) d³x = ∫ψ†ψ d³x.

This is the total probability of finding the particle somewhere in space.
For a normalized state, P(t) = 1 for all t. -/
noncomputable def totalProbability (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) : ℝ :=
  ∫ x : Fin 3 → ℝ, probabilityDensity Γ (ψ.ψ (spacetimePoint t x)) ∂volume

end Dirac.Current
