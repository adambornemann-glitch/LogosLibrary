/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.Current

/-!
# Probability Conservation and the Born Rule

This file proves the fundamental physical results: the Dirac equation implies
conservation of probability, and the probability density satisfies the axioms
of the Born rule.

## Main definitions

* `stdBasis`: Standard basis vectors in ℝ⁴
* `fourDivergence`: The 4-divergence ∂ᵤjᵘ
* `partialDeriv'`: Partial derivative of a spinor field
* `normalizedProbability`: P(x,t) = ρ(x,t) / ∫ρ d³x

## Main results

* `probability_conserved`: d/dt ∫ρ d³x = 0 (probability is conserved)
* `born_rule_valid`: P(x,t) = ρ/∫ρ satisfies probability axioms

## Axioms

The proofs rely on several axioms from analysis and PDE theory:

* `dirac_current_conserved`: The Dirac equation implies ∂ᵤjᵘ = 0
* `leibniz_integral_rule`: d/dt ∫f(t,x)dx = ∫(∂f/∂t)dx
* `continuity_equation`: ∂ρ/∂t = -∇·j
* `divergence_integral_vanishes`: ∫∇·j d³x = 0 with decay conditions

These are standard results that would follow from a complete development of
Sobolev spaces and distribution theory.

## Physical interpretation

### Current Conservation
The continuity equation ∂ᵤjᵘ = ∂ρ/∂t + ∇·j = 0 is the local form of
probability conservation. It says that probability density changes only
due to probability current flowing in or out — there are no sources or sinks.

### Global Conservation
Integrating over all space: d/dt ∫ρ d³x = -∫∇·j d³x = 0 (by divergence theorem
with vanishing boundary conditions). The total probability is constant.

### The Born Rule
Max Born's interpretation (1926): |ψ(x)|² gives the probability density for
finding the particle at position x. Our theorem `born_rule_valid` shows that
ρ/∫ρ satisfies the mathematical axioms of a probability distribution:
1. Non-negativity: P(x) ≥ 0
2. Normalization: ∫P(x)d³x = 1

This connects the mathematical formalism to physical measurement.

## References

* [Born, *Zur Quantenmechanik der Stoßvorgänge*][born1926]
* [Dirac, *The Principles of Quantum Mechanics*][dirac1930], Chapter XI
* [Thaller, *The Dirac Equation*][thaller1992], Chapter 1

## Tags

probability conservation, continuity equation, Born rule, divergence theorem,
current conservation
-/

namespace SpectralTheory.Conservation

open Dirac.Current Complex MeasureTheory Filter

/-! ## Calculus Setup -/

/-- Standard basis vector eᵤ in ℝ⁴.

  e₀ = (1,0,0,0), e₁ = (0,1,0,0), e₂ = (0,0,1,0), e₃ = (0,0,0,1)

Used to define partial derivatives via directional derivatives. -/
def stdBasis (μ : Fin 4) : Spacetime := fun ν => if μ = ν then 1 else 0

/-- The four-divergence ∂ᵤjᵘ = ∂₀j⁰ + ∂₁j¹ + ∂₂j² + ∂₃j³.

In components: ∂ᵤjᵘ = ∂ρ/∂t + ∂jˣ/∂x + ∂jʸ/∂y + ∂jᶻ/∂z.

The continuity equation states ∂ᵤjᵘ = 0 for solutions of the Dirac equation. -/
noncomputable def fourDivergence (j : (Fin 4 → ℝ) → (Fin 4 → ℂ)) : (Fin 4 → ℝ) → ℂ :=
  fun x => ∑ μ, deriv (fun t => j (Function.update x μ t) μ) (x μ)

/-- Partial derivative of a spinor field: ∂ᵤψ.

This is the directional derivative along the μ-th coordinate axis:
  (∂ᵤψ)(x) = lim_{ε→0} (ψ(x + εeᵤ) - ψ(x)) / ε

Each spinor component is differentiated separately. -/
noncomputable def partialDeriv' (μ : Fin 4) (ψ : Spacetime → (Fin 4 → ℂ)) (x : Spacetime) : Fin 4 → ℂ :=
  fun a => fderiv ℝ (fun y => ψ y a) x (stdBasis μ)


/-! ## Current Conservation Axiom -/

/-- **Axiom**: The Dirac equation implies current conservation: ∂ᵤjᵘ = 0.

If ψ satisfies the Dirac equation (iγᵘ∂ᵤ - m)ψ = 0, then the current
jᵘ = ψ̄γᵘψ is conserved: ∂ᵤjᵘ = 0.

**Proof sketch** (not formalized):
1. Take ∂ᵤ of jᵘ = ψ̄γᵘψ using the product rule
2. Use the Dirac equation to replace iγᵘ∂ᵤψ with mψ
3. Use the adjoint equation to replace i∂ᵤψ̄γᵘ with -mψ̄
4. The mass terms cancel, leaving ∂ᵤjᵘ = 0

This axiom would follow from a formalization of distribution theory and
the calculus of spinor-valued functions. -/
axiom dirac_current_conserved (Γ : GammaMatrices) (ψ : SpinorField) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x) :
    ∀ x, fourDivergence (fun x => diracCurrent Γ (ψ.ψ x)) x = 0


/-! ## Integration Axioms -/

/-- **Axiom**: Leibniz integral rule — differentiation commutes with integration.

  d/dt ∫f(t,x)d³x = ∫(∂f/∂t)(t,x)d³x

This holds under suitable regularity conditions (f continuous, ∂f/∂t exists
and is dominated by an integrable function). -/
axiom leibniz_integral_rule (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) :
    deriv (totalProbability Γ ψ) t =
    ∫ x : Fin 3 → ℝ, deriv (fun s => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) t ∂volume

/-- **Axiom**: The continuity equation ∂ρ/∂t = -∇·j.

This is the spatial decomposition of ∂ᵤjᵘ = 0:
  ∂j⁰/∂t + ∂j¹/∂x¹ + ∂j²/∂x² + ∂j³/∂x³ = 0
  ⟺  ∂ρ/∂t = -(∂jˣ/∂x + ∂jʸ/∂y + ∂jᶻ/∂z) = -∇·j

The axiom states this pointwise for each (t,x). -/
axiom continuity_equation (Γ : GammaMatrices) (ψ : SpinorField) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x)
    (t : ℝ) (x : Fin 3 → ℝ) :
    deriv (fun s => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) t =
    -(∑ i : Fin 3, deriv (fun s => (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re) (x i))

/-- **Axiom**: The divergence theorem with vanishing boundary conditions.

  ∫∇·j d³x = 0

when j(x) → 0 as |x| → ∞.

This is the divergence theorem applied to all of ℝ³: the "boundary at infinity"
contributes nothing if the field decays sufficiently fast. Physically, this
means no probability escapes to infinity. -/
axiom divergence_integral_vanishes (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ)
    (h_vanish : Tendsto (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint t x)))
                        (cocompact _) (nhds 0)) :
    ∫ x : Fin 3 → ℝ, (∑ i : Fin 3, deriv (fun s => (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re) (x i)) ∂volume = 0


/-! ## Main Theorem: Probability Conservation -/

/-- **MAIN THEOREM**: Total probability is conserved: d/dt ∫ρ d³x = 0.

**Physical meaning**: The total probability of finding the particle somewhere
in space is constant in time. Particles are neither created nor destroyed
by the free Dirac equation.

**Hypotheses**:
- `h_dirac`: ψ satisfies the Dirac equation
- `h_vanish`: ψ decays at spatial infinity (physically reasonable)

**Proof**:
1. Differentiate under the integral sign (Leibniz rule)
2. Apply the continuity equation ∂ρ/∂t = -∇·j
3. The integral of ∇·j vanishes by the divergence theorem -/
theorem probability_conserved (Γ : GammaMatrices) (ψ : SpinorField) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x)
    (h_vanish : ∀ t, Tendsto (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint t x)))
                              (cocompact _) (nhds 0)) :
    ∀ t, deriv (totalProbability Γ ψ) t = 0 := by
  intro t
  -- Step 1: Move derivative inside integral (Leibniz rule)
  rw [leibniz_integral_rule]
  -- Step 2: Apply continuity equation ∂₀ρ = -∇·j
  have h_cont := continuity_equation Γ ψ m h_dirac t
  simp_rw [h_cont]
  -- Step 3: Integral of negative divergence
  rw [MeasureTheory.integral_neg]
  -- Step 4: Divergence integral vanishes by boundary conditions
  rw [divergence_integral_vanishes Γ ψ t (h_vanish t)]
  simp


/-! ## The Born Rule -/

namespace BornRuleConnection

/-- The normalized probability density: P(x,t) = ρ(x,t) / ∫ρ d³x.

This converts the (unnormalized) probability density ρ into a proper
probability distribution that integrates to 1.

For a state already normalized to ∫ρ d³x = 1, we have P = ρ. -/
noncomputable def normalizedProbability (Γ : GammaMatrices) (ψ : SpinorField)
    (t : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  probabilityDensity Γ (ψ.ψ (spacetimePoint t x)) / totalProbability Γ ψ t

/-- **BORN'S RULE**: The normalized probability density is a valid probability distribution.

**The theorem**: For any non-trivial solution ψ of the Dirac equation:
1. P(x,t) ≥ 0 for all x (non-negativity)
2. ∫P(x,t) d³x = 1 (normalization)

**Physical meaning**: |ψ(x)|² / ∫|ψ|²d³x gives the probability density for
finding the particle at position x. This is the Born rule — the fundamental
link between the mathematical wavefunction and physical measurement.

**Historical note**: Max Born proposed this interpretation in 1926, for which
he received the Nobel Prize in 1954. It was initially controversial (Einstein:
"God does not play dice") but is now universally accepted.

**Hypotheses**:
- `h_dirac`: ψ satisfies the Dirac equation
- `h_nonzero`: ψ is not the zero state (otherwise probability is undefined) -/
theorem born_rule_valid (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) (m : ℂ)
    (_ /-h_dirac-/ : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x)
    (h_nonzero : totalProbability Γ ψ t ≠ 0) :
    -- Part 1: Probability is non-negative
    (∀ x, 0 ≤ normalizedProbability Γ ψ t x) ∧
    -- Part 2: Probability integrates to 1
    (∫ x, normalizedProbability Γ ψ t x ∂volume = 1) := by
  constructor
  · -- Part 1: Non-negativity
    intro x
    unfold normalizedProbability
    -- P = ρ(x)/∫ρ ≥ 0 because both numerator and denominator are ≥ 0
    apply div_nonneg
    · -- ρ(x) = (j⁰).re ≥ 0
      exact current_zero_nonneg Γ _
    · -- ∫ρ ≥ 0 (integral of non-negative function)
      unfold totalProbability
      apply MeasureTheory.integral_nonneg
      intro y
      exact current_zero_nonneg Γ _
  · -- Part 2: Normalization to 1
    unfold normalizedProbability
    -- ∫(ρ/∫ρ) = (1/∫ρ) · ∫ρ = 1
    simp only [div_eq_mul_inv]
    rw [MeasureTheory.integral_mul_const]
    -- (∫ρ) · (∫ρ)⁻¹ = 1 (using h_nonzero)
    exact CommGroupWithZero.mul_inv_cancel
        (∫ (a : Fin 3 → ℝ), probabilityDensity Γ (ψ.ψ (spacetimePoint t a))) h_nonzero

end BornRuleConnection

end SpectralTheory.Conservation
