/-
================================================================================
HEISENBERG UNCERTAINTY PRINCIPLE - FOUNDATIONS
================================================================================

The Heisenberg uncertainty principle:

    σₓ · σₚ ≥ ℏ/2

is a direct consequence of the canonical commutation relation:

    [X̂, P̂] = iℏ

**References:**
- Heisenberg, W. (1927). "Über den anschaulichen Inhalt der quantentheoretischen
  Kinematik und Mechanik". Z. Physik 43, 172-198.
- Kennard, E.H. (1927). "Zur Quantenmechanik einfacher Bewegungstypen".
  Z. Physik 44, 326-352. (First rigorous proof of σₓσₚ ≥ ℏ/2)
- Robertson, H.P. (1929). "The Uncertainty Principle". Phys. Rev. 34, 163-164.
-/
import LogosLibrary.QuantumMechanics.Uncertainty.Robertson

namespace Heisenberg.Theorem
open Robertson.Theorem Robertson.Core InnerProductSpace Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/--
Heisenberg's Uncertainty Principle: σₓ · σₚ ≥ ℏ/2

**The Fundamental Limit:** For any quantum state ψ, the product of uncertainties
in position (X) and momentum (P) is bounded below by half the reduced Planck constant.

**Physical Statement:**
It is impossible to prepare a quantum state with arbitrarily precise position AND
momentum simultaneously. This is not a measurement limitation — it's intrinsic to
the mathematical structure of quantum mechanics.

**Proof Strategy:**

1. **Robertson's General Principle:** For any self-adjoint A, B:
   σ_A · σ_B ≥ (1/2)|⟨[A,B]⟩|

   Proven via Cauchy-Schwarz on shifted operators Ã = A - ⟨A⟩, B̃ = B - ⟨B⟩.

2. **Canonical Commutation Relation:** Position and momentum satisfy:
   [X, P] = iℏ

   This is the defining algebraic relation of quantum mechanics, arising from
   the representation X̂ψ(x) = xψ(x) and P̂ψ(x) = -iℏ(d/dx)ψ(x) on L²(ℝ).

3. **Substitution:** The commutator expectation is state-independent:
   ⟨ψ, [X,P]ψ⟩ = ⟨ψ, iℏψ⟩ = iℏ⟨ψ,ψ⟩ = iℏ

   Therefore: σₓ · σₚ ≥ (1/2)|iℏ| = (1/2)ℏ = ℏ/2

**Why This Matters:**

- **Foundation of QM:** Heisenberg (1927) showed uncertainty is fundamental, not
  due to experimental clumsiness. Robertson (1929) generalized to all observables.

- **Wave-Particle Duality:** A state localized in position (small σₓ) must be
  delocalized in momentum (large σₚ), explaining diffraction and tunneling.

- **Minimum Uncertainty States:** Gaussian wave packets saturate the bound,
  achieving σₓ · σₚ = ℏ/2 exactly. These are the "most classical" quantum states.

- **Energy-Time Relation:** Similar analysis gives ΔE · Δt ≥ ℏ/2, though "time"
  requires careful interpretation (it's not an observable in standard QM).

**Mathematical Subtlety:**
Position and momentum are unbounded operators, requiring careful domain tracking.
The canonical commutation relation [X,P] = iℏ cannot hold for bounded operators
on a finite-dimensional space (take the trace of both sides: 0 ≠ iℏ·dim(H)).
This is why we work with unbounded operators on infinite-dimensional Hilbert space.
-/
theorem heisenberg_uncertainty_principle
    (X P : UnboundedObservable H)
    (ψ : H)
    (h_norm : ‖ψ‖ = 1)
    (h_domX : ψ ∈ X.domain)
    (h_domP : ψ ∈ P.domain)
    (h_dom_XP : P.op ψ ∈ X.domain)
    (h_dom_PX : X.op ψ ∈ P.domain)
    (h_canonical : ⟪ψ, (X.op ∘ₗ P.op - P.op ∘ₗ X.op) ψ⟫_ℂ = Complex.I * ℏ) :
    unboundedStandardDeviation X ψ h_norm h_domX *
    unboundedStandardDeviation P ψ h_norm h_domP ≥ ℏ / 2 := by
  have h_robertson := robertson_uncertainty_principle X P ψ h_norm h_domX h_domP h_dom_XP h_dom_PX
  rw [h_canonical] at h_robertson
  have h_norm_iℏ : ‖Complex.I * ℏ‖ = ℏ := by
    rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    exact Real.norm_of_nonneg (le_of_lt ℏ_pos)
  calc unboundedStandardDeviation X ψ h_norm h_domX *
       unboundedStandardDeviation P ψ h_norm h_domP
      ≥ (1/2) * ‖Complex.I * ℏ‖ := h_robertson
    _ = (1/2) * ℏ := by rw [h_norm_iℏ]
    _ = ℏ / 2 := by ring

  end Heisenberg.Theorem
