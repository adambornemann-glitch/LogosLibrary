/-
Author: Adam Bornemann
Created: 10/22/2025
Updated: 12/26/2025

================================================================================
PHYSICAL INTERPRETATION OF STONE'S THEOREM
================================================================================

In quantum mechanics, Stone's theorem is the mathematical foundation for
the time evolution of quantum states.
-/
import LogosLibrary.QuantumMechanics.Evolution.MarshallStone

namespace Schrödinger

open InnerProductSpace Complex Filter Topology
open StonesTheorem.Yosida StonesTheorem.Resolvent StonesTheorem.Bochner Stone.Generators StonesTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Schrödinger Equation**

For a quantum system with Hamiltonian H (a self-adjoint operator),
the time evolution satisfies:

  i ℏ d/dt |ψ(t)⟩ = H |ψ(t)⟩

In our convention with U(t) = exp(itA), we get d/dt[U(t)ψ] = iA·U(t)ψ.

Note: Physics typically uses U(t) = exp(-itH), giving d/dt = -iH.
Our convention is A = -H (generator = negative Hamiltonian).
-/
theorem schrodinger_equation
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ₀ : H) (hψ₀ : ψ₀ ∈ gen.domain) :
    -- The evolved state ψ(t) = U(t)ψ₀ satisfies d/dt[U(t)ψ₀]|_{t=0} = iAψ₀
    HasDerivAt (fun t : ℝ => U_grp.U t ψ₀)
               (I • gen.op ⟨U_grp.U 0 ψ₀, gen.domain_invariant 0 ψ₀ hψ₀⟩)
               0 := by
  -- Use exponential_derivative_on_domain at t = 0
  have h_deriv := exponential_derivative_on_domain gen hsa h_dense 0 ψ₀ hψ₀

  -- Convert from exponential to U_grp.U
  have h_eq : ∀ t, exponential' gen hsa h_dense t ψ₀ = U_grp.U t ψ₀ :=
    fun t => stone_exponential_eq_group U_grp gen hsa h_dense t ψ₀

  -- Rewrite the derivative using the equality
  have h_fun_eq : (fun t => exponential' gen hsa h_dense t ψ₀) = (fun t => U_grp.U t ψ₀) := by
    ext t; exact h_eq t
  rw [h_fun_eq] at h_deriv

  exact h_deriv

  end Schrödinger
