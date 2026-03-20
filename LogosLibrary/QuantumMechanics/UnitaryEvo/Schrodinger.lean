/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: UnitaryEvo/Schrodinger.lean
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Stone
/-!
# The Schrödinger Equation

The Schrödinger equation emerges as a theorem from Stone's correspondence.

## Main result

* `schrödinger_equation`: For a state ψ₀ in the domain of the Hamiltonian,
  the time-evolved state U(t)ψ₀ satisfies

      d/dt |ψ(t)⟩ = iA|ψ(t)⟩

  where A is the self-adjoint generator (the Hamiltonian, up to constants).

## Physical interpretation

This theorem says: **unitary time evolution implies the Schrödinger equation.**

The converse is Stone's theorem: **the Schrödinger equation implies unitary evolution.**

Together, they establish that the Schrödinger equation is not an independent axiom
of quantum mechanics, but rather equivalent to the requirement that time evolution
preserve probability and form a continuous group.

## References

* Schrödinger, "Quantisierung als Eigenwertproblem" (1926)
* Stone, "On one-parameter unitary groups in Hilbert space" (1932)
-/
namespace QuantumMechanics.Schrödinger

open InnerProductSpace Complex Filter Topology
open QuantumMechanics.Yosida QuantumMechanics.Resolvent QuantumMechanics.Bochner QuantumMechanics.Generators QuantumMechanics.StonesTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


theorem schrödinger_equation₁
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ₀ : H) (hψ₀ : ψ₀ ∈ gen.domain) :
    HasDerivAt (fun t : ℝ => U_grp.U t ψ₀)
               (I • gen.op ⟨U_grp.U 0 ψ₀, gen.domain_invariant 0 ψ₀ hψ₀⟩)
               0 := by
  have h_deriv := exponential_derivative_on_domain gen hsa h_dense 0 ψ₀ hψ₀
  have h_eq : ∀ t, exponential gen hsa h_dense t ψ₀ = U_grp.U t ψ₀ :=
    fun t => stone_exponential_eq_group U_grp gen hsa h_dense t ψ₀
  have h_fun_eq : (fun t => exponential gen hsa h_dense t ψ₀) = (fun t => U_grp.U t ψ₀) := by
    ext t; exact h_eq t
  rw [h_fun_eq] at h_deriv
  exact h_deriv


/-- **The Schrödinger equation at arbitrary time.**
If `ψ₀` is in the domain of the generator, then `t ↦ U(t)ψ₀` is differentiable
with `d/dt U(t)ψ₀ = iA(U(t)ψ₀)` for all `t ∈ ℝ`. -/
theorem schrödinger_equation₂
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ₀ : H) (hψ₀ : ψ₀ ∈ gen.domain)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => U_grp.U s ψ₀)
               (I • gen.op ⟨U_grp.U t ψ₀, gen.domain_invariant t ψ₀ hψ₀⟩)
               t := by
  have hφ : U_grp.U t ψ₀ ∈ gen.domain := gen.domain_invariant t ψ₀ hψ₀
  have h0 := schrödinger_equation₁ U_grp gen hsa h_dense (U_grp.U t ψ₀) hφ
  have hfun : (fun r => U_grp.U r (U_grp.U t ψ₀)) =
      (fun r => U_grp.U (r + t) ψ₀) := by
    ext r; exact (ContinuousLinearMap.ext_iff.mp (U_grp.group_law r t) ψ₀).symm
  have hderiv : gen.op ⟨U_grp.U 0 (U_grp.U t ψ₀), gen.domain_invariant 0 _ hφ⟩ =
      gen.op ⟨U_grp.U t ψ₀, hφ⟩ := by
    congr 1; ext
    simp [show U_grp.U 0 = ContinuousLinearMap.id ℂ H from U_grp.identity]
  rw [hfun, hderiv] at h0
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at h0 ⊢
  refine h0.congr (fun r => ?_) (fun _ => rfl)
  congr 2; congr 1; ring_nf; 
  norm_num


  end QuantumMechanics.Schrödinger
