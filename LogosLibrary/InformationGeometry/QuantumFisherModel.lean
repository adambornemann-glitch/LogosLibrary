/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/QuantumFisherModel.lean
-/
import LogosLibrary.InformationGeometry.CompositeObservable
/-!
# The Quantum Fisher Model: Discharging the Kähler Axiom

This file constructs an `RLDFisherModel` — the information-geometric
structure carrying both a Riemannian metric and a symplectic form —
from quantum-mechanical data.  It is the **bridge file** that proves
the Kähler structure of the quantum state manifold is not merely
analogical but a theorem.

The construction proceeds in two steps:

**Step 1: The quantum Schrödinger bound** (`quantum_schrodinger_bilinear`).
Applying the Schrödinger uncertainty relation to composite observables
`O_v = ∑ vᵢ Oᵢ` and `O_w = ∑ wⱼ Oⱼ`, and substituting the bilinearity
lemmas from `CompositeObservable.lean`, yields:

  `(∑ vᵢvⱼ Cov_{ij})(∑ wᵢwⱼ Cov_{ij}) ≥ (∑ vᵢwⱼ Cov_{ij})² + ¼(∑ vᵢwⱼ ω_{ij})²`

where `Cov_{ij} = Cov(Oᵢ,Oⱼ)_ψ` and `ω_{ij} = Im⟨ψ,[Oᵢ,Oⱼ]ψ⟩`.
This is Cauchy–Schwarz for a complex Hermitian form restricted to
real vectors — exactly the RLD Cauchy–Schwarz condition.

**Step 2: The model construction** (`quantumRLDFisherModel`).  Given
quantum data `D : QuantumRLDData` and a statistical model `M` whose
Fisher matrix satisfies `g_{ij}(θ) = 4 Cov(Oᵢ,Oⱼ)_ψ`, we set the
symplectic form to `ω_{ij} = 2 Im⟨ψ,[Oᵢ,Oⱼ]ψ⟩` and discharge the
RLD Cauchy–Schwarz axiom from Step 1.  The factors of 4 and 2 are
the standard normalization: the SLD Fisher information for pure states
is `4 Var(A)` (the Braunstein–Caves factor), and the symplectic form
carries the corresponding factor of 2.

## The information-geometric meaning

The `rld_cauchy_schwarz` axiom of `RLDFisherModel` is the assertion
that the complex matrix `G^RLD = g + iω` is positive semidefinite.
In classical statistics, `ω = 0` and this reduces to positive
semidefiniteness of the Fisher matrix — a consequence of its Gram
matrix structure `g_{ij} = E[sᵢ sⱼ]`.

In quantum mechanics, the Gram matrix structure generalizes to
`G^RLD_{ij} = Tr(ρ Rᵢ† Rⱼ)` (the RLD Gram matrix), whose positive
semidefiniteness is Hilbert-space Cauchy–Schwarz applied to the
vectors `Rᵢ √ρ` in the Hilbert–Schmidt space.  Our proof works
directly with the shifted observables `Õᵢψ = (Oᵢ - ⟨Oᵢ⟩)ψ` in
the original Hilbert space, which is equivalent for pure states.

The result: **the Schrödinger uncertainty relation is the quantum
Cramér–Rao bound for the RLD Fisher information**.  The covariance
term is the Riemannian (SLD) contribution; the commutator term is
the symplectic contribution.  Together they form the Kähler metric
on the quantum state manifold.

## References

* D. Petz, "Monotone metrics on matrix spaces",
  *Linear Algebra Appl.* **244** (1996), 81–96.
  — Classification of quantum Fisher informations; the SLD metric
  is the maximal element.
* S. L. Braunstein, C. M. Caves, "Statistical distance and the
  geometry of quantum states", *Phys. Rev. Lett.* **72** (1994),
  3439–3443. — The factor of 4 relating quantum and classical
  Fisher information.
* S. Amari, H. Nagaoka, *Methods of Information Geometry*, AMS,
  2000, Ch. 7. — Quantum information geometry and the duality
  between the e- and m-connections, which becomes the duality
  between `g` and `ω` in the Kähler setting.
-/
namespace QuantumMechanics.Bridge

open InnerProductSpace UnboundedObservable Robertson Schrodinger InformationGeometry
open scoped ComplexConjugate

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Quantum Schrödinger–Cauchy–Schwarz bound (bilinear form level).**

For all real coefficient vectors `v, w`:

  `(∑ᵢⱼ vᵢvⱼ Cov(Oᵢ,Oⱼ)) · (∑ᵢⱼ wᵢwⱼ Cov(Oᵢ,Oⱼ))
   ≥ (∑ᵢⱼ vᵢwⱼ Cov(Oᵢ,Oⱼ))² + ¼(∑ᵢⱼ vᵢwⱼ Im⟨ψ,[Oᵢ,Oⱼ]ψ⟩)²`

This is the quantum content that discharges the `rld_cauchy_schwarz`
axiom of `RLDFisherModel`. -/
theorem quantum_schrodinger_bilinear (D : QuantumRLDData n H) (v w : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
      v i * v j * covariance (D.O i) (D.O j) D.ψ (pairwise_shiftedDC D i j)) *
    (∑ i : Fin n, ∑ j : Fin n,
      w i * w j * covariance (D.O i) (D.O j) D.ψ (pairwise_shiftedDC D i j)) ≥
    (∑ i : Fin n, ∑ j : Fin n,
      v i * w j * covariance (D.O i) (D.O j) D.ψ (pairwise_shiftedDC D i j)) ^ 2 +
    (1/4) * (∑ i : Fin n, ∑ j : Fin n,
      v i * w j * (⟪D.ψ, commutatorAt (D.O i) (D.O j) D.ψ
        (pairwise_shiftedDC D i j).toDomainConditions⟫_ℂ).im) ^ 2 := by
  -- Step 1: Apply schrodinger_uncertainty to O_v, O_w
  have h_sch := schrodinger_uncertainty
    (compositeObservable D.O v D.h_dense)
    (compositeObservable D.O w D.h_dense)
    D.ψ (D.composites_shiftedDC v w)
  -- Step 2: Substitute bilinearity of variance
  rw [variance_composite D v, variance_composite D w] at h_sch
  -- Step 3: Substitute bilinearity of covariance
  rw [covariance_composite D v w] at h_sch
  -- Step 4: Convert ‖z‖² to z.im² in h_sch (since z.re = 0)
  have h_comm_re := commutator_re_eq_zero
    (compositeObservable D.O v D.h_dense)
    (compositeObservable D.O w D.h_dense)
    D.ψ (D.composites_shiftedDC v w).toDomainConditions
  have h_norm_to_im : ‖⟪D.ψ, commutatorAt
      (compositeObservable D.O v D.h_dense)
      (compositeObservable D.O w D.h_dense)
      D.ψ (D.composites_shiftedDC v w).toDomainConditions⟫_ℂ‖ ^ 2 =
    (⟪D.ψ, commutatorAt
      (compositeObservable D.O v D.h_dense)
      (compositeObservable D.O w D.h_dense)
      D.ψ (D.composites_shiftedDC v w).toDomainConditions⟫_ℂ).im ^ 2 := by
    rw [Complex.sq_norm, normSq_of_re_zero h_comm_re]
  rw [h_norm_to_im] at h_sch
  -- Step 5: Now substitute commutator bilinearity
  rw [commutator_im_composite D v w] at h_sch
  -- h_sch now matches the goal exactly (possibly up to add_comm)
  linarith


/-- Factor a constant out of a bilinear double sum. -/
private lemma factor_sum (c : ℝ) (f : Fin n → Fin n → ℝ) (u₁ u₂ : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, u₁ i * u₂ j * (c * f i j) =
    c * (∑ i : Fin n, ∑ j : Fin n, u₁ i * u₂ j * f i j) := by
  simp_rw [show ∀ i j, u₁ i * u₂ j * (c * f i j) =
    c * (u₁ i * u₂ j * f i j) from fun i j => by ring]
  simp_rw [← Finset.mul_sum]


variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
/-- The quantum RLD Fisher model: information geometry from Hilbert space.

Given quantum data `D` and a regular statistical model `M` whose Fisher
matrix satisfies `g_{ij}(θ) = 4 Cov(Oᵢ,Oⱼ)_ψ`, we construct an
`RLDFisherModel` with symplectic form `ω_{ij} = 2 Im⟨ψ,[Oᵢ,Oⱼ]ψ⟩`.

The RLD Cauchy–Schwarz condition is discharged from the Schrödinger
uncertainty relation applied to composite observables. -/
noncomputable def quantumRLDFisherModel (D : QuantumRLDData n H)
    (M : RegularStatisticalModel n Ω)
    (h_fisher : ∀ θ ∈ M.paramDomain, ∀ i j : Fin n,
      M.fisherMatrix θ i j =
        4 * covariance (D.O i) (D.O j) D.ψ (pairwise_shiftedDC D i j))
    : RLDFisherModel n Ω where
  toRegularStatisticalModel := M
  symplecticForm := fun _θ i j =>
    2 * (⟪D.ψ, commutatorAt (D.O i) (D.O j) D.ψ
      (pairwise_shiftedDC D i j).toDomainConditions⟫_ℂ).im
  symplectic_antisymm := fun _θ _hθ i j => by
    -- [Oᵢ,Oⱼ]ψ = -[Oⱼ,Oᵢ]ψ
    have h_anti : commutatorAt (D.O i) (D.O j) D.ψ
        (pairwise_shiftedDC D i j).toDomainConditions =
      -commutatorAt (D.O j) (D.O i) D.ψ
        (pairwise_shiftedDC D j i).toDomainConditions := by
      unfold commutatorAt DomainConditions.ABψ DomainConditions.BAψ
      module
    rw [h_anti, inner_neg_right, Complex.neg_im]; ring
  rld_cauchy_schwarz := fun θ hθ v w => by
    -- Substitute g_{ij} = 4 * Cov_{ij}
    simp_rw [h_fisher θ hθ]
    -- Factor constants out of all sums:
    --   ∑ᵢⱼ uᵢuⱼ (4 * Cov) = 4 * ∑ᵢⱼ uᵢuⱼ Cov
    --   ∑ᵢⱼ uᵢuⱼ (2 * Im)  = 2 * ∑ᵢⱼ uᵢuⱼ Im
    rw [factor_sum 4 _ v w, factor_sum 4 _ v v, factor_sum 4 _ w w,
        factor_sum 2 _ v w]
    -- Goal: (4 * Σ Cov_vw)² + (2 * Σ Im_vw)² ≤ (4 * Σ Cov_vv) * (4 * Σ Cov_ww)
    -- i.e.: 16 Cov_vw² + 4 Im_vw² ≤ 16 Cov_vv · Cov_ww
    -- From quantum_schrodinger_bilinear: Cov_vv · Cov_ww ≥ Cov_vw² + ¼ Im_vw²
    -- Multiply by 16: done.
    have h := quantum_schrodinger_bilinear D v w
    nlinarith


end QuantumMechanics.Bridge
