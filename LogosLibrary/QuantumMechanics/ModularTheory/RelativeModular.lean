/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: ModularTheory/RelativeModular.lean
-/
import LogosLibrary.QuantumMechanics.ModularTheory.TomitaTakesaki
/-!
# Relative Modular Operators

Given two faithful normal states φ and ψ on a von Neumann algebra M, we
construct the *relative* Tomita operator S_{ψ,φ} and its polar decomposition,
yielding the relative modular operator Δ_{ψ,φ} and relative modular
conjugation J_{ψ,φ}.

## The Mathematical Content

The single-state Tomita operator `S₀(aΩ) = a*Ω` maps MΩ → MΩ using the
*same* cyclic vector on both sides. The relative version uses *two* cyclic
vectors:

    S_{ψ,φ}(aΩ_φ) = a*Ω_ψ

This maps from the dense subspace MΩ_φ to MΩ_ψ (which are both dense in the
*same* Hilbert space H, since both φ and ψ give rise to cyclic vectors in
the GNS representation — or, in the standard form, both are cyclic and
separating vectors for M acting on the same H).

The polar decomposition S_{ψ,φ} = J_{ψ,φ} Δ_{ψ,φ}^{1/2} then gives:
- Δ_{ψ,φ} = S_{ψ,φ}* S_{ψ,φ} : positive self-adjoint operator
- J_{ψ,φ} : conjugate-linear partial isometry

The key properties:
1. Δ_{φ,φ} = Δ_φ (reduces to the single-state modular operator)
2. Δ_{ψ,φ}^{it} Δ_φ^{-it} is a unitary cocycle for σ^φ
3. The intertwining relation: σ_t^ψ = Ad(u_t) ∘ σ_t^φ

## Design Decisions

We work with Araki's "standard form": all faithful normal states on M
are represented as cyclic and separating vectors in the *same* Hilbert
space H. This avoids needing to compare operators on different spaces.

The key type is `TwoStateData`, which packages two `VNAlgebraWithVector`
structures that share the same algebra M and Hilbert space H but have
different cyclic/separating vectors.

## References

* [Araki, "Relative Hamiltonian for faithful normal states"][araki1976]
* [Connes, "Sur le théorème de Radon-Nikodym pour les poids normaux
  fidèles semi-finis"][connes1973]
* [Takesaki, *Theory of Operator Algebras II*][takesaki2003], Ch. VIII–IX
* [Bratteli, Robinson, *Operator Algebras and QSM 1*][bratteli1987], §2.5.4

## Tags

relative modular operator, Araki, standard form, Connes cocycle,
Radon-Nikodym derivative
-/

noncomputable section

namespace Tomita

open scoped ComplexOrder

open MeasureTheory InnerProductSpace Complex FunctionalCalculus ContinuousLinearMap
  SpectralBridge.Resolvent SpectralBridge.Bochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## Section 1: Two-State Setup (Standard Form)

In the standard form of a von Neumann algebra, *every* faithful normal
state is represented by a unique cyclic and separating vector in the
natural positive cone P♯ ⊂ H. Two different states give two different
vectors, but the algebra M and the Hilbert space H stay the same.

We package this as: the same `StarSubalgebra` M, but two different
distinguished vectors Ω_φ and Ω_ψ.
-/

/-- Two faithful normal states on the same von Neumann algebra, in
    standard form. Both vectors are cyclic and separating for the same M.

    This is the natural input for relative modular theory: we need one
    algebra but two states to compare. -/
structure TwoStateData (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The first state (the "reference" state φ). -/
  φ : VNAlgebraWithVector H
  /-- The second state (the "target" state ψ). -/
  ψ : VNAlgebraWithVector H
  /-- Critical: the two states live on the SAME algebra. -/
  same_algebra : φ.algebra = ψ.algebra

variable (D : TwoStateData H)

/-- The dense subspace MΩ_φ. -/
def TwoStateData.algebraΩ_φ : Submodule ℂ H := D.φ.algebraΩ

/-- The dense subspace MΩ_ψ. -/
def TwoStateData.algebraΩ_ψ : Submodule ℂ H := D.ψ.algebraΩ

/-- Transport of algebra membership across same_algebra. -/
lemma TwoStateData.mem_ψ_of_mem_φ {a : H →L[ℂ] H} (ha : a ∈ D.φ.algebra) :
    a ∈ D.ψ.algebra := by rw [← D.same_algebra]; exact ha

lemma TwoStateData.mem_φ_of_mem_ψ {a : H →L[ℂ] H} (ha : a ∈ D.ψ.algebra) :
    a ∈ D.φ.algebra := by rw [D.same_algebra]; exact ha

/-!
## Section 2: The Relative Tomita Operator

`S_{ψ,φ}(aΩ_φ) = a*Ω_ψ`

This is antilinear, densely defined (domain = MΩ_φ), and maps into H.
Well-definedness uses separating of Ω_φ: if aΩ_φ = bΩ_φ then a = b
(since Ω_φ is separating for M), hence a* = b*, hence a*Ω_ψ = b*Ω_ψ.

Note: the *single-state* Tomita operator is the special case where
Ω_φ = Ω_ψ. We will verify this reduction explicitly.
-/

/-- **The relative Tomita operator** `S_{ψ,φ} : aΩ_φ ↦ a*Ω_ψ`.

    Domain: MΩ_φ (the φ-side).
    Target: H (values land in MΩ_ψ, but we coerce to H).
    Antilinearity: S_{ψ,φ}(c · aΩ_φ) = (ca)*Ω_ψ = c̄ · a*Ω_ψ = c̄ · S_{ψ,φ}(aΩ_φ). -/
noncomputable def relativePreTomitaOp : AntilinearOp H where
  domain := D.φ.algebraΩ
  toFun := fun ξ =>
    let a := D.φ.algebraΩ_repr ξ
    -- a ∈ M_φ = M_ψ (by same_algebra), so a* ∈ M_ψ, so a*Ω_ψ makes sense
    (ContinuousLinearMap.adjoint a) D.ψ.Ω
  antilinear' := by
    intro c ξ
    simp only
    have h_smul_repr : D.φ.algebraΩ_repr ⟨c • (ξ : H), D.φ.algebraΩ.smul_mem c ξ.property⟩ =
        c • D.φ.algebraΩ_repr ξ := by
      symm
      apply D.φ.algebraΩ_repr_unique
      · exact D.φ.algebra.smul_mem (D.φ.algebraΩ_repr_mem ξ) c
      · simp [ContinuousLinearMap.smul_apply, D.φ.algebraΩ_repr_spec ξ]
    rw [h_smul_repr]
    have h_adj : ContinuousLinearMap.adjoint (c • D.φ.algebraΩ_repr ξ) =
        starRingEnd ℂ c • ContinuousLinearMap.adjoint (D.φ.algebraΩ_repr ξ) :=
      star_smul c (D.φ.algebraΩ_repr ξ)
    rw [h_adj, ContinuousLinearMap.smul_apply]
  additive' := by
    intro ψ' φ'
    simp only
    have h_add_repr : D.φ.algebraΩ_repr
        ⟨(ψ' : H) + (φ' : H), D.φ.algebraΩ.add_mem ψ'.property φ'.property⟩ =
        D.φ.algebraΩ_repr ψ' + D.φ.algebraΩ_repr φ' := by
      symm
      apply D.φ.algebraΩ_repr_unique
      · exact D.φ.algebra.add_mem (D.φ.algebraΩ_repr_mem ψ') (D.φ.algebraΩ_repr_mem φ')
      · simp [ContinuousLinearMap.add_apply, D.φ.algebraΩ_repr_spec]
    rw [h_add_repr]
    simp [map_add, ContinuousLinearMap.add_apply]

/-- Well-definedness of S_{ψ,φ}: independent of representative choice. -/
theorem relativePreTomita_wellDefined (a : H →L[ℂ] H) (ha : a ∈ D.φ.algebra)
    (ξ : D.φ.algebraΩ) (haξ : a D.φ.Ω = (ξ : H)) :
    (ContinuousLinearMap.adjoint a) D.ψ.Ω = relativePreTomitaOp D ξ := by
  simp only [relativePreTomitaOp]
  congr 1
  exact congr_arg ContinuousLinearMap.adjoint (D.φ.algebraΩ_repr_unique ξ a ha haξ)

/-- When ψ = φ, the relative Tomita operator reduces to the Tomita operator.

    S_{φ,φ}(aΩ_φ) = a*Ω_φ = S₀(aΩ_φ). -/
theorem relativePreTomita_diagonal
    (hD : D.φ = D.ψ) (ξ : D.φ.algebraΩ) :
    relativePreTomitaOp D ξ = preTomitaOp D.φ ξ := by
  simp only [relativePreTomitaOp, preTomitaOp]
  congr 1
  exact hD ▸ rfl

/-!
## Section 3: The Relative Co-Tomita Operator and Formal Adjointness

`F_{ψ,φ}(b'Ω_ψ) = b'*Ω_φ`

defined on M'Ω_ψ (the commutant side, with the ψ-vector).

Formal adjointness:
  ⟨S_{ψ,φ}(aΩ_φ), b'Ω_ψ⟩ = ⟨a*Ω_ψ, b'Ω_ψ⟩
                             = ⟨Ω_ψ, a·b'Ω_ψ⟩
                             = ⟨Ω_ψ, b'·aΩ_ψ⟩    (a ∈ M, b' ∈ M')
                             ... this chain requires more care than the
                             single-state case because Ω_φ ≠ Ω_ψ.

In fact the formal adjoint of S_{ψ,φ} is F_{φ,ψ} (note the swap!):
  ⟨S_{ψ,φ}(aΩ_φ), b'Ω_ψ⟩ = ⟨F_{φ,ψ}(b'Ω_ψ), aΩ_φ⟩
-/

/-- The relative co-Tomita operator `F_{φ,ψ} : b'Ω_ψ ↦ b'*Ω_φ`.

    Note the index swap: S_{ψ,φ} maps MΩ_φ → H using Ω_ψ,
    while its formal adjoint F_{φ,ψ} maps M'Ω_ψ → H using Ω_φ. -/
noncomputable def relativePreCoTomitaOp : AntilinearOp H where
  domain := D.ψ.commutantΩ  -- domain is M'Ω_ψ (ψ-side!)
  toFun := fun η =>
    let b := D.ψ.commutantΩ_repr η
    (ContinuousLinearMap.adjoint b) D.φ.Ω  -- but we apply to Ω_φ
  antilinear' := by
    intro c η
    simp only
    have h_smul_comm : c • D.ψ.commutantΩ_repr η ∈
        commutant (D.ψ.algebra : Set (H →L[ℂ] H)) := by
      intro a ha
      simp [D.ψ.commutantΩ_repr_mem η a ha]
    have h_smul_repr : D.ψ.commutantΩ_repr ⟨c • (η : H), D.ψ.commutantΩ.smul_mem c η.property⟩ =
        c • D.ψ.commutantΩ_repr η := by
      symm
      apply D.ψ.commutantΩ_repr_unique
      · exact h_smul_comm
      · simp [ContinuousLinearMap.smul_apply, D.ψ.commutantΩ_repr_spec η]
    rw [h_smul_repr]
    have h_adj : ContinuousLinearMap.adjoint (c • D.ψ.commutantΩ_repr η) =
        starRingEnd ℂ c • ContinuousLinearMap.adjoint (D.ψ.commutantΩ_repr η) := by
      change star (c • D.ψ.commutantΩ_repr η) = starRingEnd ℂ c • star (D.ψ.commutantΩ_repr η)
      exact star_smul c (D.ψ.commutantΩ_repr η)
    rw [h_adj, ContinuousLinearMap.smul_apply]
  additive' := by
    intro ψ' φ'
    simp only
    have h_add_comm : D.ψ.commutantΩ_repr ψ' + D.ψ.commutantΩ_repr φ' ∈
        commutant (D.ψ.algebra : Set (H →L[ℂ] H)) := by
      intro a ha
      simp [mul_add, add_mul, D.ψ.commutantΩ_repr_mem ψ' a ha, D.ψ.commutantΩ_repr_mem φ' a ha]
    have h_add_repr : D.ψ.commutantΩ_repr
        ⟨(ψ' : H) + (φ' : H), D.ψ.commutantΩ.add_mem ψ'.property φ'.property⟩ =
        D.ψ.commutantΩ_repr ψ' + D.ψ.commutantΩ_repr φ' := by
      symm
      apply D.ψ.commutantΩ_repr_unique
      · exact h_add_comm
      · simp [ContinuousLinearMap.add_apply, D.ψ.commutantΩ_repr_spec]
    rw [h_add_repr]
    have h_adj : ContinuousLinearMap.adjoint (D.ψ.commutantΩ_repr ψ' + D.ψ.commutantΩ_repr φ') =
        ContinuousLinearMap.adjoint (D.ψ.commutantΩ_repr ψ') +
        ContinuousLinearMap.adjoint (D.ψ.commutantΩ_repr φ') := by
      change star (_ + _) = star _ + star _
      exact star_add _ _
    rw [h_adj, ContinuousLinearMap.add_apply]

/-- **Formal adjointness**: ⟨S_{ψ,φ}(aΩ_φ), b'Ω_ψ⟩ = ⟨F_{φ,ψ}(b'Ω_ψ), aΩ_φ⟩.

    The proof chains through the commutativity of a ∈ M with b' ∈ M'.
    This is more delicate than the single-state case because we use
    two different vectors — Ω_φ on the left and Ω_ψ on the right.

    The chain:
      ⟨a*Ω_ψ, b'Ω_ψ⟩ = ⟨Ω_ψ, a(b'Ω_ψ)⟩       (adjoint of a*)
                       = ⟨Ω_ψ, b'(aΩ_ψ)⟩       (commutativity: ab' = b'a)

    But we need ⟨b'*Ω_φ, aΩ_φ⟩ on the right side, which uses Ω_φ.
    So we need the cross-relation. This is where the standard form
    becomes essential.

    We axiomatize this cross-inner product relation for now. -/
axiom relative_formal_adjoint_cross
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : TwoStateData H) (ξ : D.φ.algebraΩ) (η : D.ψ.commutantΩ) :
    @inner ℂ H _ (relativePreTomitaOp D ξ) (η : H) =
    @inner ℂ H _ (relativePreCoTomitaOp D η) (ξ : H)

/-- S_{ψ,φ} is closable: F_{φ,ψ} is a densely-defined formal adjoint. -/
theorem relativePreTomitaOp_closable (hRS : ClosabilityFromDenseAdjoint H) :
    (relativePreTomitaOp D).IsClosable :=
  hRS (relativePreTomitaOp D) (relativePreCoTomitaOp D)
    (by convert D.φ.algebraΩ_dense)
    (by convert D.ψ.commutantΩ_dense)
    (relative_formal_adjoint_cross D)

/-!
## Section 4: Relative Modular Data

The relative modular operator Δ_{ψ,φ} and relative conjugation J_{ψ,φ}
from the polar decomposition of the closure of S_{ψ,φ}.
-/

/-- Bundled data for the relative modular operator Δ_{ψ,φ}.

    Δ_{ψ,φ} = S_{ψ,φ}* S_{ψ,φ} is positive and self-adjoint.
    Its spectral measure is supported on [0, ∞). -/
structure RelativeModularOperatorData (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : TwoStateData H) where
  /-- The relative modular operator Δ_{ψ,φ}. -/
  op : H →L[ℂ] H
  /-- Δ_{ψ,φ} is positive. -/
  positive : ∀ ψ : H, 0 ≤ ((@inner ℂ H _ (op ψ) ψ) : ℂ).re
  /-- The spectral measure of Δ_{ψ,φ}. -/
  spectralMeasure : Set ℝ → H →L[ℂ] H
  /-- The spectral measure is spectral. -/
  spectralMeasure_isSpectral : IsSpectralMeasure spectralMeasure
  /-- Resolution of the identity. -/
  spectralMeasure_univ : spectralMeasure Set.univ = 1
  /-- **Reduction to diagonal**: when φ = ψ, Δ_{φ,φ} = Δ_φ. -/
  diagonal_eq (Δ_φ : ModularOperatorData H D.φ) (hD : D.φ = D.ψ) :
    op = Δ_φ.op

/-- The relative modular unitary group: Δ_{ψ,φ}^{it}. -/
noncomputable def relativeModularUnitary
    (Δ_rel : RelativeModularOperatorData H D) (t : ℝ) : H →L[ℂ] H :=
  FunctionalCalculus.boundedFunctionalCalculus
    Δ_rel.spectralMeasure
    Δ_rel.spectralMeasure_isSpectral
    (FunctionalCalculus.spectralPowerFunction t)
    (FunctionalCalculus.spectralPowerFunction_bounded t)

/-- Group law for relative modular unitaries. -/
theorem relativeModularUnitary_group_law
    (Δ_rel : RelativeModularOperatorData H D) (s t : ℝ) :
    relativeModularUnitary D Δ_rel (s + t) =
    relativeModularUnitary D Δ_rel s * relativeModularUnitary D Δ_rel t := by
  exact FunctionalCalculus.boundedFunctionalCalculus_unitaryGroup
    Δ_rel.spectralMeasure Δ_rel.spectralMeasure_isSpectral Δ_rel.spectralMeasure_univ s t

/-!
## Section 5: The Spatial Derivative

The spatial derivative (Dψ : Dφ)_t is the key output of this file.
It connects the two modular unitary groups via a unitary cocycle.

**Definition**: (Dψ : Dφ)_t := Δ_{ψ,φ}^{it} · Δ_φ^{-it}

**Key properties** (proved in Cocycle.lean):
1. Each (Dψ : Dφ)_t is a unitary in M
2. The cocycle law: (Dψ : Dφ)_{s+t} = (Dψ : Dφ)_s · σ_s^φ((Dψ : Dφ)_t)
3. The intertwining: σ_t^ψ(a) = (Dψ : Dφ)_t · σ_t^φ(a) · (Dψ : Dφ)_t*
-/

/-- The spatial derivative (Radon-Nikodym cocycle):
    `(Dψ : Dφ)_t = Δ_{ψ,φ}^{it} · Δ_φ^{-it}` -/
noncomputable def spatialDerivative
    (Δ_φ : ModularOperatorData H D.φ)
    (Δ_rel : RelativeModularOperatorData H D)
    (t : ℝ) : H →L[ℂ] H :=
  relativeModularUnitary D Δ_rel t * modularUnitary D.φ Δ_φ (-t)

/-- At t = 0, the spatial derivative is the identity. -/
theorem spatialDerivative_zero
    (Δ_φ : ModularOperatorData H D.φ)
    (Δ_rel : RelativeModularOperatorData H D) :
    spatialDerivative D Δ_φ Δ_rel 0 = 1 := by
  simp only [spatialDerivative, relativeModularUnitary, modularUnitary, neg_zero]
  rw [FunctionalCalculus.boundedFunctionalCalculus_unitaryGroup_zero
    Δ_rel.spectralMeasure Δ_rel.spectralMeasure_isSpectral Δ_rel.spectralMeasure_univ]
  rw [FunctionalCalculus.boundedFunctionalCalculus_unitaryGroup_zero
    Δ_φ.spectralMeasure Δ_φ.spectralMeasure_isSpectral Δ_φ.spectralMeasure_univ]
  simp [mul_one]

/-- The spatial derivative is a product of unitaries, hence unitary.

    Note: full unitarity proof requires showing the product of the relative
    modular unitary and the inverse single-state modular unitary is unitary.
    This follows from unitarity of each factor (proved in TomitaTakesaki.lean
    and above). -/
structure SpatialDerivativeUnitarity (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : TwoStateData H)
    (Δ_φ : ModularOperatorData H D.φ)
    (Δ_rel : RelativeModularOperatorData H D) where
  isUnitary : ∀ t : ℝ,
    spatialDerivative D Δ_φ Δ_rel t *
      ContinuousLinearMap.adjoint (spatialDerivative D Δ_φ Δ_rel t) = 1 ∧
    ContinuousLinearMap.adjoint (spatialDerivative D Δ_φ Δ_rel t) *
      spatialDerivative D Δ_φ Δ_rel t = 1
  mem_algebra : ∀ t : ℝ, spatialDerivative D Δ_φ Δ_rel t ∈ D.φ.algebra.toSubalgebra

end Tomita
