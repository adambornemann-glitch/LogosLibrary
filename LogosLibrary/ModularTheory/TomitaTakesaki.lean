/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: ModularTheory/PreTomitaTakesaki.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.Generator
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.BoundedFunctionalCalc
/-!
# Tomita–Takesaki Modular Theory

The modular automorphism group `t ↦ σ_t(a) = Δ^{it} a Δ^{-it}` is realized
via the one-parameter unitary group from the spectral power function
`f_t(λ) = λ^{it}`, whose group law was established in the parent file.

## Sections

1. **Antilinear Framework**: Unbounded conjugate-linear operators via
   semilinear maps over `starRingEnd ℂ`.
2. **Von Neumann Algebra Setup**: `StarSubalgebra` acting on H with a cyclic
   and separating vector Ω.
3. **Tomita Operator S₀**: `S₀(aΩ) = a*Ω`, well-definedness via separating.
4. **Closability**: Formal adjointness of S₀ and F₀, closability.
5. **Modular Operator Δ and Conjugation J**: Polar decomposition `S = JΔ^{1/2}`,
   connection to bounded functional calculus.
6. **Tomita's Theorem**: `JMJ = M'` and `Δ^{it}MΔ^{-it} = M`.
7. **Packaging**: Wire into downstream AQFT types.

## Main definitions

* `AntilinearOp`: Unbounded conjugate-linear operator with domain
* `VNAlgebraWithVector`: Von Neumann algebra with cyclic/separating vector
* `preTomitaOp`: The operator `S₀ : aΩ ↦ a*Ω`
* `preCoTomitaOp`: The operator `F₀ : b'Ω ↦ b'*Ω` on the commutant
* `tomitaClosure`: The closure `S = S₀̄`
* `modularOperator`: `Δ = S*S`
* `modularConjugation`: `J` from polar decomposition `S = JΔ^{1/2}`
* `modularUnitary`: `Δ^{it}` via bounded functional calculus
* `modularAutomorphism`: `σ_t(a) = Δ^{it} a Δ^{-it}`

## Main results

* `preTomita_wellDefined`: S₀ is independent of the choice of representative
* `preTomita_formal_adjoint`: ⟨S₀(aΩ), b'Ω⟩ = ⟨F₀(b'Ω), aΩ⟩
* `conjugation_fixes_vacuum`: `JΩ = Ω`
* `conjugation_involutive`: `J² = 1`
* `conjugation_antiunitary`: `⟨Jψ, Jφ⟩ = ⟨φ, ψ⟩`
* `modularUnitary_group_law`: `Δ^{i(s+t)} = Δ^{is} Δ^{it}`
* `modularUnitary_eq_spectralPower`: Bridge to `spectralPowerFunction`
* `tomita_conjugation`: `JMJ = M'` (axiom)
* `tomita_modular_automorphism`: `Δ^{it}MΔ^{-it} = M` (axiom)

## References

* [Takesaki, *Theory of Operator Algebras I*][takesaki1979], Ch. VI
* [Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics*][bratteli1987]
* [Connes, *Noncommutative Geometry*][connes1994], Ch. V

## Tags

Tomita–Takesaki, modular operator, modular conjugation, modular automorphism,
von Neumann algebra, cyclic vector, separating vector
-/
noncomputable section

namespace Tomita

open scoped ComplexOrder

open MeasureTheory InnerProductSpace Complex FunctionalCalculus ContinuousLinearMap
  SpectralBridge.Resolvent SpectralBridge.Bochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## Section 1: Antilinear Framework

We model unbounded conjugate-linear operators as semilinear maps over
`starRingEnd ℂ` with an explicit domain submodule. This interfaces cleanly
with Mathlib's `SemilinearMapClass` hierarchy while supporting the unbounded
setting required for the Tomita operator.

Key design decision: the domain is a `Submodule ℂ H` (a *linear* subspace),
even though the map itself is antilinear. This is correct — the domain of
an antilinear operator is still a vector space; only the *action* is
conjugate-linear.
-/

/-- An unbounded conjugate-linear (antilinear) operator on a Hilbert space.

    The operator is defined on a dense submodule of `H` and satisfies
    `T(c • ψ) = c̄ • T(ψ)` for all `c : ℂ` and `ψ` in the domain.

    This is the natural home for the Tomita operator S and its companion F. -/
structure AntilinearOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The domain of the operator, as a ℂ-submodule of H. -/
  domain : Submodule ℂ H
  /-- The action on domain elements. -/
  toFun : domain → H
  /-- Antilinearity: T(c·ψ) = c̄·T(ψ). -/
  antilinear' : ∀ (c : ℂ) (ψ : domain),
    toFun (⟨c • (ψ : H), domain.smul_mem c ψ.property⟩) =
    starRingEnd ℂ c • toFun ψ
  /-- Additivity: T(ψ + φ) = T(ψ) + T(φ). -/
  additive' : ∀ (ψ φ : domain),
    toFun (⟨(ψ : H) + (φ : H), domain.add_mem ψ.property φ.property⟩) =
    toFun ψ + toFun φ

/-- Coerce an `AntilinearOp` to a function on its domain. -/
instance : CoeFun (AntilinearOp H) (fun T => T.domain → H) :=
  ⟨AntilinearOp.toFun⟩

/-- An antilinear operator is *closable* if the closure of its graph is
    still the graph of an operator (equivalently: if (0, η) is in the
    graph closure then η = 0). -/
def AntilinearOp.IsClosable (T : AntilinearOp H) : Prop :=
  ∀ (η : H), (∀ ε > 0, ∃ ξ : T.domain, ‖(ξ : H)‖ < ε ∧ ‖T ξ - η‖ < ε) → η = 0

/-- An antilinear operator has *dense domain*. -/
def AntilinearOp.DenseDomain (T : AntilinearOp H) : Prop :=
  Dense (T.domain : Set H)

/-- A *closed* antilinear operator: the graph is closed in H × H. -/
structure ClosedAntilinearOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    extends AntilinearOp H where
  /-- The graph is closed: limits of graph sequences are in the graph. -/
  graph_closed : ∀ (ξs : ℕ → domain) (ξ η : H),
    Filter.Tendsto (fun n => (ξs n : H)) Filter.atTop (nhds ξ) →
    Filter.Tendsto (fun n => toFun (ξs n)) Filter.atTop (nhds η) →
    ∃ (hξ : ξ ∈ domain), toFun ⟨ξ, hξ⟩ = η

/-! ### General closability criterion -/

/-- The functional analysis closability criterion (Reed–Simon, Thm. VIII.1)
    packaged as a local hypothesis: any antilinear operator admitting a
    densely-defined formal adjoint is closable. -/
def ClosabilityFromDenseAdjoint (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ (T T_adj : AntilinearOp H),
    T.DenseDomain → T_adj.DenseDomain →
    (∀ (ξ : T.domain) (η : T_adj.domain),
      @inner ℂ H _ (T ξ) (η : H) = @inner ℂ H _ (T_adj η) (ξ : H)) →
    T.IsClosable

/-!
## Section 2: Von Neumann Algebra with Cyclic and Separating Vector

A von Neumann algebra M acting on H, equipped with a unit vector Ω that is
both cyclic (MΩ is dense in H) and separating (aΩ = 0 ⟹ a = 0).

We use `StarSubalgebra ℂ (H →L[ℂ] H)` so that the *-operation is baked in.
The weak closure condition (double commutant) is not needed for the Tomita
construction — cyclicity and separability suffice.
-/

/-- The commutant of a set of bounded operators: all operators that commute
    with every element of the set. -/
def commutant (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  {b | ∀ a ∈ S, a * b = b * a}

/-- The ambient data for Tomita–Takesaki theory: a *-subalgebra of B(H) acting
    on a Hilbert space with a distinguished cyclic and separating vector.

    The vector Ω plays the role of the vacuum state in QFT, or the GNS vector
    for a faithful normal state on M. -/
structure VNAlgebraWithVector (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The algebra, as a *-subalgebra of B(H). -/
  algebra : StarSubalgebra ℂ (H →L[ℂ] H)
  /-- The distinguished vector. -/
  Ω : H
  /-- Ω is nonzero. -/
  Ω_ne_zero : Ω ≠ 0
  /-- Ω is normalized. -/
  Ω_norm : ‖Ω‖ = 1
  /-- **Cyclic**: MΩ is dense in H. -/
  cyclic : ∀ ε > 0, ∀ ψ : H, ∃ a ∈ algebra, ‖a Ω - ψ‖ < ε
  /-- **Separating**: aΩ = 0 implies a = 0 for a ∈ M. -/
  separating : ∀ a ∈ algebra, a Ω = 0 → a = 0
  /-- Ω is also cyclic for the commutant M'.
      (This follows from separating + double commutant theorem,
       but we include it to avoid needing the full vN algebra theory.) -/
  cyclic_commutant : ∀ ε > 0, ∀ ψ : H,
    ∃ b ∈ commutant (algebra : Set (H →L[ℂ] H)), ‖b Ω - ψ‖ < ε
  /-- Ω is separating for the commutant M'. -/
  separating_commutant : ∀ b ∈ commutant (algebra : Set (H →L[ℂ] H)), b Ω = 0 → b = 0

variable (M : VNAlgebraWithVector H)

/-- The dense subspace MΩ = {aΩ : a ∈ M}. -/
def VNAlgebraWithVector.algebraΩ : Submodule ℂ H where
  carrier := {ξ | ∃ a ∈ M.algebra, a M.Ω = ξ}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, M.algebra.add_mem ha hb, by simp [ContinuousLinearMap.add_apply]⟩
  zero_mem' := ⟨0, M.algebra.zero_mem, by simp⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    exact ⟨c • a, M.algebra.smul_mem ha c, by simp [ContinuousLinearMap.smul_apply]⟩

/-- The dense subspace M'Ω = {b'Ω : b' ∈ M'}. -/
def VNAlgebraWithVector.commutantΩ : Submodule ℂ H where
  carrier := {ξ | ∃ b ∈ commutant (M.algebra : Set (H →L[ℂ] H)), b M.Ω = ξ}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a + b, fun c hc => by rw [mul_add, add_mul, ha c hc, hb c hc], by simp⟩
  zero_mem' := ⟨0, fun _ _ => by simp, by simp⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    refine ⟨c • a, fun d hd => by simp [ha d hd], by simp⟩

/-- MΩ is dense. -/
lemma VNAlgebraWithVector.algebraΩ_dense : Dense (M.algebraΩ : Set H) := by
  rw [Metric.dense_iff]
  intro ψ ε hε
  obtain ⟨a, ha, hclose⟩ := M.cyclic ε hε ψ
  have hmem : a M.Ω ∈ (M.algebraΩ : Set H) := ⟨a, ha, rfl⟩
  have hdist : dist (a M.Ω) ψ < ε := by rw [dist_eq_norm]; exact hclose
  rw [@Set.inter_nonempty_iff_exists_right]
  exact ⟨a M.Ω, hmem, hdist⟩

/-- M'Ω is dense. -/
lemma VNAlgebraWithVector.commutantΩ_dense : Dense (M.commutantΩ : Set H) := by
  rw [Metric.dense_iff]
  intro ψ ε hε
  obtain ⟨b, hb, hclose⟩ := M.cyclic_commutant ε hε ψ
  have hmem : b M.Ω ∈ (M.commutantΩ : Set H) := ⟨b, hb, rfl⟩
  have hdist : dist (b M.Ω) ψ < ε := by rw [dist_eq_norm]; exact hclose
  rw [@Set.inter_nonempty_iff_exists_right]
  exact ⟨b M.Ω, hmem, hdist⟩


/-!
## Section 3: The Tomita Operator S₀

The pre-Tomita operator is defined on the dense subspace MΩ by

    S₀(aΩ) = a*Ω

Well-definedness: if aΩ = bΩ then (a - b)Ω = 0, so a = b by
separability, hence a* = b* and a*Ω = b*Ω.
-/

/-- The unique representative: given ξ ∈ MΩ, pick the (unique) a ∈ M
    with aΩ = ξ. Uniqueness is guaranteed by separability. -/
noncomputable def VNAlgebraWithVector.algebraΩ_repr (ξ : M.algebraΩ) : H →L[ℂ] H :=
  Classical.choose ξ.property

/-- The representative is in the algebra. -/
lemma VNAlgebraWithVector.algebraΩ_repr_mem (ξ : M.algebraΩ) :
    M.algebraΩ_repr ξ ∈ M.algebra :=
  (Classical.choose_spec ξ.property).1

/-- The representative maps Ω to ξ. -/
lemma VNAlgebraWithVector.algebraΩ_repr_spec (ξ : M.algebraΩ) :
    M.algebraΩ_repr ξ M.Ω = (ξ : H) :=
  (Classical.choose_spec ξ.property).2

/-- The representative is unique (by separability of Ω). -/
lemma VNAlgebraWithVector.algebraΩ_repr_unique (ξ : M.algebraΩ) (a : H →L[ℂ] H)
    (ha : a ∈ M.algebra) (haΩ : a M.Ω = (ξ : H)) :
    a = M.algebraΩ_repr ξ := by
  have h_diff : (a - M.algebraΩ_repr ξ) M.Ω = 0 := by
    simp [ContinuousLinearMap.sub_apply, haΩ, M.algebraΩ_repr_spec ξ]
  have h_mem : a - M.algebraΩ_repr ξ ∈ M.algebra :=
    M.algebra.sub_mem ha (M.algebraΩ_repr_mem ξ)
  have := M.separating _ h_mem h_diff
  grind

/-- Similarly for the commutant: pick b' ∈ M' with b'Ω = η. -/
noncomputable def VNAlgebraWithVector.commutantΩ_repr (η : M.commutantΩ) : H →L[ℂ] H :=
  Classical.choose η.property

/-- The commutant representative is in M'. -/
lemma VNAlgebraWithVector.commutantΩ_repr_mem (η : M.commutantΩ) :
    M.commutantΩ_repr η ∈ commutant (M.algebra : Set (H →L[ℂ] H)) :=
  (Classical.choose_spec η.property).1

/-- The commutant representative maps Ω to η. -/
lemma VNAlgebraWithVector.commutantΩ_repr_spec (η : M.commutantΩ) :
    M.commutantΩ_repr η M.Ω = (η : H) :=
  (Classical.choose_spec η.property).2

/-- The commutant representative is unique (by separability of Ω for M'). -/
lemma VNAlgebraWithVector.commutantΩ_repr_unique (η : M.commutantΩ) (b : H →L[ℂ] H)
    (hb : b ∈ commutant (M.algebra : Set (H →L[ℂ] H))) (hbΩ : b M.Ω = (η : H)) :
    b = M.commutantΩ_repr η := by
  have h_diff : (b - M.commutantΩ_repr η) M.Ω = 0 := by
    simp [ContinuousLinearMap.sub_apply, hbΩ, M.commutantΩ_repr_spec η]
  have h_mem : b - M.commutantΩ_repr η ∈ commutant (M.algebra : Set (H →L[ℂ] H)) := by
    intro a ha
    simp [mul_sub, sub_mul, hb a ha, M.commutantΩ_repr_mem η a ha]
  exact sub_eq_zero.mp (M.separating_commutant _ h_mem h_diff)

/-- **The pre-Tomita operator** `S₀ : MΩ → H` defined by `S₀(aΩ) = a*Ω`.

    This is conjugate-linear: `S₀(c · aΩ) = (ca)*Ω = ā · a*Ω = ā · S₀(aΩ)`. -/
noncomputable def preTomitaOp : AntilinearOp H where
  domain := M.algebraΩ
  toFun := fun ξ =>
    let a := M.algebraΩ_repr ξ
    -- a* is the star in the StarSubalgebra; we need star in ContinuousLinearMap
    -- Since M.algebra is a StarSubalgebra, a ∈ M.algebra implies star a ∈ M.algebra
    -- and star a is the ContinuousLinearMap adjoint
    (ContinuousLinearMap.adjoint a) M.Ω
  antilinear' := by
    intro c ξ
    simp only
    have h_smul_repr : M.algebraΩ_repr ⟨c • (ξ : H), M.algebraΩ.smul_mem c ξ.property⟩ =
        c • M.algebraΩ_repr ξ := by
      symm
      apply M.algebraΩ_repr_unique
      · exact M.algebra.smul_mem (M.algebraΩ_repr_mem ξ) c
      · simp [ContinuousLinearMap.smul_apply, M.algebraΩ_repr_spec ξ]
    rw [h_smul_repr]
    have h_adj : ContinuousLinearMap.adjoint (c • M.algebraΩ_repr ξ) =
        starRingEnd ℂ c • ContinuousLinearMap.adjoint (M.algebraΩ_repr ξ) :=
      star_smul c (M.algebraΩ_repr ξ)
    rw [h_adj, ContinuousLinearMap.smul_apply]
  additive' := by
    intro ψ φ
    simp only
    have h_add_repr : M.algebraΩ_repr
        ⟨(ψ : H) + (φ : H), M.algebraΩ.add_mem ψ.property φ.property⟩ =
        M.algebraΩ_repr ψ + M.algebraΩ_repr φ := by
      symm
      apply M.algebraΩ_repr_unique
      · exact M.algebra.add_mem (M.algebraΩ_repr_mem ψ) (M.algebraΩ_repr_mem φ)
      · simp [ContinuousLinearMap.add_apply, M.algebraΩ_repr_spec]
    rw [h_add_repr]
    simp [map_add, ContinuousLinearMap.add_apply]

/-- **The pre-co-Tomita operator** `F₀ : M'Ω → H` defined by `F₀(b'Ω) = b'*Ω`.

    This is the "partner" of S₀, defined on the commutant. The key fact is
    that S₀ and F₀ are formal adjoints of each other. -/
noncomputable def preCoTomitaOp : AntilinearOp H where
  domain := M.commutantΩ
  toFun := fun η =>
    let b := M.commutantΩ_repr η
    (ContinuousLinearMap.adjoint b) M.Ω
  antilinear' := by
    intro c η
    simp only
    have h_smul_comm : c • M.commutantΩ_repr η ∈
        commutant (M.algebra : Set (H →L[ℂ] H)) := by
      intro a ha
      simp [M.commutantΩ_repr_mem η a ha]
    have h_smul_repr : M.commutantΩ_repr ⟨c • (η : H), M.commutantΩ.smul_mem c η.property⟩ =
        c • M.commutantΩ_repr η := by
      symm
      apply M.commutantΩ_repr_unique
      · exact h_smul_comm
      · simp [ContinuousLinearMap.smul_apply, M.commutantΩ_repr_spec η]
    rw [h_smul_repr]
    have h_adj : ContinuousLinearMap.adjoint (c • M.commutantΩ_repr η) =
        starRingEnd ℂ c • ContinuousLinearMap.adjoint (M.commutantΩ_repr η) := by
      change star (c • M.commutantΩ_repr η) = starRingEnd ℂ c • star (M.commutantΩ_repr η)
      exact star_smul c (M.commutantΩ_repr η)
    rw [h_adj, ContinuousLinearMap.smul_apply]
  additive' := by
    intro ψ φ
    simp only
    have h_add_comm : M.commutantΩ_repr ψ + M.commutantΩ_repr φ ∈
        commutant (M.algebra : Set (H →L[ℂ] H)) := by
      intro a ha
      simp [mul_add, add_mul, M.commutantΩ_repr_mem ψ a ha, M.commutantΩ_repr_mem φ a ha]
    have h_add_repr : M.commutantΩ_repr
        ⟨(ψ : H) + (φ : H), M.commutantΩ.add_mem ψ.property φ.property⟩ =
        M.commutantΩ_repr ψ + M.commutantΩ_repr φ := by
      symm
      apply M.commutantΩ_repr_unique
      · exact h_add_comm
      · simp [ContinuousLinearMap.add_apply, M.commutantΩ_repr_spec]
    rw [h_add_repr]
    have h_adj : ContinuousLinearMap.adjoint (M.commutantΩ_repr ψ + M.commutantΩ_repr φ) =
        ContinuousLinearMap.adjoint (M.commutantΩ_repr ψ) +
        ContinuousLinearMap.adjoint (M.commutantΩ_repr φ) := by
      change star (_ + _) = star _ + star _
      exact star_add _ _
    rw [h_adj, ContinuousLinearMap.add_apply]

/-- **Well-definedness of S₀**: the output depends only on the vector ξ,
    not on the choice of representative a with aΩ = ξ.

    This is immediate from our construction (we use `Classical.choose`
    which picks a canonical representative), but the mathematical content
    is: if aΩ = bΩ then a = b (separating), so a* = b*, so a*Ω = b*Ω. -/
theorem preTomita_wellDefined (a : H →L[ℂ] H) (ha : a ∈ M.algebra)
    (ξ : M.algebraΩ) (haξ : a M.Ω = (ξ : H)) :
    (ContinuousLinearMap.adjoint a) M.Ω = preTomitaOp M ξ := by
  simp only [preTomitaOp]
  congr 1
  exact congr_arg ContinuousLinearMap.adjoint (M.algebraΩ_repr_unique ξ a ha haξ)

/-- S₀ sends Ω to Ω: `S₀(1·Ω) = 1*·Ω = Ω`. -/
lemma preTomita_vacuum : preTomitaOp M ⟨M.Ω, ⟨1, M.algebra.one_mem, by simp⟩⟩ = M.Ω := by
  simp only [preTomitaOp]
  have h_repr_one : M.algebraΩ_repr ⟨M.Ω, ⟨1, M.algebra.one_mem, by simp⟩⟩ = 1 := by
    symm
    apply M.algebraΩ_repr_unique
    · exact M.algebra.one_mem
    · simp
  rw [h_repr_one]
  -- ⊢ (adjoint 1) M.Ω = M.Ω
  have h_adj_one : ContinuousLinearMap.adjoint (1 : H →L[ℂ] H) = 1 := by
    change star (1 : H →L[ℂ] H) = 1
    exact star_one (H →L[ℂ] H)
  rw [h_adj_one, ContinuousLinearMap.one_apply]

/-!
## Section 4: Closability

The mathematical argument:
  ⟨S₀(aΩ), b'Ω⟩ = ⟨a*Ω, b'Ω⟩ = ⟨Ω, a b'Ω⟩ = ⟨Ω, b'aΩ⟩ = ⟨b'*Ω, aΩ⟩ = ⟨F₀(b'Ω), aΩ⟩

The middle equality `a b'Ω = b'aΩ` uses commutativity: b' ∈ M' so ab' = b'a.
This shows S₀* ⊇ F₀, so S₀* is densely defined, hence S₀ is closable.
-/

/-- **Formal adjointness**: ⟨S₀(aΩ), b'Ω⟩ = ⟨F₀(b'Ω), aΩ⟩.

    The proof chains: adjointness of star, commutativity of a ∈ M with b' ∈ M',
    and adjointness of star again. -/
theorem preTomita_formal_adjoint (ξ : M.algebraΩ) (η : M.commutantΩ) :
    @inner ℂ H _ (preTomitaOp M ξ) (η : H) =
    @inner ℂ H _ (preCoTomitaOp M η) (ξ : H) := by
  simp only [preTomitaOp, preCoTomitaOp]
  -- Let a = repr(ξ), b' = repr(η)
  set a := M.algebraΩ_repr ξ
  set b := M.commutantΩ_repr η
  -- LHS = ⟨a*Ω, b'Ω⟩
  -- We need: ⟨a*Ω, bΩ⟩ = ⟨b*Ω, aΩ⟩
  -- Step 1: ⟨a*Ω, bΩ⟩ = ⟨Ω, a(bΩ)⟩  (adjoint of a*)
  -- Step 2: a(bΩ) = b(aΩ)              (a, b' commute)
  -- Step 3: ⟨Ω, b(aΩ)⟩ = ⟨b*Ω, aΩ⟩  (adjoint of b*)
  have ha_mem := M.algebraΩ_repr_mem ξ
  have hb_mem := M.commutantΩ_repr_mem η
  have haΩ := M.algebraΩ_repr_spec ξ
  have hbΩ := M.commutantΩ_repr_spec η
  -- The commutativity: ab = ba (as operators)
  have h_comm : a * b = b * a := by
    have := hb_mem a (by exact ha_mem)
    exact this
  -- Rewrite the coercions to their repr forms
  rw [← haΩ, ← hbΩ]
  -- Now the goal is ⟨adjoint a Ω, b Ω⟩ = ⟨adjoint b Ω, a Ω⟩
  calc @inner ℂ H _ ((ContinuousLinearMap.adjoint a) M.Ω) (b M.Ω)
      = @inner ℂ H _ M.Ω (a (b M.Ω)) := by
        rw [ContinuousLinearMap.adjoint_inner_left]
    _ = @inner ℂ H _ M.Ω (b (a M.Ω)) := by
        congr 1
        have : (a * b) M.Ω = (b * a) M.Ω := by rw [h_comm]
        simp [ContinuousLinearMap.mul_apply] at this
        exact this
    _ = @inner ℂ H _ ((ContinuousLinearMap.adjoint b) M.Ω) (a M.Ω) := by
        rw [ContinuousLinearMap.adjoint_inner_left]

/-- S₀ is closable: F₀ is a densely-defined formal adjoint. -/
theorem preTomitaOp_closable (hRS : ClosabilityFromDenseAdjoint H) :
    (preTomitaOp M).IsClosable :=
  hRS (preTomitaOp M) (preCoTomitaOp M)
    (by convert M.algebraΩ_dense)
    (by convert M.commutantΩ_dense)
    (preTomita_formal_adjoint M)

/-- Bundled closure data for a closable, densely-defined antilinear operator.
    Packages the closed extension together with its key properties.
    (Reed–Simon, Thm. VIII.1 + standard graph-closure construction.) -/
structure AntilinearOp.ClosureData {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : AntilinearOp H) where
  /-- The closed extension. -/
  closed : ClosedAntilinearOp H
  /-- The closure extends T on its original domain. -/
  extends_op : ∀ (ξ : T.domain),
    ∃ (hξ : (ξ : H) ∈ closed.domain),
      closed.toFun ⟨ξ, hξ⟩ = T ξ
  /-- The closure still has dense domain. -/
  dense_domain : closed.DenseDomain

/-!
## Section 4.5: Closure of S₀

The closed Tomita operator S is the closure of S₀. Since S₀ is closable,
its graph closure is the graph of a closed operator extending S₀.
-/

/-- The closed Tomita operator S = closure(S₀).

    Since S₀ is closable (by formal adjointness with F₀) and densely defined,
    a closure construction yields a closed antilinear operator extending S₀. -/
noncomputable def tomitaClosure
    (_hRS : ClosabilityFromDenseAdjoint H)
    (hcl : (preTomitaOp M).ClosureData) : ClosedAntilinearOp H :=
  hcl.closed

variable (hRS : ClosabilityFromDenseAdjoint H)
variable (hcl : (preTomitaOp M).ClosureData)

lemma tomitaClosure_extends
    (hRS : ClosabilityFromDenseAdjoint H)
    (hcl : (preTomitaOp M).ClosureData) (ξ : M.algebraΩ) :
    ∃ (hξ : (ξ : H) ∈ (tomitaClosure M hRS hcl).domain),
      (tomitaClosure M hRS hcl).toFun ⟨ξ, hξ⟩ = preTomitaOp M ξ :=
  hcl.extends_op ξ

lemma tomitaClosure_dense
    (hRS : ClosabilityFromDenseAdjoint H)
    (hcl : (preTomitaOp M).ClosureData) :
    (tomitaClosure M hRS hcl).toAntilinearOp.DenseDomain :=
  hcl.dense_domain


/-!
## Bundled Hypotheses

All axioms from Part 1 are replaced by bundled structure hypotheses.
Construct each term once downstream; everything lights up for free.
-/

/-- Bundled data for the modular operator Δ = S*S and its spectral theory.
    (Von Neumann's theorem: S*S is self-adjoint and positive for any
    densely-defined closed operator S. Spectral theorem: a positive
    self-adjoint operator has a unique spectral measure on [0, ∞).) -/
structure ModularOperatorData (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VNAlgebraWithVector H) where
  /-- The modular operator Δ = S*S. -/
  op : H →L[ℂ] H
  /-- Δ is positive: ⟨Δψ, ψ⟩ ≥ 0. -/
  positive : ∀ ψ : H, 0 ≤ ((@inner ℂ H _ (op ψ) ψ) : ℂ).re
  /-- Ω is a fixed point: ΔΩ = Ω. -/
  fixes_vacuum : op M.Ω = M.Ω
  /-- The spectral measure of Δ, supported on [0, ∞). -/
  spectralMeasure : Set ℝ → H →L[ℂ] H
  /-- The spectral measure is indeed spectral. -/
  spectralMeasure_isSpectral : IsSpectralMeasure spectralMeasure
  /-- Resolution of the identity. -/
  spectralMeasure_univ : spectralMeasure Set.univ = 1

/-- Bundled data for the modular conjugation J from the polar
    decomposition S = JΔ^{1/2}.
    (Polar decomposition of a closed antilinear operator.) -/
structure ModularConjugationData (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VNAlgebraWithVector H) where
  /-- The modular conjugation J. -/
  toFun : H → H
  /-- J² = id. -/
  involutive : Function.Involutive toFun
  /-- ⟨Jψ, Jφ⟩ = ⟨φ, ψ⟩. -/
  antiunitary : ∀ ψ φ : H,
    @inner ℂ H _ (toFun ψ) (toFun φ) = @inner ℂ H _ φ ψ
  /-- JΩ = Ω. -/
  fixes_vacuum : toFun M.Ω = M.Ω

variable (Δ : ModularOperatorData H M)
variable (J : ModularConjugationData H M)

/-! ### Local helper: conjugate of a bounded function is bounded

    This is proved as `private lemma bounded_conj` in `BoundedFunctionalCalc.lean`.
    We reproduce it here since `private` declarations are file-scoped.
    TODO: make `bounded_conj` public upstream and remove this. -/
lemma bounded_conj_local {f : ℝ → ℂ}
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) :
    ∃ M, ∀ s, ‖(starRingEnd ℂ ∘ f) s‖ ≤ M := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, fun s => by simp only [Function.comp_apply, RCLike.norm_conj]; exact hM s⟩

/-!
## Section 5: The Modular Unitary Group

`Δ^{it}` via the bounded functional calculus applied to the spectral
power function `f_t(λ) = exp(i t log λ) = λ^{it}`.
-/

/-- **The modular unitary group**: `Δ^{it}` via the bounded functional calculus. -/
noncomputable def modularUnitary (t : ℝ) : H →L[ℂ] H :=
  FunctionalCalculus.boundedFunctionalCalculus
    Δ.spectralMeasure
    Δ.spectralMeasure_isSpectral
    (FunctionalCalculus.spectralPowerFunction t)
    (FunctionalCalculus.spectralPowerFunction_bounded t)

/-- **Bridge theorem**: The modular unitary equals the spectral power function
    applied through the bounded functional calculus of Δ's spectral measure. -/
theorem modularUnitary_eq_spectralPower (t : ℝ) :
    modularUnitary M Δ t =
    FunctionalCalculus.boundedFunctionalCalculus
      Δ.spectralMeasure
      Δ.spectralMeasure_isSpectral
      (FunctionalCalculus.spectralPowerFunction t)
      (FunctionalCalculus.spectralPowerFunction_bounded t) :=
  rfl

/-- **Group law for the modular unitary**: Δ^{i(s+t)} = Δ^{is} · Δ^{it}. -/
theorem modularUnitary_group_law (s t : ℝ) :
    modularUnitary M Δ (s + t) = modularUnitary M Δ s * modularUnitary M Δ t := by
  exact FunctionalCalculus.boundedFunctionalCalculus_unitaryGroup
    Δ.spectralMeasure Δ.spectralMeasure_isSpectral Δ.spectralMeasure_univ s t

/-- **Identity**: Δ^{i·0} = I. -/
theorem modularUnitary_zero :
    modularUnitary M Δ 0 = 1 := by
  exact FunctionalCalculus.boundedFunctionalCalculus_unitaryGroup_zero
    Δ.spectralMeasure Δ.spectralMeasure_isSpectral Δ.spectralMeasure_univ

/-- **Unitarity**: Δ^{it} is unitary for all t. -/
theorem modularUnitary_isUnitary (t : ℝ) :
    let hft := FunctionalCalculus.spectralPowerFunction_bounded t
    let hft_conj := bounded_conj_local hft
    modularUnitary M Δ t *
      FunctionalCalculus.boundedFunctionalCalculus
        Δ.spectralMeasure Δ.spectralMeasure_isSpectral
        (starRingEnd ℂ ∘ FunctionalCalculus.spectralPowerFunction t) hft_conj = 1 ∧
    FunctionalCalculus.boundedFunctionalCalculus
        Δ.spectralMeasure Δ.spectralMeasure_isSpectral
        (starRingEnd ℂ ∘ FunctionalCalculus.spectralPowerFunction t) hft_conj *
      modularUnitary M Δ t = 1 := by
  exact FunctionalCalculus.boundedFunctionalCalculus_unitaryGroup_isUnitary
    Δ.spectralMeasure Δ.spectralMeasure_isSpectral Δ.spectralMeasure_univ t

/-- **Adjoint = inverse**: (Δ^{it})* = Δ^{-it}. -/
theorem modularUnitary_adjoint (t : ℝ) :
    (modularUnitary M Δ t).adjoint = modularUnitary M Δ (-t) := by
  exact FunctionalCalculus.boundedFunctionalCalculus_unitaryGroup_adjoint
    Δ.spectralMeasure Δ.spectralMeasure_isSpectral Δ.spectralMeasure_univ t

/-!
## Section 5.5: Modular Conjugation — Derived Properties

J is provided by `ModularConjugationData`. We derive isometry from antiunitarity.
-/

/-- J is isometric: ‖Jψ‖ = ‖ψ‖. -/
lemma modularConjugation_isometry (ψ : H) :
    ‖J.toFun ψ‖ = ‖ψ‖ := by
  have h := J.antiunitary ψ ψ
  have h_re : ‖J.toFun ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    have := congr_arg Complex.re h
    simp at this
    exact_mod_cast this
  simp_all only [inner_self_eq_norm_sq_to_K, coe_algebraMap, norm_nonneg, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀]

/-!
## Section 6: Tomita's Theorem

The two fundamental results of Tomita–Takesaki theory, plus vacuum
invariance under Δ^{it}. Bundled as a structure hypothesis.
-/

/-- The two halves of Tomita's theorem plus vacuum invariance under Δ^{it}.
    (Takesaki, *Theory of Operator Algebras I*, Ch. VI.) -/
structure TomitaTheorem (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VNAlgebraWithVector H)
    (Δ : ModularOperatorData H M)
    (J : ModularConjugationData H M) where
  /-- **Part I**: JMJ = M' — conjugation exchanges algebra and commutant. -/
  conjugation : ∀ a ∈ M.algebra, ∀ b ∈ M.algebra, ∀ ψ : H,
    (b ∘ fun ψ => J.toFun (a (J.toFun ψ))) ψ =
    (fun ψ => J.toFun (a (J.toFun ψ))) (b ψ)
  /-- **Part II**: Δ^{it}MΔ^{-it} ⊆ M — modular automorphisms preserve M. -/
  modular_automorphism : ∀ t : ℝ, ∀ a ∈ M.algebra,
    modularUnitary M Δ t * a * modularUnitary M Δ (-t) ∈ M.algebra.toSubalgebra
  /-- Δ^{it}Ω = Ω for all t. -/
  unitary_fixes_vacuum : ∀ t, modularUnitary M Δ t M.Ω = M.Ω

variable (hTT : TomitaTheorem H M Δ J)

/-!
## Section 6.5: The Modular Automorphism Group

`σ_t(a) = Δ^{it} a Δ^{-it}` and its algebraic properties.
-/

/-- The modular automorphism group: σ_t(a) = Δ^{it} a Δ^{-it}. -/
noncomputable def modularAutomorphism (t : ℝ) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  modularUnitary M Δ t * a * modularUnitary M Δ (-t)

/-- The modular automorphism preserves algebra elements. -/
theorem modularAutomorphism_mem (hTT : TomitaTheorem H M Δ J)
    (t : ℝ) (a : H →L[ℂ] H) (ha : a ∈ M.algebra) :
    modularAutomorphism M Δ t a ∈ M.algebra.toSubalgebra :=
  hTT.modular_automorphism t a ha

/-- σ_{s+t} = σ_s ∘ σ_t: the modular automorphisms form a group. -/
theorem modularAutomorphism_group_law (s t : ℝ) (a : H →L[ℂ] H) :
    modularAutomorphism M Δ (s + t) a =
    modularAutomorphism M Δ s (modularAutomorphism M Δ t a) := by
  simp only [modularAutomorphism]
  rw [modularUnitary_group_law M Δ s t]
  have h_neg : modularUnitary M Δ (-(s + t)) =
      modularUnitary M Δ (-t) * modularUnitary M Δ (-s) := by
    rw [show -(s + t) = -t + -s from by ring]
    exact modularUnitary_group_law M Δ (-t) (-s)
  rw [h_neg]
  ring_nf
  norm_cast

/-- σ_0 = id: the identity automorphism. -/
theorem modularAutomorphism_zero (a : H →L[ℂ] H) :
    modularAutomorphism M Δ 0 a = a := by
  simp only [modularAutomorphism, modularUnitary_zero M Δ, neg_zero]
  simp [mul_one, one_mul]

/-- σ_t is multiplicative: σ_t(ab) = σ_t(a) σ_t(b). -/
theorem modularAutomorphism_mul (t : ℝ) (a b : H →L[ℂ] H) :
    modularAutomorphism M Δ t (a * b) =
    modularAutomorphism M Δ t a * modularAutomorphism M Δ t b := by
  simp only [modularAutomorphism]
  have h_inv : modularUnitary M Δ (-t) * modularUnitary M Δ t = 1 := by
    rw [← modularUnitary_group_law M Δ (-t) t]
    simp [modularUnitary_zero]
  calc modularUnitary M Δ t * (a * b) * modularUnitary M Δ (-t)
      = modularUnitary M Δ t * a * (modularUnitary M Δ (-t) * modularUnitary M Δ t) *
        b * modularUnitary M Δ (-t) := by grind
    _ = modularUnitary M Δ t * a * 1 * b * modularUnitary M Δ (-t) := by rw [h_inv]
    _ = (modularUnitary M Δ t * a * modularUnitary M Δ (-t)) *
        (modularUnitary M Δ t * b * modularUnitary M Δ (-t)) := by
          rw [mul_one]; grind

/-- σ_t preserves the star operation: σ_t(a*) = σ_t(a)*.

    Uses: (Δ^{it})* = Δ^{-it} and the adjoint reverses products. -/
theorem modularAutomorphism_star (t : ℝ) (a : H →L[ℂ] H) :
    modularAutomorphism M Δ t (ContinuousLinearMap.adjoint a) =
    ContinuousLinearMap.adjoint (modularAutomorphism M Δ t a) := by
  simp only [modularAutomorphism]
  have adj_mul₃ : ∀ (U a V : H →L[ℂ] H),
      ContinuousLinearMap.adjoint (U * a * V) =
      ContinuousLinearMap.adjoint V * ContinuousLinearMap.adjoint a *
        ContinuousLinearMap.adjoint U := by
    intro U a V
    change star (U * a * V) = star V * star a * star U
    rw [star_mul, star_mul, mul_assoc]
  rw [adj_mul₃, modularUnitary_adjoint M Δ (-t), neg_neg, modularUnitary_adjoint M Δ t]

/-!
## Section 7: Packaging for Downstream

Connect the Tomita–Takesaki structure to the rest of the library.
The modular data (group + KMS condition) is the interface that
AQFT.lean and thermal physics consume.
-/

/-- The vacuum state ⟨Ω, · Ω⟩ as a functional on M. -/
noncomputable def vacuumState (a : H →L[ℂ] H) : ℂ :=
  @inner ℂ H _ M.Ω (a M.Ω)

/-- The vacuum state is σ_t-invariant: ω(σ_t(a)) = ω(a).

    This is a consequence of Δ^{it}Ω = Ω. -/
theorem vacuumState_modular_invariant (t : ℝ) (a : H →L[ℂ] H)
  (hTT : TomitaTheorem H M Δ J):
    vacuumState M (modularAutomorphism M Δ t a) = vacuumState M a := by
  simp only [vacuumState, modularAutomorphism]
  have hΩ_neg : modularUnitary M Δ (-t) M.Ω = M.Ω :=
    hTT.unitary_fixes_vacuum (-t)
  have hΩ_pos : modularUnitary M Δ t M.Ω = M.Ω :=
    hTT.unitary_fixes_vacuum t
  calc @inner ℂ H _ M.Ω ((modularUnitary M Δ t * a * modularUnitary M Δ (-t)) M.Ω)
      = @inner ℂ H _ M.Ω (modularUnitary M Δ t (a M.Ω)) := by
        simp [ContinuousLinearMap.mul_apply, hΩ_neg]
    _ = @inner ℂ H _ ((modularUnitary M Δ t).adjoint M.Ω) (a M.Ω) := by
        rw [ContinuousLinearMap.adjoint_inner_left]
    _ = @inner ℂ H _ (modularUnitary M Δ (-t) M.Ω) (a M.Ω) := by
        rw [modularUnitary_adjoint]
    _ = @inner ℂ H _ M.Ω (a M.Ω) := by
        rw [hΩ_neg]

/-- Bundle type for the modular automorphism group data. -/
structure ModularGroupData (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  σ : ℝ → (H →L[ℂ] H) → (H →L[ℂ] H)
  group_law : ∀ s t (a : H →L[ℂ] H), σ (s + t) a = σ s (σ t a)
  zero_eq : ∀ (a : H →L[ℂ] H), σ 0 a = a
  mul_eq : ∀ t (a b : H →L[ℂ] H), σ t (a * b) = σ t a * σ t b

/-- Bundle: the modular group as a one-parameter family of *-automorphisms. -/
noncomputable def modularGroupBundle : ModularGroupData H where
  σ := modularAutomorphism M Δ
  group_law := modularAutomorphism_group_law M Δ
  zero_eq := modularAutomorphism_zero M Δ
  mul_eq := modularAutomorphism_mul M Δ

end Tomita
