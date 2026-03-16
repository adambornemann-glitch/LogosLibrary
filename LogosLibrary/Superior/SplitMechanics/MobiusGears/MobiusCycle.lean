/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: ModularTheory/MobiusCycle.lean
-/
import LogosLibrary.QuantumMechanics.ModularTheory.Cocycle
import LogosLibrary.QuantumMechanics.ModularTheory.KMS.Condition
/-!
# The Möbius Structure of the KMS Strip and Cocycle

## The Idea

The KMS boundary condition identifies the lower and upper boundaries of the
strip with a **reversal of operator ordering**:

    F(t)      = ω(a · α_t(b))       (lower boundary)
    F(t + iβ) = ω(α_t(b) · a)       (upper boundary)

The map `(a, b) ↦ (b, a)` is an anti-automorphism — an orientation reversal.
This makes the KMS strip a **Möbius strip** when the algebra is non-commutative,
and a **cylinder** when commutative.

## Main Results

### Möbius Generator J (Section 1)
* `conjugateByJ`: The map `ψ ↦ J(a(Jψ))` implementing JaJ on vectors.
* `mobius_double_twist`: Two applications of J-conjugation return to the
  identity: J(J(a(J(Jψ)))) = a(ψ). This is π₁(Möbius) = ℤ₂.
* `mobius_twist_exchanges_algebras`: JaJ commutes with all of M,
  hence lives in M'. One traversal of the strip exchanges algebra and commutant.

### Fermionic KMS (Section 2)
* `FermionicKMSFunction`: Anti-periodic boundary condition F(t+iβ) = −ω(α_t(b)·a).
* `fermionic_kms_unit_vanishes`: For pair (1,a), anti-periodicity forces F ≡ 0.
* `no_fermionic_kms_ungraded`: There is no fermionic KMS state on an ungraded
  C*-algebra. **Fermions require ℤ₂-grading.** This is the topological content
  of spin-statistics: the Möbius strip with a sign twist has no nonzero
  global sections.

### Orientable Carrier Shaft (Section 3)
* `carrier_shaft_well_defined`: The canonical outer flow δ : ℝ → Out(M) is
  independent of which state (which Möbius gear) we use to compute it.
  The differential gear mechanism of the cocycle cancels the Möbius twist.

## References

* [Connes, Rovelli, "Von Neumann algebra automorphisms and
  time-thermodynamics relation", gr-qc/9406019][connesrovelli1994]
* [Haag, Hugenholtz, Winnink, "On the Equilibrium States in Quantum
  Statistical Mechanics", Comm. Math. Phys. 5 (1967)][hhw1967]

## Tags

Möbius strip, KMS condition, fermionic, spin-statistics, cylinder,
operator reversal, modular conjugation, outer automorphism
-/

noncomputable section

open Complex Set Filter Topology
/-!
## Section 1: The Möbius Half-Twist J

The modular conjugation J is the **generator** of the Möbius monodromy.
-/

namespace Tomita

open scoped ComplexOrder

open MeasureTheory InnerProductSpace Complex FunctionalCalculus ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **J-conjugation of an operator**: the map `ψ ↦ J(a(Jψ))`.

    This implements "JaJ" at the level of vectors. It is the Möbius
    half-twist applied to the operator a: after one traversal of the
    KMS strip, the operator a becomes JaJ. -/
def conjugateByJ (M : VNAlgebraWithVector H) (J : ModularConjugationData H M)
    (a : H →L[ℂ] H) (ψ : H) : H :=
  J.toFun (a (J.toFun ψ))

/-- **The double twist is the identity**: J(J(a(J(Jψ)))) = a(ψ).

    Two traversals of the Möbius strip return to the original orientation.
    This is the content of π₁(Möbius strip) = ℤ₂.

    We state this at the vector level: applying J on both sides of a
    twice collapses via J² = 1. Note that the inner `JaJ` is not a
    `ContinuousLinearMap` in our type system (J is antilinear), so we
    unfold to the raw `J.toFun` chain rather than nesting `conjugateByJ`. -/
theorem mobius_double_twist (M : VNAlgebraWithVector H)
    (J : ModularConjugationData H M) (a : H →L[ℂ] H) (ψ : H) :
    J.toFun (J.toFun (a (J.toFun (J.toFun ψ)))) = a ψ := by
  rw [J.involutive ψ, J.involutive (a ψ)]

/-- J-conjugation fixes the vacuum: J(a(JΩ)) = J(aΩ) when JΩ = Ω. -/
lemma conjugateByJ_vacuum (M : VNAlgebraWithVector H)
    (J : ModularConjugationData H M) (a : H →L[ℂ] H) :
    conjugateByJ M J a M.Ω = J.toFun (a M.Ω) := by
  simp only [conjugateByJ, J.fixes_vacuum]

/-- **The Möbius twist exchanges algebra and commutant.**

    For a ∈ M and b ∈ M, the operator JaJ commutes with b.
    Therefore JaJ ∈ M' — the twist maps M into the commutant.

    This is the topological content of JMJ = M': one traversal of the
    Möbius strip takes you from one face (M) to the other face (M').
    Two traversals bring you back: J(M')J = J(JMJ)J = M. -/
theorem mobius_twist_exchanges_algebras (M : VNAlgebraWithVector H)
    (Δ : ModularOperatorData H M)
    (J : ModularConjugationData H M)
    (hTT : TomitaTheorem H M Δ J)
    (a : H →L[ℂ] H) (ha : a ∈ M.algebra)
    (b : H →L[ℂ] H) (hb : b ∈ M.algebra) (ψ : H) :
    b (conjugateByJ M J a ψ) = conjugateByJ M J a (b ψ) := by
  simp only [conjugateByJ]
  -- Goal: b (J.toFun (a (J.toFun ψ))) = J.toFun (a (J.toFun (b ψ)))
  -- This is exactly Tomita's theorem Part I (up to beta reduction of ∘)
  exact hTT.conjugation a ha b hb ψ

/-- **The antiunitary inner product reversal.**

    ⟨JaJψ, JbJφ⟩ = ⟨J(a(Jψ)), J(b(Jφ))⟩ = ⟨b(Jφ), a(Jψ)⟩

    The Möbius twist reverses the inner product. This is the operator-level
    manifestation of the boundary condition reversal in the KMS strip:
    the inner product ⟨Ω, abΩ⟩ on the lower boundary becomes ⟨Ω, baΩ⟩
    on the upper boundary. -/
theorem conjugateByJ_reverses_inner (M : VNAlgebraWithVector H)
    (J : ModularConjugationData H M) (a b : H →L[ℂ] H) (ψ φ : H) :
    @inner ℂ H _ (conjugateByJ M J a ψ) (conjugateByJ M J b φ) =
    @inner ℂ H _ (b (J.toFun φ)) (a (J.toFun ψ)) := by
  simp only [conjugateByJ]
  exact J.antiunitary (a (J.toFun ψ)) (b (J.toFun φ))

/-- **J reverses the modular flow direction.**

    Conjugating the modular automorphism by J reverses time:
    J(σ_t(a)(Jψ)) = σ_{-t}(JaJ)(ψ)

    This is bundled as a hypothesis because the proof requires
    the identity JΔ^{it}J = Δ^{-it}, which follows from the polar
    decomposition S = JΔ^{1/2} but needs careful functional calculus. -/
structure TimeReversalData (M : VNAlgebraWithVector H)
    (Δ : ModularOperatorData H M)
    (J : ModularConjugationData H M) where
  /-- JΔ^{it}J = Δ^{-it} -/
  conjugate_modular_unitary : ∀ (t : ℝ) (ψ : H),
    J.toFun (modularUnitary M Δ t (J.toFun ψ)) = modularUnitary M Δ (-t) ψ

/-- Under time-reversal data, the Möbius twist reverses the modular flow. -/
theorem mobius_twist_reverses_time (M : VNAlgebraWithVector H)
    (Δ : ModularOperatorData H M)
    (J : ModularConjugationData H M)
    (hTR : TimeReversalData M Δ J)
    (t : ℝ) (ψ : H) :
    J.toFun (modularUnitary M Δ t (J.toFun ψ)) =
    modularUnitary M Δ (-t) ψ :=
  hTR.conjugate_modular_unitary t ψ

end Tomita

/-!
## Section 2: The Fermionic KMS Condition

The fermionic (anti-periodic) boundary condition is:

    F(t + iβ) = −ω(α_t(b) · a)

The sign flip implements the Möbius strip with a **ℤ₂ twist in the fiber**.
The resulting topology forces nonzero global sections to be impossible —
which is exactly what we prove.

### The spin-statistics connection

The half-integer shift in fermionic Matsubara frequencies is a direct
consequence of anti-periodicity.
-/

namespace KMSCondition

variable {A : Type*} [CStarAlgebra A]

/-- A **fermionic KMS function**: the upper boundary carries a minus sign.

    F(t)      = ω(a · α_t(b))
    F(t + iβ) = −ω(α_t(b) · a)

    The sign flip is the ℤ₂ twist that makes the KMS strip into a
    Möbius strip with nontrivial monodromy in the fiber. -/
structure FermionicKMSFunction
    (ω : State A) (α : Dynamics A) (β : ℝ) (a b : A) where
  /-- The underlying function. -/
  toFun : ℂ → ℂ
  /-- Holomorphic on the open strip. -/
  holomorphic : DifferentiableOn ℂ toFun (Strip β)
  /-- Continuous on the closed strip. -/
  continuousOn : ContinuousOn toFun (ClosedStrip β)
  /-- Bounded on the closed strip. -/
  bounded : BddAbove (norm '' (toFun '' ClosedStrip β))
  /-- Lower boundary. -/
  lower_boundary : ∀ t : ℝ, toFun (realToLower t) = ω (a * α.evolve t b)
  /-- Upper boundary with sign flip. -/
  upper_boundary : ∀ t : ℝ, toFun (realToUpper β t) = -(ω (α.evolve t b * a))

/-- A state is **fermionic KMS** if every pair admits a fermionic KMS function. -/
def IsFermionicKMSState
    (ω : State A) (α : Dynamics A) (β : ℝ) : Prop :=
  ∀ a b : A, Nonempty (FermionicKMSFunction ω α β a b)

/-- For pair (1, a), the fermionic boundaries are anti-periodic:
    F(t) = ω(α_t(a)) and F(t + iβ) = −ω(α_t(a)). -/
lemma fermionic_boundaries_anti_periodic
    {ω : State A} {α : Dynamics A} {β : ℝ} {a : A}
    (F : FermionicKMSFunction ω α β 1 a) (t : ℝ) :
    F.toFun (realToUpper β t) = -(F.toFun (realToLower t)) := by
  rw [F.lower_boundary, F.upper_boundary]
  simp only [one_mul, mul_one]


/-- **Fermionic KMS forces vanishing for the unit pair.**

    For pair (1, a), anti-periodicity gives F(t) = −F(t + iβ). The
    anti-periodic extension to all of ℂ with period 2β is bounded and
    entire, hence constant by Liouville. But the constant must equal
    its own negation, so it is zero.

    Therefore ω(α_t(a)) = F(t) = 0 for all t, including t = 0: ω(a) = 0. -/
theorem fermionic_kms_unit_vanishes
    {ω : State A} {α : Dynamics A} {β : ℝ} (_hβ : 0 < β)
    (F : FermionicKMSFunction ω α β 1 a)
    (hExtension : ∃ G : ℂ → ℂ,
      Differentiable ℂ G ∧
      Bornology.IsBounded (Set.range G) ∧
      (∀ t : ℝ, G (realToLower t) = F.toFun (realToLower t)) ∧
      (∀ z : ℂ, G (z + ↑β * I) = -G z)) :
    ∀ t : ℝ, ω (α.evolve t a) = 0 := by
  intro t
  -- Unpack the bounded entire anti-periodic extension
  obtain ⟨G, hG_diff, hG_bdd, hG_ext, hG_anti⟩ := hExtension
  have hG_const : ∀ z w : ℂ, G z = G w :=
    fun z w => hG_diff.apply_eq_apply_of_bounded hG_bdd z w
  have hG_zero : ∀ z : ℂ, G z = 0 := by
    intro z
    have heq := hG_const z (z + ↑β * I)
    rw [hG_anti] at heq
    -- heq : G z = −(G z)
    have h2 : (2 : ℂ) * G z = 0 := by linear_combination heq
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  have hFt : F.toFun (realToLower t) = 0 := by
    have := hG_zero (realToLower t)
    rwa [hG_ext] at this
  have h := F.lower_boundary t
  rw [hFt] at h
  -- h : 0 = ω (1 * α.evolve t a)
  rw [one_mul] at h
  exact h.symm

/-- **No fermionic KMS states exist on ungraded C*-algebras.**

    If ω is fermionic KMS, then ω(a) = 0 for all a (by the vanishing
    theorem). But ω(1) = 1 (normalization). Contradiction.

    **This is why fermions require ℤ₂-grading.** The Möbius strip with
    a sign twist has no nonzero global sections. To have fermionic
    thermal states, one must work with super-algebras where the KMS
    condition is restricted to homogeneous elements with appropriate
    sign factors. -/
theorem no_fermionic_kms_ungraded
    {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β)
    (hExtension : ∀ a : A, ∀ F : FermionicKMSFunction ω α β 1 a,
      ∃ G : ℂ → ℂ,
        Differentiable ℂ G ∧
        Bornology.IsBounded (Set.range G) ∧
        (∀ t : ℝ, G (realToLower t) = F.toFun (realToLower t)) ∧
        (∀ z : ℂ, G (z + ↑β * I) = -G z)) :
    ¬ IsFermionicKMSState ω α β := by
  intro hfkms
  -- Apply to pair (1, 1)
  obtain ⟨F⟩ := hfkms 1 1
  -- All expectation values vanish
  have hvanish := fermionic_kms_unit_vanishes hβ F (hExtension 1 F)
  -- In particular at t = 0: ω(α_0(1)) = ω(1) = 0
  have h0 := hvanish 0
  rw [α.evolve_zero] at h0
  -- But ω(1) = 1 by normalization — contradiction
  have := ω.normalized
  simp_all


end KMSCondition

/-!
## Section 3: Orientability of the Canonical Flow

Each modular flow σ^φ lives on a Möbius strip (non-commutative boundary
identification). But the **carrier shaft** δ : ℝ → Out(M) is orientable:
the Möbius twist is an inner automorphism, and inner automorphisms die
in the quotient Aut(M)/Inn(M).

This is the mechanical content of the Connes cocycle theorem: the
differential gear absorbs the twist from each individual Möbius gear,
producing an orientable output.
-/

namespace Tomita

open scoped ComplexOrder

open MeasureTheory InnerProductSpace Complex FunctionalCalculus ContinuousLinearMap
  SpectralBridge.Resolvent SpectralBridge.Bochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A single Möbius gear**: the modular data of one faithful normal state.

    Packages a state's modular operator, conjugation, Tomita theorem,
    and KMS structure. The "gear" is the modular flow σ^φ, the "Möbius
    topology" comes from J, and the "teeth" are the operators in M
    meshing with M' along the cyclic vector Ω. -/
structure MobiusGear (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The algebra with cyclic/separating vector. -/
  state : VNAlgebraWithVector H
  /-- The modular operator Δ. -/
  modOp : ModularOperatorData H state
  /-- The modular conjugation J (the half-twist). -/
  modConj : ModularConjugationData H state
  /-- Tomita's theorem (the twist exchanges algebra and commutant). -/
  tomita : TomitaTheorem H state modOp modConj

/-- The modular automorphism of a Möbius gear. -/
noncomputable def MobiusGear.flow (G : MobiusGear H) (t : ℝ) :
    (H →L[ℂ] H) → (H →L[ℂ] H) :=
  modularAutomorphism G.state G.modOp t

/-- **A differential gear**: two Möbius gears coupled by a cocycle.

    The left gear is σ^φ, the right gear is σ^ψ, and the bevel gear
    is the spatial derivative u_t = (Dψ : Dφ)_t. The carrier shaft
    is the canonical outer flow δ.

    **Design**: We store the modular data directly at the `twoState.φ`
    and `twoState.ψ` types rather than storing separate `MobiusGear`s
    and transporting via `▸`. This avoids dependent-type transport hell.
    Individual gears can be *extracted* via `leftGear` / `rightGear`. -/
structure DifferentialGear (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The two-state data (reference φ and target ψ on same algebra). -/
  twoState : TwoStateData H
  /-- Modular operator for the reference state φ. -/
  Δ_φ : ModularOperatorData H twoState.φ
  /-- Modular operator for the target state ψ. -/
  Δ_ψ : ModularOperatorData H twoState.ψ
  /-- Modular conjugation for φ (the left half-twist). -/
  J_φ : ModularConjugationData H twoState.φ
  /-- Modular conjugation for ψ (the right half-twist). -/
  J_ψ : ModularConjugationData H twoState.ψ
  /-- Tomita's theorem for φ. -/
  hTT_φ : TomitaTheorem H twoState.φ Δ_φ J_φ
  /-- Tomita's theorem for ψ. -/
  hTT_ψ : TomitaTheorem H twoState.ψ Δ_ψ J_ψ
  /-- Relative modular data (for constructing the bevel gear). -/
  relMod : RelativeModularOperatorData H twoState
  /-- The intertwining theorem (bevel gear engages both shafts). -/
  intertwine : IntertwiningData twoState Δ_φ Δ_ψ relMod J_φ J_ψ hTT_φ hTT_ψ
  /-- Unitarity of the spatial derivative (cocycle values are unitary). -/
  unitarity : SpatialDerivativeUnitarity H twoState Δ_φ relMod

/-- Extract the left (φ) Möbius gear from a differential gear. -/
def DifferentialGear.leftGear (DG : DifferentialGear H) : MobiusGear H :=
  ⟨DG.twoState.φ, DG.Δ_φ, DG.J_φ, DG.hTT_φ⟩

/-- Extract the right (ψ) Möbius gear from a differential gear. -/
def DifferentialGear.rightGear (DG : DifferentialGear H) : MobiusGear H :=
  ⟨DG.twoState.ψ, DG.Δ_ψ, DG.J_ψ, DG.hTT_ψ⟩

/-- **The carrier shaft is well-defined (orientable).**

    The outer automorphism class [σ_t^φ] = [σ_t^ψ] in Out(M) for
    every t, regardless of which Möbius gear we observe.

    This is the fundamental theorem of the differential gear: the
    bevel gear (cocycle) absorbs the difference between the two shafts,
    so the carrier always turns at the same rate.

    Equivalently: the Möbius twist (inner automorphism) dies in the
    quotient Aut(M)/Inn(M), making the carrier shaft orientable. -/
theorem carrier_shaft_well_defined (DG : DifferentialGear H) (t : ℝ) :
    InnerEquivalent
      (modularAutomorphism DG.twoState.φ DG.Δ_φ t)
      (modularAutomorphism DG.twoState.ψ DG.Δ_ψ t)
      DG.twoState.φ.algebra :=
  modular_flow_state_independent DG.twoState DG.hTT_φ DG.hTT_ψ DG.intertwine DG.unitarity t

/-- **The cocycle condition is the mechanical constraint.**

    In a physical differential, the bevel gears are constrained by the
    housing geometry. The total angular momentum must balance.

    The cocycle condition u_{s+t} = u_s · σ_s^φ(u_t) is this constraint:
    the correction at time s+t is not a free product u_s · u_t, but
    u_s times u_t **transported by the φ-flow**. You must evaluate the
    t-correction in the frame already rotated by s.

    This is `connes_cocycle_identity` from Cocycle.lean. We re-export it
    with differential gear language. -/
theorem bevel_gear_constraint (DG : DifferentialGear H) (s t : ℝ) :
    spatialDerivative DG.twoState DG.Δ_φ DG.relMod (s + t) =
    spatialDerivative DG.twoState DG.Δ_φ DG.relMod s *
      modularAutomorphism DG.twoState.φ DG.Δ_φ s
        (spatialDerivative DG.twoState DG.Δ_φ DG.relMod t) :=
  connes_cocycle_identity DG.twoState DG.Δ_φ DG.relMod s t

/-!
## Section 5: The Gear Ratio Chain Rule

For three states φ, ψ, χ (three Möbius gears meshing pairwise),
the cocycle satisfies the chain rule:

    (Dχ : Dφ)_t = (Dχ : Dψ)_t · (Dψ : Dφ)_t

This is **transitivity of gear ratios**: going from the φ-shaft to the
χ-shaft via the ψ-shaft, the total correction is the product of individual
corrections. -/

-- The chain rule is formalized in `ChainRuleData` in Cocycle.lean.
-- We note the Möbius interpretation: each pairwise cocycle represents
-- the bevel gear coupling two specific Möbius gears. The chain rule
-- says: cascading two differential gears is equivalent to a single
-- differential gear with the composite bevel.

/-!
## Summary: The Möbius Architecture

```
                    MÖBIUS GEAR (state φ)
                   ╭─────────────────────╮
                   │  σ_t^φ (rotation)   │
                   │  J_φ (half-twist)   │
                   │  M ←→ M' (meshing)  │
                   │  Ω_φ (contact pt)   │
                   ╰──────────┬──────────╯
                              │
                     u_t = (Dψ:Dφ)_t
                    (bevel gear / cocycle)
                    u_{s+t} = u_s σ_s^φ(u_t)
                     (mechanical constraint)
                              │
                   ╭──────────┴──────────╮
                   │  σ_t^ψ (rotation)   │
                   │  J_ψ (half-twist)   │
                   │  M ←→ M' (meshing)  │
                   │  Ω_ψ (contact pt)   │
                   ╰─────────────────────╯
                    MÖBIUS GEAR (state ψ)

         CARRIER SHAFT: δ_t = [σ_t^φ] = [σ_t^ψ] ∈ Out(M)
                    (orientable, state-independent)

         CYLINDER:  commutative ⟹ no twist ⟹ F constant (Liouville)
         MÖBIUS:    non-commutative ⟹ twist ⟹ nontrivial dynamics
         FERMIONIC: sign twist ⟹ no global sections ⟹ need ℤ₂-grading
```
-/

end Tomita
