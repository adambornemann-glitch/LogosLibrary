/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: ModularTheory/Cocycle.lean
-/
import LogosLibrary.QuantumMechanics.ModularTheory.RelativeModular
import LogosLibrary.QuantumMechanics.ModularTheory.TomitaTakesaki
/-!
# The Connes Cocycle (Radon-Nikodym Theorem for von Neumann Algebras)

## The Theorem

Let M be a von Neumann algebra with faithful normal states φ and ψ. Then:

1. **Cocycle identity**: The spatial derivative u_t = (Dψ : Dφ)_t satisfies
       u_{s+t} = u_s · σ_s^φ(u_t)
   This is the "twisted" group law — it would be u_{s+t} = u_s · u_t if
   σ^φ were trivial.

2. **Intertwining**: The modular automorphism groups are related by
       σ_t^ψ(a) = u_t · σ_t^φ(a) · u_t*
   So σ^ψ and σ^φ differ by an inner automorphism Ad(u_t).

3. **State-independence in Out(M)**: The image of σ_t in the outer
   automorphism group Out(M) = Aut(M)/Inn(M) is independent of the
   state. This defines a canonical one-parameter subgroup
       δ : ℝ → Out(M)
   which is the "thermal time flow" of the algebra.

## Why This Matters

The cocycle theorem says that while the modular flow σ^φ depends on the
state φ, this dependence is only through inner automorphisms — which are
"gauge transformations" in the physics language. The *physical* content
of the flow, captured by δ : ℝ → Out(M), is intrinsic to the algebra.

This is what makes the thermal time hypothesis possible: you do not need
to choose a state to define the flow of time. The algebra M alone determines
it, up to the gauge freedom of inner automorphisms.

## The Proof Architecture

The cocycle identity follows from a computation with the spatial derivative:

  u_{s+t} = Δ_{ψ,φ}^{i(s+t)} · Δ_φ^{-i(s+t)}
           = Δ_{ψ,φ}^{is} · Δ_{ψ,φ}^{it} · Δ_φ^{-it} · Δ_φ^{-is}
           = Δ_{ψ,φ}^{is} · (Δ_φ^{-is} · Δ_φ^{is}) · Δ_{ψ,φ}^{it} · Δ_φ^{-it} · Δ_φ^{-is}
           = (Δ_{ψ,φ}^{is} · Δ_φ^{-is}) · (Δ_φ^{is} · Δ_{ψ,φ}^{it} · Δ_φ^{-it} · Δ_φ^{-is})
           = u_s · σ_s^φ(u_t)

The key step is inserting Δ_φ^{-is} · Δ_φ^{is} = 1 and recognizing
the conjugation Δ_φ^{is} · (·) · Δ_φ^{-is} as σ_s^φ.

## References

* [Connes, "Une classification des facteurs de type III",
  Ann. Sci. École Norm. Sup. 6 (1973), 133–252][connes1973]
* [Connes, "Sur le théorème de Radon-Nikodym pour les poids normaux
  fidèles semi-finis", Bull. Sci. Math. 97 (1973)][connes1973b]
* [Connes, Rovelli, "Von Neumann algebra automorphisms and
  time-thermodynamics relation", gr-qc/9406019][connesrovelli1994]
* [Takesaki, *Theory of Operator Algebras II*][takesaki2003], Ch. VIII, Thm. 3.3

## Tags

Connes cocycle, Radon-Nikodym, outer automorphism, thermal time,
state-independence
-/

noncomputable section

namespace Tomita

open scoped ComplexOrder

open MeasureTheory InnerProductSpace Complex FunctionalCalculus ContinuousLinearMap
  SpectralBridge.Resolvent SpectralBridge.Bochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## Section 1: The Cocycle Identity
-/

variable (D : TwoStateData H)
variable (Delta_phi : ModularOperatorData H D.φ)
variable (Delta_psi : ModularOperatorData H D.ψ)
variable (Delta_rel : RelativeModularOperatorData H D)
variable (J_phi : ModularConjugationData H D.φ)
variable (J_psi : ModularConjugationData H D.ψ)

/-- **The Connes Cocycle Identity** (Radon-Nikodym theorem).

    u_{s+t} = u_s . sigma_s^phi(u_t)

    where u_t = Delta_{psi,phi}^{it} . Delta_phi^{-it}
    and sigma_s^phi(.) = Delta_phi^{is} . (.) . Delta_phi^{-is}.

    This is [Connes 1973, Theoreme 1.2.1] / [Takesaki, TOA II, Ch. VIII, Thm. 3.3]. -/
theorem connes_cocycle_identity (s t : Real) :
    spatialDerivative D Delta_phi Delta_rel (s + t) =
    spatialDerivative D Delta_phi Delta_rel s *
      modularAutomorphism D.φ Delta_phi s (spatialDerivative D Delta_phi Delta_rel t) := by
  -- Expand spatialDerivative to relativeModularUnitary * modularUnitary(-.)
  simp only [spatialDerivative]
  -- Expand modularAutomorphism to conjugation by modularUnitary
  simp only [modularAutomorphism]
  -- Step 1: Group law for relative modular unitary
  rw [relativeModularUnitary_group_law D Delta_rel s t]
  -- Step 2: Group law for phi-modular unitary (with negation)
  have h_neg_add : modularUnitary D.φ Delta_phi (-(s + t)) =
      modularUnitary D.φ Delta_phi (-t) * modularUnitary D.φ Delta_phi (-s) := by
    rw [show -(s + t) = -t + -s from by ring]
    exact modularUnitary_group_law D.φ Delta_phi (-t) (-s)
  rw [h_neg_add]
  -- Step 3: Insert identity Delta_phi^{-is} . Delta_phi^{is} = 1
  have h_inv : modularUnitary D.φ Delta_phi (-s) * modularUnitary D.φ Delta_phi s = 1 := by
    rw [<- modularUnitary_group_law D.φ Delta_phi (-s) s]
    simp [modularUnitary_zero]
  -- Step 4: Algebra
  calc relativeModularUnitary D Delta_rel s * relativeModularUnitary D Delta_rel t *
        (modularUnitary D.φ Delta_phi (-t) * modularUnitary D.φ Delta_phi (-s))
      = relativeModularUnitary D Delta_rel s *
        (modularUnitary D.φ Delta_phi (-s) * modularUnitary D.φ Delta_phi s) *
        relativeModularUnitary D Delta_rel t *
        (modularUnitary D.φ Delta_phi (-t) * modularUnitary D.φ Delta_phi (-s)) := by
          rw [h_inv, mul_one]
    _ = (relativeModularUnitary D Delta_rel s * modularUnitary D.φ Delta_phi (-s)) *
        (modularUnitary D.φ Delta_phi s *
          (relativeModularUnitary D Delta_rel t * modularUnitary D.φ Delta_phi (-t)) *
          modularUnitary D.φ Delta_phi (-s)) := by ring_nf; norm_cast

/-!
## Section 1: The Cocycle Identity

The heart of the matter. We prove:
  u_{s+t} = u_s · σ_s^φ(u_t)
where u_t = (Dψ : Dφ)_t = Δ_{ψ,φ}^{it} · Δ_φ^{-it}.
-/



/-!
### The algebraic computation

The cocycle identity is fundamentally an algebraic identity involving
the group laws of three one-parameter unitary groups:
- Δ_{ψ,φ}^{it} (relative modular unitary)
- Δ_φ^{it} (φ-modular unitary)
- σ_t^φ (φ-modular automorphism)

Step 1: Expand u_{s+t} using the definition
Step 2: Factor using group laws of each unitary group
Step 3: Insert the identity Δ_φ^{-is} · Δ_φ^{is} = 1
Step 4: Recognize σ_s^φ(u_t) = Δ_φ^{is} u_t Δ_φ^{-is}
-/

/-!
## Section 2: The Intertwining Theorem

σ_t^ψ(a) = u_t · σ_t^φ(a) · u_t*

This says: the ψ-modular automorphism is obtained from the φ-modular
automorphism by conjugating with the cocycle.
-/

/-- **The Intertwining Theorem** bundled as a hypothesis.

    σ_t^ψ(a) = u_t · σ_t^φ(a) · u_t*

    for all a ∈ M and t ∈ ℝ.

    This is the statement that the modular automorphism groups of different
    states differ by inner automorphisms. It is equivalent to the cocycle
    identity and in fact follows from it together with the definition of
    the spatial derivative.

    The proof requires the analytic structure of the relative modular operator
    and the relation Δ_{ψ,φ}^{it} M Δ_{ψ,φ}^{-it} = M (relative Tomita theorem),
    which is harder than the single-state case. -/
structure IntertwiningData
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : TwoStateData H)
    (Δ_φ : ModularOperatorData H D.φ)
    (Δ_ψ : ModularOperatorData H D.ψ)
    (Δ_rel : RelativeModularOperatorData H D)
    (J_φ : ModularConjugationData H D.φ)
    (J_ψ : ModularConjugationData H D.ψ)
    (hTT_φ : TomitaTheorem H D.φ Δ_φ J_φ)
    (hTT_ψ : TomitaTheorem H D.ψ Δ_ψ J_ψ) where
  /-- σ_t^ψ(a) = u_t · σ_t^φ(a) · u_t* -/
  intertwine : ∀ (t : ℝ) (a : H →L[ℂ] H), a ∈ D.φ.algebra →
    modularAutomorphism D.ψ Δ_ψ t a =
    spatialDerivative D Δ_φ Δ_rel t *
      modularAutomorphism D.φ Δ_φ t a *
      ContinuousLinearMap.adjoint (spatialDerivative D Δ_φ Δ_rel t)

/-!
## Section 3: State-Independence in Out(M)

The outer automorphism group Out(M) = Aut(M) / Inn(M).

Two automorphisms α, β ∈ Aut(M) define the same class in Out(M) iff
there exists a unitary u ∈ M with β = Ad(u) ∘ α.

The intertwining theorem says exactly that σ_t^ψ and σ_t^φ define the
same class in Out(M). We formalize this.
-/
section CocycleIdentity
local notation "u" => spatialDerivative D Delta_phi Delta_rel

end CocycleIdentity
-- notation is dead here, so `u` is a normal identifier again
/-- Two automorphisms of M are *inner-equivalent* if they differ by
    conjugation with a unitary in M. -/
def InnerEquivalent
    (α β : (H →L[ℂ] H) → (H →L[ℂ] H))
    (M : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∃ (u /-unexpected token 'u'; expected '_' or identifier-/: H →L[ℂ] H),
    u ∈ M.toSubalgebra ∧
    u * ContinuousLinearMap.adjoint u = 1 ∧
    ContinuousLinearMap.adjoint u * u = 1 ∧
    ∀ a ∈ M, β a = u * α a * ContinuousLinearMap.adjoint u

/-- Inner equivalence is reflexive. -/
lemma innerEquivalent_refl (α : (H →L[ℂ] H) → (H →L[ℂ] H))
    (M : StarSubalgebra ℂ (H →L[ℂ] H)) :
    InnerEquivalent α α M := by
  have hadj : ContinuousLinearMap.adjoint (1 : H →L[ℂ] H) = 1 := star_one _
  exact ⟨1, M.toSubalgebra.one_mem,
    by simp [hadj], by simp [hadj], fun a _ => by simp [hadj]⟩

/-- Inner equivalence is symmetric.

    If β = Ad(u) ∘ α, then α = Ad(u*) ∘ β. -/
lemma innerEquivalent_symm {α β : (H →L[ℂ] H) → (H →L[ℂ] H)}
    {M : StarSubalgebra ℂ (H →L[ℂ] H)}
    (h : InnerEquivalent α β M) :
    InnerEquivalent β α M := by
  obtain ⟨u, hu_mem, hu_l, hu_r, hu_eq⟩ := h
  refine ⟨ContinuousLinearMap.adjoint u,
    M.star_mem' hu_mem,
    by rwa [ContinuousLinearMap.adjoint_adjoint],
    by rwa [ContinuousLinearMap.adjoint_adjoint],
    fun a ha => ?_⟩
  -- β(a) = u · α(a) · u*  ⟹  α(a) = u* · β(a) · u
  have hβ := hu_eq a ha
  -- Multiply on left by u* and right by u
  calc α a
      = ContinuousLinearMap.adjoint u * u * α a *
          (ContinuousLinearMap.adjoint u * u) := by rw [hu_r]; simp
    _ = ContinuousLinearMap.adjoint u * (u * α a * ContinuousLinearMap.adjoint u) *
          u := by norm_cast
    _ = ContinuousLinearMap.adjoint u * β a * u := by rw [← hβ]
    _ = ContinuousLinearMap.adjoint u * β a *
          ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint u) := by
        rw [ContinuousLinearMap.adjoint_adjoint]

/-- Inner equivalence is transitive.

    If β = Ad(u) ∘ α and γ = Ad(v) ∘ β, then γ = Ad(vu) ∘ α. -/
lemma innerEquivalent_trans {α β γ : (H →L[ℂ] H) → (H →L[ℂ] H)}
    {M : StarSubalgebra ℂ (H →L[ℂ] H)}
    (h₁ : InnerEquivalent α β M)
    (h₂ : InnerEquivalent β γ M) :
    InnerEquivalent α γ M := by
  obtain ⟨u, /-unexpected token 'u'; expected '⟩'-/ hu_mem, hu_l, hu_r, hu_eq⟩ := h₁
  obtain ⟨v, hv_mem, hv_l, hv_r, hv_eq⟩ := h₂
  refine ⟨v * u,
    M.toSubalgebra.mul_mem hv_mem hu_mem,
    ?_, ?_,
    fun a ha => ?_⟩
  · -- (vu)(vu)* = vu u* v* = v·1·v* = 1
    calc (v * u) * ContinuousLinearMap.adjoint (v * u)
        = v * (u * ContinuousLinearMap.adjoint u) * ContinuousLinearMap.adjoint v := by
          change (v * u) * star (v * u) = _
          rw [star_mul]; norm_cast
      _ = v * ContinuousLinearMap.adjoint v := by rw [hu_l, mul_one]
      _ = 1 := hv_l
  · -- (vu)*(vu) = u* v* v u = u*·1·u = 1
    calc ContinuousLinearMap.adjoint (v * u) * (v * u)
        = ContinuousLinearMap.adjoint u * (ContinuousLinearMap.adjoint v * v) * u := by
          change star (v * u) * (v * u) = _
          rw [star_mul]; norm_cast
      _ = ContinuousLinearMap.adjoint u * u := by rw [hv_r, mul_one]
      _ = 1 := hu_r
  · -- γ(a) = v · β(a) · v* = v · (u · α(a) · u*) · v* = (vu) · α(a) · (vu)*
    calc γ a = v * β a * ContinuousLinearMap.adjoint v := hv_eq a ha
      _ = v * (u * α a * ContinuousLinearMap.adjoint u) *
            ContinuousLinearMap.adjoint v := by rw [← hu_eq a ha]
      _ = (v * u) * α a * ContinuousLinearMap.adjoint (v * u) := by
          change _ = (v * u) * α a * star (v * u)
          rw [star_mul]; norm_cast

/-- Inner equivalence is an equivalence relation. -/
def innerEquivalentSetoid (M : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Setoid ((H →L[ℂ] H) → (H →L[ℂ] H)) :=
  ⟨fun α β => InnerEquivalent α β M,
    ⟨fun α => innerEquivalent_refl α M,
     fun h => innerEquivalent_symm h,
     fun h₁ h₂ => innerEquivalent_trans h₁ h₂⟩⟩

/-- **Connes' Theorem: State-independence of the modular flow in Out(M).**

    For any two faithful normal states φ and ψ on M, the modular
    automorphisms σ_t^φ and σ_t^ψ define the same element of Out(M)
    for every t.

    This is the *raison d'être* of the cocycle theorem. -/
theorem modular_flow_state_independent
    (hTT_φ : TomitaTheorem H D.φ Δ_φ J_φ)
    (hTT_ψ : TomitaTheorem H D.ψ Δ_ψ J_ψ)
    (hI : IntertwiningData D Δ_φ Δ_ψ Δ_rel J_φ J_ψ hTT_φ hTT_ψ)
    (hU : SpatialDerivativeUnitarity H D Δ_φ Δ_rel)
    (t : ℝ) :
    InnerEquivalent
      (modularAutomorphism D.φ Δ_φ t)
      (modularAutomorphism D.ψ Δ_ψ t)
      D.φ.algebra :=
  ⟨spatialDerivative D Δ_φ Δ_rel t,
   hU.mem_algebra t,
   (hU.isUnitary t).1,
   (hU.isUnitary t).2,
   fun a ha => hI.intertwine t a ha⟩

/-!
## Section 4: The Canonical Flow δ : ℝ → Out(M)

Since the image of σ_t in Out(M) is state-independent, it defines a
canonical one-parameter group homomorphism. We package this.
-/

/-- The outer automorphism class of σ_t^φ, which is state-independent.

    Represented as the equivalence class of σ_t^φ modulo inner
    automorphisms of M. -/
def canonicalOuterFlow (t : ℝ) :
    Quotient (innerEquivalentSetoid D.φ.algebra) :=
  Quotient.mk _ (modularAutomorphism D.φ Delta_phi t)

/-- The canonical flow respects the group law:
    [σ_{s+t}^φ] = [σ_s^φ ∘ σ_t^φ] in Out(M).

    This is the pointwise version. A full group homomorphism statement
    requires defining multiplication on Out(M), which we defer. -/
theorem canonicalOuterFlow_group_law (s t : ℝ) :
    canonicalOuterFlow D Delta_phi (s + t) =
    Quotient.mk (innerEquivalentSetoid D.φ.algebra)
      (fun a => modularAutomorphism D.φ Delta_phi s
        (modularAutomorphism D.φ Delta_phi t a)) := by
  simp only [canonicalOuterFlow]
  congr 1
  funext a
  exact modularAutomorphism_group_law D.φ Delta_phi s t a

/-!
## Section 5: Connection to Thermal Time

The canonical flow δ : ℝ → Out(M) is what Connes and Rovelli call
the "thermal time flow". The thermal time hypothesis states:

**The physical time flow of a generally covariant quantum system
is given by δ.**

This is formalized not as a theorem but as a *definition*: we define
thermal time to be the canonical flow, and derive consequences.
-/

/-- **The thermal time flow** of a von Neumann algebra M.

    This is the state-independent one-parameter group of outer
    automorphisms defined by the modular flow. It is the mathematical
    content of the Connes-Rovelli thermal time hypothesis.

    For any choice of faithful normal state φ, the thermal time flow
    at time t is the outer automorphism class [σ_t^φ] ∈ Out(M). -/
def thermalTimeFlow := canonicalOuterFlow D Delta_phi

/-!
## Section 6: The Chain Rule (Transitivity of the Cocycle)

For three states φ, ψ, χ:
  (Dχ : Dφ)_t = (Dχ : Dψ)_t · (Dψ : Dφ)_t

This is the "chain rule" for the Connes cocycle, analogous to the
chain rule for classical Radon-Nikodym derivatives:
  dχ/dφ = (dχ/dψ) · (dψ/dφ)
-/

/-- Setup for the chain rule: three states on the same algebra. -/
structure ThreeStateData (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The first state φ. -/
  φ : VNAlgebraWithVector H
  /-- The second state ψ. -/
  ψ : VNAlgebraWithVector H
  /-- The third state χ. -/
  χ : VNAlgebraWithVector H
  /-- All three live on the same algebra. -/
  same_algebra_φψ : φ.algebra = ψ.algebra
  same_algebra_ψχ : ψ.algebra = χ.algebra

/-- Extract the (φ, ψ) pair. -/
def ThreeStateData.toφψ (T : ThreeStateData H) : TwoStateData H :=
  ⟨T.φ, T.ψ, T.same_algebra_φψ⟩

/-- Extract the (ψ, χ) pair. -/
def ThreeStateData.toψχ (T : ThreeStateData H) : TwoStateData H :=
  ⟨T.ψ, T.χ, T.same_algebra_ψχ⟩

/-- Extract the (φ, χ) pair. -/
def ThreeStateData.toφχ (T : ThreeStateData H) : TwoStateData H :=
  ⟨T.φ, T.χ, T.same_algebra_φψ.trans T.same_algebra_ψχ⟩

/-- **The Chain Rule for Connes Cocycles** bundled as a hypothesis.

    (Dχ : Dφ)_t = (Dχ : Dψ)_t · (Dψ : Dφ)_t

    This is the non-commutative analogue of the multiplicativity
    of the Radon-Nikodym derivative.

    The proof requires showing that the product of spatial
    derivatives with respect to intermediate states equals the direct
    spatial derivative. This follows from the factorization of relative
    modular operators but requires careful domain arguments. -/
structure ChainRuleData
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : ThreeStateData H)
    (Δ_φ : ModularOperatorData H T.φ)
    (Δ_ψ : ModularOperatorData H T.ψ)
    (Δ_rel_φψ : RelativeModularOperatorData H T.toφψ)
    (Δ_rel_ψχ : RelativeModularOperatorData H T.toψχ)
    (Δ_rel_φχ : RelativeModularOperatorData H T.toφχ) where
  /-- (Dχ : Dφ)_t = (Dχ : Dψ)_t · (Dψ : Dφ)_t -/
  chain_rule : ∀ (t : ℝ),
    spatialDerivative T.toφχ Δ_φ Δ_rel_φχ t =
    spatialDerivative T.toψχ Δ_ψ Δ_rel_ψχ t * spatialDerivative T.toφψ Δ_φ Δ_rel_φψ t

/-!
## Section 7: The Converse (Cocycle Characterization)

Every σ^φ-cocycle arises as a Connes cocycle (Dψ : Dφ)_t for some
faithful normal state ψ. This is the *surjectivity* part of the
Radon-Nikodym theorem.

Formally: if u_t ∈ M is a strongly continuous family of unitaries
satisfying u_{s+t} = u_s · σ_s^φ(u_t), then there exists a unique
faithful normal state ψ such that u_t = (Dψ : Dφ)_t.
-/

/-- A σ-cocycle: a strongly continuous unitary-valued 1-cocycle
    for the modular automorphism group. -/
structure ModularCocycle
    (M : VNAlgebraWithVector H)
    (Δ : ModularOperatorData H M)
    (J : ModularConjugationData H M) where
  /-- The cocycle values. -/
  u /-unexpected token 'u'; expected 'lemma'-/: ℝ → H →L[ℂ] H
  /-- Each u_t is unitary. -/
  isUnitary /-unexpected token 'u'; expected 'lemma'-/ : ∀ t,
    u t * ContinuousLinearMap.adjoint (u t) = 1 ∧
    ContinuousLinearMap.adjoint (u t) * u t = 1
  /-- Each u_t ∈ M. -/
  mem_algebra /-unexpected token 'u'; expected 'lemma'-/: ∀ t, u t ∈ M.algebra.toSubalgebra
  /-- The cocycle identity. -/
  cocycle_law : ∀ s t, u (s + t) = u s * modularAutomorphism M Δ s (u t)
  /-- u_0 = 1. -/
  at_zero : u 0 = 1
  /-- Strong continuity: t ↦ u_t(ψ) is continuous for all ψ. -/
  strongly_continuous : ∀ ψ : H, Continuous (fun t => u t ψ)

/-- **Connes' Radon-Nikodym Theorem (Surjectivity)** bundled as a hypothesis.

    Every σ^φ-cocycle arises from a faithful normal state.

    Given a cocycle u_t for σ^φ, there exists a faithful normal state ψ
    (represented by a cyclic separating vector Ω_ψ) such that
    u_t = (Dψ : Dφ)_t.

    This is [Connes 1973, Théorème 1.2.4]. The proof requires the Connes
    inverse construction: given u_t, define ψ(a) = φ(u_{-i/2}* a u_{-i/2})
    using analytic continuation of the cocycle to imaginary time. -/
structure RadonNikodymSurjectivity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VNAlgebraWithVector H)
    (Δ : ModularOperatorData H M)
    (J : ModularConjugationData H M)
    (c : ModularCocycle M Δ J) where
  /-- The two-state data witnessing the cocycle as a spatial derivative. -/
  twoState : TwoStateData H
  /-- Modular operator data for the base state of twoState. -/
  deltaBase : ModularOperatorData H twoState.φ
  /-- The relative modular operator data. -/
  relModular : RelativeModularOperatorData H twoState
  /-- The base state matches M. -/
  base_eq : twoState.φ = M
  /-- The cocycle equals the spatial derivative. -/
  is_spatial : ∀ t, c.u t = spatialDerivative twoState deltaBase relModular t
/-
## Axiom Count and Status

### Hypotheses in this file (bundled as structures):
1. `IntertwiningData`
   — σ_t^ψ(a) = u_t σ_t^φ(a) u_t*
   — Status: follows from relative Tomita theorem + spectral calculus

2. `ChainRuleData`
   — (Dχ : Dφ)_t = (Dχ : Dψ)_t · (Dψ : Dφ)_t
   — Status: follows from factorization of relative modular operators

3. `RadonNikodymSurjectivity`
   — Every cocycle is a spatial derivative
   — Status: hardest hypothesis; requires constructing ψ from u_t
   — This is the deep content of [Connes 1973, Thm. 1.2.4]

### Path to discharging:
- Hypotheses 1–2 are "medium" — they require careful but standard functional
  analysis that your existing spectral calculus can handle once you build
  out the relative modular operator construction.
- Hypothesis 3 is "hard" — it requires the Connes inverse construction:
  given u_t, define ψ(a) = φ(u_{-i/2}* a u_{-i/2}) using analytic
  continuation of the cocycle to imaginary time. This needs the full
  KMS strip machinery from your PeriodicStrip.lean.
-/

end Tomita
