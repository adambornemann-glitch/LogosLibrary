/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Existence/GNS/Completion.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.GNS.PreHilbert
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Tactic
/-!
# GNS Completion: From Pre-Hilbert Space to Unitary Group

Given a continuous positive definite function `f : ℝ → ℂ`, we:

1. Identify the null space `N = {α : ⟨α, α⟩_f = 0}` as a submodule
2. Quotient `(ℝ →₀ ℂ) / N` to get a genuine inner product space
3. Complete to a Hilbert space `H`
4. Extend translations `U(t)` to unitary operators on `H`
5. Package as a `OneParameterUnitaryGroup`
6. Establish `f(t) = ⟨ξ, U(t)ξ⟩` in `H`

## Architecture note

The Mathlib plumbing to go from a sesquilinear form on `Finsupp` to a
completed inner product space is substantial. We factor the construction
through an intermediate structure `GNSData` that bundles the Hilbert space,
the embedding, the unitary group, and the cyclic vector together with their
key properties. The *existence* of this data is the content of this file;
the proofs of individual fields involve quotient/completion machinery.

## References

* Folland, *A Course in Abstract Harmonic Analysis*, §3.3
* Reed & Simon, *Methods of Modern Mathematical Physics I*, §II.6
* Dixmier, *C*-Algebras*, §2.4 (GNS construction)

## Tags

GNS construction, Hilbert space completion, cyclic representation,
unitary group, Bochner's theorem
-/

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp Filter Topology


-- ════════════════════════════════════════════════════════════════════
-- §1  The null space
-- ════════════════════════════════════════════════════════════════════

/-- The null space of the PD pre-inner product:
    `N = {α : ℝ →₀ ℂ | ⟨α, α⟩_f = 0}`.

By positive semi-definiteness, `⟨α, α⟩_f = 0` iff `Re⟨α, α⟩_f = 0`
(since the imaginary part already vanishes by Hermitian symmetry).

By Cauchy-Schwarz, `N = {α | ∀ β, ⟨α, β⟩_f = 0}` — the radical of
the form. This makes N a ℂ-submodule. -/
def pdNullSpace (f : ℝ → ℂ) : Set (ℝ →₀ ℂ) :=
  {α | pdInner f α α = 0}

/-- Membership criterion: α is null iff `pdInner f α α = 0`. -/
lemma mem_pdNullSpace (f : ℝ → ℂ) (α : ℝ →₀ ℂ) :
    α ∈ pdNullSpace f ↔ pdInner f α α = 0 := Iff.rfl

/-- Null elements are orthogonal to everything (from Cauchy-Schwarz).

If `⟨α, α⟩ = 0` then `|⟨α, β⟩|² ≤ ⟨α,α⟩ · ⟨β,β⟩ = 0`,
so `⟨α, β⟩ = 0`. -/
lemma pdInner_eq_zero_of_null {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f)
    {α : ℝ →₀ ℂ} (hα : α ∈ pdNullSpace f) (β : ℝ →₀ ℂ) :
    pdInner f α β = 0 := by
  have hCS := pdInner_cauchy_schwarz_re hPD hH α β
  have hα_re : (pdInner f α α).re = 0 := by
    rw [mem_pdNullSpace] at hα; simp [hα]
  -- Re⟨α,β⟩ = 0: rewrite CS to get (Re⟨α,β⟩)² ≤ 0·⟨β,β⟩ = 0
  have hre : (pdInner f α β).re = 0 := by
    rw [hα_re, zero_mul] at hCS
    exact sq_eq_zero_iff.mp (le_antisymm hCS (sq_nonneg _))
  -- Im⟨α,β⟩ = 0: apply CS to (α, I•β), use Re(I·z) = -Im(z)
  have him : (pdInner f α β).im = 0 := by
    have hCS' := pdInner_cauchy_schwarz_re hPD hH α (I • β)
    rw [pdInner_smul_right] at hCS'
    have hIre : (I * pdInner f α β).re = -(pdInner f α β).im := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [hIre, hα_re, zero_mul, neg_sq] at hCS'
    exact sq_eq_zero_iff.mp (le_antisymm hCS' (sq_nonneg _))
  exact Complex.ext hre him

/-- The null space is a ℂ-submodule of `ℝ →₀ ℂ`. -/
lemma pdNullSpace_submodule {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) :
    ∀ (α β : ℝ →₀ ℂ), α ∈ pdNullSpace f → β ∈ pdNullSpace f →
      α + β ∈ pdNullSpace f := by
  intro α β hα hβ
  rw [mem_pdNullSpace]
  rw [pdInner_add_left hH, pdInner_add_right, pdInner_add_right]
  rw [pdInner_eq_zero_of_null hPD hH hα β,
      pdInner_eq_zero_of_null hPD hH hα α,
      pdInner_eq_zero_of_null hPD hH hβ α,
      pdInner_eq_zero_of_null hPD hH hβ β]
  simp

/-- The null space is invariant under translation:
    if `α ∈ N` then `U(t)α ∈ N`.

This follows from the translation isometry: `⟨U(t)α, U(t)α⟩ = ⟨α, α⟩ = 0`. -/
lemma pdNullSpace_translate_invariant {f : ℝ → ℂ}
    {α : ℝ →₀ ℂ} (hα : α ∈ pdNullSpace f) (t : ℝ) :
    translate t α ∈ pdNullSpace f := by
  rw [mem_pdNullSpace, pdInner_translate]
  exact (mem_pdNullSpace f α).mp hα


-- ════════════════════════════════════════════════════════════════════
-- §2  The GNS data bundle
-- ════════════════════════════════════════════════════════════════════

/-- The complete GNS data for a continuous positive definite function.

Rather than constructing the quotient and completion step by step
(which requires heavy Mathlib plumbing), we bundle everything into
a single structure and show it exists.

This is the mathematical content of the GNS theorem; the individual
fields are established through the quotient-completion construction
outlined in §3 below. -/
structure GNSData (f : ℝ → ℂ) where
  /-- The GNS Hilbert space. -/
  H : Type*
  /-- H is a normed additive commutative group. -/
  instNACG : NormedAddCommGroup H
  /-- H is an inner product space over ℂ. -/
  instIPS : @InnerProductSpace ℂ H _ instNACG.toSeminormedAddCommGroup
  /-- H is complete (Hilbert). -/
  instComplete : @CompleteSpace H instNACG.toUniformSpace
  /-- Embedding of formal sums into H. -/
  embed : letI := instNACG; letI := instIPS; (ℝ →₀ ℂ) →ₗ[ℂ] H
  /-- The embedding respects the pre-inner product. -/
  embed_inner : ∀ (α β : ℝ →₀ ℂ),
    @inner ℂ H instIPS.toInner (embed α) (embed β) = pdInner f α β
  /-- The embedded formal sums are dense in H. -/
  embed_dense : letI := instNACG; Dense (Set.range embed)
  /-- The kernel of the embedding is the null space. -/
  embed_ker : letI := instNACG; ∀ α, embed α = 0 ↔ α ∈ pdNullSpace f


-- ════════════════════════════════════════════════════════════════════
-- §3  Construction of GNSData (the hard Mathlib plumbing)
-- ════════════════════════════════════════════════════════════════════

/-- The null space is closed under scalar multiplication:
    if `α ∈ N` then `c • α ∈ N`.

Proof: `⟨cα, cα⟩ = c̄ · c · ⟨α, α⟩ = c̄ · c · 0 = 0`. -/
private lemma pdNullSpace_smul_mem {f : ℝ → ℂ}
    (hH : IsHermitian f) (c : ℂ) {α : ℝ →₀ ℂ} (hα : α ∈ pdNullSpace f) :
    c • α ∈ pdNullSpace f := by
  rw [mem_pdNullSpace, pdInner_smul_left hH, pdInner_smul_right,
      (mem_pdNullSpace f α).mp hα, mul_zero, mul_zero]

/-- The null space as a ℂ-submodule of `ℝ →₀ ℂ`. -/
def pdNullSubmodule {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) : Submodule ℂ (ℝ →₀ ℂ) where
  carrier := pdNullSpace f
  zero_mem' := pdInner_zero_left f 0
  add_mem' := fun ha hb => pdNullSpace_submodule hPD hH _ _ ha hb
  smul_mem' := fun c _ hα => pdNullSpace_smul_mem hH c hα

/-- Null elements kill from the right: if `β ∈ N` then `⟨α, β⟩ = 0`.
    (Companion to `pdInner_eq_zero_of_null` which handles the left.) -/
lemma pdInner_eq_zero_of_null_right {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f)
    (α : ℝ →₀ ℂ) {β : ℝ →₀ ℂ} (hβ : β ∈ pdNullSpace f) :
    pdInner f α β = 0 := by
  rw [pdInner_conj_symm hH, pdInner_eq_zero_of_null hPD hH hβ, map_zero]

/-- Well-definedness in the first argument:
    if `α₁ - α₂ ∈ N` then `⟨α₁, β⟩ = ⟨α₂, β⟩`. -/
lemma pdInner_resp_left {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f)
    {α₁ α₂ : ℝ →₀ ℂ} (h : α₁ - α₂ ∈ pdNullSpace f) (β : ℝ →₀ ℂ) :
    pdInner f α₁ β = pdInner f α₂ β := by
  have : α₁ = α₂ + (α₁ - α₂) := by abel
  rw [this, pdInner_add_left hH, pdInner_eq_zero_of_null hPD hH h β, add_zero]

/-- Well-definedness in the second argument:
    if `β₁ - β₂ ∈ N` then `⟨α, β₁⟩ = ⟨α, β₂⟩`. -/
lemma pdInner_resp_right {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f)
    (α : ℝ →₀ ℂ) {β₁ β₂ : ℝ →₀ ℂ} (h : β₁ - β₂ ∈ pdNullSpace f) :
    pdInner f α β₁ = pdInner f α β₂ := by
  have : β₁ = β₂ + (β₁ - β₂) := by abel
  rw [this, pdInner_add_right, pdInner_eq_zero_of_null_right hPD hH α h, add_zero]

/-- The GNS quotient: formal sums modulo the null space. -/
abbrev GNSQuotient {f : ℝ → ℂ} (hPD : PositiveDefinite f) (hH : IsHermitian f) :=
  (ℝ →₀ ℂ) ⧸ pdNullSubmodule hPD hH

/-- The pre-inner product lifted to the quotient.
    Well-defined by `pdInner_resp_left`/`pdInner_resp_right`. -/
noncomputable def quotientInner {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f)
    (x y : GNSQuotient hPD hH) : ℂ := by
  refine Quotient.liftOn₂ x y (pdInner f) ?_
  intro a₁ a₂ b₁ b₂ h₁ h₂
  have relMem : ∀ {a b : ℝ →₀ ℂ}, (pdNullSubmodule hPD hH).quotientRel.r a b →
      a - b ∈ pdNullSubmodule hPD hH := fun h => by
    have h1 := (pdNullSubmodule hPD hH).neg_mem
      ((Submodule.quotientRel_def (pdNullSubmodule hPD hH)).mp h)
    simp only [neg_sub] at h1
    exact (Submodule.quotientRel_def (pdNullSubmodule hPD hH)).mp h
  exact (pdInner_resp_left hPD hH (relMem h₁) a₂).trans
    (pdInner_resp_right hPD hH b₁ (relMem h₂))


/-- Computation rule: the lifted inner product on representatives
    equals the pre-inner product. -/
@[simp]
lemma quotientInner_mk {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f)
    (a b : ℝ →₀ ℂ) :
    quotientInner hPD hH (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
    pdInner f a b := rfl

/-- Full inner product space core on the quotient. -/
noncomputable def quotientCore {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) :
    @InnerProductSpace.Core ℂ (GNSQuotient hPD hH) _
      (inferInstance : AddCommGroup _) (inferInstance : Module ℂ _) where
  inner := quotientInner hPD hH
  conj_inner_symm x y := by
    induction x using Submodule.Quotient.induction_on with | _ a =>
    induction y using Submodule.Quotient.induction_on with | _ b =>
    simp only [quotientInner_mk]
    exact Eq.symm (pdInner_conj_symm hH b a)
  re_inner_nonneg x := by
    induction x using Submodule.Quotient.induction_on with | _ a =>
    exact pdInner_self_re_nonneg hPD a
  definite x hx := by
    induction x using Submodule.Quotient.induction_on with | _ a =>
    simp only [quotientInner_mk] at hx
    exact (Submodule.Quotient.mk_eq_zero (pdNullSubmodule hPD hH)).mpr hx
  add_left x y z := by
    induction x using Submodule.Quotient.induction_on with | _ a =>
    induction y using Submodule.Quotient.induction_on with | _ b =>
    induction z using Submodule.Quotient.induction_on with | _ c =>
    change quotientInner hPD hH (Submodule.Quotient.mk (a + b)) (Submodule.Quotient.mk c) = _
    simp only [quotientInner_mk, pdInner_add_left hH]
  smul_left x y r := by
    induction x using Submodule.Quotient.induction_on with | _ a =>
    induction y using Submodule.Quotient.induction_on with | _ b =>
    change quotientInner hPD hH (Submodule.Quotient.mk (r • a)) (Submodule.Quotient.mk b) = _
    simp only [quotientInner_mk, pdInner_smul_left hH]

/-- Definiteness: `⟨[α], [α]⟩ = 0 → [α] = 0` on the quotient. -/
lemma quotientInner_definite {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f)
    (x : GNSQuotient hPD hH) (hx : quotientInner hPD hH x x = 0) : x = 0 := by
  induction x using Submodule.Quotient.induction_on with | _ a =>
  simp only [quotientInner_mk] at hx
  exact (Submodule.Quotient.mk_eq_zero (pdNullSubmodule hPD hH)).mpr hx


/-- Scalar multiplication on the GNS quotient is uniformly continuous.
    (Instance synthesis can't derive this due to the NormedAddCommGroup/Module diamond,
    so we build it from the Lipschitz bound directly.) -/
private lemma gnsQuotient_uniformContinuousConstSMul {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) := by
  letI nacgV : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI ipsV : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  constructor; intro c
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hc : (0 : ℝ) < ‖c‖ + 1 := by linarith [norm_nonneg c]
  refine ⟨ε / (‖c‖ + 1), by positivity, fun {x y} hxy => ?_⟩
  calc dist (c • x) (c • y)
      = ‖c • (x - y)‖ := by rw [dist_eq_norm, smul_sub]
    _ ≤ ‖c‖ * ‖x - y‖ := NormedSpace.norm_smul_le c (x - y)
    _ ≤ (‖c‖ + 1) * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]
    _ = (‖c‖ + 1) * dist x y := by rw [dist_eq_norm]
    _ < (‖c‖ + 1) * (ε / (‖c‖ + 1)) := by exact mul_lt_mul_of_pos_left hxy hc
    _ = ε := by field_simp


/-- **Existence of the GNS Hilbert space.**

Construction outline:
1. `pdInner` is a positive semi-definite Hermitian form on `ℝ →₀ ℂ`.
2. The null space `N = {α : pdInner f α α = 0}` is a ℂ-submodule.
3. The quotient `V = (ℝ →₀ ℂ) / N` inherits a genuine inner product:
   `⟨[α], [β]⟩_V = pdInner f α β` (well-defined by null orthogonality).
4. This makes `V` a pre-Hilbert space.
5. The Cauchy completion `H = V̂` is a Hilbert space.
6. The embedding `ι : (ℝ →₀ ℂ) → H` is `α ↦ [α]` composed with
   the completion embedding. It is ℂ-linear and has dense range.

Mathlib tools:
- `Submodule.Quotient` for V = (ℝ →₀ ℂ) / N
- `InnerProductSpace.Core` to build the inner product on V
- `UniformSpace.Completion` for H = V̂
- `UniformSpace.Completion.denseRange_coe` for density -/
noncomputable def gnsConstruction {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) :
    GNSData f := by
  let core := quotientCore hPD hH
  let V := GNSQuotient hPD hH
  letI nacgV : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ core
  letI ipsV : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  haveI : UniformContinuousConstSMul ℂ V :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  let H := UniformSpace.Completion V
  let mkQ := (pdNullSubmodule hPD hH).mkQ
  let ι : V →ₗᵢ[ℂ] H := UniformSpace.Completion.toComplₗᵢ
  let emb : (ℝ →₀ ℂ) →ₗ[ℂ] H := ι.toLinearMap.comp mkQ
  exact {
    H := H
    instNACG := inferInstance
    instIPS := inferInstance
    instComplete := inferInstance
    embed := emb
    embed_inner := fun α β => by
      show @inner ℂ H _ (↑(mkQ α) : H) (↑(mkQ β) : H) = pdInner f α β
      rw [@UniformSpace.Completion.inner_coe]
      rfl
    embed_dense := by
      have h1 : DenseRange (mkQ : (ℝ →₀ ℂ) → V) :=
        (Submodule.mkQ_surjective _).denseRange
      have h2 : DenseRange (UniformSpace.Completion.coe' : V → H) :=
        UniformSpace.Completion.denseRange_coe
      exact h2.comp h1 (UniformSpace.Completion.continuous_coe V)
    embed_ker := fun α => by
      constructor
      · intro h
        change (↑(mkQ α) : H) = 0 at h
        rw [← UniformSpace.Completion.coe_zero] at h
        have hinj : mkQ α = 0 := by
          have := UniformSpace.Completion.isUniformEmbedding_coe (α := V)
          exact this.injective h
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hinj
      · intro h
        show (↑(mkQ α) : H) = 0
        have : mkQ α = 0 := (Submodule.Quotient.mk_eq_zero _).mpr h
        rw [this, UniformSpace.Completion.coe_zero]
  }


-- ════════════════════════════════════════════════════════════════════
-- §4  The unitary group on H
-- ════════════════════════════════════════════════════════════════════

/-- Extended translation action on the GNS Hilbert space.

Since `translate t` is an isometry of the pre-inner product:
  `⟨U(t)α, U(t)β⟩ = ⟨α, β⟩`
it descends to an isometry on the quotient, which extends uniquely
to an isometry on the completion. -/
structure GNSUnitaryGroup (f : ℝ → ℂ) extends GNSData f where
  /-- The unitary group action on H. -/
  unitaryAction : ℝ → H →ₗ[ℂ] H
  /-- U(t) is an isometry (hence unitary, since it's surjective). -/
  isometry : ∀ (t : ℝ) (ψ φ : H),
    @inner ℂ H instIPS.toInner (unitaryAction t ψ) (unitaryAction t φ) =
    @inner ℂ H instIPS.toInner ψ φ
  /-- Group law: U(s+t) = U(s) ∘ U(t). -/
  group_law : ∀ (s t : ℝ) (ψ : H),
    unitaryAction (s + t) ψ = unitaryAction s (unitaryAction t ψ)
  /-- Identity: U(0) = id. -/
  identity : ∀ (ψ : H), unitaryAction 0 ψ = ψ
  /-- Strong continuity: t ↦ U(t)ψ is continuous for each ψ. -/
  strong_continuous : ∀ (ψ : H), Continuous (fun t => unitaryAction t ψ)
  /-- Compatibility: U(t) ∘ embed = embed ∘ translate(t). -/
  compat : ∀ (t : ℝ) (α : ℝ →₀ ℂ),
    unitaryAction t (toGNSData.embed α) = toGNSData.embed (translate t α)


-- ════════════════════════════════════════════════════════════════════
-- §5  Construction of the unitary group
-- ════════════════════════════════════════════════════════════════════

/-- `translate t` as a ℂ-linear map on `ℝ →₀ ℂ`. -/
noncomputable def translateLM (t : ℝ) : (ℝ →₀ ℂ) →ₗ[ℂ] (ℝ →₀ ℂ) where
  toFun := translate t
  map_add' := translate_add_right t
  map_smul' := translate_smul t


/-- Translation preserves the null submodule (needed for `Submodule.mapQ`). -/
lemma translateLM_preserves_null {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    pdNullSubmodule hPD hH ≤ (pdNullSubmodule hPD hH).comap (translateLM t) := by
  intro α hα
  exact pdNullSpace_translate_invariant hα t


/-- Translation descended to the GNS quotient via `Submodule.mapQ`. -/
noncomputable def quotientTranslate {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    GNSQuotient hPD hH →ₗ[ℂ] GNSQuotient hPD hH :=
  Submodule.mapQ _ _ (translateLM t) (translateLM_preserves_null hPD hH t)


/-- Computation rule: `quotientTranslate` on a representative. -/
@[simp]
lemma quotientTranslate_mk {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) (α : ℝ →₀ ℂ) :
    quotientTranslate hPD hH t (Submodule.Quotient.mk α) =
    Submodule.Quotient.mk (translate t α) := rfl


/-- Group law: `U₀(s) ∘ U₀(t) = U₀(s + t)` on the quotient. -/
lemma quotientTranslate_comp {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (s t : ℝ)
    (x : GNSQuotient hPD hH) :
    quotientTranslate hPD hH s (quotientTranslate hPD hH t x) =
    quotientTranslate hPD hH (s + t) x := by
  induction x using Submodule.Quotient.induction_on with | _ a =>
  simp only [quotientTranslate_mk]
  congr 1
  exact translate_translate s t a


/-- Identity: `U₀(0) = id` on the quotient. -/
lemma quotientTranslate_zero {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f)
    (x : GNSQuotient hPD hH) :
    quotientTranslate hPD hH 0 x = x := by
  induction x using Submodule.Quotient.induction_on with | _ a =>
  simp only [quotientTranslate_mk, translate_zero]


/-- Isometry: `quotientTranslate t` preserves `quotientInner`. -/
lemma quotientTranslate_inner {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ)
    (x y : GNSQuotient hPD hH) :
    quotientInner hPD hH (quotientTranslate hPD hH t x)
                         (quotientTranslate hPD hH t y) =
    quotientInner hPD hH x y := by
  induction x using Submodule.Quotient.induction_on with | _ a =>
  induction y using Submodule.Quotient.induction_on with | _ b =>
  simp only [quotientTranslate_mk, quotientInner_mk]
  exact pdInner_translate t a b


/-- `quotientTranslate t` preserves the norm. -/
lemma quotientTranslate_norm {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ)
    (x : GNSQuotient hPD hH) :
    letI := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI := InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    ‖quotientTranslate hPD hH t x‖ = ‖x‖ := by
  letI nacgV := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI ipsV := InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  have h_inner : @inner ℂ _ ipsV.toInner
      (quotientTranslate hPD hH t x) (quotientTranslate hPD hH t x) =
      @inner ℂ _ ipsV.toInner x x := by
    induction x using Submodule.Quotient.induction_on with | _ a =>
    show quotientInner hPD hH _ _ = quotientInner hPD hH _ _
    simp only [quotientTranslate_mk, quotientInner_mk]
    exact pdInner_translate t a a
  have h_sq : ‖quotientTranslate hPD hH t x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
    exact congrArg RCLike.re h_inner
  have hfact : (‖quotientTranslate hPD hH t x‖ - ‖x‖) *
               (‖quotientTranslate hPD hH t x‖ + ‖x‖) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfact with h | h
  · linarith
  · linarith [norm_nonneg (quotientTranslate hPD hH t x), norm_nonneg x]


/-- `quotientTranslate t` as a linear isometry on the GNS quotient. -/
noncomputable def quotientTranslateLI {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI := InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    GNSQuotient hPD hH →ₗᵢ[ℂ] GNSQuotient hPD hH := by
  letI := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI := InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  exact ⟨quotientTranslate hPD hH t, quotientTranslate_norm hPD hH t⟩


/-- Uniform continuity of `quotientTranslate` (isometries are uniformly continuous). -/
lemma quotientTranslate_uniformContinuous {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI := InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    UniformContinuous (quotientTranslate hPD hH t) := by
  letI := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI := InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  exact (quotientTranslateLI hPD hH t).isometry.uniformContinuous


/-- Translation extended to the GNS completion as a ℂ-linear map.
    Linearity proved by density: `Completion.map` preserves add/smul
    because it agrees with the linear `quotientTranslate` on the dense image. -/
noncomputable def completionTranslate {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    UniformSpace.Completion (GNSQuotient hPD hH) →ₗ[ℂ]
    UniformSpace.Completion (GNSQuotient hPD hH) := by
  letI nacgV : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI ipsV : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  have huc : UniformContinuous (quotientTranslate hPD hH t) :=
    quotientTranslate_uniformContinuous hPD hH t
  -- Pre-wire completion-level instances at outer scope so nested by-blocks see them
  letI : AddGroup (UniformSpace.Completion (GNSQuotient hPD hH)) := inferInstance
  letI : IsUniformAddGroup (UniformSpace.Completion (GNSQuotient hPD hH)) := inferInstance
  haveI : ContinuousAdd (UniformSpace.Completion (GNSQuotient hPD hH)) :=
    IsTopologicalAddGroup.toContinuousAdd
  exact {
    toFun := UniformSpace.Completion.map (quotientTranslate hPD hH t)
    map_add' := fun x y => by
      refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
      · apply isClosed_eq
        · exact UniformSpace.Completion.continuous_map.comp continuous_add
        · haveI : ContinuousAdd (UniformSpace.Completion (GNSQuotient hPD hH)) :=
            IsTopologicalAddGroup.toContinuousAdd
          exact continuous_add.comp
            ((UniformSpace.Completion.continuous_map.comp continuous_fst).prodMk
             (UniformSpace.Completion.continuous_map.comp continuous_snd))
      · intro a b
        simp only [← UniformSpace.Completion.coe_add,
                   UniformSpace.Completion.map_coe huc, map_add]
    map_smul' := fun c x => by
      refine UniformSpace.Completion.induction_on x ?_ ?_
      · apply isClosed_eq
        · exact UniformSpace.Completion.continuous_map.comp (continuous_const_smul c)
        · exact (continuous_const_smul c).comp UniformSpace.Completion.continuous_map
      · intro a
        simp only [← UniformSpace.Completion.coe_smul,
                   UniformSpace.Completion.map_coe huc, map_smul]
        rfl
  }


/-- Computation rule: `completionTranslate` on a coerced quotient element. -/
@[simp]
lemma completionTranslate_coe {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ)
    (a : GNSQuotient hPD hH) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    completionTranslate hPD hH t ↑a =
    ↑(quotientTranslate hPD hH t a) := by
  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  show UniformSpace.Completion.map (quotientTranslate hPD hH t) ↑a = _
  exact UniformSpace.Completion.map_coe
    (quotientTranslate_uniformContinuous hPD hH t) a


/-- Group law on the completion: U(s)(U(t)(ψ)) = U(s+t)(ψ). -/
lemma completionTranslate_comp {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (s t : ℝ) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (ψ : UniformSpace.Completion (GNSQuotient hPD hH)),
    completionTranslate hPD hH s (completionTranslate hPD hH t ψ) =
    completionTranslate hPD hH (s + t) ψ := by
  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  intro ψ
  refine UniformSpace.Completion.induction_on ψ ?_ ?_
  · apply isClosed_eq
    · exact UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map
    · exact UniformSpace.Completion.continuous_map
  · intro a
    rw [completionTranslate_coe, completionTranslate_coe, completionTranslate_coe]
    congr 1
    exact quotientTranslate_comp hPD hH s t a


/-- Identity on the completion: U(0)(ψ) = ψ. -/
lemma completionTranslate_zero' {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (ψ : UniformSpace.Completion (GNSQuotient hPD hH)),
    completionTranslate hPD hH 0 ψ = ψ := by
  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  intro ψ
  refine UniformSpace.Completion.induction_on ψ ?_ ?_
  · apply isClosed_eq
    · exact UniformSpace.Completion.continuous_map
    · exact continuous_id
  · intro a
    rw [completionTranslate_coe]
    simp only [quotientTranslate_zero]


/-- Isometry on the completion: ⟨U(t)ψ, U(t)φ⟩ = ⟨ψ, φ⟩. -/
lemma completionTranslate_inner {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (ψ φ : UniformSpace.Completion (GNSQuotient hPD hH)),
    @inner ℂ _ InnerProductSpace.toInner
      (completionTranslate hPD hH t ψ) (completionTranslate hPD hH t φ) =
    @inner ℂ _ InnerProductSpace.toInner ψ φ := by
  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  intro ψ φ
  refine UniformSpace.Completion.induction_on₂ ψ φ ?_ ?_
  · apply isClosed_eq
    haveI : ContinuousAdd (UniformSpace.Completion (GNSQuotient hPD hH)) :=
      IsTopologicalAddGroup.toContinuousAdd
    have hcont_map : Continuous (completionTranslate hPD hH t) :=
      UniformSpace.Completion.continuous_map
    have hcont_pair : Continuous (fun (p : UniformSpace.Completion _ × UniformSpace.Completion _) =>
        (completionTranslate hPD hH t p.1, completionTranslate hPD hH t p.2)) :=
      (hcont_map.comp continuous_fst).prodMk (hcont_map.comp continuous_snd)
    · exact (@continuous_inner ℂ _ _ _ _).comp hcont_pair
    · exact @continuous_inner ℂ _ _ _ _
  · intro a b
    rw [completionTranslate_coe, completionTranslate_coe]
    simp only [UniformSpace.Completion.inner_coe]
    exact quotientTranslate_inner hPD hH t a b


/-- Compatibility: U(t) ∘ embed = embed ∘ translate(t) on the completion. -/
lemma completionTranslate_compat {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) (α : ℝ →₀ ℂ) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    let emb := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ)).toLinearMap.comp
                 (pdNullSubmodule hPD hH).mkQ
    completionTranslate hPD hH t (emb α) = emb (translate t α) := by
  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  show completionTranslate hPD hH t
    (↑(Submodule.Quotient.mk (p := pdNullSubmodule hPD hH) α)) =
    ↑(Submodule.Quotient.mk (p := pdNullSubmodule hPD hH) (translate t α))
  rw [completionTranslate_coe, quotientTranslate_mk]


/-- The inner product `t ↦ ⟨translate t α, β⟩_f` is continuous.
    Each term in the double sum involves `f` at a shifted argument;
    `f` is continuous, the sum is finite. -/
lemma pdInner_translate_left_continuous {f : ℝ → ℂ}
    (hf : IsContinuous f) (α β : ℝ →₀ ℂ) :
    Continuous (fun t => pdInner f (translate t α) β) := by
  -- Rewrite as a double Finset.sum
  have heq : ∀ t, pdInner f (translate t α) β =
      ∑ r ∈ α.support, ∑ s ∈ β.support,
        starRingEnd ℂ (α r) * β s * f (s - (r + t)) := by
    intro t
    simp only [pdInner, translate]
    rw [Finsupp.sum_mapDomain_index
      (fun r => by simp [Finsupp.sum])
      (fun r c₁ c₂ => by
        simp only [Finsupp.sum, map_add, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro s _; ring)]
    exact Eq.symm (Complex.ext rfl rfl)
  simp_rw [heq]
  apply continuous_finset_sum; intro r _
  apply continuous_finset_sum; intro s _
  exact continuous_const.mul
    (hf.continuity.comp (continuous_const.sub (continuous_const.add continuous_id)))


/-- For Finsupp α, the map t ↦ quotientTranslate t (mkQ α) is continuous ℝ → V. -/
lemma quotientTranslate_continuous {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (hf : IsContinuous f) (α : ℝ →₀ ℂ) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    Continuous (fun t => quotientTranslate hPD hH t
      ((pdNullSubmodule hPD hH).mkQ α)) := by
  letI nacgV : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI ipsV : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  set mkQ := (pdNullSubmodule hPD hH).mkQ
  set qα := mkQ α
  rw [continuous_iff_continuousAt]; intro t₀
  rw [Metric.continuousAt_iff]; intro ε hε
  -- The cross term: t ↦ Re(pdInner f (translate t α) (translate t₀ α))
  set cross := fun t => (pdInner f (translate t α) (translate t₀ α)).re
  have hcross_cont : Continuous cross :=
    Complex.continuous_re.comp (pdInner_translate_left_continuous hf α (translate t₀ α))
  -- At t = t₀, cross = Re(pdInner f α α) = ‖qα‖² (by isometry + inner_self_eq_norm_sq)
  have hcross_eq : cross t₀ = ‖qα‖ ^ 2 := by
    show (pdInner f (translate t₀ α) (translate t₀ α)).re = _
    rw [pdInner_translate]
    rw [← @inner_self_eq_norm_sq ℂ]; rfl
  -- Choose δ from continuity of cross
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.continuousAt_iff.mp
    hcross_cont.continuousAt (ε ^ 2 / 2) (by positivity)
  refine ⟨δ, hδ, @fun t ht => ?_⟩
  rw [dist_eq_norm]
  -- Expand ‖x - y‖² via norm_sub_sq
  set x := quotientTranslate hPD hH t qα
  set y := quotientTranslate hPD hH t₀ qα
  have hx_norm : ‖x‖ = ‖qα‖ := quotientTranslate_norm hPD hH t qα
  have hy_norm : ‖y‖ = ‖qα‖ := quotientTranslate_norm hPD hH t₀ qα
  have hinner_re : RCLike.re (@inner ℂ _ ipsV.toInner x y) = cross t := by
    change (quotientInner hPD hH _ _).re = _
    rfl
  have hnorm_sq : ‖x - y‖ ^ 2 = 2 * ‖qα‖ ^ 2 - 2 * cross t := by
    rw [@norm_sub_sq ℂ, hx_norm, hy_norm, hinner_re]; ring
  -- From continuity: |cross t - cross t₀| < ε²/2
  have hcross_near : |cross t - cross t₀| < ε ^ 2 / 2 := by
    rw [← Real.dist_eq]; exact hδ_spec ht
  -- ‖x - y‖² = 2(cross t₀ - cross t) = 2(‖qα‖² - cross t)
  rw [← hcross_eq] at hnorm_sq
  -- ‖x - y‖² < ε²
  have hnn : 0 ≤ ‖x - y‖ ^ 2 := sq_nonneg _
  have hnorm_bound : ‖x - y‖ ^ 2 < ε ^ 2 := by
    grind only [= abs.eq_1, = max_def]
  -- ‖x - y‖ < ε
  nlinarith [sq_nonneg ‖x - y‖, sq_abs ε]


/-- `completionTranslate t` preserves distances (isometry on the completion). -/
lemma completionTranslate_dist {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (x y : UniformSpace.Completion (GNSQuotient hPD hH)),
    dist (completionTranslate hPD hH t x) (completionTranslate hPD hH t y) =
    dist x y := by
  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  -- ‖U(t)(x - y)‖² = ‖x - y‖² from inner product preservation
  have h := completionTranslate_inner hPD hH t (x - y) (x - y)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (by exact_mod_cast h)

/-- For Finsupp α, t ↦ completionTranslate t (↑(mkQ α)) is continuous in the completion. -/
lemma completionTranslate_continuous_on_dense {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (hf : IsContinuous f) (α : ℝ →₀ ℂ) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    Continuous (fun t => completionTranslate hPD hH t
      (↑((pdNullSubmodule hPD hH).mkQ α) :
        UniformSpace.Completion (GNSQuotient hPD hH))) := by
  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  have heq : (fun t => completionTranslate hPD hH t
      (↑((pdNullSubmodule hPD hH).mkQ α))) =
    (fun t => (↑(quotientTranslate hPD hH t
      ((pdNullSubmodule hPD hH).mkQ α)) :
        UniformSpace.Completion (GNSQuotient hPD hH))) := by
    ext t; exact completionTranslate_coe hPD hH t _
  rw [heq]
  exact (UniformSpace.Completion.continuous_coe _).comp
    (quotientTranslate_continuous hPD hH hf α)

/-- **Strong continuity**: for every ψ in the completion,
    t ↦ completionTranslate t ψ is continuous. -/
theorem completionTranslate_strong_continuous {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (hf : IsContinuous f) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (ψ : UniformSpace.Completion (GNSQuotient hPD hH)),
    Continuous (fun t => completionTranslate hPD hH t ψ) := by

  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  intro ψ
  rw [continuous_iff_continuousAt]; intro t₀
  rw [Metric.continuousAt_iff]; intro ε hε
  -- Step 1: approximate ψ by ↑v
  have hd := UniformSpace.Completion.denseRange_coe (α := GNSQuotient hPD hH)
  obtain ⟨v, hv⟩ := hd.exists_dist_lt ψ (by positivity : (0 : ℝ) < ε / 3)
  obtain ⟨α, rfl⟩ := Submodule.mkQ_surjective (pdNullSubmodule hPD hH) v
  set w : UniformSpace.Completion (GNSQuotient hPD hH) :=
    ↑((pdNullSubmodule hPD hH).mkQ α)
  -- Step 2: from continuity on the dense set, get δ
  have hcont_α := completionTranslate_continuous_on_dense hPD hH hf α
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.continuousAt_iff.mp
    hcont_α.continuousAt (ε / 3) (by positivity)
  refine ⟨δ, hδ, @fun t ht => ?_⟩
  -- Step 3: triangle inequality with isometry
  calc dist (completionTranslate hPD hH t ψ) (completionTranslate hPD hH t₀ ψ)
      ≤ dist (completionTranslate hPD hH t ψ) (completionTranslate hPD hH t w) +
        dist (completionTranslate hPD hH t w) (completionTranslate hPD hH t₀ w) +
        dist (completionTranslate hPD hH t₀ w) (completionTranslate hPD hH t₀ ψ) := by
        have h1 := dist_triangle (completionTranslate hPD hH t ψ)
          (completionTranslate hPD hH t w) (completionTranslate hPD hH t₀ ψ)
        have h2 := dist_triangle (completionTranslate hPD hH t w)
          (completionTranslate hPD hH t₀ w) (completionTranslate hPD hH t₀ ψ)
        linarith
    _ < ε / 3 + ε / 3 + ε / 3 := by
        -- Term 1: dist(U(t)ψ, U(t)w) = dist(ψ, w) < ε/3 by isometry
        have h1 : dist (completionTranslate hPD hH t ψ)
            (completionTranslate hPD hH t w) < ε / 3 := by
          rw [completionTranslate_dist hPD hH t ψ w]; exact hv
        -- Term 2: dist(U(t)w, U(t₀)w) < ε/3 by continuity on dense set
        have h2 : dist (completionTranslate hPD hH t w)
            (completionTranslate hPD hH t₀ w) < ε / 3 :=
          hδ_spec ht
        -- Term 3: dist(U(t₀)w, U(t₀)ψ) = dist(w, ψ) < ε/3 by isometry
        have h3 : dist (completionTranslate hPD hH t₀ w)
            (completionTranslate hPD hH t₀ ψ) < ε / 3 := by
          rw [completionTranslate_dist hPD hH t₀ w ψ, dist_comm]; exact hv
        linarith
    _ = ε := by ring


/-- **Existence of the GNS unitary group.**

Construction:
1. `translate t` preserves `N` (by `pdNullSpace_translate_invariant`),
   so it descends to a map `U₀(t)` on the quotient `V = (ℝ →₀ ℂ)/N`.
2. `U₀(t)` is an isometry of `V` (by `pdInner_translate`).
3. Every isometry of a pre-Hilbert space extends uniquely to an isometry
   of the completion (`UniformSpace.Completion.map` with uniform continuity).
4. Group law and identity follow from `translate_translate` and `translate_zero`.
5. Strong continuity is established in §6 below. -/
noncomputable def gnsUnitaryConstruction {f : ℝ → ℂ}
    (hf : IsContinuous f) :
    GNSUnitaryGroup f := by
  set gns := gnsConstruction hf.pd hf.hermitian
  letI := gns.instNACG
  letI := gns.instIPS
  haveI := gns.instComplete
  exact {
    toGNSData := gns
    unitaryAction := fun t => completionTranslate hf.pd hf.hermitian t
    isometry := fun t ψ φ => completionTranslate_inner hf.pd hf.hermitian t ψ φ
    group_law := fun s t ψ =>
      (completionTranslate_comp hf.pd hf.hermitian s t ψ).symm
    identity := fun ψ => completionTranslate_zero' hf.pd hf.hermitian ψ
    strong_continuous := fun ψ =>
      completionTranslate_strong_continuous hf.pd hf.hermitian hf ψ
    compat := fun t α => completionTranslate_compat hf.pd hf.hermitian t α
  }


/-- **Strong continuity of U(t) on the dense set.**

For any formal sum `α = Σⱼ cⱼ δ_{sⱼ}`, we have
  ‖U(t)(embed α) - embed α‖² = Re⟨U(t)α - α, U(t)α - α⟩_f

Expanding the bilinear form over the finite support:
  = Σⱼ Σₖ c̄ⱼ cₖ [2f(sₖ-sⱼ) - f(sₖ-sⱼ+t) - f(sₖ-sⱼ-t)]

Each term → 0 as t → 0 by continuity of f (proved in IsContinuous.continuity).
Since the sum is finite, the whole expression → 0.

This gives: for each α, ‖U(t)(embed α) - embed α‖ → 0 as t → 0.
By the group law, t ↦ U(t)(embed α) is continuous at every point. -/
lemma strong_continuity_on_dense {f : ℝ → ℂ}
    (hf : IsContinuous f) (gns : GNSData f)
    (U : letI := gns.instNACG; letI := gns.instIPS; ℝ → gns.H →ₗ[ℂ] gns.H)
    (hcompat : ∀ t α, U t (gns.embed α) = gns.embed (translate t α))
    (_hiso : ∀ t ψ φ, @inner ℂ _ gns.instIPS.toInner (U t ψ) (U t φ) =
                      @inner ℂ _ gns.instIPS.toInner ψ φ) :
    ∀ (α : ℝ →₀ ℂ), letI := gns.instNACG;
      Continuous (fun t => U t (gns.embed α)) := by
  letI := gns.instNACG
  letI := gns.instIPS
  intro α
  -- Reduce to continuity of embed ∘ translate via compatibility
  suffices Continuous (fun t => gns.embed (translate t α)) from
    this.congr (fun t => (hcompat t α).symm)
  rw [continuous_iff_continuousAt]; intro t₀
  rw [Metric.continuousAt_iff]; intro ε hε
  -- The cross term: t ↦ Re(pdInner f (translate t α) (translate t₀ α))
  set cross := fun t => (pdInner f (translate t α) (translate t₀ α)).re
  have hcross_cont : Continuous cross :=
    Complex.continuous_re.comp (pdInner_translate_left_continuous hf α (translate t₀ α))
  -- At t = t₀, cross reduces via translation isometry
  have hcross_t₀ : cross t₀ = (pdInner f α α).re := by
    show (pdInner f (translate t₀ α) (translate t₀ α)).re = _
    rw [pdInner_translate]
  -- Both norms equal the same constant (translation isometry + embed_inner)
  have hF_norm_sq : ∀ s, ‖gns.embed (translate s α)‖ ^ 2 = (pdInner f α α).re := by
    intro s; rw [← @inner_self_eq_norm_sq ℂ, gns.embed_inner, pdInner_translate]; rfl
  -- The H-inner product real part matches cross
  have hinner_re : ∀ s, RCLike.re (@inner ℂ gns.H _
      (gns.embed (translate s α)) (gns.embed (translate t₀ α))) = cross s := by
    intro s; rw [gns.embed_inner]; rfl
  -- ‖F(t) - F(t₀)‖² = 2(cross t₀ - cross t) via norm_sub_sq
  have hnorm_sq : ∀ s, ‖gns.embed (translate s α) - gns.embed (translate t₀ α)‖ ^ 2 =
      2 * (cross t₀ - cross s) := by
    intro s
    rw [@norm_sub_sq ℂ, hF_norm_sq s, hF_norm_sq t₀, hinner_re s, hcross_t₀]; ring
  -- Choose δ from continuity of cross at t₀
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.continuousAt_iff.mp
    hcross_cont.continuousAt (ε ^ 2 / 2) (by positivity)
  refine ⟨δ, hδ, fun {t} ht => ?_⟩
  rw [dist_eq_norm]
  -- |cross t - cross t₀| < ε²/2
  have hcross_near : |cross t - cross t₀| < ε ^ 2 / 2 := by
    rw [← Real.dist_eq]; exact hδ_spec ht
  -- cross t₀ - cross t ≥ 0 (from ‖·‖² ≥ 0)
  have hnn : 0 ≤ cross t₀ - cross t := by
    have := (sq_nonneg ‖gns.embed (translate t α) - gns.embed (translate t₀ α)‖).trans_eq
      (hnorm_sq t)
    linarith
  -- ‖F(t) - F(t₀)‖² < ε²
  have hnorm_bound : ‖gns.embed (translate t α) - gns.embed (translate t₀ α)‖ ^ 2 < ε ^ 2 := by
    rw [hnorm_sq]
    have : cross t₀ - cross t ≤ |cross t - cross t₀| := by
      rw [abs_sub_comm]; exact le_abs_self _
    linarith
  -- ‖F(t) - F(t₀)‖ < ε
  nlinarith [sq_nonneg ‖gns.embed (translate t α) - gns.embed (translate t₀ α)‖, sq_abs ε]

/-- **Strong continuity extends to all of H.**

Given:
- Strong continuity on a dense set D ⊆ H
- Each U(t) is an isometry
Then U(t) is strongly continuous on all of H.

Standard 3ε argument: for ψ ∈ H and ε > 0,
1. Pick φ ∈ D with ‖ψ - φ‖ < ε/3
2. Pick δ so |t| < δ ⟹ ‖U(t)φ - φ‖ < ε/3
3. Then ‖U(t)ψ - ψ‖ ≤ ‖U(t)(ψ-φ)‖ + ‖U(t)φ - φ‖ + ‖φ - ψ‖
                       = ‖ψ-φ‖ + ‖U(t)φ - φ‖ + ‖φ - ψ‖ < ε -/
lemma strong_continuity_extends {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : ℝ → H →ₗ[ℂ] H)
    (hiso : ∀ t ψ, ‖U t ψ‖ = ‖ψ‖)
    (_hgroup : ∀ s t ψ, U (s + t) ψ = U s (U t ψ))
    (_hid : ∀ ψ, U 0 ψ = ψ)
    (D : Set H) (hD : Dense D)
    (hD_cont : ∀ φ ∈ D, Continuous (fun t => U t φ)) :
    ∀ ψ, Continuous (fun t => U t ψ) := by
  -- Key lemma: U(t) preserves distances (from norm preservation + linearity)
  have hdist_iso : ∀ (s : ℝ) (a b : H), dist (U s a) (U s b) = dist a b := by
    intro s a b; simp only [dist_eq_norm, ← map_sub, hiso]
  intro ψ
  rw [continuous_iff_continuousAt]; intro t₀
  rw [Metric.continuousAt_iff]; intro ε hε
  -- Step 1: Approximate ψ by φ ∈ D with ‖ψ - φ‖ < ε/3
  obtain ⟨φ, hφD, hφ_close⟩ :=
    Metric.mem_closure_iff.mp (hD ψ) (ε / 3) (by positivity)
  -- Step 2: From continuity of t ↦ U(t)φ at t₀, get δ
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.continuousAt_iff.mp
    (hD_cont φ hφD).continuousAt (ε / 3) (by positivity)
  -- Step 3: The 3ε argument
  refine ⟨δ, hδ, fun {t} ht => ?_⟩
  calc dist (U t ψ) (U t₀ ψ)
      ≤ dist (U t ψ) (U t φ) +
        dist (U t φ) (U t₀ φ) +
        dist (U t₀ φ) (U t₀ ψ) := by
          linarith [dist_triangle (U t ψ) (U t φ) (U t₀ ψ),
                    dist_triangle (U t φ) (U t₀ φ) (U t₀ ψ)]
    _ < ε / 3 + ε / 3 + ε / 3 := by
          -- Term 1: dist(U(t)ψ, U(t)φ) = dist(ψ, φ) < ε/3
          have h1 : dist (U t ψ) (U t φ) < ε / 3 := by
            rw [hdist_iso]; exact hφ_close
          -- Term 2: dist(U(t)φ, U(t₀)φ) < ε/3 by continuity on D
          have h2 : dist (U t φ) (U t₀ φ) < ε / 3 := hδ_spec ht
          -- Term 3: dist(U(t₀)φ, U(t₀)ψ) = dist(φ, ψ) < ε/3
          have h3 : dist (U t₀ φ) (U t₀ ψ) < ε / 3 := by
            rw [hdist_iso, dist_comm]; exact hφ_close
          linarith
    _ = ε := by ring


-- ════════════════════════════════════════════════════════════════════
-- §7  The cyclic vector and the representation theorem
-- ════════════════════════════════════════════════════════════════════

/-- The cyclic vector in the GNS Hilbert space:
    `ξ = embed(δ₀) = embed(single 0 1)`. -/
noncomputable def gns_cyclic (gns : GNSData f) : gns.H :=
  gns.embed cyclicVector

/-- **THE KEY IDENTITY in H**: `f(t) = ⟨ξ, U(t)ξ⟩_H`.

This is the representation theorem at the Hilbert space level.
It follows directly from PreHilbert's `pdInner_cyclic` composed
with the embedding's inner product preservation.

Proof:
  ⟨ξ, U(t)ξ⟩_H
    = ⟨embed(δ₀), U(t)(embed(δ₀))⟩_H           [definition of ξ]
    = ⟨embed(δ₀), embed(translate t δ₀)⟩_H       [compatibility]
    = pdInner f δ₀ (translate t δ₀)               [embed_inner]
    = f(t)                                         [pdInner_cyclic] -/
theorem gns_representation {f : ℝ → ℂ}
    (gns : GNSUnitaryGroup f) (t : ℝ) :
    @inner ℂ gns.H gns.instIPS.toInner
      (gns_cyclic gns.toGNSData)
      (gns.unitaryAction t (gns_cyclic gns.toGNSData)) = f t := by
  unfold gns_cyclic
  rw [gns.compat t cyclicVector,
      gns.toGNSData.embed_inner cyclicVector (translate t cyclicVector),
      pdInner_cyclic f t]

/-- The norm of the cyclic vector: `‖ξ‖² = f(0).re`.

Proof: ‖ξ‖² = Re⟨ξ,ξ⟩ = Re(pdInner f δ₀ δ₀) = Re(f(0)) = f(0).re. -/
lemma gns_cyclic_norm_sq {f : ℝ → ℂ}
    (_hH : IsHermitian f) (gns : GNSData f) :
    @inner ℂ gns.H gns.instIPS.toInner
      (gns_cyclic gns) (gns_cyclic gns) = f 0 := by
  unfold gns_cyclic
  rw [gns.embed_inner]
  have := pdInner_cyclic f 0
  rw [translate_zero] at this
  exact this


-- ════════════════════════════════════════════════════════════════════
-- §8  Packaging for Stone's theorem
-- ════════════════════════════════════════════════════════════════════

/-- The GNS unitary group satisfies all the axioms of a
    `OneParameterUnitaryGroup`.

This provides the input to Stone's theorem. The output of Stone
gives a self-adjoint generator A, and the spectral theorem then
produces the representing measure.

Note: the exact packaging depends on the `OneParameterUnitaryGroup`
structure from `UnitaryEvo/Generator.lean`. The map is:
  - `U : ℝ → H →L[ℂ] H`   from   `unitaryAction`
  - `unitary t ψ φ`         from   `isometry t ψ φ`
  - `group_law s t`          from   `group_law s t`
  - `identity`               from   `identity`
  - `strong_continuous`      from   `strong_continuous`
-/
noncomputable def toOneParameterUnitaryGroup {f : ℝ → ℂ}
    (gns : GNSUnitaryGroup f) :
    @QuantumMechanics.Generators.OneParameterUnitaryGroup gns.H
      gns.instNACG gns.instIPS := by
  letI := gns.instNACG
  letI := gns.instIPS
  haveI := gns.instComplete
  -- Each U(t) preserves norms (from inner product isometry)
  have hnorm : ∀ (t : ℝ) (ψ : gns.H), ‖gns.unitaryAction t ψ‖ = ‖ψ‖ := by
    intro t ψ
    have h := gns.isometry t ψ ψ
    rw [@inner_self_eq_norm_sq_to_K ℂ, @inner_self_eq_norm_sq_to_K ℂ] at h
    have h_sq : ‖gns.unitaryAction t ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by exact_mod_cast h
    nlinarith [sq_nonneg (‖gns.unitaryAction t ψ‖ - ‖ψ‖),
               sq_nonneg (‖gns.unitaryAction t ψ‖ + ‖ψ‖),
               norm_nonneg (gns.unitaryAction t ψ), norm_nonneg ψ]
  -- Promote each LinearMap to a ContinuousLinearMap via the norm bound
  set U : ℝ → (gns.H →L[ℂ] gns.H) := fun t =>
    (gns.unitaryAction t).mkContinuous 1 (fun ψ => by rw [hnorm, one_mul])
  exact {
    U := U
    unitary := fun t ψ φ => by
      simp only [U, LinearMap.mkContinuous_apply]
      exact gns.isometry t ψ φ
    group_law := fun s t => ContinuousLinearMap.ext fun ψ => by
      simp only [U, LinearMap.mkContinuous_apply, ContinuousLinearMap.comp_apply]
      exact (gns.group_law s t ψ)
    identity := ContinuousLinearMap.ext fun ψ => by
      simp only [U, LinearMap.mkContinuous_apply, ContinuousLinearMap.id_apply]
      exact gns.identity ψ
    strong_continuous := fun ψ => by
      exact (gns.strong_continuous ψ).congr fun t => by
        simp only [U, LinearMap.mkContinuous_apply]
  }


-- ════════════════════════════════════════════════════════════════════
-- §9  Summary: the complete GNS pipeline
-- ════════════════════════════════════════════════════════════════════

/-- **The GNS theorem for positive definite functions on ℝ.**

Given a continuous positive definite function `f : ℝ → ℂ`, there exists:
1. A Hilbert space H
2. A strongly continuous one-parameter unitary group U(t) on H
3. A vector ξ ∈ H with ‖ξ‖² = f(0).re
4. f(t) = ⟨ξ, U(t)ξ⟩ for all t

Moreover, the translates `{U(t)ξ : t ∈ ℝ}` span a dense subspace of H
(cyclicity).

This is the existence half of the GNS construction. Combined with
Stone's theorem and the spectral theorem, it yields Bochner's theorem. -/
theorem gns_theorem {f : ℝ → ℂ} (hf : IsContinuous f) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H)
      (U : ℝ → H →ₗ[ℂ] H) (ξ : H),
      (∀ t ψ φ, @inner ℂ H ‹InnerProductSpace ℂ H›.toInner (U t ψ) (U t φ) =
                 @inner ℂ H ‹InnerProductSpace ℂ H›.toInner ψ φ) ∧
      (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧
      (∀ ψ, U 0 ψ = ψ) ∧
      (∀ ψ, Continuous (fun t => U t ψ)) ∧
      (∀ t, @inner ℂ H ‹InnerProductSpace ℂ H›.toInner ξ (U t ξ) = f t) := by
  let gns := gnsUnitaryConstruction hf
  exact ⟨gns.H, gns.instNACG, gns.instIPS, gns.instComplete,
    gns.unitaryAction, gns_cyclic gns.toGNSData,
    gns.isometry, gns.group_law, gns.identity, gns.strong_continuous,
    fun t => gns_representation gns t⟩


end SpectralBridge.Bochner.GNS
