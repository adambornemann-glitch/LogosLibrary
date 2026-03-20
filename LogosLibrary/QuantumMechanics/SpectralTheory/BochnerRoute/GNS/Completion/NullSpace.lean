/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/GNS/Completion/NullSpace.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.GNS.PreHilbert
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Tactic

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp Filter Topology

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

/-- The null space is closed under scalar multiplication:
    if `α ∈ N` then `c • α ∈ N`.

Proof: `⟨cα, cα⟩ = c̄ · c · ⟨α, α⟩ = c̄ · c · 0 = 0`. -/
lemma pdNullSpace_smul_mem {f : ℝ → ℂ}
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


end SpectralBridge.Bochner.GNS
