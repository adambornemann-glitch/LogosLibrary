/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.ModularTheory.KMS.Condition
/-!
# Tomita-Takesaki Modular Theory and the KMS Condition

This file contains the axiomatized statement of the fundamental connection between
modular theory and the KMS condition:

**Every faithful normal state on a von Neumann algebra is KMS at β = 1 with respect
to its modular automorphism group.**

**The modular flow IS thermal time evolution at temperature T = 1/k_B.**

This is the mathematical foundation of the "thermal time hypothesis" in quantum
gravity and the reason modular theory appears throughout quantum field theory.

## What We Bundle as Hypotheses

Since the full Tomita-Takesaki theory requires:
- Von Neumann algebras (weak operator topology, preduals)
- Unbounded operators (densely defined, closed, polar decomposition)
- Cyclic and separating vectors
- The actual construction of Δ and J

We bundle:
1. `IsVonNeumannAlgebra` - the property of being a von Neumann algebra
2. `IsFaithfulNormal` - the property of a state being faithful and normal
3. `ModularTheoryData` - the modular automorphism group, its invariance, and KMS

## References

* M. Tomita, "Quasi-standard von Neumann algebras" (1967, unpublished)
* M. Takesaki, "Tomita's theory of modular Hilbert algebras" (1970)
* O. Bratteli, D.W. Robinson, "Operator Algebras and Quantum Statistical Mechanics 2"
* A. Connes, "Noncommutative Geometry" (1994)
* S.J. Summers, "Tomita-Takesaki Modular Theory" (arXiv:math-ph/0511034)
-/

open Complex Set Filter Topology StarAlgebra

namespace KMSCondition

variable {A : Type*} [CStarAlgebra A]

/-! ## Von Neumann Algebras

A von Neumann algebra is a C*-algebra that is also closed in the weak operator
topology (equivalently, equals its double commutant, or has a predual).

For now, we axiomatize this as a property.
-/

/-- The property of being a von Neumann algebra. -/
class IsVonNeumannAlgebra (A : Type*) [CStarAlgebra A] : Prop where
  /-- A von Neumann algebra has a predual -/
  has_predual : True  -- Placeholder for actual predual condition

/-- A state is faithful if ω(a*a) = 0 implies a = 0. -/
def State.IsFaithful (ω : State A) : Prop :=
  ∀ a : A, ω (star a * a) = 0 → a = 0

/-- A state is normal if it is weak*-continuous (equivalently, comes from the predual) -/
def State.IsNormal [IsVonNeumannAlgebra A] (_ω : State A) : Prop :=
  True  -- Placeholder

/-- A faithful normal state. These are the states for which modular theory applies. -/
structure FaithfulNormalState (A : Type*) [CStarAlgebra A] [IsVonNeumannAlgebra A]
    extends State A where
  faithful : toState.IsFaithful
  normal : toState.IsNormal

/-! ## The Modular Automorphism Group

The crown jewel of Tomita-Takesaki theory: every faithful normal state ω on a
von Neumann algebra M determines a canonical one-parameter automorphism group σ^ω,
called the modular automorphism group.

Construction (sketch):
1. GNS representation: (H_ω, π_ω, Ω_ω) with ω(a) = ⟨Ω_ω, π_ω(a)Ω_ω⟩
2. Ω_ω is cyclic (by GNS) and separating (by faithfulness)
3. Define S : π_ω(a)Ω_ω ↦ π_ω(a*)Ω_ω
4. S is closable; take polar decomposition S̄ = JΔ^{1/2}
5. The modular automorphism group is σ_t(a) = Δ^{it} a Δ^{-it}

Properties:
- σ_t is a *-automorphism for each t
- t ↦ σ_t is a group homomorphism
- t ↦ σ_t(a) is strongly continuous
- ω is σ-invariant: ω ∘ σ_t = ω
- ω satisfies KMS at β = 1 with respect to σ
-/

/-- Bundled data for the Tomita-Takesaki modular theory of a faithful normal state.

    Packages the modular automorphism group together with its two fundamental
    properties: state invariance and the KMS condition at β = 1.

    Construct this term once from a concrete Tomita-Takesaki construction
    (e.g. via `TomitaTakesaki.modularGroupBundle`); everything downstream
    lights up for free. -/
structure ModularTheoryData (A : Type*) [CStarAlgebra A] [IsVonNeumannAlgebra A]
    (ω : FaithfulNormalState A) where
  /-- The modular automorphism group σ^ω. -/
  dynamics : Dynamics A
  /-- ω is σ-invariant: ω ∘ σ_t = ω. -/
  invariant : IsInvariant ω.toState dynamics
  /-- ω satisfies KMS at β = 1 with respect to σ^ω. -/
  kms_at_one : IsKMSState ω.toState dynamics 1

-- Notation: σ[hmod] extracts the dynamics from the bundle
notation:max "σ[" hmod "]" => ModularTheoryData.dynamics hmod

/-! ## Properties of the Modular Automorphism Group

These are now projections from `ModularTheoryData`, not global axioms.
-/

/-- The modular automorphism group leaves the state invariant. -/
theorem modularAutomorphismGroup_invariant {A : Type*} [CStarAlgebra A] [IsVonNeumannAlgebra A]
    {ω : FaithfulNormalState A} (hmod : ModularTheoryData A ω) :
    IsInvariant ω.toState σ[hmod] :=
  hmod.invariant

/-- **Connes' cocycle theorem (Radon-Nikodym)**: If ω and φ are both faithful
normal states, their modular automorphism groups differ by a cocycle.

σ^φ_t = u_t σ^ω_t u_t* where u_t is a σ^ω-cocycle.

This means the modular flow is "almost unique" - unique up to inner automorphisms.
-/
structure ConnesCocycle {A : Type*} [CStarAlgebra A] [IsVonNeumannAlgebra A]
    {ω : FaithfulNormalState A} (hmod : ModularTheoryData A ω) (u : ℝ → A) where
  unitary : ∀ t, u t * star (u t) = 1 ∧ star (u t) * u t = 1
  cocycle_law : ∀ s t, u (s + t) = u s * σ[hmod].evolve s (u t)
  continuous : Continuous u

/-! ## The Main Theorem: Modular States are KMS

This is the fundamental result of Tomita-Takesaki theory in its thermodynamic
interpretation. The state ω is KMS at β = 1 with respect to its own modular
automorphism group.

The proof requires constructing the KMS function F_{a,b}(z) explicitly:
- F_{a,b}(t) = ω(a · σ_t(b)) for t real
- Extend analytically to the strip 0 < Im(z) < 1
- Show F_{a,b}(t + i) = ω(σ_t(b) · a)

The analyticity comes from the spectral theory of Δ:
  ω(a · Δ^{iz} b Δ^{-iz}) is analytic in z for 0 < Im(z) < 1
-/

/-- **Takesaki's Theorem**: A faithful normal state ω on a von Neumann algebra
is KMS at β = 1 with respect to its modular automorphism group σ^ω.

This is a direct projection from the bundled modular theory data. -/
theorem modular_state_is_kms {A : Type*} [CStarAlgebra A] [IsVonNeumannAlgebra A]
    {ω : FaithfulNormalState A} (hmod : ModularTheoryData A ω) :
    IsKMSState ω.toState σ[hmod] 1 :=
  hmod.kms_at_one

/-! ## Scaling: KMS at Arbitrary Temperature

The modular group gives KMS at β = 1. What about other temperatures?

If we rescale time: α_t = σ_{t/β}, then ω is KMS at inverse temperature β
with respect to α. This is just reparametrization.
-/

/-- Rescale dynamics by a factor. -/
def Dynamics.rescale (α : Dynamics A) (c : ℝ) : Dynamics A where
  evolve := fun t => α.evolve (c * t)
  map_mul := fun t a b => α.map_mul (c * t) a b
  map_one := fun t => α.map_one (c * t)
  map_star := fun t a => α.map_star (c * t) a
  evolve_add := fun s t a => by simp [mul_add, α.evolve_add]
  evolve_zero := fun a => by simp [α.evolve_zero]
  continuous_evolve := fun a => (α.continuous_evolve a).comp (continuous_const_mul c)

/-! ## Rescaling KMS States

The key lemma: if ω is KMS at β₁ for dynamics α, then ω is KMS at β₂ for the
rescaled dynamics α_{t·β₁/β₂}. This is just reparametrization of time.
-/

/-- Rescaling the strip: z ↦ z/β maps Strip β to Strip 1. -/
lemma strip_rescale_mem {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : z ∈ Strip β) :
    z / β ∈ Strip 1 := by
  simp only [Strip, mem_setOf_eq] at hz ⊢
  simp only [div_ofReal_im]
  constructor
  · exact div_pos hz.1 hβ
  · rw [div_lt_one hβ]
    exact hz.2

/-- Rescaling the closed strip. -/
lemma closedStrip_rescale_mem {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : z ∈ ClosedStrip β) :
    z / β ∈ ClosedStrip 1 := by
  simp only [ClosedStrip, mem_setOf_eq] at hz ⊢
  simp only [div_ofReal_im]
  constructor
  · exact div_nonneg hz.1 (le_of_lt hβ)
  · rw [div_le_one hβ]
    exact hz.2

/-- The inverse rescaling. -/
lemma strip_rescale_mem' {β : ℝ} (hβ : 0 < β) {w : ℂ} (hw : w ∈ Strip 1) :
    w * β ∈ Strip β := by
  simp only [Strip, mem_setOf_eq] at hw ⊢
  constructor
  · simp only [mul_im, ofReal_im, mul_zero, ofReal_re, zero_add]
    exact mul_pos hw.1 hβ
  · calc (w * β).im = w.im * β := by simp [mul_comm]
      _ < 1 * β := by exact mul_lt_mul_of_pos_right hw.2 hβ
      _ = β := one_mul β

lemma Complex.im_div_ofReal {z : ℂ} {r : ℝ} (hr : r ≠ 0) :
       (z / r).im = z.im / r := by
     rw [div_eq_mul_inv]
     simp only [mul_im, inv_im, ofReal_im, neg_zero, normSq_ofReal, zero_div, mul_zero, inv_re,
       ofReal_re, div_self_mul_self', zero_add]
     field_simp

/-- Rescale a KMS function from temperature 1 to temperature β.

If F witnesses KMS at β=1 for dynamics σ, then G(z) = F(z/β) witnesses
KMS at β for the rescaled dynamics α_t = σ_{t/β}.
-/
noncomputable def KMSFunction.rescale {A : Type*} [CStarAlgebra A]
    {ω : State A} {σ : Dynamics A} {a b : A}
    (F : KMSFunction ω σ 1 a b) (β : ℝ) (hβ : 0 < β) :
    KMSFunction ω (σ.rescale (1/β)) β a b where
  toFun := fun z => F.toFun (z / β)
  holomorphic := by
    have h1 : DifferentiableOn ℂ (fun z : ℂ => z / (β : ℂ)) (Strip β) := by
      apply DifferentiableOn.div_const
      exact differentiableOn_id
    have h2 : Set.MapsTo (fun z : ℂ => z / (β : ℂ)) (Strip β) (Strip 1) :=
      fun z hz => strip_rescale_mem hβ hz
    convert F.holomorphic.comp h1 h2 using 1
  continuousOn := by
    have h1 : ContinuousOn (fun z : ℂ => z / (β : ℂ)) (ClosedStrip β) := by
      apply ContinuousOn.div_const
      exact continuousOn_id
    have h2 : Set.MapsTo (fun z : ℂ => z / (β : ℂ)) (ClosedStrip β) (ClosedStrip 1) :=
      fun z hz => closedStrip_rescale_mem hβ hz
    convert F.continuousOn.comp h1 h2 using 1
  bounded := by
    obtain ⟨M, hM⟩ := F.bounded
    use M
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hz
    apply hM
    exact ⟨F.toFun (w / β), ⟨w / β, closedStrip_rescale_mem hβ hw, rfl⟩, rfl⟩
  lower_boundary := by
    intro t
    have h1 : (realToLower t) / β = realToLower (t / β) := by
      simp only [realToLower, ofReal_div]
    rw [h1, F.lower_boundary]
    congr 2
    simp only [Dynamics.rescale, one_div]
    ring_nf
  upper_boundary := by
    intro t
    have hβ' : (β : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hβ)
    have h1 : (realToUpper β t) / β = realToUpper 1 (t / β) := by
      simp only [realToUpper, ofReal_div]
      rw [add_div, mul_comm (↑β) I, mul_div_assoc, div_self hβ', mul_one]
      ring_nf
      simp only [ofReal_one, mul_one]
    rw [h1, F.upper_boundary]
    congr 2
    simp only [Dynamics.rescale, one_div]
    ring_nf

/-- General rescaling: KMS function at β₁ → KMS function at β₂. -/
noncomputable def KMSFunction.rescaleGeneral {A : Type*} [CStarAlgebra A]
    {ω : State A} {α : Dynamics A} {a b : A} {β₁ : ℝ}
    (F : KMSFunction ω α β₁ a b) (β₂ : ℝ) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) :
    KMSFunction ω (α.rescale (β₁/β₂)) β₂ a b where
  toFun := fun z => F.toFun (z * (β₁ / β₂))
  holomorphic := by
    have hc : (β₁ / β₂ : ℂ) ≠ 0 := by simp [ne_of_gt hβ₁, ne_of_gt hβ₂]
    have h1 : DifferentiableOn ℂ (fun z : ℂ => z * (β₁ / β₂ : ℂ)) (Strip β₂) :=
      differentiableOn_id.mul (differentiableOn_const _)
    have h2 : Set.MapsTo (fun z : ℂ => z * (β₁ / β₂ : ℂ)) (Strip β₂) (Strip β₁) := by
      intro z hz
      simp only [Strip, mem_setOf_eq] at hz ⊢
      simp only [mul_im, div_ofReal_im, ofReal_im, zero_div, mul_zero, div_ofReal_re, ofReal_re,
        zero_add]
      constructor
      · exact mul_pos hz.1 (div_pos hβ₁ hβ₂)
      · calc z.im * (β₁ / β₂) < β₂ * (β₁ / β₂) := by apply mul_lt_mul_of_pos_right hz.2 (div_pos hβ₁ hβ₂)
          _ = β₁ := by field_simp
    convert F.holomorphic.comp h1 h2 using 1
  continuousOn := by
    have h1 : ContinuousOn (fun z : ℂ => z * (β₁ / β₂ : ℂ)) (ClosedStrip β₂) :=
      continuousOn_id.mul continuousOn_const
    have h2 : Set.MapsTo (fun z : ℂ => z * (β₁ / β₂ : ℂ)) (ClosedStrip β₂) (ClosedStrip β₁) := by
      intro z hz
      simp only [ClosedStrip, mem_setOf_eq] at hz ⊢
      simp only [mul_im, div_ofReal_im, ofReal_im, zero_div, mul_zero, div_ofReal_re, ofReal_re,
        zero_add]
      constructor
      · exact mul_nonneg hz.1 (le_of_lt (div_pos hβ₁ hβ₂))
      · calc z.im * (β₁ / β₂) ≤ β₂ * (β₁ / β₂) := by apply mul_le_mul_of_nonneg_right hz.2 (le_of_lt (div_pos hβ₁ hβ₂))
          _ = β₁ := by field_simp
    convert F.continuousOn.comp h1 h2 using 1
  bounded := by
    obtain ⟨M, hM⟩ := F.bounded
    use M
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hz
    apply hM
    refine ⟨F.toFun (w * (β₁ / β₂)), ⟨w * (β₁ / β₂), ?_, rfl⟩, rfl⟩
    simp only [ClosedStrip, mem_setOf_eq] at hw ⊢
    simp only [mul_im, div_ofReal_im, ofReal_im, zero_div, mul_zero, div_ofReal_re, ofReal_re,
      zero_add]
    constructor
    · exact mul_nonneg hw.1 (le_of_lt (div_pos hβ₁ hβ₂))
    · calc w.im * (β₁ / β₂) ≤ β₂ * (β₁ / β₂) := by apply mul_le_mul_of_nonneg_right hw.2 (le_of_lt (div_pos hβ₁ hβ₂))
        _ = β₁ := by field_simp
  lower_boundary := by
    intro t
    have h1 : realToLower t * (β₁ / β₂ : ℂ) = realToLower (t * (β₁ / β₂)) := by
      simp only [realToLower, ofReal_mul, ofReal_div]
    rw [h1, F.lower_boundary]
    congr 2
    simp only [Dynamics.rescale]
    ring_nf
  upper_boundary := by
    intro t
    have hβ₂' : (β₂ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hβ₂)
    have h1 : realToUpper β₂ t * (β₁ / β₂ : ℂ) = realToUpper β₁ (t * (β₁ / β₂)) := by
      simp only [realToUpper, ofReal_mul, ofReal_div]
      have hβ₂' : (β₂ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hβ₂)
      field_simp
    rw [h1, F.upper_boundary]
    congr 2
    simp only [Dynamics.rescale]
    ring_nf

/-- General rescaling theorem: KMS at β₁ implies KMS at β₂ for appropriately rescaled dynamics. -/
theorem IsKMSState.rescale {A : Type*} [CStarAlgebra A]
    {ω : State A} {α : Dynamics A} {β₁ : ℝ} (hβ₁ : 0 < β₁)
    (h : IsKMSState ω α β₁) (β₂ : ℝ) (hβ₂ : 0 < β₂) :
    IsKMSState ω (α.rescale (β₁/β₂)) β₂ := by
  intro a b
  obtain ⟨F⟩ := h a b
  exact ⟨F.rescaleGeneral β₂ hβ₁ hβ₂⟩

/-- A faithful normal state is KMS at any inverse temperature β > 0 with respect
to the rescaled modular automorphism group. -/
theorem modular_state_is_kms_at_beta {A : Type*} [CStarAlgebra A] [IsVonNeumannAlgebra A]
    {ω : FaithfulNormalState A} (hmod : ModularTheoryData A ω)
    (β : ℝ) (hβ : 0 < β) :
    IsKMSState ω.toState (σ[hmod].rescale (1/β)) β := by
  intro a b
  obtain ⟨F⟩ := hmod.kms_at_one a b
  exact ⟨F.rescale β hβ⟩

end KMSCondition
