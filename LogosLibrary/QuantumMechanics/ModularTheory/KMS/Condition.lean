/-
Copyright (c) 2026 KMS Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Complex.Liouville

import LogosLibrary.QuantumMechanics.ModularTheory.KMS.PeriodicStrip

/-!
# The Kubo-Martin-Schwinger (KMS) Condition

This file defines the KMS condition for states on C*-algebras with dynamics.

## The Physics

The KMS condition characterizes thermal equilibrium states in quantum statistical mechanics.
It was introduced by Kubo (1957) and Martin-Schwinger (1959), and given its modern
operator-algebraic form by Haag-Hugenholtz-Winnink (1967).

The key insight: at inverse temperature β = 1/(k_B T), equilibrium correlation functions
satisfy a specific analyticity condition in the complex time plane. This is equivalent
to the Gibbs condition ρ = e^{-βH}/Z for finite systems, but generalizes to infinite
systems where no trace or Hamiltonian may exist.

## The Mathematics

Given:
- A C*-algebra `A` (the observables)
- A one-parameter automorphism group `α : ℝ → Aut(A)` (time evolution)
- A state `ω : A → ℂ` (expectation values)
- Inverse temperature `β > 0`

The state ω satisfies the **KMS condition at inverse temperature β** if:
for all a, b ∈ A, there exists a function F : ℂ → ℂ such that:

1. F is holomorphic on the open strip S_β = {z : 0 < Im(z) < β}
2. F is bounded and continuous on the closed strip S̄_β = {z : 0 ≤ Im(z) ≤ β}
3. F(t) = ω(a · α_t(b)) for all t ∈ ℝ (lower boundary)
4. F(t + iβ) = ω(α_t(b) · a) for all t ∈ ℝ (upper boundary)

The "twist" between the two boundaries encodes the non-commutativity of quantum
observables and the thermal nature of the state.

## Main Definitions

- `Strip β`: The horizontal strip {z ∈ ℂ : 0 < Im(z) < β}
- `ClosedStrip β`: The closed strip {z ∈ ℂ : 0 ≤ Im(z) ≤ β}
- `KMSFunction`: A function satisfying the analyticity/boundary conditions
- `IsKMSState`: The predicate that a state satisfies the KMS condition

## References

* R. Kubo, "Statistical-Mechanical Theory of Irreversible Processes", J. Phys. Soc. Japan 12 (1957)
* P.C. Martin, J. Schwinger, "Theory of Many-Particle Systems. I", Phys. Rev. 115 (1959)
* R. Haag, N. Hugenholtz, M. Winnink, "On the Equilibrium States in Quantum Statistical Mechanics",
  Comm. Math. Phys. 5 (1967)
* O. Bratteli, D.W. Robinson, "Operator Algebras and Quantum Statistical Mechanics 2" (1997)

-/
namespace KMSCondition

open Complex Set Filter Topology Convex

/-! ## The Strip in the Complex Plane -/

/-- The lower boundary of the strip (the real line) -/
def LowerBoundary : Set ℂ :=
  {z : ℂ | z.im = 0}

/-- The upper boundary of the strip at height β -/
def UpperBoundary (β : ℝ) : Set ℂ :=
  {z : ℂ | z.im = β}

-- Basic lemmas about strips
lemma Strip_subset_ClosedStrip {β : ℝ} (_hβ : 0 < β) : Strip β ⊆ ClosedStrip β := by
  intro z ⟨h1, h2⟩
  exact ⟨le_of_lt h1, le_of_lt h2⟩

lemma LowerBoundary_subset_ClosedStrip {β : ℝ} (hβ : 0 ≤ β) : LowerBoundary ⊆ ClosedStrip β := by
  intro z hz
  simp only [LowerBoundary, ClosedStrip, mem_setOf_eq] at *
  exact ⟨le_of_eq hz.symm, by linarith⟩

lemma UpperBoundary_subset_ClosedStrip {β : ℝ} (hβ : 0 ≤ β) : UpperBoundary β ⊆ ClosedStrip β := by
  intro z hz
  simp only [UpperBoundary, ClosedStrip, mem_setOf_eq] at *
  exact ⟨by linarith, le_of_eq hz⟩

lemma realToLower_im (t : ℝ) : (realToLower t).im = 0 := by
  simp [realToLower]

lemma realToUpper_im (β t : ℝ) : (realToUpper β t).im = β := by
  simp [realToUpper]

lemma realToLower_mem_LowerBoundary (t : ℝ) : realToLower t ∈ LowerBoundary :=
  realToLower_im t

lemma realToUpper_mem_UpperBoundary (β t : ℝ) : realToUpper β t ∈ UpperBoundary β :=
  realToUpper_im β t

/-! ## Axiomatized Structures

We axiomatize the structures we need. These will be replaced with proper
definitions as we build out the library.
-/

/-- A C*-algebra. Axiomatized for now.

Mathematically: A Banach *-algebra over ℂ satisfying the C*-identity ‖a*a‖ = ‖a‖².
This includes bounded operators on Hilbert spaces, continuous functions vanishing
at infinity, and many other examples.
-/
class CStarAlgebra (A : Type*) extends Ring A, StarRing A, Algebra ℂ A, NormedRing A where
  /-- The C*-identity: ‖a*a‖ = ‖a‖² -/
  norm_star_mul_self : ∀ a : A, ‖star a * a‖ = ‖a‖ ^ 2
  /-- Star is an isometry -/
  norm_star : ∀ a : A, ‖star a‖ = ‖a‖
  /-- Completeness -/
  complete : CompleteSpace A

/-- A one-parameter *-automorphism group on a C*-algebra.

Mathematically: A strongly continuous group homomorphism α : ℝ → Aut(A),
where Aut(A) is the group of *-automorphisms of A.

This represents time evolution: α_t(a) is the observable a evolved by time t.
-/
structure Dynamics (A : Type*) [CStarAlgebra A] where
  /-- The automorphism at time t -/
  evolve : ℝ → A →ₗ⋆[ℂ] A
  /-- Each α_t is multiplicative -/
  map_mul : ∀ t a b, evolve t (a * b) = evolve t a * evolve t b
  /-- Each α_t preserves the unit (if it exists) -/
  map_one : ∀ t, evolve t 1 = 1
  /-- Each α_t preserves the star -/
  map_star : ∀ t a, evolve t (star a) = star (evolve t a)
  /-- Group property: α_{s+t} = α_s ∘ α_t -/
  evolve_add : ∀ s t a, evolve (s + t) a = evolve s (evolve t a)
  /-- Identity at t = 0 -/
  evolve_zero : ∀ a, evolve 0 a = a
  /-- Strong continuity: t ↦ α_t(a) is continuous for each a -/
  continuous_evolve : ∀ a, Continuous (fun t => evolve t a)

-- Notation for dynamics
notation:max "α[" τ "]" => Dynamics.evolve τ

/-- A state on a C*-algebra.

Mathematically: A positive linear functional of norm 1.
Physically: An expectation value functional ω(a) = ⟨ψ|a|ψ⟩.
-/
structure State (A : Type*) [CStarAlgebra A] where
  /-- The underlying linear functional -/
  toFun : A →ₗ[ℂ] ℂ
  /-- Positivity: ω(a*a) ≥ 0 -/
  nonneg : ∀ a, 0 ≤ (toFun (star a * a)).re
  /-- Normalization: ω(1) = 1 -/
  normalized : toFun 1 = 1
  /-- Continuity -/
  continuous : Continuous toFun

-- Coercion to function
instance (A : Type*) [CStarAlgebra A] : CoeFun (State A) (fun _ => A → ℂ) :=
  ⟨fun ω => ω.toFun⟩

/-! ## The KMS Condition -/

/-- A KMS function for elements a, b at inverse temperature β.

This encapsulates a function F : ℂ → ℂ satisfying:
1. Holomorphic on the open strip S_β
2. Bounded and continuous on the closed strip
3. Correct boundary values relating ω(a·α_t(b)) and ω(α_t(b)·a)
-/
structure KMSFunction {A : Type*} [CStarAlgebra A]
    (ω : State A) (α : Dynamics A) (β : ℝ) (a b : A) where
  /-- The underlying function -/
  toFun : ℂ → ℂ
  /-- Holomorphic on the open strip -/
  holomorphic : DifferentiableOn ℂ toFun (Strip β)
  /-- Continuous on the closed strip -/
  continuousOn : ContinuousOn toFun (ClosedStrip β)
  /-- Bounded on the closed strip -/
  bounded : BddAbove (norm '' (toFun '' ClosedStrip β))
  /-- Lower boundary condition: F(t) = ω(a · α_t(b)) -/
  lower_boundary : ∀ t : ℝ, toFun (realToLower t) = ω (a * α.evolve t b)
  /-- Upper boundary condition: F(t + iβ) = ω(α_t(b) · a) -/
  upper_boundary : ∀ t : ℝ, toFun (realToUpper β t) = ω (α.evolve t b * a)

/-- A state ω is a KMS state at inverse temperature β with respect to dynamics α
if for every pair of elements a, b ∈ A, there exists a KMS function. -/
def IsKMSState {A : Type*} [CStarAlgebra A]
    (ω : State A) (α : Dynamics A) (β : ℝ) : Prop :=
  ∀ a b : A, Nonempty (KMSFunction ω α β a b)

/-! ## Important Special Cases -/

/-- A state is a ground state (KMS at β = +∞) if it satisfies a one-sided
analyticity condition. -/
def IsGroundState {A : Type*} [CStarAlgebra A]
    (ω : State A) (α : Dynamics A) : Prop :=
  ∀ a b : A, ∃ F : ℂ → ℂ,
    DifferentiableOn ℂ F {z : ℂ | 0 < z.im} ∧
    ContinuousOn F {z : ℂ | 0 ≤ z.im} ∧
    (∀ t : ℝ, F t = ω (a * α.evolve t b))

/-- A state is α-invariant if ω ∘ α_t = ω for all t. -/
def IsInvariant {A : Type*} [CStarAlgebra A]
    (ω : State A) (α : Dynamics A) : Prop :=
  ∀ t a, ω (α.evolve t a) = ω a

/-! ## Basic Properties -/


variable {A : Type*} [CStarAlgebra A]

/-! ## The Convex Combination of KMS Functions -/

/-- Given KMS functions F₁, F₂ for states ω₁, ω₂, construct the convex combination. -/
def KMSFunction.convexCombination
    {ω₁ ω₂ ω : State A} {α : Dynamics A} {β : ℝ} {a b : A}
    (F₁ : KMSFunction ω₁ α β a b)
    (F₂ : KMSFunction ω₂ α β a b)
    (t : ℝ)
    (hω : ∀ x, ω x = t * ω₁ x + (1 - t) * ω₂ x) :
    KMSFunction ω α β a b where
  -- The underlying function is the convex combination
  toFun := fun z => t * F₁.toFun z + (1 - t) * F₂.toFun z

  -- Holomorphic: sum of holomorphic functions is holomorphic
  holomorphic := by
    refine DifferentiableOn.add ?_ ?_
    · convert F₁.holomorphic.const_smul (t : ℂ) using 1
    · convert F₂.holomorphic.const_smul ((1 - t) : ℂ) using 1

  -- Continuous: sum of continuous functions is continuous
  continuousOn := by
    refine ContinuousOn.add ?_ ?_
    · exact (continuousOn_const).mul F₁.continuousOn
    · exact (continuousOn_const).mul F₂.continuousOn

  -- Bounded: follows from F₁, F₂ bounded via triangle inequality
  bounded := by
    -- Get bounds for F₁ and F₂
    obtain ⟨M₁, hM₁⟩ := F₁.bounded
    obtain ⟨M₂, hM₂⟩ := F₂.bounded
    -- The combination is bounded by |t|*M₁ + |1-t|*M₂
    use |t| * M₁ + |1 - t| * M₂
    intro y hy
    -- y is in the image of norms
    simp only [mem_image] at hy
    obtain ⟨w, ⟨z, hz, rfl⟩, rfl⟩ := hy
    -- Use triangle inequality: ‖a + b‖ ≤ ‖a‖ + ‖b‖
    calc ‖t * F₁.toFun z + (1 - t) * F₂.toFun z‖
        ≤ ‖t * F₁.toFun z‖ + ‖(1 - t) * F₂.toFun z‖ := norm_add_le _ _
      _ = |t| * ‖F₁.toFun z‖ + |1 - t| * ‖F₂.toFun z‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real]
          rw [show (1 - t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; ring]
          rw [Complex.norm_real]
          rfl
      _ ≤ |t| * M₁ + |1 - t| * M₂ := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
            apply hM₁
            simp only [mem_image, exists_exists_and_eq_and]
            exact ⟨z, hz, rfl⟩
          · apply mul_le_mul_of_nonneg_left _ (abs_nonneg (1 - t))
            apply hM₂
            simp only [mem_image, exists_exists_and_eq_and]
            exact ⟨z, hz, rfl⟩

  -- Lower boundary: F(t) = ω(a · α_t(b))
  lower_boundary := by
    intro s
    -- F(s) = t * F₁(s) + (1-t) * F₂(s)
    --      = t * ω₁(a * α_s(b)) + (1-t) * ω₂(a * α_s(b))
    --      = ω(a * α_s(b))
    rw [F₁.lower_boundary, F₂.lower_boundary]
    rw [hω]

  -- Upper boundary: F(t + iβ) = ω(α_t(b) · a)
  upper_boundary := by
    intro s
    rw [F₁.upper_boundary, F₂.upper_boundary]
    rw [hω]

/-! ## The Main Theorem -/

/-- The set of KMS states at fixed β is convex.

If ω₁ and ω₂ are both KMS at β, then so is λω₁ + (1-λ)ω₂ for 0 ≤ λ ≤ 1.
This reflects that mixtures of equilibrium states at the same temperature
are still equilibrium states.
-/
theorem kms_states_convex_combination
    (α : Dynamics A) (β : ℝ) (ω₁ ω₂ : State A)
    (h₁ : IsKMSState ω₁ α β) (h₂ : IsKMSState ω₂ α β)
    (t : ℝ) (_ht₀ : 0 ≤ t) (_ht₁ : t ≤ 1)
    (ω : State A)
    (hω : ∀ a, ω a = t * ω₁ a + (1 - t) * ω₂ a) :
    IsKMSState ω α β := by
  -- We need to show: for all a b, there exists a KMS function
  intro a b
  -- Get the KMS functions for ω₁ and ω₂
  obtain ⟨F₁⟩ := h₁ a b
  obtain ⟨F₂⟩ := h₂ a b
  -- The convex combination works!
  exact ⟨KMSFunction.convexCombination F₁ F₂ t hω⟩


/-! ## The Special KMS Function for (1, a) -/

/-- For a KMS function witnessing the pair (1, a), both boundaries give ω(α_t(a)).
This is the key observation that enables the invariance proof. -/
lemma kms_function_one_boundaries_agree
    {ω : State A} {α : Dynamics A} {β : ℝ} {a : A}
    (F : KMSFunction ω α β 1 a) (t : ℝ) :
    F.toFun (realToLower t) = F.toFun (realToUpper β t) := by
  rw [F.lower_boundary, F.upper_boundary]
  -- Lower: ω(1 * α_t(a)) = ω(α_t(a))
  -- Upper: ω(α_t(a) * 1) = ω(α_t(a))
  simp only [one_mul, mul_one]


/-! ## The Main Invariance Theorem -/

/-- **KMS states are time-invariant.**

If ω is a KMS state at inverse temperature β with respect to dynamics α,
then ω(α_t(a)) = ω(a) for all t ∈ ℝ and a ∈ A.

**Proof outline:**
1. Get the KMS function F for pair (1, a)
2. Both boundaries give ω(α_t(a)), so F(t) = F(t + iβ)
3. Extend F periodically to get a bounded entire function G
4. By Liouville's theorem, G is constant
5. Therefore ω(α_t(a)) = G(t) = G(0) = ω(a)
-/
theorem IsKMSState.isInvariant
    {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β)
    (h : IsKMSState ω α β)
    /- Morera: periodic extensions of KMS functions are entire -/
    (hMorera : ∀ a : A, ∀ F : KMSFunction ω α β 1 a,
      Differentiable ℂ (periodicExtension F.toFun β)) :
    IsInvariant ω α := by
  intro t a
  -- Get the KMS function for (1, a)
  obtain ⟨F⟩ := h 1 a
  -- The boundaries agree
  have boundary_match : ∀ s : ℝ, F.toFun (realToLower s) = F.toFun (realToUpper β s) :=
    kms_function_one_boundaries_agree F
  -- Extend to a bounded entire function
  obtain ⟨G, G_diff, G_bdd, G_extends⟩ := periodic_strip_extension
    F.toFun hβ F.holomorphic F.continuousOn F.bounded boundary_match (hMorera a F)
  -- By Liouville, G is constant
  have G_const : ∀ z w : ℂ, G z = G w :=
    fun z w => G_diff.apply_eq_apply_of_bounded G_bdd z w
  -- Connect back to ω
  calc ω (α.evolve t a)
      = F.toFun (realToLower t) := by rw [F.lower_boundary]; simp [one_mul]
    _ = G (realToLower t) := (G_extends (realToLower t) (by
        simp only [ClosedStrip, realToLower, mem_setOf_eq, ofReal_im]
        exact ⟨le_refl 0, le_of_lt hβ⟩)).symm
    _ = G (realToLower 0) := by
        simp only [realToLower]
        exact G_const t 0
    _ = F.toFun (realToLower 0) := G_extends (realToLower 0) (by
        simp only [ClosedStrip, realToLower, mem_setOf_eq, ofReal_zero, zero_im]
        exact ⟨le_refl 0, le_of_lt hβ⟩)
    _ = ω (α.evolve 0 a) := by rw [F.lower_boundary]; simp [one_mul]
    _ = ω a := by rw [α.evolve_zero]

end KMSCondition
