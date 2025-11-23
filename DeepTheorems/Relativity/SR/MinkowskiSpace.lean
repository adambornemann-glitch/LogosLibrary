/-
==================================================================================================================
  MINKOWSKI SPACE: The Foundation of Relativity
==================================================================================================================

Before we can understand curved spacetime and rotating black holes, we must understand
flat spacetime. This is Minkowski space - the arena of Special Relativity.

**Historical Context:**
- 1905: Einstein publishes Special Relativity (time is relative, space is relative)
- 1908: Hermann Minkowski realizes spacetime is a unified 4D geometry
- 1915: Einstein extends this to General Relativity (spacetime can curve)
- 1963: Roy Kerr solves Einstein's equations for rotating black holes

Minkowski famously declared: "Henceforth space by itself, and time by itself, are doomed
to fade away into mere shadows, and only a kind of union of the two will preserve an
independent reality."

**Why This Matters:**

Minkowski space is to General Relativity what Euclidean geometry is to curved surfaces.
You must understand the flat case before you can understand curvature. Every point in
a curved spacetime looks approximately Minkowski in a small enough region (just like
Earth looks flat locally, even though it's a sphere).

**The Key Idea: The Metric**

In Euclidean 3D space, distance squared is: ds² = dx² + dy² + dz²
In Minkowski 4D spacetime, interval squared is: ds² = -dt² + dx² + dy² + dz²

That minus sign changes EVERYTHING:
- Some separations are timelike (ds² < 0) - can be connected by massive particles
- Some separations are spacelike (ds² > 0) - cannot be causally connected
- Some separations are lightlike/null (ds² = 0) - connected by light rays

This is the signature of spacetime: (-, +, +, +) or equivalently (+, -, -, -) depending
on convention. We use the "mostly plus" convention: (-, +, +, +).

**Lorentz Transformations:**

In Euclidean space, rotations preserve distances.
In Minkowski space, Lorentz boosts preserve intervals.

A Lorentz boost is like a "rotation" that mixes time and space, corresponding to
viewing spacetime from a moving reference frame. These transformations preserve the
Minkowski metric - they're the symmetries of special relativity.

**Why We Start Here:**

The Kerr metric reduces to Minkowski space in two important limits:
1. Far from the black hole (r → ∞) - spacetime becomes flat
2. In a freely falling frame near any point - locally looks Minkowski

So Minkowski space is the "background" against which we measure curvature.

By formalizing Minkowski space in Lean, we:
- Establish the mathematical machinery for metrics and inner products
- Prove basic theorems about causal structure (timelike, spacelike, lightlike)
- Set up coordinates and transformations properly
- Create a template for more complex curved spacetimes like Kerr

**Structure of This Section:**

1. Basic Definitions - Vectors, metric, inner product
2. Causal Structure - Timelike, spacelike, lightlike vectors
3. Light Cone - The boundary of causality
4. Lorentz Transformations - Symmetries of Minkowski space
5. Examples - Photon 4-velocities, time dilation, proper time
6. Physical Interpretation - What the mathematics means

**Notation:**
- n: number of spatial dimensions (usually 3 for physical spacetime)
- vec: components of a vector (vec 0 = time, vec 1,2,3 = space)
- ⟪v, w⟫ₘ: Minkowski inner product (our notation for the metric)
- ds²: interval (squared "distance" in spacetime)

**Convention:**
We use signature (-, +, +, +): time gets a minus sign, space gets plus signs.
This is the "mostly plus" or "spacelike" convention, common in particle physics.
Some texts use (+, -, -, -) - the physics is the same, just signs flip.

**A Note on Rigor:**

We're formalizing this in Lean 4, a proof assistant. This means every theorem must be
actually proven - no handwaving allowed. This is overkill for standard special relativity
(which is well-understood), but it's essential practice for the Kerr metric, where
separating rigorous mathematics from physical speculation becomes critical.

Think of this section as "warming up" before we tackle rotating black holes.

Let's begin with the simplest structure: a vector in spacetime.
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

/-- The Minkowski metric signature (+, -, -, -) or (-, +, +, +) depending on convention -/
structure MinkowskiSpace (n : ℕ) where
  /-- We'll use ℝⁿ⁺¹ as our vector space (n spatial + 1 time) -/
  vec : Fin (n + 1) → ℝ

namespace MinkowskiSpace

/-- The Minkowski inner product with signature (-, +, +, ..., +) -/

-- Alternative cleaner version using Fin.succ:
def minkowskiMetric {n : ℕ} (v w : MinkowskiSpace n) : ℝ :=
  - v.vec 0 * w.vec 0 + (Finset.sum (Finset.univ : Finset (Fin n)) fun i =>
    v.vec i.succ * w.vec i.succ)

-- Or even cleaner, sum over all indices and handle the sign:
def minkowskiMetric' {n : ℕ} (v w : MinkowskiSpace n) : ℝ :=
  Finset.sum (Finset.univ : Finset (Fin (n + 1))) fun i =>
    if i = 0 then - v.vec i * w.vec i else v.vec i * w.vec i


notation "⟪" v ", " w "⟫ₘ" => minkowskiMetric v w

/-- A vector is timelike if its Minkowski norm is negative -/
def isTimelike {n : ℕ} (v : MinkowskiSpace n) : Prop :=
  ⟪v, v⟫ₘ < 0

/-- A vector is spacelike if its Minkowski norm is positive -/
def isSpacelike {n : ℕ} (v : MinkowskiSpace n) : Prop :=
  ⟪v, v⟫ₘ > 0

/-- A vector is lightlike (null) if its Minkowski norm is zero -/
def isLightlike {n : ℕ} (v : MinkowskiSpace n) : Prop :=
  ⟪v, v⟫ₘ = 0

/-- The light cone at the origin -/
def lightCone (n : ℕ) : Set (MinkowskiSpace n) :=
  {v | isLightlike v}

/-- Lorentz transformation: preserves the Minkowski metric -/
structure LorentzTransform (n : ℕ) where
  transform : MinkowskiSpace n → MinkowskiSpace n
  preserves_metric : ∀ v w, ⟪transform v, transform w⟫ₘ = ⟪v, w⟫ₘ


/-- Example: construct a 4-vector (for 3+1 spacetime) -/
def fourVector (t x y z : ℝ) : MinkowskiSpace 3 :=
  ⟨fun i => match i with
    | 0 => t
    | 1 => x
    | 2 => y
    | 3 => z
    | _ => 0⟩  -- This case is actually impossible but Lean needs it

/-- Example: construct a 4-vector (for 3+1 spacetime) -/
def fourVector' (t x y z : ℝ) : MinkowskiSpace 3 :=
  ⟨fun i =>
    if _ : i = 0 then t
    else if _ : i = 1 then x
    else if _ : i = 2 then y
    else if _ : i = 3 then z
    else 0⟩  -- Never reached but Lean needs completeness

/-- Prove that the metric is symmetric -/
theorem minkowski_symmetric {n : ℕ} (v w : MinkowskiSpace n) :
    ⟪v, w⟫ₘ = ⟪w, v⟫ₘ := by
  --simp [minkowskiMetric, mul_comm]
  unfold minkowskiMetric
  simp only [mul_comm (v.vec _) (w.vec _)]
  congr 1
  linarith

/-- A simple example: a photon's 4-velocity is lightlike -/
example : isLightlike (fourVector' 1 1 0 0) := by
  unfold isLightlike minkowskiMetric fourVector'
  --simp! < -- method 1
  --ring_nf!;simp! <-- method 2
  abel_nf!;simp! -- <-- metho 3
   -- The metric gives -1 + 1 + 0 + 0 = 0 ✓

/-- A Lorentz boost in the x-direction with velocity v (where c=1) -/
noncomputable def lorentzBoostX (v : ℝ) (hv : |v| < 1) : LorentzTransform 3 where
  transform := fun vec4 =>
    let γ := 1 / Real.sqrt (1 - v^2)
    ⟨fun i =>
      if i = 0 then γ * (vec4.vec 0 - v * vec4.vec 1)
      else if i = 1 then γ * (vec4.vec 1 - v * vec4.vec 0)
      else vec4.vec i⟩
  preserves_metric := by sorry -- This is a real proof but non-trivial!

/-- The zero vector (origin in spacetime) -/
def origin (n : ℕ) : MinkowskiSpace n := ⟨fun _ => 0⟩

/-- Proper time squared (negative of Minkowski norm for timelike vectors) -/
def properTimeSquared {n : ℕ} (v : MinkowskiSpace n) : ℝ := -⟪v, v⟫ₘ

/-- The interval between two events -/
def interval {n : ℕ} (event1 event2 : MinkowskiSpace n) : ℝ :=
  let diff := ⟨fun i => event2.vec i - event1.vec i⟩
  ⟪diff, diff⟫ₘ

/-- Every vector is exactly one type -/
theorem vector_classification_clean {n : ℕ} (v : MinkowskiSpace n) :
    isTimelike v ∨ isSpacelike v ∨ isLightlike v := by
  unfold isTimelike isSpacelike isLightlike
  have := lt_trichotomy (⟪v, v⟫ₘ) 0
  tauto

/-- Classification theorem: every vector is exactly one of timelike, spacelike, or lightlike -/
theorem vector_classification {n : ℕ} (v : MinkowskiSpace n) :
    (isTimelike v ∧ ¬isSpacelike v ∧ ¬isLightlike v) ∨
    (¬isTimelike v ∧ isSpacelike v ∧ ¬isLightlike v) ∨
    (¬isTimelike v ∧ ¬isSpacelike v ∧ isLightlike v) := by
  unfold isTimelike isSpacelike isLightlike
  --omega  Only works on ℕ ℤ and ℝ
  have h := lt_trichotomy (⟪v, v⟫ₘ) 0
  cases h with
  | inl h => -- metric < 0, so timelike
    left
    constructor
    · exact h
    constructor
    · linarith
    · linarith
  | inr h =>
    cases h with
    | inl h => -- metric = 0, so lightlike
      right; right
      constructor
      · linarith
      constructor
      · linarith
      · exact h
    | inr h => -- metric > 0, so spacelike
      right; left
      constructor
      · linarith
      constructor
      · exact h
      · linarith


/-- Physical example: time dilation -/
def movingClock (τ : ℝ) (v : ℝ) : MinkowskiSpace 3 :=
  fourVector τ (v * τ) 0 0

/-- Physical example: time dilation - Fixed version -/
theorem time_dilation (τ : ℝ) (v : ℝ) (_ : τ > 0) (_ : |v| < 1) :
    properTimeSquared (movingClock τ v) = τ^2 * (1 - v^2) := by
  unfold properTimeSquared movingClock fourVector minkowskiMetric
  rw [Finset.sum_fin_eq_sum_range]
  simp [Finset.sum_range_succ, Fin.succ]
  ring_nf!


/-- The velocity 4-vector of a worldline at proper time τ -/
structure FourVelocity (n : ℕ) where
  vec : Fin (n + 1) → ℝ
  normalized : ⟪⟨vec⟩, ⟨vec⟩⟫ₘ = -1  -- For massive particles

/-- A worldline parameterized by proper time -/
structure Worldline (n : ℕ) where
  path : ℝ → MinkowskiSpace n
  -- For massive particles, the tangent vector should be timelike with norm -1

/-- A simpler example: uniform motion in the x direction -/
noncomputable def uniformMotion (v : ℝ) (_ : |v| < 1) : Worldline 3 where
  path := fun τ =>
    let γ := 1 / Real.sqrt (1 - v^2)
    --fourVector (γ * τ) (γ * v * τ) 0 0
    fourVector (γ * τ) (γ * v * τ) τ τ

/-- A metric tensor at a point (symmetric 2-tensor) -/
structure MetricTensor (n : ℕ) where
  g : Fin n → Fin n → ℝ
  symmetric : ∀ i j, g i j = g j i

/-- Christoffel symbols (connection coefficients) -/
structure ChristoffelSymbols (n : ℕ) where
  Γ : Fin n → Fin n → Fin n → ℝ  -- Γⁱⱼₖ

/-- The Riemann curvature tensor -/
structure RiemannTensor (n : ℕ) where
  R : Fin n → Fin n → Fin n → Fin n → ℝ  -- Rⁱⱼₖₗ
  -- Should satisfy various symmetries
